import .ack .prim_rec


def sum_of_fin: forall {n}, (fin n -> nat) -> nat :=
begin
  intro n,
  induction n with n' sof,
  { intro _, exact 0 },
  intro ls,
  exact sof (fun x, ls (fin.succ x)) + ls 0,
end


lemma sum_of_fin_1: forall x, sum_of_fin (fun _: fin 1, x) = x :=
begin
  intro x,
  show 0 + x = x,
  apply zero_add,
end


lemma sum_of_fin_ge_arg : forall n, forall tuple: fin n -> nat, forall i: fin n,
  sum_of_fin tuple >= tuple i :=
fun n tuple i,
begin
  induction n,
  show sum_of_fin tuple >= tuple i,
  {
    cases i with _ ilt0,
    pose h: false := nat.not_succ_le_zero _ ilt0,
    contradiction,
  },
  show sum_of_fin tuple >= tuple i,
  cases i with i is_lt,
  cases i with i',
  calc
    sum_of_fin tuple
        = sum_of_fin (fun j, tuple (fin.succ j)) + tuple 0 : by reflexivity
    ... >= tuple 0 : by apply nat.le_add_left,
  calc
    sum_of_fin tuple
        = sum_of_fin (fun j, tuple (fin.succ j)) + tuple 0 : by reflexivity
    ... >= sum_of_fin (fun j, tuple (fin.succ j)) : by apply nat.le_add_right
    ... >= (fun j, tuple (fin.succ j)) ⟨i', nat.lt_of_succ_lt_succ is_lt⟩
           : by apply ih_1 (fun j, tuple (fin.succ j)),
end


lemma sum_of_fin_const: forall k v, sum_of_fin (fun _: fin k, v) = k * v :=
fun k v,
begin
  induction k with k' ih,
  { rw nat.mul_comm; reflexivity },
  calc
    sum_of_fin (fun (_x : fin (k' + 1)), v)
        = sum_of_fin (fun (_: fin k'), v) + v : by reflexivity
    ... = k' * v + v : by rw ih
    ... = (k' + 1) * v : by rw nat.succ_mul,
end


lemma sum_of_fin_incr_eq: forall k, forall x y: fin k -> nat,
  (forall i: fin k, x i <= y i) -> sum_of_fin x <= sum_of_fin y :=
fun k,
begin
  induction k with k' ih,
  {
    intros x y h,
    reflexivity,
  },
  intros x y h,
  calc
    sum_of_fin x = sum_of_fin (fun i, x (fin.succ i)) + x 0 : by reflexivity
    ... <= sum_of_fin (fun i, x (fin.succ i)) + y 0 : by apply nat.add_le_add_left; apply h
    ... <= sum_of_fin (fun i, y (fin.succ i)) + y 0 :
           begin
             apply nat.add_le_add_right,
             apply ih,
             intro i,
             apply h,
           end
    ... =  sum_of_fin y : by reflexivity
end


lemma fin_1_curry: forall arg: fin 1 -> nat, (fun _: fin 1, arg 0) = arg :=
take arg,
begin
  apply funext,
  intro x,
  cases x with x lt,
  cases lt with s a,
  reflexivity,
  note h: false := nat.not_succ_le_zero x a,
  contradiction,
end


def prim_depth: forall {k}, prim_rec k -> nat
| 0 prim_rec.zero := 0
| 1 prim_rec.succ := 0
| m (@prim_rec.proj .(m) _) := 0
| m (@prim_rec.comp k .(m) (f: prim_rec k) (g: fin k -> prim_rec m)) :=
  max (prim_depth f) (k + 3 + sum_of_fin (fun i, prim_depth (g i))) + 2
| (k + 1) (@prim_rec.prec .(k) f g) := max (prim_depth f) (prim_depth g + 2)


lemma prim_depth_rw_proj : forall n, forall idx: fin n, @prim_depth n (@prim_rec.proj n idx) = 0 :=
begin
  intros n idx,
  cases n with n',
  reflexivity,
  cases n';
  reflexivity,
end


lemma prim_depth_rw_comp: forall k m, forall f: prim_rec k, forall g: fin k -> prim_rec m,
  prim_depth (prim_rec.comp f g) = max (prim_depth f) (k + 3 + sum_of_fin (fun i, prim_depth (g i))) + 2
  :=
fun k m f g,
begin
  induction m with m',
  reflexivity,
  induction m'; reflexivity,
end


theorem ack_dominates_prim_rec:
  forall k, forall f: prim_rec k,
  forall arg: fin k -> nat,
  ack (prim_depth f) (sum_of_fin arg) >= prim_eval f arg :=
fun k_d f arg,
begin
induction f with n a k m f g _ _ k f g; clear k_d,
calc
  ack (prim_depth prim_rec.zero) (sum_of_fin arg)
      =  ack (prim_depth prim_rec.zero) 0 : by reflexivity
  ... =  ack 0 0 : by reflexivity
  ... =  1 : by simp [ack]
  ... >= 0 : by apply nat.le_succ
  ... =  prim_eval prim_rec.zero arg : by reflexivity,
calc
  ack (prim_depth prim_rec.succ) (sum_of_fin arg)
       = ack 0 (sum_of_fin arg) : by reflexivity
   ... = sum_of_fin arg + 1 : by simp [ack]
   ... = sum_of_fin (fun _: fin 1, arg 0) + 1 : by rw fin_1_curry
   ... = arg 0 + 1 : by rw sum_of_fin_1
   ... >= prim_eval prim_rec.succ arg : by unfold prim_eval; apply nat.le_refl,
calc
  ack (prim_depth (@prim_rec.proj n a)) (@sum_of_fin n arg)
       = ack 0 (@sum_of_fin n arg) : by rw prim_depth_rw_proj
   ... = sum_of_fin arg + 1 : by simp [ack]
   ... >= sum_of_fin arg : by apply nat.le_succ
   ... >= arg a : by apply sum_of_fin_ge_arg
   ... =  prim_eval (prim_rec.proj a) arg : by reflexivity,
calc
  ack (prim_depth (prim_rec.comp f g)) (sum_of_fin arg)
       = ack (max (prim_depth f) (k + 3 + sum_of_fin (fun i, prim_depth (g i))) + 2) (sum_of_fin arg)
         : by rw prim_depth_rw_comp
  ...  >= ack (max (prim_depth f) (k + 3 + sum_of_fin (fun i, prim_depth (g i))) + 1) (sum_of_fin arg + 1) :
           by apply ack_arg_1st_prior
  ...  >= ack (prim_depth f) (ack (k + 3 + sum_of_fin (fun i, prim_depth (g i))) (sum_of_fin arg))
         : by apply ack_dual_app
  ...  >= ack (prim_depth f) (sum_of_fin (fun i, prim_eval (g i) arg)) :
           begin
             apply ack_2nd_incr_eq,
             calc
               sum_of_fin (fun i, prim_eval (g i) arg)
                    <= sum_of_fin (fun i, ack (prim_depth (g i)) (sum_of_fin arg)) :
                       begin
                         apply sum_of_fin_incr_eq,
                         intro i,
                         apply ih_2,
                       end
               ...  <= sum_of_fin (fun _: fin k, ack (sum_of_fin (fun i, prim_depth (g i))) (sum_of_fin arg)) :
                       begin
                         apply sum_of_fin_incr_eq,
                         intro i,
                         apply ack_1st_incr_eq,
                         apply sum_of_fin_ge_arg k (fun (i : fin k), prim_depth (g i))
                       end
               ...  =  k * ack (sum_of_fin (fun i, prim_depth (g i))) (sum_of_fin arg) :
                          by apply sum_of_fin_const
               ...  <= (k + 1) * ack (sum_of_fin (fun i, prim_depth (g i))) (sum_of_fin arg) :
                          by apply nat.mul_le_mul_right; apply nat.le_add_right
               ...  <= (k + 1) * ack (sum_of_fin (fun i, prim_depth (g i)) + 3) (sum_of_fin arg) :
                       begin
                         apply nat.mul_le_mul_left,
                         apply ack_1st_incr_eq,
                         apply nat.le_add_right,
                       end
               ...  <= ack (sum_of_fin (fun i, prim_depth (g i)) + 3) (sum_of_fin arg + k) :
                       begin
                         apply ack_lemma_7,
                         apply nat.le_add_left,
                       end
               ...  <= ack (k + 3 + sum_of_fin (fun i, prim_depth (g i))) (sum_of_fin arg) :
                       begin
                         generalize (sum_of_fin (fun i, prim_depth (g i))) x,
                         generalize (sum_of_fin arg) y,
                         intros x y,
                         calc
                           ack (y + 3) (x + k) <= ack (y + 3 + k) x :
                             by apply ack_arg_1st_prior_any
                           ... = ack (k + 3 + y) x : by simp
                       end
           end
  ...  >= prim_eval f (fun i, prim_eval (g i) arg) : by apply ih_1
  ...  =  prim_eval (prim_rec.comp f g) arg : by reflexivity,
calc
  ack (prim_depth (prim_rec.prec f g)) (sum_of_fin arg)
       >= prim_eval (prim_rec.prec f g) arg : by admit,
end


theorem ack_is_not_prim_rec:
  forall f: prim_rec 1, (forall x,
  ack x x = prim_eval f (fun _, x)) -> false :=
begin
  intros f h,
  pose x: nat := prim_depth f + 1,
  note ph := ack_dominates_prim_rec 1 f (fun _, x),
  rw sum_of_fin_1 at ph,
  rw - (h x) at ph,
  apply lt_irrefl (ack (prim_depth f) x),
  apply nat.lt_of_lt_of_le,
  show ack (prim_depth f) x < ack x x, { apply ack_1st_succ },
  show ack x x <= ack (prim_depth f) x, { exact ph },
end
