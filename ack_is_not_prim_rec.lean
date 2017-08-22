import .ack .prim_rec


def sum_of_fin: forall {n}, (fin n -> nat) -> nat
| 0 _ := 0
| (n' + 1) ls := sum_of_fin (fun i, ls (fin.succ i)) + ls 0


lemma sum_of_fin_ge_arg : forall n, forall tuple: fin n -> nat, forall i: fin n,
  sum_of_fin tuple >= tuple i :=
fun n tuple i,
begin
  induction n,
  show sum_of_fin tuple >= tuple i,
  {
    cases i with _ ilt0,
    note := nat.not_succ_le_zero _ ilt0,
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


lemma sum_of_fin_1: forall x, sum_of_fin (fun _: fin 1, x) = x :=
fun x, by rw sum_of_fin_const; simp


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
    sum_of_fin x
        =  sum_of_fin (fun i, x (fin.succ i)) + x 0 : by reflexivity
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


lemma sum_of_fin_of_curry: forall k v, forall rest: fin k -> nat,
  sum_of_fin (curry v rest) = sum_of_fin rest + v := fun k v rest,
begin
  calc
    sum_of_fin (curry v rest)
        = sum_of_fin (fun i, curry v rest (fin.succ i)) + curry v rest 0 : by reflexivity
    ... = sum_of_fin rest + curry v rest 0 :
          begin
            note h : (fun i, curry v rest (fin.succ i)) = rest :=
            begin
              apply funext,
              intro x,
              rw curry_at_succ,
            end,
            rw h,
          end
    ... = sum_of_fin rest + v : by rw curry_at_0
end


lemma fin_1_curry: forall arg: fin 1 -> nat, (fun _: fin 1, arg 0) = arg :=
take arg,
begin
  apply funext,
  intro x,
  cases x with x lt,
  note h: x <= 0 := nat.le_of_lt_succ lt,
  note xeq0: x = 0 := nat.eq_zero_of_le_zero h,
  cases xeq0,
  reflexivity,
end


def prim_depth: forall {k}, prim_rec k -> nat
| 0 prim_rec.zero := 0
| 1 prim_rec.succ := 0
| m (prim_rec.proj _) := 0
| m (@prim_rec.comp k .(m) (f: prim_rec k) (g: fin k -> prim_rec m)) :=
  max (prim_depth f) (k + 3 + sum_of_fin (fun i, prim_depth (g i))) + 2
| (k + 1) (prim_rec.prec f g) := max (prim_depth f) (prim_depth g + 2) + 1


lemma prim_depth_rw_proj : forall n, forall idx: fin n, prim_depth (prim_rec.proj idx) = 0 :=
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


lemma prim_depth_rw_prec: forall k, forall f: prim_rec k, forall g: prim_rec (k + 2),
  prim_depth (prim_rec.prec f g) = max (prim_depth f) (prim_depth g + 2) + 1 :=
fun k f g, by cases k; reflexivity


theorem ack_dominates_prim_rec:
  forall k, forall f: prim_rec k,
  forall arg: fin k -> nat,
  ack (prim_depth f) (sum_of_fin arg) >= prim_eval f arg :=
fun k_d f arg,
begin
induction f with n a k m f g _ _ k f g; clear k_d,
calc
  ack (prim_depth prim_rec.zero) (sum_of_fin arg)
      =  ack 0 0 : by reflexivity
  ... =  1 : by simp only [ack]
  ... >= 0 : by apply nat.le_succ
  ... =  prim_eval prim_rec.zero arg : by reflexivity,
calc
  ack (prim_depth prim_rec.succ) (sum_of_fin arg)
       = ack 0 (sum_of_fin arg) : by reflexivity
   ... = sum_of_fin arg + 1 : by simp only [ack]
   ... = sum_of_fin (fun _: fin 1, arg 0) + 1 : by rw fin_1_curry
   ... = arg 0 + 1 : by rw sum_of_fin_1
   ... >= prim_eval prim_rec.succ arg : by apply nat.le_refl,
calc
  ack (prim_depth (prim_rec.proj a)) (sum_of_fin arg)
       = ack 0 (sum_of_fin arg) : by rw prim_depth_rw_proj
   ... = sum_of_fin arg + 1 : by simp only [ack]
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
  unfold prim_eval,
  pose h: nat -> (fin k -> nat) -> nat :=
    fun (v: nat) (arg: fin k -> nat),
      nat.rec (prim_eval f arg) (fun v' prev, prim_eval g (curry prev (curry v' arg))) v,
  show ack (prim_depth (prim_rec.prec f g)) (sum_of_fin arg) >= prim_eval._match_1 k h (uncurry arg),
  rw curry_of_uncurry arg,
  generalize (uncurry arg) pq,
  intro pq,
  cases pq with v rest,
  rw sum_of_fin_of_curry,
  rw prim_depth_rw_prec,
  pose fgdep := max (prim_depth f) (prim_depth g + 2) + 1,
  show ack fgdep (sum_of_fin rest + v) >= h v rest,
  induction v with v' ihinner,
  calc
    ack fgdep (sum_of_fin rest)
        >= ack (prim_depth f) (sum_of_fin rest) :
           begin
             apply ack_1st_incr_eq,
             apply nat.le_succ_of_le,
             apply le_max_left,
           end
    ... >= prim_eval f rest : by apply ih_1
    ... =  h 0 rest : by reflexivity,
  calc
    ack fgdep (sum_of_fin rest + v' + 1)
    = ack (max (prim_depth f) (prim_depth g + 2)) (ack fgdep (sum_of_fin rest + v')) : by simp only [ack]
    ... >= ack (prim_depth g + 2) (ack fgdep (sum_of_fin rest + v')) : by apply ack_1st_incr_eq; apply le_max_right
    ... >= ack (prim_depth g + 1) (2 * ack fgdep (sum_of_fin rest + v')) : by apply nat.le_of_lt; apply ack_lemma_8; apply nat.le_add_left
    ... >= ack (prim_depth g) (2 * ack fgdep (sum_of_fin rest + v')) : by apply ack_1st_incr_eq; apply nat.le_add_right
    ... >= ack (prim_depth g) (sum_of_fin (curry (h v' rest) (curry v' rest))) :
           begin
             apply ack_2nd_incr_eq,
             calc
               2 * ack fgdep (sum_of_fin rest + v')
               >= sum_of_fin rest + v' + ack fgdep (sum_of_fin rest + v') :
                 begin
                   rw nat.succ_mul,
                   apply nat.add_le_add_right,
                   rw nat.one_mul,
                   apply nat.le_of_lt,
                   apply ack_2nd_lt_val,
                 end
               ... >= sum_of_fin rest + v' + h v' rest :
                 begin
                   apply nat.add_le_add_left,
                   exact ihinner,
                 end
               ... =  sum_of_fin (curry (h v' rest) (curry v' rest)) :
                   by repeat { rw sum_of_fin_of_curry },
           end
    ... >= prim_eval g (curry (h v' rest) (curry v' rest)) : by apply ih_2
    ... =  h (v' + 1) rest : by reflexivity,
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
  calc
    ack (prim_depth f) x
        <  ack x x : by apply ack_1st_succ
    ... <= ack (prim_depth f) x : ph,
end


theorem ack_is_not_prim_rec_2:
  forall f: prim_rec 2, (forall x y,
  ack x y =  prim_eval f (curry x (fun _: fin 1, y))) -> false :=
begin
  intros f h,
  note one_arg_ver: forall x, ack x x = prim_eval (prim_rec.comp f (fun _, prim_id)) (fun _, x)
  :=
  begin
    intro x,
    show ack x x = prim_eval f (fun _, prim_eval prim_id (fun _, x)),
    rw prim_id_is_id,
    rw h x x,
    apply congr_arg,
    apply funext,
    intro i,
    cases i with i is_lt,
    note h := nat.le_of_lt_succ is_lt,
    cases h,
    reflexivity,
    note hp := nat.eq_zero_of_le_zero a,
    cases hp,
    reflexivity,
  end,
  exact ack_is_not_prim_rec _ one_arg_ver,
end
