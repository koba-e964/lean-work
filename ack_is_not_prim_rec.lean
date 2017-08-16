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


def prim_depth: forall {k}, prim_rec k -> nat
| 0 prim_rec.zero := 0
| 1 prim_rec.succ := 0
| m (prim_rec.proj idx) := 0
| m (@prim_rec.comp k .(m) (f: prim_rec k) (g: fin k -> prim_rec m)) :=
  max (prim_depth f) (k + 3 + sum_of_fin (fun i, prim_depth (g i)))
| (k + 1) (@prim_rec.prec .(k) f g) := max (prim_depth f) (prim_depth g + 2)


theorem ack_dominates_prim_rec:
  forall k, forall f: prim_rec k,
  forall arg: fin k -> nat,
  ack (prim_depth f) (sum_of_fin arg) >= prim_eval f arg :=
sorry


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
