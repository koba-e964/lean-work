import .axiom_int

namespace myint
-- order axioms
constant le : myint -> myint -> Prop
reserve infixl ` <== `:40
notation a `<==` b := le a b
axiom le_refl: forall x, x <== x
axiom le_succ: forall x y, x <== y -> x <== S y
axiom not_succ_le: forall x, not (S x <== x)

@[simp]
lemma le_refl_simp: forall x, x <== x := le_refl

-- induction on nat
axiom ind_on_nat: forall Q: myint -> Prop, forall a,
  Q a -> (forall x, a <== x -> Q x -> Q (S x)) -> forall x, a <== x -> Q x

lemma le_trans {x y z} (h1: x <== y) : y <== z -> x <== z :=
begin
  revert z,
  apply ind_on_nat,
  exact h1,
  intros z' h2 h3,
  exact le_succ _ _ h3,
end


lemma succ_le_succ : forall x y, x <== y -> S x <== S y :=
begin
  intro x,
  apply ind_on_nat,
  apply le_refl,
  intro y,
  intro h,
  apply le_succ,
end


lemma pred_le_pred : forall x y, x <== y -> P x <== P y :=
begin
  intro x,
  apply ind_on_nat,
  apply le_refl,
  intro y,
  simp,
  intros h h2,
  rw -succ_of_pred y,
  apply le_succ,
  exact h2,
end


lemma add_le_add_right {x y k: myint}: x <== y -> x ++ k <== y ++ k :=
begin
  intro h,
  induction k with k' ih k' ih,
  simp,
  apply h,
  simp,
  apply succ_le_succ,
  apply ih,
  simp,
  apply pred_le_pred,
  apply ih,
end


lemma add_le_add_left {x y k: myint}: x <== y -> k ++ x <== k ++ y :=
begin
  rw @add_comm k x,
  rw @add_comm k y,
  exact add_le_add_right
end


lemma add_le_add {x y z w: myint}: x <== y -> z <== w -> x ++ z <== y ++ w :=
assume h1 h2,
begin
  apply le_trans,
  apply add_le_add_right,
  exact h1,
  apply add_le_add_left,
  exact h2,
end


lemma eq_or_lt_of_le {x y: myint} (h: x <== y): x = y \/ S x <== y :=
begin
  apply fun foo bar, ind_on_nat (fun y, x = y \/ S x <== y) x foo bar _ h,
  simp,
  intros y' h1 h2,
  right,
  apply succ_le_succ,
  exact h1,
end


lemma le_dichotomy_zero {x: myint}: O <== x \/ x <== O :=
begin
  induction x with x' ih x' ih,
  simp,
  cases ih with ih ih,
  left,
  apply le_succ _ _ ih,
  note h := eq_or_lt_of_le ih,
  cases h with h h,
  left,
  apply le_succ,
  rw h,
  simp,
  right,
  exact h,
  cases ih with ih ih,
  note h := eq_or_lt_of_le ih,
  cases h with h h,
  rw -h,
  right,
  rw -succ_of_pred O,
  apply le_succ,
  simp,
  left,
  rw -pred_of_succ O,
  apply pred_le_pred _ _ h,
  right,
  rw -pred_of_succ O,
  apply pred_le_pred,
  apply le_succ,
  exact ih,
end


lemma le_of_add_le_add_right: forall x y k, x ++ k <== y ++ k -> x <== y :=
begin
  intros x y k h,
  note h2 := @add_le_add_right (x ++ k) (y ++ k) (neg k) h, clear h,
  repeat { rw add_assoc at h2 },
  simp at h2,
  exact h2,
end

lemma neg_le_neg {x y: myint}: x <== y -> neg y <== neg x :=
begin
  apply ind_on_nat,
  apply le_refl,
  intros y' h h1,
  simp,
  apply le_of_add_le_add_right _ _ (S O),
  simp,
  apply le_succ,
  exact h1,
end


lemma le_of_neg_le_neg {x y: myint} (h: neg x <== neg y): y <== x :=
begin
  note h2 := neg_le_neg h,
  simp at h2,
  exact h2,
end


lemma mul_le_mul_right_nonneg {x y k: myint}: O <== k -> x <== y -> x ** k <== y ** k :=
begin
  apply ind_on_nat (fun k, x <== y -> x ** k <== y ** k) O,
  intro h,
  simp,
  intros k' h h1 h2,
  simp,
  apply add_le_add,
  exact h1 h2,
  exact h2,
end


lemma mul_le_mul_right_nonpos {x y k: myint} (h1: k <== O) (h2: x <== y): y ** k <== x ** k :=
begin
  apply le_of_neg_le_neg,
  repeat { rw -mul_neg },
  apply mul_le_mul_right_nonneg _ h2,
  apply le_of_neg_le_neg,
  simp,
  exact h1,
end


lemma either_zero_of_mul_eq_zero_nonneg {x y: myint}:
  O <== x -> O <== y -> x ** y = O -> x = O \/ y = O :=
begin
  apply ind_on_nat (fun x, O <== y -> x ** y = O -> _ \/ _),
  simp,
  intros x' h,
  simp,
  intros h1 h2 h3,
  left,
  revert h2 h3,
  apply ind_on_nat (fun y, _ ** y = O -> _ = O);
  simp,
  intros y' h2 h3 h4,
  rw mul_comm at h4,
  simp at h4,
  assert hfalse: false,
  apply not_succ_le O,
  apply @eq.rec _ _ (fun x, S O <== x) _ _ h4,
  apply succ_le_succ,
  rw -add_of_zero O,
  apply add_le_add,
  rw -add_of_zero O,
  apply add_le_add,
  apply le_trans,
  show O <== O ** x',
  rw mul_comm,
  simp,
  apply mul_le_mul_right_nonneg,
  all_goals { try { assumption } },
  contradiction,
end


theorem either_zero_of_mul_eq_zero {x y: myint}:
  x ** y = O -> x = O \/ y = O :=
begin
  assert dich: forall x, O <== x \/ O <== neg x,
  {
    intro x,
    cases @le_dichotomy_zero x with h h,
    left,
    exact h,
    right,
    apply le_of_neg_le_neg,
    simp,
    exact h,
  },
  assert neg_zero: forall x, neg x = O <-> x = O,
  {
    intro x,
    split,
    intro h,
    rw -@neg_of_neg x,
    rw h,
    simp,
    intro h,
    rw h,
    simp,
  },
  intro h,
  cases dich x with h1 h1;
  cases dich y with h2 h2,

  apply either_zero_of_mul_eq_zero_nonneg; assumption,

  rw -neg_zero y,
  apply either_zero_of_mul_eq_zero_nonneg,
  exact h1,
  exact h2,
  simp,
  rw h,
  simp,

  rw -neg_zero x,
  apply either_zero_of_mul_eq_zero_nonneg,
  exact h1,
  exact h2,
  rw mul_comm,
  simp,
  rw mul_comm,
  rw h,
  simp,

  rw -neg_zero x,
  rw -neg_zero y,
  apply either_zero_of_mul_eq_zero_nonneg,
  exact h1,
  exact h2,
  simp,
  rw mul_comm,
  simp,
  rw mul_comm,
  exact h,
end


end myint
