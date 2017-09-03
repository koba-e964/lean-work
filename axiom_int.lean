constant myint: Type

namespace myint

constant zero: myint
constant succ: myint -> myint
constant pred: myint -> myint
constant add: myint -> myint -> myint
constant mul: myint -> myint -> myint
constant neg: myint -> myint


noncomputable def has_add: has_add myint :=
⟨add⟩

-- def has_add: has_add myint := sorry

notation `O` := zero
notation `S` := succ
notation `P` := pred
reserve infixl ` ++ `:65
reserve infixl ` ** `:67
notation a `++` b := add a b
notation a `**` b := mul a b
notation `neg` := neg

axiom succ_of_pred: forall x, S (P x) = x
axiom pred_of_succ: forall x, P (S x) = x
axiom add_of_zero: forall x: myint, add x zero = x
axiom add_of_succ: forall x y, add x (S y) = S (add x y)
axiom add_of_pred: forall x y, add x (P y) = P (add x y)

axiom neg_of_zero: neg zero = zero
axiom neg_of_succ: forall x, neg (S x) = P (neg x)
axiom neg_of_pred: forall x, neg (P x) = S (neg x)


axiom mul_of_zero: forall x, x ** zero = zero
axiom mul_of_succ: forall x y, x ** S y = add (x ** y) x
axiom mul_of_pred: forall x y, x ** P y = add (x ** y) (neg x)


axiom rec: forall Q: myint -> Prop,
  Q zero -> (forall x, Q x -> Q (S x)) -> (forall x, Q x -> Q (P x)) -> forall x, Q x


@[simp]
lemma succ_of_pred_simp: forall x, S (P x) = x := succ_of_pred
@[simp]
lemma pred_of_succ_simp: forall x, P (S x) = x := pred_of_succ
@[simp]
lemma add_of_zero_simp: forall x, x ++ O = x := add_of_zero
@[simp]
lemma add_of_succ_simp: forall x y, x ++ S y = S (x ++ y) := add_of_succ
@[simp]
lemma add_of_pred_simp: forall x y, x ++ P y = P (x ++ y) := add_of_pred

@[simp]
lemma neg_of_zero_simp: neg O = O := neg_of_zero
@[simp]
lemma neg_of_succ_simp: forall x, neg (S x) = P (neg x) := neg_of_succ
@[simp]
lemma neg_of_pred_simp: forall x, neg (P x) = S (neg x) := neg_of_pred

@[simp]
lemma mul_of_zero_simp: forall x, x ** O = O := mul_of_zero
@[simp]
lemma mul_of_succ_simp: forall x y, x ** S y = x ** y ++ x := mul_of_succ
@[simp]
lemma mul_of_pred_simp: forall x y, x ** P y = x ** y ++ neg x := mul_of_pred


lemma add_comm: forall x y: myint, add x y = add y x :=
begin
  intro x,
  induction x with x' ih x' ih,
  intro y,
  induction y with y' ih2 y' ih2,
  reflexivity,
  rw add_of_succ,
  rw ih2,
  simp,
  rw add_of_pred,
  rw ih2,
  simp,

  intro y,
  induction y with y' ih2 y' ih2,
  rw add_of_zero,
  simp,
  rw -ih O,
  simp,
  simp,
  rw ih2,
  rw -ih,
  simp,
  rw ih,
  simp,
  rw ih2,
  rw -ih,
  simp,
  rw ih,

  intro y,
  induction y with y' ih2 y' ih2,
  simp,
  rw -ih,
  simp,
  simp [ih2],
  rw -ih, rw -ih,
  simp,
  simp [ih2],
  rw -ih, rw -ih,
  simp,
end


lemma add_assoc: forall x y z: myint, (x ++ y) ++ z = x ++ (y ++ z) :=
fun x y z,
begin
  induction z with z' ih z' ih;
  { simp [ih] <|> simp },
end


@[simp]
lemma add_of_neg: forall x, x ++ neg x = O :=
fun x,
begin
  induction x,
  simp,
  simp,
  rw add_comm,
  simp,
  rw add_comm,
  rw a,
  simp,
  rw add_comm,
  simp,
  rw add_comm,
  rw a,
end


@[simp]
lemma neg_of_neg {x: myint}: neg (neg x) = x :=
begin
  induction x with x' ih x' ih;
  { simp [ih] <|> simp },
end


lemma neg_of_add {x y: myint}: neg x ++ neg y = neg (x ++ y) :=
begin
  induction y with y' ih y' ih;
  { simp [ih] <|> simp },
end


@[simp]
lemma mul_neg {x y: myint}: x ** neg y = neg (x ** y) :=
begin
  induction y with y' ih y' ih; simp,
  rw ih,
  rw neg_of_add,
  rw ih,
  rw -neg_of_add,
  simp,
end



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


end myint
