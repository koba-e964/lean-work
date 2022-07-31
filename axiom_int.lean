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
  rw <- ih O,
  simp,
  simp,
  rw ih2,
  rw <- ih,
  simp,
  rw ih,
  simp,
  rw ih2,
  rw <- ih,
  simp,
  rw ih,

  intro y,
  induction y with y' ih2 y' ih2,
  simp,
  rw <- ih,
  simp,
  simp [ih2],
  rw <- ih, rw <- ih,
  simp,
  simp [ih2],
  rw <- ih, rw <- ih,
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
  induction x with _ a _ a,
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


lemma mul_comm {x y: myint}: x ** y = y ** x :=
begin
  revert y,
  induction x with x' ih x' ih; intro y,
  induction y with y' ih y' ih;
  { simp [ih] <|> simp },

  all_goals {
    induction y with y' ih2 y' ih2,
    simp,
    rw <- ih,
    simp,
    all_goals {
      simp,
      rw ih2,
      simp,
      rw <- ih,
      rw <- ih,
      simp,
      repeat { rw add_assoc },
      repeat { apply congr_arg },
      rw add_comm,
    },
  },
end


lemma mul_add_dist_right {x y z: myint}: x ** z ++ y ** z = (x ++ y) ** z :=
begin
  induction z with z' ih z' ih,
  simp,
  all_goals {
    simp,
    rw <- ih,
    repeat { rw add_assoc },
    rw <- add_assoc _ (y ** z'),
    rw add_comm _ (y ** z'),
    rw add_assoc (y ** z'),
  },
  repeat { apply congr_arg },
  apply neg_of_add,
end


lemma mul_add_dist_left {x y z: myint}: x ** y ++ x ** z = x ** (y ++ z) :=
begin
  repeat { rw @mul_comm x },
  exact mul_add_dist_right,
end


@[simp]
lemma mul_neg {x y: myint}: x ** neg y = neg (x ** y) :=
begin
  induction y with y' ih y' ih; simp,
  rw ih,
  rw neg_of_add,
  rw ih,
  rw <- neg_of_add,
  simp,
end


lemma mul_assoc {x y z: myint}: x ** y ** z = x ** (y ** z) :=
begin
  induction z with z' ih z' ih,
  simp,
  simp [ih],
  rw mul_add_dist_left,
  simp [ih],
  rw <- mul_add_dist_left,
  simp,
end


end myint
