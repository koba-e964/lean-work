import .fin_seq

inductive prim_rec: nat -> Type
| zero: prim_rec 0
| succ: prim_rec 1
| proj: forall {n}, fin n -> prim_rec n
| comp: forall {k m}, prim_rec k -> (fin k -> prim_rec m) -> prim_rec m
| prec: forall {k}, prim_rec k -> prim_rec (k + 2) -> prim_rec (k + 1)

namespace prim_rec

def eval : forall {k}, prim_rec k -> (fin k -> nat) -> nat
| 0 prim_rec.zero _arg := 0
| 1 prim_rec.succ arg := arg 0 + 1
| m (prim_rec.proj idx) arg := arg idx
| m (@prim_rec.comp k .(m) (f: prim_rec k) g) arg
  := eval f (fun i, eval (g i) arg)
| .(_) (@prim_rec.prec k f g) arg :=
  let h :=
  fun (v: nat) (arg: fin k -> nat),
  @nat.rec (fun _, nat) (eval f arg)
    (fun (v': nat) (prev: nat), eval g (fin_seq.push prev (fin_seq.push v' arg))) v in
  let ⟨x, y⟩ := fin_seq.pop arg in
  h x y

def sum_of_fin: forall {n}, fin_seq n nat -> nat
| 0 _ := 0
| (n' + 1) ls := sum_of_fin (fun i, ls (fin.succ i)) + ls 0

def size_of: forall {k}, prim_rec k -> nat
| 0 prim_rec.zero := 1
| 1 prim_rec.succ := 1
| m (prim_rec.proj idx) := 1
| m (@prim_rec.comp k .(m) (f: prim_rec k) g)
  := size_of f + sum_of_fin (λi, size_of (g i)) + 1
| .(_) (@prim_rec.prec k f g) :=
  size_of f + size_of g + 1

@[simp] lemma zero.is_zero: eval zero fin_seq.empty = 0 :=
begin
  reflexivity,
end

lemma zero.size: size_of zero = 1 := rfl

def const: nat -> prim_rec 0
| 0 := zero
| (k + 1) := comp succ ({const k}: fin_seq _ _) 

@[simp] def const.is_const: forall x, eval (const x) fin_seq.empty = x :=
begin
  intro x,
  induction x with x' ih,
  { reflexivity },
  {
    simp [eval, const],
    rw ih,
  },
end

lemma const.size: forall x, size_of (const x) = x * 2 + 1 :=
begin
  intro x,
  induction x with x' ih,
  reflexivity,
  simp [size_of, const],
  change 1 + sum_of_fin ({size_of (const x')}) + 1 = x'.succ * 2 + 1,
  rw ih,
  simp [sum_of_fin],
  rw nat.zero_add,
  rw nat.add_comm 1 _,
  rw nat.succ_mul x',
end


@[simp] lemma succ.is_succ: forall x, eval prim_rec.succ ({x}: fin_seq _ _) = x + 1 :=
fun x,
calc
  eval prim_rec.succ ({x}: fin_seq _ _) = x + 1 : by unfold eval; reflexivity

lemma succ.size: size_of succ = 1 := rfl

lemma uncurry_1: forall v: nat, fin_seq.pop {v} = ⟨v, fin_seq.empty⟩ :=
  fin_seq.pop_1

lemma curry_at_0: forall k v (rest: fin k -> nat), fin_seq.push v rest 0 = v :=
begin
  apply fin_seq.push_at_0
end

lemma curry_at_succ: forall k v (rest: fin k -> nat) (i: fin k), fin_seq.push v rest (fin.succ i) = rest i
  :=
begin
  apply fin_seq.push_at_succ,
end

def id: prim_rec 1 := proj 0

@[simp] lemma id.is_id : forall x, eval id ({x}: fin_seq 1 nat) = x :=
begin
  intro x,
  reflexivity,
end

lemma id.size: size_of id = 1 := rfl

def pred: prim_rec 1 := prec zero (proj 1)

@[simp] lemma pred.is_pred: forall x, eval pred ({x}: fin_seq _ _) = x - 1 :=
begin
  intro x,
  cases x with x',
  { reflexivity },
  { reflexivity },
end

lemma pred.size: size_of pred = 3 := rfl

def is_zero: prim_rec 1 := prec (const 1) (comp zero (fun _, proj 0))

@[simp] lemma is_zero.is_is_zero: forall x, eval is_zero ({x}: fin_seq 1 nat) = if x = 0 then 1 else 0 :=
begin
  intro x,
  cases x with x',
  { reflexivity },
  { reflexivity },
end

@[simp] lemma is_zero.is_is_zero_bulk: forall (xs: fin_seq 1 nat), eval is_zero xs = if xs 0 = 0 then 1 else 0 :=
begin
  intro xs,
  rw <- fin_seq.length_1_of_singleton xs,
  rw is_zero.is_is_zero,
  simp,
end

lemma is_zero.size: size_of is_zero = 6 := rfl

-- S(x) + y = S(x + y)
def add: prim_rec 2 := prec id (comp succ ({proj 0}: fin_seq _ _))
-- sub_rev(x, y) = y - x
def sub_rev: prim_rec 2 := prec id (comp pred ({proj 0}: fin_seq _ _))
def sub: prim_rec 2 := comp sub_rev (fin_seq.push (proj 1) {proj 0})
def mul: prim_rec 2 := prec (comp zero (fun _, succ)) (comp add (fin_seq.push (proj 0) {proj 2}))

-- logic
def le: prim_rec 2 := comp is_zero ({sub}: fin_seq _ _)
def ge: prim_rec 2 := comp is_zero ({sub_rev}: fin_seq _ _)
-- and(x, y) = if x != 0 then y else 0
def and: prim_rec 2 := prec (comp zero (fun _, proj 0)) (proj 2)
-- or(x, y) = if x != 0 then x else y
def or: prim_rec 2 := prec id (comp succ ({proj 1}: fin_seq _ _))
def not: prim_rec 1 := is_zero
-- cond(x, y, z) = if x != 0 then y else z
def cond: prim_rec 3 := prec (proj 1) (proj 2)
-- def eq: prim_rec 2 := comp and (fin_seq.push le {ge})
def eq: prim_rec 2 := comp is_zero ({comp add (fin_seq.push sub {sub_rev})}: fin_seq _ _)

@[simp] lemma add.is_add: forall x y, eval add (fin_seq.push x {y}) = x + y :=
begin
  intro x,
  induction x with x' ih,
  {
    intro y,
    rw nat.add_comm,
    rw nat.add_zero,
    simp [add, eval],
    reflexivity,
  },
  {
    intro y,
    change add.eval (fin_seq.push x' {y}) + 1 = x'.succ + y,
    rw ih,
    rw nat.add_comm x'.succ y,
    rw nat.add_succ y x',
    rw nat.add_comm y x',
  },
end

@[simp] lemma add.is_add_bulk: forall xy, eval add xy = xy 0 + xy 1 :=
begin
  intro xy,
  rw <- fin_seq.length_2_of_insert_of_singleton xy,
  apply add.is_add,
end


lemma add.size: size_of add = 5 := rfl

@[simp] lemma sub_rev.is_sub_rev: forall x y, eval sub_rev (fin_seq.push x {y}) = y - x :=
begin
  intro x,
  induction x with x' ih,
  {
    intro y,
    simp [sub_rev, eval],
    reflexivity,
  },
  {
    intro y,
    change pred.eval ({sub_rev.eval (fin_seq.push x' {y})}: fin_seq _ _) = y - x'.succ,
    simp,
    rw ih,
    reflexivity,
  },
end

lemma sub_rev.size: size_of sub_rev = 7 := rfl

@[simp] lemma sub_rev.is_sub_rev_bulk: forall xy, eval sub_rev xy = xy 1 - xy 0 :=
begin
  intro xy,
  rw <- fin_seq.length_2_of_insert_of_singleton xy,
  apply sub_rev.is_sub_rev,
end

@[simp] lemma sub.is_sub: forall x y, eval sub (fin_seq.push x {y}) = x - y :=
begin
  simp only [eval, sub],
  simp [sub_rev.is_sub_rev_bulk, eval],
  intros x y,
  reflexivity,
end

lemma sub.size: size_of sub = 10 := rfl

@[simp] lemma mul.is_mul: forall x y, eval mul (fin_seq.push x {y}) = x * y :=
begin
  intro x,
  induction x with x' ih; intro y,
  {
    change 0 = 0 * y,
    rw nat.zero_mul,
  },
  {
    simp only [mul, eval],
    change add.eval (fin_seq.push (mul.eval (fin_seq.push x' {y})) ({y}: fin_seq _ _)) = x'.succ * y,
    rw ih,
    rw add.is_add,
    rw nat.succ_mul,
  },
end

lemma mul.size: size_of sub = 10 := rfl

@[simp] lemma le.is_le: forall x y, eval le (fin_seq.push x {y}) = if x <= y then 1 else 0 :=
begin
  simp [le, eval],
  intros x y,
  apply if_congr,
  rw @nat.sub_eq_zero_iff_le x y,
  simp,
end

lemma le.size: size_of le = 17 := rfl

@[simp] lemma ge.is_ge: forall x y, eval ge (fin_seq.push x {y}) = if x >= y then 1 else 0 :=
begin
  simp [ge, eval],
  intros x y,
  apply if_congr,
  change y - x = 0 <-> x >= y,
  rw nat.sub_eq_zero_iff_le,
  simp,
end

lemma ge.size: size_of ge = 14 := rfl

@[simp] lemma and.is_and: forall x y, eval and (fin_seq.push x {y}) = if x ≠ 0 then y else 0 :=
begin
  intros x y,
  cases x with x'; reflexivity,
end

lemma and.size: size_of and = 4 := rfl

@[simp] lemma or.is_or: forall x y, eval or (fin_seq.push x {y}) = if x ≠ 0 then x else y :=
begin
  intros x y,
  cases x with x'; reflexivity,
end

lemma or.size: size_of or = 5 := rfl

@[simp] lemma not.is_not: forall x, eval not ({x}: fin_seq _ _) = if x ≠ 0 then 0 else 1 :=
begin
  intros x,
  cases x with x'; reflexivity,
end

lemma not.size: size_of not = 6 := rfl

@[simp] lemma cond.is_cond: forall (x y z: nat), eval cond (fin_seq.push x (fin_seq.push y ({z}: fin_seq 1 nat))) = if x ≠ 0 then y else z :=
begin
  intros x y z,
  cases x with x'; reflexivity,
end

lemma cond.size: size_of cond = 3 := rfl

@[simp] lemma eq.is_eq: forall x y, eval eq (fin_seq.push x {y}) = if x = y then 1 else 0 :=
begin
  intros x y,
  simp [eval, eq],
  apply if_congr,
  change (x - y) + eval sub_rev (fin_seq.push x {y}) = 0 <-> x = y,
  rw sub_rev.is_sub_rev,
  change (x - y) + (y - x) = 0 <-> x = y,
  split,
  {
    intro h,
    have := nat.eq_zero_of_add_eq_zero h,
    cases this with h1 h2,
    apply nat.le_antisymm,
    apply nat.le_of_sub_eq_zero h1,
    apply nat.le_of_sub_eq_zero h2,
  },
  {
    intro h,
    cases h,
    rw nat.sub_self,
  },
  simp,
end

lemma eq.size: size_of eq = 30 := rfl

end prim_rec
