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

@[simp] lemma zero.is_zero: eval zero fin_seq.empty = 0 :=
begin
  reflexivity,
end

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

@[simp] lemma succ.is_succ: forall x, eval prim_rec.succ ({x}: fin_seq _ _) = x + 1 :=
fun x,
calc
  eval prim_rec.succ ({x}: fin_seq _ _) = x + 1 : by unfold eval; reflexivity

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


def id: prim_rec 1 := prim_rec.prec prim_rec.zero
  (prim_rec.comp prim_rec.succ ({prim_rec.proj 0}: fin_seq _ _))

@[simp] lemma id.is_id : forall x, eval id ({x}: fin_seq 1 nat) = x :=
begin
  intro x,
  induction x with x' ih,
  reflexivity,
  show eval id ({x' + 1}: fin_seq _ _) =
    x' + 1,
  calc
    eval id ({x' + 1}: fin_seq _ _)
    = eval id ({x'}: fin_seq _ _) + 1 : by reflexivity
... = x' + 1 :
      by rw ih
end

def pred: prim_rec 1 := prec zero (proj 1)

@[simp] lemma pred.is_pred: forall x, eval pred ({x}: fin_seq _ _) = x - 1 :=
begin
  intro x,
  cases x with x',
  { reflexivity },
  { reflexivity },
end

def is_zero: prim_rec 1 := prec (const 1) (comp zero (fun _, proj 0))

@[simp] lemma is_zero.is_is_zero: forall x, eval is_zero ({x}: fin_seq 1 nat) = if decidable.to_bool (x = 0) then 1 else 0 :=
begin
  intro x,
  cases x with x',
  { reflexivity },
  { reflexivity },
end

-- S(x) + y = S(x + y)
def add: prim_rec 2 := prec id (comp succ ({proj 0}: fin_seq _ _))
-- sub_rev(x, y) = y - x
def sub_rev: prim_rec 2 := prec id (comp pred ({proj 0}: fin_seq _ _))
def sub: prim_rec 2 := comp sub_rev (fin_seq.push (proj 1) {proj 0})
def mul: prim_rec 2 := prec (comp zero (fun _, succ)) (comp add (fin_seq.push (proj 1) {proj 2}))

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

end prim_rec
