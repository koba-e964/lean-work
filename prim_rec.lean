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

lemma zero.is_zero: eval zero fin_seq.empty = 0 :=
begin
  reflexivity,
end

lemma succ.is_succ: forall x, eval prim_rec.succ (fun _, x) = x + 1 :=
fun x,
calc
  eval prim_rec.succ (fun _, x) = x + 1 : by unfold eval; reflexivity

lemma uncurry_1: forall v: nat, fin_seq.pop (fun _: fin 1, v) = ⟨v, fin_seq.empty⟩ :=
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
  (prim_rec.comp prim_rec.succ (fun _, prim_rec.proj 0))


lemma id.is_id : forall x, eval id (fun _, x) = x :=
begin
  intro x,
  induction x with x' ih,
  reflexivity,
  show eval id
      (fun _ : fin 1, x' + 1) =
    x' + 1,
  calc
    eval id
      (fun _ : fin 1, x' + 1)
    = eval id
      (fun _ : fin 1, x') + 1 : by reflexivity
... = x' + 1 :
      by rw ih
end

end prim_rec
