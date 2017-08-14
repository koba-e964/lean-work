inductive prim_rec: nat -> Type
| zero: prim_rec 0
| succ: prim_rec 1
| proj: forall {n}, fin n -> prim_rec n
| comp: forall {k m}, prim_rec k -> (fin k -> prim_rec m) -> prim_rec m
| prec: forall {k}, prim_rec k -> prim_rec (k + 2) -> prim_rec (k + 1)


def curry {k} (v: nat) (a: fin k -> nat): fin (k + 1) -> nat :=
begin
  intro arg,
  cases arg with val is_lt,
  cases val with val',
  exact v, -- arg(0) = v
  apply a,
  existsi val',
  apply nat.lt_of_succ_lt_succ,
  exact is_lt,
end


def uncurry {k} (a: fin (k + 1) -> nat): prod nat (fin k -> nat) :=
begin
  split,
  exact a 0,
  intro arg,
  cases arg with val is_lt,
  apply a,
  split,
  show val + 1 < k + 1,
  apply nat.succ_lt_succ,
  exact is_lt,
end


lemma curry_of_uncurry: forall {k} (a: fin (k + 1) -> nat),
  a = let p := uncurry a in
      curry p.fst p.snd :=
begin
  intros k a,
  apply funext,
  intro arg,
  cases arg with val is_lt,
  cases val with val',
  reflexivity,
    show a ⟨nat.succ val', is_lt⟩ =
  curry ((uncurry a).fst) ((uncurry a).snd) ⟨val' + 1, is_lt⟩,
  unfold curry,
  simp,
  reflexivity,
end


def prim_eval : forall {k}, prim_rec k -> (fin k -> nat) -> nat
| 0 prim_rec.zero _arg := 0
| 1 prim_rec.succ arg := arg 0 + 1
| m (prim_rec.proj idx) arg := arg idx
| m (@prim_rec.comp k .(m) (f: prim_rec k) g) arg
  := prim_eval f (fun i, prim_eval (g i) arg)
| .(_) (@prim_rec.prec k f g) arg :=
  let h :=
  fun (v: nat) (arg: fin k -> nat),
  @nat.rec (fun _, nat) (prim_eval f arg)
    (fun (v': nat) (prev: nat), prim_eval g (curry prev (curry v' arg))) v in
  let ⟨x, y⟩ := uncurry arg in
  h x y


lemma succ_succ : forall x, prim_eval prim_rec.succ (fun _, x) = x + 1 :=
begin
  intro x,
  unfold prim_eval,
  reflexivity,
end


example : prim_eval prim_rec.zero (fun _, 0) = 0 :=
begin
  reflexivity,
end


example : forall x, prim_eval (prim_rec.prec prim_rec.zero
  (prim_rec.comp prim_rec.succ (fun _, prim_rec.proj 0))) (fun _, x) = x :=
begin
  intro x,
  induction x with x' ih,
  reflexivity,
  show prim_eval (prim_rec.prec prim_rec.zero (prim_rec.comp prim_rec.succ (fun (_ : fin 1), prim_rec.proj 0)))
      (fun (_ : fin 1), nat.succ x') =
    x' + 1,
  unfold prim_eval,
  unfold prim_eval at ih,
  dsimp,
  dsimp at ih,
  assert curry_1: forall v: nat, uncurry (fun _: fin 1, v) = ⟨v, fun _, 0⟩,
  admit,
  rw curry_1,
  rw curry_1 at ih,
  show prim_eval._match_1 0
      (fun (v : nat) (arg : fin 0 -> nat), nat.rec 0 (fun (v' prev :
        nat), curry prev (curry v' arg) 0 + 1) v)
      ((nat.succ x', fun _: fin 0, 0)) =
    x' + 1,
  unfold prim_eval._match_1,
  unfold prim_eval._match_1 at ih,
  dsimp,
  dsimp at ih,
  rw ih,
  assert curry_at_0: forall k v (rest: fin k -> nat), curry v rest 0 = v,
  admit,
  rw curry_at_0,
end


def prim_depth: forall {k}, prim_rec k -> nat :=
sorry


def sum_of_fin: forall {n}, (fin n -> nat) -> nat :=
begin
  intro n,
  induction n with n' sof,
  { intro _, exact 0 },
  intro ls,
  exact sof (fun x, ls (fin.succ x)) + ls 0,
end


theorem ack_dominates_prim_rec:
  forall k, forall f: prim_rec k,
  forall arg: fin k -> nat,
  ack (prim_depth f) (sum_of_fin arg) >= prim_eval f arg :=
sorry
