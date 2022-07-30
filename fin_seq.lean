def fin_seq (k: nat) (t: Type) := fin k -> t

namespace fin_seq

def push {t k} (v: t) (a: fin_seq k t): fin_seq (k + 1) t
| ⟨val, is_lt⟩ :=
  begin
    cases val with val',
    exact v, -- arg(0) = v
    apply a,
    existsi val',
    apply nat.lt_of_succ_lt_succ,
    exact is_lt,
  end

def pop {t k} (a: fin_seq (k + 1) t): prod t (fin_seq k t) :=
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

def empty: fin_seq 0 nat := fun _, 0

def singleton {t: Type} (v: t): fin_seq 1 t := fun _, v

lemma push_of_pop: forall {t: Type} {k} (a: fin_seq (k + 1) t),
  a = let p := pop a in
      push p.fst p.snd :=
begin
  intros t k a,
  apply funext,
  intro arg,
  cases arg with val is_lt,
  cases val with val',
  reflexivity,
    show a ⟨nat.succ val', is_lt⟩ =
  push ((pop a).fst) ((pop a).snd) ⟨val' + 1, is_lt⟩,
  unfold push,
  reflexivity,
end

lemma empty_is_unique: forall x: fin_seq 0 nat, x = empty :=
begin
  intros x,
  apply funext,
  intro fin0,
  cases fin0 with val is_lt,
  cases is_lt,  
end

lemma pop_of_push: forall {t k} (v: t) (a: fin_seq k t),
  (v, a) = pop (push v a) :=
begin
  intros t k v a,
  simp [pop],
  have left: v = push v a 0,
  {
    reflexivity,
  },
  rw <- left,
  apply congr_arg,
  apply funext,
  intro x,
  cases x with val is_lt,
  reflexivity,
end

lemma pop_1: forall v: nat, pop (singleton v) = ⟨v, empty⟩ :=
begin
  intro v,
  simp [singleton],
  simp [pop],
  have : forall x: fin 0 -> nat, (v, x) = (v, empty),
  {
    intro x,
    rw empty_is_unique x,
  },
  apply this,
end

lemma push_at_0: forall {t k} v (rest: fin_seq k t), fin_seq.push v rest 0 = v :=
begin
  intros t k v rest,
  reflexivity,
end

lemma push_at_succ: forall {t k} v (rest: fin_seq k t) (i: fin k), push v rest (fin.succ i) = rest i
  :=
begin
  intros t k v rest i,
  cases i with i is_lt,
  reflexivity,
end

end fin_seq
