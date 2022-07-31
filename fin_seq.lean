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

instance : has_emptyc (fin_seq 0 nat) := ⟨empty⟩

instance {t: Type}: has_singleton t (fin_seq 1 t) := ⟨singleton⟩

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

@[simp] lemma empty_is_unique: forall x: fin_seq 0 nat, x = empty :=
begin
  intros x,
  apply funext,
  intro fin0,
  cases fin0 with val is_lt,
  cases is_lt,  
end

@[simp] lemma pop_of_push: forall {t k} (v: t) (a: fin_seq k t),
  pop (push v a) = (v, a) :=
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

@[simp] lemma pop_1: forall v: nat, pop (singleton v) = ⟨v, empty⟩ :=
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

@[simp] lemma push_at_0: forall {t k} v (rest: fin_seq k t), fin_seq.push v rest 0 = v :=
begin
  intros t k v rest,
  reflexivity,
end

@[simp] lemma push_at_succ: forall {t k} v (rest: fin_seq k t) (i: fin k), push v rest (fin.succ i) = rest i
  :=
begin
  intros t k v rest i,
  cases i with i is_lt,
  reflexivity,
end

@[simp] lemma singleton_at_0: forall {t} (v: t), ({v}: fin_seq 1 t) 0 = v :=
begin
  intros t v,
  reflexivity,
end

@[simp] lemma length_1_of_singleton: forall {t} (xs: fin_seq 1 t), ({xs 0}: fin_seq 1 _) = xs :=
begin
  intros t xs,
  apply funext,
  intro i,
  cases i with i is_lt,
  have := nat.le_of_lt_succ is_lt,
  have := nat.eq_zero_of_le_zero this,
  cases this,
  reflexivity,
end

@[simp] lemma length_2_of_insert_of_singleton: forall {t} (xs: fin_seq 2 t),
  fin_seq.push (xs 0) {xs 1} = xs :=
begin
  intros t xs,
  apply funext,
  intro i,
  induction i with i is_lt,
  cases is_lt with _ is_le,
  -- i = 1
  {
    reflexivity,
  },
  -- i = 0
  {
    cases is_le with _ is_le,
    -- i = 0
    {
      reflexivity,
    },
    -- i < 0
    {
      have := nat.not_succ_le_zero _ is_le,
      contradiction,
    },
  },
end

end fin_seq
