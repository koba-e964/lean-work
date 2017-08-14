def ack: nat -> nat -> nat
| 0 n := n + 1
| (m + 1) 0 := ack m 1
| (m + 1) (n + 1) := ack m (ack (m + 1) n)


lemma ack_2nd_lt_val: forall m n, n < ack m n :=
begin
  intro m,
  induction m with m' ih,
  show forall n, n < ack 0 n,
  {
    simp [ack],
    intro n,
    apply nat.le_refl
  },
  show forall n, n < ack (m' + 1) n,
  {
    intro n,
    induction n with n' ih2,
    show 0 < ack (m' + 1) 0,
    {
      simp [ack],
      transitivity 1,
      apply nat.le_refl,
      apply ih,
    },
    show n' + 1 < ack (m' + 1) (n' + 1),
    {
      simp [ack],
      show n' + 2 <= ack m' (ack (m' + 1) n'),
      transitivity ack (m' + 1) n' + 1,
      note ih2': n' + 1 <= ack (m' + 1) n' := ih2,
      apply add_le_add_right ih2' 1,
      apply ih,
    },
  }
end


lemma ack_argsum_lt_val: forall m n, m + n < ack m n :=
begin
  intro m,
  induction m with m' ih,
  show forall n, 0 + n < ack 0 n,
  {
    intro n,
    rw add_comm,
    apply ack_2nd_lt_val,
  },
  show forall n, m' + 1 + n < ack (m' + 1) n,
  {
    intro n,
    induction n with n' ih2,
    {
      show m' + 1 < ack (m' + 1) 0,
      simp [ack],
      apply ih,
    },
    {
      show m' + 1 + n' + 1 < ack (m' + 1) (n' + 1),
      simp [ack],
      apply nat.lt_of_le_of_lt,
      show m' + ack (m' + 1) n' < ack m' (ack (m' + 1) n'), { apply ih },
      show m' + n' + 2 <= m' + ack (m' + 1) n',
      repeat { rw nat.add_assoc },
      apply add_le_add_left,
      show n' + 2 ≤ ack (m' + 1) n',
      transitivity m' + 1 + n' + 1,
      show m' + 1 + n' + 1 <= ack (m' + 1) n', { exact ih2 },
      show n' + 2 <= m' + 1 + n' + 1,
      simp,
      apply nat.le_add_left,
    },
  }
end


lemma ack_2nd_succ: forall m n, ack m n < ack m (n + 1) :=
begin
  intros m,
  induction m with m' ih,
  show forall n, ack 0 n < ack 0 (n + 1),
  {
    simp [ack],
    apply add_lt_add_left,
    apply nat.le_refl
  },
  show forall n, ack (m' + 1) n < ack (m' + 1) (n + 1),
  {
    intro n,
    simp [ack],
    apply ack_2nd_lt_val,
  }
end


lemma ack_2nd_incr: forall m n p, n < p -> ack m n < ack m p :=
begin
  intros m n p hlt,
  induction hlt with p' ih,
  show ack m n < ack m (n + 1), { apply ack_2nd_succ },
  show ack m n < ack m (p' + 1),
  {
    transitivity,
    assumption,
    apply ack_2nd_succ,
  }
end


lemma ack_2nd_incr_eq: forall m n p, n <= p -> ack m n <= ack m p :=
begin
  intros m n p hle,
  cases nat.eq_or_lt_of_le hle with heq hlt,
  {
    rw heq,
  },
  {
    apply le_of_lt,
    apply ack_2nd_incr,
    assumption,
  }
end


lemma ack_1st_succ: forall m n, ack m n < ack (m + 1) n :=
begin
  intros m n,
  induction n with n' ih; simp [ack],
  show ack m 0 < ack m 1, { apply ack_2nd_succ },
  show ack m (n' + 1) < ack m (ack (m + 1) n'),
  {
    apply nat.lt_of_le_of_lt,
    {
      show ack m (n' + 1) <= ack m (m + 1 + n'),
      apply ack_2nd_incr_eq, simp,
      apply nat.le_add_left,
    },
    {
      show ack m (m + 1 + n') < ack m (ack (m + 1) n'),
      apply ack_2nd_incr,
      apply ack_argsum_lt_val,
    },
  },
end


lemma ack_1st_incr: forall l m n, l < m -> ack l n < ack m n :=
begin
  intros l m n hlt,
  induction hlt with m' ih,
  show ack l n < ack (l + 1) n, { apply ack_1st_succ },
  show ack l n < ack (m' + 1) n,
  {
    transitivity,
    assumption,
    apply ack_1st_succ
  }
end


lemma ack_1st_incr_eq: forall l m n, l <= m -> ack l n <= ack m n :=
begin
  intros l m n hle,
  cases nat.eq_or_lt_of_le hle with heq hlt,
  {
    rw heq,
  },
  {
    apply le_of_lt,
    apply ack_1st_incr,
    assumption,
  }
end


lemma ack_arg_1st_prior: forall m n, ack m (n + 1) <= ack (m + 1) n :=
begin
  intros m n,
  cases n with n',
  show ack m 1 <= ack (m + 1) 0, { simp [ack] },
  show ack m (n' + 2) <= ack (m + 1) (n' + 1),
  {
    simp [ack],
    apply ack_2nd_incr_eq,
    show n' + 2 <= ack (m + 1) n',
    transitivity,
    show m + 1 + n' + 1 <= ack (m + 1) n', { apply ack_argsum_lt_val },
    show n' + 2 <= m + 1 + n' + 1,
    {
      simp,
      apply nat.le_add_left,
    }
  }
end


lemma ack_dual_app:
  forall a b y, ack a (ack b y) <= ack (max a b + 1) (y + 1) :=
begin
  intros a b y,
  simp only [ack],
  transitivity ack a (ack (max a b + 1) y),
  show ack a (ack b y) <= ack a (ack (max a b + 1) y),
  {
    apply ack_2nd_incr_eq,
    apply ack_1st_incr_eq,
    transitivity max a b,
    apply le_max_right,
    apply nat.le_succ,
  },
  show ack a (ack (max a b + 1) y) <= ack (max a b) (ack (max a b + 1) y),
  apply ack_1st_incr_eq,
  apply le_max_left,
end


lemma ack_1_n: forall n, ack 1 n = n + 2 :=
begin
  intro n,
  induction n with n' ih,
  show ack 1 0 = 2, { simp [ack], },
  show ack 1 (n' + 1) = n' + 3,
  simp [ack],
  rw ih,
  simp,
end


lemma ack_2_n: forall n, ack 2 n = 2 * n + 3 :=
begin
  intro n,
  induction n with n' ih,
  show ack 2 0 = 3, { simp [ack], },
  show ack 2 (n' + 1) = 2 * n' + 5,
  simp only [ack],
  rw ih,
  rw ack_1_n,
end  


lemma ack_lemma_7: forall n x y,
  x >= 3 -> (n + 1) * ack x y <= ack x (y + n) :=
begin
  intros n x y hlt,
  induction n with n' ih2,
  show 1 * ack x y <= ack x y, { simp },
  show (n' + 2) * ack x y <= ack x (y + n' + 1),
  transitivity 2 * ack x (y + n'),
  show (n' + 2) * ack x y <= 2 * ack x (y + n'),
  {
    transitivity 2 * (n' + 1) * ack x y,
    {
      apply nat.mul_le_mul_right,
      apply nat.add_le_add_right _ 2,
      show n' <= 2 * n',
      rw nat.succ_mul,
      apply nat.le_add_left,
    },
    rw nat.mul_assoc,
    apply nat.mul_le_mul_left,
    apply ih2,
  },
  show 2 * ack x (y + n') <= ack x (y + n' + 1),
  assert h: {x': nat // x' + 1 = x},
  {
    cases x with x',
    note hnotle: not (3 <= 0) := nat.not_succ_le_zero 2,
    contradiction,
    existsi x',
    reflexivity,
  },
  cases h with x' xsucc,
  assert x'ge2: x' >= 2,
  {
    apply nat.le_of_add_le_add_right,
    rw xsucc,
    exact hlt,
  },
  rw -xsucc,
  simp only [ack],
  transitivity ack 2 (ack (x' + 1) (y + n')),
  {
    rw ack_2_n,
    apply nat.le_add_right,
  },
  apply ack_1st_incr_eq,
  assumption,
end


lemma ack_lemma_8: forall m n, m >= 1 -> ack (m + 1) n > ack m (2 * n) :=
begin
  intros m n mge1,
  revert n,
  cases nat.eq_or_lt_of_le mge1 with heq hlt,
  cases heq,
  show forall n, ack 2 n > ack 1 (2 * n),
  {
    intro n,
    rw [ack_2_n, ack_1_n],
    apply nat.le_refl,
  },
  show forall n, ack (m + 1) n > ack m (2 * n),
  intro n,
  induction n with n' ih2,
  show ack (m + 1) 0 > ack m 0, { apply ack_1st_succ },
  show ack (m + 1) (n' + 1) > ack m (2 * n' + 2),
  transitivity ack m (ack m (2 * n')),
  show ack (m + 1) (n' + 1) > ack m (ack m (2 * n')),
  {
    simp only [ack],
    apply ack_2nd_incr,
    apply ih2,
  },
  show ack m (ack m (2 * n')) > ack m (2 * n' + 2),
  apply ack_2nd_incr,
  show ack m (2 * n') > 2 * n' + 2,
  apply nat.lt_of_lt_of_le,
  show 2 * n' + 2 < ack 2 (2 * n'),
  {
    generalize (2 * n') x,
    intro x,
    rw ack_2_n,
    show x + 3 <= 2 * x + 3,
    rw nat.succ_mul,
    apply nat.add_le_add_right,
    apply nat.le_add_left,
  },
  show ack 2 (2 * n') <= ack m (2 * n'),
  apply ack_1st_incr_eq,
  apply hlt,
end
