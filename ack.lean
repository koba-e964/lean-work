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
    intro n,
    calc
      n   < n + 1 : nat.le_refl _
      ... = ack 0 n : by simp [ack]
  },
  show forall n, n < ack (m' + 1) n,
  {
    intro n,
    induction n with n' ih2,
    show 0 < ack (m' + 1) 0,
    {
      calc
        0   < 1 : nat.le_refl 1
        ... < ack m' 1 : ih 1
        ... = ack (m' + 1) 0 : by simp [ack]
    },
    show n' + 1 < ack (m' + 1) (n' + 1),
    {
      calc
        n' + 1 <= ack (m' + 1) n' : ih2
           ... <  ack m' (ack (m' + 1) n') : by apply ih
           ... =  ack (m' + 1) (n' + 1) : by simp [ack]
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
    show m' + 1 < ack (m'+ 1) 0,
    {
      calc
        m' + 1 < ack m' 1 : by apply ih
           ... = ack (m' + 1) 0 : by simp [ack]
    },
    show m' + 1 + n' + 1 < ack (m' + 1) (n' + 1),
    {
      calc
        m' + 1 + n' + 1 <= m' + (m' + 1 + n' + 1) : by apply nat.le_add_left
                    ... <= m' + ack (m' + 1) n' :
                           by apply nat.add_le_add_left ih2
                    ... < ack m' (ack (m' + 1) n') : by apply ih
                    ... = ack (m' + 1) (n' + 1) : by simp [ack]
    },
  }
end


lemma ack_2nd_succ: forall m n, ack m n < ack m (n + 1) :=
begin
  intros m,
  induction m with m' ih,
  show forall n, ack 0 n < ack 0 (n + 1),
  {
    intro n,
    calc
      ack 0 n = n + 1 : by simp [ack]
          ... < n + 2 : by apply nat.le_refl
          ... = ack 0 (n + 1) : by simp [ack]
  },
  show forall n, ack (m' + 1) n < ack (m' + 1) (n + 1),
  {
    intro n,
    calc
      ack (m' + 1) n < ack m' (ack (m' + 1) n) : by apply ack_2nd_lt_val
                 ... = ack (m' + 1) (n + 1) : by simp [ack]
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
    calc
      ack m (n' + 1) <= ack m (m + 1 + n') :
            by apply ack_2nd_incr_eq; simp; apply nat.le_add_left
                 ... <  ack m (ack (m + 1) n') :
            by apply ack_2nd_incr; apply ack_argsum_lt_val
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
    calc
      ack m (n' + 2) <= ack m (ack (m + 1) n') :
        begin
          apply ack_2nd_incr_eq,
          calc
            n' + 2 <= m + 1 + n' + 1 : by simp; apply nat.le_add_left
               ... <= ack (m + 1) n' : by apply ack_argsum_lt_val
        end
                 ... =  ack (m + 1) (n' + 1) : by simp [ack]
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
    calc
      b   <= max a b : by apply le_max_right
      ... <= max a b + 1 : by apply nat.le_succ
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
  calc
    ack 1 (n' + 1) = (ack 1 n') + 1 : by simp [ack]
               ... = n' + 3 : by rw ih
end


lemma ack_2_n: forall n, ack 2 n = 2 * n + 3 :=
begin
  intro n,
  induction n with n' ih,
  show ack 2 0 = 3, { simp [ack], },
  show ack 2 (n' + 1) = 2 * n' + 5,
  calc
    ack 2 (n' + 1) = ack 1 (ack 2 n') : by simp [ack]
               ... = ack 2 n' + 2 : by rw ack_1_n
               ... = 2 * n' + 5 : by rw ih
end  


lemma ack_lemma_7: forall n x y,
  x >= 3 -> (n + 1) * ack x y <= ack x (y + n) :=
begin
  intros n x y hlt,
  induction n with n' ih2,
  show 1 * ack x y <= ack x y, { simp },
  show (n' + 2) * ack x y <= ack x (y + n' + 1),
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
  calc
    (n' + 2) * ack x y <= 2 * (n' + 1) * ack x y :
                          begin
                            apply nat.mul_le_mul_right,
                            calc
                              n' + 2 <= 1 * n' + n' + 2 :
                                        by apply nat.le_add_left
                                 ... =  2 * n' + 2 : by rw nat.succ_mul 1
                                 ... =  2 * (n' + 1) : by reflexivity,
                          end
                   ... =  2 * ((n' + 1) * ack x y) : by rw mul_assoc
                   ... <= 2 * ack x (y + n') : by
                          apply nat.mul_le_mul_left;
                          exact ih2
                   ... =  2 * ack (x' + 1) (y + n') : by rw xsucc
                   ... <= ack 2 (ack (x' + 1) (y + n')) : by
                          rw ack_2_n; apply nat.le_add_right
                   ... <= ack x' (ack (x' + 1) (y + n')) :
                          by apply ack_1st_incr_eq; exact x'ge2
                   ... =  ack (x' + 1) (y + n' + 1) : by simp only [ack]
                   ... =  ack x (y + n' + 1) : by rw xsucc
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
    calc
      ack 2 n = 2 * n + 3 : by rw ack_2_n
          ... > 2 * n + 2 : by apply nat.le_refl
          ... = ack 1 (2 * n) : by rw ack_1_n
  },
  show forall n, ack (m + 1) n > ack m (2 * n),
  intro n,
  induction n with n' ih2,
  show ack (m + 1) 0 > ack m 0, { apply ack_1st_succ },
  show ack (m + 1) (n' + 1) > ack m (2 * n' + 2),
  calc
    ack (m + 1) (n' + 1) =  ack m (ack (m + 1) n') : by simp [ack]
                    ...  >  ack m (ack m (2 * n')) : by
                            apply ack_2nd_incr; apply ih2
                    ...  >= ack m (2 * n' + 2) :
                           begin
                             apply ack_2nd_incr_eq,
                             calc
                               ack m (2 * n') >= ack 1 (2 * n') :
                                                 begin
                                                   apply ack_1st_incr_eq,
                                                   exact mge1
                                                 end
                                          ... =  2 * n' + 2 : by rw ack_1_n
                           end
end
