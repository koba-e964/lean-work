example : forall n m: nat, n + m = m + n :=
begin
  intros n,
  induction n with n' ih,
  show forall m, 0 + m = m + 0,
  {
    intro m,
    induction m with m' ih2,
    show 0 + 0 = 0 + 0, { reflexivity },
    show 0 + (m' + 1) = (m' + 1) + 0,
    calc
      0 + (m' + 1) = (0 + m') + 1 : by reflexivity
              ...  = (m' + 0) + 1 : by rw ih2
              ...  = m' + 1 : by reflexivity
              ...  = (m' + 1) + 0 : by reflexivity
  },
  show forall m, (n' + 1) + m = m + (n' + 1),
  intro m,
  induction m with m' ih2,
  show (n' + 1) + 0 = 0 + (n' + 1),
  {
    calc
      (n' + 1) + 0 = n' + 1 : by reflexivity
               ... = (n' + 0) + 1 : by reflexivity
               ... = (0 + n') + 1 : by rw ih
               ... = 0 + (n' + 1) : by reflexivity
  },
  show (n' + 1) + (m' + 1) = (m' + 1) + (n' + 1),
  calc
    (n' + 1) + (m' + 1) = (n' + 1) + m' + 1 : by reflexivity
                   ...  = m' + (n' + 1) + 1 : by rw ih2
                   ...  = m' + n' + 2 : by reflexivity
                   ...  = n' + m' + 2 : by rw <- ih
                   ...  = n' + (m' + 1) + 1 : by reflexivity
                   ...  = (m' + 1) + n' + 1 : by rw ih
                   ...  = (m' + 1) + (n' + 1) : by reflexivity
end
