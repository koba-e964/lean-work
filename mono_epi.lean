namespace mono_epi

variables {A B: Type}

def is_inj (f: A -> B) :=
  forall x1 x2, f x1 = f x2 -> x1 = x2

def is_surj (f: A -> B) :=
  forall y, exists x, y = f x

def is_mono (f: A -> B) :=
  forall (X: Type) (g1 g2: X -> A), f ∘ g1 = f ∘ g2 -> g1 = g2

def is_epi (f: A -> B) :=
  forall (X: Type) (g1 g2: B -> X), g1 ∘ f = g2 ∘ f -> g1 = g2

lemma inj_iff_mono: forall (f: A -> B), is_inj f <-> is_mono f :=
begin
  intro f,
  split,
  {
    intros finj X g1 g2 fg,
    apply funext,
    intro x,
    apply finj,
    change (f ∘ g1) x = (f ∘ g2) x,
    rw fg,
  },
  {
    intros fmono x1 x2 feq,
    change (fun _, x1) unit.star = (fun _, x2) unit.star,
    apply congr_fun,
    apply fmono,
    apply funext,
    intro x,
    exact feq,
  },
end

lemma surj_iff_epi: forall (f: A -> B), is_surj f <-> is_epi f :=
begin
  intro f,
  split,
  {
    intros fsurj X g1 g2 gf,
    apply funext,
    intro y,
    cases (fsurj y) with x eq,
    rw eq,
    change (g1 ∘ f) x = (g2 ∘ f) x,
    rw gf,
  },
  {
    intros fepi y,
    let g1: B -> set B := λx, {y: B | y = x /\ exists x, y = f x},
    let g2: B -> set B := λx, {x},
    have h1 := fepi (set B) g1 g2,
    have : g1 ∘ f = g2 ∘ f,
    {
      apply funext,
      intro x,
      change g1 (f x) = g2 (f x),
      simp [g1, g2],
      apply funext,
      intro y,
      apply iff.to_eq,
      split,
      {
        intro h,
        cases h with h1 h2,
        exact h1,
      },
      {
        intro h,
        split,
        {
          exact h,
        },
        {
          existsi x,
          exact h,
        }
      },
    },
    have h1 := congr_fun (h1 this) y,
    simp [g1, g2] at h1,
    have : y ∈ {y_1 : B | y_1 = y /\ ∃ (x : A), y_1 = f x},
    {
      rw h1,
      simp [singleton],
    },
    simp at this,
    exact this,
  },
end

end mono_epi
