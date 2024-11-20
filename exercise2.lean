-- section 1

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro h
    constructor
    <;> intro x
    . exact (h x).left
    . exact (h x).right
  . intro h
    intro x
    constructor
    . exact h.left x
    . exact h.right x

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h1 h2 hx
  exact (h1 hx) (h2 hx)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h hx
  rcases h with fp | fq
  . apply Or.inl
    exact (fp hx)
  . apply Or.inr
    exact (fq hx)

-- section 2

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro ha
  constructor
  . intro har
    apply har
    exact ha
  . intro hr _
    exact hr

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  . intro h
    by_cases hr : r -- classical reasoning
    . exact (Or.inr hr)
    . left
      intro hx
      rcases (h hx) with h1 | h2
      . exact h1
      . contradiction
  . intro h x
    rcases h with h1 | h2
    . left
      apply h1
    . right
      exact h2

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  . intro h hr a
    apply h
    exact hr
  . intro h a hr
    apply h
    exact hr

-- section 3

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

theorem contra {a : Prop} : ((a ↔ ¬a) → False) := by
  intro ⟨hf, hb⟩
  let f := fun hp => hf hp hp -- syntax for assumption
  let ha := hb f
  contradiction

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have t := h barber
  apply contra
  exact t

-- existentials

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  intro h
  sorry

example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
