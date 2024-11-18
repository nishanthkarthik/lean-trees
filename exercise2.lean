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

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro halpha

  sorry

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
