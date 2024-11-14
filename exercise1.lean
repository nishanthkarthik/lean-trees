variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  <;> intro h
  <;> apply And.symm
  <;> exact h

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  <;> intro h
  <;> apply Or.symm
  <;> exact h

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro t
    apply And.intro
    . exact t.left.left
    . apply And.intro
      . exact t.left.right
      . exact t.right
  . intro h
    apply And.intro
    . apply And.intro
      . exact h.left
      . exact h.right.left
    . exact h.right.right

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro t
    sorry
  . intro h
    sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro npq
    apply And.intro
    <;> intro hp
    <;> apply npq
    . apply Or.inl; exact hp
    . apply Or.inr; exact hp
  . intro npnq
    intro poq
    cases poq with
    | inl hp => apply npnq.left; exact hp
    | inr hq => apply npnq.right; exact hq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h
  intro ⟨ hp, hq ⟩
  cases h with
  | inl l => contradiction
  | inr l => contradiction

example : ¬(p ∧ ¬p) := by
  intro ⟨ pp, np ⟩
  contradiction

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨ hl, hr ⟩ n
  apply hr
  exact (n hl)

example : ¬p → (p → q) := by
  intro hnp
  intro hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h
  intro hp
  cases h with
  | inl hi => contradiction
  | inr hi => exact hi

example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro hy
    apply Or.elim hy
    <;> intro ph
    . exact ph
    . contradiction
  . intro hy
    apply Or.inl
    exact hy

example : p ∧ False ↔ False := by
  apply Iff.intro
  <;> intro h
  . apply And.right
    exact h
  . contradiction

example : (p → q) → (¬q → ¬p) := by
  intro h nq p
  exact nq (h p)
