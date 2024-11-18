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
    cases t with
    | inl hpq =>
      cases hpq with
      | inl hl => apply Or.intro_left; exact hl
      | inr hr => apply Or.intro_right; apply Or.intro_left; exact hr
    | inr hr => apply Or.intro_right; apply Or.intro_right; exact hr
  . intro h
    cases h with
    | inl hp => apply Or.intro_left; apply Or.intro_left; exact hp
    | inr qr =>
      cases qr with
      | inl hq => apply Or.intro_left; apply Or.intro_right; exact hq
      | inr hr => apply Or.intro_right; exact hr

example : ¬(p ↔ ¬p) := by
  intro h
  rcases h with ⟨h1, h2⟩
  have np : ¬p := by
    intro hp
    exact h1 hp hp
  . apply h1
    <;> exact (h2 np)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro pqr
    cases pqr.right with
    | inl q =>
      apply Or.intro_left
      constructor
      . exact pqr.left
      . exact q
    | inr r =>
      apply Or.intro_right
      constructor
      . exact pqr.left
      . exact r
  . intro pqpr
    cases pqpr with
    | inl pq =>
      constructor
      . exact pq.left
      . apply Or.intro_left
        exact pq.right
    | inr pr =>
      constructor
      . exact pr.left
      . apply Or.intro_right
        exact pr.right

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  <;> intro h
  <;> intro l
  . apply h
    . exact l.left
    . exact l.right
  . intro hq
    apply h
    constructor
    . exact l
    . exact hq

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  . intro l
    constructor
    <;> intro h
    <;> apply l
    . apply Or.inl
      exact h
    . apply Or.inr
      exact h
  . intro ⟨ pr, qr ⟩ pq
    cases pq with
    | inl hp => exact (pr hp)
    | inr hq => exact (qr hq)

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
