
theorem q1 (p q r : Prop) : ((p ∨ q) → r) ↔ ((p → r) ∧ (q → r)) := by
    apply Iff.intro
    . intro hd
      constructor
      <;> intro h
      <;> apply hd
      . apply Or.inl
        exact h
      . apply Or.inr
        exact h
    . intro hc
      intro pq
      apply Or.elim pq
      . exact hc.left
      . exact hc.right
