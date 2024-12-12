variable (a b : Prop)

theorem p : a ∨ ¬a := Classical.em a

theorem q : (¬a ∨ ¬b) → ¬(a ∧ b) := by
  intro h1
  -- ¬(a ∧ b)
  apply h1.elim
  -- ¬a → ¬(a ∧ b)
  -- ¬b → ¬(a ∧ b)
  <;> intro h2
  -- ¬(a ∧ b)
  -- ¬(a ∧ b)
  <;> intro ⟨h3l, h3r⟩
  -- h2: ¬a, h3l: a
  -- h2: ¬b, h3r: b
  <;> contradiction

def head
  (a : Array Int)
  -- (a.size > 0) is a Prop
  -- pf_non_empty is an instance of (a.size > 0)
  (pf_non_empty: a.size > 0)
  : Int
  := a[0]'pf_non_empty

theorem id_exists (i : Int) : ∃(j : Int), j = i := by
  have h : (i = i) := rfl
  constructor
  exact h
