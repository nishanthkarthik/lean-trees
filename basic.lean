import Mathlib.Algebra.Group.Nat.Even

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

structure Result where
  original: Nat
  rounded_up: Nat
  inv_a: original <= rounded_up
  inv_b: rounded_up - original <= 1
  inv_c: rounded_up % 2 = 0

def round_up_even (n : Nat) : Result :=
  let r := if n % 2 = 0 then n else n + 1

  have inv_a : n <= r := by
    unfold r; split
    all_goals simp [Nat.le_refl, Nat.le_add_right]

  have inv_b : r - n <= 1 := by
    unfold r; split
    . rw [Nat.sub_self]
      simp [Nat.zero_le]
    . rw [Nat.add_sub_cancel_left n 1]

  have inv_c : r % 2 = 0 := by
    unfold r; split <;> rename_i h
    . exact h
    . simp [Nat.succ_mod_two_eq_zero_iff]
      exact Nat.mod_two_ne_zero.mp h

  Result.mk n r inv_a inv_b inv_c
