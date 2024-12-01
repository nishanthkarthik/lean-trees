import Mathlib
import Aesop

set_option pp.fieldNotation false

-- Report ideas
-- No abstraction leakage (the foundation is well hidden)
-- simp is like trigger based instantiation

-- Min heap
structure Heap where
  st : Array Nat

def heapify (a : Array Nat) (s : Fin a.size) : Array Nat :=
  let pf_s := s.isLt
  let s := s.val

  let l := 2 * s
  let r := 2 * s + 1

  let sm := if h : l < a.size then ite (a[l] < a[s]) l s else s

  have pf_sm : sm < a.size := by
    unfold sm
    split <;> rename_i h1
    . split <;> rename_i h2
      . exact h1
      . exact pf_s
    . exact pf_s

  let sm := if h : r < a.size then ite (a[r] < a[sm]) r sm else sm
  have pf_sm : sm < a.size := by
    unfold sm
    split <;> rename_i h1
    . rw [apply_ite (fun x => x < a.size)]
      split
      . exact h1
      . exact pf_sm
    . exact pf_sm

  if ht : sm = s
    then a -- do nothing
    else   -- recurse
      let swapped := a.swap (Fin.mk s pf_s) (Fin.mk sm pf_sm)

      -- recursion is still valid
      have pf_sz : swapped.size = a.size := by rw [Array.size_swap]
      have pf_sm : sm < swapped.size := by rw [pf_sz]; exact pf_sm

      -- termination
      have pf_term : s <= sm := sorry

      have pf_term : a.size - sm <= a.size - s := by
        exact Nat.sub_le_sub_left pf_term (Array.size a)

      have pf_term : a.size - sm < a.size - s := by
        apply Nat.lt_of_le_of_ne
        . exact pf_term
        . intro h
          have g : sm = s := sorry
          contradiction

      heapify swapped (Fin.mk sm pf_sm)
