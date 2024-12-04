set_option pp.fieldNotation false

theorem nat_sub_elim (a b k : Nat) {_ : k > a} {q : k > b}
  : (a > b) → (k - a < k - b) := by
  intro h
  apply Nat.sub_lt_sub_left
  exact q
  exact h

-- Report ideas
-- No abstraction leakage (the foundation is well hidden)
-- simp is like trigger based instantiation
-- Viper makes it easier to hide a proof for False. In Lean, it's explicit

-- Min heap
structure Heap where
  st : Array Nat

def heapify (a : Array Nat) (s : Nat) (pf_s_lower : s > 0) (pf_s_upper : s < a.size) : Array Nat :=
  let l := 2 * s
  let r := 2 * s + 1

  -- first assignment
  let sm_1 := if h : l < a.size then ite (a[l] < a[s]) l s else s

  -- still within bounds
  have pf_sm1_size : sm_1 < a.size := by
    unfold sm_1
    split <;> rename_i h1
    split <;> rename_i h2
    all_goals (try exact pf_s_upper)
    exact h1

  -- move towards termination
  have pf_sm1_dec : sm_1 >= s := by
    rw [apply_dite (fun x => x >= s)]
    split <;> rename_i h1
    rw [apply_ite (fun x => x >= s)]
    split <;> rename_i h2
    all_goals (try exact Nat.le_refl s)
    unfold l
    refine Nat.le_mul_of_pos_left s ?_
    exact Nat.zero_lt_two

  -- second assignment
  let sm_2 := if h : r < a.size then ite (a[r] < a[sm_1]) r sm_1 else sm_1

  -- still within bounds
  have pf_sm2_size : sm_2 < a.size := by
    unfold sm_2
    split <;> rename_i h1
    . rw [apply_ite (fun x => x < a.size)]
      split
      . exact h1
      . exact pf_sm1_size
    . exact pf_sm1_size

  -- move towards termination
  have pf_sm2_dec : sm_2 >= s := by
    rw [apply_dite (fun x => x >= s)]
    split <;> rename_i h1
    rw [apply_ite (fun x => x >= s)]
    split <;> rename_i h2
    all_goals (try exact pf_sm1_dec)
    unfold r
    simp [*]
    refine Nat.le_add_right_of_le ?_
    have h : 2 * s = s + s := by exact Nat.two_mul s
    rw [h]
    exact Nat.le_add_right s s

  if ht : sm_2 = s
    then a -- do nothing
    else   -- recurse
      let swapped := a.swap (Fin.mk s pf_s_upper) (Fin.mk sm_2 pf_sm2_size)

      -- recursion is still valid
      have pf_sz : swapped.size = a.size := by rw [Array.size_swap]
      have pf_sm : sm_2 < swapped.size := by rw [pf_sz]; exact pf_sm2_size

      -- termination
      have pf_term : (a.size - sm_2) < (a.size - s) := by
        apply nat_sub_elim
        . exact pf_sm2_size
        . exact pf_s_upper
        . apply Nat.lt_of_le_of_ne pf_sm2_dec
          exact fun a => ht (Eq.symm a)

      -- our next s is also > 0
      have sm_lower : sm_2 > 0 := by
        exact Nat.lt_of_lt_of_le pf_s_lower pf_sm2_dec

      heapify swapped sm_2 sm_lower pf_sm

termination_by a.size - s
