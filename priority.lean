import Batteries.Data.Array.Basic

set_option pp.fieldNotation true

inductive Kind where
  | proc : Kind
  | lock : Kind

open Kind

theorem distinct_kind : lock ≠ proc := by
  intro h
  nomatch h

theorem other_kind (k : Kind) : (k = lock ↔ k ≠ proc) ∧ (k = proc ↔ k ≠ lock) := by
  constructor <;> constructor <;> intro h
  <;> induction k <;> simp [*] at *

structure St (world_size : Nat) where
  pto: Option (Fin world_size)
  def_prio: Nat
  prios: Array Nat
  kind: Kind

def St.curr_prio (s : St n) : Nat :=
  match s.prios.max? with
  | none => s.def_prio
  | some m => max m s.def_prio

structure World (size : Nat) where
  store : Array (St size)
  -- this is by definition
  pf_sz : store.size = size
  -- valid, easy to prove
  pf_idx : (i : Fin size) → (h : store.size = size) → i < store.size
  -- invariant
  pf_ptr : (i : Fin size)
    → (h : (store[i]'(pf_idx i pf_sz)).pto = some pto)
    → (store[i]'(pf_idx i pf_sz)).kind ≠ (store[pto]'(pf_idx pto pf_sz)).kind

theorem th_pf_idx (i : Fin a) (h : b = a) : i < b := by
  rw [h]
  exact i.isLt

partial def World.update_prio {wsize : Nat} (w : World wsize)
  (n : Fin wsize)
  (fr_pr : Option Nat) (to_pr : Nat)
  (h_inc_pr : if let some f := fr_pr then to_pr >= f else true) : World wsize :=

  let nst := w.store[n]'(w.pf_idx n w.pf_sz)
  let new_fr_pr := nst.curr_prio

  -- erase {from} from prios
  let prios1 := match fr_pr with
    | none => nst.prios
    | some p => if nst.prios.contains p then nst.prios.erase p else nst.prios

  -- insert {to} into prios
  let prios2 : Array _ := prios1.push to_pr

  let nst1 := {nst with prios := prios2}
  let new_to_pr := nst1.curr_prio

  -- prios2 should not be empty
  have prios2_nempty : prios2.max? ≠ none := by sorry

  -- monotonicity
  have new_pr_inc : new_fr_pr <= new_to_pr := by
    unfold new_fr_pr new_to_pr St.curr_prio
    split <;> rename_i h1
    split <;> rename_i h2
    try (simp [*] at *)
    . exact Nat.le_max_right _ nst.def_prio
    split <;> rename_i h3
    . have g : nst1.def_prio = nst.def_prio := by rfl
      rw [g]
      simp
      -- h3 says prios2 is empty. this is false
      sorry
    . sorry

  let store := w.store.set (Fin.mk n (w.pf_idx n w.pf_sz)) nst1

  have pf_sz : store.size = wsize := by
    unfold store
    rw [Array.size_set, w.pf_sz]

  have pf_idx : (i : Fin wsize) → (h : store.size = wsize) → i < store.size := th_pf_idx

  -- framing
  have pf_frame (i : Fin wsize) :
    store[i].kind = (w.store[i]'(w.pf_idx i w.pf_sz)).kind
      ∧ store[i].pto = (w.store[i]'(w.pf_idx i w.pf_sz)).pto
    := by
    by_cases h : i = n
    . rw [h]
      unfold store
      simp [*] at *
      unfold nst
      constructor
      <;> rfl
    . unfold store
      let n' := Fin.mk n (w.pf_idx n w.pf_sz)
      simp [*] at *
      rw [w.store.getElem_set_ne]
      constructor
      all_goals (try rfl)
      simp
      exact Fin.val_ne_of_ne fun a => h (id (Eq.symm a))

  have pf_ptr {pto : Fin wsize} (i : Fin wsize) (h : store[i].pto = some pto)
    : store[i].kind ≠ store[pto].kind := by
    rw [(pf_frame _).left, (pf_frame _).left]
    rw [(pf_frame _).right] at h
    exact (w.pf_ptr i h)

  let world := World.mk store pf_sz pf_idx pf_ptr

  if ifh : new_fr_pr ≠ new_to_pr ∧ nst1.pto.isSome then
    have h : (if let some f := some new_fr_pr then new_to_pr >= f else true) := by simp; exact new_pr_inc
    world.update_prio (nst1.pto.get ifh.right) new_fr_pr new_to_pr h
  else world

def World.acquire {wsize : Nat} (w : World wsize)
  (p_i r_i : Fin wsize)
  {p_k : (w.store[p_i]'(w.pf_idx p_i w.pf_sz)).kind = proc}
  {r_k : (w.store[r_i]'(w.pf_idx r_i w.pf_sz)).kind = lock} : World wsize :=

  have _ : p_i < w.store.size := w.pf_idx p_i w.pf_sz
  have _ : r_i < w.store.size := w.pf_idx r_i w.pf_sz

  have pf_p_ne_r : p_i ≠ r_i := by
    intro h
    have _ : lock = proc := by
      calc lock
      _ = w.store[r_i].kind := by rw [r_k]
      _ = w.store[p_i].kind := by simp [h]
      _ = proc := p_k
    contradiction

  let p := w.store[p_i]
  let r := w.store[r_i]

  match r.pto with
  -- point the resource to the process
  | none =>
    let res := {w.store[r_i] with pto := some p_i}
    have r_set : r_i < w.store.size := by simp [w.pf_sz]
    let store := w.store.set (Fin.mk r_i r_set) res

    -- proof components
    have pf_res_kind : res.kind = w.store[r_i].kind := by rfl
    have pf_res_pto : res.pto = some p_i := by rfl

    have pf_sz : store.size = wsize := by
      unfold store
      rw [Array.size_set, w.pf_sz]

    have pf_store_ri : store[r_i] = res := by
      unfold store
      simp [Array.get_set_eq]

    have pf_store_ri_pto : store[r_i].pto = some p_i := by simp [pf_store_ri]

    have _ := w.pf_sz -- valid index
    have pf_store_framing : (i : Fin wsize) → i ≠ r_i → store[i] = w.store[i] := by
      intro ih h
      unfold store
      simp [*] at *
      rw [Array.getElem_set_ne]
      simp
      exact Fin.val_ne_of_ne fun a => h (id (Eq.symm a))

    -- invariants for the returned world
    have pf_ptr {pto : Fin wsize} (i : Fin wsize) (h : store[i].pto = some pto)
      : store[i].kind ≠ store[pto].kind := by
      by_cases h1 : i = r_i
      . simp [*] at *
        have h_ : pto = p_i := by rw [h]
        rw [h_]
        have h_ : store[p_i.val].kind = proc := by
          calc store[p_i].kind
            _ = w.store[p_i].kind := by exact congrArg St.kind (pf_store_framing p_i pf_p_ne_r)
            _ = proc := by exact p_k
        intro m
        rw [h_] at m
        apply distinct_kind
        exact m
      . rw [pf_store_framing i h1]
        by_cases h2 : pto = r_i
        . simp [*] at *
          have hx : (w.store[i].kind ≠ w.store[r_i].kind) := w.pf_ptr i h
          have hy : w.store[r_i].kind = lock := r_k
          rw [hy] at hx
          exact hx
        . rw [pf_store_framing pto h2]
          rw [pf_store_framing i h1] at h
          exact w.pf_ptr i h

    let from_pr := none
    let to_pr := store[p_i].curr_prio

    have pf_inc_pr : (if let some f := from_pr then to_pr >= f else true) := by rfl
    World.update_prio (World.mk store pf_sz th_pf_idx pf_ptr) p_i from_pr to_pr pf_inc_pr
    -- World.mk store pf_sz th_pf_idx pf_ptr
  | some pto =>
    if pto == p_i
      -- resource already points to this process
      then w
      -- point this process to the resource
      else
        let res := {w.store[p_i] with pto := some r_i}
        have p_set : p_i < w.store.size := by simp [w.pf_sz]
        let store := w.store.set (Fin.mk p_i p_set) res

        -- proof components
        have pf_res_kind : res.kind = w.store[p_i].kind := by rfl
        have pf_res_pto : res.pto = some r_i := by rfl

        have pf_sz : store.size = wsize := by
          unfold store
          rw [Array.size_set, w.pf_sz]

        have pf_store_pi : store[p_i] = res := by
          unfold store
          simp [Array.get_set_eq]

        have pf_store_pi_pto : store[p_i].pto = some r_i := by simp [pf_store_pi]

        have _ := w.pf_sz -- valid index
        have pf_store_framing : (i : Fin wsize) -> i ≠ p_i → store[i] = w.store[i] := by
          intro ih h
          unfold store
          simp [*] at *
          rw [Array.getElem_set_ne]
          simp
          exact Fin.val_ne_of_ne fun a => h (id (Eq.symm a))

        -- invariants for the returned world
        have pf_ptr {pto : Fin wsize} (i : Fin wsize) (h : store[i].pto = some pto)
          : store[i].kind ≠ store[pto].kind := by
          by_cases h1 : i = p_i
          . simp [*] at *
            have h_ : pto = r_i := by rw [h]
            rw [h_]
            have h_ : store[r_i.val].kind = lock := by
              have pf_r_ne_p : r_i ≠ p_i := by
                symm
                simp [pf_p_ne_r]
              calc store[r_i].kind
                _ = w.store[r_i].kind := by exact congrArg St.kind (pf_store_framing r_i pf_r_ne_p)
                _ = lock := by exact r_k
            intro m
            rw [h_] at m
            apply distinct_kind
            symm
            exact m
          . rw [pf_store_framing i h1]
            by_cases h2 : pto = p_i
            . simp [*] at *
              have hx : (w.store[i].kind ≠ w.store[p_i].kind) := w.pf_ptr i h
              have hy : w.store[p_i].kind = proc := p_k
              rw [hy] at hx
              exact hx
            . rw [pf_store_framing pto h2]
              rw [pf_store_framing i h1] at h
              exact w.pf_ptr i h

        let from_pr := none
        let to_pr := store[r_i].curr_prio
        have pf_inc_pr : (if let some f := from_pr then to_pr >= f else true) := by rfl
        World.update_prio (World.mk store pf_sz th_pf_idx pf_ptr) r_i from_pr to_pr pf_inc_pr
        -- World.mk store pf_sz th_pf_idx pf_ptr
