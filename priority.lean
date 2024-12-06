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
  match s.prios.getMax? (fun a b => a < b) with
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

def World.update {wsize : Nat} (w : World wsize) (n : Fin wsize) (fr to : Option Nat)
  {h_inc_pr : match fr, to with
      | some fr, some to => to >= fr
      | _, _ => true }
  : World wsize :=
  sorry

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
    have pf_store_framing : (i : Fin wsize) -> i ≠ r_i → store[i] = w.store[i] := by
      intro ih h
      unfold store
      simp [*] at *
      rw [Array.getElem_set_ne]
      simp
      exact Fin.val_ne_of_ne fun a => h (id (Eq.symm a))

    -- invariants for the returned world
    have pf_idx : (i : Fin wsize) → (h : store.size = wsize) → i < store.size := by
      intro i h
      rw [h]
      exact i.isLt

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

    let fr := none
    let to := store[p_i].curr_prio
    World.update (World.mk store pf_sz pf_idx pf_ptr) p_i fr to -- new world
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
        have pf_idx : (i : Fin wsize) → (h : store.size = wsize) → i < store.size := by
          intro i h
          rw [h]
          exact i.isLt

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

        let fr := none
        let to := store[r_i].curr_prio
        World.update (World.mk store pf_sz pf_idx pf_ptr) r_i fr to -- new world
