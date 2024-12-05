set_option pp.fieldNotation true

inductive Kind where
  | proc : Kind
  | lock : Kind

open Kind
axiom distinct_kind : lock ≠ proc

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

theorem World.no_self_ptr {size : Nat} {w : World size}
  : ((i : Fin size) → (w.store[i]'(w.pf_idx i w.pf_sz)).pto ≠ some i) := by
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
  | none =>
    let res := {w.store[r_i] with pto := some p_i}
    have r_set : r_i < w.store.size := by simp [w.pf_sz]

    let store := w.store.set (Fin.mk r_i r_set) res

    have pf_res_kind : res.kind = w.store[r_i].kind := by rfl
    have pf_res_pto : res.pto = some p_i := by rfl

    have pf_sz : store.size = wsize := by
      unfold store
      rw [Array.size_set, w.pf_sz]

    have pf_store_ri : store[r_i] = res := by sorry
    have pf_store_ri_pto : store[r_i].pto = some p_i := by simp [pf_store_ri]

    have _ := w.pf_sz
    have pf_store_eq_1 : (i : Fin wsize) -> i ≠ r_i → store[i] = w.store[i] := by sorry

    have pf_idx : (i : Fin wsize) → (h : store.size = wsize) → i < store.size := by
      intro i h
      rw [h]
      exact i.isLt

    have pf_ptr {pto : Fin wsize} (i : Fin wsize) (h : store[i].pto = some pto)
      : store[i].kind ≠ store[pto].kind := by
      by_cases h1 : i = r_i
      . simp [*] at *
        rw [h]
        sorry
      . rw [pf_store_eq_1 i h1]
        sorry

    World.mk store pf_sz pf_idx pf_ptr -- new world
  | some pto =>
    if pto == p_i
      -- resource already points to the process
      then w
      else sorry

def World.update {wsize : Nat} (w : World wsize) (fr to : Nat) {_ : to >= fr} : World wsize := sorry
