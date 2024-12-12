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

def List.nemax (a : List Nat) (v : Nat) : Nat := a.foldr max v

theorem nat_max_cmp (a b c : Nat) (h : a <= b) : max a c <= max b c := by
  simp [Nat.max_def]
  by_cases h1 : a <= b
  <;> by_cases h2 : b <= c
  <;> by_cases h3 : a <= c
  all_goals (try simp [*])
  . have _ : a <= c := by exact Nat.le_trans h h2
    contradiction
  . apply Nat.le_of_lt
    exact Nat.gt_of_not_le h2
  . contradiction
  . exact False.elim (h1 h)

theorem nat_max_lim (a b x : Nat) (h1 : a <= x) (h2 : b <= x) : max a b <= x := Nat.max_le_of_le_of_le h1 h2

theorem nat_max_elim {a b x : Nat} (h1 : x <= a) (h2 : x <= b) : x <= max a b := by
  rw [Nat.max_def]
  split
  exact h2
  exact h1

theorem max_comm_aux (a b c : Nat) : max (max a b) c = max a (max b c) := Nat.max_assoc a b c

theorem max_smaller {a b ah f : Nat} (h1 : a <= max f b) (h2 : max f b < ah) : a <= max ah (max f b) := by
  have fact : max ah (max f b) = ah := by
    rw [Nat.max_def]
    simp [Nat.not_le_of_lt h2]
  rw [fact]
  apply Nat.le_of_lt
  calc a
    _ <= max f b := h1
    _ < ah := h2

theorem list_erase_max (a : List Nat) (d p f : Nat) (h0 : p <= f)
  : a.nemax d <= (f :: a.erase p).nemax d := by
  by_cases h1 : p ∈ a
  . unfold List.nemax
    have a_ne : a ≠ .nil := by intro e; rw [e, List.mem_nil_iff] at h1; exact h1
    induction a with
    | nil => contradiction
    | cons ah as ih =>
      unfold List.foldr
      by_cases h2 : p ∈ as
      <;> by_cases h3 : as = []
      <;> by_cases h4 : ah = p
      all_goals (try simp [*, nat_max_cmp, Nat.le_max_right] at *)
      . apply nat_max_lim
        . rw [Nat.max_comm, max_comm_aux]
          simp [Nat.le_max_left]
        . rw [Nat.max_comm, max_comm_aux]
          have hh : max (List.foldr max d (as.erase p)) f = max f (List.foldr max d (as.erase p)) := by rw [Nat.max_comm]
          rw [hh]
          by_cases h6 : ah <= (max f (List.foldr max d (as.erase p)))
          . have hh : max ah (max f (List.foldr max d (as.erase p))) = (max f (List.foldr max d (as.erase p))) := by
              exact Nat.max_eq_right h6
            rw [hh]
            exact ih
          . rw [Nat.not_le] at h6
            exact max_smaller ih h6
      . simp [List.erase_of_not_mem h2, Nat.le_max_right]
  . simp [List.nemax, h1, List.erase, List.mem_cons_of_mem]
    simp [List.erase_of_not_mem h1, Nat.le_max_right]

theorem list_add_max (a : List Nat) (d n : Nat)
  : a.nemax d <= (n :: a).nemax d := by
  unfold List.nemax
  induction a with
  | nil => simp [Nat.le_max_right]
  | cons ah as ih => simp [List.foldr, Nat.le_max_right]

structure St (world_size : Nat) where
  pto: Option (Fin world_size)
  def_prio: Nat
  prios: List Nat
  kind: Kind

def St.curr_prio (s : St n) : Nat :=
  s.prios.nemax s.def_prio

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
  let prios2 : List _ := to_pr :: prios1

  let nst1 := {nst with prios := prios2}
  let new_to_pr := nst1.curr_prio

  -- monotonicity
  have new_pr_inc : new_fr_pr <= new_to_pr := by
    unfold new_fr_pr new_to_pr St.curr_prio nst1 prios2 prios1
    simp
    split <;> rename_i fr_pr
    . exact Nat.le_max_right to_pr (List.foldr max nst.def_prio nst.prios)
    . rename_i p
      by_cases h : p ∈ nst.prios
      <;> simp [*]
      . simp [*] at fr_pr
        exact list_erase_max nst.prios nst.def_prio p to_pr fr_pr
      . simp [list_add_max]

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
