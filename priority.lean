set_option pp.fieldNotation false

inductive Kind where
  | proc : Kind
  | lock : Kind

structure St (world_size : Nat) where
  pto: Option (Fin world_size)
  def_prio: Nat
  prios: Array Nat
  kind: Kind

def St.curr_prio (s : St n) : Nat :=
  match s.prios.getMax? (fun a b => a < b) with
  | none => s.def_prio
  | some m => max m s.def_prio

structure World where
  size : Nat
  store : Array (St size)
  invariant : store.size = size
  pf_ptr : ∀ (i : Fin size), match store[i].pto with
                              | none => true
                              | some pto => store[i].kind ≠ store[pto].kind

def World.acquire (w : World) (p_i r_i : Fin w.store.size) {p_k : w.store[p_i].kind = proc} {r_k : w.store[r_i].kind = lock} : World :=
  have _ : p_i < w.size := by sorry
  have _ : r_i < w.size := by sorry

  let p := w.store[p_i]
  let r := w.store[r_i]

  w

def World.update (w : World) (fr to : Nat) {_ : to >= fr} : World := sorry
