import Mathlib.Data.Multiset.Basic

def Multiset.max (m : Multiset α) : Option α := sorry

structure St (comm : Nat) where
  pto: Fin comm
  def_prio: Int
  prios: Multiset Int

def St.curr_prio (s : St n) : Int :=
  match s.prios.max with
  | none => s.def_prio
  | some m => max m s.def_prio
