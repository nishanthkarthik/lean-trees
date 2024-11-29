set_option pp.fieldNotation false

inductive Tree where
| Nil : Tree
| Node (left right : Tree) (val : Nat) (pf : val % 2 = 0) : Tree

open Tree

def max_val (t : Tree) : Nat :=
  match t with
  | Nil => 0
  | Node l r v _ => max v (max (max_val l) (max_val r))

theorem max_pair {a b : Nat} {pfa : a % 2 = 0} {pfb : b % 2 = 0} : max a b % 2 = 0 := by
  by_cases h : a <= b
  . rw [Nat.max_eq_right h]
    exact pfb
  . have h' : b <= a := Nat.le_of_not_le h
    rw [Nat.max_comm, Nat.max_eq_right h']
    exact pfa

theorem even_max_val (t : Tree) : max_val t % 2 = 0 := by
  induction t with
  | Nil => rfl
  | Node l r v vp lih rih =>
    rw [max_val, max_pair]
    . exact vp
    . rw [max_pair]
      . exact lih
      . exact rih
