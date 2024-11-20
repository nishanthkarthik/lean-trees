inductive TSum (α : Type u) (β : Type v) where
  | inl : α -> TSum α β
  | inr : β -> TSum α β

def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))
