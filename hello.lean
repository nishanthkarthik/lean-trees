
example (p q r : Prop) : ((p ∨ q) → r) ↔ ((p → r) ∧ (q → r)) :=
Iff.intro
    (fun l : (p ∨ q) → r => sorry)
    (fun l : ((p → r) ∧ (q → r)) =>
        have a := l.left
        have b := l.right
        (fun l : (p ∨ q) => Or.elim l a b)
    )
