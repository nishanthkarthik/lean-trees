set_option pp.fieldNotation false

inductive Expr where
  | const (n : Nat) : Expr
  | var (n : Nat) : Expr
  | plus (s : Expr) (t : Expr) : Expr
  | times (s : Expr) (t : Expr) : Expr

open Expr

def eval (v : (Nat -> Nat)) (e : Expr) : Nat :=
  match e with
  | const n => n
  | var n => v n
  | plus s t => eval v s + eval v t
  | times s t => eval v s * eval v t

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse (e : Expr) : Expr :=
  match e with
    | plus s t => simpConst (plus (fuse s) (fuse t))
    | times s t => simpConst (times (fuse s) (fuse t))
    | e => e

theorem simpConst_eq (v : Nat → Nat)
  : ∀ e : Expr, eval v (simpConst e) = eval v e := by
  intro e
  induction e with
  | const n => rfl
  | var n => rfl
  | plus s t g h =>
    congr
    have hs : simpConst s = s := by sorry
    have ht : simpConst t = t := by sorry
    match s, t with
    | const cs, const ct => rfl
    | es, et => sorry
  | times s t => sorry

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  sorry
