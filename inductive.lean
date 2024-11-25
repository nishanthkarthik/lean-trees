set_option pp.fieldNotation false

inductive TList (α : Type u) where
  | tnil  : TList α
  | tcons : α → TList α → TList α

namespace TList

def append (as bs : TList α) : TList α :=
  match as with
  | tnil => bs
  | tcons x xs => tcons x (append xs bs)

theorem nil_append (as : TList α) : append tnil as = as := by
  rfl

theorem nil_append_symm (as : TList α) : append as tnil = as := by
  induction as with
  | tnil => rfl
  | tcons a ar ih =>
    calc append (tcons a ar) tnil
      _ = tcons a (append ar tnil) := by rfl
      _ = tcons a ar := by rw [ih]

theorem cons_append (a : α) (as bs : TList α)
  : append (tcons a as) bs = tcons a (append as bs) := by
  induction as with
  | tnil => rfl
  | tcons x xs ih => rfl

def len (a : TList α) : Nat :=
  match a with
  | tnil => 0
  | tcons _ as => 1 + len as

theorem len_dist (as bs : TList α)
  : len (append as bs) = len as + len bs := by
  induction as with
  | tnil => simp [nil_append, len]
  | tcons x xs ih =>
    simp [cons_append]
    calc
      1 + len (append xs bs) = len (tcons x (append xs bs)) := by rfl
      _ = 1 + len (append xs bs) := by rfl
      _ = 1 + (len xs + len bs) := by rw [ih]
      _ = (1 + len xs) + len bs := by rw [Nat.add_assoc]

def rev (a : TList α) : TList α :=
  match a with
  | tnil => tnil
  | tcons ah as => append (rev as) (tcons ah tnil)

theorem rev_len (as : TList α) : len as = len (rev as) := by
  induction as with
  | tnil => rfl
  | tcons x xs ih =>
    symm
    calc len (rev (tcons x xs))
      _ = len (append (rev xs) (tcons x tnil)) := by rfl
      _ = len xs + len (tcons x tnil) := by rw [len_dist, ih]
      _ = 1 + len xs := by simp [len, Nat.add_comm]
      _ = len (tcons x xs) := by rfl

theorem app_assoc (a b c : TList α) : append a (append b c) = append (append a b) c := by
  induction a with
  | tnil => rfl
  | tcons x xs ih =>
    calc append (tcons x xs) (append b c)
    _ = tcons x (append xs (append b c)) := by rfl
    _ = tcons x (append (append xs b) c) := by rw [ih]
    _ = append (tcons x (append xs b)) c := by rfl
    _ = append (append (tcons x xs) b ) c := by rfl

theorem rev_app (as : TList α) (bs : TList α) :
  rev (append as bs) = append (rev bs) (rev as) := by
  induction as with
  | tnil =>
    symm
    calc append (rev bs) (rev tnil)
      _ = append (rev bs) tnil := by rfl
      _ = rev bs := by rw [nil_append_symm]
  | tcons h t ih =>
    calc rev (append (tcons h t) bs)
    _ = rev (tcons h (append t bs)) := by rfl
    _ = append (rev (append t bs)) (tcons h tnil) := by rfl
    _ = append (append (rev bs) (rev t)) (tcons h tnil) := by rw [ih]
    _ = append (rev bs) (append (rev t) (tcons h tnil)) := by rw [app_assoc]

theorem rev_rev (as : TList α) : rev (rev as) = as := by
  induction as with
  | tnil => rfl
  | tcons x xs ih =>
    calc rev (rev (tcons x xs))
      _ = rev (append (rev xs) (tcons x tnil)) := by rfl
      _ = _ := by sorry
