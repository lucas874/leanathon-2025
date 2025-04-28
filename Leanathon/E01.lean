def all (l : List α) (p : α → Prop) : Prop :=
  match l with
  | .nil => true
  | .cons x xs => p x ∧ all xs p
def any (l : List α) (p : α → Prop) : Prop :=
  match l with
  | .nil => false
  | .cons x xs => p x ∨ any xs p

example : all l (fun n ↦ 0 ≤ n) := by
  induction l with
  | nil =>
    simp [all]
  | cons x tail ih =>
    simp_all [all]

def filter (l : List α) (p : α → Prop) [DecidablePred p] : List α :=
  match l with
  | [] => []
  | x :: xs => if p x then x :: filter xs p else filter xs p

theorem filter_all (l : List α) (p : α → Prop) [DecidablePred p] :
    all (filter l p) p := by
  induction l with
  | nil => rw [filter, all]
  | cons x tail ih =>
    rw [filter]
    split
    · rename_i h
      rw [all]
      exact ⟨h, ih⟩
    · rename_i h
      assumption
