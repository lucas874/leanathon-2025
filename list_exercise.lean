def all (l : List α) (p : α → Bool) : Bool :=
  match l with
  | [] => true
  | x::l' => p x ∧ all l' p

example : all l (fun n ↦ 0 <= n) := by
  induction l with
  | nil =>
    simp [all]
  | cons x tail ih => simp_all [all]

def filter (l : List α) (p : α → Bool) : List α :=
  match l with
  | [] => []
  | x::l' =>
    match p x with
    | true => x::filter l' p
    | _ => filter l' p

theorem filter_all (l : List α) (p : α → Bool) : (filter l p).all p := by
  induction l with
  | nil => simp [filter]
  | cons x tail ih =>
    rw[filter]
    split
    . simp
      rename_i h2
      constructor
      exact h2
      simp at ih
      exact ih
    . exact ih

def append (l₁ : List α) (l₂ : List α) : List α :=
  match l₁ with
  | [] => l₂
  | x::l₁' => x::(append l₁' (l₂))

#eval append [1,2,3] [4]

theorem cons_append_assoc (x: α) (l₁: List α) (l₂: List α) :
    append (x::l₁) l₂ = x::(append l₁ l₂) := by
  induction l₁ with
  | nil => simp[append]
  | cons x tal ih =>
    rw[append]

theorem append_filter (l₁: List α) (l₂: List α) (p : α → Bool) :
    filter (append l₁ l₂) p = append (filter l₁ p) (filter l₂ p) := by
  induction l₁ with
  | nil =>
    simp[append, filter]
  | cons x tail ih =>
    rw[filter, append]
    split
    . rw[cons_append_assoc]
      rw[filter]
      rename_i h
      simp[h]
      exact ih
    . rw[filter]
      rename_i h1
      simp[h1]
      exact ih
