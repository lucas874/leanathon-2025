def all (l : List α) (p : α → Prop) : Prop :=
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

inductive Tree where
  | leaf
  | node : Tree -> Tree -> Nat -> Tree

#eval Tree.node (Tree.node Tree.leaf Tree.leaf 1) (Tree.node Tree.leaf Tree.leaf 3) 2

def Tree.toList (t : Tree) : List Nat :=
  match t with
  | leaf => []
  | node t1 t2 val =>
      Tree.toList t1 ++ [val] ++ Tree.toList t2

#eval Tree.toList (Tree.node (Tree.node Tree.leaf Tree.leaf 1) (Tree.node Tree.leaf Tree.leaf 3) 2)

inductive Tree.All : (Nat → Prop) → Tree → Prop where
  | leaf : Tree.All p Tree.leaf
  | node : p x -> Tree.All p l -> Tree.All p r -> Tree.All p (.node l r x)

theorem all_append (l1: List α) (l2: List α) p : all (l1 ++ l2) p ↔ all l1 p ∧ all l2 p := by
  induction l1 with
  | nil => simp[all]
  | cons x tail ih =>
    simp[all]
    simp[ih]
    simp[and_assoc]

theorem tree_all_eq_tree_to_list_all (t: Tree) (p : Nat → Prop) :
    all (Tree.toList t) p  = Tree.All p t := by
  induction t with
  | leaf =>
    simp[Tree.toList, all]
    exact Tree.All.leaf
  | node left right val ih_left ih_right =>
    simp
    rw[Tree.toList]
    rw[all_append]
    rw[all_append]
    rw[ih_left]
    rw[ih_right]
    constructor
    . simp
      intro h1
      intro h2
      intro h3
      apply Tree.All.node
      . rw[all] at h2
        exact h2.left
      . exact h1
      . exact h3
    . intro h1
      cases h1
      simp[*]
      simp[all]
      assumption
