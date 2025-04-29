import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Defs

structure PetriNet (S T : Type) where
  W : (S × T) ⊕ (T × S) -> Nat

def PetriNet.Marking (_N : PetriNet S T) := S -> Nat

inductive Place where
  | P₁ | P₂ | P₃ | P₄ | P₅
deriving Repr

inductive Transition where
  | T₁ | T₂ | T₃
deriving Repr

def N₁ : PetriNet Place Transition where
  W := fun x ↦
    match x with
    | .inl (.P₁, .T₁) => 1
    | .inr (.T₁, .P₂) => 1
    | .inr (.T₁, .P₃) => 1
    | .inl (.P₃, .T₂) => 1
    | .inr (.T₂, .P₄) => 1
    | .inl (.P₂, .T₃) => 1
    | .inl (.P₄, .T₃) => 1
    | .inr (.T₃, .P₅) => 1
    | _ => 0

-- the set of all edges
def PetriNet.Edge (_N : PetriNet S T) :=
  ((S × T) ⊕ (T × S)) × Nat

def PetriNet.edges (N : PetriNet S T) : Set (PetriNet.Edge N) :=
  { edge: N.Edge | 0 < edge.snd ∧ edge.snd = N.W edge.fst }

class Listed (α : Type) where
  elems : List α
  complete : ∀ a, a ∈ elems

instance : Listed Place where
  elems :=  [ .P₁, .P₂, .P₃, .P₄, .P₅]
  complete := by
    rintro (_ | _) <;> simp_all

instance : Listed Transition where
  elems :=  [ .T₁, .T₂, .T₃]
  complete := by
    rintro (_ | _) <;> simp_all

@[simp]
theorem Listed.mem_elems {α : Type} [Listed α] {a : α} :
  a ∈ Listed.elems := complete a

instance [Listed α] [Listed β] : Listed (α × β) where
  elems := Listed.elems.product Listed.elems
  complete := by simp

instance [Listed α] [Listed β] : Listed (α ⊕ β) where
  elems :=
    Listed.elems.map (fun x ↦ .inl x)
    ++ Listed.elems.map (fun x ↦ .inr x)
  complete := by simp

#eval (Listed.elems : List Place)
#eval (Listed.elems : List Transition)
#eval (Listed.elems : List (Place × Transition))
#eval (Listed.elems :
  List (Place × Transition ⊕ Transition × Place))

def Listed.setToList [Listed α] (S: Set α)
    [∀ x, Decidable (x ∈ S)] : List α :=
  Listed.elems.filter (fun x ↦ decide (x ∈ S))

--instance [Listed S] [Listed T] {N : PetriNet S T} :
--    Listed N.edge :=
--  inferInstanceAs (Listed (((S × T) ⊕ (T × S))))

/--
-/
def PetriNet.edges' [Listed S] [Listed T] (N : PetriNet S T) :
    List N.Edge :=
  Listed.elems.map (fun edge ↦ (edge, N.W edge))
    |>.filter (0 < ·.snd)

instance {N : PetriNet S T} [Repr S] [Repr T]: Repr N.Edge where
  reprPrec n _ :=
    match n with
    | ⟨.inl (p, t), 1⟩ => s!"{reprStr p} --> {reprStr t}"
    | ⟨.inr (t, p), 1⟩ => s!"{reprStr t} --> {reprStr p}"
    | ⟨.inl (p, t), w⟩ => s!"{reprStr p} -[{w}]-> {reprStr t}"
    | ⟨.inr (t, p), w⟩ => s!"{reprStr t} -[{w}]-> {reprStr p}"

--#guard_msgs in
#eval N₁.edges'

def PetriNet.enabled (N : PetriNet S T) (M : N.Marking) :
    Set T :=
  { t | ∀ s, M s >= N.W (.inl (s, t)) }

def M₁ : N₁.Marking := fun s ↦
  match s with
  | .P₁ => 1
  --| .P₂ => 1
  --| .P₄ => 1
  | _ => 0

instance {N : PetriNet S T} (x : T) [Listed S] :
    Decidable (x ∈ N.enabled M) :=
  if h : Listed.elems.all (fun s ↦  M s >= N.W (.inl (s, x))) then
    .isTrue (by simp_all [PetriNet.enabled])
  else
    .isFalse (by simp_all [PetriNet.enabled])

#eval N₁.enabled M₁ |> Listed.setToList


def PetriNet.fire (N : PetriNet S T) (M : N.Marking) (t : T)
    (h : t ∈ N.enabled M) : N.Marking :=
  fun s ↦ M s - (N.W (.inl (s, t))) + (N.W (.inr (t, s)))

def PetriNet.fire_unchecked (N : PetriNet S T) (M : N.Marking) (t : T)
    : N.Marking :=
  fun s ↦ M s - (N.W (.inl (s, t))) + (N.W (.inr (t, s)))

#eval N₁.enabled
  (N₁.fire M₁ .T₁
    (by
      simp [PetriNet.enabled, N₁, M₁]
      intro p; split <;> simp_all)) |> Listed.setToList

#eval N₁.enabled
  (N₁.fire_unchecked M₁ .T₁) |> Listed.setToList

def PetriNet.succ (N : PetriNet S T) (M₀ : N.Marking) :
    Set N.Marking :=
  { M' : N.Marking | ∃ t h, N.fire M₀ t h = M'}

def PetriNet.reachable (N : PetriNet S T) (M₀ : N.Marking) :
    N.Marking -> N.Marking -> Prop :=
  Relation.ReflTransGen (fun M M' ↦ M' ∈ N.succ M)
