def add (a : Nat) (b : Nat) : Nat := a + b

#eval add 10 3

def fac (a : Nat) : Nat :=
  match a with
  | 0 => 1
  | n + 1 => (n + 1) * fac n

#eval fac 10

#eval List.map (fun m ↦ m + 2) [1, 2, 3]

theorem all_in_123_are_pos : ∀ n ∈ [1, 2, 3], 0 < n := by
  intro n
  intro h
  simp at h
  cases h
  subst_eqs
  trivial
  rename_i h
  cases h
  subst_eqs
  trivial
  subst_eqs
  trivial

structure Person where
  name : String
  age : Nat
  friends : List Person

def oliver := Person.mk "Oliver" 27
  [{name := "Oskar", age := 29, friends := []}]

def Person.get_names (p : Person) : List String :=
  [p.name] ++ p.friends.attach.flatMap (fun p' ↦ Person.get_names p'.val)
decreasing_by
  obtain ⟨p', h⟩ := p'
  simp
  obtain ⟨_, _, friends⟩ := p
  simp_all
  have : sizeOf p' < sizeOf friends := List.sizeOf_lt_of_mem h
  omega

#eval oliver.get_names.map (fun name ↦ name.toUpper)

inductive Animal where
  | cat : (lives : Nat) → Animal
  | dog : (name : String) → Animal
  | dragon : (owner : Animal) → (friend : Animal) → Animal

def Animal.get_name (a : Animal) : Option String :=
  match a with
  | .cat _ => none
  | .dog name => name
  | .dragon owner _ => s!"{owner.get_name}'s dragon"

#eval Animal.cat 9
#eval Animal.dog "fido"

#eval Animal.cat 9 |>.get_name
#eval Animal.dog "fido" |>.get_name
#eval Animal.dragon (.dog "fido") (.cat 1) |>.get_name

inductive Tree where
  | leaf
  | node (left : Tree) (x : Nat) (right : Tree) : Tree
