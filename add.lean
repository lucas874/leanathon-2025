def add (a: Nat) (b: Nat) : Nat := a + b

#eval add 1 1

def fac (a: Nat) : Nat :=
  match a with
  | 0 => 1
  | n+1 => (n+1) * fac n


#eval fac 4

#eval List.map (fun m ↦ m + 2) [1,2,3]


theorem in_123 : ∀ n ∈ [1,3,4], 0 < n := by
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


#eval List.foldl (fun m x ↦ m + x) 0 [1,2,3]

structure Person where
  name : String
  age : Nat
  kids : List Person

def oliver := Person.mk "Oliver" 27
  [{name := "Oskar", age := 29, kids := []}]


--def Person.get_names (p: Person): List String :=
--  [p.name] ++ p.kids.attach.flatMap (fun p' ↦ Person.get_names p'.val)
-- decreasing_by
--  obtain ⟨p', h⟩


inductive Animal where
  | cat : (lives : Nat) -> Animal
  | dog : (name: String) -> Animal

--def Animal.get_name (a: Animal) : String :=
