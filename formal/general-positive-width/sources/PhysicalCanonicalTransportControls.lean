import PhysicalCanonicalWitnessTransport

namespace StackSorting.SparseEndpointMSO.CanonicalChoice.TransportControls

def numbered : Model where
  domain := List.range 2
  I _ := False
  R _ := False
  S x y := x+1=y
  M _ _ := False

def renameIndex (x : Nat) : Nat := if x=70 then 0 else 1
def originalName (i : Nat) : Nat := if i=0 then 70 else 3

/-- Deliberately reversed numeric names and a repeated domain entry. -/
def renamed : Model where
  domain := [70,3,70]
  I _ := False
  R _ := False
  S x y := renameIndex x+1=renameIndex y
  M _ _ := False

def renameIso : Isomorphism renamed numbered where
  toFun := renameIndex
  invFun := originalName
  to_mem := by
    intro x hx
    have h : x=70 ∨ x=3 := by
      have hmem : x=70 ∨ x=3 ∨ x=70 := by simpa [renamed] using hx
      rcases hmem with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl h
    rcases h with rfl | rfl <;> simp [numbered,renameIndex]
  inv_mem := by
    intro y hy
    have h : y=0 ∨ y=1 := by have := List.mem_range.mp hy; omega
    rcases h with rfl | rfl <;> simp [renamed,originalName]
  left_inv := by
    intro x hx
    have h : x=70 ∨ x=3 := by
      have hmem : x=70 ∨ x=3 ∨ x=70 := by simpa [renamed] using hx
      rcases hmem with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl h
    rcases h with rfl | rfl <;> simp [originalName,renameIndex]
  right_inv := by
    intro y hy
    have h : y=0 ∨ y=1 := by have := List.mem_range.mp hy; omega
    rcases h with rfl | rfl <;> simp [originalName,renameIndex]
  insert_iff _ _ := Iff.rfl
  remove_iff _ _ := Iff.rfl
  successor_iff _ _ _ _ := Iff.rfl
  matching_iff _ _ _ _ := Iff.rfl

theorem numbered_time_path : TimePath numbered 2 := ⟨rfl,fun _ _ _ _ => Iff.rfl⟩

theorem chronology_reverses_numeric_name_order :
    OrderEval renamed chronologicalBefore 70 3 ∧ ¬ (70<3) := by
  constructor
  · have h := (chronological_naming_exact renameIso numbered_time_path (0 : Fin 2) 1).mpr
      (by decide)
    simpa [orderedDomainOfTimeIsomorphism,renameIso,originalName] using h
  · decide

def firstTime : Fin 1 → Nat → Prop := fun _ y => y=0

theorem renamed_parameter_is_exact (x : Nat) :
    pullbackTuple renameIso firstTime 0 x ↔ x=70 := by
  by_cases hx : x=70
  · subst x; simp [pullbackTuple,renameIso,firstTime,renamed,renameIndex]
  · simp [pullbackTuple,renameIso,firstTime,renamed,renameIndex,hx]

theorem ghost_parameter_rejected : ¬ pullbackTuple renameIso firstTime 0 5 := by
  rw [renamed_parameter_is_exact]
  decide

theorem all_formula_binders_preserved (f : Formula 0 1) :
    Eval renamed f Fin.elim0 (pullbackTuple renameIso firstTime) ↔
      Eval numbered f Fin.elim0 firstTime := pullbackTuple_eval renameIso f firstTime

#print axioms chronology_reverses_numeric_name_order
#print axioms renamed_parameter_is_exact
#print axioms all_formula_binders_preserved
end StackSorting.SparseEndpointMSO.CanonicalChoice.TransportControls
