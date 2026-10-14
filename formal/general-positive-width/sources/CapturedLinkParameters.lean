import CapturedLinkMSO

namespace StackSorting.CapturedLinkExtraction
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership

/-- Three unary predicates per color, one selected-base predicate per ordered
color pair, plus selected original edges and selected forest roots. -/
abbrev Parameter (k : Nat) := (Fin k × Fin 3) ⊕ ((Fin k × Fin k) ⊕ Fin 2)

abbrev parameterCount (k : Nat) := Fintype.card (Parameter k)

theorem parameterCount_eq (k : Nat) : parameterCount k = k*3+k*k+2 := by
  simp only [parameterCount,Parameter,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

noncomputable def fixedIndices (k : Nat) : LinkIndices k (parameterCount k) where
  color i j := Fintype.equivFin (Parameter k) (.inl (i,j))
  candidate i j := Fintype.equivFin (Parameter k) (.inr (.inl (i,j)))
  original := Fintype.equivFin (Parameter k) (.inr (.inr 0))
  roots := Fintype.equivFin (Parameter k) (.inr (.inr 1))

structure Selection (D : Model) (k : Nat) where
  original : IncSet D
  candidate : Fin k → Fin k → IncSet D
  roots : IncSet D

def parameterSets {D : Model} (C : Colors D k) (S : Selection D k) : Parameter k → IncSet D
  | .inl (i,j) => Fin.cases (C i).vertices (Fin.cases (C i).edges (fun _ => (C i).roots)) j
  | .inr (.inl (i,j)) => S.candidate i j
  | .inr (.inr j) => Fin.cases S.original (fun _ => S.roots) j

noncomputable def chosenSets {D : Model} (C : Colors D k) (S : Selection D k) :
    Fin (parameterCount k) → IncSet D :=
  fun j => parameterSets C S ((Fintype.equivFin (Parameter k)).symm j)

@[simp] theorem chosenSets_color {D : Model} (C : Colors D k) (S : Selection D k)
    (i : Fin k) (j : Fin 3) :
    chosenSets C S ((fixedIndices k).color i j) =
      Fin.cases (C i).vertices (Fin.cases (C i).edges (fun _ => (C i).roots)) j := by
  simp only [chosenSets,fixedIndices,Equiv.symm_apply_apply,parameterSets]

@[simp] theorem chosenSets_candidate {D : Model} (C : Colors D k) (S : Selection D k)
    (i j : Fin k) : chosenSets C S ((fixedIndices k).candidate i j) = S.candidate i j := by
  simp only [chosenSets,fixedIndices,Equiv.symm_apply_apply,parameterSets]

@[simp] theorem chosenSets_original {D : Model} (C : Colors D k) (S : Selection D k) :
    chosenSets C S (fixedIndices k).original = S.original := by
  simp only [chosenSets,fixedIndices,Equiv.symm_apply_apply,parameterSets,Fin.cases_zero]

@[simp] theorem chosenSets_roots {D : Model} (C : Colors D k) (S : Selection D k) :
    chosenSets C S (fixedIndices k).roots = S.roots := by
  simp only [chosenSets,fixedIndices,Equiv.symm_apply_apply,parameterSets]
  rfl

/-- The actual formula, already back-translated to the original sparse
I/R/S/M/equality/membership vocabulary. Its size and free-set arity depend on
k only. Both free vertex variables retain the original-vertex tag zero. -/
noncomputable def sparseEarlier (k : Nat) : Formula 2 (parameterCount k * 3) :=
  compileActual (capturedEarlierFormula (fixedIndices k) (0 : Fin 2) 1) (fun _ => 0)

theorem originalSets_supported {D : Model} (h : Laws D) (sets : Fin b → IncSet D) :
    CanonicalChoice.SupportedTuple D (originalSets h sets) := by
  intro j x hx
  let p := finProdFinEquiv.symm j
  exact ((realization h).liftSet_supported (sets p.1) (p.2,x) hx).1

/-- Pointwise compiler correctness, with no assumed decomposition or binary
parent input. The remaining forest witness is exposed on the right. -/
theorem eval_sparseEarlier {D : Model} (h : Laws D) (C : Colors D k) (S : Selection D k)
    (x y : Vertex D) :
    Eval D (sparseEarlier k) (Fin.cases x.val (fun _ => y.val))
      (originalSets h (chosenSets C S)) ↔
    RawRootSeparator (fixedIndices k) (chosenSets C S) (.inl x) (.inl y) ∧ x ≠ y := by
  have hc := eval_compileActual h
    (capturedEarlierFormula (fixedIndices k) (0 : Fin 2) 1) (fun _ => 0)
    (Fin.cases x.val (fun _ => y.val)) (Fin.cases (.inl x) (fun _ => .inl y))
    (chosenSets C S) (by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> exact ⟨rfl,rfl⟩)
  rw [sparseEarlier,hc]
  simp only [capturedEarlierFormula,ActualEval,eval_capturedPreorderFormula]
  change (RawRootSeparator (fixedIndices k) (chosenSets C S) (.inl x) (.inl y) ∧
    (Sum.inl x : IncidenceOwnership.Element D) ≠ .inl y) ↔ _
  exact and_congr Iff.rfl (not_congr ⟨Sum.inl.inj, fun h => congrArg Sum.inl h⟩)

#print axioms originalSets_supported
#print axioms eval_sparseEarlier
end StackSorting.CapturedLinkExtraction
