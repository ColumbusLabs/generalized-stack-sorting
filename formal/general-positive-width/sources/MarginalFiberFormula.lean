import MarginalIncidenceAtoms

namespace StackSorting.GraphWidth.MarginalA2.Incidence
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership SparseEndpointMSO.FiniteCopy
open FinitePort Nested Actual GuidedPathwidth
variable {A : Model} {n t q W a b m : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)
variable (x : Fin t) (localNames : Fin q ≃ {v : Fin n // introductionNode D v=x})
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

/-- The entire incidence language, including nested set quantifiers, is
transported along the proved bijection to the actual owner fiber. -/
theorem eval_fiber (p : CopyFormula IncidenceAtom a b)
    (env : Fin a → Fin q ⊕ Edge D names x)
    (sets : Fin b → (Fin q ⊕ Edge D names x) → Prop)
    (outSets : Fin b → Actual.LocalCarrier D names x → Prop)
    (hs : ∀ j z, sets j z ↔ outSets j (fiberEquiv D names x localNames z)) :
    ActualEval (system D names x localNames hA hG C).atoms p env sets ↔
      ActualEval (OwnerMerge.fiberAtoms (NestedSyntax.incidenceAtoms (outputAtoms D names))
        (NestedSyntax.ownerRelation (outputAtoms D names)) (.inl (Actual.node x))) p
        (fun i => fiberEquiv D names x localNames (env i)) outSets := by
  apply actualEval_equiv _ _ (fiberEquiv D names x localNames) _ p env _ sets outSets
    (fun _ => rfl) hs
  intro r atom e
  exact (embedded_atoms D names x localNames hA hG C atom e).symm

/-- Relativization, signature projection and concrete incidence transport
compose without assuming an abstract marginal representation. -/
theorem eval_project_local (p : CopyFormula IncidenceAtom a b)
    (vars : Fin a → Fin m) (anchor : Fin m)
    (env : Fin m → Carrier.Actual (A := A) D)
    (localEnv : Fin a → Fin q ⊕ Edge D names x)
    (sets : Fin b → Carrier.Actual (A := A) D → Prop)
    (localSets : Fin b → (Fin q ⊕ Edge D names x) → Prop)
    (ha : env anchor=.inl (Actual.node x))
    (hv : ∀ i, env (vars i)=embed D names x localNames (localEnv i))
    (hs : ∀ j z, sets j (embed D names x localNames z) ↔ localSets j z) :
    ActualEval (outputAtoms D names) (NestedSyntax.project (OwnerMerge.relativize p vars anchor)) env sets ↔
      ActualEval (system D names x localNames hA hG C).atoms p localEnv localSets := by
  let e := fiberEquiv D names x localNames
  let fs : Fin b → Actual.LocalCarrier D names x → Prop := fun j z => sets j z.val
  have hproj := NestedSyntax.eval_project_relativize (outputAtoms D names)
    (.inl (Actual.node x)) p vars anchor env (fun i => e (localEnv i)) sets fs ha hv
    (fun _ _ => Iff.rfl)
  have hlocal := eval_fiber D names x localNames hA hG C p localEnv localSets fs
    (fun j z => (hs j z).symm)
  exact hproj.trans hlocal.symm

#print axioms eval_fiber
#print axioms eval_project_local
end StackSorting.GraphWidth.MarginalA2.Incidence
