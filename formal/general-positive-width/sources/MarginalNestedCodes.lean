import MarginalNestedSyntax
import MarginalOwnerFibers
import MarginalLocalNodeNames

namespace StackSorting.GraphWidth.MarginalA2.NestedCodes
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric FinitePort Nested
variable {A : Model} {n t colors : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)
variable (X : Fin (CapturedLinkExtraction.parameterCount colors) → Carrier.Actual (A := A) D → Prop)

/-- Original vertices, outer owners, local vertex nodes, local empty roots. -/
abbrev FlatCarrier (n t : Nat) := Fin n ⊕ (Fin t ⊕ (Fin n ⊕ Fin t))
abbrev Step := StepElement (NestedSyntax.interpretation colors) (Actual.outputAtoms D names) X

noncomputable def encode : FlatCarrier n t → Step D names X
  | .inl v => ⟨(0,.inl (Actual.vertex names v)),by
      simp [NestedSyntax.interpretation,NestedSyntax.domain,NestedSyntax.disj,NestedSyntax.unary,
        ActualEval,Actual.outputAtoms,Actual.outerAtoms,Actual.vertex,IsVertex]⟩
  | .inr (.inl x) => ⟨(0,.inl (Actual.node x)),by
      simp [NestedSyntax.interpretation,NestedSyntax.domain,NestedSyntax.disj,NestedSyntax.unary,
        ActualEval,Actual.outputAtoms,Actual.outerAtoms,Actual.node]⟩
  | .inr (.inr (.inl v)) => ⟨(1,.inl (Actual.vertex names v)),by
      simp [NestedSyntax.interpretation,NestedSyntax.domain,NestedSyntax.unary,
        ActualEval,Actual.outputAtoms,Actual.outerAtoms,Actual.vertex,IsVertex]⟩
  | .inr (.inr (.inr x)) => ⟨(2,.inl (Actual.node x)),by
      simp [NestedSyntax.interpretation,NestedSyntax.domain,NestedSyntax.unary,
        ActualEval,Actual.outputAtoms,Actual.outerAtoms,Actual.node]⟩

@[simp] theorem original_code (v : Fin n) :
    (encode D names X (.inl v)).val=(0,.inl (Actual.vertex names v)) := rfl

theorem encode_injective : Function.Injective (encode D names X) := by
  intro u v h
  have he := congrArg Subtype.val h
  rcases u with u | (u | (u | u)) <;> rcases v with v | (v | (v | v)) <;>
    simp only [encode,Prod.mk.injEq,Actual.vertex,Actual.node,Sum.inl.injEq,Sum.inr.injEq,
       ] at he <;>
    simp_all
  all_goals exact names.injective (Sum.inl.inj (Sum.inl.inj he))

theorem encode_surjective : Function.Surjective (encode D names X) := by
  rintro ⟨⟨tag,z⟩,hz⟩
  change ActualEval (Actual.outputAtoms D names) (NestedSyntax.domain tag) (fun _ => z) X at hz
  fin_cases tag <;> rcases z with ((v | e) | x) | e <;>
    simp [NestedSyntax.domain,NestedSyntax.disj,NestedSyntax.unary,ActualEval,
      Actual.outputAtoms,Actual.outerAtoms,IsVertex] at hz
  · exact ⟨.inl (names.symm v),by apply Subtype.ext; simp [encode,Actual.vertex]⟩
  · exact ⟨.inr (.inl x),rfl⟩
  · exact ⟨.inr (.inr (.inl (names.symm v))),by apply Subtype.ext; simp [encode,Actual.vertex]⟩
  · exact ⟨.inr (.inr (.inr x)),rfl⟩

noncomputable def codeEquiv : FlatCarrier n t ≃ Step D names X :=
  Equiv.ofBijective (encode D names X) ⟨encode_injective D names X,encode_surjective D names X⟩

#print axioms original_code
#print axioms codeEquiv
end StackSorting.GraphWidth.MarginalA2.NestedCodes
