import PhysicalCanonicalUniqueness

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseEndpointMSO

def Isomorphism.carrierEquiv {D E : Model} (iso : Isomorphism D E) :
    {x // x ∈ D.domain} ≃ {x // x ∈ E.domain} where
  toFun x := ⟨iso.toFun x.val,iso.to_mem x.val x.property⟩
  invFun y := ⟨iso.invFun y.val,iso.inv_mem y.val y.property⟩
  left_inv x := Subtype.ext (iso.left_inv x.val x.property)
  right_inv y := Subtype.ext (iso.right_inv y.val y.property)

def DomainInterpretation.transportIsomorphism {P : Type} {D E : Model} {R : Relations P}
    (J : DomainInterpretation D R) (iso : Isomorphism D E) : DomainInterpretation E R where
  vertex := J.vertex.trans iso.carrierEquiv
  insert_iff p := (iso.insert_iff (J.vertex p).val (J.vertex p).property).symm.trans (J.insert_iff p)
  remove_iff p := (iso.remove_iff (J.vertex p).val (J.vertex p).property).symm.trans (J.remove_iff p)
  successor_iff p q :=
    (iso.successor_iff (J.vertex p).val (J.vertex p).property
      (J.vertex q).val (J.vertex q).property).symm.trans (J.successor_iff p q)
  matching_iff p q :=
    (iso.matching_iff (J.vertex p).val (J.vertex p).property
      (J.vertex q).val (J.vertex q).property).symm.trans (J.matching_iff p q)

end StackSorting.SparseEndpointMSO

namespace StackSorting.SparseTreeCompiler
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO
open FinitePort FinitePort.ChildSibling FinitePort.ChildSibling.BinaryOrderMSO

theorem physical_same_model_canonical_tree_unique {D : Model} {r s k b : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (earlier : SparseEndpointMSO.Formula 2 k)
    (t u : BinaryTree (Alphabet 2 2 (b-1)))
    (J : SameNodeDecoding (physicalPortDecoder (b-1)) D t)
    (K : SameNodeDecoding (physicalPortDecoder (b-1)) D u)
    (ht : (canonicalCodeSentence earlier b r s).EvalAt t Fin.elim0)
    (hu : (canonicalCodeSentence earlier b r s).EvalAt u Fin.elim0) : t=u := by
  have st := (evalAt_normalizedShapeSentence t).mp ht.2.1.1.1
  have su := (evalAt_normalizedShapeSentence u).mp hu.2.1.1.1
  rcases st with rfl | ⟨a,l,rfl⟩
  · rcases su with rfl | ⟨a,l,rfl⟩
    · rfl
    · exact nomatch J.vertex.symm (K.vertex Position.root)
  · rcases su with rfl | ⟨a',l',rfl⟩
    · exact nomatch K.vertex.symm (J.vertex Position.root)
    · exact physical_same_model_canonical_unique hD earlier a a' l l' J K ht hu

/-- Different temporary names and different initially chosen parent trees
cannot duplicate a physical object in this literal canonical language. -/
theorem canonical_code_isomorphism_unique {r s k b : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k)
    (t u : BinaryTree (Alphabet 2 2 (b-1)))
    (ht : (canonicalCodeSentence earlier b r s).EvalAt t Fin.elim0)
    (hu : (canonicalCodeSentence earlier b r s).EvalAt u Fin.elim0)
    (iso : Isomorphism (decodedModel (physicalPortDecoder (b-1)) t)
      (decodedModel (physicalPortDecoder (b-1)) u)) : t=u := by
  let J := decodedModel_sameNode (physicalPortDecoder (b-1)) t
  let K := (decodedModel_sameNode (physicalPortDecoder (b-1)) u).transportIsomorphism iso.symm
  have hD := (J.satisfies (fullAcceptedSentence r s)).mpr
    ((sentence_evalAt _ _ _).mp ht.1)
  exact physical_same_model_canonical_tree_unique hD earlier t u J K ht hu

/-- Exact injectivity at the physical output level, rather than at a supplied
decomposition or a single fixed parent tree. -/
theorem canonical_code_output_unique {r s k b : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k)
    (t u : BinaryTree (Alphabet 2 2 (b-1)))
    (ht : (canonicalCodeSentence earlier b r s).EvalAt t Fin.elim0)
    (hu : (canonicalCodeSentence earlier b r s).EvalAt u Fin.elim0)
    (output : List Nat)
    (it : Isomorphism (decodedModel (physicalPortDecoder (b-1)) t) (canonicalDiagram output))
    (iu : Isomorphism (decodedModel (physicalPortDecoder (b-1)) u) (canonicalDiagram output)) : t=u :=
  canonical_code_isomorphism_unique earlier t u ht hu (it.trans iu.symm)

#print axioms canonical_code_isomorphism_unique
#print axioms canonical_code_output_unique
end StackSorting.SparseTreeCompiler
