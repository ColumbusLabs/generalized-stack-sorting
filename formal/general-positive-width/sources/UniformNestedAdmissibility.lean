import NestedRepresentedAdmissibility
import PhysicalCanonicalWitnessTransport

namespace StackSorting.GraphWidth.Nested.IntroductionSyntax
open FinitePort
open StackSorting.SparseEndpointMSO StackSorting.SparseEndpointMSO.FiniteCopy
open StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
open StackSorting.SparseEndpointMSO.EliminationSyntax

/-- The concrete remaining existence interface. Every datum is an actual
finite graph, decomposition, bag, supported set, or pointwise finite-copy
realization. The interpretation, tag and numerical bounds are fixed outside
this input-dependent witness. -/
structure NestedSourceWitness {c d : Nat}
    (J : Interpretation Syntax.InputAtom c d) (tag : Fin c)
    (a b : Nat) (M : Model) where
  size : Nat
  graph : Graph size
  treeSize : Nat
  tree : RootedTree treeSize
  outer : Decomposition graph tree
  nested : NestedInput outer
  adhesionBound : ∀ x, (nested.adhesionList x).length ≤ a
  localBound : ∀ x, (nested.localDecomp x).BagBound b
  physicalTime : TimePath M size
  adjacency : ∀ u v : Fin size, graph.Adj u v ↔ ModelAdjacent M u.val v.val
  params : Fin d → Nat → Prop
  supported : CanonicalChoice.SupportedTuple M params
  realization : Realization J M params (CarrierSemantics.Carrier nested)
    (Syntax.atoms (CarrierSemantics.relations nested))
  vertexCode : ∀ v, realization.rep (tag,v.val) (CarrierSemantics.vertex nested v)

theorem NestedSourceWitness.supported_admissible {c d a b : Nat}
    {J : Interpretation Syntax.InputAtom c d} {tag : Fin c} {M : Model}
    (W : NestedSourceWitness J tag a b M) :
    ∃ X, CanonicalChoice.SupportedTuple M X ∧
      Eval M (admissibleSentence (nestedEarlier J tag) (a+b)) Fin.elim0 X :=
  nested_represented_supported_admissible W.nested W.adhesionBound W.localBound
    W.physicalTime W.adjacency W.realization W.supported tag W.vertexCode

/-- Conditional final quantifier join. The substantive nonempty witness
existence premise is explicit. Empty models are discharged directly, and
arbitrary domain names are handled by unchanged-formula isomorphism pullback.
This theorem does not construct the nonempty witnesses. -/
theorem canonical_nested_witnesses_give_uniform_admissibility {c d : Nat}
    (J : Interpretation Syntax.InputAtom c d) (tag : Fin c) (a b r s : Nat)
    (h : ∀ n output, output.Perm (List.range n) →
      Generalized.Run r s [] (List.range n) output [] →
      (canonicalDiagram output).domain ≠ [] →
      Nonempty (NestedSourceWitness J tag a b (canonicalDiagram output))) :
    ∀ M : Model, Satisfies M (fullAcceptedSentence r s) →
      ∃ X, CanonicalChoice.SupportedTuple M X ∧
        Eval M (admissibleSentence (nestedEarlier J tag) (a+b)) Fin.elim0 X := by
  apply CanonicalChoice.canonical_witnesses_cover_accepted _ r s
  intro n output hp hr
  classical
  by_cases he : (canonicalDiagram output).domain = []
  · exact empty_supported_admissible _ _ he
  · obtain ⟨W⟩ := h n output hp hr he
    exact W.supported_admissible

#print axioms NestedSourceWitness.supported_admissible
#print axioms canonical_nested_witnesses_give_uniform_admissibility
end StackSorting.GraphWidth.Nested.IntroductionSyntax
