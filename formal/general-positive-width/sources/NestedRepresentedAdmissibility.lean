import RepresentedDecompositionAdmissibility
import NumberedFlatteningRealization

namespace StackSorting.GraphWidth.Nested.IntroductionSyntax
open FinitePort
open StackSorting.SparseEndpointMSO StackSorting.SparseEndpointMSO.FiniteCopy
open StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
open StackSorting.SparseEndpointMSO.EliminationSyntax
open CarrierSemantics
variable {n t c d a b : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}

/-- Fixed source-vocabulary strict order for a fixed nested interpretation and
retained original-vertex tag. Its finite parameter count does not depend on
any input graph or decomposition. -/
def nestedEarlier (J : Interpretation Syntax.InputAtom c d) (tag : Fin c) :=
  splitPreorder (sourcePreorder (compose J Syntax.interpretation) (finProdFinEquiv (0,tag)))

/-- End-to-end semantic join: actual nested representation, actual local bag
bounds, and actual adhesion bounds give a supported literal admissibility
witness. The introduction preorder is the compiled formula proved above. -/
theorem nested_represented_supported_admissible (N : NestedInput D)
    (ha : ∀ x, (N.adhesionList x).length ≤ a)
    (hb : ∀ x, (N.localDecomp x).BagBound b)
    {M : Model} (hp : TimePath M n)
    (hG : ∀ u v : Fin n, G.Adj u v ↔ ModelAdjacent M u.val v.val)
    {J : Interpretation Syntax.InputAtom c d} {params : Fin d → Nat → Prop}
    (R : Realization J M params (CarrierSemantics.Carrier N) (Syntax.atoms (relations N)))
    (hs : CanonicalChoice.SupportedTuple M params)
    (tag : Fin c) (hcode : ∀ v, R.rep (tag,v.val) (vertex N v)) :
    ∃ X, CanonicalChoice.SupportedTuple M X ∧
      Eval M (admissibleSentence (nestedEarlier J tag) (a+b)) Fin.elim0 X := by
  apply represented_decomposition_supported_admissible N.flattened
    (N.flattened_bound ha hb) hp hG (numberedRealization N R)
    (R.flattened_actual_supported hs Fin.elim0) (finProdFinEquiv (0,tag))
  intro v
  exact (numbered_vertex_code N R tag v.val v).mpr (hcode v)

/-- The empty physical domain is handled directly and needs no outer node,
margin, local root or nested representation. -/
theorem empty_supported_admissible {M : Model} {k : Nat}
    (earlier : Formula 2 k) (B : Nat) (hempty : M.domain = []) :
    ∃ X : Fin k → Nat → Prop, CanonicalChoice.SupportedTuple M X ∧
      Eval M (admissibleSentence earlier B) Fin.elim0 X := by
  have noDomain : ∀ x, x ∈ M.domain → False := by
    intro x hx
    simp only [hempty,List.mem_nil_iff] at hx
  refine ⟨fun _ _ => False,?_,?_⟩
  · intro i x hx
    exact hx.elim
  · refine ⟨(eval_forestOrderSentence M earlier _).mpr ?_,
      (eval_eliminationSentence M earlier _).mpr ?_,
      (eval_frontierBoundSentence M earlier _ B).mpr ?_⟩
    · exact ⟨fun x hx => (noDomain x hx).elim,
        fun x hx => (noDomain x hx).elim,fun x hx => (noDomain x hx).elim⟩
    · exact fun x hx => (noDomain x hx).elim
    · exact fun x hx => (noDomain x hx).elim

#print axioms nested_represented_supported_admissible
#print axioms empty_supported_admissible
end StackSorting.GraphWidth.Nested.IntroductionSyntax
