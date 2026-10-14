import MarginalNestedRealization

namespace StackSorting.GraphWidth.MarginalA2
open FinitePort Nested SparseEndpointMSO SparseEndpointMSO.FiniteCopy SparseEndpointMSO.FiniteCopy.Parametric
open SparseEndpointMSO.IncidenceOwnership

noncomputable def marginalRetainedTag (W : Nat) : Fin (Syntax.copies W) := Syntax.tagEquiv W (.inl ())
def nestedRetainedTag {c : Nat} (tag : Fin c) : Fin (3*c) := finProdFinEquiv ((0 : Fin 3),tag)
noncomputable def fullRetainedTag {c : Nat} (W : Nat) (tag : Fin c) : Fin (3*(Syntax.copies W*c)) :=
  nestedRetainedTag (finProdFinEquiv (marginalRetainedTag W,tag))

variable {A : Model} {n t k W c d : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A) (C : AdhesionColoring D W)

theorem marginal_original_rep {J : Parametric.Interpretation Syntax.InputAtom c d}
    {params : Fin d → Nat → Prop}
    (R : Parametric.Realization J A params (Carrier.Base A t) (Actual.outerAtoms D names))
    (tag : Fin c) (number : Nat) (v : Fin n) :
    (Actual.realization D names C R).rep (finProdFinEquiv (marginalRetainedTag W,tag),number)
      (.inl (Actual.vertex names v)) ↔ R.rep (tag,number) (Actual.vertex names v) := by
  change (outerTag (finProdFinEquiv (marginalRetainedTag W,tag))=marginalRetainedTag W ∧
    R.rep (innerTag (finProdFinEquiv (marginalRetainedTag W,tag)),number) (Actual.vertex names v)) ↔ _
  simp only [outerTag,innerTag,Equiv.symm_apply_apply,true_and]

#print axioms marginal_original_rep
end StackSorting.GraphWidth.MarginalA2

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested SparseEndpointMSO SparseEndpointMSO.FiniteCopy SparseEndpointMSO.FiniteCopy.Parametric
open SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W c d : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (ht : 0<t) (hm : ∀ x, ∃ v, introductionNode D v=x)
variable (hc : ConnectedIntroductionComponents D)
variable (names : Fin n ≃ Vertex A) (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem nested_original_rep {J : Parametric.Interpretation Syntax.OutputAtom c d}
    {params : Fin d → Nat → Prop}
    (R : Parametric.Realization J A params (Carrier.Actual (A := A) D) (Actual.outputAtoms D names))
    (tag : Fin c) (number : Nat) (v : Fin n) :
    (F.nestedRealization ht hm hc names hA hG C R).rep (nestedRetainedTag tag,number) (.inl v) ↔
      R.rep (tag,number) (.inl (Actual.vertex names v)) := by
  change (outerTag (nestedRetainedTag tag)=0 ∧
    R.rep (innerTag (nestedRetainedTag tag),number) (.inl (Actual.vertex names v))) ↔ _
  simp only [nestedRetainedTag,outerTag,innerTag,Equiv.symm_apply_apply,true_and]

#print axioms nested_original_rep
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
