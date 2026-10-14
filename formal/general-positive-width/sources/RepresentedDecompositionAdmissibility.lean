import SourceIntroductionPreorder
import SparseOrderWitnessAdmissibility

namespace StackSorting.GraphWidth.Nested.IntroductionSyntax
open FinitePort
open StackSorting.SparseEndpointMSO StackSorting.SparseEndpointMSO.FiniteCopy
open StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
open StackSorting.SparseEndpointMSO.EliminationSyntax
open StackSorting.ConnectedConeNormalization
variable {n t c d B : Nat} {G : Graph n} {T : RootedTree t}

/-- Exact physical-time names. Arbitrary accepted names are handled afterward
by the separately proved unchanged-formula isomorphism pullback. -/
def timeNames (M : Model) (hp : TimePath M n) : Fin n ≃ {x // x∈M.domain} where
  toFun v := ⟨v.val,by rw [hp.1]; exact List.mem_range.mpr v.isLt⟩
  invFun x := ⟨x.val, by
    have h : x.val ∈ List.range n := by simpa only [hp.1] using x.property
    exact List.mem_range.mp h⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem introduction_region_bound (D : Decomposition G T) (hb : D.BagBound B) (v : Fin n) :
    (FiniteTupleBound.points (RegionBag G (introductionOrder D) v)).card ≤ B := by
  classical
  have he : FiniteTupleBound.points (RegionBag G (introductionOrder D) v) =
      introductionFrontierSet D v := by
    ext u
    simp only [FiniteTupleBound.points,Finset.mem_filter,Finset.mem_univ,true_and,
      introductionFrontierSet]
    rw [regionBag_iff_frontier]
    exact eliminationFrontier_iff D v u
  rw [he]
  exact introductionFrontier_bound D hb v

/-- Literal admissibility from a genuine finite-copy decomposition
representation. The formula is fixed by J/tag, and its frontier bound is the
actual supplied decomposition bound. No preorder or parent atom is a premise. -/
theorem represented_decomposition_admissible (D : Decomposition G T)
    (hb : D.BagBound B) {M : Model} (hp : TimePath M n)
    (hG : ∀ u v : Fin n, G.Adj u v ↔ ModelAdjacent M u.val v.val)
    {J : Interpretation Syntax.OutputAtom c d} {params : Fin d → Nat → Prop}
    (R : Realization J M params (Carrier n t) (atoms D))
    (tag : Fin c) (hcode : ∀ v, R.rep (tag,v.val) (.inl v)) :
    Eval M (admissibleSentence (splitPreorder (sourcePreorder J tag)) B) Fin.elim0
      (flattenedSets params (fun i : Fin 0 => R.liftSet (Fin.elim0 i))) := by
  apply named_order_admissible M (timeNames M hp) _ _ (introductionOrder D) G
  · intro u v
    exact source_split_identifies D hp R tag hcode u v
  · intro u v
    exact hG u v
  · intro u v huv
    exact introductionEarlier_eliminates D huv
  · exact introduction_region_bound D hb

theorem represented_decomposition_supported_admissible (D : Decomposition G T)
    (hb : D.BagBound B) {M : Model} (hp : TimePath M n)
    (hG : ∀ u v : Fin n, G.Adj u v ↔ ModelAdjacent M u.val v.val)
    {J : Interpretation Syntax.OutputAtom c d} {params : Fin d → Nat → Prop}
    (R : Realization J M params (Carrier n t) (atoms D))
    (hs : CanonicalChoice.SupportedTuple M params)
    (tag : Fin c) (hcode : ∀ v, R.rep (tag,v.val) (.inl v)) :
    ∃ X, CanonicalChoice.SupportedTuple M X ∧
      Eval M (admissibleSentence (splitPreorder (sourcePreorder J tag)) B) Fin.elim0 X :=
  ⟨_,R.flattened_actual_supported hs Fin.elim0,
    represented_decomposition_admissible D hb hp hG R tag hcode⟩

#print axioms introduction_region_bound
#print axioms represented_decomposition_admissible
#print axioms represented_decomposition_supported_admissible
end StackSorting.GraphWidth.Nested.IntroductionSyntax
