import ReplacementAppendixSeparation
import ReplacementMergedSupport

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {old : V → E → Prop} {inserted : V → F → Prop} {s t : V} {removed : E}
namespace ReplacementFrame

omit [Fintype V] [DecidableEq V] in
theorem surviving_appendix_old_support
    (R : ReplacementFrame old inserted s t removed) (p : Path old s t)
    (new_to_anchor : ∀ x ∈ R.newVertices, Nonempty (HWalk inserted x R.anchor))
    (removed_in_new : ∀ x, old x removed → x ∈ R.newVertices)
    (e : E) (he : Cutedge old s t e) (hne : e ≠ removed)
    (x : V) (hx : x ∈ R.oldVertices ∨ x ∈ R.newVertices)
    (hregion : AppendixRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (.inl ⟨e,hne⟩) x) :
    AppendixRegion (inc := old) (s := s) (t := t) e x := by
  classical
  have hxo : x ∈ R.oldVertices := hx.elim id
    (fun hxn => (R.surviving_appendix_avoids_inserted p new_to_anchor e he hne x hxn hregion).elim)
  have avoids : ∀ y, SameCutedgeComponent old s t x y → ¬ old y removed := by
    intro y hxy hyr
    have hnew := old_component_survives_replacement removed R.removed_cutedge R.inserted_connects hxy
    have hyregion : AppendixRegion (inc := ReplacementIncidence old inserted removed)
        (s := s) (t := t) (.inl ⟨e,hne⟩) y := by
      intro b hb
      exact (componentTouches_congr hnew b).symm.trans (hregion b hb)
    exact R.surviving_appendix_avoids_inserted p new_to_anchor e he hne y
      (removed_in_new y hyr) hyregion
  intro b hb
  by_cases hbr : b = .cut removed
  · subst b
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact (avoids y hxy hy).elim
    · intro h
      exact (hne (CutBoundary.cut.inj h).symm).elim
  · have hiff := R.unaffected_surviving_boundary_iff x hxo avoids b hbr
    constructor
    · intro hxb
      have hEq := (hregion _ (R.survivingBoundary_valid b hbr hb)).mp (hiff.mpr hxb)
      have hne' : (CutBoundary.cut e : CutBoundary E) ≠ .cut removed :=
        fun h => hne (CutBoundary.cut.inj h)
      exact survivingBoundary_injective hbr hne' hEq
    · intro h
      subst b
      exact hiff.mp ((hregion _ (R.survivingBoundary_valid (.cut e) hbr he)).mpr rfl)

/-- Surviving appendices inherit their actual old bags by restriction; no
component equality or output decomposition is supplied as a hypothesis. -/
noncomputable def survivingAppendixBagPath
    (R : ReplacementFrame old inserted s t removed) (p : Path old s t)
    (new_to_anchor : ∀ x ∈ R.newVertices, Nonempty (HWalk inserted x R.anchor))
    (removed_in_new : ∀ x, old x removed → x ∈ R.newVertices)
    (e : E) (he : Cutedge old s t e) (hne : e ≠ removed) (k : Nat) (P : Finset V)
    (part_support : ∀ x ∈ P, x ∈ R.oldVertices ∨ x ∈ R.newVertices)
    (part_region : ∀ x ∈ P, AppendixRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (.inl ⟨e,hne⟩) x)
    (D : BagPath (appendixVertices old s t e) (k+1)) (hD : D.Covers old)
    (hfirst : ∀ x ∈ appendixVertices old s t e, old x e → x ∈ D.bag 0) :
    {Q : BagPath P (k+1) // Q.Covers (ReplacementIncidence old inserted removed) ∧
      ∀ x ∈ P, old x e → x ∈ Q.bag 0} := by
  classical
  have hsub : P ⊆ appendixVertices old s t e := by
    intro x hx
    exact (mem_appendixVertices old s t e x).mpr
      (R.surviving_appendix_old_support p new_to_anchor removed_in_new e he hne x
        (part_support x hx) (part_region x hx))
  let Q := D.restrictSubset P hsub
  refine ⟨Q,?_,?_⟩
  · intro f
    cases f with
    | inl f => exact D.restrictSubset_covers P hsub hD f.val
    | inr f =>
      refine ⟨0,Nat.zero_le _,?_⟩
      intro x hx hxf
      exact (R.surviving_appendix_avoids_inserted p new_to_anchor e he hne x
        (R.new_support x f hxf) (part_region x hx)).elim
  · intro x hx hxe
    exact Finset.mem_inter.mpr ⟨hfirst x (hsub hx) hxe,hx⟩

end ReplacementFrame
end FiniteFlow.Hypergraph
