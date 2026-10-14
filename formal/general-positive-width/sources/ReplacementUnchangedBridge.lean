import ReplacementMergedSupport
import OrientedBridgeCertificates

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {old : V → E → Prop} {inserted : V → F → Prop} {s t : V} {removed : E}
namespace ReplacementFrame

/-- A two-old-boundary bridge disjoint from the inserted vertices inherits an
actual old local bag path. The absence of the removed edge in each component
is derived from the exact new region and the inclusion of its old incidences in K. -/
noncomputable def unchangedBridgeBagPath
    (R : ReplacementFrame old inserted s t removed) (p : Path old s t) (k : Nat)
    (T : ThinNetworkLocalWitnesses p k) (P : Finset V)
    (removed_in_new : ∀ x, old x removed → x ∈ R.newVertices)
    (part_support : ∀ x ∈ P, x ∈ R.oldVertices ∨ x ∈ R.newVertices)
    (avoids_new : ∀ x ∈ P, x ∉ R.newVertices)
    (b c : CutBoundary E)
    (hb : BoundaryValid (inc := old) (s := s) (t := t) b)
    (hc : BoundaryValid (inc := old) (s := s) (t := t) c)
    (hbr : b ≠ .cut removed) (hcr : c ≠ .cut removed) (hbc : b ≠ c)
    (part_exact : ∀ x, x ∈ P ↔ BridgeRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (survivingBoundary (F := F) b hbr) (survivingBoundary (F := F) c hcr) x) :
    {Q : BagPath P (2*k+2) // Q.Covers (ReplacementIncidence old inserted removed) ∧
      (∀ x ∈ P, BoundaryIncidence (inc := ReplacementIncidence old inserted removed)
        (s := s) (t := t) x (survivingBoundary (F := F) b hbr) → x ∈ Q.bag 0) ∧
      (∀ x ∈ P, BoundaryIncidence (inc := ReplacementIncidence old inserted removed)
        (s := s) (t := t) x (survivingBoundary (F := F) c hcr) → x ∈ Q.bag Q.last)} := by
  classical
  have old_region : ∀ x ∈ P, BridgeRegion (inc := old) (s := s) (t := t) b c x := by
    intro x hx
    have hxo : x ∈ R.oldVertices := (part_support x hx).elim id (fun hn => (avoids_new x hx hn).elim)
    have hregion := (part_exact x).mp hx
    have avoids : ∀ y, SameCutedgeComponent old s t x y → ¬ old y removed := by
      intro y hxy hyr
      have hnew := old_component_survives_replacement removed R.removed_cutedge R.inserted_connects hxy
      have hyregion : BridgeRegion (inc := ReplacementIncidence old inserted removed)
          (s := s) (t := t) (survivingBoundary (F := F) b hbr) (survivingBoundary (F := F) c hcr) y := by
        intro d hd
        exact (componentTouches_congr hnew d).symm.trans (hregion d hd)
      exact avoids_new y ((part_exact y).mpr hyregion) (removed_in_new y hyr)
    intro d hd
    by_cases hdr : d = .cut removed
    · subst d
      constructor
      · rintro ⟨y,hy,hxy⟩
        exact (avoids y hxy hy).elim
      · rintro (h | h)
        · exact (hbr h.symm).elim
        · exact (hcr h.symm).elim
    · have hiff := R.unaffected_surviving_boundary_iff x hxo avoids d hdr
      constructor
      · intro hxd
        rcases (hregion _ (R.survivingBoundary_valid d hdr hd)).mp (hiff.mpr hxd) with h | h
        · exact Or.inl (survivingBoundary_injective hdr hbr h)
        · exact Or.inr (survivingBoundary_injective hdr hcr h)
      · rintro (rfl | rfl)
        · exact hiff.mp ((hregion _ (R.survivingBoundary_valid _ hdr hd)).mpr (Or.inl rfl))
        · exact hiff.mp ((hregion _ (R.survivingBoundary_valid _ hdr hd)).mpr (Or.inr rfl))
  let ii := List.mem_iff_get.mp ((mem_boundaryTrace p b).mpr hb)
  let i := Classical.choose ii
  have hi : (boundaryTrace p).get i = b := Classical.choose_spec ii
  let jj := List.mem_iff_get.mp ((mem_boundaryTrace p c).mpr hc)
  let j := Classical.choose jj
  have hj : (boundaryTrace p).get j = c := Classical.choose_spec jj
  have hij : i ≠ j := by
    intro h
    exact hbc (hi.symm.trans ((congrArg (fun a => (boundaryTrace p).get a) h).trans hj))
  let dd := T.oriented_bridge p k i j hij
  let D := Classical.choose dd
  have hD := (Classical.choose_spec dd).1
  have hfirst := (Classical.choose_spec dd).2.1
  have hlast := (Classical.choose_spec dd).2.2
  have hsub : P ⊆ bridgeVertices p i j := by
    intro x hx
    apply (mem_bridgeVertices p i j x).mpr
    rw [hi,hj]
    exact old_region x hx
  let Q := D.restrictSubset P hsub
  refine ⟨Q,?_,?_,?_⟩
  · intro e
    cases e with
    | inl e => exact D.restrictSubset_covers P hsub hD e.val
    | inr f =>
      refine ⟨0,Nat.zero_le _,?_⟩
      intro x hx hxf
      exact (avoids_new x hx (R.new_support x f hxf)).elim
  · intro x hx hxb
    have hbold := (boundaryIncidence_surviving b hbr x).mp hxb
    have hbi := (mem_boundaryVertices p i x).mpr (hi.symm ▸ hbold)
    exact Finset.mem_inter.mpr ⟨hfirst x (hsub hx) hbi,hx⟩
  · intro x hx hxc
    have hcold := (boundaryIncidence_surviving c hcr x).mp hxc
    have hcj := (mem_boundaryVertices p j x).mpr (hj.symm ▸ hcold)
    exact Finset.mem_inter.mpr ⟨hlast x (hsub hx) hcj,hx⟩

end ReplacementFrame
end FiniteFlow.Hypergraph
