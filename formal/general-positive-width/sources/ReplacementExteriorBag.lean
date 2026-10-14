import ReplacementInsertedInterior
import BagPathReversal

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {old : V → E → Prop} {inserted : V → F → Prop} {s t : V} {removed : E}

noncomputable def exteriorOldVertices (old : V → E → Prop) (s t : V)
    (b : CutBoundary E) (removed : E) : Finset V := by
  classical
  exact Finset.univ.filter (BridgeRegion (inc := old) (s := s) (t := t) b (.cut removed))

omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_exteriorOldVertices (old : V → E → Prop) (s t : V)
    (b : CutBoundary E) (removed : E) (x : V) :
    x ∈ exteriorOldVertices old s t b removed ↔
      BridgeRegion (inc := old) (s := s) (t := t) b (.cut removed) x := by
  classical
  simp [exteriorOldVertices]

namespace ReplacementFrame

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem boundaryIncidence_supported (R : ReplacementFrame old inserted s t removed)
    (x : V) (b : CutBoundary E)
    (hx : BoundaryIncidence (inc := old) (s := s) (t := t) x b) : x ∈ R.oldVertices := by
  cases b with
  | source => exact hx.symm ▸ R.source_old
  | sink => exact hx.symm ▸ R.sink_old
  | cut e => exact R.old_support x e hx

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem boundaryIncidence_surviving (b : CutBoundary E) (hne : b ≠ .cut removed) (x : V) :
    BoundaryIncidence (inc := ReplacementIncidence old inserted removed) (s := s) (t := t)
      x (survivingBoundary (F := F) b hne) ↔
    BoundaryIncidence (inc := old) (s := s) (t := t) x b := by
  cases b <;> rfl

omit [DecidableEq V] [DecidableEq E] in
theorem exteriorOld_supported (R : ReplacementFrame old inserted s t removed)
    (b : CutBoundary E) (x : V) (hx : x ∈ exteriorOldVertices old s t b removed) :
    x ∈ R.oldVertices := by
  have hr := (mem_exteriorOldVertices old s t b removed x).mp hx
  obtain ⟨y,hy,hxy⟩ := (hr (.cut removed) R.removed_cutedge).mpr (Or.inr rfl)
  exact old_component_supported R.oldVertices R.old_support
    (R.old_support y removed hy) (sameCutedgeComponent_symm old s t hxy)

/-- Actual left-exterior bridge surgery. Its region split, overlap seam and
whole-hyperedge localization are all derived, including surviving old cutedges.
Only the old local thinness witnesses and primitive replacement data are inputs. -/
noncomputable def exteriorBridgeBagPath
    (R : ReplacementFrame old inserted s t removed) (k : Nat)
    (K P : Finset V) (small : K.card ≤ k+1)
    (K_exact : ∀ x, x ∈ R.newVertices ↔ x ∈ K)
    (part_support : ∀ x ∈ P, x ∈ R.oldVertices ∨ x ∈ K)
    (b : CutBoundary E) (hb : BoundaryValid (inc := old) (s := s) (t := t) b)
    (hne : b ≠ .cut removed) (f : F)
    (hf : Cutedge (ReplacementIncidence old inserted removed) s t (.inr f))
    (part_region : ∀ x ∈ P, BridgeRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (survivingBoundary (F := F) b hne) (.cut (.inr f)) x)
    (A : BagPath (exteriorOldVertices old s t b removed) (2*k+2)) (hA : A.Covers old)
    (Afirst : ∀ x ∈ exteriorOldVertices old s t b removed,
      BoundaryIncidence (inc := old) (s := s) (t := t) x b → x ∈ A.bag 0)
    (Alast : ∀ x ∈ exteriorOldVertices old s t b removed, old x removed → x ∈ A.bag A.last)
    (D : BagPath (appendixVertices old s t removed) (k+1)) (hD : D.Covers old) :
    {Q : BagPath P (2*k+2) // Q.Covers (ReplacementIncidence old inserted removed) ∧
      (∀ x ∈ P, BoundaryIncidence (inc := ReplacementIncidence old inserted removed)
        (s := s) (t := t) x (survivingBoundary (F := F) b hne) → x ∈ Q.bag 0) ∧
      (∀ x ∈ P, inserted x f → x ∈ Q.bag Q.last)} := by
  classical
  let B := exteriorOldVertices old s t b removed
  let W := appendixVertices old s t removed
  have old_part : ∀ x ∈ P, x ∈ R.oldVertices → x ∈ W ∨ x ∈ B := by
    intro x hx hxo
    rcases R.exterior_bridge_old_support x hxo b hne f hf (part_region x hx) with hw | hbridge
    · exact Or.inl ((mem_appendixVertices old s t removed x).mpr hw)
    · apply Or.inr
      apply (mem_exteriorOldVertices old s t b removed x).mpr
      intro c hc
      exact (hbridge c hc).trans or_comm
  have disjoint : ∀ x, x ∈ B → x ∈ W → False := by
    intro x hxB hxW
    have hB := (mem_exteriorOldVertices old s t b removed x).mp hxB
    have hW := (mem_appendixVertices old s t removed x).mp hxW
    exact hne ((hW b hb).mp ((hB b hb).mpr (Or.inl rfl)))
  have hK : ∀ x g, inserted x g → x ∈ K :=
    fun x g hxg => (K_exact x).mp (R.new_support x g hxg)
  let L := A.restrict P
  let C := D.replacementInterior P K small
  have split : (B ∩ P) ∪ ((W ∩ P) ∪ (K ∩ P)) = P := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).2
      · rcases Finset.mem_union.mp hx with hx | hx
        · exact (Finset.mem_inter.mp hx).2
        · exact (Finset.mem_inter.mp hx).2
    · intro x hx
      rcases part_support x hx with hxo | hxK
      · rcases old_part x hx hxo with hxW | hxB
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxW,hx⟩))
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxB,hx⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxK,hx⟩))
  have seam : ∀ x ∈ (B ∩ P) ∩ ((W ∩ P) ∪ (K ∩ P)), x ∈ L.bag L.last ∧ x ∈ C.bag 0 := by
    intro x hx
    obtain ⟨hxL,hxC⟩ := Finset.mem_inter.mp hx
    obtain ⟨hxB,hxP⟩ := Finset.mem_inter.mp hxL
    have hxKP : x ∈ K ∩ P := by
      rcases Finset.mem_union.mp hxC with hxW | hxK
      · exact (disjoint x hxB (Finset.mem_inter.mp hxW).1).elim
      · exact hxK
    have hremoved := R.overlap x (R.exteriorOld_supported b x hxB)
      ((K_exact x).mpr (Finset.mem_inter.mp hxKP).1)
    exact ⟨Finset.mem_inter.mpr ⟨Alast x hxB hremoved,hxP⟩,
      D.replacementInterior_boundary P K small 0 hxKP⟩
  have hL : L.Covers (ReplacementIncidence old inserted removed) := by
    intro e
    cases e with
    | inl e => exact A.restrict_covers P hA e.val
    | inr g =>
      refine ⟨L.last,le_rfl,?_⟩
      intro x hx hxg
      obtain ⟨hxB,hxP⟩ := Finset.mem_inter.mp hx
      have hr := R.overlap x (R.exteriorOld_supported b x hxB) (R.new_support x g hxg)
      exact Finset.mem_inter.mpr ⟨Alast x hxB hr,hxP⟩
  have hC : C.Covers (ReplacementIncidence old inserted removed) :=
    D.replacementInterior_covers P K small removed hD hK
  have localized : ∀ e, (∀ x ∈ (B ∩ P) ∪ ((W ∩ P) ∪ (K ∩ P)),
      ReplacementIncidence old inserted removed x e → x ∈ B ∩ P) ∨
      (∀ x ∈ (B ∩ P) ∪ ((W ∩ P) ∪ (K ∩ P)),
      ReplacementIncidence old inserted removed x e → x ∈ (W ∩ P) ∪ (K ∩ P)) := by
    intro e
    cases e with
    | inr g =>
      apply Or.inr
      intro x hx hxg
      rw [split] at hx
      exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hK x g hxg,hx⟩)
    | inl e =>
      by_cases he : Cutedge old s t e.val
      · apply Or.inl
        intro x hx hxe
        rw [split] at hx
        rcases old_part x hx (R.old_support x e.val hxe) with hxW | hxB
        · exact (e.property (appendix_incident_cutedge_eq
            ((mem_appendixVertices old s t removed x).mp hxW) he hxe)).elim
        · exact Finset.mem_inter.mpr ⟨hxB,hx⟩
      · by_cases hex : ∃ x ∈ P, old x e.val
        · obtain ⟨x,hx,hxe⟩ := hex
          rcases old_part x hx (R.old_support x e.val hxe) with hxW | hxB
          · apply Or.inr
            intro y hy hye
            rw [split] at hy
            have hyW := noncut_edge_appendix_localized he hxe
              ((mem_appendixVertices old s t removed x).mp hxW) y hye
            exact Finset.mem_union_left _ (Finset.mem_inter.mpr
              ⟨(mem_appendixVertices old s t removed y).mpr hyW,hy⟩)
          · apply Or.inl
            intro y hy hye
            rw [split] at hy
            have hyB := noncut_edge_bridge_localized he hxe
              ((mem_exteriorOldVertices old s t b removed x).mp hxB) y hye
            exact Finset.mem_inter.mpr ⟨(mem_exteriorOldVertices old s t b removed y).mpr hyB,hy⟩
        · apply Or.inl
          intro x hx hxe
          rw [split] at hx
          exact (hex ⟨x,hx,hxe⟩).elim
  let Q := L.concat C seam
  have hQ := L.concat_covers C seam hL hC localized
  refine ⟨Q.recast split,Q.recast_covers split hQ,?_,?_⟩
  · intro x hx hxb
    have hbold := (boundaryIncidence_surviving b hne x).mp hxb
    have hxo := R.boundaryIncidence_supported x b hbold
    have hxB : x ∈ B := by
      rcases old_part x hx hxo with hxW | hxB
      · have hw := (mem_appendixVertices old s t removed x).mp hxW
        exact (hne ((hw b hb).mp (boundary_incidence_touches x b hbold))).elim
      · exact hxB
    change x ∈ Q.bag 0
    rw [BagPath.concat_first]
    exact Finset.mem_inter.mpr ⟨Afirst x hxB hbold,hx⟩
  · intro x hx hxf
    change x ∈ Q.bag Q.last
    rw [BagPath.concat_last]
    exact D.replacementInterior_boundary P K small C.last
      (Finset.mem_inter.mpr ⟨hK x f hxf,hx⟩)

end ReplacementFrame
end FiniteFlow.Hypergraph
