import ReplacementMergedSupport
import OrientedBridgeCertificates
import BagPathTripleAssembly

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {old : V → E → Prop} {inserted : V → F → Prop} {s t : V} {removed : E}
namespace ReplacementFrame

/-- The two-old-boundary replacement case is assembled from both actual old
exterior bridges and the augmented removed appendix. The support classification,
all seams, and full-edge localization are derived from primitive incidence data. -/
noncomputable def mergedBridgeBagPath
    (R : ReplacementFrame old inserted s t removed) (p : Path old s t) (k : Nat)
    (T : ThinNetworkLocalWitnesses p k) (K P : Finset V) (small : K.card ≤ k+1)
    (K_exact : ∀ x, x ∈ R.newVertices ↔ x ∈ K)
    (part_support : ∀ x ∈ P, x ∈ R.oldVertices ∨ x ∈ K)
    (b c : CutBoundary E)
    (hb : BoundaryValid (inc := old) (s := s) (t := t) b)
    (hc : BoundaryValid (inc := old) (s := s) (t := t) c)
    (hbr : b ≠ .cut removed) (hcr : c ≠ .cut removed) (hbc : b ≠ c)
    (part_region : ∀ x ∈ P, BridgeRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (survivingBoundary (F := F) b hbr) (survivingBoundary (F := F) c hcr) x)
    (z : V) (hzK : z ∈ K) (hzP : z ∈ P) :
    {Q : BagPath P (2*k+2) // Q.Covers (ReplacementIncidence old inserted removed) ∧
      (∀ x ∈ P, BoundaryIncidence (inc := ReplacementIncidence old inserted removed)
        (s := s) (t := t) x (survivingBoundary (F := F) b hbr) → x ∈ Q.bag 0) ∧
      (∀ x ∈ P, BoundaryIncidence (inc := ReplacementIncidence old inserted removed)
        (s := s) (t := t) x (survivingBoundary (F := F) c hcr) → x ∈ Q.bag Q.last)} := by
  classical
  let B := exteriorOldVertices old s t b removed
  let C := exteriorOldVertices old s t c removed
  let W := appendixVertices old s t removed
  let ha := T.exterior_old_certificate p k b removed hb R.removed_cutedge hbr
  let A := Classical.choose ha
  have hA := (Classical.choose_spec ha).1
  have Afirst := (Classical.choose_spec ha).2.1
  have Alast := (Classical.choose_spec ha).2.2
  let hz := T.exterior_old_certificate p k c removed hc R.removed_cutedge hcr
  let Z := Classical.choose hz
  have hZ := (Classical.choose_spec hz).1
  have Zfirst := (Classical.choose_spec hz).2.1
  have Zlast := (Classical.choose_spec hz).2.2
  let hd := T.appendix removed R.removed_cutedge
  let D := Classical.choose hd
  have hD := (Classical.choose_spec hd).1
  have old_part : ∀ x ∈ P, x ∈ R.oldVertices → x ∈ W ∨ x ∈ B ∨ x ∈ C := by
    intro x hx hxo
    have hr := R.merged_bridge_old_vertex_touches_removed p z ((K_exact z).mpr hzK)
      b c hb hc hbr hcr hbc (part_region z hzP) x hxo (part_region x hx)
    rcases R.affected_two_old_region_support p b c hb hc hbr hcr hbc x hr (part_region x hx) with hw | hB | hC
    · exact Or.inl ((mem_appendixVertices old s t removed x).mpr hw)
    · exact Or.inr (Or.inl ((mem_exteriorOldVertices old s t b removed x).mpr
        (fun d hd => (hB d hd).trans or_comm)))
    · exact Or.inr (Or.inr ((mem_exteriorOldVertices old s t c removed x).mpr
        (fun d hd => (hC d hd).trans or_comm)))
  have disjointBW : ∀ x, x ∈ B → x ∈ W → False := by
    intro x hxB hxW
    have hB := (mem_exteriorOldVertices old s t b removed x).mp hxB
    have hW := (mem_appendixVertices old s t removed x).mp hxW
    exact hbr ((hW b hb).mp ((hB b hb).mpr (Or.inl rfl)))
  have disjointCW : ∀ x, x ∈ C → x ∈ W → False := by
    intro x hxC hxW
    have hC := (mem_exteriorOldVertices old s t c removed x).mp hxC
    have hW := (mem_appendixVertices old s t removed x).mp hxW
    exact hcr ((hW c hc).mp ((hC c hc).mpr (Or.inl rfl)))
  have disjointBC : ∀ x, x ∈ B → x ∈ C → False := by
    intro x hxB hxC
    have hB := (mem_exteriorOldVertices old s t b removed x).mp hxB
    have hC := (mem_exteriorOldVertices old s t c removed x).mp hxC
    exact ((hC b hb).mp ((hB b hb).mpr (Or.inl rfl))).elim hbc hbr
  have hK : ∀ x f, inserted x f → x ∈ K := fun x f h => (K_exact x).mp (R.new_support x f h)
  let L := A.restrict P
  let M := D.replacementInterior P K small
  let U := (Z.restrict P).reverse
  have split : ((B ∩ P) ∪ ((W ∩ P) ∪ (K ∩ P))) ∪ (C ∩ P) = P := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · exact (Finset.mem_inter.mp hx).2
        · rcases Finset.mem_union.mp hx with hx | hx
          · exact (Finset.mem_inter.mp hx).2
          · exact (Finset.mem_inter.mp hx).2
      · exact (Finset.mem_inter.mp hx).2
    · intro hx
      rcases part_support x hx with ho | hk
      · rcases old_part x hx ho with hw | hb' | hc'
        · simp only [Finset.mem_union,Finset.mem_inter]
          exact Or.inl (Or.inr (Or.inl ⟨hw,hx⟩))
        · simp only [Finset.mem_union,Finset.mem_inter]
          exact Or.inl (Or.inl ⟨hb',hx⟩)
        · simp only [Finset.mem_union,Finset.mem_inter]
          exact Or.inr ⟨hc',hx⟩
      · simp only [Finset.mem_union,Finset.mem_inter]
        exact Or.inl (Or.inr (Or.inr ⟨hk,hx⟩))
  have outer : ∀ x, x ∈ B ∩ P → x ∈ C ∩ P → False :=
    fun x hB hC => disjointBC x (Finset.mem_inter.mp hB).1 (Finset.mem_inter.mp hC).1
  have left_seam : ∀ x ∈ (B ∩ P) ∩ ((W ∩ P) ∪ (K ∩ P)),
      x ∈ L.bag L.last ∧ x ∈ M.bag 0 := by
    intro x hx
    obtain ⟨hB,hM⟩ := Finset.mem_inter.mp hx
    obtain ⟨hB,hP⟩ := Finset.mem_inter.mp hB
    have hk : x ∈ K ∩ P := (Finset.mem_union.mp hM).elim
      (fun hw => (disjointBW x hB (Finset.mem_inter.mp hw).1).elim) id
    have hr := R.overlap x (R.exteriorOld_supported b x hB) ((K_exact x).mpr (Finset.mem_inter.mp hk).1)
    exact ⟨Finset.mem_inter.mpr ⟨Alast x hB hr,hP⟩,D.replacementInterior_boundary P K small 0 hk⟩
  have right_seam : ∀ x ∈ ((W ∩ P) ∪ (K ∩ P)) ∩ (C ∩ P),
      x ∈ M.bag M.last ∧ x ∈ U.bag 0 := by
    intro x hx
    obtain ⟨hM,hC⟩ := Finset.mem_inter.mp hx
    obtain ⟨hC,hP⟩ := Finset.mem_inter.mp hC
    have hk : x ∈ K ∩ P := (Finset.mem_union.mp hM).elim
      (fun hw => (disjointCW x hC (Finset.mem_inter.mp hw).1).elim) id
    have hr := R.overlap x (R.exteriorOld_supported c x hC) ((K_exact x).mpr (Finset.mem_inter.mp hk).1)
    refine ⟨D.replacementInterior_boundary P K small M.last hk,?_⟩
    change x ∈ (Z.restrict P).reverse.bag 0
    rw [BagPath.reverse_first]
    exact Finset.mem_inter.mpr ⟨Zlast x hC hr,hP⟩
  have hL : L.Covers (ReplacementIncidence old inserted removed) := by
    intro e
    cases e with
    | inl e => exact A.restrict_covers P hA e.val
    | inr f =>
      refine ⟨L.last,le_rfl,?_⟩
      intro x hx hxf
      obtain ⟨hxB,hxP⟩ := Finset.mem_inter.mp hx
      have hr := R.overlap x (R.exteriorOld_supported b x hxB) (R.new_support x f hxf)
      exact Finset.mem_inter.mpr ⟨Alast x hxB hr,hxP⟩
  have hU : U.Covers (ReplacementIncidence old inserted removed) := by
    apply BagPath.reverse_covers
    intro e
    cases e with
    | inl e => exact Z.restrict_covers P hZ e.val
    | inr f =>
      refine ⟨(Z.restrict P).last,le_rfl,?_⟩
      intro x hx hxf
      obtain ⟨hxC,hxP⟩ := Finset.mem_inter.mp hx
      have hr := R.overlap x (R.exteriorOld_supported c x hxC) (R.new_support x f hxf)
      exact Finset.mem_inter.mpr ⟨Zlast x hxC hr,hxP⟩
  have hM : M.Covers (ReplacementIncidence old inserted removed) :=
    D.replacementInterior_covers P K small removed hD hK
  have localized : ∀ e,
      (∀ x ∈ ((B ∩ P) ∪ ((W ∩ P) ∪ (K ∩ P))) ∪ (C ∩ P),
        ReplacementIncidence old inserted removed x e → x ∈ B ∩ P) ∨
      (∀ x ∈ ((B ∩ P) ∪ ((W ∩ P) ∪ (K ∩ P))) ∪ (C ∩ P),
        ReplacementIncidence old inserted removed x e → x ∈ (W ∩ P) ∪ (K ∩ P)) ∨
      (∀ x ∈ ((B ∩ P) ∪ ((W ∩ P) ∪ (K ∩ P))) ∪ (C ∩ P),
        ReplacementIncidence old inserted removed x e → x ∈ C ∩ P) := by
    intro e
    cases e with
    | inr f =>
      refine Or.inr (Or.inl ?_)
      intro x hx hxf
      rw [split] at hx
      exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hK x f hxf,hx⟩)
    | inl e =>
      have hne : (CutBoundary.cut e.val : CutBoundary E) ≠ .cut removed :=
        fun h => e.property (CutBoundary.cut.inj h)
      by_cases he : Cutedge old s t e.val
      · by_cases heb : (CutBoundary.cut e.val : CutBoundary E) = b
        · apply Or.inl
          intro x hx hxe
          rw [split] at hx
          rcases old_part x hx (R.old_support x e.val hxe) with hw | hB | hC
          · exact (e.property (appendix_incident_cutedge_eq
              ((mem_appendixVertices old s t removed x).mp hw) he hxe)).elim
          · exact Finset.mem_inter.mpr ⟨hB,hx⟩
          · have endpt := bridge_incident_cutedge_endpoint
              ((mem_exteriorOldVertices old s t c removed x).mp hC) he hxe
            exact (endpt.elim (fun h => hbc (heb.symm.trans h)) hne).elim
        · refine Or.inr (Or.inr ?_)
          intro x hx hxe
          rw [split] at hx
          rcases old_part x hx (R.old_support x e.val hxe) with hw | hB | hC
          · exact (e.property (appendix_incident_cutedge_eq
              ((mem_appendixVertices old s t removed x).mp hw) he hxe)).elim
          · have endpt := bridge_incident_cutedge_endpoint
              ((mem_exteriorOldVertices old s t b removed x).mp hB) he hxe
            exact (endpt.elim heb hne).elim
          · exact Finset.mem_inter.mpr ⟨hC,hx⟩
      · by_cases hex : ∃ x ∈ P, old x e.val
        · obtain ⟨x,hx,hxe⟩ := hex
          rcases old_part x hx (R.old_support x e.val hxe) with hw | hB | hC
          · refine Or.inr (Or.inl ?_)
            intro y hy hye
            rw [split] at hy
            have hyW := noncut_edge_appendix_localized he hxe
              ((mem_appendixVertices old s t removed x).mp hw) y hye
            exact Finset.mem_union_left _ (Finset.mem_inter.mpr
              ⟨(mem_appendixVertices old s t removed y).mpr hyW,hy⟩)
          · apply Or.inl
            intro y hy hye
            rw [split] at hy
            have hyB := noncut_edge_bridge_localized he hxe
              ((mem_exteriorOldVertices old s t b removed x).mp hB) y hye
            exact Finset.mem_inter.mpr ⟨(mem_exteriorOldVertices old s t b removed y).mpr hyB,hy⟩
          · refine Or.inr (Or.inr ?_)
            intro y hy hye
            rw [split] at hy
            have hyC := noncut_edge_bridge_localized he hxe
              ((mem_exteriorOldVertices old s t c removed x).mp hC) y hye
            exact Finset.mem_inter.mpr ⟨(mem_exteriorOldVertices old s t c removed y).mpr hyC,hy⟩
        · apply Or.inl
          intro x hx hxe
          rw [split] at hx
          exact (hex ⟨x,hx,hxe⟩).elim
  let Q := L.triple M U outer left_seam right_seam
  have hQ := L.triple_covers M U outer left_seam right_seam hL hM hU localized
  refine ⟨Q.recast split,Q.recast_covers split hQ,?_,?_⟩
  · intro x hx hxb
    have hbold := (boundaryIncidence_surviving b hbr x).mp hxb
    have hxo := R.boundaryIncidence_supported x b hbold
    have hxB : x ∈ B := by
      rcases old_part x hx hxo with hw | hB | hC
      · exact (hbr (((mem_appendixVertices old s t removed x).mp hw b hb).mp
          (boundary_incidence_touches x b hbold))).elim
      · exact hB
      · have htouch := ((mem_exteriorOldVertices old s t c removed x).mp hC b hb).mp
          (boundary_incidence_touches x b hbold)
        exact (htouch.elim hbc hbr).elim
    change x ∈ Q.bag 0
    rw [BagPath.triple_first]
    exact Finset.mem_inter.mpr ⟨Afirst x hxB hbold,hx⟩
  · intro x hx hxc
    have hcold := (boundaryIncidence_surviving c hcr x).mp hxc
    have hxo := R.boundaryIncidence_supported x c hcold
    have hxC : x ∈ C := by
      rcases old_part x hx hxo with hw | hB | hC
      · exact (hcr (((mem_appendixVertices old s t removed x).mp hw c hc).mp
          (boundary_incidence_touches x c hcold))).elim
      · have htouch := ((mem_exteriorOldVertices old s t b removed x).mp hB c hc).mp
          (boundary_incidence_touches x c hcold)
        exact (htouch.elim (fun h => hbc h.symm) hcr).elim
      · exact hC
    change x ∈ Q.bag Q.last
    rw [BagPath.triple_last]
    change x ∈ (Z.restrict P).reverse.bag (Z.restrict P).reverse.last
    rw [BagPath.reverse_last]
    exact Finset.mem_inter.mpr ⟨Zfirst x hxC hcold,hx⟩

end ReplacementFrame
end FiniteFlow.Hypergraph
