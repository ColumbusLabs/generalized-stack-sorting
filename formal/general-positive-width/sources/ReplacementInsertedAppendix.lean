import ReplacementAffectedRegions
import ThinNetworkDefinitionBridge
import ReplacementCoverage

namespace FiniteFlow.Hypergraph.ReplacementFrame
variable {V E F : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {old : V → E → Prop} {inserted : V → F → Prop} {s t : V} {removed : E}

/- Every vertex of the old removed-edge appendix union is an old supported
vertex. This is proved from its actual component walk to the removed edge. -/
omit [DecidableEq V] [DecidableEq E] in
theorem appendix_supported (R : ReplacementFrame old inserted s t removed)
    (x : V) (hx : x ∈ appendixVertices old s t removed) : x ∈ R.oldVertices := by
  have hr := (mem_appendixVertices old s t removed x).mp hx
  obtain ⟨y,hy,hxy⟩ := (hr (.cut removed) R.removed_cutedge).mpr rfl
  exact old_component_supported R.oldVertices R.old_support
    (R.old_support y removed hy) (sameCutedgeComponent_symm old s t hxy)

/-- Construct the actual width-k decomposition of any new inserted appendix
part. The old-origin condition and prepend seam are derived from component
transport and the replacement overlap, not supplied as decomposition premises. -/
noncomputable def insertedAppendixBagPath
    (R : ReplacementFrame old inserted s t removed) (k : Nat)
    (K P : Finset V) (small : K.card ≤ k+1)
    (K_exact : ∀ x, x ∈ R.newVertices ↔ x ∈ K)
    (old_to_source : ∀ x ∈ R.oldVertices, Nonempty (HWalk old x s))
    (part_support : ∀ x ∈ P, x ∈ R.oldVertices ∨ x ∈ K)
    (f : F)
    (part_region : ∀ x ∈ P, AppendixRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (.inr f) x)
    (D : BagPath (appendixVertices old s t removed) (k+1)) (hD : D.Covers old)
    (Dfirst : ∀ x ∈ appendixVertices old s t removed, old x removed → x ∈ D.bag 0) :
    {Q : BagPath P (k+1) // Q.Covers (ReplacementIncidence old inserted removed) ∧
      ∀ x ∈ P, ∀ g, inserted x g → x ∈ Q.bag 0} := by
  classical
  let W := appendixVertices old s t removed
  have old_part : ∀ x ∈ P, x ∈ R.oldVertices → x ∈ W := by
    intro x hx hxo
    exact (mem_appendixVertices old s t removed x).mpr
      (R.inserted_appendix_old_support x (old_to_source x hxo) f (part_region x hx))
  have split : (K ∩ P) ∪ (W ∩ P) = P := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).2
      · exact (Finset.mem_inter.mp hx).2
    · intro x hx
      rcases part_support x hx with hxo | hxk
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨old_part x hx hxo,hx⟩)
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxk,hx⟩)
  have seam : ∀ x ∈ (K ∩ P) ∩ (W ∩ P), x ∈ (D.restrict P).bag 0 := by
    intro x hx
    obtain ⟨hxk,hxw⟩ := Finset.mem_inter.mp hx
    obtain ⟨hxK,hxP⟩ := Finset.mem_inter.mp hxk
    have hxW := (Finset.mem_inter.mp hxw).1
    have hxo := R.appendix_supported x hxW
    have hr := R.overlap x hxo ((K_exact x).mpr hxK)
    exact Finset.mem_inter.mpr ⟨Dfirst x hxW hr,hxP⟩
  have small' : (K ∩ P).card ≤ k+1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans small
  let Q := (D.restrict P).replacementAppendix (K ∩ P) small' seam
  have hQ : Q.Covers (ReplacementIncidence old inserted removed) := by
    intro e
    cases e with
    | inl e =>
      obtain ⟨a,ha,hea⟩ := D.restrict_covers P hD e.val
      refine ⟨1+a,by change 1+a ≤ 0+1+(D.restrict P).last; omega,?_⟩
      intro x hx hxe
      have hxP : x ∈ P := by rw [split] at hx; exact hx
      have hxW := old_part x hxP (R.old_support x e.val hxe)
      change x ∈ if 1+a ≤ 0 then _ else (D.restrict P).bag (1+a-0-1)
      rw [ite_eq_right (by omega),show 1+a-0-1=a by omega]
      exact hea x (Finset.mem_inter.mpr ⟨hxW,hxP⟩) hxe
    | inr g =>
      refine ⟨0,Nat.zero_le _,?_⟩
      intro x hx hxg
      have hxP : x ∈ P := by rw [split] at hx; exact hx
      change x ∈ Q.bag 0
      rw [BagPath.replacementAppendix_first]
      exact Finset.mem_inter.mpr ⟨(K_exact x).mp (R.new_support x g hxg),hxP⟩
  refine ⟨Q.recast split, Q.recast_covers split hQ, ?_⟩
  intro x hx g hxg
  change x ∈ Q.bag 0
  rw [BagPath.replacementAppendix_first]
  exact Finset.mem_inter.mpr ⟨(K_exact x).mp (R.new_support x g hxg),hx⟩

end FiniteFlow.Hypergraph.ReplacementFrame
