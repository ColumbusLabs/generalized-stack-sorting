import SupportedNetworkThinness

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} [Fintype V] [DecidableEq V] [DecidableEq E] [DecidableEq F]
variable {old : V → E → Prop} {inserted : V → F → Prop} {s t : V} {removed : E}
namespace ReplacementFrame

omit [DecidableEq F] in
/-- The four boundary-origin cases produce an actual local bridge path in the
replacement. The two-old case also includes the merged, no-inserted-cutedge case. -/
theorem replacement_bridge_certificate_on_support
    (R : ReplacementFrame old inserted s t removed) (p : Path old s t) (k : Nat)
    (T : ThinNetworkLocalWitnesses p k) (K P : Finset V) (small : K.card ≤ k+1)
    (K_exact : ∀ x, x ∈ R.newVertices ↔ x ∈ K)
    (old_to_source : ∀ x ∈ R.oldVertices, Nonempty (HWalk old x s))
    (removed_in_new : ∀ x, old x removed → x ∈ R.newVertices)
    (support : ∀ x ∈ P, x ∈ R.oldVertices ∨ x ∈ R.newVertices)
    (a d : CutBoundary ({e : E // e ≠ removed} ⊕ F))
    (ha : BoundaryValid (inc := ReplacementIncidence old inserted removed) (s := s) (t := t) a)
    (hd : BoundaryValid (inc := ReplacementIncidence old inserted removed) (s := s) (t := t) d)
    (had : a ≠ d)
    (part_exact : ∀ x, x ∈ P ↔ BridgeRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) a d x) :
    ∃ Q : BagPath P (2*k+2), Q.Covers (ReplacementIncidence old inserted removed) ∧
      (∀ x ∈ P, BoundaryIncidence (inc := ReplacementIncidence old inserted removed)
        (s := s) (t := t) x a → x ∈ Q.bag 0) ∧
      (∀ x ∈ P, BoundaryIncidence (inc := ReplacementIncidence old inserted removed)
        (s := s) (t := t) x d → x ∈ Q.bag Q.last) := by
  classical
  have part_support : ∀ x ∈ P, x ∈ R.oldVertices ∨ x ∈ K :=
    fun x hx => (support x hx).imp_right ((K_exact x).mp)
  have part_region := fun x hx => (part_exact x).mp hx
  obtain ⟨D,hD,Dfirst⟩ := T.appendix removed R.removed_cutedge
  rcases R.newBoundary_cases a ha with ⟨b,hbr,hb,rfl⟩ | ⟨f,rfl,hf⟩
  · rcases R.newBoundary_cases d hd with ⟨c,hcr,hc,rfl⟩ | ⟨g,rfl,hg⟩
    · have hbc : b ≠ c := by
        intro heq
        subst c
        exact had rfl
      by_cases hex : ∃ z ∈ P, z ∈ K
      · obtain ⟨z,hzP,hzK⟩ := hex
        let Q := R.mergedBridgeBagPath p k T K P small K_exact part_support b c hb hc hbr hcr hbc
          part_region z hzK hzP
        exact ⟨Q.val,Q.property⟩
      · have avoids : ∀ x ∈ P, x ∉ R.newVertices :=
          fun x hx hxn => hex ⟨x,hx,(K_exact x).mp hxn⟩
        let Q := R.unchangedBridgeBagPath p k T P removed_in_new support avoids
          b c hb hc hbr hcr hbc part_exact
        exact ⟨Q.val,Q.property⟩
    · obtain ⟨A,hA,Afirst,Alast⟩ := T.exterior_old_certificate p k b removed hb R.removed_cutedge hbr
      let Q := R.exteriorBridgeBagPath k K P small K_exact part_support b hb hbr g hg
        part_region A hA Afirst Alast D hD
      exact ⟨Q.val,Q.property⟩
  · rcases R.newBoundary_cases d hd with ⟨c,hcr,hc,rfl⟩ | ⟨g,rfl,hg⟩
    · obtain ⟨A,hA,Afirst,Alast⟩ := T.exterior_old_certificate p k c removed hc R.removed_cutedge hcr
      have swapped : ∀ x ∈ P, BridgeRegion (inc := ReplacementIncidence old inserted removed)
          (s := s) (t := t) (survivingBoundary (F := F) c hcr) (.cut (.inr f)) x := by
        intro x hx b hb
        exact (part_region x hx b hb).trans or_comm
      let Q := R.exteriorBridgeBagPath k K P small K_exact part_support c hc hcr f hf
        swapped A hA Afirst Alast D hD
      refine ⟨Q.val.reverse,Q.val.reverse_covers Q.property.1,?_,?_⟩
      · intro x hx hxf
        rw [BagPath.reverse_first]
        exact Q.property.2.2 x hx hxf
      · intro x hx hxc
        rw [BagPath.reverse_last]
        exact Q.property.2.1 x hx hxc
    · let Q := R.insertedInteriorBagPath k K P small K_exact old_to_source part_support f g part_region D hD
      exact ⟨Q.val,Q.property.1,
        fun x hx hxf => Q.property.2 0 (Nat.zero_le _) x hx f hxf,
        fun x hx hxg => Q.property.2 Q.val.last le_rfl x hx g hxg⟩

/-- Replacement preserves local thinness inside actual supported component
unions, without requiring future isolated ambient vertices to be present yet. -/
theorem replacement_preserves_supported_local_thinness
    (R : ReplacementFrame old inserted s t removed) (p : Path old s t) (k : Nat)
    (T : ThinNetworkLocalWitnesses p k) (K : Finset V) (small : K.card ≤ k+1)
    (K_exact : ∀ x, x ∈ R.newVertices ↔ x ∈ K)
    (old_to_source : ∀ x ∈ R.oldVertices, Nonempty (HWalk old x s))
    (new_to_anchor : ∀ x ∈ R.newVertices, Nonempty (HWalk inserted x R.anchor))
    (removed_in_new : ∀ x, old x removed → x ∈ R.newVertices)
    (q : Path (ReplacementIncidence old inserted removed) s t) : ThinNetworkLocalWitnesses q k := by
  classical
  have appendix_support : ∀ e, Cutedge (ReplacementIncidence old inserted removed) s t e →
      ∀ x ∈ appendixVertices (ReplacementIncidence old inserted removed) s t e,
        x ∈ R.oldVertices ∨ x ∈ R.newVertices := by
    intro e he x hx
    exact R.touched_replacement_supported x (.cut e)
      (((mem_appendixVertices _ _ _ e x).mp hx) (.cut e) he |>.mpr rfl)
  constructor
  · intro e he
    cases e with
    | inl e =>
      have heold := replacement_cutedge_old_implies removed R.inserted_connects e he
      obtain ⟨D,hD,hfirst⟩ := T.appendix e.val heold
      let P := appendixVertices (ReplacementIncidence old inserted removed) s t (.inl e)
      let Q := R.survivingAppendixBagPath p new_to_anchor removed_in_new e.val heold e.property k P
        (appendix_support (.inl e) he) (fun x hx => (mem_appendixVertices _ _ _ _ x).mp hx) D hD hfirst
      exact ⟨Q.val,Q.property⟩
    | inr f =>
      obtain ⟨D,hD,hfirst⟩ := T.appendix removed R.removed_cutedge
      let P := appendixVertices (ReplacementIncidence old inserted removed) s t (.inr f)
      let Q := R.insertedAppendixBagPath k K P small K_exact old_to_source
        (fun x hx => (appendix_support (.inr f) he x hx).imp_right ((K_exact x).mp)) f
        (fun x hx => (mem_appendixVertices _ _ _ _ x).mp hx) D hD hfirst
      exact ⟨Q.val,Q.property.1,fun x hx hxf => Q.property.2 x hx f hxf⟩
  · intro i j hij
    have valid : ∀ a : Fin (boundaryTrace q).length,
        BoundaryValid (inc := ReplacementIncidence old inserted removed) (s := s) (t := t)
          ((boundaryTrace q).get a) := fun a => (mem_boundaryTrace q _).mp (List.get_mem _ a)
    have hne : (boundaryTrace q).get i ≠ (boundaryTrace q).get j := by
      intro h
      have before := (boundaryTrace_get_before q i j).mpr (by change i.val < j.val; omega)
      rw [h] at before
      exact boundaryBefore_irrefl q _ before
    have support : ∀ x ∈ bridgeVertices q i j, x ∈ R.oldVertices ∨ x ∈ R.newVertices := by
      intro x hx
      exact R.touched_replacement_supported x _
        (((mem_bridgeVertices q i j x).mp hx) _ (valid i) |>.mpr (Or.inl rfl))
    obtain ⟨Q,hQ,hfirst,hlast⟩ := R.replacement_bridge_certificate_on_support p k T K (bridgeVertices q i j)
      small K_exact old_to_source removed_in_new support _ _ (valid i) (valid j) hne
      (fun x => mem_bridgeVertices q i j x)
    exact ⟨Q,hQ,fun x hx hxi => hfirst x hx ((mem_boundaryVertices q i x).mp hxi),
      fun x hx hxj => hlast x hx ((mem_boundaryVertices q j x).mp hxj)⟩

end ReplacementFrame
end FiniteFlow.Hypergraph
