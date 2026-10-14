import PrefixMarginalCoverage
import PrunedPrefixSeparation
import SelectionPathwidthParts
import BagPathImage

namespace FiniteFlow.Hypergraph.BagPath
variable {V : Type} [DecidableEq V] {region : Finset V} {b : Nat}

/-- Restrict actual bags to a specified subregion without changing its names. -/
def restrictTo (D : BagPath region b) (part : Finset V) (h : part ⊆ region) :
    BagPath part b where
  last := D.last
  bag i := D.bag i ∩ part
  inside _ _ := Finset.inter_subset_right
  bounded i hi := (Finset.card_le_card Finset.inter_subset_left).trans (D.bounded i hi)
  vertex := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := D.vertex x (h hx)
    exact ⟨i,hi,Finset.mem_inter.mpr ⟨hxi,hx⟩⟩
  interval := by
    intro i j k hij hjk hk x hxi hxk
    exact Finset.mem_inter.mpr ⟨D.interval i j k hij hjk hk x
      (Finset.mem_inter.mp hxi).1 (Finset.mem_inter.mp hxk).1,(Finset.mem_inter.mp hxi).2⟩
end FiniteFlow.Hypergraph.BagPath

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}

/-- The full indexed pruned hypertorso certificate restricts to precisely the
original prefix vertices. Both original and child-completion pairs are retained. -/
theorem prefix_marginal_path (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r : Fin n) (k : Nat) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (small : Z = {r} ∨ ∃ s t, Nonempty (PrunedPrefixWitness G O r s t k Z))
    (A : RootedSelection O r)
    (honly : ∀ a ∈ A.nodes, a ∈ Z → a = r)
    (hfront : ∀ z, Frontier (clippedParent O r) Z z → z ∈ A.nodes) :
    ∃ D : BagPath Z (2*k+2), ∀ u v, u ∈ Z → v ∈ Z →
      A.MarginalEdge G ⟨r,A.root_mem⟩ u v →
      ∃ i, i ≤ D.last ∧ u ∈ D.bag i ∧ v ∈ D.bag i := by
  classical
  rcases small with hs | ⟨s,t,⟨W⟩⟩
  · have hb : Z.card ≤ 2*k+2 := by simp [hs]
    exact ⟨(BagPath.single Z).weaken hb,fun u v hu hv _ => ⟨0,le_rfl,hu,hv⟩⟩
  · let P := prefixVertices (inducedGraph G (rootAllowed G O r s t))
      (prunedOrder G O r s t) r Z
    let M := W.bags.map (fun x => x.val) Subtype.val_injective
    have hZM : Z ⊆ (Finset.univ : Finset {x : Fin n // x ∈ P}).image Subtype.val := by
      intro x hx
      exact Finset.mem_image.mpr ⟨⟨x,Finset.mem_union_left _ hx⟩,Finset.mem_univ _,rfl⟩
    let D := M.restrictTo Z hZM
    refine ⟨D,?_⟩
    intro u v hu hv huv
    have he : ∃ e : ActiveEdge (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
        (prunedOrder G O r s t) r Z),
        ActiveIncidence (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
          (prunedOrder G O r s t) r Z) u e ∧
        ActiveIncidence (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
          (prunedOrder G O r s t) r Z) v e := by
      rcases huv with h | ⟨a,har,hparent,ha,hb⟩
      · exact pruned_prefix_original_pair G O r s t Z hp hu hv h
      · exact pruned_prefix_child_pair G O cones r s t Z hp A honly hfront a har
          (congrArg Subtype.val hparent) hu hv ha hb
    obtain ⟨e,heU,heV⟩ := he
    obtain ⟨i,hi,hcover⟩ := W.covers e
    have up : u ∈ P := Finset.mem_union_left _ hu
    have vp : v ∈ P := Finset.mem_union_left _ hv
    have hU := hcover ⟨u,up⟩ (Finset.mem_univ _) heU
    have hV := hcover ⟨v,vp⟩ (Finset.mem_univ _) heV
    exact ⟨i,hi,Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨⟨u,up⟩,hU,rfl⟩,hu⟩,
      Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨⟨v,vp⟩,hV,rfl⟩,hv⟩⟩

end StackSorting.LowPathwidthParts
