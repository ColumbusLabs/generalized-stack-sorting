import RankedForestNumbering
import EliminationForestFromDecomposition
import Mathlib.Data.Finset.Card

namespace StackSorting.SameVertexForest.RankedOrder.Numbered
open GraphWidth FinitePort

variable {n colors relations : Nat} (O : RankedOrder n) (r : Fin n)
  (hr : O.parent r = r) (ha : ∀ v, SameVertexForest.Ancestor O.forest r v)
  (N : (O.rootedParent r hr ha).Numbered)

/-- The two-sided numbering changes names only, retaining every color and
every direction of every relation. -/
def relabelDiagram (G : Diagram n colors relations) : Diagram n colors relations where
  color v := G.color (N.label v)
  rel q u v := G.rel q (N.label u) (N.label v)

theorem relabel_adjacent (G : Diagram n colors relations) (u v : Fin n) :
    Adjacent (relabelDiagram O r hr ha N G) u v ↔ Adjacent G (N.label u) (N.label v) :=
  Iff.rfl

theorem relabel_loopless (G : Diagram n colors relations) (h : Loopless G) :
    Loopless (relabelDiagram O r hr ha N G) := fun q v => h q (N.label v)

theorem relabel_eliminates (G : Diagram n colors relations)
    (he : ∀ u v, Adjacent G u v →
      SameVertexForest.Ancestor O.forest u v ∨ SameVertexForest.Ancestor O.forest v u) :
    Eliminates N.tree (relabelDiagram O r hr ha N G) := by
  intro u v huv
  rcases he _ _ huv with h | h
  · exact Or.inl ((ancestor_iff O r hr ha N).mpr h)
  · exact Or.inr ((ancestor_iff O r hr ha N).mpr h)

theorem bag_mem_frontier (G : Diagram n colors relations) (H : Graph n)
    (hH : ∀ u v, H.Adj u v ↔ Adjacent G u v) (ord : FixedOrder n) (v u : Fin n) :
    u ∈ bag N.tree ord (relabelDiagram O r hr ha N G) v ↔
      EliminationFrontier O.forest H (N.label v) (N.label u) := by
  rw [mem_bag]
  simp only [Inherited, EliminationFrontier, ancestor_iff O r hr ha N]
  constructor
  · rintro (h | ⟨huv,hne,w,hw,he⟩)
    · exact Or.inl (congrArg N.label h)
    · exact Or.inr ⟨huv, fun e => hne (N.label_injective e), N.label w, hw, (hH _ _).mpr he⟩
  · rintro (h | ⟨huv,hne,w,hw,he⟩)
    · exact Or.inl (N.label_injective h)
    · refine Or.inr ⟨huv, fun e => hne (congrArg N.label e), N.index w, ?_, ?_⟩
      · simpa only [N.label_index] using hw
      · change Adjacent G (N.label u) (N.label (N.index w))
        rw [N.label_index]
        exact (hH _ _).mp he

theorem bag_length_eq_frontier_card (G : Diagram n colors relations) (H : Graph n)
    (hH : ∀ u v, H.Adj u v ↔ Adjacent G u v) (ord : FixedOrder n) (v : Fin n) :
    (bag N.tree ord (relabelDiagram O r hr ha N G) v).length =
      (eliminationFrontierSet O.forest H (N.label v)).card := by
  classical
  let b := bag N.tree ord (relabelDiagram O r hr ha N G) v
  let e : Fin n ↪ Fin n := ⟨N.label, fun _ _ h => N.label_injective h⟩
  have hset : b.toFinset.map e = eliminationFrontierSet O.forest H (N.label v) := by
    ext u
    simp only [Finset.mem_map, List.mem_toFinset, eliminationFrontierSet,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (bag_mem_frontier O r hr ha N G H hH ord v i).mp hi
    · intro hu
      refine ⟨N.index u, ?_, N.label_index u⟩
      apply (bag_mem_frontier O r hr ha N G H hH ord v (N.index u)).mpr
      simpa only [N.label_index] using hu
  rw [← hset, Finset.card_map]
  exact (List.toFinset_card_of_nodup (bag_nodup N.tree ord _ v)).symm

theorem bounded_codec (G : Diagram n colors relations) (H : Graph n)
    (hH : ∀ u v, H.Adj u v ↔ Adjacent G u v) (ord : FixedOrder n) {b : Nat}
    (hb : ∀ v, (eliminationFrontierSet O.forest H v).card ≤ b) :
    BoundedCode (encode N.tree ord (relabelDiagram O r hr ha N G)) (b-1) := by
  apply encode_bounded
  intro v
  have hc := bag_length_eq_frontier_card O r hr ha N G H hH ord v
  have hh := hb (N.label v)
  have hl : (bag N.tree ord (relabelDiagram O r hr ha N G) v).length =
      (inherited N.tree ord (relabelDiagram O r hr ha N G) v).length + 1 := rfl
  omega

/-- Exact decoding is retained under the constructed bijective renumbering. -/
theorem decoded_original_relation (G : Diagram n colors relations) (ord : FixedOrder n)
    (hl : Loopless G)
    (he : ∀ u v, Adjacent G u v →
      SameVertexForest.Ancestor O.forest u v ∨ SameVertexForest.Ancestor O.forest v u)
    (q : Fin relations) (u v : Fin n) :
    DecodedRel N.tree (encode N.tree ord (relabelDiagram O r hr ha N G)) q
      (N.index u) (N.index v) ↔ G.rel q u v = true := by
  rw [decode_encode_relation N.tree ord _ (relabel_loopless O r hr ha N G hl)
    (relabel_eliminates O r hr ha N G he)]
  simp only [relabelDiagram, N.label_index]

theorem decoded_original_color (G : Diagram n colors relations) (ord : FixedOrder n)
    (u : Fin n) (c : Fin colors) :
    (decode N.tree (encode N.tree ord (relabelDiagram O r hr ha N G))).color
      (N.index u) c = G.color u c := by
  simp only [decode, encode, relabelDiagram, N.label_index]

#print axioms bag_length_eq_frontier_card
#print axioms bounded_codec
#print axioms decoded_original_relation
end StackSorting.SameVertexForest.RankedOrder.Numbered
