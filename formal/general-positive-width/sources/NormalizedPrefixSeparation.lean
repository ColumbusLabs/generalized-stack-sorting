import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import NormalizedPrefixSaturation
import NormalizedPrefixRank
import SupportedGlobalPathwidth

namespace StackSorting.PrefixGrowth
open GraphWidth SameVertexForest ConnectedConeNormalization FiniteFlow.Hypergraph
variable {n : Nat}
noncomputable section

/-- Concrete Lemma 5.2 output for normalized singleton-margin decompositions.
The edge carrier still keeps opposite original orientations as separate copies;
only original copies may occur in both paths. Boundary adhesion IDs are exact.
The bag path covers precisely the actually exposed vertices, with bound 2k+2. -/
theorem exists_prefix_separation (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1)
    (r s t : Fin n) (hs : s ∈ regionBagSet G O r) (ht : t ∈ regionBagSet G O r) :
    ∃ Z : Finset (Fin n), RelativePrefix O r Z ∧
      (∃ p q : Path (ActiveIncidence (PrefixHypertorsoInc G O r Z)) s t,
        ∀ e, e ∈ p.walk.edges → e ∈ q.walk.edges → ∃ a b, e.val = .inl (a,b)) ∧
      ∃ D : BagPath (Finset.univ : Finset {x : Fin n // x ∈ prefixVertices G O r Z}) (2*k+2),
        D.Covers (SupportedIncidence (inc := ActiveIncidence (PrefixHypertorsoInc G O r Z))
          (↑(prefixVertices G O r Z))) := by
  classical
  obtain ⟨Z,hZ,hd⟩ := exists_original_cutedge_prefix G O helim cones k width r s t hs ht
  obtain ⟨hp,hs',ht',connected,p,T⟩ := hZ
  let : Fintype (ActiveEdge (PrefixHypertorsoInc G O r Z)) :=
    inferInstanceAs (Fintype {e : (Fin n × Fin n) ⊕ Fin n // ∃ x, PrefixHypertorsoInc G O r Z x e})
  obtain ⟨a,b,hab⟩ := exists_two_paths (ActiveIncidence (PrefixHypertorsoInc G O r Z)) s t ⟨p.walk⟩
  have rank : ∀ e : ActiveEdge (PrefixHypertorsoInc G O r Z),
      Cutedge (ActiveIncidence (PrefixHypertorsoInc G O r Z)) s t e →
      (hyperedgeVertices (ActiveIncidence (PrefixHypertorsoInc G O r Z)) e).card ≤ k+1 := by
    intro e _
    exact prefix_hyperedge_rank G O helim k width r Z e.val
  obtain ⟨D,hD⟩ := supported_thin_network_has_bag_path (↑(prefixVertices G O r Z))
    (fun x e hx => prefixHypertorso_support G O r Z hp x e.val hx)
    ⟨s,hs'⟩ ⟨t,ht'⟩ connected p k T rank
  exact ⟨Z,hp,⟨a,b,fun e ha hb => hd e ((hab e).mp ⟨ha,hb⟩)⟩,D,hD⟩

end
end StackSorting.PrefixGrowth
