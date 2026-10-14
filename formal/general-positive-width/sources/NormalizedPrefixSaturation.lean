import NormalizedPrefixBase

namespace StackSorting.PrefixGrowth
open GraphWidth SameVertexForest ConnectedConeNormalization FiniteFlow.Hypergraph
variable {n : Nat}

/-- The fully instantiated finite growth invariant. All paths are actual walks
in the current prefix incidence structure, and thinness has concrete bag witnesses. -/
def PrefixInvariant (G : Graph n) (O : RankedOrder n) (r s t : Fin n) (k : Nat)
    (Z : Finset (Fin n)) : Prop :=
  RelativePrefix O r Z ∧ s ∈ prefixVertices G O r Z ∧ t ∈ prefixVertices G O r Z ∧
  (∀ x ∈ prefixVertices G O r Z,
    Nonempty (HWalk (ActiveIncidence (PrefixHypertorsoInc G O r Z)) x s)) ∧
  ∃ p : Path (ActiveIncidence (PrefixHypertorsoInc G O r Z)) s t, ThinNetworkLocalWitnesses p k

def OriginalCutedges (G : Graph n) (O : RankedOrder n) (r s t : Fin n)
    (Z : Finset (Fin n)) : Prop :=
  ∀ e : ActiveEdge (PrefixHypertorsoInc G O r Z),
    Cutedge (ActiveIncidence (PrefixHypertorsoInc G O r Z)) s t e →
      ∃ a b, e.val = .inl (a,b)

/-- Actual network replacement supplies the finite induction step; the step is
proved rather than supplied as a global prefix-growth oracle. -/
theorem prefixInvariant_step (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1)
    (r s t : Fin n) (Z : Finset (Fin n)) (hZ : PrefixInvariant G O r s t k Z)
    (hd : ¬ OriginalCutedges G O r s t Z) :
    ∃ z, z ∉ Z ∧ PrefixInvariant G O r s t k (insert z Z) := by
  classical
  obtain ⟨hp,hs,ht,connected,p,T⟩ := hZ
  obtain ⟨e,hcut,hnot⟩ : ∃ e : ActiveEdge (PrefixHypertorsoInc G O r Z),
      Cutedge (ActiveIncidence (PrefixHypertorsoInc G O r Z)) s t e ∧
      ¬ ∃ a b, e.val = .inl (a,b) := by
    simpa only [OriginalCutedges,not_forall,not_imp,exists_prop] using hd
  cases he : e.val with
  | inl ab => exact (hnot ⟨ab.1,ab.2,he⟩).elim
  | inr z =>
    obtain ⟨x,hx⟩ := e.property
    rw [he] at hx
    have hz : Frontier (clippedParent O r) Z z := hx.1
    have hvis : prefixVertices G O r Z ⊆ prefixVertices G O r (insert z Z) := by
      rw [prefixVertices_insert]
      exact Finset.subset_insert _ _
    obtain ⟨q,hq⟩ := prefix_expansion_preserves_thinness G O helim cones k width
      r Z hp z hz s t hs ht connected e he hcut p T
    exact ⟨z,hz.1,relativePrefix_insert O r Z hp z hz,hvis hs,hvis ht,
      prefix_expansion_connected G O helim cones r Z hp z hz s t hs ht connected e he hcut,q,hq⟩

/-- An actual root-containing prefix with only original cutedges exists. This
is the constructive saturation stage of Lemma 5.2; the final pathwidth and
undirected original-edge comparison are separate obligations. -/
theorem exists_original_cutedge_prefix (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1)
    (r s t : Fin n) (hs : s ∈ regionBagSet G O r) (ht : t ∈ regionBagSet G O r) :
    ∃ Z, PrefixInvariant G O r s t k Z ∧ OriginalCutedges G O r s t Z := by
  classical
  have hs' : s ∈ prefixVertices G O r {r} := by simpa only [singleton_prefix_vertices] using hs
  have ht' : t ∈ prefixVertices G O r {r} := by simpa only [singleton_prefix_vertices] using ht
  obtain ⟨p,T⟩ := singleton_prefix_thin G O helim cones r k (width r) s t hs' ht'
  have hbase : PrefixInvariant G O r s t k {r} :=
    ⟨relativePrefix_singleton O r,hs',ht',
      fun x hx => singleton_prefix_connected G O helim cones r x s hx hs',p,T⟩
  obtain ⟨Z,_,hZ,hd⟩ := finite_invariant_saturation
    (PrefixInvariant G O r s t k) (OriginalCutedges G O r s t)
    (prefixInvariant_step G O helim cones k width r s t) {r} hbase
  exact ⟨Z,hZ,hd⟩

end StackSorting.PrefixGrowth
