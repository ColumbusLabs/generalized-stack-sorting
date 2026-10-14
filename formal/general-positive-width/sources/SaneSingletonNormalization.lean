import NormalizedDecompositionRegions

namespace StackSorting.ConnectedConeNormalization
open GraphWidth SameVertexForest
variable {n : Nat}

@[simp] theorem normalized_cone (G : Graph n) (O : RankedOrder n) (v u) :
    Cone (normalizedOrder G O) v u ↔ ReachCone G O v u := by
  exact ((normalizedOrder G O).ancestor_iff).symm.trans (normalized_ancestor G O v u)

theorem normalized_eliminates (G : Graph n) (O : RankedOrder n)
    (he : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u) {u v}
    (h : G.Adj u v) : (normalizedOrder G O).rel u v ∨ (normalizedOrder G O).rel v u := by
  have hne : u ≠ v := by intro eq; subst v; exact G.loopless _ h
  rcases reachCone_eliminates G O he h with h | h
  · exact Or.inl ⟨h,hne⟩
  · exact Or.inr ⟨h,Ne.symm hne⟩

theorem normalized_component_connected (G : Graph n) (O : RankedOrder n) {v x y}
    (hx : BagComponent G (normalizedOrder G O) v x)
    (hy : BagComponent G (normalizedOrder G O) v y) :
    Walk G.Adj (BagComponent G (normalizedOrder G O) v) x y := by
  have hx' := (normalized_cone G O v x).mp ((bagComponent_iff G _ v x).mp hx)
  have hy' := (normalized_cone G O v y).mp ((bagComponent_iff G _ v y).mp hy)
  exact (reachCone_connected G O hx' hy').mono (fun z hz =>
    (bagComponent_iff G _ v z).mpr ((normalized_cone G O v z).mpr hz))

/-- Saneness's adhesion-neighbor condition holds by the actual frontier
construction, using the proven union-of-bags component equality. -/
theorem adhesion_component_neighbor (G : Graph n) (O : RankedOrder n) {v u}
    (h : RegionAdhesion G O v u) : ∃ w, BagComponent G O v w ∧ G.Adj u w := by
  obtain ⟨hb,hne⟩ := (regionAdhesion_iff G O v u).mp h
  obtain ⟨_,w,hw,he⟩ := hb.resolve_left hne
  exact ⟨w,(bagComponent_iff G O v w).mpr hw,he⟩

/-- A real path crossing a vertex set contains a real boundary edge. -/
theorem walk_crosses {G : Graph n} {P S : Fin n → Prop} {u v}
    (h : Walk G.Adj P u v) (hu : ¬ S u) (hv : S v) :
    ∃ x y, P x ∧ ¬ S x ∧ G.Adj x y ∧ S y := by
  induction h with
  | refl => exact False.elim (hu hv)
  | @step u z v hpu huz tail ih =>
    by_cases hz : S z
    · exact ⟨u,z,hpu,hu,huz,hz⟩
    · exact ih hz hv

/-- In a connected-cone elimination order, every nonroot's parent is in its
actual adhesion. This is the singleton-margin case of the sane connector
lemma, proved without assuming any parent edge in the original graph. -/
theorem connected_parent_in_bag (G : Graph n) (O : RankedOrder n)
    (he : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (hc : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    {v} (hp : O.parent v ≠ v) : RegionBag G O v (O.parent v) := by
  have hpv := O.parent_rel hp
  have hpath := hc (O.parent v) v (Or.inl hpv)
  have hnot : ¬ Cone O v (O.parent v) := by
    rintro (h | h)
    · exact O.irrefl v (O.trans h hpv)
    · exact hp h.symm
  obtain ⟨x,y,hpx,hx,hxy,hy⟩ := walk_crosses hpath hnot (cone_refl O v)
  have hb : RegionBag G O v x := (regionBag_boundary G O he v x).mpr
    (Or.inr ⟨hx,y,hy,hxy⟩)
  have hxv : O.rel x v := (hb.resolve_left (fun eq => hx (Or.inr eq.symm))).1
  have hxp : x = O.parent v := by
    rcases hpx with h | h
    · exact False.elim ((O.parent_cover hpv).2 ⟨x,h,hxv⟩)
    · exact h.symm
  exact hxp ▸ hb

/-- The parent forest can therefore be realized using edges of cliques on
captured whole bags. No binary parent parameter needs to be guessed. -/
def FilledBagsAdj (G : Graph n) (O : RankedOrder n) (u v : Fin n) : Prop :=
  u ≠ v ∧ (G.Adj u v ∨ ∃ x, RegionBag G O x u ∧ RegionBag G O x v)

theorem normalized_parent_filled (G : Graph n) (O : RankedOrder n)
    (he : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u) {v}
    (hp : (normalizedOrder G O).parent v ≠ v) :
    FilledBagsAdj G (normalizedOrder G O) ((normalizedOrder G O).parent v) v := by
  refine ⟨hp,Or.inr ⟨v,?_,Or.inl rfl⟩⟩
  apply connected_parent_in_bag G (normalizedOrder G O) (normalized_eliminates G O he) ?_ hp
  intro x y h
  exact (reachCone_connected G O (reachCone_refl G O x)
    ((normalized_cone G O x y).mp h)).mono
      (fun z hz => (normalized_cone G O x z).mpr hz)

/-- An actual finite parent-forest decomposition. Its nodes are original
vertices and the rank is an acyclicity certificate, not a new hypothesis. -/
structure ForestDecomposition (G : Graph n) where
  order : RankedOrder n
  bag : Fin n → Finset (Fin n)
  vertex : ∀ u, ∃ v, u ∈ bag v
  edge : ∀ {u v}, G.Adj u v → ∃ x, u ∈ bag x ∧ v ∈ bag x
  running : ∀ {u v w}, u ∈ bag v → u ∈ bag w →
    Walk (ParentAdj order) (fun z => u ∈ bag z) v w

noncomputable def normalizedDecomposition (G : Graph n) (O : RankedOrder n)
    (he : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u) : ForestDecomposition G where
  order := normalizedOrder G O
  bag v := eliminationFrontierSet (normalizedOrder G O).forest G v
  vertex u := ⟨u,by
    classical
    simp only [eliminationFrontierSet,Finset.mem_filter,Finset.mem_univ,true_and]
    exact Or.inl rfl⟩
  edge := by
    intro u v huv
    obtain ⟨x,hx,hy⟩ := regionBag_edge G (normalizedOrder G O) (normalized_eliminates G O he) huv
    refine ⟨x,?_,?_⟩ <;>
      simp only [eliminationFrontierSet,Finset.mem_filter,Finset.mem_univ,true_and]
    · exact (regionBag_iff_frontier G _ x u).mp hx
    · exact (regionBag_iff_frontier G _ x v).mp hy
  running := by
    intro u v w hv hw
    simp only [eliminationFrontierSet,Finset.mem_filter,Finset.mem_univ,true_and] at hv hw
    have hv' := (regionBag_iff_frontier G _ v u).mpr hv
    have hw' := (regionBag_iff_frontier G _ w u).mpr hw
    exact (regionBag_running G _ hv' hw').mono (fun z hz => by
      simp only [eliminationFrontierSet,Finset.mem_filter,Finset.mem_univ,true_and]
      exact (regionBag_iff_frontier G _ z u).mp hz)

/-- Concrete normalization of the accepted supplied-decomposition object.
Every output bag is contained in the input bag selected by its retained
introduction-node origin label. -/
noncomputable def normalizeSupplied {t} {G : Graph n} {T : FinitePort.RootedTree t}
    (D : Decomposition G T) : ForestDecomposition G :=
  normalizedDecomposition G (introductionOrder D) (introductionEarlier_eliminates D)

theorem normalizeSupplied_origin {t} {G : Graph n} {T : FinitePort.RootedTree t}
    (D : Decomposition G T) {v u} (h : u ∈ (normalizeSupplied D).bag v) :
    u ∈ D.bag (introductionNode D v) := by
  classical
  apply normalized_origin_bag D
  exact (Finset.mem_filter.mp h).2

theorem normalizeSupplied_bound {t} {G : Graph n} {T : FinitePort.RootedTree t}
    (D : Decomposition G T) {b} (hb : D.BagBound b) (v) :
    ((normalizeSupplied D).bag v).card ≤ b :=
  (normalized_frontier_card G (introductionOrder D) v).trans (eliminationFrontier_bound D hb v)

#print axioms normalizedDecomposition
#print axioms normalizeSupplied_bound
#print axioms normalized_component_connected
#print axioms normalized_parent_filled
end StackSorting.ConnectedConeNormalization
