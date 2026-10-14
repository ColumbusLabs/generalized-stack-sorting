import SaneSingletonNormalization

/-! Singleton-margin specialization of Appendix C.2, Claims 10 and 11.
The filled graph uses only original edges and cliques on actual adhesions.
No parent atom or clique on an entire bag is assumed. -/
namespace StackSorting.ConnectedConeNormalization
open GraphWidth SameVertexForest
variable {n : Nat}

/-- Every strict descendant lies below an actual immediate child. -/
theorem cone_child (O : RankedOrder n) {v w} (h : O.rel v w) :
    ∃ c, O.parent c = v ∧ c ≠ v ∧ Cone O c w := by
  by_cases hp : O.parent w = v
  · exact ⟨w,hp,by intro e; subst w; exact O.irrefl v h,cone_refl O w⟩
  · have hvp : O.rel v (O.parent w) := (cone_parent O h).resolve_right (Ne.symm hp)
    obtain ⟨c,hcv,hne,hc⟩ := cone_child O hvp
    exact ⟨c,hcv,hne,cone_trans O hc (Or.inl (O.parent_of_pred h).1)⟩
termination_by O.rank w
decreasing_by exact O.parent_rank_lt (O.parent_ne_of_pred h)

/-- Adhesion-only clique completion, corresponding to the paper's G<t>. -/
def FilledAdhesionsAdj (G : Graph n) (O : RankedOrder n) (u v : Fin n) : Prop :=
  u ≠ v ∧ (G.Adj u v ∨ ∃ x, RegionAdhesion G O x u ∧ RegionAdhesion G O x v)

/-- Claim 11 for a singleton margin: every adhesion vertex is linked to
that margin in the adhesion-completed graph. -/
theorem adhesion_margin_filled (G : Graph n) (O : RankedOrder n)
    (he : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (hc : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    {v u} (ha : RegionAdhesion G O v u) : FilledAdhesionsAdj G O u v := by
  obtain ⟨hb,hne⟩ := (regionAdhesion_iff G O v u).mp ha
  obtain ⟨huv,w,hw,heuw⟩ := hb.resolve_left hne
  refine ⟨hne,?_⟩
  rcases hw with hvw | hvw
  · obtain ⟨c,hcv,hcvne,hcw⟩ := cone_child O hvw
    have hpc : O.parent c ≠ c := by intro h; exact hcvne (h.symm.trans hcv)
    have hvc : O.rel v c := hcv ▸ O.parent_rel hpc
    have huc : O.rel u c := O.trans huv hvc
    have hucne : u ≠ c := by intro h; subst u; exact O.irrefl c huc
    have hbcu : RegionBag G O c u := Or.inr ⟨huc,w,hcw,heuw⟩
    have hbcv : RegionBag G O c v := hcv ▸ connected_parent_in_bag G O he hc hpc
    exact Or.inr ⟨c,(regionAdhesion_iff G O c u).mpr ⟨hbcu,hucne⟩,
      (regionAdhesion_iff G O c v).mpr ⟨hbcv,Ne.symm hcvne⟩⟩
  · exact Or.inl (hvw.symm ▸ heuw)

/-- The normalized parent forest is a subgraph of the adhesion completion.
Combined with root-separator extraction this removes the whole-bag shortcut. -/
theorem normalized_parent_adhesion_filled (G : Graph n) (O : RankedOrder n)
    (he : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u) {v}
    (hp : (normalizedOrder G O).parent v ≠ v) :
    FilledAdhesionsAdj G (normalizedOrder G O) ((normalizedOrder G O).parent v) v := by
  have hc : ∀ x y, Cone (normalizedOrder G O) x y →
      Walk G.Adj (Cone (normalizedOrder G O) x) x y := by
    intro x y h
    exact (reachCone_connected G O (reachCone_refl G O x)
      ((normalized_cone G O x y).mp h)).mono
        (fun z hz => (normalized_cone G O x z).mpr hz)
  apply adhesion_margin_filled G (normalizedOrder G O) (normalized_eliminates G O he) hc
  exact (regionAdhesion_iff G _ v _).mpr
    ⟨connected_parent_in_bag G _ (normalized_eliminates G O he) hc hp,hp⟩

#print axioms cone_child
#print axioms adhesion_margin_filled
#print axioms normalized_parent_adhesion_filled
end StackSorting.ConnectedConeNormalization
