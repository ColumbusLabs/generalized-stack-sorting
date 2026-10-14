import SuppliedPrefixSeparation

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}

/-- Deleted vertices remain isolated in the ambient type; no new vertices or
edges are introduced by root-adhesion pruning. -/
def inducedGraph (G : Graph n) (allowed : Fin n → Prop) : Graph n where
  Adj x y := G.Adj x y ∧ allowed x ∧ allowed y
  symm := fun h => ⟨G.symm h.1,h.2.2,h.2.1⟩
  loopless := fun x h => G.loopless x h.1

namespace Walk
/-- Preserve an actual walk whose entire allowed region survives pruning. -/
theorem toInduced {G : Graph n} {P allowed : Fin n → Prop}
    (keep : ∀ x, P x → allowed x) {x y : Fin n} (w : GraphWidth.Walk G.Adj P x y) :
    GraphWidth.Walk (inducedGraph G allowed).Adj P x y :=
  match w with
  | .refl hx => .refl hx
  | .step hx hxy tail => .step hx ⟨hxy,keep _ hx,keep _ tail.start⟩ (toInduced keep tail)
end Walk

def rootAllowed (G : Graph n) (O : RankedOrder n) (r s t x : Fin n) : Prop :=
  ¬ RegionAdhesion G O r x ∨ x = s ∨ x = t

theorem cone_disjoint_adhesion (G : Graph n) (O : RankedOrder n) {r x : Fin n}
    (hx : Cone O r x) : ¬ RegionAdhesion G O r x := by
  intro ha
  obtain ⟨hb,hne⟩ := (regionAdhesion_iff G O r x).mp ha
  rcases hb with he | ⟨hxr,_,_,_⟩
  · exact hne he
  · rcases hx with hrx | he
    · exact O.irrefl r (O.trans hrx hxr)
    · subst x
      exact O.irrefl r hxr

theorem cone_allowed (G : Graph n) (O : RankedOrder n) (r s t : Fin n)
    {x : Fin n} (hx : Cone O r x) : rootAllowed G O r s t x :=
  Or.inl (cone_disjoint_adhesion G O hx)

noncomputable def prunedOrder (G : Graph n) (O : RankedOrder n) (r s t : Fin n) : RankedOrder n :=
  normalizedOrder (inducedGraph G (rootAllowed G O r s t)) O

theorem pruned_walk (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) {v u : Fin n} (hv : Cone O r v) (hu : Cone O v u) :
    GraphWidth.Walk (inducedGraph G (rootAllowed G O r s t)).Adj (Cone O v) v u :=
  Walk.toInduced (fun _ hx => cone_allowed G O r s t (cone_trans O hv hx)) (cones v u hu)

/-- All descendant cones below the selected root are unchanged. The global
normalization may change ancestors above that root, which are not assumed fixed. -/
theorem pruned_cone_iff (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) {v u : Fin n} (hv : Cone O r v) :
    Cone (prunedOrder G O r s t) v u ↔ Cone O v u := by
  constructor
  · intro h
    exact ((normalized_cone _ O v u).mp h).finish
  · intro h
    exact (normalized_cone _ O v u).mpr (pruned_walk G O cones r s t hv h)

theorem pruned_rel_old (G : Graph n) (O : RankedOrder n) (r s t : Fin n)
    {u v : Fin n} (h : (prunedOrder G O r s t).rel u v) : O.rel u v :=
  h.1.finish.resolve_right h.2

theorem pruned_rel_iff (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) {v u : Fin n} (hv : Cone O r v) :
    (prunedOrder G O r s t).rel v u ↔ O.rel v u := by
  constructor
  · exact pruned_rel_old G O r s t
  · intro h
    refine ⟨pruned_walk G O cones r s t hv (Or.inl h),?_⟩
    intro he
    subst u
    exact O.irrefl v h

/-- The exact parent is preserved at every proper descendant of the root. -/
theorem pruned_parent (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) {v : Fin n} (hv : O.rel r v) :
    (prunedOrder G O r s t).parent v = O.parent v := by
  have hc := O.parent_cover hv
  apply ((prunedOrder G O r s t).parent_eq_iff_cover (O.parent_ne_of_pred hv)).mpr
  refine ⟨(pruned_rel_iff G O cones r s t (cone_parent O hv)).mpr hc.1,?_⟩
  rintro ⟨w,hw,hwv⟩
  exact hc.2 ⟨w,pruned_rel_old G O r s t hw,pruned_rel_old G O r s t hwv⟩

end StackSorting.LowPathwidthParts
