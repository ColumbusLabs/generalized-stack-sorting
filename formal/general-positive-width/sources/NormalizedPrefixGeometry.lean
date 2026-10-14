import NormalizedLocalHypertorso
import FinitePrefixSaturation

namespace StackSorting.PrefixGrowth
open GraphWidth SameVertexForest ConnectedConeNormalization
variable {n : Nat}

noncomputable def clippedParent (O : RankedOrder n) (r x : Fin n) : Fin n := if x = r then r else O.parent x

def RelativePrefix (O : RankedOrder n) (r : Fin n) (Z : Finset (Fin n)) : Prop :=
  IsPrefix (clippedParent O r) Z ∧ r ∈ Z ∧ ∀ x ∈ Z, Cone O r x

theorem relativePrefix_singleton (O : RankedOrder n) (r : Fin n) : RelativePrefix O r {r} := by
  refine ⟨root_prefix _ r (by simp [clippedParent]),by simp,?_⟩
  intro x hx
  have he := Finset.mem_singleton.mp hx
  subst x
  exact cone_refl O r

theorem relative_frontier_cone (O : RankedOrder n) (r : Fin n) (Z : Finset (Fin n))
    (hp : RelativePrefix O r Z) (x : Fin n) (hx : Frontier (clippedParent O r) Z x) :
    O.rel r x ∧ O.parent x ∈ Z ∧ O.parent x ≠ x := by
  have hxr : x ≠ r := fun he => hx.1 (he.symm ▸ hp.2.1)
  have hpx : O.parent x ∈ Z := by simpa only [clippedParent,ite_eq_right hxr] using hx.2
  have hne : O.parent x ≠ x := fun he => hx.1 (he ▸ hpx)
  have hrel := O.parent_rel hne
  have hc := hp.2.2 _ hpx
  refine ⟨?_,hpx,hne⟩
  rcases hc with hc | hc
  · exact O.trans hc hrel
  · exact hc.symm ▸ hrel

theorem relativePrefix_insert (O : RankedOrder n) (r : Fin n) (Z : Finset (Fin n))
    (hp : RelativePrefix O r Z) (x : Fin n) (hx : Frontier (clippedParent O r) Z x) :
    RelativePrefix O r (insert x Z) := by
  refine ⟨insert_frontier_prefix _ Z x hp.1 hx,Finset.mem_insert_of_mem hp.2.1,?_⟩
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact Or.inl (relative_frontier_cone O r Z hp _ hx).1
  · exact hp.2.2 y hy

/-- Every ancestor in the chosen rooted subtree has already been exposed. -/
theorem relativePrefix_ancestor (O : RankedOrder n) (r : Fin n) (Z : Finset (Fin n))
    (hp : RelativePrefix O r Z) {u v : Fin n} (hu : Cone O r u)
    (huv : Cone O u v) (hv : v ∈ Z) : u ∈ Z := by
  rcases huv with huv | rfl
  · have hvr : v ≠ r := by
      intro he
      subst v
      rcases hu with hu | hu
      · exact O.irrefl r (O.trans hu huv)
      · exact O.irrefl r (hu.symm ▸ huv)
    have hparent : O.parent v ∈ Z := by
      simpa only [clippedParent,ite_eq_right hvr] using hp.1 v hv
    exact relativePrefix_ancestor O r Z hp hu (cone_parent O huv) hparent
  · exact hv
termination_by O.rank v
decreasing_by exact O.parent_rank_lt (O.parent_ne_of_pred huv)

/-- Visible original vertices consist of exposed singleton margins and the
fixed root adhesion, exactly matching the union of the exposed bags. -/
noncomputable def prefixVertices (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) : Finset (Fin n) := Z ∪ regionAdhesionSet G O r

theorem exposed_bag_subset (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) {z : Fin n} (hz : z ∈ Z) :
    regionBagSet G O z ⊆ prefixVertices G O r Z := by
  classical
  intro x hx
  have hb := (mem_regionBagSet G O z x).mp hx
  by_cases hxr : Cone O r x
  · exact Finset.mem_union_left _ (relativePrefix_ancestor O r Z hp hxr (regionBag_ancestor G O hb) hz)
  · apply Finset.mem_union_right _
    apply (mem_regionAdhesionSet G O r x).mpr
    apply (regionAdhesion_iff G O r x).mpr
    have hxne : x ≠ r := fun he => hxr (Or.inr he.symm)
    refine ⟨?_,hxne⟩
    have hxz := (regionBag_ancestor G O hb).resolve_right (fun he => hxr (he.symm ▸ hp.2.2 z hz))
    rcases hp.2.2 z hz with hrz | hrz
    · have hxr' : O.rel x r := by
        rcases O.predecessors hxz hrz with h | h | h
        · exact h
        · exact (hxne h).elim
        · exact (hxr (Or.inl h)).elim
      exact regionBag_interval G O hb (Or.inl hxr') (Or.inl hrz)
    · exact hrz.symm ▸ hb

theorem prefixVertices_eq_bag_union (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) :
    prefixVertices G O r Z = Z.biUnion (regionBagSet G O) := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_biUnion.mpr ⟨x,hx,(mem_regionBagSet G O x x).mpr (Or.inl rfl)⟩
    · have hb := ((mem_regionAdhesionSet G O r x).mp hx).2.1
      exact Finset.mem_biUnion.mpr ⟨r,hp.2.1,(mem_regionBagSet G O r x).mpr hb⟩
  · intro hx
    obtain ⟨z,hz,hxz⟩ := Finset.mem_biUnion.mp hx
    exact exposed_bag_subset G O r Z hp hz hxz

/-- A frontier margin is genuinely new, despite possible old adhesion overlap. -/
theorem frontier_not_visible (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) : z ∉ prefixVertices G O r Z := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · exact hz.1 h
  · have hzr := (((regionAdhesion_iff G O r z).mp ((mem_regionAdhesionSet G O r z).mp h)).1.resolve_left
      ((regionAdhesion_iff G O r z).mp ((mem_regionAdhesionSet G O r z).mp h)).2).1
    exact O.irrefl r (O.trans (relative_frontier_cone O r Z hp z hz).1 hzr)

/-- Exact vertex overlap for the next actual replacement is the actual
adhesion of the frontier node, derived from the decomposition geometry. -/
theorem frontier_overlap (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) :
    prefixVertices G O r Z ∩ regionBagSet G O z = regionAdhesionSet G O z := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hvis,hbag⟩ := Finset.mem_inter.mp hx
    have hne : x ≠ z := fun he => frontier_not_visible G O r Z hp z hz (he ▸ hvis)
    exact (mem_regionAdhesionSet G O z x).mpr ((regionAdhesion_iff G O z x).mpr
      ⟨(mem_regionBagSet G O z x).mp hbag,hne⟩)
  · intro hx
    have had := (mem_regionAdhesionSet G O z x).mp hx
    have hpz := (relative_frontier_cone O r Z hp z hz).2.1
    exact Finset.mem_inter.mpr ⟨exposed_bag_subset G O r Z hp hpz
      ((mem_regionBagSet G O (O.parent z) x).mpr had.2.2),
      (mem_regionBagSet G O z x).mpr had.2.1⟩

theorem frontier_visible_union (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) :
    prefixVertices G O r (insert z Z) = prefixVertices G O r Z ∪ regionBagSet G O z := by
  classical
  rw [prefixVertices_eq_bag_union G O r (insert z Z) (relativePrefix_insert O r Z hp z hz),
    Finset.biUnion_insert,← prefixVertices_eq_bag_union G O r Z hp]
  exact Finset.union_comm _ _

end StackSorting.PrefixGrowth
