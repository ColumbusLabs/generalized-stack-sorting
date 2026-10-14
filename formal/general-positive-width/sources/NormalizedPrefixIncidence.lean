import NormalizedPrefixGeometry

namespace StackSorting.PrefixGrowth
open GraphWidth SameVertexForest ConnectedConeNormalization
variable {n : Nat}

/-- Concrete hypertorso edge identifiers retain original ordered edge copies
and individual boundary-node identifiers; equal adhesions are not identified. -/
def PrefixHypertorsoInc (G : Graph n) (O : RankedOrder n) (r : Fin n) (Z : Finset (Fin n)) :
    Fin n → ((Fin n × Fin n) ⊕ Fin n) → Prop
  | x,.inl e => G.Adj e.1 e.2 ∧ e.1 ∈ prefixVertices G O r Z ∧
      e.2 ∈ prefixVertices G O r Z ∧ (x = e.1 ∨ x = e.2)
  | x,.inr c => Frontier (clippedParent O r) Z c ∧ RegionAdhesion G O c x

theorem prefixHypertorso_support (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (x : Fin n)
    (e : (Fin n × Fin n) ⊕ Fin n) (h : PrefixHypertorsoInc G O r Z x e) :
    x ∈ prefixVertices G O r Z := by
  cases e with
  | inl e => exact h.2.2.2.elim (fun he => he.symm ▸ h.2.1) (fun he => he.symm ▸ h.2.2.1)
  | inr c =>
    have hc := (relative_frontier_cone O r Z hp c h.1).2.1
    exact exposed_bag_subset G O r Z hp hc ((mem_regionBagSet G O (O.parent c) x).mpr h.2.2.2)

theorem prefixVertices_insert (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (z : Fin n) :
    prefixVertices G O r (insert z Z) = insert z (prefixVertices G O r Z) := by
  classical
  simp only [prefixVertices,Finset.insert_union]

/-- No still-hidden frontier vertex can precede an already visible vertex. -/
theorem frontier_no_visible_descendant (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) {x : Fin n}
    (hx : x ∈ prefixVertices G O r Z) : ¬ O.rel z x := by
  intro hzx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact hz.1 (relativePrefix_ancestor O r Z hp
      (Or.inl (relative_frontier_cone O r Z hp z hz).1) (Or.inl hzx) hx)
  · have had := (regionAdhesion_iff G O r x).mp ((mem_regionAdhesionSet G O r x).mp hx)
    have hxr := (had.1.resolve_left had.2).1
    exact O.irrefl r (O.trans (relative_frontier_cone O r Z hp z hz).1 (O.trans hzx hxr))

/-- Every original edge newly exposed by inserting z has both endpoints in
z's actual bag. This prevents duplication of already present original edges. -/
theorem frontier_neighbor_in_bag (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (r : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) {x : Fin n}
    (hx : x ∈ prefixVertices G O r Z) (hxe : G.Adj x z) : RegionBag G O z x := by
  rcases helim hxe with hxz | hzx
  · exact Or.inr ⟨hxz,z,cone_refl O z,hxe⟩
  · exact (frontier_no_visible_descendant G O r Z hp z hz hx hzx).elim

/-- The exposed boundary-node set changes exactly by removing z and adding its
actual children. No cutedge order or replacement component label is assumed. -/
theorem relative_frontier_insert_iff (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) (c : Fin n) :
    Frontier (clippedParent O r) (insert z Z) c ↔
      (Frontier (clippedParent O r) Z c ∧ c ≠ z) ∨ (O.parent c = z ∧ O.parent c ≠ c) := by
  rw [frontier_insert_iff _ Z z c hp.1 hz.1]
  have hzr : z ≠ r := fun he => hz.1 (he.symm ▸ hp.2.1)
  constructor
  · rintro (h | ⟨hpar,hcz⟩)
    · exact Or.inl h
    · have hcr : c ≠ r := by
        intro he
        subst c
        have hrz : r = z := by simpa [clippedParent] using hpar
        exact hzr hrz.symm
      have hc : O.parent c = z := by simpa only [clippedParent,ite_eq_right hcr] using hpar
      exact Or.inr ⟨hc,fun he => hcz (he.symm.trans hc)⟩
  · rintro (h | ⟨hpar,hne⟩)
    · exact Or.inl h
    · have hcr : c ≠ r := by
        intro he
        subst c
        have hpr := O.parent_rel hne
        have hzr' : O.rel z r := hpar ▸ hpr
        exact O.irrefl r (O.trans (relative_frontier_cone O r Z hp z hz).1 hzr')
      exact Or.inr ⟨by simpa only [clippedParent,ite_eq_right hcr] using hpar,
        fun he => hne (hpar.trans he.symm)⟩

/-- The next concrete incidence relation is exactly old surviving incidences
plus the local replacement incidences. An original edge identifier is not duplicated across exposure stages. -/
theorem prefix_incidence_step (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (r : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) (x : Fin n) (e : (Fin n × Fin n) ⊕ Fin n) :
    PrefixHypertorsoInc G O r (insert z Z) x e ↔
      (PrefixHypertorsoInc G O r Z x e ∧ e ≠ .inr z) ∨ LocalHypertorsoInc G O z x e := by
  classical
  cases e with
  | inr c =>
    change (Frontier (clippedParent O r) (insert z Z) c ∧ RegionAdhesion G O c x) ↔ _
    rw [relative_frontier_insert_iff O r Z hp z hz c]
    constructor
    · rintro ⟨(⟨hfront,hcz⟩ | ⟨hpar,hne⟩),had⟩
      · exact Or.inl ⟨⟨hfront,had⟩,fun h => hcz (Sum.inr.inj h)⟩
      · exact Or.inr ⟨hpar,hne,had⟩
    · rintro (⟨⟨hfront,had⟩,hcz⟩ | ⟨hpar,hne,had⟩)
      · exact ⟨Or.inl ⟨hfront,fun h => hcz (congrArg Sum.inr h)⟩,had⟩
      · exact ⟨Or.inr ⟨hpar,hne⟩,had⟩
  | inl e =>
    constructor
    · rintro ⟨hedge,ha,hb,hx⟩
      rw [prefixVertices_insert] at ha hb
      by_cases haold : e.1 ∈ prefixVertices G O r Z
      · by_cases hbold : e.2 ∈ prefixVertices G O r Z
        · exact Or.inl ⟨⟨hedge,haold,hbold,hx⟩,by simp⟩
        · have hbz : e.2 = z := (Finset.mem_insert.mp hb).resolve_right hbold
          have habag := frontier_neighbor_in_bag G O helim r Z hp z hz haold (hbz ▸ hedge)
          have hbbag : RegionBag G O z e.2 := hbz.symm ▸ (Or.inl rfl : RegionBag G O z z)
          exact Or.inr ⟨hedge,Or.inr hbz,habag,hbbag,hx⟩
      · have haz : e.1 = z := (Finset.mem_insert.mp ha).resolve_right haold
        have habag : RegionBag G O z e.1 := haz.symm ▸ (Or.inl rfl : RegionBag G O z z)
        have hbbag : RegionBag G O z e.2 := by
          rcases Finset.mem_insert.mp hb with hbz | hbold
          · exact hbz.symm ▸ (Or.inl rfl : RegionBag G O z z)
          · exact frontier_neighbor_in_bag G O helim r Z hp z hz hbold (haz ▸ G.symm hedge)
        exact Or.inr ⟨hedge,Or.inl haz,habag,hbbag,hx⟩
    · rintro (⟨⟨hedge,ha,hb,hx⟩,_⟩ | ⟨hedge,_,ha,hb,hx⟩)
      · refine ⟨hedge,?_,?_,hx⟩ <;> rw [prefixVertices_insert]
        · exact Finset.mem_insert_of_mem ha
        · exact Finset.mem_insert_of_mem hb
      · have hnew := relativePrefix_insert O r Z hp z hz
        have hbag := exposed_bag_subset G O r (insert z Z) hnew (Finset.mem_insert_self z Z)
        exact ⟨hedge,hbag ((mem_regionBagSet G O z e.1).mpr ha),
          hbag ((mem_regionBagSet G O z e.2).mpr hb),hx⟩

/-- Active old and inserted identifiers are disjoint even though they share a
common presentation type. This is the injectivity fact for the replacement relabeling. -/
theorem old_local_identifiers_disjoint (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) (e : (Fin n × Fin n) ⊕ Fin n)
    (x y : Fin n) (hold : PrefixHypertorsoInc G O r Z x e)
    (hnew : LocalHypertorsoInc G O z y e) : False := by
  cases e with
  | inl e =>
    rcases hnew.2.1 with ha | hb
    · exact frontier_not_visible G O r Z hp z hz (ha ▸ hold.2.1)
    · exact frontier_not_visible G O r Z hp z hz (hb ▸ hold.2.2.1)
  | inr c =>
    have hcr : c ≠ r := fun he => hold.1.1 (he.symm ▸ hp.2.1)
    have hpar : O.parent c ∈ Z := by simpa only [clippedParent,ite_eq_right hcr] using hold.1.2
    exact hz.1 (hnew.1 ▸ hpar)

end StackSorting.PrefixGrowth
