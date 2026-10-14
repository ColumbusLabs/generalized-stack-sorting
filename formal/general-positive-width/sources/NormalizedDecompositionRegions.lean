import ConnectedConeNormalization
import RankedForestRoots

namespace StackSorting.ConnectedConeNormalization
open GraphWidth SameVertexForest
variable {n : Nat}

/-- Actual undirected parent links, with all root self-loops omitted. -/
def ParentAdj (O : RankedOrder n) (x y : Fin n) : Prop :=
  (O.parent x ≠ x ∧ O.parent x = y) ∨ (O.parent y ≠ y ∧ O.parent y = x)

theorem parentAdj_symm (O : RankedOrder n) {x y} : ParentAdj O x y → ParentAdj O y x := Or.symm

/-- Bags in an elimination order are its vertex plus its genuine frontier. -/
def RegionBag (G : Graph n) (O : RankedOrder n) (v u : Fin n) : Prop :=
  u = v ∨ O.rel u v ∧ ∃ w, Cone O v w ∧ G.Adj u w

@[simp] theorem regionBag_iff_frontier (G : Graph n) (O : RankedOrder n) (v u) :
    RegionBag G O v u ↔ EliminationFrontier O.forest G v u := by
  simp only [RegionBag,EliminationFrontier,O.ancestor_iff]
  constructor
  · rintro (h | ⟨huv,w,hw,he⟩)
    · exact Or.inl h
    · refine Or.inr ⟨Or.inl huv,?_,w,hw,he⟩
      intro e
      subst u
      exact O.irrefl v huv
  · rintro (h | ⟨huv,hne,w,hw,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨huv.resolve_right hne,w,hw,he⟩

theorem regionBag_ancestor (G : Graph n) (O : RankedOrder n) {u v}
    (h : RegionBag G O v u) : Cone O u v := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h.1

theorem cone_parent (O : RankedOrder n) {u v}
    (h : O.rel u v) : Cone O u (O.parent v) := by
  have hp := (O.parent_of_pred h).1
  rcases O.predecessors h hp with hu | he | hu
  · exact Or.inl hu
  · exact Or.inr he
  · exact False.elim ((O.parent_cover h).2 ⟨u,hu,h⟩)

/-- Explicit parent-link walk through every branch interval. -/
theorem cone_walk (O : RankedOrder n) {P : Fin n → Prop} {u v}
    (h : Cone O u v) (hc : ∀ z, Cone O u z → Cone O z v → P z) :
    Walk (ParentAdj O) P u v := by
  rcases h with h | rfl
  · have hp : O.rel (O.parent v) v := (O.parent_of_pred h).1
    have hu := cone_parent O h
    have hq : P (O.parent v) := hc _ hu (Or.inl hp)
    have hv : P v := hc _ (Or.inl h) (cone_refl O v)
    exact (cone_walk O hu (fun z hz hzq => hc z hz (cone_trans O hzq (Or.inl hp)))).trans
      (.step hq (Or.inr ⟨O.parent_ne_of_pred h,rfl⟩) (.refl hv))
  · exact .refl (hc _ (cone_refl O u) (cone_refl O u))
termination_by O.rank v
decreasing_by exact O.parent_rank_lt (O.parent_ne_of_pred h)

/-- Every occurrence is joined to the vertex's own bag using only bags
containing that vertex. Thus the occurrence sets are genuinely connected. -/
theorem regionBag_walk (G : Graph n) (O : RankedOrder n) {u v}
    (h : RegionBag G O v u) : Walk (ParentAdj O) (fun z => RegionBag G O z u) u v := by
  apply cone_walk O (regionBag_ancestor G O h)
  intro z huz hzv
  by_cases he : u = z
  · exact Or.inl he
  · refine Or.inr ⟨huz.resolve_right he,?_⟩
    rcases h with huv | ⟨_,w,hw,he⟩
    · subst v
      rcases hzv with hz | hz
      · exact False.elim (O.irrefl u (O.trans (huz.resolve_right he) hz))
      · exact False.elim (he hz.symm)
    · exact ⟨w,cone_trans O hzv hw,he⟩

theorem regionBag_running (G : Graph n) (O : RankedOrder n) {u v w}
    (hv : RegionBag G O v u) (hw : RegionBag G O w u) :
    Walk (ParentAdj O) (fun z => RegionBag G O z u) v w :=
  ((regionBag_walk G O hv).reverse (parentAdj_symm O)).trans (regionBag_walk G O hw)

theorem regionBag_edge (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u) {u v}
    (h : G.Adj u v) : ∃ x, RegionBag G O x u ∧ RegionBag G O x v := by
  rcases helim h with huv | hvu
  · exact ⟨v,Or.inr ⟨huv,v,cone_refl O v,h⟩,Or.inl rfl⟩
  · exact ⟨u,Or.inl rfl,Or.inr ⟨hvu,u,cone_refl O u,G.symm h⟩⟩

/-- Every strict bag member persists to the actual parent bag. -/
theorem strict_regionBag_parent (G : Graph n) (O : RankedOrder n) {u v}
    (h : RegionBag G O v u) (hne : u ≠ v) : RegionBag G O (O.parent v) u := by
  obtain ⟨huv,w,hw,he⟩ := h.resolve_left hne
  rcases cone_parent O huv with hup | hup
  · exact Or.inr ⟨hup,w,cone_trans O (Or.inl (O.parent_of_pred huv).1) hw,he⟩
  · exact Or.inl hup

/-- Margins are exactly singleton original vertices; no auxiliary graph
objects become introduction nodes. -/
theorem regionBag_margin (G : Graph n) (O : RankedOrder n) (u v) :
    (RegionBag G O v u ∧ (O.parent v = v ∨ ¬ RegionBag G O (O.parent v) u)) ↔ u = v := by
  constructor
  · rintro ⟨h,hroot | hnot⟩
    · rcases h with h | h
      · exact h
      · exact False.elim (O.parent_ne_of_pred h.1 hroot)
    · by_contra he
      exact hnot (strict_regionBag_parent G O h he)
  · intro he
    subst u
    refine ⟨Or.inl rfl,?_⟩
    by_cases hp : O.parent v = v
    · exact Or.inl hp
    · refine Or.inr ?_
      intro h
      rcases regionBag_ancestor G O h with h | h
      · exact O.irrefl v (O.trans h (O.parent_rel hp))
      · exact hp h.symm

/-- The external graph neighborhood of a rooted component. -/
def Boundary (G : Graph n) (O : RankedOrder n) (v u : Fin n) : Prop :=
  ¬ Cone O v u ∧ ∃ w, Cone O v w ∧ G.Adj u w

/-- Bag recovery uses only the rooted cones and original adjacency. -/
theorem regionBag_boundary (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u) (v u) :
    RegionBag G O v u ↔ u = v ∨ Boundary G O v u := by
  constructor
  · rintro (h | ⟨huv,w,hw,he⟩)
    · exact Or.inl h
    · refine Or.inr ⟨?_,w,hw,he⟩
      rintro (hvu | hvu)
      · exact O.irrefl u (O.trans huv hvu)
      · subst u
        exact O.irrefl v huv
  · rintro (h | ⟨hnot,w,hw,he⟩)
    · exact Or.inl h
    · refine Or.inr ⟨?_,w,hw,he⟩
      rcases helim he with huw | hwu
      · rcases hw with hvw | hvw
        · rcases O.predecessors huw hvw with huv | heq | hvu
          · exact huv
          · exact False.elim (hnot (Or.inr heq.symm))
          · exact False.elim (hnot (Or.inl hvu))
        · exact hvw.symm ▸ huw
      · exact False.elim (hnot (cone_trans O hw (Or.inl hwu)))

#print axioms regionBag_running
#print axioms regionBag_margin
#print axioms regionBag_boundary
end StackSorting.ConnectedConeNormalization

namespace StackSorting.ConnectedConeNormalization
open GraphWidth SameVertexForest
variable {n : Nat}

theorem regionBag_interval (G : Graph n) (O : RankedOrder n) {u v z}
    (hz : RegionBag G O z u) (huv : Cone O u v) (hvz : Cone O v z) :
    RegionBag G O v u := by
  by_cases he : u = v
  · exact Or.inl he
  · refine Or.inr ⟨huv.resolve_right he,?_⟩
    rcases hz with huz | ⟨_,w,hw,ha⟩
    · subst z
      rcases hvz with h | h
      · exact False.elim (O.irrefl u (O.trans (huv.resolve_right he) h))
      · exact False.elim (he h.symm)
    · exact ⟨w,cone_trans O hvz hw,ha⟩

def RegionAdhesion (G : Graph n) (O : RankedOrder n) (v u : Fin n) : Prop :=
  O.parent v ≠ v ∧ RegionBag G O v u ∧ RegionBag G O (O.parent v) u

def BagCone (G : Graph n) (O : RankedOrder n) (v u : Fin n) : Prop :=
  ∃ z, Cone O v z ∧ RegionBag G O z u

def BagComponent (G : Graph n) (O : RankedOrder n) (v u : Fin n) : Prop :=
  BagCone G O v u ∧ ¬ RegionAdhesion G O v u

theorem regionAdhesion_iff (G : Graph n) (O : RankedOrder n) (v u) :
    RegionAdhesion G O v u ↔ RegionBag G O v u ∧ u ≠ v := by
  constructor
  · rintro ⟨hp,hv,hq⟩
    refine ⟨hv,?_⟩
    intro he
    subst u
    rcases regionBag_ancestor G O hq with h | h
    · exact O.irrefl v (O.trans h (O.parent_rel hp))
    · exact hp h.symm
  · rintro ⟨h,hne⟩
    exact ⟨O.parent_ne_of_pred (h.resolve_left hne).1,h,strict_regionBag_parent G O h hne⟩

/-- The concrete union-of-bags minus adhesion agrees exactly with the
ancestry cone, not merely with a stipulated component field. -/
theorem bagComponent_iff (G : Graph n) (O : RankedOrder n) (v u) :
    BagComponent G O v u ↔ Cone O v u := by
  constructor
  · rintro ⟨⟨z,hvz,hzu⟩,hn⟩
    have huz := regionBag_ancestor G O hzu
    rcases hvz with hvz | hvz
    · rcases huz with huz | huz
      · rcases O.predecessors huz hvz with huv | he | hvu
        · exact False.elim (hn ((regionAdhesion_iff G O v u).mpr
            ⟨regionBag_interval G O hzu (Or.inl huv) (Or.inl hvz),by
              intro he; subst u; exact O.irrefl v huv⟩))
        · exact Or.inr he.symm
        · exact Or.inl hvu
      · exact Or.inl (huz.symm ▸ hvz)
    · have hb : RegionBag G O v u := hvz.symm ▸ hzu
      by_cases he : u = v
      · exact Or.inr he.symm
      · exact False.elim (hn ((regionAdhesion_iff G O v u).mpr ⟨hb,he⟩))
  · intro h
    refine ⟨⟨u,h,Or.inl rfl⟩,?_⟩
    intro ha
    obtain ⟨hb,hne⟩ := (regionAdhesion_iff G O v u).mp ha
    have huv := (hb.resolve_left hne).1
    rcases h with h | h
    · exact O.irrefl u (O.trans huv h)
    · exact hne h.symm
end StackSorting.ConnectedConeNormalization
