import SaneParentConnector

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.MultiMargin
open FinitePort Nested
variable {n t : Nat} {G : Graph n} {T : RootedTree t}

/-- Literal original adhesion: the parent-bag intersection, empty at the root. -/
def adhesion (D : Decomposition G T) (x : Fin t) (v : Fin n) : Prop :=
  x.val ≠ 0 ∧ v ∈ D.bag x ∧ v ∈ D.bag (T.parent x)

theorem adhesion_iff (D : Decomposition G T) (x : Fin t) (v : Fin n) :
    adhesion D x v ↔ outerAdhesion D x v := by
  constructor
  · rintro ⟨hx,hb,hp⟩
    refine ⟨hb,?_⟩
    intro he
    have hi := (introduction_ancestor D hp).val_le
    rw [he] at hi
    have := T.parent_lt x hx
    omega
  · rintro ⟨hb,hn⟩
    have hi := introduction_ancestor D hb
    have hx := hi.ne_zero_of_strict hn
    exact ⟨hx,hb,TreeAncestry.walk_convex (T := T) (P := fun i => v ∈ D.bag i)
      (D.running (introduction_spec D v).1 hb)
      (hi.parent_of_ne hn) (.step hx (.refl _))⟩

def Margin (D : Decomposition G T) (x : Fin t) (v : Fin n) : Prop :=
  introductionNode D v = x

theorem margin_iff (D : Decomposition G T) (x : Fin t) (v : Fin n) :
    Margin D x v ↔ v ∈ D.bag x ∧ ¬ adhesion D x v := by
  rw [adhesion_iff]
  constructor
  · intro h
    exact ⟨h ▸ (introduction_spec D v).1,fun ha => ha.2 h⟩
  · rintro ⟨hb,ha⟩
    by_contra hn
    exact ha ⟨hb,hn⟩

/-- The actual simple adhesion completion, retaining all original edges. -/
def Completion (D : Decomposition G T) : Graph n where
  Adj u v := u ≠ v ∧ (G.Adj u v ∨ ∃ x, outerAdhesion D x u ∧ outerAdhesion D x v)
  symm := by
    rintro u v ⟨hn,he | ⟨x,hu,hv⟩⟩
    · exact ⟨(Ne.symm hn),Or.inl (G.symm he)⟩
    · exact ⟨(Ne.symm hn),Or.inr ⟨x,hv,hu⟩⟩
  loopless _ h := h.1 rfl

theorem completion_original (D : Decomposition G T) {u v} (h : G.Adj u v) :
    (Completion D).Adj u v :=
  ⟨fun he => G.loopless v (he ▸ h),Or.inl h⟩

/-- Saneness data concern the original graph; no marginal connectivity or
completion-neighbor claim is assumed. -/
structure Sane (D : Decomposition G T) : Prop where
  margin_nonempty : ∀ x, ∃ v, Margin D x v
  component_connected : ConnectedIntroductionComponents D
  adhesion_neighbor : ∀ x v, outerAdhesion D x v →
    ∃ u, IntroductionComponent D x u ∧ G.Adj v u

def ChildBelow (T : RootedTree t) (x z y : Fin t) : Prop :=
  y.val ≠ 0 ∧ T.parent y=x ∧ Ancestor T y z

theorem exists_childBelow {x z : Fin t} (h : Ancestor T x z) (hn : x ≠ z) :
    ∃ y, ChildBelow T x z y := by
  induction h with
  | refl => exact (hn rfl).elim
  | @step z hz hxp ih =>
    by_cases he : x=T.parent z
    · exact ⟨z,hz,he.symm,.refl _⟩
    · obtain ⟨y,hy,hp,ha⟩ := ih he
      exact ⟨y,hy,hp,.step hz ha⟩

theorem childBelow_unique {x z y y' : Fin t}
    (h : ChildBelow T x z y) (h' : ChildBelow T x z y') : y=y' := by
  rcases TreeAncestry.comparable h.2.2 h'.2.2 with ha | ha
  · by_contra hn
    have hi := (ha.parent_of_ne hn).val_le
    rw [h'.2.1,← h.2.1] at hi
    have := T.parent_lt y h.1
    omega
  · by_contra hn
    have hi := (ha.parent_of_ne (Ne.symm hn)).val_le
    rw [h.2.1,← h'.2.1] at hi
    have := T.parent_lt y' h'.1
    omega

variable {D : Decomposition G T}

noncomputable def connector (s : Sane D) (y : Fin t) (hy : y.val ≠ 0) : Fin n :=
  Classical.choose (sane_parent_margin_connector D s.margin_nonempty s.component_connected y hy)

theorem connector_spec (s : Sane D) (y : Fin t) (hy : y.val ≠ 0) :
    Margin D (T.parent y) (connector s y hy) ∧ outerAdhesion D y (connector s y hy) :=
  Classical.choose_spec (sane_parent_margin_connector D s.margin_nonempty s.component_connected y hy)

noncomputable def retract (s : Sane D) (x : Fin t) (u : Fin n) : Fin n := by
  classical
  exact if h : ∃ y, ChildBelow T x (introductionNode D u) y then
    connector s (Classical.choose h) (Classical.choose_spec h).1 else u

theorem retract_child (s : Sane D) {x u y}
    (hy : ChildBelow T x (introductionNode D u) y) :
    retract s x u = connector s y hy.1 := by
  classical
  have h : ∃ z, ChildBelow T x (introductionNode D u) z := ⟨y,hy⟩
  have he := childBelow_unique (Classical.choose_spec h) hy
  simp only [retract,dite_eq_left h]
  subst y
  rfl

theorem retract_margin (s : Sane D) {x u} (hu : Margin D x u) : retract s x u=u := by
  classical
  have hn : ¬ ∃ y, ChildBelow T x (introductionNode D u) y := by
    rintro ⟨y,hy,hp,ha⟩
    have hi := ha.val_le
    rw [hu,← hp] at hi
    have := T.parent_lt y hy
    omega
  simp only [retract,dite_eq_right hn]

theorem retract_mem (s : Sane D) {x u} (hu : IntroductionComponent D x u) :
    Margin D x (retract s x u) := by
  by_cases he : introductionNode D u=x
  · rw [retract_margin s he]
    exact he
  · obtain ⟨y,hy⟩ := exists_childBelow hu (Ne.symm he)
    rw [retract_child s hy]
    simpa only [hy.2.1] using (connector_spec s y hy.1).1

theorem margin_outside_child {x u y} (hu : Margin D x u)
    (hy : y.val ≠ 0) (hp : T.parent y=x) : ¬ IntroductionComponent D y u := by
  intro ha
  have hi := ha.val_le
  rw [hu,← hp] at hi
  have := T.parent_lt y hy
  omega

/-- Distinct immediate child components have no original edge between them. -/
theorem edge_child_equal {x u v y z}
    (hy : ChildBelow T x (introductionNode D u) y)
    (hz : ChildBelow T x (introductionNode D v) z) (he : G.Adj u v) : y=z := by
  rcases edge_introductions_comparable D he with h | h
  · exact childBelow_unique ⟨hy.1,hy.2.1,hy.2.2.trans h⟩ hz
  · exact childBelow_unique hy ⟨hz.1,hz.2.1,hz.2.2.trans h⟩

/-- The retraction of each original edge is equality or a real completed edge. -/
theorem retract_edge (s : Sane D) {x u v}
    (hu : IntroductionComponent D x u) (hv : IntroductionComponent D x v)
    (he : G.Adj u v) :
    retract s x u=retract s x v ∨ (Completion D).Adj (retract s x u) (retract s x v) := by
  by_cases hn : retract s x u=retract s x v
  · exact Or.inl hn
  right
  refine ⟨hn,?_⟩
  by_cases hum : introductionNode D u=x
  · rw [retract_margin s hum]
    by_cases hvm : introductionNode D v=x
    · rw [retract_margin s hvm]
      exact Or.inl he
    · obtain ⟨y,hy⟩ := exists_childBelow hv (Ne.symm hvm)
      rw [retract_child s hy]
      exact Or.inr ⟨y,component_exit_adhesion D hy.2.2
        (margin_outside_child hum hy.1 hy.2.1) (G.symm he),(connector_spec s y hy.1).2⟩
  · obtain ⟨y,hy⟩ := exists_childBelow hu (Ne.symm hum)
    rw [retract_child s hy]
    by_cases hvm : introductionNode D v=x
    · rw [retract_margin s hvm]
      exact Or.inr ⟨y,(connector_spec s y hy.1).2,component_exit_adhesion D hy.2.2
        (margin_outside_child hvm hy.1 hy.2.1) he⟩
    · obtain ⟨z,hz⟩ := exists_childBelow hv (Ne.symm hvm)
      have eq := edge_child_equal hy hz he
      have hre : retract s x u=retract s x v := by
        rw [retract_child s hy,retract_child s hz]
        subst z
        rfl
      exact (hn hre).elim

/-- A component walk maps to a marginal walk, collapsing repeated images. -/
theorem retract_walk (s : Sane D) {x u v}
    (w : Walk G.Adj (IntroductionComponent D x) u v) :
    Walk (Completion D).Adj (Margin D x) (retract s x u) (retract s x v) := by
  induction w with
  | refl hu => exact .refl (retract_mem s hu)
  | @step u a v hu he w ih =>
    rcases retract_edge s hu w.start he with eq | adj
    · exact eq.symm ▸ ih
    · exact .step (retract_mem s hu) adj ih

/-- Actual marginal connectivity, with unbounded margins permitted. -/
theorem marginal_connected (s : Sane D) {x u v} (hu : Margin D x u) (hv : Margin D x v) :
    Walk (Completion D).Adj (Margin D x) u v := by
  have hcu : IntroductionComponent D x u := by rw [IntroductionComponent,hu]; exact .refl _
  have hcv : IntroductionComponent D x v := by rw [IntroductionComponent,hv]; exact .refl _
  have h := retract_walk s (s.component_connected x u v hcu hcv)
  simpa only [retract_margin s hu,retract_margin s hv] using h

/-- Claim 11 is derived from original-edge saneness, not supplied as a premise. -/
theorem adhesion_margin_neighbor (s : Sane D) {x v} (hv : outerAdhesion D x v) :
    ∃ u, Margin D x u ∧ (Completion D).Adj v u := by
  obtain ⟨w,hw,he⟩ := s.adhesion_neighbor x v hv
  refine ⟨retract s x w,retract_mem s hw,?_⟩
  have hne : v ≠ retract s x w := by
    intro eq
    exact hv.2 (eq.symm ▸ retract_mem s hw)
  refine ⟨hne,?_⟩
  by_cases hm : introductionNode D w=x
  · rw [retract_margin s hm]
    exact Or.inl he
  · obtain ⟨y,hy⟩ := exists_childBelow hw (Ne.symm hm)
    rw [retract_child s hy]
    have hout : ¬ IntroductionComponent D y v := by
      intro ha
      have hi := (introduction_ancestor D hv.1).val_le
      have hj := ha.val_le
      have hp := T.parent_lt y hy.1
      rw [hy.2.1] at hp
      omega
    exact Or.inr ⟨y,component_exit_adhesion D hy.2.2 hout (G.symm he),
      (connector_spec s y hy.1).2⟩

/-- The original bag is precisely its margin and the original-graph boundary
of its original component. Completion adjacency is deliberately not used. -/
theorem bag_boundary_exact (s : Sane D) (x : Fin t) (v : Fin n) :
    v ∈ D.bag x ↔ Margin D x v ∨
      (¬ IntroductionComponent D x v ∧ ∃ u, IntroductionComponent D x u ∧ G.Adj v u) := by
  constructor
  · intro hv
    by_cases hm : introductionNode D v=x
    · exact Or.inl hm
    · refine Or.inr ⟨?_,s.adhesion_neighbor x v ⟨hv,hm⟩⟩
      intro ha
      exact hm (TreeAncestry.antisymm (introduction_ancestor D hv) ha)
  · rintro (hm | ⟨hout,u,hu,he⟩)
    · exact hm ▸ (introduction_spec D v).1
    · exact (component_exit_adhesion D hu hout (G.symm he)).1

#print axioms marginal_connected
#print axioms adhesion_margin_neighbor
#print axioms bag_boundary_exact
end StackSorting.GraphWidth.MultiMargin
