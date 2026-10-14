import NestedCliqueAttachment

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.Nested
open FinitePort
variable {n t : Nat} {G : Graph n} {T : RootedTree t}

/-- The actual component, expressed using derived introduction nodes. For
sane decompositions this is the connected cone with its adhesion removed. -/
def IntroductionComponent (D : Decomposition G T) (x : Fin t) (v : Fin n) : Prop :=
  Ancestor T x (introductionNode D v)

def ConnectedIntroductionComponents (D : Decomposition G T) : Prop :=
  ∀ x u v, IntroductionComponent D x u → IntroductionComponent D x v →
    Walk G.Adj (IntroductionComponent D x) u v

/-- A concrete crossing also retains the ambient allowed-vertex predicate. -/
theorem crossing_inside {α : Type} {adj : α → α → Prop} {P S : α → Prop}
    {a b : α} (w : Walk adj P a b) (ha : S a) (hb : ¬ S b) :
    ∃ u v, P u ∧ P v ∧ S u ∧ ¬ S v ∧ adj u v := by
  classical
  induction w with
  | refl => exact (hb ha).elim
  | @step a c b hpa hac hcb ih =>
    by_cases hc : S c
    · exact ih hc hb
    · exact ⟨a,c,hpa,hcb.start,ha,hc,hac⟩

/-- An actual edge leaving a child component ends in the child's adhesion. -/
theorem component_exit_adhesion (D : Decomposition G T) {x : Fin t} {u v : Fin n}
    (hu : IntroductionComponent D x u) (hv : ¬ IntroductionComponent D x v)
    (he : G.Adj u v) : outerAdhesion D x v := by
  have hviu : Ancestor T (introductionNode D v) (introductionNode D u) := by
    rcases edge_introductions_comparable D he with h | h
    · exact (hv (hu.trans h)).elim
    · exact h
  have hvx : Ancestor T (introductionNode D v) x := by
    rcases TreeAncestry.comparable hu hviu with h | h
    · exact (hv h).elim
    · exact h
  have hne : introductionNode D v≠x := by
    intro e
    apply hv
    rw [IntroductionComponent,e]
    exact .refl _
  obtain ⟨z,huz,hvz⟩ := D.edge he
  refine ⟨?_,hne⟩
  exact TreeAncestry.walk_convex (T := T) (P := fun i => v ∈ D.bag i)
    (D.running (introduction_spec D v).1 hvz) hvx
    (hu.trans (introduction_ancestor D huz))

/-- General multi-margin parent connector: no singleton normalization or bag
capture is used. The path is taken inside the actual parent component. -/
theorem sane_parent_margin_connector (D : Decomposition G T)
    (hm : ∀ x, ∃ v, introductionNode D v=x)
    (hc : ConnectedIntroductionComponents D) (x : Fin t) (hx : x.val≠0) :
    ∃ v, introductionNode D v=T.parent x ∧ outerAdhesion D x v := by
  obtain ⟨a,ha⟩ := hm x
  obtain ⟨b,hb⟩ := hm (T.parent x)
  have hpa : IntroductionComponent D (T.parent x) a := by
    rw [IntroductionComponent,ha]
    exact .step hx (.refl _)
  have hpb : IntroductionComponent D (T.parent x) b := by
    rw [IntroductionComponent,hb]
    exact .refl _
  have hxa : IntroductionComponent D x a := by
    rw [IntroductionComponent,ha]
    exact .refl _
  have hxb : ¬ IntroductionComponent D x b := by
    intro h
    have hle := h.val_le
    rw [hb] at hle
    have hlt := T.parent_lt x hx
    omega
  obtain ⟨u,v,hpu,hpv,hu,hv,he⟩ := crossing_inside (hc _ _ _ hpa hpb) hxa hxb
  have hav := component_exit_adhesion D hu hv he
  have hiv := introduction_ancestor D hav.1
  have heq : introductionNode D v=T.parent x :=
    TreeAncestry.antisymm (hiv.parent_of_ne hav.2) hpv
  exact ⟨v,heq,hav⟩

/-- Packaging supplied local marginal decompositions now derives the connector
law from genuine connected-component paths instead of taking it as an oracle. -/
def NestedInput.ofConnectedComponents (D : Decomposition G T) (ht : 0<t)
    (vertices : Fin t → Nat)
    (names : ∀ x, Fin (vertices x) ≃ {v : Fin n // introductionNode D v=x})
    (hm : ∀ x, ∃ v, introductionNode D v=x)
    (hc : ConnectedIntroductionComponents D)
    (nodes : Fin t → Nat) (localTree : ∀ x, RootedTree (nodes x))
    (localDecomp : ∀ x, Decomposition (marginalGraph D x (names x)) (localTree x)) :
    NestedInput D where
  outerNonempty := ht
  vertices := vertices
  names := names
  marginNonempty := hm
  nodes := nodes
  localTree := localTree
  localDecomp := localDecomp
  connector := sane_parent_margin_connector D hm hc

#print axioms component_exit_adhesion
#print axioms sane_parent_margin_connector
end StackSorting.GraphWidth.Nested
