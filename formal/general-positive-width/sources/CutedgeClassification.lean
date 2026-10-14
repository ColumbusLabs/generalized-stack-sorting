import CutedgeComponentSeparation

namespace FiniteFlow.Hypergraph

inductive CutBoundary (E : Type*)
  | source
  | cut (e : E)
  | sink
  deriving DecidableEq

variable {V E : Type*} {inc : V → E → Prop} {s t : V}

def BoundaryValid : CutBoundary E → Prop
  | .source => True
  | .cut e => Cutedge inc s t e
  | .sink => True

def ComponentTouches (x : V) : CutBoundary E → Prop
  | .source => SameCutedgeComponent inc s t x s
  | .cut e => ∃ y, inc y e ∧ SameCutedgeComponent inc s t x y
  | .sink => SameCutedgeComponent inc s t x t

def BoundaryBefore [DecidableEq E] (p : Path inc s t) :
    CutBoundary E → CutBoundary E → Prop
  | .source, .cut _ => True
  | .source, .sink => True
  | .cut e, .cut f => p.walk.edges.idxOf e < p.walk.edges.idxOf f
  | .cut _, .sink => True
  | _, _ => False

/-- Consecutive among the valid boundaries, in their canonical path order. -/
def BoundaryAdjacent [DecidableEq E] (p : Path inc s t) (a b : CutBoundary E) : Prop :=
  BoundaryBefore p a b ∧
    ¬ ∃ c, BoundaryValid (inc := inc) (s := s) (t := t) c ∧
      BoundaryBefore p a c ∧ BoundaryBefore p c b

/-- Boundary ordering is independent of the selected actual path. -/
theorem boundaryBefore_iff [DecidableEq E] (p q : Path inc s t)
    {a b : CutBoundary E} (ha : BoundaryValid (inc := inc) (s := s) (t := t) a)
    (hb : BoundaryValid (inc := inc) (s := s) (t := t) b) :
    BoundaryBefore p a b ↔ BoundaryBefore q a b := by
  cases a <;> cases b <;> simp only [BoundaryBefore, BoundaryValid] at *
  exact cutedge_idxOf_lt_iff p q ha hb

theorem boundary_trichotomy [DecidableEq E] (p : Path inc s t)
    {a b : CutBoundary E} (ha : BoundaryValid (inc := inc) (s := s) (t := t) a)
    (hb : BoundaryValid (inc := inc) (s := s) (t := t) b) :
    a = b ∨ BoundaryBefore p a b ∨ BoundaryBefore p b a := by
  cases a <;> cases b <;> simp_all only [BoundaryValid, BoundaryBefore, CutBoundary.cut.injEq,
    reduceCtorEq, or_true, or_false]
  rename_i e f
  rcases lt_trichotomy (p.walk.edges.idxOf e) (p.walk.edges.idxOf f) with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl ((List.idxOf_inj (ha p)).mp h)
  · exact Or.inr (Or.inr h)

/-- No component touches boundaries on opposite sides of a third valid boundary. -/
theorem component_boundaries_no_gap [DecidableEq E] (p : Path inc s t) (x : V)
    {a b c : CutBoundary E}
    (ha : BoundaryValid (inc := inc) (s := s) (t := t) a)
    (hb : BoundaryValid (inc := inc) (s := s) (t := t) b)
    (hc : BoundaryValid (inc := inc) (s := s) (t := t) c)
    (hab : BoundaryBefore p a b) (hbc : BoundaryBefore p b c)
    (hxa : ComponentTouches (inc := inc) (s := s) (t := t) x a)
    (hxc : ComponentTouches (inc := inc) (s := s) (t := t) x c) : False := by
  cases a <;> cases b <;> cases c <;>
    simp only [BoundaryBefore, BoundaryValid, ComponentTouches] at *
  · obtain ⟨y, hy, hxy⟩ := hxc
    exact source_component_no_earlier_cutedge p hb hc hbc hy
      (sameCutedgeComponent_trans inc s t (sameCutedgeComponent_symm inc s t hxa) hxy)
  · exact terminal_component_has_no_cutedge
      (sameCutedgeComponent_trans inc s t (sameCutedgeComponent_symm inc s t hxa) hxc) hb
  · obtain ⟨y, hy, hxy⟩ := hxa
    obtain ⟨z, hz, hxz⟩ := hxc
    exact component_no_intermediate_cutedge p ha hb hc hab hbc hy hz
      (sameCutedgeComponent_trans inc s t (sameCutedgeComponent_symm inc s t hxy) hxz)
  · obtain ⟨y, hy, hxy⟩ := hxa
    exact sink_component_no_later_cutedge p ha hb hab hy
      (sameCutedgeComponent_trans inc s t (sameCutedgeComponent_symm inc s t hxy) hxc)

theorem component_third_boundary_eq [DecidableEq E] (p : Path inc s t) (x : V)
    {a b c : CutBoundary E}
    (ha : BoundaryValid (inc := inc) (s := s) (t := t) a)
    (hb : BoundaryValid (inc := inc) (s := s) (t := t) b)
    (hc : BoundaryValid (inc := inc) (s := s) (t := t) c)
    (hab : BoundaryBefore p a b)
    (hxa : ComponentTouches (inc := inc) (s := s) (t := t) x a)
    (hxb : ComponentTouches (inc := inc) (s := s) (t := t) x b)
    (hxc : ComponentTouches (inc := inc) (s := s) (t := t) x c) : c = a ∨ c = b := by
  rcases boundary_trichotomy p ha hc with h | hac | hca
  · exact Or.inl h.symm
  · rcases boundary_trichotomy p hb hc with h | hbc | hcb
    · exact Or.inr h.symm
    · exact (component_boundaries_no_gap p x ha hb hc hab hbc hxa hxc).elim
    · exact (component_boundaries_no_gap p x ha hc hb hac hcb hxa hxb).elim
  · exact (component_boundaries_no_gap p x hc ha hb hca hab hxc hxb).elim

/-- Exact cutedge-component classification (Bojanczyk--Pilipczuk Lemma 5.4).
The source and sink boundaries remain distinct labels even in the empty trace
case. An appendix touches precisely one actual cutedge. A bridge touches
precisely two consecutive valid boundaries in the canonical cutedge order. -/
theorem cutedge_component_classification [DecidableEq E]
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t) (x : V) :
    (∃ e, Cutedge inc s t e ∧
      ∀ b, BoundaryValid (inc := inc) (s := s) (t := t) b →
        (ComponentTouches (inc := inc) (s := s) (t := t) x b ↔ b = .cut e)) ∨
    (∃ a b, BoundaryValid (inc := inc) (s := s) (t := t) a ∧
      BoundaryValid (inc := inc) (s := s) (t := t) b ∧ BoundaryAdjacent p a b ∧
      ∀ c, BoundaryValid (inc := inc) (s := s) (t := t) c →
        (ComponentTouches (inc := inc) (s := s) (t := t) x c ↔ c = a ∨ c = b)) := by
  classical
  have hex : ∃ a, BoundaryValid (inc := inc) (s := s) (t := t) a ∧
      ComponentTouches (inc := inc) (s := s) (t := t) x a := by
    rcases component_meets_cutedge_or_both_terminals connected x with
      ⟨e, y, he, hy, hxy⟩ | ⟨hs, _⟩
    · exact ⟨.cut e, he, y, hy, hxy⟩
    · exact ⟨.source, trivial, hs⟩
  obtain ⟨a, ha, hxa⟩ := hex
  by_cases hone : ∀ b, BoundaryValid (inc := inc) (s := s) (t := t) b →
      ComponentTouches (inc := inc) (s := s) (t := t) x b → b = a
  · have hacut : ∃ e, Cutedge inc s t e ∧ a = .cut e := by
      rcases component_meets_cutedge_or_both_terminals connected x with
        ⟨e, y, he, hy, hxy⟩ | ⟨hs, ht⟩
      · exact ⟨e, he, (hone (.cut e) he ⟨y, hy, hxy⟩).symm⟩
      · have hs' := hone .source trivial hs
        have ht' := hone .sink trivial ht
        have hbad : (CutBoundary.source : CutBoundary E) = .sink := hs'.trans ht'.symm
        cases hbad
    obtain ⟨e, he, rfl⟩ := hacut
    refine Or.inl ⟨e, he, ?_⟩
    intro b hb
    exact ⟨hone b hb, fun h => h.symm ▸ hxa⟩
  · push Not at hone
    obtain ⟨b, hb, hxb, hne⟩ := hone
    have hpair : ∀ a b, BoundaryValid (inc := inc) (s := s) (t := t) a →
        BoundaryValid (inc := inc) (s := s) (t := t) b → BoundaryBefore p a b →
        ComponentTouches (inc := inc) (s := s) (t := t) x a →
        ComponentTouches (inc := inc) (s := s) (t := t) x b →
        BoundaryAdjacent p a b ∧
        ∀ c, BoundaryValid (inc := inc) (s := s) (t := t) c →
          (ComponentTouches (inc := inc) (s := s) (t := t) x c ↔ c = a ∨ c = b) := by
      intro a b ha hb hab hxa hxb
      refine ⟨⟨hab, ?_⟩, ?_⟩
      · rintro ⟨c, hc, hac, hcb⟩
        exact component_boundaries_no_gap p x ha hc hb hac hcb hxa hxb
      · intro c hc
        constructor
        · exact component_third_boundary_eq p x ha hb hc hab hxa hxb
        · rintro (rfl | rfl)
          · exact hxa
          · exact hxb
    rcases boundary_trichotomy p ha hb with h | hab | hba
    · exact (hne h.symm).elim
    · obtain ⟨hadj, hall⟩ := hpair a b ha hb hab hxa hxb
      exact Or.inr ⟨a, b, ha, hb, hadj, hall⟩
    · obtain ⟨hadj, hall⟩ := hpair b a hb ha hba hxb hxa
      exact Or.inr ⟨b, a, hb, ha, hadj, hall⟩

end FiniteFlow.Hypergraph
