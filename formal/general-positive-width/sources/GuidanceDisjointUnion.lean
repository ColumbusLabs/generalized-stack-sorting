import DecompositionForests

namespace StackSorting.GuidedPathwidth
universe u
variable {V : Type u} {G : SimpleGraph V} {P Q : Set V} {c : Nat}

namespace Color
/-- Disjoint regions reuse the same color without identifying any roots. -/
def disjointUnion (C : Color G P) (D : Color G Q) (hPQ : Disjoint P Q) :
    Color G (P ∪ Q) where
  support := fun r => C.support r ∪ D.support r
  inside := by
    intro r x hx
    rcases hx with hx | hx
    · exact Or.inl (C.inside r hx)
    · exact Or.inr (D.inside r hx)
  reaches := by
    intro r x hx
    rcases hx with hx | hx
    · exact (C.reaches r x hx).mono Set.subset_union_left
    · exact (D.reaches r x hx).mono Set.subset_union_right
  unique := by
    intro r s x hr hs
    rcases hr with hr | hr <;> rcases hs with hs | hs
    · exact C.unique r s x hr hs
    · exact False.elim (Set.disjoint_left.mp hPQ (C.inside r hr) (D.inside s hs))
    · exact False.elim (Set.disjoint_left.mp hPQ (C.inside s hs) (D.inside r hr))
    · exact D.unique r s x hr hs
end Color

namespace System
noncomputable def disjointUnion (C : System G P c) (D : System G Q c)
    (hPQ : Disjoint P Q) : System G (P ∪ Q) c :=
  fun i => (C i).disjointUnion (D i) hPQ

theorem disjointUnion_captures_left (C : System G P c) (D : System G Q c)
    (hPQ : Disjoint P Q) {B : Set V} (h : Captures G C B) :
    Captures G (C.disjointUnion D hPQ) B := by
  intro hb
  obtain ⟨x,hx⟩ := h hb
  refine ⟨x,?_⟩
  intro r hr
  obtain ⟨i,hi⟩ := hx r hr
  exact ⟨i,Or.inl hi⟩

theorem disjointUnion_captures_right (C : System G P c) (D : System G Q c)
    (hPQ : Disjoint P Q) {B : Set V} (h : Captures G D B) :
    Captures G (C.disjointUnion D hPQ) B := by
  intro hb
  obtain ⟨x,hx⟩ := h hb
  refine ⟨x,?_⟩
  intro r hr
  obtain ⟨i,hi⟩ := hx r hr
  exact ⟨i,Or.inr hi⟩
end System
end StackSorting.GuidedPathwidth
