import GuidanceDisjointUnion
import ForestDisjointUnion

namespace StackSorting.GuidedPathwidth
universe u
variable {V : Type u} {G : SimpleGraph V} {P Q : Set V} {c : Nat}

namespace Decomposition
/-- Combine two disjoint vertex regions with no graph edge between them.
The index forest is their literal disjoint union and every bag is retained. -/
noncomputable def disjointUnion (D : Decomposition G P) (E : Decomposition G Q)
    (hPQ : Disjoint P Q) (hsep : ∀ x ∈ P, ∀ y ∈ Q, ¬ G.Adj x y) :
    Decomposition G (P ∪ Q) where
  Node := D.Node ⊕ E.Node
  finiteNode := inferInstance
  forest := D.forest ⊕g E.forest
  acyclic := sumForest_acyclic D.acyclic E.acyclic
  bag := Sum.elim D.bag E.bag
  inside := by
    intro a x hx
    cases a with
    | inl a => exact Or.inl (D.inside a hx)
    | inr a => exact Or.inr (E.inside a hx)
  vertex := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨a,ha⟩ := D.vertex x hx
      exact ⟨.inl a,ha⟩
    · obtain ⟨a,ha⟩ := E.vertex x hx
      exact ⟨.inr a,ha⟩
  edge := by
    intro x y hxy hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · obtain ⟨a,ha,hb⟩ := D.edge hxy hx hy
      exact ⟨.inl a,ha,hb⟩
    · exact (hsep x hx y hy hxy).elim
    · exact (hsep y hy x hx hxy.symm).elim
    · obtain ⟨a,ha,hb⟩ := E.edge hxy hx hy
      exact ⟨.inr a,ha,hb⟩
  running := by
    intro x a b ha hb
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have h := D.running x a b ha hb
        refine ⟨ha,hb,?_⟩
        exact h.2.2.map Sum.inl (by intro a b hab; exact hab) (by intro a ha; exact ha)
      | inr b => exact (Set.disjoint_left.mp hPQ (D.inside a ha) (E.inside b hb)).elim
    | inr a =>
      cases b with
      | inl b => exact (Set.disjoint_left.mp hPQ (D.inside b hb) (E.inside a ha)).elim
      | inr b =>
        have h := E.running x a b ha hb
        refine ⟨ha,hb,?_⟩
        exact h.2.2.map Sum.inr (by intro a b hab; exact hab) (by intro a ha; exact ha)
end Decomposition

namespace GuidedDecomposition
noncomputable def disjointUnion (D : GuidedDecomposition G P c)
    (E : GuidedDecomposition G Q c) (hPQ : Disjoint P Q)
    (hsep : ∀ x ∈ P, ∀ y ∈ Q, ¬ G.Adj x y) :
    GuidedDecomposition G (P ∪ Q) c where
  decomposition := D.decomposition.disjointUnion E.decomposition hPQ hsep
  guides := D.guides.disjointUnion E.guides hPQ
  captured := by
    intro a
    cases a with
    | inl a => exact System.disjointUnion_captures_left D.guides E.guides hPQ (D.captured a)
    | inr a => exact System.disjointUnion_captures_right D.guides E.guides hPQ (E.captured a)
end GuidedDecomposition

#print axioms GuidedDecomposition.disjointUnion
end StackSorting.GuidedPathwidth
