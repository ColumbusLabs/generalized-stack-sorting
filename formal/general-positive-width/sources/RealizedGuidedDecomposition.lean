import DecompositionForests
import GuidanceForestRealization

namespace StackSorting.GuidedPathwidth
universe u
variable {V : Type u} {G : SimpleGraph V} {P : Set V} {c : Nat}

/-- A color is an actual original-edge forest with selected vertices and roots.
Every selected vertex belongs to exactly one rooted component. -/
structure RootedColor (G : SimpleGraph V) (P : Set V) where
  graph : SimpleGraph V
  subgraph : graph ≤ G
  acyclic : graph.IsAcyclic
  selected : Set V
  roots : Set V
  selectedInside : selected ⊆ P
  rootSelected : roots ⊆ selected
  edgeSelected : ∀ {x y}, graph.Adj x y → x ∈ selected ∧ y ∈ selected
  uniqueRoot : ∀ x ∈ selected, ∃! r, r ∈ roots ∧ graph.Reachable x r

def ForestCaptures (C : Fin c → RootedColor G P) (B : Set V) : Prop :=
  B.Nonempty → ∃ x, ∀ r ∈ B, ∃ i,
    r ∈ (C i).roots ∧ x ∈ (C i).selected ∧ r ∈ (C i).selected ∧
      (C i).graph.Reachable x r

structure ForestGuidedDecomposition (G : SimpleGraph V) (P : Set V) (c : Nat) where
  decomposition : Decomposition G P
  colors : Fin c → RootedColor G P
  captured : ∀ a, ForestCaptures colors (decomposition.bag a)

/-- A real forest palette bounds every captured bag by its number of colors. -/
theorem forestCapture_card_le (C : Fin c → RootedColor G P) {B : Set V}
    (h : ForestCaptures C B) : Nat.card B ≤ c := by
  classical
  by_cases hb : B.Nonempty
  · obtain ⟨x,hx⟩ := h hb
    let f : B → Fin c := fun r => Classical.choose (hx r r.property)
    have hf : Function.Injective f := by
      intro r s he
      have hr := Classical.choose_spec (hx r r.property)
      have hs := Classical.choose_spec (hx s s.property)
      change r.val ∈ (C (f r)).roots ∧ x ∈ (C (f r)).selected ∧
        r.val ∈ (C (f r)).selected ∧ (C (f r)).graph.Reachable x r.val at hr
      change s.val ∈ (C (f s)).roots ∧ x ∈ (C (f s)).selected ∧
        s.val ∈ (C (f s)).selected ∧ (C (f s)).graph.Reachable x s.val at hs
      rw [← he] at hs
      obtain ⟨q,_,hu⟩ := (C (f r)).uniqueRoot x hr.2.1
      exact Subtype.ext ((hu r.val ⟨hr.1,hr.2.2.2⟩).trans
        (hu s.val ⟨hs.1,hs.2.2.2⟩).symm)
    let : Fintype B := Fintype.ofInjective f hf
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using Fintype.card_le_of_injective f hf
  · have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hb
    subst B
    simp

theorem ForestGuidedDecomposition.bag_card_le (D : ForestGuidedDecomposition G P c)
    (a : D.decomposition.Node) : Nat.card (D.decomposition.bag a) ≤ c :=
  forestCapture_card_le D.colors (D.captured a)

namespace Color
noncomputable def realize (C : Color G P) : RootedColor G P := by
  let F := Classical.choice C.exists_forest
  exact {
    graph := F.graph
    subgraph := F.subgraph
    acyclic := F.acyclic
    selected := {x | ∃ r, x ∈ C.support r}
    roots := {r | r ∈ C.support r}
    selectedInside := by rintro x ⟨r,hr⟩; exact C.inside r hr
    rootSelected := fun r hr => ⟨r,hr⟩
    edgeSelected := F.endpoints
    uniqueRoot := fun x hx => F.unique_root hx }

theorem realize_rootRelation (C : Color G P) (x r : V) :
    (r ∈ C.realize.roots ∧ x ∈ C.realize.selected ∧ r ∈ C.realize.selected ∧
      C.realize.graph.Reachable x r) ↔ x ∈ C.support r := by
  let F := Classical.choice C.exists_forest
  constructor
  · intro h
    exact (F.exactRoots x r).mp ⟨h.1,h.2.2.2⟩
  · intro hx
    obtain ⟨hr,hreach⟩ := (F.exactRoots x r).mpr hx
    exact ⟨hr,⟨r,hx⟩,⟨r,hr⟩,hreach⟩
end Color

/-- Realize every constructed guide by an actual acyclic original-edge forest.
The bags and capture witnesses are unchanged and the palette has exactly c
entries, including zero for an empty allowed graph. -/
noncomputable def GuidedDecomposition.realize (D : GuidedDecomposition G P c) :
    ForestGuidedDecomposition G P c where
  decomposition := D.decomposition
  colors := fun i => (D.guides i).realize
  captured := by
    intro a hb
    obtain ⟨x,hx⟩ := D.captured a hb
    refine ⟨x,?_⟩
    intro r hr
    obtain ⟨i,hi⟩ := hx r hr
    exact ⟨i,((D.guides i).realize_rootRelation x r).mpr hi⟩

#print axioms GuidedDecomposition.realize
end StackSorting.GuidedPathwidth
