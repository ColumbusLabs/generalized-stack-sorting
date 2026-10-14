import ConnectedFiberDecomposition
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Lemmas

namespace StackSorting.GraphWidth
open FinitePort

namespace TreeAncestry

theorem antisymm {t} {T : RootedTree t} {u v}
    (h : Ancestor T u v) (k : Ancestor T v u) : u = v :=
  Fin.ext (Nat.le_antisymm h.val_le k.val_le)

theorem comparable {t} {T : RootedTree t} {u v w}
    (h : Ancestor T u w) (k : Ancestor T v w) :
    Ancestor T u v ∨ Ancestor T v u := by
  induction h with
  | refl => exact Or.inr k
  | @step w hw hu ih =>
    by_cases hv : v = w
    · subst v; exact Or.inl (.step hw hu)
    · exact ih (k.parent_of_ne hv)

/-- A connected set's minimum topological index is above all its vertices.
Only actual parent-tree edges and the connected occurrence walk are used. -/
theorem ancestor_of_walk_minimum {t} {T : RootedTree t} {P : Fin t → Prop}
    {a x y : Fin t} (h : Walk (TreeAdj T) P x y)
    (hm : ∀ z, P z → a.val ≤ z.val) (ha : Ancestor T a x) : Ancestor T a y := by
  induction h with
  | refl => exact ha
  | @step x z y hx hnext htail ih =>
    apply ih
    rcases hnext with ⟨hn, he⟩ | ⟨hn, he⟩
    · have hxa : a ≠ x := by
        intro eq
        have hlow := hm z htail.start
        have hlt := T.parent_lt x hn
        rw [he] at hlt
        subst a
        omega
      simpa only [he] using ha.parent_of_ne hxa
    · exact Ancestor.step hn (he.symm ▸ ha)

/-- Every walk entering a rooted subtree passes through its root. -/
theorem subtree_entry {t} {T : RootedTree t} {P : Fin t → Prop}
    {a x y : Fin t} (h : Walk (TreeAdj T) P x y)
    (hx : ¬ Ancestor T a x) (hy : Ancestor T a y) : P a := by
  induction h with
  | refl => exact False.elim (hx hy)
  | @step x z y hpx hnext htail ih =>
    by_cases hz : Ancestor T a z
    · rcases hnext with ⟨hn, he⟩ | ⟨hn, he⟩
      · exact False.elim (hx (Ancestor.step hn (he.symm ▸ hz)))
      · by_cases heq : a = z
        · exact heq.symm ▸ htail.start
        · exact False.elim (hx (he ▸ hz.parent_of_ne heq))
    · exact ih hz hy

/-- Running intersection contains every intermediate node on a root branch. -/
theorem walk_convex {t} {T : RootedTree t} {P : Fin t → Prop}
    {x a y : Fin t} (h : Walk (TreeAdj T) P x y)
    (hxa : Ancestor T x a) (hay : Ancestor T a y) : P a := by
  by_cases hx : x = a
  · exact hx ▸ h.start
  · apply subtree_entry h ?_ hay
    intro hax
    exact hx (antisymm hxa hax)

end TreeAncestry

/-- The introduction node is derived from an actual decomposition. Its
ancestor property is a theorem below, not an extra decomposition premise. -/
noncomputable def introductionNode {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (v : Fin n) : Fin t := by
  classical
  exact Classical.choose (Set.exists_min_image {i | v ∈ D.bag i} Fin.val
    (Set.toFinite _) (D.vertex v))

theorem introduction_spec {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (v : Fin n) :
    v ∈ D.bag (introductionNode D v) ∧
      ∀ i, v ∈ D.bag i → (introductionNode D v).val ≤ i.val := by
  classical
  exact Classical.choose_spec (Set.exists_min_image {i | v ∈ D.bag i} Fin.val
    (Set.toFinite _) (D.vertex v))

theorem introduction_ancestor {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {v : Fin n} {i : Fin t} (hi : v ∈ D.bag i) :
    Ancestor T (introductionNode D v) i := by
  have h := introduction_spec D v
  exact TreeAncestry.ancestor_of_walk_minimum (D.running h.1 hi) h.2 (.refl _)

theorem edge_introductions_comparable {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {u v : Fin n} (huv : G.Adj u v) :
    Ancestor T (introductionNode D u) (introductionNode D v) ∨
      Ancestor T (introductionNode D v) (introductionNode D u) := by
  obtain ⟨i, hu, hv⟩ := D.edge huv
  exact TreeAncestry.comparable (introduction_ancestor D hu) (introduction_ancestor D hv)

/-- The exact branch-convexity fact needed for frontier-bag containment. -/
theorem frontier_mem_introduction_bag {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {u v w : Fin n}
    (huv : Ancestor T (introductionNode D u) (introductionNode D v))
    (hvw : Ancestor T (introductionNode D v) (introductionNode D w))
    (huw : G.Adj u w) : u ∈ D.bag (introductionNode D v) := by
  obtain ⟨i, hu, hw⟩ := D.edge huw
  apply TreeAncestry.walk_convex (D.running (introduction_spec D u).1 hu) huv
  exact hvw.trans (introduction_ancestor D hw)

#print axioms introduction_ancestor
#print axioms frontier_mem_introduction_bag
end StackSorting.GraphWidth
