import RankedForestParent
import Mathlib.Data.Finset.Card

namespace StackSorting.SameVertexForest

/-- A finite strict forest order before any numerical rank or parent is
constructed. The clauses are first-order properties of its binary relation. -/
structure StrictForestOrder (n : Nat) where
  rel : Fin n → Fin n → Prop
  irrefl : ∀ v, ¬ rel v v
  trans : ∀ {u v w}, rel u v → rel v w → rel u w
  predecessors : ∀ {u v w}, rel u w → rel v w → rel u v ∨ u=v ∨ rel v u

namespace StrictForestOrder
variable {n : Nat} (O : StrictForestOrder n)

noncomputable def predecessorSet (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun u => O.rel u v)

@[simp] theorem mem_predecessorSet (u v : Fin n) :
    u ∈ O.predecessorSet v ↔ O.rel u v := by
  classical
  simp [predecessorSet]

/-- Counting strict predecessors supplies the well-founded rank; no rank
witness is assumed in the admissibility relation. -/
theorem predecessor_card_lt {u v : Fin n} (h : O.rel u v) :
    (O.predecessorSet u).card < (O.predecessorSet v).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro w hw
    exact (O.mem_predecessorSet w v).mpr (O.trans ((O.mem_predecessorSet w u).mp hw) h)
  · intro he
    have hu : u ∈ O.predecessorSet v := (O.mem_predecessorSet u v).mpr h
    rw [←he] at hu
    exact O.irrefl u ((O.mem_predecessorSet u u).mp hu)

noncomputable def ranked : RankedOrder n where
  rel := O.rel
  irrefl := O.irrefl
  trans := O.trans
  predecessors := O.predecessors
  rank v := (O.predecessorSet v).card
  increasing h := O.predecessor_card_lt h

/-- The constructed parent forest has exactly the supplied strict order as
its proper ancestry, without a supplied parent map. -/
theorem ranked_ancestor_iff (u v : Fin n) :
    Ancestor O.ranked.forest u v ↔ O.rel u v ∨ u=v := O.ranked.ancestor_iff

theorem ranked_parent_iff_cover {u v : Fin n} (hne : u≠v) :
    O.ranked.parent v=u ↔ O.rel u v ∧ ¬ ∃ w, O.rel u w ∧ O.rel w v :=
  O.ranked.parent_eq_iff_cover hne

#print axioms predecessor_card_lt
#print axioms ranked_ancestor_iff
#print axioms ranked_parent_iff_cover
end StrictForestOrder
end StackSorting.SameVertexForest
