import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Lean.Elab.Tactic.Omega

/-! Nonempty finite bag paths. Bounds count vertices, so width is one less.
Every construction retains the original vertex names and hyperedge identifiers.
Empty regions still have a real empty bag, needed when an entire cutedge is added.
-/
namespace FiniteFlow.Hypergraph

variable {V E : Type*} [DecidableEq V]

structure BagPath (region : Finset V) (bound : Nat) where
  last : Nat
  bag : Nat → Finset V
  inside : ∀ i, i ≤ last → bag i ⊆ region
  bounded : ∀ i, i ≤ last → (bag i).card ≤ bound
  vertex : ∀ x ∈ region, ∃ i, i ≤ last ∧ x ∈ bag i
  interval : ∀ i j k, i ≤ j → j ≤ k → k ≤ last →
    ∀ x, x ∈ bag i → x ∈ bag k → x ∈ bag j

namespace BagPath
variable {region : Finset V} {bound : Nat}

def Covers (D : BagPath region bound) (inc : V → E → Prop) : Prop :=
  ∀ e, ∃ i, i ≤ D.last ∧ ∀ x ∈ region, inc x e → x ∈ D.bag i

def single (region : Finset V) : BagPath region region.card where
  last := 0
  bag := fun _ => region
  inside := fun _ _ => Finset.Subset.refl _
  bounded := fun _ _ => le_rfl
  vertex := fun _x hx => ⟨0, le_rfl, hx⟩
  interval := fun _ _ _ _ _ _ _ h _ => h

omit [DecidableEq V] in
theorem single_covers (region : Finset V) (inc : V → E → Prop) :
    (single region).Covers inc := fun _ => ⟨0, le_rfl, fun _ hx _ => hx⟩

def weaken (D : BagPath region bound) {n : Nat} (h : bound ≤ n) : BagPath region n where
  last := D.last
  bag := D.bag
  inside := D.inside
  bounded := fun i hi => (D.bounded i hi).trans h
  vertex := D.vertex
  interval := D.interval

def restrict (D : BagPath region bound) (part : Finset V) :
    BagPath (region ∩ part) bound where
  last := D.last
  bag := fun i => D.bag i ∩ part
  inside := by
    intro i hi x hx
    exact Finset.mem_inter.mpr ⟨D.inside i hi (Finset.mem_inter.mp hx).1,
      (Finset.mem_inter.mp hx).2⟩
  bounded := fun i hi => (Finset.card_le_card Finset.inter_subset_left).trans (D.bounded i hi)
  vertex := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := D.vertex x (Finset.mem_inter.mp hx).1
    exact ⟨i, hi, Finset.mem_inter.mpr ⟨hxi, (Finset.mem_inter.mp hx).2⟩⟩
  interval := by
    intro i j k hij hjk hk x hxi hxk
    exact Finset.mem_inter.mpr ⟨D.interval i j k hij hjk hk x
      (Finset.mem_inter.mp hxi).1 (Finset.mem_inter.mp hxk).1,
      (Finset.mem_inter.mp hxi).2⟩

theorem restrict_covers (D : BagPath region bound) (part : Finset V)
    {inc : V → E → Prop} (h : D.Covers inc) : (D.restrict part).Covers inc := by
  intro e
  obtain ⟨i, hi, he⟩ := h e
  exact ⟨i, hi, fun x hx hxe => Finset.mem_inter.mpr
    ⟨he x (Finset.mem_inter.mp hx).1 hxe, (Finset.mem_inter.mp hx).2⟩⟩

/-- Add the same finite separator to every actual bag. -/
def augment (D : BagPath region bound) (extra : Finset V) :
    BagPath (region ∪ extra) (bound + extra.card) where
  last := D.last
  bag := fun i => D.bag i ∪ extra
  inside := by
    intro i hi x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (D.inside i hi hx)
    · exact Finset.mem_union_right _ hx
  bounded := fun i hi => (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (D.bounded i hi) _)
  vertex := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, hxi⟩ := D.vertex x hx
      exact ⟨i, hi, Finset.mem_union_left _ hxi⟩
    · exact ⟨0, Nat.zero_le _, Finset.mem_union_right _ hx⟩
  interval := by
    intro i j k hij hjk hk x hxi hxk
    by_cases hx : x ∈ extra
    · exact Finset.mem_union_right _ hx
    · exact Finset.mem_union_left _ (D.interval i j k hij hjk hk x
        ((Finset.mem_union.mp hxi).resolve_right hx)
        ((Finset.mem_union.mp hxk).resolve_right hx))

theorem augment_covers (D : BagPath region bound) (extra : Finset V)
    {inc : V → E → Prop} (h : D.Covers inc) : (D.augment extra).Covers inc := by
  intro e
  obtain ⟨i, hi, he⟩ := h e
  refine ⟨i, hi, ?_⟩
  intro x hx hxe
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (he x hx hxe)
  · exact Finset.mem_union_right _ hx

/-- The quantitative appendix surgery retains the explicit rank premise. -/
def augmentThin (k : Nat) (D : BagPath region (k+1)) (edge : Finset V)
    (rank : edge.card ≤ k+1) : BagPath (region ∪ edge) (2*k+2) :=
  (D.augment edge).weaken (by omega)

theorem augmentThin_covers (k : Nat) (D : BagPath region (k+1))
    (edge : Finset V) (rank : edge.card ≤ k+1)
    {inc : V → E → Prop} (h : D.Covers inc) : (D.augmentThin k edge rank).Covers inc :=
  D.augment_covers edge h

end BagPath
end FiniteFlow.Hypergraph
