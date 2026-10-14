import HypergraphBagPath

namespace FiniteFlow.Hypergraph.BagPath
variable {V E : Type*} [DecidableEq V] {A B : Finset V} {w : Nat}

def recast (D : BagPath A w) (h : A = B) : BagPath B w where
  last := D.last
  bag := D.bag
  inside := by intro i hi x hx; rw [← h]; exact D.inside i hi hx
  bounded := D.bounded
  vertex := by intro x hx; rw [← h] at hx; exact D.vertex x hx
  interval := D.interval

omit [DecidableEq V] in
theorem recast_covers (D : BagPath A w) (h : A = B) {inc : V → E → Prop}
    (hc : D.Covers inc) : (D.recast h).Covers inc := by
  intro e
  obtain ⟨i,hi,he⟩ := hc e
  refine ⟨i,hi,?_⟩
  intro x hx hxe
  rw [← h] at hx
  exact he x hx hxe

def restrictSubset (D : BagPath A w) (part : Finset V) (h : part ⊆ A) : BagPath part w :=
  (D.restrict part).recast (Finset.inter_eq_right.mpr h)

@[simp] theorem restrictSubset_bag (D : BagPath A w) (part : Finset V) (h : part ⊆ A) (i : Nat) :
    (D.restrictSubset part h).bag i = D.bag i ∩ part := rfl

@[simp] theorem restrictSubset_last (D : BagPath A w) (part : Finset V) (h : part ⊆ A) :
    (D.restrictSubset part h).last = D.last := rfl

theorem restrictSubset_covers (D : BagPath A w) (part : Finset V) (h : part ⊆ A)
    {inc : V → E → Prop} (hc : D.Covers inc) : (D.restrictSubset part h).Covers inc :=
  (D.restrict part).recast_covers _ (D.restrict_covers part hc)

end FiniteFlow.Hypergraph.BagPath
