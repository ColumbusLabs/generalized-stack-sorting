import HypergraphBagPath

namespace FiniteFlow.Hypergraph.BagPath
variable {V E : Type*} {A : Finset V} {w : Nat}

/-- Reverse the actual bag sequence, preserving every region, bag bound and
full-hyperedge covering witness. This supplies right-exterior surgery from left. -/
def reverse (D : BagPath A w) : BagPath A w where
  last := D.last
  bag := fun i => D.bag (D.last-i)
  inside := fun i _ => D.inside _ (Nat.sub_le _ _)
  bounded := fun i _ => D.bounded _ (Nat.sub_le _ _)
  vertex := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := D.vertex x hx
    refine ⟨D.last-i,Nat.sub_le _ _,?_⟩
    simpa only [show D.last-(D.last-i)=i by omega] using hxi
  interval := by
    intro i j k hij hjk hk x hxi hxk
    exact D.interval (D.last-k) (D.last-j) (D.last-i)
      (by omega) (by omega) (Nat.sub_le _ _) x hxk hxi

@[simp] theorem reverse_first (D : BagPath A w) : D.reverse.bag 0 = D.bag D.last := by
  simp [reverse]

@[simp] theorem reverse_last (D : BagPath A w) : D.reverse.bag D.reverse.last = D.bag 0 := by
  simp [reverse]

theorem reverse_covers (D : BagPath A w) {inc : V → E → Prop} (hc : D.Covers inc) :
    D.reverse.Covers inc := by
  intro e
  obtain ⟨i,hi,he⟩ := hc e
  refine ⟨D.last-i,Nat.sub_le _ _,?_⟩
  intro x hx hxe
  change x ∈ D.bag (D.last-(D.last-i))
  rw [show D.last-(D.last-i)=i by omega]
  exact he x hx hxe

end FiniteFlow.Hypergraph.BagPath
