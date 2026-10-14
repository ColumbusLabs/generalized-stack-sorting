import PrefixConePartition

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}

noncomputable def coneNodes (O : RankedOrder n) (r : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (Cone O r)

@[simp] theorem mem_coneNodes (O : RankedOrder n) (r v : Fin n) :
    v ∈ coneNodes O r ↔ Cone O r v := by
  classical
  simp [coneNodes]

theorem coneNodes_card_lt (O : RankedOrder n) {r z : Fin n} (hz : O.rel r z) :
    (coneNodes O z).card < (coneNodes O r).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro v hv
    exact (mem_coneNodes O r v).mpr (cone_trans O (Or.inl hz) ((mem_coneNodes O z v).mp hv))
  · intro he
    have hr : r ∈ coneNodes O r := (mem_coneNodes O r r).mpr (cone_refl O r)
    rw [← he] at hr
    rcases (mem_coneNodes O z r).mp hr with hr | hr
    · exact O.irrefl r (O.trans hz hr)
    · exact O.irrefl r (hr ▸ hz)

theorem frontier_coneNodes_card_lt (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) :
    (coneNodes O z).card < (coneNodes O r).card :=
  coneNodes_card_lt O (relative_frontier_cone O r Z hp z hz).1

/-- The genuine finite subtree induction principle used by the routing
construction. Its recursive hypotheses are only proper descendant cones. -/
theorem cone_induction (O : RankedOrder n) (P : Fin n → Prop)
    (step : ∀ r, (∀ z, O.rel r z → P z) → P r) (r : Fin n) : P r := by
  apply step r
  intro z hz
  exact cone_induction O P step z
termination_by (coneNodes O r).card
decreasing_by exact coneNodes_card_lt O hz

end StackSorting.LowPathwidthParts
