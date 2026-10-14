import FiniteFlowCut

open scoped BigOperators

namespace FiniteFlow

/-- A nonnegative integer-valued finite sum equal to one has exactly one nonzero term. -/
theorem sum_one_unique {I : Type*} [DecidableEq I] (S : Finset I) (f : I → ℤ)
    (nonneg : ∀ i ∈ S, 0 ≤ f i) (hsum : ∑ i ∈ S, f i = 1) :
    ∃ i ∈ S, f i = 1 ∧ ∀ j ∈ S, j ≠ i → f j = 0 := by
  revert nonneg hsum
  induction S using Finset.induction_on with
  | empty =>
    intro nonneg hsum
    simp at hsum
  | @insert a S ha ih =>
    intro nonneg hsum
    have hn : ∀ i ∈ S, 0 ≤ f i := fun i hi => nonneg i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha] at hsum
    by_cases hfa : f a = 0
    · have hsumS : ∑ i ∈ S, f i = 1 := by omega
      obtain ⟨i, hi, hfi, hzero⟩ := ih hn hsumS
      refine ⟨i, Finset.mem_insert_of_mem hi, hfi, ?_⟩
      intro j hj hji
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hfa
      · exact hzero j hj hji
    · have hna : 0 ≤ f a := nonneg a (Finset.mem_insert_self a S)
      have hnS : 0 ≤ ∑ i ∈ S, f i := Finset.sum_nonneg hn
      have hfa1 : f a = 1 := by omega
      have hSzero : ∑ i ∈ S, f i = 0 := by omega
      refine ⟨a, Finset.mem_insert_self a S, hfa1, ?_⟩
      intro j hj hja
      have hjS : j ∈ S := (Finset.mem_insert.mp hj).resolve_left hja
      exact (Finset.sum_eq_zero_iff_of_nonneg hn).mp hSzero j hjS

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Directed cut capacities are nonnegative. -/
theorem cutCapacity_nonneg (c : V → V → ℕ) (S : Finset V) :
    0 ≤ cutCapacity c S :=
  Finset.sum_nonneg fun u _hu => Finset.sum_nonneg fun v _hv => Int.natCast_nonneg (c u v)

/-- A capacity-zero cut has no positive-capacity crossing edge. -/
theorem cut_capacity_zero (c : V → V → ℕ) (S : Finset V)
    (hzero : cutCapacity c S = 0) :
    ∀ u ∈ S, ∀ v ∉ S, c u v = 0 := by
  intro u hu v hv
  have hn : ∀ a ∈ S, 0 ≤ ∑ b ∈ Sᶜ, (c a b : ℤ) :=
    fun a ha => Finset.sum_nonneg fun b hb => Int.natCast_nonneg _
  have hrow : ∑ b ∈ Sᶜ, (c u b : ℤ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hn).mp hzero u hu
  have hcell : (c u v : ℤ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun b hb => Int.natCast_nonneg (c u b))).mp
      hrow v (Finset.mem_compl.mpr hv)
  omega

/-- A capacity-one directed cut has one unit-capacity crossing pair and all other
crossing ordered pairs have zero capacity. -/
theorem cut_capacity_one_unique (c : V → V → ℕ) (S : Finset V)
    (hone : cutCapacity c S = 1) :
    ∃ u ∈ S, ∃ v ∉ S, c u v = 1 ∧
      ∀ a ∈ S, ∀ b ∉ S, (a, b) ≠ (u, v) → c a b = 0 := by
  have hsum : ∑ p ∈ S ×ˢ Sᶜ, (c p.1 p.2 : ℤ) = 1 := by
    simpa [Finset.sum_product, cutCapacity] using hone
  obtain ⟨⟨u, v⟩, huv, hcap, hzero⟩ :=
    sum_one_unique (S ×ˢ Sᶜ) (fun p => (c p.1 p.2 : ℤ))
      (fun p hp => Int.natCast_nonneg _) hsum
  have hu : u ∈ S := (Finset.mem_product.mp huv).1
  have hv : v ∉ S := Finset.mem_compl.mp (Finset.mem_product.mp huv).2
  change (c u v : ℤ) = 1 at hcap
  refine ⟨u, hu, v, hv, ?_, ?_⟩
  · omega
  · intro a ha b hb hab
    have hz := hzero (a, b) (Finset.mem_product.mpr ⟨ha, Finset.mem_compl.mpr hb⟩) hab
    change (c a b : ℤ) = 0 at hz
    omega

/-- The nonzero crossing ordered pair in a capacity-one cut is unique. -/
theorem cut_capacity_one_existsUnique (c : V → V → ℕ) (S : Finset V)
    (hone : cutCapacity c S = 1) :
    ∃! p : V × V, p.1 ∈ S ∧ p.2 ∉ S ∧ 0 < c p.1 p.2 := by
  obtain ⟨u, hu, v, hv, hcap, hzero⟩ := cut_capacity_one_unique c S hone
  refine ⟨(u, v), ⟨hu, hv, by change 0 < c u v; omega⟩, ?_⟩
  intro p hp
  by_contra hne
  have hz := hzero p.1 hp.1 p.2 hp.2.1 hne
  omega

/-- A capacity-zero cut blocks every positive-capacity source-sink walk. -/
theorem cut_capacity_zero_blocks (c : V → V → ℕ) (S : Finset V)
    (hzero : cutCapacity c S = 0) (s t : V) (hs : s ∈ S) (ht : t ∉ S) :
    ¬ Relation.ReflTransGen (fun u v => 0 < c u v) s t := by
  apply not_reachable_of_cut (fun u v => 0 < c u v) S s t hs ht
  intro u hu v hv hpos
  have hz := cut_capacity_zero c S hzero u hu v hv
  omega

/-- Removing the unique positive crossing ordered pair of a capacity-one cut
blocks every positive-capacity source-sink walk. -/
theorem cut_capacity_one_blocks_after_removal (c : V → V → ℕ) (S : Finset V)
    (hone : cutCapacity c S = 1) (s t : V) (hs : s ∈ S) (ht : t ∉ S) :
    ∃ u ∈ S, ∃ v ∉ S, c u v = 1 ∧
      ¬ Relation.ReflTransGen
        (fun a b => 0 < c a b ∧ (a, b) ≠ (u, v)) s t := by
  obtain ⟨u, hu, v, hv, hcap, hzero⟩ := cut_capacity_one_unique c S hone
  refine ⟨u, hu, v, hv, hcap, ?_⟩
  apply not_reachable_of_cut _ S s t hs ht
  intro a ha b hb hab
  have hz := hzero a ha b hb hab.2
  omega

end FiniteFlow
