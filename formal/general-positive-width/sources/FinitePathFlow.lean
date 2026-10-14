import FiniteDirectedPath
import FiniteFlowCut

/-! Signed unit flows carried by actual directed simple paths. -/
open scoped BigOperators
namespace FiniteFlow

variable {V : Type*} [DecidableEq V] {R : V → V → Prop}

def edgeFlow (a b u v : V) : ℤ :=
  (if u = a ∧ v = b then 1 else 0) - (if u = b ∧ v = a then 1 else 0)

namespace DWalk

def flow {s t} : DWalk R s t → V → V → ℤ
  | .nil _, _, _ => 0
  | .cons (s := s) (a := a) _ p, u, v => edgeFlow s a u v + p.flow u v

theorem flow_antisym {s t} (p : DWalk R s t) (u v : V) :
    p.flow u v = -p.flow v u := by
  induction p with
  | nil => simp [flow]
  | @cons s a t edge p ih =>
    have he : edgeFlow s a u v = -edgeFlow s a v u := by
      simp only [edgeFlow, and_comm]
      omega
    simp only [flow]
    rw [he, ih]
    omega

theorem flow_zero_of_not_mem_left {s t} (p : DWalk R s t) {u v : V}
    (hu : u ∉ p.vertices) : p.flow u v = 0 := by
  induction p with
  | nil => rfl
  | @cons s a t edge p ih =>
    have hus : u ≠ s := fun h => hu (by simp [vertices, h])
    have hut : u ∉ p.vertices := fun h => hu (List.mem_cons_of_mem _ h)
    have hua : u ≠ a := fun h => hut (by simp [h])
    simp [flow, edgeFlow, hus, hua, ih hut]

theorem flow_zero_of_not_mem_right {s t} (p : DWalk R s t) {u v : V}
    (hv : v ∉ p.vertices) : p.flow u v = 0 := by
  rw [p.flow_antisym, p.flow_zero_of_not_mem_left hv, neg_zero]

theorem edgeFlow_divergence [Fintype V] (a b u : V) :
    divergence (edgeFlow a b) u =
      (if u = a then 1 else 0) - (if u = b then 1 else 0) := by
  unfold divergence edgeFlow
  rw [Finset.sum_sub_distrib]
  have hx : ∀ z : V, (∑ v : V, if u = z ∧ v = b then (1 : ℤ) else 0) = if u = z then 1 else 0 := by
    intro z
    by_cases hz : u = z
    · simp only [hz, true_and, ite_true]; simp
    · simp only [hz, false_and, ite_false, Finset.sum_const_zero]
  rw [hx]
  by_cases hz : u = b
  · simp only [hz, true_and, ite_true]; simp
  · simp only [hz, false_and, ite_false, Finset.sum_const_zero]

theorem flow_balance [Fintype V] {s t} (p : DWalk R s t) (u : V) :
    divergence p.flow u =
      (if u = s then 1 else 0) - (if u = t then 1 else 0) := by
  induction p with
  | nil s => simp [divergence, flow]
  | @cons s a t edge p ih =>
    have he : divergence (DWalk.cons edge p).flow u =
        divergence (edgeFlow s a) u + divergence p.flow u := by
      exact Finset.sum_add_distrib
    rw [he, edgeFlow_divergence, ih]
    omega

theorem flow_nonpos_of_not_uses {s t} (p : DWalk R s t) {u v : V}
    (h : ¬ p.Uses u v) : p.flow u v ≤ 0 := by
  induction p with
  | nil => simp [flow]
  | @cons s a t edge p ih =>
    have he : ¬ (u = s ∧ v = a) := fun he => h (Or.inl he)
    have ht : ¬ p.Uses u v := fun ht => h (Or.inr ht)
    have hp := ih ht
    simp only [flow, edgeFlow, ite_eq_right he]
    split <;> omega

theorem uses_of_flow_pos {s t} (p : DWalk R s t) {u v : V}
    (h : 0 < p.flow u v) : p.Uses u v := by
  by_contra hn
  have := p.flow_nonpos_of_not_uses hn
  omega

theorem flow_eq_one_of_uses {s t} (p : DWalk R s t)
    (hp : p.vertices.Nodup) {u v : V} (h : p.Uses u v) : p.flow u v = 1 := by
  induction p with
  | nil => exact False.elim h
  | @cons s a t edge p ih =>
    obtain ⟨hs, ht⟩ := List.nodup_cons.mp hp
    have hsa : s ≠ a := fun h => hs (by simp [h])
    rcases h with ⟨rfl, rfl⟩ | h
    · have hz := p.flow_zero_of_not_mem_left (v := v) hs
      simp [flow, edgeFlow, hsa, hz]
    · have hu : u ≠ s := fun h' => hs (h' ▸ (p.uses_vertices h).1)
      have hv : v ≠ s := fun h' => hs (h' ▸ (p.uses_vertices h).2)
      simp [flow, edgeFlow, hu, hv, ih ht h]

theorem flow_bounds {s t} (p : DWalk R s t) (hp : p.vertices.Nodup) (u v : V) :
    -1 ≤ p.flow u v ∧ p.flow u v ≤ 1 := by
  have hupper : ∀ x y, p.flow x y ≤ 1 := by
    intro x y
    by_cases h : p.Uses x y
    · rw [p.flow_eq_one_of_uses hp h]
    · have := p.flow_nonpos_of_not_uses h
      omega
  have hu := hupper u v
  have hv := hupper v u
  have ha := p.flow_antisym u v
  omega

/-- One residual simple path gives a feasible one-unit augmentation. -/
theorem augment_capacity {s t} (c : V → V → ℕ) (f : V → V → ℤ)
    (hf : ∀ u v, f u v ≤ (c u v : ℤ))
    (p : DWalk (Residual c f) s t) (hp : p.vertices.Nodup) :
    ∀ u v, f u v + p.flow u v ≤ (c u v : ℤ) := by
  intro u v
  have hb := p.flow_bounds hp u v
  have hc := hf u v
  by_cases hpos : 0 < p.flow u v
  · have hr := p.uses_relation (p.uses_of_flow_pos hpos)
    change f u v < (c u v : ℤ) at hr
    omega
  · omega

/-- Removing one positive-flow simple path preserves all upper capacities. -/
theorem subtract_capacity {s t} (c : V → V → ℕ) (f : V → V → ℤ)
    (ha : ∀ u v, f u v = -f v u)
    (hf : ∀ u v, f u v ≤ (c u v : ℤ))
    (p : DWalk (Positive f) s t) (hp : p.vertices.Nodup) :
    ∀ u v, f u v - p.flow u v ≤ (c u v : ℤ) := by
  intro u v
  have hb := p.flow_bounds hp u v
  have hc := hf u v
  by_cases hneg : p.flow u v < 0
  · have hr : 0 < p.flow v u := by have := p.flow_antisym u v; omega
    have hfpos := p.uses_relation (p.uses_of_flow_pos hr)
    change 0 < f v u at hfpos
    have hfa := ha u v
    have hcap : (0 : ℤ) ≤ c u v := Int.natCast_nonneg _
    omega
  · omega

end DWalk
end FiniteFlow
