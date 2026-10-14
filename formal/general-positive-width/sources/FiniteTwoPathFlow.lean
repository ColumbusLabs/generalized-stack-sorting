import FinitePathFlow
import FiniteFlowCutOne

/-! A constructive two-unit residual-flow theorem, without Menger. -/
namespace FiniteFlow
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Feasible unit flow supplied by an actual simple positive-capacity path. -/
theorem initial_path_capacity (c : V → V → ℕ) {s t}
    (p : DWalk (fun u v => 0 < c u v) s t) (hp : p.vertices.Nodup) :
    ∀ u v, p.flow u v ≤ (c u v : ℤ) := by
  intro u v
  have hb := (p.flow_bounds hp u v).2
  by_cases h : 0 < p.flow u v
  · have hc := p.uses_relation (p.uses_of_flow_pos h)
    omega
  · have hc : (0 : ℤ) ≤ c u v := Int.natCast_nonneg _
    omega

/-- Unless some unit-capacity arc is unavoidable, a feasible unit flow augments. -/
theorem unit_residual_reachable (c : V → V → ℕ) (f : V → V → ℤ) (s t : V)
    (ha : ∀ u v, f u v = -f v u)
    (hc : ∀ u v, f u v ≤ (c u v : ℤ))
    (hb : ∀ u, divergence f u = (if u = s then 1 else 0) - (if u = t then 1 else 0))
    (avoid : ∀ u v, c u v = 1 → Relation.ReflTransGen
      (fun a b => 0 < c a b ∧ (a, b) ≠ (u, v)) s t) :
    Relation.ReflTransGen (Residual c f) s t := by
  by_contra hn
  have he := residual_nonreachable_cut_eq c f ha hc s t 1 hb hn
  obtain ⟨u, _, v, _, huv, hblock⟩ := cut_capacity_one_blocks_after_removal c
    (reachableFinset (Residual c f) s) he s t (self_mem_reachableFinset _ _)
    (by simpa using hn)
  exact hblock (avoid u v huv)

/-- Two simple directed paths exist, and every shared arc has capacity at least two.
The premise demands an actual avoiding walk for each capacity-one ordered pair. -/
theorem exists_two_paths (c : V → V → ℕ) (s t : V)
    (reach : Relation.ReflTransGen (fun u v => 0 < c u v) s t)
    (avoid : ∀ u v, c u v = 1 → Relation.ReflTransGen
      (fun a b => 0 < c a b ∧ (a, b) ≠ (u, v)) s t) :
    ∃ p q : DWalk (fun u v => 0 < c u v) s t,
      p.vertices.Nodup ∧ q.vertices.Nodup ∧
      ∀ u v, p.Uses u v → q.Uses u v → 2 ≤ c u v := by
  obtain ⟨p₀, hp₀⟩ := DWalk.exists_simple_of_reachable reach
  have hc₀ := initial_path_capacity c p₀ hp₀
  have hr := unit_residual_reachable c p₀.flow s t p₀.flow_antisym hc₀ p₀.flow_balance avoid
  obtain ⟨a, ha⟩ := DWalk.exists_simple_of_reachable hr
  let f : V → V → ℤ := fun u v => p₀.flow u v + a.flow u v
  have haf : ∀ u v, f u v = -f v u := antisym_add _ _ p₀.flow_antisym a.flow_antisym
  have hcf : ∀ u v, f u v ≤ (c u v : ℤ) := a.augment_capacity c p₀.flow hc₀ ha
  have hbf : ∀ u, divergence f u =
      (if u = s then 2 else 0) - (if u = t then 2 else 0) := by
    simpa using balance_add p₀.flow a.flow s t 1 1 p₀.flow_balance a.flow_balance
  have hrf := positive_reachable f haf s t 2 hbf (by decide)
  obtain ⟨p, hp⟩ := DWalk.exists_simple_of_reachable hrf
  let g : V → V → ℤ := fun u v => f u v - p.flow u v
  have hag : ∀ u v, g u v = -g v u := antisym_sub _ _ haf p.flow_antisym
  have hcg : ∀ u v, g u v ≤ (c u v : ℤ) := p.subtract_capacity c f haf hcf hp
  have hbg : ∀ u, divergence g u =
      (if u = s then 1 else 0) - (if u = t then 1 else 0) := by
    simpa using balance_sub f p.flow s t 2 1 hbf p.flow_balance
  have hrg := positive_reachable g hag s t 1 hbg (by decide)
  obtain ⟨q, hq⟩ := DWalk.exists_simple_of_reachable hrg
  have mapf : ∀ u v, Positive f u v → 0 < c u v := by
    intro u v h
    have := hcf u v
    change 0 < f u v at h
    omega
  have mapg : ∀ u v, Positive g u v → 0 < c u v := by
    intro u v h
    have := hcg u v
    change 0 < g u v at h
    omega
  refine ⟨p.mono mapf, q.mono mapg, by simpa using hp, by simpa using hq, ?_⟩
  intro u v hpu hqu
  have hpuse : p.Uses u v := (p.uses_mono mapf u v).mp hpu
  have hquse : q.Uses u v := (q.uses_mono mapg u v).mp hqu
  have heq := p.flow_eq_one_of_uses hp hpuse
  have hg := q.uses_relation hquse
  change 0 < f u v - p.flow u v at hg
  have hc := hcf u v
  omega

end FiniteFlow
