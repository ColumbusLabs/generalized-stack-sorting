import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Logic.Relation
import Lean.Elab.Tactic.Omega

/-!
# Finite antisymmetric integer-flow cut algebra

The statements below use only finite sums and directed reachability. They do
not assume Menger's theorem, a max-flow theorem, or a min-cut theorem.
-/

open scoped BigOperators

namespace FiniteFlow

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Net flow out of a vertex. -/
def divergence (f : V → V → ℤ) (u : V) : ℤ := ∑ v, f u v

/-- Signed net flow out of a finite vertex set. -/
def cutFlow (f : V → V → ℤ) (S : Finset V) : ℤ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, f u v

/-- Total directed capacity out of a finite vertex set, as an integer. -/
def cutCapacity (c : V → V → ℕ) (S : Finset V) : ℤ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, (c u v : ℤ)

/-- Directed residual edge: one additional integer unit can be sent. -/
def Residual (c : V → V → ℕ) (f : V → V → ℤ) (u v : V) : Prop :=
  f u v < (c u v : ℤ)

/-- Directed edge currently carrying strictly positive flow. -/
def Positive (f : V → V → ℤ) (u v : V) : Prop := 0 < f u v

@[simp] theorem divergence_zero (u : V) :
    divergence (fun _ _ => (0 : ℤ)) u = 0 := by simp [divergence]

/-- Divergence is additive under pointwise flow addition. -/
theorem divergence_add (f g : V → V → ℤ) (u : V) :
    divergence (fun a b => f a b + g a b) u = divergence f u + divergence g u :=
  Finset.sum_add_distrib

/-- Divergence is additive under pointwise flow subtraction. -/
theorem divergence_sub (f g : V → V → ℤ) (u : V) :
    divergence (fun a b => f a b - g a b) u = divergence f u - divergence g u :=
  Finset.sum_sub_distrib (f u) (g u)

/-- Pointwise addition preserves antisymmetry. -/
theorem antisym_add (f g : V → V → ℤ)
    (hf : ∀ u v, f u v = -f v u) (hg : ∀ u v, g u v = -g v u) :
    ∀ u v, f u v + g u v = -(f v u + g v u) := by
  intro u v
  have hfu := hf u v
  have hgu := hg u v
  omega

/-- Pointwise subtraction preserves antisymmetry. -/
theorem antisym_sub (f g : V → V → ℤ)
    (hf : ∀ u v, f u v = -f v u) (hg : ∀ u v, g u v = -g v u) :
    ∀ u v, f u v - g u v = -(f v u - g v u) := by
  intro u v
  have hfu := hf u v
  have hgu := hg u v
  omega

/-- Adding flows adds their source values and preserves conservation. -/
theorem balance_add (f g : V → V → ℤ) (s t : V) (v w : ℤ)
    (hf : ∀ u, divergence f u =
      (if u = s then v else 0) - (if u = t then v else 0))
    (hg : ∀ u, divergence g u =
      (if u = s then w else 0) - (if u = t then w else 0)) :
    ∀ u, divergence (fun a b => f a b + g a b) u =
      (if u = s then v + w else 0) - (if u = t then v + w else 0) := by
  intro u
  rw [divergence_add, hf, hg]
  by_cases hs : u = s <;> by_cases ht : u = t
  · simp only [ite_eq_left hs, ite_eq_left ht]
    omega
  · simp only [ite_eq_left hs, ite_eq_right ht]
    omega
  · simp only [ite_eq_right hs, ite_eq_left ht]
    omega
  · simp only [ite_eq_right hs, ite_eq_right ht]
    omega

/-- Subtracting flows subtracts their source values and preserves conservation. -/
theorem balance_sub (f g : V → V → ℤ) (s t : V) (v w : ℤ)
    (hf : ∀ u, divergence f u =
      (if u = s then v else 0) - (if u = t then v else 0))
    (hg : ∀ u, divergence g u =
      (if u = s then w else 0) - (if u = t then w else 0)) :
    ∀ u, divergence (fun a b => f a b - g a b) u =
      (if u = s then v - w else 0) - (if u = t then v - w else 0) := by
  intro u
  rw [divergence_sub, hf, hg]
  by_cases hs : u = s <;> by_cases ht : u = t
  · simp only [ite_eq_left hs, ite_eq_left ht]
    omega
  · simp only [ite_eq_left hs, ite_eq_right ht]
    omega
  · simp only [ite_eq_right hs, ite_eq_left ht]
    omega
  · simp only [ite_eq_right hs, ite_eq_right ht]
    omega

/-- Internal flows cancel in pairs. -/
theorem internal_sum_eq_zero (f : V → V → ℤ)
    (antisym : ∀ u v, f u v = -f v u) (S : Finset V) :
    (∑ u ∈ S, ∑ v ∈ S, f u v) = 0 := by
  have h : (∑ u ∈ S, ∑ v ∈ S, f u v) =
      -(∑ u ∈ S, ∑ v ∈ S, f u v) := by
    calc
      (∑ u ∈ S, ∑ v ∈ S, f u v) =
          ∑ u ∈ S, ∑ v ∈ S, -f v u := by
            apply Finset.sum_congr rfl
            intro u hu
            apply Finset.sum_congr rfl
            intro v hv
            exact antisym u v
      _ = -(∑ u ∈ S, ∑ v ∈ S, f v u) := by
        simp only [Finset.sum_neg_distrib]
      _ = -(∑ u ∈ S, ∑ v ∈ S, f u v) := by
        rw [Finset.sum_comm]
  omega

/-- The discrete divergence theorem for antisymmetric finite flows. -/
theorem cut_divergence (f : V → V → ℤ)
    (antisym : ∀ u v, f u v = -f v u) (S : Finset V) :
    (∑ u ∈ S, divergence f u) = cutFlow f S := by
  unfold divergence cutFlow
  calc
    (∑ u ∈ S, ∑ v, f u v) =
        ∑ u ∈ S, ((∑ v ∈ S, f u v) + ∑ v ∈ Sᶜ, f u v) := by
          apply Finset.sum_congr rfl
          intro u hu
          exact (Finset.sum_add_sum_compl S (f u)).symm
    _ = (∑ u ∈ S, ∑ v ∈ S, f u v) +
        ∑ u ∈ S, ∑ v ∈ Sᶜ, f u v := Finset.sum_add_distrib
    _ = ∑ u ∈ S, ∑ v ∈ Sᶜ, f u v := by
      rw [internal_sum_eq_zero f antisym S, zero_add]

/-- Any cut containing the source but not the sink carries the flow value. -/
theorem source_cutFlow (f : V → V → ℤ)
    (antisym : ∀ u v, f u v = -f v u)
    (s t : V) (value : ℤ)
    (balance : ∀ u, divergence f u =
      (if u = s then value else 0) - (if u = t then value else 0))
    (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    cutFlow f S = value := by
  rw [← cut_divergence f antisym S]
  simp_rw [balance]
  rw [Finset.sum_sub_distrib]
  simp [hs, ht]

/-- Every feasible flow is bounded above by every source-sink cut. -/
theorem value_le_cutCapacity (c : V → V → ℕ) (f : V → V → ℤ)
    (antisym : ∀ u v, f u v = -f v u)
    (capacityBound : ∀ u v, f u v ≤ (c u v : ℤ))
    (s t : V) (value : ℤ)
    (balance : ∀ u, divergence f u =
      (if u = s then value else 0) - (if u = t then value else 0))
    (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    value ≤ cutCapacity c S := by
  rw [← source_cutFlow f antisym s t value balance S hs ht]
  exact Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => capacityBound u v

/-- A cut with no outgoing residual edge is saturated edge by edge. -/
theorem residual_closed_saturated (c : V → V → ℕ) (f : V → V → ℤ)
    (capacityBound : ∀ u v, f u v ≤ (c u v : ℤ))
    (S : Finset V)
    (closed : ∀ u ∈ S, ∀ v ∉ S, ¬ Residual c f u v) :
    ∀ u ∈ S, ∀ v ∉ S, f u v = (c u v : ℤ) := by
  intro u hu v hv
  exact le_antisymm (capacityBound u v) (le_of_not_gt (closed u hu v hv))

/-- A residual-closed source-sink cut has capacity exactly the flow value. -/
theorem residual_closed_cut_eq (c : V → V → ℕ) (f : V → V → ℤ)
    (antisym : ∀ u v, f u v = -f v u)
    (capacityBound : ∀ u v, f u v ≤ (c u v : ℤ))
    (s t : V) (value : ℤ)
    (balance : ∀ u, divergence f u =
      (if u = s then value else 0) - (if u = t then value else 0))
    (S : Finset V) (hs : s ∈ S) (ht : t ∉ S)
    (closed : ∀ u ∈ S, ∀ v ∉ S, ¬ Residual c f u v) :
    cutCapacity c S = value := by
  rw [← source_cutFlow f antisym s t value balance S hs ht]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  exact (residual_closed_saturated c f capacityBound S closed u hu v
    (Finset.mem_compl.mp hv)).symm

/-- Positive source value forces a positive-flow edge across every source-sink cut. -/
theorem positive_value_crossing (f : V → V → ℤ)
    (antisym : ∀ u v, f u v = -f v u)
    (s t : V) (value : ℤ)
    (balance : ∀ u, divergence f u =
      (if u = s then value else 0) - (if u = t then value else 0))
    (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) (hvalue : 0 < value) :
    ∃ u ∈ S, ∃ v ∉ S, Positive f u v := by
  by_contra h
  have hclosed : ∀ u ∈ S, ∀ v ∉ S, f u v ≤ 0 := by
    intro u hu v hv
    exact le_of_not_gt (fun hpos => h ⟨u, hu, v, hv, hpos⟩)
  have hnonpos : cutFlow f S ≤ 0 := by
    apply Finset.sum_nonpos
    intro u hu
    apply Finset.sum_nonpos
    intro v hv
    exact hclosed u hu v (Finset.mem_compl.mp hv)
  rw [source_cutFlow f antisym s t value balance S hs ht] at hnonpos
  omega

/-- The set reachable by a finite directed walk, including the starting vertex. -/
noncomputable def reachableFinset (r : V → V → Prop) (s : V) : Finset V := by
  classical
  exact Finset.univ.filter (Relation.ReflTransGen r s)

@[simp] theorem mem_reachableFinset (r : V → V → Prop) (s v : V) :
    v ∈ reachableFinset r s ↔ Relation.ReflTransGen r s v := by
  classical
  simp [reachableFinset]

@[simp] theorem self_mem_reachableFinset (r : V → V → Prop) (s : V) :
    s ∈ reachableFinset r s := by
  exact (mem_reachableFinset r s s).mpr .refl

/-- An edge cannot leave the reachable set. -/
theorem reachableFinset_closed (r : V → V → Prop) (s : V) :
    ∀ u ∈ reachableFinset r s, ∀ v ∉ reachableFinset r s, ¬ r u v := by
  intro u hu v hv huv
  exact hv ((mem_reachableFinset r s v).mpr
    ((mem_reachableFinset r s u).mp hu |>.tail huv))

/-- A directed relation with no edge leaving a source-sink cut cannot connect
its source to its sink. -/
theorem not_reachable_of_cut (r : V → V → Prop) (S : Finset V)
    (s t : V) (hs : s ∈ S) (ht : t ∉ S)
    (closed : ∀ u ∈ S, ∀ v ∉ S, ¬ r u v) :
    ¬ Relation.ReflTransGen r s t := by
  intro hreach
  have hmem : ∀ v, Relation.ReflTransGen r s v → v ∈ S := by
    intro v h
    induction h with
    | refl => exact hs
    | @tail u v h huv ih =>
      by_contra hv
      exact closed u ih v hv huv
  exact ht (hmem t hreach)

/-- If the sink is not residual-reachable, the reachable cut realizes the value. -/
theorem residual_nonreachable_cut_eq (c : V → V → ℕ) (f : V → V → ℤ)
    (antisym : ∀ u v, f u v = -f v u)
    (capacityBound : ∀ u v, f u v ≤ (c u v : ℤ))
    (s t : V) (value : ℤ)
    (balance : ∀ u, divergence f u =
      (if u = s then value else 0) - (if u = t then value else 0))
    (hnoreach : ¬ Relation.ReflTransGen (Residual c f) s t) :
    cutCapacity c (reachableFinset (Residual c f) s) = value := by
  apply residual_closed_cut_eq c f antisym capacityBound s t value balance
  · exact self_mem_reachableFinset _ _
  · simpa using hnoreach
  · exact reachableFinset_closed _ _

/-- A positive-value balanced flow contains a directed positive-flow source-sink walk. -/
theorem positive_reachable (f : V → V → ℤ)
    (antisym : ∀ u v, f u v = -f v u)
    (s t : V) (value : ℤ)
    (balance : ∀ u, divergence f u =
      (if u = s then value else 0) - (if u = t then value else 0))
    (hvalue : 0 < value) : Relation.ReflTransGen (Positive f) s t := by
  by_contra hnoreach
  have ht : t ∉ reachableFinset (Positive f) s := by simpa using hnoreach
  obtain ⟨u, hu, v, hv, huv⟩ := positive_value_crossing f antisym s t value balance
    (reachableFinset (Positive f) s) (self_mem_reachableFinset _ _) ht hvalue
  exact reachableFinset_closed (Positive f) s u hu v hv huv

end FiniteFlow
