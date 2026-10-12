import CapacityEnumeration
import CapacityStabilization

/-! End-to-end finite physical-capacity enumeration. Every series below is
instantiated from exact finite cardinalities; no recurrence is assumed. -/
namespace StackSorting.Capacity
open StackSorting PowerSeries

theorem capacitySeries_zero : capacitySeries 0 = 1 := by
  rw [capacitySeries_eq_pathSeries, pathSeries_no_space]

/-- The uniform recurrence for the actual number of distinct inputs admitting
an original-machine history within physical capacity h, including bypass's
transient slot in its canonical representation. -/
theorem capacity_recurrence (h : Nat) :
    (1+X-4*X*auxiliarySeries h+2*X*capacitySeries h)*auxiliarySeries (h+1) = 1 ∧
    (1-X*auxiliarySeries h)*capacitySeries (h+1) = 1 := by
  simpa only [capacitySeries_eq_pathSeries] using actual_recurrence h

theorem capacity_one : (1-X)*capacitySeries 1 = 1 := by
  simpa [auxiliarySeries_zero] using (capacity_recurrence 0).2

/-- Each recurrence multiplier is a unit, justifying its reciprocal notation
without analytic convergence assumptions. -/
theorem capacity_denominators_units (h : Nat) :
    IsUnit (1+X-4*X*auxiliarySeries h+2*X*capacitySeries h) ∧
    IsUnit (1-X*auxiliarySeries h) := by
  constructor <;> apply isUnit_iff_constantCoeff.mpr <;> simp

/-- The recurrence uniquely specifies the actual capacity family at every bound. -/
theorem capacity_recurrence_unique (k f : Nat → PowerSeries ℤ)
    (hk0 : k 0 = 1) (hf0 : f 0 = 1)
    (hk : ∀ h, (1+X-4*X*k h+2*X*f h)*k (h+1)=1)
    (hf : ∀ h, (1-X*k h)*f (h+1)=1) :
    ∀ h, k h = auxiliarySeries h ∧ f h = capacitySeries h := by
  simpa only [capacitySeries_eq_pathSeries] using actual_recurrence_unique k f hk0 hf0 hk hf

#print axioms capacitySeries_coeff
#print axioms capacity_recurrence
#print axioms capacity_denominators_units
#print axioms capacitySeries_stabilizes
#print axioms capacity_recurrence_unique
end StackSorting.Capacity
