import EqualBasis

/-! Exact displacement widths of the three literal obstruction families.
The width is the least endpoint capacity bound, not a successful-run claim
for these forbidden permutations. -/
namespace StackSorting.Generalized

/-- Maximum of the positive endpoint excesses, with empty maximum zero. -/
def endpointWidth : List Nat → Nat
  | [] => 0
  | x :: xs => max (x+1) (endpointWidth xs - 1)

theorem boundedAt_iff_endpointWidth_le (B : Nat) (p : List Nat) :
    BoundedAt B p ↔ endpointWidth p ≤ B := by
  induction p generalizing B with
  | nil => simp [BoundedAt, endpointWidth]
  | cons x xs ih =>
    simp only [BoundedAt, endpointWidth, ih, Nat.max_le]
    omega

/-- The maximum of value minus zero-based position, truncated at zero. -/
def maxDisplacementFrom : Nat → List Nat → Nat
  | _, [] => 0
  | i, x :: xs => max (x-i) (maxDisplacementFrom (i+1) xs)

def generatedDisplacementWidth (p : List Nat) : Nat :=
  1 + maxDisplacementFrom 0 p

theorem maxDisplacementFrom_bound (D i : Nat) (p : List Nat) :
    maxDisplacementFrom i p ≤ D ↔ BoundedAt (D+i+1) p := by
  induction p generalizing i with
  | nil => simp [maxDisplacementFrom, BoundedAt]
  | cons x xs ih =>
    simp only [maxDisplacementFrom, Nat.max_le, BoundedAt, ih]
    simp only [Nat.add_assoc]
    constructor <;> intro h <;> exact ⟨by omega, h.2⟩

theorem endpointWidth_eq_displacement_of_pos {p : List Nat}
    (hp : 0 < endpointWidth p) : endpointWidth p = generatedDisplacementWidth p := by
  unfold generatedDisplacementWidth
  apply Nat.le_antisymm
  · apply (boundedAt_iff_endpointWidth_le _ _).mp
    have h := (maxDisplacementFrom_bound (maxDisplacementFrom 0 p) 0 p).mp (Nat.le_refl _)
    simpa [Nat.add_comm] using h
  · have h := (boundedAt_iff_endpointWidth_le (endpointWidth p) p).mpr (Nat.le_refl _)
    have he : endpointWidth p - 1 + 0 + 1 = endpointWidth p := by omega
    rw [← he] at h
    have hm := (maxDisplacementFrom_bound (endpointWidth p-1) 0 p).mpr h
    omega

namespace Unequal

theorem lowSeg_first_lower {B s c : Nat} {rest : List Nat}
    (h : BoundedAt B (lowSeg s 0 (c+1) ++ rest)) : s+2 ≤ B := by
  rw [lowSeg_succ] at h
  simp only [Nat.mul_zero, Nat.add_zero, List.cons_append, List.nil_append,
    BoundedAt] at h
  omega

theorem family_boundedAt_iff {r s m H : Nat} (hr : 2 ≤ r) (hrs : r < s) :
    BoundedAt H (family r s m) ↔ s+2 ≤ H := by
  constructor
  · intro h
    rw [family_segments, show r-1 = (r-2)+1 by omega] at h
    exact lowSeg_first_lower h
  · exact fun h => (family_boundedAt hr hrs).mono h

theorem family_endpointWidth {r s m : Nat} (hr : 2 ≤ r) (hrs : r < s) :
    endpointWidth (family r s m) = s+2 := by
  apply Nat.le_antisymm
  · exact (boundedAt_iff_endpointWidth_le _ _).mp (family_boundedAt hr hrs)
  · exact (family_boundedAt_iff hr hrs).mp
      ((boundedAt_iff_endpointWidth_le _ _).mpr (Nat.le_refl _))
theorem family_generatedDisplacementWidth {r s m : Nat} (hr : 2 ≤ r) (hrs : r < s) :
    generatedDisplacementWidth (family r s m) = s+2 := by
  have hw := family_endpointWidth (m := m) hr hrs
  rw [← endpointWidth_eq_displacement_of_pos (by omega)]
  exact hw
end Unequal

namespace Equal
open Unequal (lowSeg lowSeg_bounded all_bounded length_lowSeg)

theorem famA_boundedAt {r k : Nat} (hr : 3 ≤ r) : BoundedAt (r+3) (famA r k) := by
  rw [famA_eq, boundedAt_append, boundedAt_append, boundedAt_append]
  refine ⟨lowSeg_bounded r _ 0 _ (by omega), ?_, ?_, ?_⟩
  · simp only [prefixTail, length_lowSeg, BoundedAt]
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩
  · exact stepSeg_bounded hr _ 0 _ (by simp [length_lowSeg, prefixTail]; omega)
  · simp only [finA, length_lowSeg, length_stepSeg, prefixTail, List.length_cons,
      List.length_nil, List.cons_append, BoundedAt]
    refine ⟨by omega, by omega, by omega, all_bounded _ (fun x hx => ?_)⟩
    rcases List.mem_append.mp hx with hx | hx
    · have := queue_bound hr hx; omega
    · simp at hx; omega

theorem famA_boundedAt_iff {r k H : Nat} (hr : 3 ≤ r) :
    BoundedAt H (famA r k) ↔ r+3 ≤ H := by
  constructor
  · intro h
    rw [famA_eq, boundedAt_append, boundedAt_append, boundedAt_append] at h
    have ht := h.2.2.2
    simp only [finA, length_lowSeg, length_stepSeg, prefixTail, List.length_cons,
      List.length_nil, List.cons_append, BoundedAt] at ht
    omega
  · exact fun h => (famA_boundedAt hr).mono h

theorem famB_boundedAt_iff {r k H : Nat} (hr : 3 ≤ r) :
    BoundedAt H (famB r k) ↔ r+2 ≤ H := by
  constructor
  · intro h
    rw [famB_eq, show r-1 = (r-2)+1 by omega] at h
    exact Unequal.lowSeg_first_lower h
  · exact fun h => (famB_boundedAt hr).mono h

theorem famA_endpointWidth {r k : Nat} (hr : 3 ≤ r) :
    endpointWidth (famA r k) = r+3 := by
  apply Nat.le_antisymm
  · exact (boundedAt_iff_endpointWidth_le _ _).mp (famA_boundedAt hr)
  · exact (famA_boundedAt_iff hr).mp
      ((boundedAt_iff_endpointWidth_le _ _).mpr (Nat.le_refl _))

theorem famB_endpointWidth {r k : Nat} (hr : 3 ≤ r) :
    endpointWidth (famB r k) = r+2 := by
  apply Nat.le_antisymm
  · exact (boundedAt_iff_endpointWidth_le _ _).mp (famB_boundedAt hr)
  · exact (famB_boundedAt_iff hr).mp
      ((boundedAt_iff_endpointWidth_le _ _).mpr (Nat.le_refl _))
theorem famA_generatedDisplacementWidth {r k : Nat} (hr : 3 ≤ r) :
    generatedDisplacementWidth (famA r k) = r+3 := by
  have hw := famA_endpointWidth (k := k) hr
  rw [← endpointWidth_eq_displacement_of_pos (by omega)]
  exact hw

theorem famB_generatedDisplacementWidth {r k : Nat} (hr : 3 ≤ r) :
    generatedDisplacementWidth (famB r k) = r+2 := by
  have hw := famB_endpointWidth (k := k) hr
  rw [← endpointWidth_eq_displacement_of_pos (by omega)]
  exact hw
end Equal

#print axioms Unequal.family_generatedDisplacementWidth
#print axioms Equal.famA_generatedDisplacementWidth
#print axioms Equal.famB_generatedDisplacementWidth
#print axioms boundedAt_iff_endpointWidth_le
#print axioms boundedAt_iff_getElem
#print axioms Unequal.family_endpointWidth
#print axioms Equal.famA_endpointWidth
#print axioms Equal.famB_endpointWidth
end StackSorting.Generalized
