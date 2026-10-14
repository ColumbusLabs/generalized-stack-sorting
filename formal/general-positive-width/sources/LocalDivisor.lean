import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Local divisors of monoids
The carrier and product follow Diekert–Kufleitner, “A Survey on the Local
Divisor Technique”, arXiv:1410.6026v4, §2.  The monoid laws do not need finiteness.
-/

namespace StackSorting.Simon

variable {M : Type*} [Monoid M]

/-- The intersection `cM ∩ Mc`, with a new monoid operation. -/
def LocalDivisor (c : M) :=
  {a : M // (∃ y, c * y = a) ∧ (∃ x, x * c = a)}

namespace LocalDivisor

variable {c : M}
noncomputable section

/-- A selected right-ideal representation. Its choice does not affect multiplication. -/
def leftFactor (a : LocalDivisor c) : M := Classical.choose a.property.2

theorem leftFactor_spec (a : LocalDivisor c) : leftFactor a * c = a.val :=
  Classical.choose_spec a.property.2

instance : Mul (LocalDivisor c) where
  mul a b := ⟨leftFactor a * b.val, by
    constructor
    · obtain ⟨u, hu⟩ := a.property.1
      obtain ⟨v, hv⟩ := b.property.1
      refine ⟨u * v, ?_⟩
      calc
        c * (u * v) = (c * u) * v := (mul_assoc _ _ _).symm
        _ = a.val * v := by rw [hu]
        _ = (leftFactor a * c) * v := by rw [leftFactor_spec]
        _ = leftFactor a * (c * v) := mul_assoc _ _ _
        _ = leftFactor a * b.val := by rw [hv]
    · obtain ⟨w, hw⟩ := b.property.2
      exact ⟨leftFactor a * w, by rw [mul_assoc, hw]⟩⟩

/-- The product is independent of the selected representative of its first factor. -/
theorem val_mul_left (a b : LocalDivisor c) (x : M) (hx : x * c = a.val) :
    (a * b).val = x * b.val := by
  obtain ⟨y, hy⟩ := b.property.1
  change leftFactor a * b.val = x * b.val
  calc
    leftFactor a * b.val = leftFactor a * (c * y) := by rw [hy]
    _ = (leftFactor a * c) * y := (mul_assoc _ _ _).symm
    _ = a.val * y := by rw [leftFactor_spec]
    _ = (x * c) * y := by rw [hx]
    _ = x * (c * y) := mul_assoc _ _ _
    _ = x * b.val := by rw [hy]

/-- The defining local-divisor formula `(xc) ∘ (cy) = xcy`. -/
theorem val_mul_of_representations (a b : LocalDivisor c) (x y : M)
    (hx : x * c = a.val) (hy : c * y = b.val) :
    (a * b).val = x * c * y := by
  rw [val_mul_left a b x hx, ← hy, mul_assoc]

instance : One (LocalDivisor c) where
  one := ⟨c, ⟨⟨1, mul_one c⟩, ⟨1, one_mul c⟩⟩⟩

@[simp] theorem val_one : (1 : LocalDivisor c).val = c := rfl

instance : Monoid (LocalDivisor c) where
  mul_assoc a b d := by
    apply Subtype.ext
    obtain ⟨x, hx⟩ := a.property.2
    obtain ⟨y, hy⟩ := b.property.2
    have hab : (x * y) * c = (a * b).val := by
      rw [mul_assoc, hy, val_mul_left a b x hx]
    rw [val_mul_left (a * b) d (x * y) hab,
      val_mul_left a (b * d) x hx, val_mul_left b d y hy, mul_assoc]
  one_mul a := by
    apply Subtype.ext
    rw [val_mul_left 1 a 1 (by simp), one_mul]
  mul_one a := by
    apply Subtype.ext
    rw [val_mul_left a 1 (leftFactor a) (leftFactor_spec a), val_one,
      leftFactor_spec]

/-- A convenient element representing a block with `c` at each end. -/
def sandwich (c x : M) : LocalDivisor c :=
  ⟨c * x * c, ⟨⟨x * c, (mul_assoc _ _ _).symm⟩, ⟨c * x, rfl⟩⟩⟩

@[simp] theorem val_sandwich (c x : M) : (sandwich c x).val = c * x * c := rfl

theorem val_mul_right (a b : LocalDivisor c) (y : M) (hy : c * y = b.val) :
    (a * b).val = a.val * y := by
  rw [val_mul_left a b (leftFactor a) (leftFactor_spec a), ← hy,
    ← mul_assoc, leftFactor_spec]

/-- Concatenating interior blocks inserts one occurrence of `c`. -/
theorem sandwich_mul (c x y : M) :
    sandwich c x * sandwich c y = sandwich c (x * c * y) := by
  apply Subtype.ext
  rw [val_mul_left (sandwich c x) (sandwich c y) (c * x) rfl]
  simp only [val_sandwich, mul_assoc]

/-- A local idempotent absorbs the right boundary of any block in its fiber. -/
theorem fiber_absorb (e : LocalDivisor c) (he : e * e = e) (x : M)
    (hx : sandwich c x = e) : e.val * x * c = e.val := by
  have h := congrArg (fun a : LocalDivisor c => a.val) he
  have hx' : c * (x * c) = e.val := by
    rw [← hx, val_sandwich, mul_assoc]
  rw [val_mul_right e e (x * c) hx', ← mul_assoc] at h
  exact h

/-- Two fiber blocks evaluate to a quantity depending only on the final block. -/
theorem fiber_pair (e : LocalDivisor c) (x y : M)
    (hx : sandwich c x = e) : (c * x) * (c * y) = e.val * y := by
  have hx' := congrArg (fun a : LocalDivisor c => a.val) hx
  change c * x * c = e.val at hx'
  rw [← mul_assoc, hx']

/-- The same last-block formula persists when another fiber block is appended. -/
theorem fiber_step (e : LocalDivisor c) (he : e * e = e) (x y : M)
    (hx : sandwich c x = e) : (e.val * x) * (c * y) = e.val * y := by
  rw [← mul_assoc, fiber_absorb e he x hx]

/-- Collapsed products form a right-zero band in the ambient monoid. -/
theorem fiber_mul (e : LocalDivisor c) (he : e * e = e) (x y : M)
    (hx : sandwich c x = e) : (e.val * x) * (e.val * y) = e.val * y := by
  have hx' := congrArg (fun a : LocalDivisor c => a.val) hx
  change c * x * c = e.val at hx'
  calc
    (e.val * x) * (e.val * y) = ((e.val * x) * e.val) * y :=
      (mul_assoc _ _ _).symm
    _ = ((e.val * x) * (c * x * c)) * y := by rw [hx']
    _ = (((e.val * x * c) * x) * c) * y := by simp only [mul_assoc]
    _ = (e.val * x * c) * y := by simp only [fiber_absorb e he x hx]
    _ = e.val * y := by rw [fiber_absorb e he x hx]

/-- The values obtained from two or more blocks are ambient idempotents. -/
theorem fiber_idempotent (e : LocalDivisor c) (he : e * e = e) (x : M)
    (hx : sandwich c x = e) : (e.val * x) * (e.val * x) = e.val * x :=
  fiber_mul e he x x hx

/-- A middle block in a three-block fiber product can be discarded. -/
theorem fiber_triple (e : LocalDivisor c) (he : e * e = e) (x y z : M)
    (hx : sandwich c x = e) (hy : sandwich c y = e) :
    ((c * x) * (c * y)) * (c * z) = (c * x) * (c * z) := by
  rw [fiber_pair e x y hx, fiber_step e he y z hy, fiber_pair e x z hx]

/-- Pairs with the same last block have the same value. -/
theorem fiber_pair_same_last (e : LocalDivisor c) (x y z : M)
    (hx : sandwich c x = e) (hz : sandwich c z = e) :
    (c * x) * (c * y) = (c * z) * (c * y) := by
  rw [fiber_pair e x y hx, fiber_pair e z y hz]

/-- Pairing neighboring fiber blocks yields a right-zero band. -/
theorem fiber_pairs_mul (e : LocalDivisor c) (he : e * e = e) (x y z t : M)
    (hx : sandwich c x = e) (hy : sandwich c y = e) (hz : sandwich c z = e) :
    ((c * x) * (c * y)) * ((c * z) * (c * t)) = (c * z) * (c * t) := by
  rw [fiber_pair e x y hx, fiber_pair e z t hz, fiber_mul e he y t hy]

/-- Equal ambient terminal blocks give equal collapsed products. -/
theorem fiber_same_terminal (e : LocalDivisor c) (x y : M)
    (hxy : c * x = c * y) : e.val * x = e.val * y := by
  obtain ⟨u, hu⟩ := e.property.2
  rw [← hu, mul_assoc, mul_assoc, hxy]

/-- An ambient identity belongs to the local divisor exactly for units. -/
theorem one_mem_iff : ((∃ y : M, c * y = 1) ∧ (∃ x : M, x * c = 1)) ↔
    IsUnit c := isUnit_iff_exists_and_exists.symm

instance [Finite M] : Finite (LocalDivisor c) :=
  Finite.of_injective (fun a => a.val) Subtype.val_injective

noncomputable instance [Fintype M] : Fintype (LocalDivisor c) :=
  Fintype.ofFinite _

/-- Strict reduction of the finite carrier at any nonunit. -/
theorem card_lt [Fintype M] (hc : ¬ IsUnit c) :
    Fintype.card (LocalDivisor c) < Fintype.card M := by
  apply Fintype.card_lt_of_injective_of_notMem
    (fun a : LocalDivisor c => a.val) Subtype.val_injective (b := 1)
  rintro ⟨a, ha⟩
  apply hc
  apply isUnit_iff_exists_and_exists.mpr
  simpa only [ha] using a.property

#print axioms val_mul_of_representations
#print axioms card_lt
#print axioms fiber_pairs_mul
#print axioms fiber_idempotent

end
end LocalDivisor
end StackSorting.Simon
