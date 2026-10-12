import FirstReturnAlgebra

/-! Conditional bounded first-return algebra. The separate finite-cardinality
layer must instantiate every identity for actual capacity-restricted paths. -/
namespace StackSorting.CapacityAlgebra
open FirstReturnAlgebra
variable {R : Type*} [CommRing R]
local notation "S" => PowerSeries R
local notation "x" => (PowerSeries.X : S)

structure Identities (R : Type*) [CommRing R] where
  left : Nat → Mat2 (PowerSeries R)
  right : Nat → Mat2 (PowerSeries R)
  v : Nat → Mat2 (PowerSeries R)
  bottomL : Nat → PowerSeries R
  bottomR : Nat → PowerSeries R
  complete : Nat → PowerSeries R
  left_zero : left 0 = ⟨2,0,1,0⟩
  right_zero : right 0 = ⟨1,1,0,1⟩
  bottomL_zero : bottomL 0 = 1
  complete_zero : complete 0 = 1
  left_colL (h) : Recurs (v h) 2 1 (left (h+1)).ll (left (h+1)).rl
  left_colR (h) : Recurs (v h) 0 0 (left (h+1)).lr (left (h+1)).rr
  right_colL (h) : Recurs (v h) 1 0 (right (h+1)).ll (right (h+1)).rl
  right_colR (h) : Recurs (v h) 1 1 (right (h+1)).lr (right (h+1)).rr
  bottom (h) : Recurs (v h) 1 1 (bottomL (h+1)) (bottomR (h+1))
  vll (h) : (v h).ll = 2 * PowerSeries.X * ((left h).rl - 1)
  vlr (h) : (v h).lr = 2 * PowerSeries.X * (left h).rr
  vrl (h) : (v h).rl = PowerSeries.X * ((right h).rl + (left h).rl - 1)
  vrr (h) : (v h).rr = PowerSeries.X * ((right h).rr - 1 + (left h).rr)
  empty_step (h) : complete (h+1) = 1 + PowerSeries.X * complete (h+1) +
    PowerSeries.X * (bottomL h - 1) * complete (h+1)

/-- Simultaneous matrix shape at every capacity, including the true bottom. -/
theorem level_shape (s : Identities R) (h : Nat) :
    (s.left h).lr = 0 ∧ (s.left h).rr = 0 ∧
    (s.left h).rl = (s.right h).rl + (s.right h).rr ∧
    (s.right h).ll = (s.right h).lr ∧ s.bottomL h = (s.right h).ll ∧
    (s.right h).rr = (s.right h).ll ∧
    s.complete h = (s.right h).rr - (s.right h).rl := by
  induction h with
  | zero => simp [s.left_zero, s.right_zero, s.bottomL_zero, s.complete_zero]
  | succ h ih =>
    rcases ih with ⟨_, hrr0, hsumPrev, _, hbottomPrev, hjPrev, hfPrev⟩
    have hvll : PowerSeries.constantCoeff (s.v h).ll = 0 := by simp [s.vll]
    have hvlr : PowerSeries.constantCoeff (s.v h).lr = 0 := by simp [s.vlr]
    have hvrl : PowerSeries.constantCoeff (s.v h).rl = 0 := by simp [s.vrl]
    have hvrr : PowerSeries.constantCoeff (s.v h).rr = 0 := by simp [s.vrr]
    have uniq := recurs_unique (s.v h) hvll hvlr hvrl hvrr
    have hz : (s.left (h+1)).lr = 0 ∧ (s.left (h+1)).rr = 0 :=
      uniq 0 0 _ _ 0 0 (s.left_colR h) (by constructor <;> simp)
    have hsum : (s.left (h+1)).ll = (s.right (h+1)).ll + (s.right (h+1)).lr ∧
        (s.left (h+1)).rl = (s.right (h+1)).rl + (s.right (h+1)).rr := by
      apply uniq 2 1 _ _ _ _ (s.left_colL h)
      constructor
      · linear_combination (s.right_colL h).1 + (s.right_colR h).1
      · linear_combination (s.right_colL h).2 + (s.right_colR h).2
    have hb : s.bottomL (h+1) = (s.right (h+1)).lr ∧
        s.bottomR (h+1) = (s.right (h+1)).rr :=
      uniq 1 1 _ _ _ _ (s.bottom h) (s.right_colR h)
    have hvlr0 : (s.v h).lr = 0 := by simp [s.vlr, hrr0]
    have htopunit : IsUnit (1 - x - (s.v h).ll) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      simp [hvll]
    have htop : (1 - x - (s.v h).ll) * ((s.right (h+1)).ll - (s.right (h+1)).lr) = 0 := by
      have ha := (s.right_colL h).1
      have hb := (s.right_colR h).1
      rw [hvlr0] at ha hb
      linear_combination ha - hb
    have htopEq : (s.right (h+1)).ll = (s.right (h+1)).lr :=
      sub_eq_zero.mp (htopunit.mul_left_cancel (by simpa using htop))
    let k := (s.right (h+1)).ll
    let u := (s.right (h+1)).rl
    let j := (s.right (h+1)).rr
    let kp := (s.right h).ll
    let fp := s.complete h
    have hv00 : (s.v h).ll = x * (4*kp-2*fp-2) := by
      rw [s.vll, hsumPrev]
      dsimp [kp,fp]
      linear_combination 2*x*hfPrev + 4*x*hjPrev
    have hv10 : (s.v h).rl = x * (3*kp-2*fp-1) := by
      rw [s.vrl, hsumPrev]
      dsimp [kp,fp]
      linear_combination 2*x*hfPrev + 3*x*hjPrev
    have hv11 : (s.v h).rr = x * (kp-1) := by simp [s.vrr, hrr0, hjPrev, kp]
    have hk : k = 1 + x * (4*kp-2*fp-1) * k := by
      have he := (s.right_colL h).1
      rw [hvlr0,hv00] at he
      dsimp [k]
      linear_combination he
    have hj : j = 1 + x*kp*j + x*(3*kp-2*fp-1)*k := by
      have he := (s.right_colR h).2
      rw [hv10,hv11,← htopEq] at he
      dsimp [k,j]
      linear_combination he
    have hu : u = x*kp*u + x*(3*kp-2*fp-1)*k := by
      have he := (s.right_colL h).2
      rw [hv10,hv11] at he
      dsimp [k,u]
      linear_combination he
    have hkj0 : (1-x*kp)*(k-j)=0 := by linear_combination hk-hj
    have hkj : k=j := sub_eq_zero.mp
      ((unit_one_sub_X_mul kp).mul_left_cancel (by simpa using hkj0))
    have hf : s.complete (h+1) = 1+x*kp*s.complete (h+1) := by
      have he := s.empty_step h
      rw [hbottomPrev] at he
      dsimp [kp]
      linear_combination he
    have hfj0 : (1-x*kp)*(s.complete (h+1)-(j-u))=0 := by
      linear_combination hf-hj+hu
    have hfj : s.complete (h+1)=j-u := sub_eq_zero.mp
      ((unit_one_sub_X_mul kp).mul_left_cancel (by simpa using hfj0))
    exact ⟨hz.1,hz.2,hsum.2,htopEq,hb.1.trans htopEq.symm,hkj.symm,hfj⟩

/-- Uniform bounded-capacity recurrences, written without division. All
multipliers have constant coefficient one, so these specify unique series. -/
theorem recurrence (s : Identities R) (h : Nat) :
    (1+x-4*x*(s.right h).ll+2*x*s.complete h)*(s.right (h+1)).ll = 1 ∧
    (1-x*(s.right h).ll)*s.complete (h+1) = 1 := by
  obtain ⟨_, hrr, hsum, _, hb, hj, hf⟩ := level_shape s h
  have hvlr : (s.v h).lr=0 := by simp [s.vlr,hrr]
  have hvll : (s.v h).ll=x*(4*(s.right h).ll-2*s.complete h-2) := by
    rw [s.vll,hsum]
    linear_combination 2*x*hf+4*x*hj
  constructor
  · have he := (s.right_colL h).1
    rw [hvlr,hvll] at he
    linear_combination he
  · have he := s.empty_step h
    rw [hb] at he
    linear_combination he

/-- The two scalar recurrences and their zero-capacity values determine the
entire family uniquely; no coefficient fitting selects a solution. -/
theorem recurrence_unique (k f k' f' : Nat → S)
    (hk0 : k 0 = k' 0) (hf0 : f 0 = f' 0)
    (hk : ∀ h, (1+x-4*x*k h+2*x*f h)*k (h+1)=1)
    (hf : ∀ h, (1-x*k h)*f (h+1)=1)
    (hk' : ∀ h, (1+x-4*x*k' h+2*x*f' h)*k' (h+1)=1)
    (hf' : ∀ h, (1-x*k' h)*f' (h+1)=1) :
    ∀ h, k h = k' h ∧ f h = f' h := by
  intro h
  induction h with
  | zero => exact ⟨hk0,hf0⟩
  | succ h ih =>
    have huk : IsUnit (1+x-4*x*k h+2*x*f h) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      simp
    have huf : IsUnit (1-x*k h) := unit_one_sub_X_mul (k h)
    constructor
    · apply huk.mul_left_cancel
      rw [hk h,ih.1,ih.2,hk' h]
    · apply huf.mul_left_cancel
      rw [hf h,ih.1,hf' h]

#print axioms level_shape
#print axioms recurrence
#print axioms recurrence_unique
end StackSorting.CapacityAlgebra
