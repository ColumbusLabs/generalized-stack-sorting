import ScalarBranchUnique

namespace StackSorting.FPSDivision
open StackSorting.ProperSeries StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics StackSorting.ConcreteScalar
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- The coefficient tail, not an inverse of the formal variable. -/
def tail (a : FPS) : FPS := ⟨fun n => a (n+1)⟩

theorem head_tail (a : FPS) : a = C (a 0) + X * tail a := by
  apply FPS.ext
  funext n
  have hs := congrFun (X_mul_coeff (tail a)) n
  cases n with
  | zero =>
    change a 0 = const (a 0) 0 + (X * tail a) 0
    rw [hs]
    change a 0 = a 0 + 0
    grind
  | succ n =>
    change a (n+1) = const (a 0) (n+1) + (X * tail a) (n+1)
    rw [hs]
    change a (n+1) = 0 + a (n+1)
    grind

/-- A fixed point of this genuinely contracting operator is the reciprocal
of a series with nonzero constant term. -/
def invStep (a : FPS) (r : Rat) (b : Family Unit Rat) : Family Unit Rat :=
  fun _ n => const r n + -(shift (fun k => r * cauchy (tail a).coeff (b ()) k) n)

theorem invStep_contracting (a : FPS) (r : Rat) : Contracting (invStep a r) := by
  intro n b c h i k hk
  cases k with
  | zero => rfl
  | succ k =>
    change const r (k+1) + -(r*cauchy (tail a).coeff (b ()) k) =
      const r (k+1) + -(r*cauchy (tail a).coeff (c ()) k)
    congr 3
    apply sumTerms_congr
    intro j hj
    rw [h () (k-j) (by omega)]

/-- Defined for all formal series. The inverse law is asserted only when
its constant coefficient is nonzero. -/
def inv (a : FPS) : FPS := ⟨solution (invStep a (a 0)⁻¹) (fun _ _ => 0) ()⟩

theorem inv_fixed (a : FPS) :
    inv a = C ((a 0)⁻¹) - X * (C ((a 0)⁻¹) * tail a * inv a) := by
  apply FPS.ext
  funext n
  have hf := congrFun (congrFun
    (solution_fixed (invStep_contracting a (a 0)⁻¹) (fun _ _ => 0)) ()) n
  change const ((a 0)⁻¹) n +
    -(shift (fun k => (a 0)⁻¹ * cauchy (tail a).coeff (inv a).coeff k) n) = (inv a) n at hf
  change (inv a) n = const ((a 0)⁻¹) n +
    -((X * (C ((a 0)⁻¹) * tail a * inv a)) n)
  have hx := congrFun (X_mul_coeff (C ((a 0)⁻¹) * tail a * inv a)) n
  rw [hx]
  have hc : (C ((a 0)⁻¹) * tail a * inv a).coeff =
      fun k => (a 0)⁻¹ * cauchy (tail a).coeff (inv a).coeff k := by
    have ha : C ((a 0)⁻¹) * tail a * inv a = C ((a 0)⁻¹) * (tail a * inv a) := by grind
    rw [ha]
    funext k
    exact cauchy_const_left _ _ k
  rw [hc]
  exact hf.symm

theorem mul_inv (a : FPS) (ha : a 0 ≠ 0) : a * inv a = 1 := by
  have hc : C (a 0) * C ((a 0)⁻¹) = 1 := by
    rw [← C_mul]
    have h : a 0 * (a 0)⁻¹ = 1 := Rat.mul_inv_cancel _ ha
    rw [h]
    rfl
  have hi := inv_fixed a
  have ht := head_tail a
  grind

theorem inv_mul (a : FPS) (ha : a 0 ≠ 0) : inv a * a = 1 := by
  rw [FPS_mul_comm]
  exact mul_inv a ha

theorem inv_constant (a : FPS) : inv a 0 = (a 0)⁻¹ := by
  have h := congrFun (congrFun
    (solution_fixed (invStep_contracting a (a 0)⁻¹) (fun _ _ => 0)) ()) 0
  change (a 0)⁻¹ + -0 = inv a 0 at h
  grind

theorem mul_cancel_left (a : FPS) (ha : a 0 ≠ 0) {b c : FPS}
    (h : a*b=a*c) : b=c := by
  have hi := inv_mul a ha
  calc
    b = (inv a*a)*b := by rw [hi]; grind
    _ = inv a*(a*b) := by grind
    _ = inv a*(a*c) := by rw [h]
    _ = (inv a*a)*c := by grind
    _ = c := by rw [hi]; grind

/-- Exact removal of a known power of x, implemented by coefficient shift. -/
def drop (k : Nat) (a : FPS) : FPS := ⟨fun n => a (n+k)⟩

theorem drop_factor (k : Nat) (a : FPS)
    (h : ∀ n, n<k → a n=0) : a = X^k * drop k a := by
  apply FPS.ext
  funext n
  rw [X_pow_mul_coeff]
  by_cases hn : n<k
  · rw [ite_eq_left hn, h n hn]
  · rw [ite_eq_right hn]
    change a n = a (n-k+k)
    congr 1
    omega

/-- A quotient after equal x-factor removal. Only the resulting unit is
inverted; the positive-valuation original denominator is never inverted. -/
def regularQuotient (k : Nat) (num den : FPS) : FPS :=
  drop k num * inv (drop k den)

theorem regularQuotient_cross (k : Nat) (num den : FPS)
    (hn : ∀ n, n<k → num n=0) (hd : ∀ n, n<k → den n=0)
    (hu : den k ≠ 0) : den * regularQuotient k num den = num := by
  have hn' := drop_factor k num hn
  have hd' := drop_factor k den hd
  have hu' : drop k den 0 ≠ 0 := by simpa [drop] using hu
  have hi := mul_inv (drop k den) hu'
  unfold regularQuotient
  rw [hd']
  calc
    _ = X^k * drop k num * (drop k den * inv (drop k den)) := by grind
    _ = X^k * drop k num := by rw [hi]; grind
    _ = num := hn'.symm

theorem regularQuotient_constant (k : Nat) (num den : FPS) :
    regularQuotient k num den 0 = num k * (den k)⁻¹ := by
  change cauchy (drop k num).coeff (inv (drop k den)).coeff 0 = _
  rw [cauchy_zero, inv_constant]
  simp only [drop, Nat.zero_add]

/-- Multiplication by such a denominator is injective even though its
constant coefficient vanishes. -/
theorem regular_cancel (k : Nat) (den : FPS)
    (hd : ∀ n, n<k → den n=0) (hu : den k ≠ 0)
    {a b : FPS} (h : den*a=den*b) : a=b := by
  have hf := drop_factor k den hd
  rw [hf] at h
  have h' : X^k*(drop k den*a)=X^k*(drop k den*b) := by grind
  have hh := X_pow_cancel k h'
  apply mul_cancel_left (drop k den) (by simpa [drop] using hu) hh

def Cancellable (a : FPS) : Prop := ∀ b c : FPS, a*b=a*c → b=c

theorem cancellable_mul {a b : FPS} (ha : Cancellable a) (hb : Cancellable b) :
    Cancellable (a*b) := by
  intro c d h
  have h' : a*(b*c)=a*(b*d) := by grind
  exact hb c d (ha _ _ h')

theorem cancellable_one : Cancellable (1 : FPS) := by
  intro b c h
  grind

theorem cancellable_pow {a : FPS} (ha : Cancellable a) (k : Nat) :
    Cancellable (a^k) := by
  induction k with
  | zero => exact cancellable_one
  | succ k ih => exact cancellable_mul ih ha

theorem cancellable_zero {a b : FPS} (ha : Cancellable a) (h : a*b=0) : b=0 := by
  apply ha b 0
  grind

#print axioms mul_inv
#print axioms regularQuotient_cross
end StackSorting.FPSDivision
