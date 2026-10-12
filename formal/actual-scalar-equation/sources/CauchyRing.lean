import PolynomialProperSystem
import Init.GrindInstances.Ring.Rat

namespace StackSorting.CauchyRing
open StackSorting.ProperSeries
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem sum_add (f g : Nat → Rat) (n : Nat) :
    sumTerms (fun k => f k + g k) n = sumTerms f n + sumTerms g n := by
  induction n with
  | zero => simp only [sumTerms]; grind
  | succ n ih => simp only [sumTerms, ih]; grind

theorem sum_scale (r : Rat) (f : Nat → Rat) (n : Nat) :
    sumTerms (fun k => r * f k) n = r * sumTerms f n := by
  induction n with
  | zero => simp only [sumTerms]; grind
  | succ n ih => simp only [sumTerms, ih]; grind

theorem sum_zero (n : Nat) : sumTerms (fun _ => (0 : Rat)) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumTerms, ih]; grind

theorem sum_head (f : Nat → Rat) (n : Nat) :
    sumTerms f (n+1) = f 0 + sumTerms (fun k => f (k+1)) n := by
  induction n with
  | zero => simp only [sumTerms]; grind
  | succ n ih => simp only [sumTerms] at *; grind

theorem sum_reverse (f : Nat → Rat) (n : Nat) :
    sumTerms (fun k => f (n-k)) (n+1) = sumTerms f (n+1) := by
  induction n with
  | zero => simp only [sumTerms]
  | succ n ih =>
    rw [sum_head]
    have h : (fun k => f (n+1-(k+1))) = (fun k => f (n-k)) := by
      funext k
      congr 1
      omega
    rw [h, ih]
    simp only [sumTerms]
    grind

theorem cauchy_zero (a b : Series Rat) : cauchy a b 0 = a 0 * b 0 := by
  simp only [cauchy, sumTerms]
  grind

theorem cauchy_head (a b : Series Rat) (n : Nat) :
    cauchy a b (n+1) = a 0 * b (n+1) + cauchy (fun k => a (k+1)) b n := by
  unfold cauchy
  rw [sum_head]
  congr 1
  apply sumTerms_congr
  intro k hk
  have h : n+1-(k+1) = n-k := by omega
  rw [h]

theorem cauchy_comm (a b : Series Rat) (n : Nat) : cauchy a b n = cauchy b a n := by
  unfold cauchy
  rw [← sum_reverse (fun k => a k * b (n-k)) n]
  apply sumTerms_congr
  intro k hk
  have h : n-(n-k) = k := by omega
  rw [h, Rat.mul_comm]

theorem cauchy_add_left (a b c : Series Rat) (n : Nat) :
    cauchy (fun k => a k+b k) c n = cauchy a c n + cauchy b c n := by
  unfold cauchy
  rw [← sum_add]
  apply sumTerms_congr
  intro k hk
  grind

theorem cauchy_scale_left (r : Rat) (a b : Series Rat) (n : Nat) :
    cauchy (fun k => r*a k) b n = r*cauchy a b n := by
  unfold cauchy
  rw [← sum_scale]
  apply sumTerms_congr
  intro k hk
  grind

theorem cauchy_zero_left (a : Series Rat) (n : Nat) :
    cauchy (fun _ => 0) a n = 0 := by
  unfold cauchy
  have h : (fun k => (0 : Rat)*a (n-k)) = (fun _ => (0 : Rat)) := by
    funext k
    exact Rat.zero_mul _
  rw [h, sum_zero]

theorem cauchy_assoc (a b c : Series Rat) (n : Nat) :
    cauchy (cauchy a b) c n = cauchy a (cauchy b c) n := by
  induction n generalizing a b c with
  | zero => simp only [cauchy_zero]; grind
  | succ n ih =>
    rw [cauchy_head, cauchy_head, cauchy_zero]
    have ht : (fun k => cauchy a b (k+1)) =
        (fun k => a 0*b (k+1)+cauchy (fun j => a (j+1)) b k) := by
      funext k
      exact cauchy_head a b k
    rw [ht, cauchy_add_left, cauchy_scale_left, ih, cauchy_head b c n]
    grind

def const (r : Rat) : Series Rat := fun n => if n=0 then r else 0

theorem cauchy_const_left (r : Rat) (a : Series Rat) (n : Nat) :
    cauchy (const r) a n = r*a n := by
  cases n with
  | zero => rw [cauchy_zero]; rfl
  | succ n =>
    rw [cauchy_head]
    have h : (fun k => const r (k+1)) = (fun _ => (0 : Rat)) := by
      funext k
      simp only [const, Nat.succ_ne_zero, if_false]
    rw [h, cauchy_zero_left]
    simp only [const, if_pos rfl]
    grind

/-- Formal coefficient sequences with the ordinary Cauchy product. -/
@[ext] structure FPS where
  coeff : Nat → Rat

instance : CoeFun FPS (fun _ => Nat → Rat) := ⟨FPS.coeff⟩
def C (r : Rat) : FPS := ⟨const r⟩
def X : FPS := ⟨fun n => if n=1 then 1 else 0⟩
instance : Add FPS := ⟨fun a b => ⟨fun n => a n+b n⟩⟩
instance : Mul FPS := ⟨fun a b => ⟨cauchy a.coeff b.coeff⟩⟩
instance : Neg FPS := ⟨fun a => ⟨fun n => -(a n)⟩⟩
instance : Sub FPS := ⟨fun a b => a + -b⟩
instance : NatCast FPS := ⟨fun n => C n⟩
instance (n : Nat) : OfNat FPS n := ⟨C n⟩
instance : IntCast FPS := ⟨fun n => C n⟩
instance : SMul Nat FPS := ⟨fun n a => C n*a⟩
instance : SMul Int FPS := ⟨fun n a => C n*a⟩
def power (a : FPS) : Nat → FPS
  | 0 => 1
  | n+1 => power a n*a
instance : HPow FPS Nat FPS := ⟨power⟩

theorem add_apply (a b : FPS) (n : Nat) : (a+b) n = a n+b n := rfl
theorem mul_apply (a b : FPS) (n : Nat) : (a*b) n = cauchy a.coeff b.coeff n := rfl
theorem neg_apply (a : FPS) (n : Nat) : (-a) n = -(a n) := rfl
theorem C_zero : C 0 = 0 := rfl
theorem C_one : C 1 = 1 := rfl

theorem C_add (r s : Rat) : C (r+s) = C r+C s := by
  apply FPS.ext
  funext n
  change (if n=0 then r+s else 0) = (if n=0 then r else 0)+(if n=0 then s else 0)
  split <;> grind

theorem C_neg (r : Rat) : C (-r) = -C r := by
  apply FPS.ext
  funext n
  change (if n=0 then -r else 0) = -(if n=0 then r else 0)
  split <;> grind

theorem C_mul (r s : Rat) : C (r*s) = C r*C s := by
  apply FPS.ext
  funext n
  change const (r*s) n = cauchy (const r) (const s) n
  rw [cauchy_const_left]
  unfold const
  split <;> grind

theorem FPS_mul_assoc (a b c : FPS) : a*b*c = a*(b*c) := by
  apply FPS.ext
  funext n
  exact cauchy_assoc a.coeff b.coeff c.coeff n

theorem FPS_mul_comm (a b : FPS) : a*b = b*a := by
  apply FPS.ext
  funext n
  exact cauchy_comm a.coeff b.coeff n

theorem FPS_one_mul (a : FPS) : 1*a = a := by
  apply FPS.ext
  funext n
  change cauchy (const 1) a.coeff n = a n
  rw [cauchy_const_left]
  exact Rat.one_mul _

theorem FPS_right_distrib (a b c : FPS) : (a+b)*c = a*c+b*c := by
  apply FPS.ext
  funext n
  exact cauchy_add_left a.coeff b.coeff c.coeff n

theorem FPS_zero_mul (a : FPS) : 0*a = 0 := by
  apply FPS.ext
  funext n
  change cauchy (const 0) a.coeff n = const 0 n
  rw [cauchy_const_left]
  unfold const
  split <;> grind

instance instFPSRing : Lean.Grind.CommRing FPS where
  add_zero a := by
    apply FPS.ext
    funext n
    change a n + const 0 n = a n
    unfold const
    split <;> grind
  add_comm a b := by
    apply FPS.ext
    funext n
    exact Rat.add_comm (a n) (b n)
  add_assoc a b c := by
    apply FPS.ext
    funext n
    exact Rat.add_assoc (a n) (b n) (c n)
  mul_assoc := FPS_mul_assoc
  mul_comm := FPS_mul_comm
  mul_one a := by rw [FPS_mul_comm, FPS_one_mul]
  one_mul := FPS_one_mul
  right_distrib := FPS_right_distrib
  left_distrib a b c := by rw [FPS_mul_comm a, FPS_right_distrib, FPS_mul_comm b a, FPS_mul_comm c a]
  zero_mul := FPS_zero_mul
  mul_zero a := by rw [FPS_mul_comm, FPS_zero_mul]
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    change C ((n+1 : Nat) : Rat) = C (n : Rat)+C 1
    rw [← C_add]
    congr 1
    grind
  neg_add_cancel a := by
    apply FPS.ext
    funext n
    change -(a n)+a n = const 0 n
    unfold const
    split <;> grind
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i a := by
    apply FPS.ext
    funext n
    change cauchy (const ((-i : Int) : Rat)) a.coeff n = -(cauchy (const (i : Rat)) a.coeff n)
    rw [cauchy_const_left, cauchy_const_left]
    grind
  intCast_neg i := by
    change C ((-i : Int) : Rat) = -C (i : Rat)
    rw [Rat.intCast_neg, C_neg]

#print axioms cauchy_assoc
#print axioms instFPSRing
end StackSorting.CauchyRing
