import FPSPowerSeriesBridge
import ScalarLiteral
import DegreeTwelveRationalIrreducible

/-! The original 69-term Core expression and the polynomial certified
irreducible over ℚ(x) are the same polynomial under every commutative
ℚ-algebra interpretation. -/
noncomputable section
namespace StackSorting.MathlibSeriesBridge
open StackSorting.ProperSeries StackSorting.ConcreteEquation
open StackSorting.ConcreteScalar StackSorting.DegreeTwelve
open Polynomial
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

theorem mathEval_powExpr {A : Type*} [CommRing A]
    (c : ℚ →+* A) (e : Expr) (n : ℕ) (x : A) (u : Fin 7 → A) :
    mathEval c (powExpr e n) x u = (mathEval c e x u) ^ n := by
  induction n with
  | zero => simp only [powExpr, mathEval, map_one, pow_zero]
  | succ n ih => simp only [powExpr, mathEval, ih, pow_succ']

/-- Kernel-checked agreement of all 69 literal coefficients and exponents.
The target ring and interpretation of x and G are arbitrary. -/
theorem scalarPolynomial_eval₂_eq_literalQ {A : Type*} [CommRing A]
    (c : ℚ →+* A) (x g : A) :
    StackSorting.DegreeTwelve.scalarPolynomial.eval₂ (Polynomial.eval₂RingHom c x) g =
      mathEval c literalQ x (fun _ => g) := by
  simp only [StackSorting.DegreeTwelve.scalarPolynomial, scalarCoeff0, scalarCoeff1, scalarCoeff2,
    scalarCoeff3, scalarCoeff4, scalarCoeff5, scalarCoeff6, scalarCoeff7,
    scalarCoeff8, scalarCoeff9, scalarCoeff10, scalarCoeff11, scalarCoeff12,
    eval₂_add, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    coe_eval₂RingHom, eval₂_neg, eval₂_ofNat,
    literalQ, sumExpr, mathEval_powExpr, mathEval,
    map_neg, map_ofNat, map_zero]
  ring

#print axioms scalarPolynomial_eval₂_eq_literalQ
end StackSorting.MathlibSeriesBridge
