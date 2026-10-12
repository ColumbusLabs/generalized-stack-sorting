import ScalarIdentity
import SeriesPolynomialSemantics

namespace StackSorting.ConcreteScalar
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def centerRing (x : FPS) : FPS := polyEval center x
def scalarPolynomialRing (x g : FPS) : FPS := ringEval f0 x (fun _ => g)

theorem scalar_taylor_ring (x c t : FPS) :
    scalarPolynomialRing x (c+t) =
      ringEval f0 x (fun _ => c) * t^0 +
      ringEval f1 x (fun _ => c) * t^1 +
      ringEval f2 x (fun _ => c) * t^2 +
      ringEval f3 x (fun _ => c) * t^3 +
      ringEval f4 x (fun _ => c) * t^4 +
      ringEval f5 x (fun _ => c) * t^5 +
      ringEval f6 x (fun _ => c) * t^6 +
      ringEval f7 x (fun _ => c) * t^7 +
      ringEval f8 x (fun _ => c) * t^8 +
      ringEval f9 x (fun _ => c) * t^9 +
      ringEval f10 x (fun _ => c) * t^10 +
      ringEval f11 x (fun _ => c) * t^11 +
      ringEval f12 x (fun _ => c) * t^12 := by
  simp only [scalarPolynomialRing, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, ringEval, expression_ringEval]
  change ((1 : FPS)*polyEval q0 x + (c+t)*((1 : FPS)*polyEval q1 x + (c+t)*((1 : FPS)*polyEval q2 x + (c+t)*((1 : FPS)*polyEval q3 x + (c+t)*((1 : FPS)*polyEval q4 x + (c+t)*((1 : FPS)*polyEval q5 x + (c+t)*((1 : FPS)*polyEval q6 x + (c+t)*((1 : FPS)*polyEval q7 x + (c+t)*((1 : FPS)*polyEval q8 x + (c+t)*((1 : FPS)*polyEval q9 x + (c+t)*((1 : FPS)*polyEval q10 x + (c+t)*((1 : FPS)*polyEval q11 x + (c+t)*((1 : FPS)*polyEval q12 x + (c+t)*(0 : FPS)))))))))))))) = ((1 : FPS)*polyEval q0 x + (c)*((1 : FPS)*polyEval q1 x + (c)*((1 : FPS)*polyEval q2 x + (c)*((1 : FPS)*polyEval q3 x + (c)*((1 : FPS)*polyEval q4 x + (c)*((1 : FPS)*polyEval q5 x + (c)*((1 : FPS)*polyEval q6 x + (c)*((1 : FPS)*polyEval q7 x + (c)*((1 : FPS)*polyEval q8 x + (c)*((1 : FPS)*polyEval q9 x + (c)*((1 : FPS)*polyEval q10 x + (c)*((1 : FPS)*polyEval q11 x + (c)*((1 : FPS)*polyEval q12 x + (c)*(0 : FPS))))))))))))))*t^0 + ((1 : FPS)*polyEval q1 x + (c)*((2 : FPS)*polyEval q2 x + (c)*((3 : FPS)*polyEval q3 x + (c)*((4 : FPS)*polyEval q4 x + (c)*((5 : FPS)*polyEval q5 x + (c)*((6 : FPS)*polyEval q6 x + (c)*((7 : FPS)*polyEval q7 x + (c)*((8 : FPS)*polyEval q8 x + (c)*((9 : FPS)*polyEval q9 x + (c)*((10 : FPS)*polyEval q10 x + (c)*((11 : FPS)*polyEval q11 x + (c)*((12 : FPS)*polyEval q12 x + (c)*(0 : FPS)))))))))))))*t^1 + ((1 : FPS)*polyEval q2 x + (c)*((3 : FPS)*polyEval q3 x + (c)*((6 : FPS)*polyEval q4 x + (c)*((10 : FPS)*polyEval q5 x + (c)*((15 : FPS)*polyEval q6 x + (c)*((21 : FPS)*polyEval q7 x + (c)*((28 : FPS)*polyEval q8 x + (c)*((36 : FPS)*polyEval q9 x + (c)*((45 : FPS)*polyEval q10 x + (c)*((55 : FPS)*polyEval q11 x + (c)*((66 : FPS)*polyEval q12 x + (c)*(0 : FPS))))))))))))*t^2 + ((1 : FPS)*polyEval q3 x + (c)*((4 : FPS)*polyEval q4 x + (c)*((10 : FPS)*polyEval q5 x + (c)*((20 : FPS)*polyEval q6 x + (c)*((35 : FPS)*polyEval q7 x + (c)*((56 : FPS)*polyEval q8 x + (c)*((84 : FPS)*polyEval q9 x + (c)*((120 : FPS)*polyEval q10 x + (c)*((165 : FPS)*polyEval q11 x + (c)*((220 : FPS)*polyEval q12 x + (c)*(0 : FPS)))))))))))*t^3 + ((1 : FPS)*polyEval q4 x + (c)*((5 : FPS)*polyEval q5 x + (c)*((15 : FPS)*polyEval q6 x + (c)*((35 : FPS)*polyEval q7 x + (c)*((70 : FPS)*polyEval q8 x + (c)*((126 : FPS)*polyEval q9 x + (c)*((210 : FPS)*polyEval q10 x + (c)*((330 : FPS)*polyEval q11 x + (c)*((495 : FPS)*polyEval q12 x + (c)*(0 : FPS))))))))))*t^4 + ((1 : FPS)*polyEval q5 x + (c)*((6 : FPS)*polyEval q6 x + (c)*((21 : FPS)*polyEval q7 x + (c)*((56 : FPS)*polyEval q8 x + (c)*((126 : FPS)*polyEval q9 x + (c)*((252 : FPS)*polyEval q10 x + (c)*((462 : FPS)*polyEval q11 x + (c)*((792 : FPS)*polyEval q12 x + (c)*(0 : FPS)))))))))*t^5 + ((1 : FPS)*polyEval q6 x + (c)*((7 : FPS)*polyEval q7 x + (c)*((28 : FPS)*polyEval q8 x + (c)*((84 : FPS)*polyEval q9 x + (c)*((210 : FPS)*polyEval q10 x + (c)*((462 : FPS)*polyEval q11 x + (c)*((924 : FPS)*polyEval q12 x + (c)*(0 : FPS))))))))*t^6 + ((1 : FPS)*polyEval q7 x + (c)*((8 : FPS)*polyEval q8 x + (c)*((36 : FPS)*polyEval q9 x + (c)*((120 : FPS)*polyEval q10 x + (c)*((330 : FPS)*polyEval q11 x + (c)*((792 : FPS)*polyEval q12 x + (c)*(0 : FPS)))))))*t^7 + ((1 : FPS)*polyEval q8 x + (c)*((9 : FPS)*polyEval q9 x + (c)*((45 : FPS)*polyEval q10 x + (c)*((165 : FPS)*polyEval q11 x + (c)*((495 : FPS)*polyEval q12 x + (c)*(0 : FPS))))))*t^8 + ((1 : FPS)*polyEval q9 x + (c)*((10 : FPS)*polyEval q10 x + (c)*((55 : FPS)*polyEval q11 x + (c)*((220 : FPS)*polyEval q12 x + (c)*(0 : FPS)))))*t^9 + ((1 : FPS)*polyEval q10 x + (c)*((11 : FPS)*polyEval q11 x + (c)*((66 : FPS)*polyEval q12 x + (c)*(0 : FPS))))*t^10 + ((1 : FPS)*polyEval q11 x + (c)*((12 : FPS)*polyEval q12 x + (c)*(0 : FPS)))*t^11 + ((1 : FPS)*polyEval q12 x + (c)*(0 : FPS))*t^12
  grind

theorem f0_ring_exact (x : FPS) (u : Fin 7 → FPS) :
    scalarPolynomialRing x (centerRing x) = x^22 * ringEval a0 x u := by
  exact splitAt_ring_divisible 22 centerFamily f0 remainder0 x u

theorem f1_ring_exact (x : FPS) (u : Fin 7 → FPS) :
    ringEval f1 x (fun _ => centerRing x) =
      -576*x^11 + x^12*ringEval a1 x u := by
  have h := splitAt_ring_exact 12 centerFamily f1 x u
  rw [remainder1] at h
  have hz : polyEval (List.replicate 11 0 ++ [(-576 : Rat)]) x = -576*x^11 := by
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, polyEval, C_neg, C_zero, C_one]
    have hc : C (576 : Rat) = (576 : FPS) := rfl
    rw [hc]
    grind
  rw [hz] at h
  exact h

theorem f2_ring_exact (x : FPS) (u : Fin 7 → FPS) :
    ringEval f2 x (fun _ => centerRing x) = x^2*ringEval a2 x u := by
  exact splitAt_ring_divisible 2 centerFamily f2 remainder2 x u

theorem powExpr_ringEval (e : Expr) (n : Nat) (x : FPS) (u : Fin 7 → FPS) :
    ringEval (powExpr e n) x u = (ringEval e x u)^n := by
  induction n with
  | zero => simp only [powExpr, ringEval, C_one]; grind
  | succ n ih => simp only [powExpr, ringEval, ih]; grind

theorem reciprocal576 : (576 : FPS)*C ((1 : Rat)/576) = 1 := by
  change C (576 : Rat)*C ((1 : Rat)/576) = C 1
  rw [← C_mul]
  congr 1
  decide +kernel

/-- The concrete reconstruction identity now holds in the actual Cauchy
ring of formal coefficient sequences. -/
theorem scalar_reconstruction_ring (x w : FPS) :
    scalarPolynomialRing x (centerRing x + x^10*w) =
      x^21*(-576*w + 576*x*ringEval rExpr x (fun _ => w)) := by
  have ht := scalar_taylor_ring x (centerRing x) (x^10*w)
  have h0 := f0_ring_exact x (fun _ => w)
  have h1 := f1_ring_exact x (fun _ => w)
  have h2 := f2_ring_exact x (fun _ => w)
  unfold scalarPolynomialRing at h0
  rw [h0, h1, h2] at ht
  simp only [rExpr, sumExpr, ringEval, powExpr_ringEval, substitute_ringEval, expression_ringEval, C_zero, C_one]
  simp only [centerRing] at *
  have hcancel := reciprocal576
  grind

theorem scalarize_ringEval (e : Expr) (x w : FPS) :
    ringEval (scalarize e) x (fun _ => w) = ringEval e x (fun _ => w) := by
  induction e with
  | scalar c => rfl
  | x => rfl
  | unknown i => rfl
  | add a b ha hb => simp only [scalarize, ringEval, ha, hb]
  | mul a b ha hb => simp only [scalarize, ringEval, ha, hb]
  | neg a ha => simp only [scalarize, ringEval, ha]

/-- The actual coefficient-recursive formal solution. -/
def W : FPS := ⟨properSolution scalarR ()⟩

theorem W_fixed : W = X*ringEval rExpr X (fun _ => W) := by
  apply FPS.ext
  have hf : (fun i : Unit => (⟨properSolution scalarR i⟩ : FPS)) = (fun _ => W) := by
    funext i
    cases i
    rfl
  have hs := ringEval_coefficient_semantics (scalarR ()) (properSolution scalarR)
  rw [hf] at hs
  change (ringEval (scalarize rExpr) X (fun _ => W)).coeff = _ at hs
  rw [scalarize_ringEval] at hs
  rw [X_mul_coeff, hs]
  exact properSolution_equation scalarR ()

/-- The scalar generating-series branch certified here. Its identification
with permutation counts is not part of this Lean theorem. -/
def G : FPS := centerRing X + X^10*W

/-- The literal 69-term polynomial annihilates the constructed formal series. -/
theorem formal_G_equation_ring : scalarPolynomialRing X G = 0 := by
  change scalarPolynomialRing X (centerRing X+X^10*W) = 0
  rw [scalar_reconstruction_ring]
  have hw := W_fixed
  grind

/-- The same conclusion stated directly in the original finite Cauchy
coefficient semantics, at every degree with no finite cutoff. -/
theorem formal_G_equation : f0.eval (fun _ => G.coeff) = (fun _ => (0 : Rat)) := by
  have h := ringEval_coefficient_semantics f0 (fun _ => G.coeff)
  change (scalarPolynomialRing X G).coeff = _ at h
  rw [formal_G_equation_ring] at h
  rw [← h]
  funext n
  change const 0 n = 0
  simp only [const]
  split <;> rfl

#print axioms scalar_reconstruction_ring
#print axioms W_fixed
#print axioms formal_G_equation_ring
#print axioms formal_G_equation
end StackSorting.ConcreteScalar
