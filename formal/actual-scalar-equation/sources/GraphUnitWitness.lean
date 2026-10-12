import GraphLiterals
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem two_half_power (h : R) (hh : 2*h=1) (n : Nat) : (2:R)^n*h^n=1 := by
  induction n with
  | zero => simp only [Lean.Grind.Semiring.pow_zero]; grind
  | succ n ih => simp only [Lean.Grind.Semiring.pow_succ]; grind

/-- Clear only an explicitly displayed power of two, cancelled using the half unit. -/
theorem unitIdealClearZero (n : Nat) (v a ai b bi c ci h w0 w1 w2 w3 : R)
    (ha : a*ai=1) (hb : b*bi=1) (hc : c*ci=1) (hh : 2*h=1)
    (cert : (2:R)^n*v=(2*h-1)*w0+(c*ci-1)*w1+(b*bi-1)*w2+(a*ai-1)*w3) : v=0 := by
  have hz : (2:R)^n*v=0 := by grind
  have hp := two_half_power h hh n
  calc
    v = ((2:R)^n*h^n)*v := by rw [hp]; grind
    _ = h^n*((2:R)^n*v) := by grind
    _ = 0 := by rw [hz]; grind

theorem signedResidual_zero (l r m : R) (hm : m=0) (h : l+(-1)*r-m=0) : l=r := by
  grind

theorem mul_zero_of_left_eq_zero (a b : R) (ha : a=0) : a*b=0 := by
  rw [ha]
  grind

/-- Evaluation of a finite linear combination of exact polynomial coefficients. -/
def weightedExprSum (e : Nat → R) : List (RingExpr × RingExpr) → R
  | [] => 0
  | (w,c)::xs => exprEval e w*exprEval e c+weightedExprSum e xs

def coefficientZeros (e : Nat → R) : List (RingExpr × RingExpr) → Prop
  | [] => True
  | (_,c)::xs => exprEval e c=0 ∧ coefficientZeros e xs

theorem weightedExprSum_zero (e : Nat → R) (xs : List (RingExpr × RingExpr))
    (h : coefficientZeros e xs) : weightedExprSum e xs=0 := by
  induction xs with
  | nil => rfl
  | cons wc xs ih =>
    rcases wc with ⟨w,c⟩
    change exprEval e w*exprEval e c+weightedExprSum e xs=0
    have hc := h.1
    have ht := ih h.2
    rw [hc, ht]
    grind

#print axioms unitIdealClearZero
#print axioms weightedExprSum_zero
end StackSorting.FiniteGraph
