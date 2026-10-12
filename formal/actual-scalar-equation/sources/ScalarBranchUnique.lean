import ScalarSeriesCertificate

namespace StackSorting.ConcreteScalar
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem X_cancel {a b : FPS} (h : X*a = X*b) : a=b := by
  apply FPS.ext
  funext n
  have hc := congrArg FPS.coeff h
  rw [X_mul_coeff, X_mul_coeff] at hc
  exact congrFun hc (n+1)

theorem X_pow_cancel (k : Nat) {a b : FPS} (h : X^k*a = X^k*b) : a=b := by
  induction k with
  | zero => change 1*a=1*b at h; grind
  | succ k ih =>
    change (X^k*X)*a=(X^k*X)*b at h
    have hh : X*(X^k*a)=X*(X^k*b) := by grind
    exact ih (X_cancel hh)

/-- Exact equivalence, inside the specified formal-series ball, between the
literal algebraic equation and the proper scalar fixed-point equation. -/
theorem scalar_ball_equivalence (w : FPS) :
    scalarPolynomialRing X (centerRing X+X^10*w)=0 ↔
      w = X*ringEval rExpr X (fun _ => w) := by
  rw [scalar_reconstruction_ring]
  constructor
  · intro h
    have hz : X^21*(-576*w+576*X*ringEval rExpr X (fun _ => w)) = X^21*0 := by grind
    have hc := X_pow_cancel 21 hz
    have hr := reciprocal576
    have hm : -w+X*ringEval rExpr X (fun _ => w) = 0 := by
      calc
        _ = (576*C ((1 : Rat)/576))*(-w+X*ringEval rExpr X (fun _ => w)) := by rw [hr]; grind
        _ = C ((1 : Rat)/576)*(-576*w+576*X*ringEval rExpr X (fun _ => w)) := by grind
        _ = 0 := by rw [hc]; grind
    grind
  · intro h
    grind

theorem scalar_fixed_unique (w : FPS)
    (hw : w = X*ringEval rExpr X (fun _ => w)) : w=W := by
  have hs : (ringEval rExpr X (fun _ => w)).coeff =
      (scalarR ()).eval (fun _ => w.coeff) := by
    have h := ringEval_coefficient_semantics (scalarR ()) (fun _ => w.coeff)
    change (ringEval (scalarize rExpr) X (fun _ => w)).coeff = _ at h
    rw [scalarize_ringEval] at h
    exact h
  have hc := congrArg FPS.coeff hw
  rw [X_mul_coeff, hs] at hc
  have heq : (fun _ : Unit => w.coeff) = properSolution scalarR := by
    apply fixed_unique (properStep_contracting scalarR)
    · funext i
      cases i
      exact hc.symm
    · exact solution_fixed (properStep_contracting scalarR) (fun _ _ => 0)
  apply FPS.ext
  exact congrFun heq ()

/-- Uniqueness of the algebraic branch in C10+x^10 Q[[x]]. -/
theorem formal_G_branch_unique (w : FPS)
    (h : scalarPolynomialRing X (centerRing X+X^10*w)=0) :
    centerRing X+X^10*w=G := by
  have hw := scalar_fixed_unique w ((scalar_ball_equivalence w).mp h)
  rw [hw]
  rfl

/-- A solution exists, and every solution in the certified ball is this one. -/
theorem formal_G_exists_unique_in_ball :
    scalarPolynomialRing X G=0 ∧
      ∀ w : FPS, scalarPolynomialRing X (centerRing X+X^10*w)=0 →
        centerRing X+X^10*w=G :=
  ⟨formal_G_equation_ring, formal_G_branch_unique⟩

theorem W_constant_zero : W 0=0 := properSolution_zero scalarR ()

theorem X_pow_mul_coeff (k : Nat) (a : FPS) (n : Nat) :
    (X^k*a) n = if n<k then 0 else a (n-k) := by
  induction k generalizing n with
  | zero =>
    have h : X^0*a=a := by change 1*a=a; exact FPS_one_mul a
    rw [h]
    simp
  | succ k ih =>
    have h : X^(k+1)*a = X*(X^k*a) := by
      change (X^k*X)*a=X*(X^k*a)
      grind
    rw [h]
    have hs := congrFun (X_mul_coeff (X^k*a)) n
    cases n with
    | zero =>
      change (X*(X^k*a)) 0 = _
      rw [hs]
      simp only [shift, Nat.zero_lt_succ, if_true]
    | succ n =>
      change (X*(X^k*a)) (n+1) = _
      rw [hs]
      change (X^k*a) n = _
      rw [ih]
      have hl : n+1<k+1 ↔ n<k := by omega
      have he : n+1-(k+1)=n-k := by omega
      simp only [hl, he]

/-- The proper solution agrees with the displayed center through degree ten. -/
theorem G_center_prefix (n : Nat) (hn : n≤10) : G n=(centerRing X) n := by
  change (centerRing X) n+(X^10*W) n=(centerRing X) n
  rw [X_pow_mul_coeff]
  by_cases h : n<10
  · rw [if_pos h]; grind
  · have he : n=10 := by omega
    subst n
    simp only [Nat.lt_irrefl, if_false, Nat.sub_self, W_constant_zero]
    grind

theorem polyEval_X_coeff (p : QPoly.Poly) (n : Nat) :
    (polyEval p X) n = p.getD n 0 := by
  induction p generalizing n with
  | nil =>
    change const 0 n = 0
    unfold const
    split <;> rfl
  | cons c p ih =>
    cases n with
    | zero =>
      change const c 0+(X*polyEval p X) 0=c
      have h := congrFun (X_mul_coeff (polyEval p X)) 0
      rw [h]
      change c+0=c
      grind
    | succ n =>
      change const c (n+1)+(X*polyEval p X) (n+1)=p.getD n 0
      have h := congrFun (X_mul_coeff (polyEval p X)) (n+1)
      rw [h]
      change 0+(polyEval p X) n=p.getD n 0
      rw [ih]
      grind

/-- The center is exactly the eleven literal coefficients in the input. -/
theorem center_coefficients : ∀ n : Fin 11,
    (centerRing X) n.val = center.getD n.val 0 := by
  intro n
  exact polyEval_X_coeff center n.val

/-- Certified prefix, including constant coefficient 1. This is an
algebraic-series prefix, not yet a formal combinatorial identification. -/
theorem G_first_eleven (n : Fin 11) : G n.val = center.getD n.val 0 := by
  rw [G_center_prefix n.val (by omega), center_coefficients n]

#print axioms G_first_eleven

#print axioms scalar_ball_equivalence
#print axioms formal_G_branch_unique
#print axioms formal_G_exists_unique_in_ball
#print axioms G_center_prefix
end StackSorting.ConcreteScalar
