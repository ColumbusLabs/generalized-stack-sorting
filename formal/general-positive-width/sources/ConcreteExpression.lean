import PolynomialProperSystem
import Init.GrindInstances.Ring.Rat

namespace StackSorting.ConcreteEquation
open StackSorting.ProperSeries
abbrev Expr := PolyExpr (Fin 7) Rat

def powExpr (e : Expr) : Nat → Expr
  | 0 => .scalar 1
  | n+1 => .mul e (powExpr e n)

def sumExpr : List Expr → Expr
  | [] => .scalar 0
  | e :: es => .add e (sumExpr es)

def substitute (e : Expr) (v : Fin 7 → Expr) : Expr :=
  match e with
  | .scalar c => .scalar c
  | .x => .x
  | .unknown i => v i
  | .add a b => .add (substitute a v) (substitute b v)
  | .mul a b => .mul (substitute a v) (substitute b v)
  | .neg a => .neg (substitute a v)

/-- Evaluation at rational points is used only for polynomial identities;
formal-series semantics remains PolyExpr.eval. -/
def pointEval (e : Expr) (x : Rat) (u : Fin 7 → Rat) : Rat :=
  match e with
  | .scalar c => c
  | .x => x
  | .unknown i => u i
  | .add a b => pointEval a x u + pointEval b x u
  | .mul a b => pointEval a x u * pointEval b x u
  | .neg a => -(pointEval a x u)

def zeroX : Expr → Expr
  | .scalar c => .scalar c
  | .x => .scalar 0
  | .unknown i => .unknown i
  | .add a b => .add (zeroX a) (zeroX b)
  | .mul a b => .mul (zeroX a) (zeroX b)
  | .neg a => .neg (zeroX a)

/-- Polynomial quotient after removing the x=0 remainder, with no division
operation and no choice of a root. It remains a finite polynomial expression. -/
def quotientX : Expr → Expr
  | .scalar _ => .scalar 0
  | .x => .scalar 1
  | .unknown _ => .scalar 0
  | .add a b => .add (quotientX a) (quotientX b)
  | .mul a b => .add (.mul (quotientX a) b) (.mul (zeroX a) (quotientX b))
  | .neg a => .neg (quotientX a)

def divideX : Nat → Expr → Expr
  | 0, e => e
  | n+1, e => divideX n (quotientX e)

theorem zeroX_eval (e : Expr) (x : Rat) (u : Fin 7 → Rat) :
    pointEval (zeroX e) x u = pointEval e 0 u := by
  induction e with
  | scalar c => rfl
  | x => rfl
  | unknown i => rfl
  | add a b ha hb => simp only [zeroX, pointEval, ha, hb]
  | mul a b ha hb => simp only [zeroX, pointEval, ha, hb]
  | neg a ha => simp only [zeroX, pointEval, ha]

theorem quotientX_identity (e : Expr) (x : Rat) (u : Fin 7 → Rat) :
    pointEval e x u = pointEval e 0 u + x * pointEval (quotientX e) x u := by
  induction e with
  | scalar c => simp only [pointEval, quotientX]; grind
  | x => simp only [pointEval, quotientX]; grind
  | unknown i => simp only [pointEval, quotientX]; grind
  | add a b ha hb => simp only [pointEval, quotientX]; grind
  | mul a b ha hb =>
    simp only [pointEval, quotientX, zeroX_eval]
    grind
  | neg a ha => simp only [pointEval, quotientX]; grind

/-- If and only if the exact remainder vanishes, the deterministic recipe is
an exact x quotient. No remainder-zero hypotheses are silently assumed. -/
theorem quotientX_exact (e : Expr) (h : ∀ u, pointEval e 0 u = 0)
    (x : Rat) (u : Fin 7 → Rat) :
    pointEval e x u = x * pointEval (quotientX e) x u := by
  rw [quotientX_identity e x u, h u, Rat.zero_add]

#print axioms quotientX_identity
#print axioms quotientX_exact
end StackSorting.ConcreteEquation
