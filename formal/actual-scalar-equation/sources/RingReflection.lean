import GraphLiterals
import Init.Grind.Ring.CommSolver
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

/-- Reuse Lean's proved multivariate polynomial normalizer, with exact integer casts. -/
def reflectRing : RingExpr → Lean.Grind.CommRing.Expr
  | .int c => .intCast c
  | .var n => .var n
  | .add a b => .add (reflectRing a) (reflectRing b)
  | .mul a b => .mul (reflectRing a) (reflectRing b)
  | .pow a n => .pow (reflectRing a) n

theorem reflectRing_denote (ctx : Lean.RArray R) (e : RingExpr) :
    (reflectRing e).denote ctx=exprEval (fun n => ctx.get n) e := by
  induction e with
  | int c => rfl
  | var n => rfl
  | add a b ha hb =>
    change (reflectRing a).denote ctx+(reflectRing b).denote ctx=_
    rw [ha, hb]
    rfl
  | mul a b ha hb =>
    change (reflectRing a).denote ctx*(reflectRing b).denote ctx=_
    rw [ha, hb]
    rfl
  | pow a n ha =>
    change (reflectRing a).denote ctx^n=_
    rw [ha]
    rfl

theorem reflected_polynomial_identity (ctx : Lean.RArray R) (a b : RingExpr)
    (h : (reflectRing a).toPoly == (reflectRing b).toPoly) :
    exprEval (fun n => ctx.get n) a=exprEval (fun n => ctx.get n) b := by
  have he := Lean.Grind.CommRing.Expr.eq_of_toPoly_eq ctx (reflectRing a) (reflectRing b) h
  rw [reflectRing_denote, reflectRing_denote] at he
  exact he

def substituteRing (sigma : Nat → RingExpr) : RingExpr → RingExpr
  | .int c => .int c
  | .var n => sigma n
  | .add a b => .add (substituteRing sigma a) (substituteRing sigma b)
  | .mul a b => .mul (substituteRing sigma a) (substituteRing sigma b)
  | .pow a n => .pow (substituteRing sigma a) n

theorem eval_substituteRing (e : Nat → R) (sigma : Nat → RingExpr) (a : RingExpr) :
    exprEval e (substituteRing sigma a)=exprEval (fun n => exprEval e (sigma n)) a := by
  induction a with
  | int c => rfl
  | var n => rfl
  | add a b ha hb =>
    change exprEval e (substituteRing sigma a)+exprEval e (substituteRing sigma b)=_
    rw [ha, hb]
    rfl
  | mul a b ha hb =>
    change exprEval e (substituteRing sigma a)*exprEval e (substituteRing sigma b)=_
    rw [ha, hb]
    rfl
  | pow a n ha =>
    change exprEval e (substituteRing sigma a)^n=_
    rw [ha]
    rfl

#print axioms reflected_polynomial_identity
#print axioms eval_substituteRing
end StackSorting.FiniteGraph
