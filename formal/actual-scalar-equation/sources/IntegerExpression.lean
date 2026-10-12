import CauchyRing
namespace StackSorting.RationalLift
open StackSorting.CauchyRing

/-- Explicit finite integer-polynomial syntax avoids elaborating thousands
of overloaded ring operations. Its semantics is the actual FPS ring. -/
inductive IExpr where
  | integer : Int → IExpr
  | var : Nat → IExpr
  | add : IExpr → IExpr → IExpr
  | mul : IExpr → IExpr → IExpr
  | pow : IExpr → Nat → IExpr

def IExpr.eval (v : Nat → FPS) : IExpr → FPS
  | .integer n => (n : FPS)
  | .var n => v n
  | .add a b => a.eval v+b.eval v
  | .mul a b => a.eval v*b.eval v
  | .pow a k => (a.eval v)^k

def polyArgs (a t u i q x y : FPS) : Nat → FPS
  | 0 => a
  | 1 => t
  | 2 => u
  | 3 => i
  | 4 => q
  | 5 => x
  | 6 => y
  | _ => 0
end StackSorting.RationalLift
