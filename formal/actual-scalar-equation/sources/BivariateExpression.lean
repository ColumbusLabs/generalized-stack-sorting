import ScalarSeriesCertificate

namespace StackSorting.RationalLift
open StackSorting.CauchyRing

/-- Finite integer polynomial syntax. Evaluation takes place in the proved
Cauchy-product ring, never in a finite quotient or at rational sample points. -/
inductive BiExpr where
  | integer : Int → BiExpr
  | x
  | y
  | add : BiExpr → BiExpr → BiExpr
  | mul : BiExpr → BiExpr → BiExpr

def biEval (x y : FPS) : BiExpr → FPS
  | .integer n => (n : FPS)
  | .x => x
  | .y => y
  | .add p q => biEval x y p + biEval x y q
  | .mul p q => biEval x y p * biEval x y q

end StackSorting.RationalLift
