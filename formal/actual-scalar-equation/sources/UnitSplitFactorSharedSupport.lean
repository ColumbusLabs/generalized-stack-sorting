import UnitSplitFactorSupport
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]
attribute [local instance] Lean.Grind.Ring.intCast

theorem evalSignedDifference (e : Nat → R) (a b : RingExpr) :
    exprEval e (.add a (.mul (.int (-1)) b))=exprEval e a-exprEval e b := by
  dsimp only [exprEval]
  grind

#print axioms evalSignedDifference
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
