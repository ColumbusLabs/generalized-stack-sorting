import GraphUnitWitness
import RingReflection
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]
attribute [local instance] Lean.Grind.Ring.intCast

def unitSplitWeightedExpr : List (RingExpr × RingExpr) → RingExpr
  | [] => .int 0
  | (w,c)::xs => .add (.mul w c) (unitSplitWeightedExpr xs)

theorem unitSplitWeightedExpr_eval (env : Nat → R) (xs : List (RingExpr × RingExpr)) :
    exprEval env (unitSplitWeightedExpr xs)=weightedExprSum env xs := by
  induction xs with
  | nil => exact Lean.Grind.Ring.intCast_zero
  | cons wc xs ih =>
    rcases wc with ⟨w,c⟩
    change exprEval env w*exprEval env c+exprEval env (unitSplitWeightedExpr xs)=
      exprEval env w*exprEval env c+weightedExprSum env xs
    rw [ih]

def unitSplitContext (env : Nat → R) : Lean.RArray R := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (env 0)) (.leaf (env 1))) (.branch 3 (.leaf (env 2)) (.leaf (env 3)))) (.branch 6 (.branch 5 (.leaf (env 4)) (.leaf (env 5))) (.branch 7 (.leaf (env 6)) (.branch 8 (.leaf (env 7)) (.leaf (env 8)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (env 9)) (.leaf (env 10))) (.branch 12 (.leaf (env 11)) (.leaf (env 12)))) (.branch 15 (.branch 14 (.leaf (env 13)) (.leaf (env 14))) (.branch 16 (.leaf (env 15)) (.branch 17 (.leaf (env 16)) (.leaf (env 17)))))))

#print axioms unitSplitWeightedExpr_eval
end StackSorting.FiniteGraph
