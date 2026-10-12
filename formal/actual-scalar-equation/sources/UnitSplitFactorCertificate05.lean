import UnitSplitFactorSharedNodes140
import UnitSplitFactorSharedSupport
import UnitSplitFactorData05
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem trans_t_5_8_normalized :
    (reflectRing (.add trans_t_5_8_res (.mul (.int (-1)) (.mul trans_t_5_8_num trans_t_5_8_mul)))).toPoly ==
      (reflectRing (unitSplitWeightedExpr trans_t_5_8_pieces)).toPoly := by
  change (reflectRing usfn1914E).toPoly == (reflectRing usfn2356E).toPoly
  rw [usfn1914_norm, usfn2356_norm]
  decide

theorem trans_t_5_8_factor (e : Nat → R) :
    exprEval e trans_t_5_8_res-(exprEval e trans_t_5_8_num*exprEval e trans_t_5_8_mul)=weightedExprSum e trans_t_5_8_pieces := by
  have h := reflected_polynomial_identity (unitSplitContext e)
    (.add trans_t_5_8_res (.mul (.int (-1)) (.mul trans_t_5_8_num trans_t_5_8_mul)))
    (unitSplitWeightedExpr trans_t_5_8_pieces) trans_t_5_8_normalized
  rw [unitSplitWeightedExpr_eval] at h
  change exprEval e (.add trans_t_5_8_res (.mul (.int (-1)) (.mul trans_t_5_8_num trans_t_5_8_mul)))=
    weightedExprSum e trans_t_5_8_pieces at h
  rw [evalSignedDifference] at h
  exact h

#print axioms trans_t_5_8_normalized
#print axioms trans_t_5_8_factor
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
