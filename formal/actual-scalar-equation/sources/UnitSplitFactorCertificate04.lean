import UnitSplitFactorSharedNodes140
import UnitSplitFactorSharedSupport
import UnitSplitFactorData04
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem trans_t_3_8_normalized :
    (reflectRing (.add trans_t_3_8_res (.mul (.int (-1)) (.mul trans_t_3_8_num trans_t_3_8_mul)))).toPoly ==
      (reflectRing (unitSplitWeightedExpr trans_t_3_8_pieces)).toPoly := by
  change (reflectRing usfn1514E).toPoly == (reflectRing usfn1842E).toPoly
  rw [usfn1514_norm, usfn1842_norm]
  decide

theorem trans_t_3_8_factor (e : Nat → R) :
    exprEval e trans_t_3_8_res-(exprEval e trans_t_3_8_num*exprEval e trans_t_3_8_mul)=weightedExprSum e trans_t_3_8_pieces := by
  have h := reflected_polynomial_identity (unitSplitContext e)
    (.add trans_t_3_8_res (.mul (.int (-1)) (.mul trans_t_3_8_num trans_t_3_8_mul)))
    (unitSplitWeightedExpr trans_t_3_8_pieces) trans_t_3_8_normalized
  rw [unitSplitWeightedExpr_eval] at h
  change exprEval e (.add trans_t_3_8_res (.mul (.int (-1)) (.mul trans_t_3_8_num trans_t_3_8_mul)))=
    weightedExprSum e trans_t_3_8_pieces at h
  rw [evalSignedDifference] at h
  exact h

#print axioms trans_t_3_8_normalized
#print axioms trans_t_3_8_factor
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
