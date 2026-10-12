import UnitSplitFactorSharedNodes140
import UnitSplitFactorSharedSupport
import UnitSplitFactorData01
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem trans_z_4_8_normalized :
    (reflectRing (.add trans_z_4_8_res (.mul (.int (-1)) (.mul trans_z_4_8_num trans_z_4_8_mul)))).toPoly ==
      (reflectRing (unitSplitWeightedExpr trans_z_4_8_pieces)).toPoly := by
  change (reflectRing usfn730E).toPoly == (reflectRing usfn1087E).toPoly
  rw [usfn730_norm, usfn1087_norm]
  decide

theorem trans_z_4_8_factor (e : Nat → R) :
    exprEval e trans_z_4_8_res-(exprEval e trans_z_4_8_num*exprEval e trans_z_4_8_mul)=weightedExprSum e trans_z_4_8_pieces := by
  have h := reflected_polynomial_identity (unitSplitContext e)
    (.add trans_z_4_8_res (.mul (.int (-1)) (.mul trans_z_4_8_num trans_z_4_8_mul)))
    (unitSplitWeightedExpr trans_z_4_8_pieces) trans_z_4_8_normalized
  rw [unitSplitWeightedExpr_eval] at h
  change exprEval e (.add trans_z_4_8_res (.mul (.int (-1)) (.mul trans_z_4_8_num trans_z_4_8_mul)))=
    weightedExprSum e trans_z_4_8_pieces at h
  rw [evalSignedDifference] at h
  exact h

#print axioms trans_z_4_8_normalized
#print axioms trans_z_4_8_factor
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
