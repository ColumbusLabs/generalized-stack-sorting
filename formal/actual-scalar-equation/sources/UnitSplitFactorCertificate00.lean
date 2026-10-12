import UnitSplitFactorSharedNodes140
import UnitSplitFactorSharedSupport
import UnitSplitFactorData00
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem trans_z_1_8_normalized :
    (reflectRing (.add trans_z_1_8_res (.mul (.int (-1)) (.int 0)))).toPoly ==
      (reflectRing (unitSplitWeightedExpr trans_z_1_8_pieces)).toPoly := by
  change (reflectRing usfn349E).toPoly == (reflectRing usfn645E).toPoly
  rw [usfn349_norm, usfn645_norm]
  decide

theorem trans_z_1_8_factor (e : Nat → R) :
    exprEval e trans_z_1_8_res-((0 : R))=weightedExprSum e trans_z_1_8_pieces := by
  have h := reflected_polynomial_identity (unitSplitContext e)
    (.add trans_z_1_8_res (.mul (.int (-1)) (.int 0)))
    (unitSplitWeightedExpr trans_z_1_8_pieces) trans_z_1_8_normalized
  rw [unitSplitWeightedExpr_eval] at h
  change exprEval e (.add trans_z_1_8_res (.mul (.int (-1)) (.int 0)))=
    weightedExprSum e trans_z_1_8_pieces at h
  rw [evalSignedDifference] at h
  rw [show exprEval e (.int 0)=(0:R) from Lean.Grind.Ring.intCast_zero] at h
  exact h

#print axioms trans_z_1_8_normalized
#print axioms trans_z_1_8_factor
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
