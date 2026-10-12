import UnitSplitFactorSharedNodes140
import UnitSplitFactorSharedSupport
import UnitSplitFactorData06
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem initial_Z_z_8_normalized :
    (reflectRing (.add initial_Z_z_8_res (.mul (.int (-1)) (.mul initial_Z_z_8_num initial_Z_z_8_mul)))).toPoly ==
      (reflectRing (unitSplitWeightedExpr initial_Z_z_8_pieces)).toPoly := by
  change (reflectRing usfn2447E).toPoly == (reflectRing usfn2898E).toPoly
  rw [usfn2447_norm, usfn2898_norm]
  decide

theorem initial_Z_z_8_factor (e : Nat → R) :
    exprEval e initial_Z_z_8_res-(exprEval e initial_Z_z_8_num*exprEval e initial_Z_z_8_mul)=weightedExprSum e initial_Z_z_8_pieces := by
  have h := reflected_polynomial_identity (unitSplitContext e)
    (.add initial_Z_z_8_res (.mul (.int (-1)) (.mul initial_Z_z_8_num initial_Z_z_8_mul)))
    (unitSplitWeightedExpr initial_Z_z_8_pieces) initial_Z_z_8_normalized
  rw [unitSplitWeightedExpr_eval] at h
  change exprEval e (.add initial_Z_z_8_res (.mul (.int (-1)) (.mul initial_Z_z_8_num initial_Z_z_8_mul)))=
    weightedExprSum e initial_Z_z_8_pieces at h
  rw [evalSignedDifference] at h
  exact h

#print axioms initial_Z_z_8_normalized
#print axioms initial_Z_z_8_factor
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
