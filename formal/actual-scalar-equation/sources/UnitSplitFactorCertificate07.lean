import UnitSplitFactorSharedNodes140
import UnitSplitFactorSharedSupport
import UnitSplitFactorData07
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem initial_Z_t_8_normalized :
    (reflectRing (.add initial_Z_t_8_res (.mul (.int (-1)) (.int 0)))).toPoly ==
      (reflectRing (unitSplitWeightedExpr initial_Z_t_8_pieces)).toPoly := by
  change (reflectRing usfn2953E).toPoly == (reflectRing usfn3379E).toPoly
  rw [usfn2953_norm, usfn3379_norm]
  decide

theorem initial_Z_t_8_factor (e : Nat → R) :
    exprEval e initial_Z_t_8_res-((0 : R))=weightedExprSum e initial_Z_t_8_pieces := by
  have h := reflected_polynomial_identity (unitSplitContext e)
    (.add initial_Z_t_8_res (.mul (.int (-1)) (.int 0)))
    (unitSplitWeightedExpr initial_Z_t_8_pieces) initial_Z_t_8_normalized
  rw [unitSplitWeightedExpr_eval] at h
  change exprEval e (.add initial_Z_t_8_res (.mul (.int (-1)) (.int 0)))=
    weightedExprSum e initial_Z_t_8_pieces at h
  rw [evalSignedDifference] at h
  rw [show exprEval e (.int 0)=(0:R) from Lean.Grind.Ring.intCast_zero] at h
  exact h

#print axioms initial_Z_t_8_normalized
#print axioms initial_Z_t_8_factor
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
