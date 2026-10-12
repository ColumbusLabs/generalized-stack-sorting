import UnitSplitFactorSharedNodes140
import UnitSplitFactorSharedSupport
import UnitSplitFactorData23
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem quotient_t_9_8_normalized :
    (reflectRing (.add quotient_t_9_8_res (.mul (.int (-1)) (.int 0)))).toPoly ==
      (reflectRing (unitSplitWeightedExpr quotient_t_9_8_pieces)).toPoly := by
  change (reflectRing usfn6033E).toPoly == (reflectRing usfn6177E).toPoly
  rw [usfn6033_norm, usfn6177_norm]
  decide

theorem quotient_t_9_8_factor (e : Nat → R) :
    exprEval e quotient_t_9_8_res-((0 : R))=weightedExprSum e quotient_t_9_8_pieces := by
  have h := reflected_polynomial_identity (unitSplitContext e)
    (.add quotient_t_9_8_res (.mul (.int (-1)) (.int 0)))
    (unitSplitWeightedExpr quotient_t_9_8_pieces) quotient_t_9_8_normalized
  rw [unitSplitWeightedExpr_eval] at h
  change exprEval e (.add quotient_t_9_8_res (.mul (.int (-1)) (.int 0)))=
    weightedExprSum e quotient_t_9_8_pieces at h
  rw [evalSignedDifference] at h
  rw [show exprEval e (.int 0)=(0:R) from Lean.Grind.Ring.intCast_zero] at h
  exact h

#print axioms quotient_t_9_8_normalized
#print axioms quotient_t_9_8_factor
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
