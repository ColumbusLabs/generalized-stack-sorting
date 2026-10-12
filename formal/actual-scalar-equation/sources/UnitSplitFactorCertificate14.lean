import UnitSplitFactorSharedNodes140
import UnitSplitFactorSharedSupport
import UnitSplitFactorData14
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem quotient_b_2_0_normalized :
    (reflectRing (.add quotient_b_2_0_res (.mul (.int (-1)) (.int 0)))).toPoly ==
      (reflectRing (unitSplitWeightedExpr quotient_b_2_0_pieces)).toPoly := by
  change (reflectRing usfn5602E).toPoly == (reflectRing usfn3891E).toPoly
  rw [usfn5602_norm, usfn3891_norm]
  decide

theorem quotient_b_2_0_factor (e : Nat → R) :
    exprEval e quotient_b_2_0_res-((0 : R))=weightedExprSum e quotient_b_2_0_pieces := by
  have h := reflected_polynomial_identity (unitSplitContext e)
    (.add quotient_b_2_0_res (.mul (.int (-1)) (.int 0)))
    (unitSplitWeightedExpr quotient_b_2_0_pieces) quotient_b_2_0_normalized
  rw [unitSplitWeightedExpr_eval] at h
  change exprEval e (.add quotient_b_2_0_res (.mul (.int (-1)) (.int 0)))=
    weightedExprSum e quotient_b_2_0_pieces at h
  rw [evalSignedDifference] at h
  rw [show exprEval e (.int 0)=(0:R) from Lean.Grind.Ring.intCast_zero] at h
  exact h

#print axioms quotient_b_2_0_normalized
#print axioms quotient_b_2_0_factor
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
