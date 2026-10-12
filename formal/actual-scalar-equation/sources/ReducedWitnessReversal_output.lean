import ReducedReversalData
import ChangedPolynomials
import CoordinatePolynomials
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def revWitness_output_0 : RingExpr := (.int (0))

def revWitness_output_1 : RingExpr := (.int (0))

def revWitness_output_2 : RingExpr := (.int (0))

def revWitness_output_3 : RingExpr := (.int (0))

theorem reversalCertificate_output (env : Nat → FPS) :
    1*(cDen (env 0) (env 1) (env 2) (env 3) (env 4) (env 10)*((env 11-1-env 10)*(env_den env 0 0-env 10*env_direction env 2 0)-2*(env 10)^2*env_den env 0 0)-4*env 0*(env 4)^2*env 2*(changedP5 (env 0) (env 1) (env 2) (env 3) (env 4) (env 10) (env 11))-12*env 0*(env 4)^2*env 2*env 10*(2*env 2-1)*(env 11-1-env 10)*(cDen (env 0) (env 1) (env 2) (env 3) (env 4) (env 10)*env 5-cNum (env 0) (env 1) (env 2) (env 3) (env 4) (env 10))) = (2*env 9-1)*exprEval env revWitness_output_0 + (env 2*env 8-1)*exprEval env revWitness_output_1 + (env 1*env 7-1)*exprEval env revWitness_output_2 + (env 4*env 6-1)*exprEval env revWitness_output_3 := by
  change 1*(cDen (env 0) (env 1) (env 2) (env 3) (env 4) (env 10)*((env 11-1-env 10)*((entry_den_0_0 env)-env 10*(entry_direction_2_0 env))-2*(env 10)^2*(entry_den_0_0 env))-4*env 0*(env 4)^2*env 2*(changedP5 (env 0) (env 1) (env 2) (env 3) (env 4) (env 10) (env 11))-12*env 0*(env 4)^2*env 2*env 10*(2*env 2-1)*(env 11-1-env 10)*(cDen (env 0) (env 1) (env 2) (env 3) (env 4) (env 10)*env 5-cNum (env 0) (env 1) (env 2) (env 3) (env 4) (env 10))) = (2*env 9-1)*exprEval env revWitness_output_0 + (env 2*env 8-1)*exprEval env revWitness_output_1 + (env 1*env 7-1)*exprEval env revWitness_output_2 + (env 4*env 6-1)*exprEval env revWitness_output_3
  dsimp [entry_T_1_0, entry_T_1_1, entry_T_1_2, entry_T_1_4, entry_T_2_0, entry_T_2_1, entry_T_2_2, entry_T_2_4, entry_T_3_1, entry_T_3_3, entry_T_3_4, entry_T_3_5, entry_T_4_0, entry_T_4_1, entry_T_4_2, entry_T_4_4, entry_T_5_0, entry_T_5_1, entry_T_5_3, entry_T_5_4, entry_T_5_5, entry_K_0_0, entry_K_0_1, entry_K_0_4, entry_K_3_1, entry_K_3_3, entry_K_3_4, entry_K_3_5, entry_K_4_0, entry_K_4_1, entry_K_4_4, entry_K_5_0, entry_K_5_1, entry_K_5_4, entry_direction_0_0, entry_direction_1_0, entry_direction_2_0, entry_direction_3_0, entry_direction_4_0, entry_direction_5_0, entry_den_0_0, entry_alpha_0_1, entry_alpha_0_3, entry_alpha_0_4, entry_alpha_0_5, revWitness_output_0, revWitness_output_1, revWitness_output_2, revWitness_output_3, exprEval, changedP0, changedP0Expr, changedP1, changedP1Expr, changedP2, changedP2Expr, changedP3, changedP3Expr, changedP4, changedP4Expr, changedP5, changedP5Expr, cDen, cDenExpr, cNum, cNumExpr, IExpr.eval, polyArgs]
  grind

#print axioms reversalCertificate_output
end StackSorting.RationalLift
