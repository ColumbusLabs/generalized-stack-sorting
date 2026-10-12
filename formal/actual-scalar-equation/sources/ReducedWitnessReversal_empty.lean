import ReducedReversalData
import ChangedPolynomials
import CoordinatePolynomials
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def revWitness_empty_0 : RingExpr := (.int (0))

def revWitness_empty_1 : RingExpr := (.int (0))

def revWitness_empty_2 : RingExpr := (.mul (.int (12)) (.mul (.var 3) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.mul (.add (.int (-1)) (.mul (.int (2)) (.var 2))) (.mul (.add (.int (-1)) (.mul (.var 4) (.pow (.var 3) 2))) (.add (.int (-1)) (.mul (.int (2)) (.mul (.var 0) (.var 1))))))))))

def revWitness_empty_3 : RingExpr := (.int (0))

theorem reversalCertificate_empty (env : Nat → FPS) :
    1*(dot (env_alpha env 0) (mv (env_K env) (fun j => env_direction env j 0))-mv (env_K env) (fun j => env_direction env j 0) 0) = (2*env 9-1)*exprEval env revWitness_empty_0 + (env 2*env 8-1)*exprEval env revWitness_empty_1 + (env 1*env 7-1)*exprEval env revWitness_empty_2 + (env 4*env 6-1)*exprEval env revWitness_empty_3 := by
  change 1*((((((((0 : FPS)+((1 : FPS)*(((((((0 : FPS)+((entry_K_0_0 env)*(entry_direction_0_0 env)))+((entry_K_0_1 env)*(entry_direction_1_0 env)))+((0 : FPS)*(entry_direction_2_0 env)))+((0 : FPS)*(entry_direction_3_0 env)))+((entry_K_0_4 env)*(entry_direction_4_0 env)))+((0 : FPS)*(entry_direction_5_0 env)))))+((entry_alpha_0_1 env)*(((((((0 : FPS)+(((-3) : FPS)*(entry_direction_0_0 env)))+((0 : FPS)*(entry_direction_1_0 env)))+((0 : FPS)*(entry_direction_2_0 env)))+((0 : FPS)*(entry_direction_3_0 env)))+((0 : FPS)*(entry_direction_4_0 env)))+((0 : FPS)*(entry_direction_5_0 env)))))+((0 : FPS)*(((((((0 : FPS)+(((-3) : FPS)*(entry_direction_0_0 env)))+((0 : FPS)*(entry_direction_1_0 env)))+((0 : FPS)*(entry_direction_2_0 env)))+((0 : FPS)*(entry_direction_3_0 env)))+((0 : FPS)*(entry_direction_4_0 env)))+((0 : FPS)*(entry_direction_5_0 env)))))+((entry_alpha_0_3 env)*(((((((0 : FPS)+(((-3) : FPS)*(entry_direction_0_0 env)))+((entry_K_3_1 env)*(entry_direction_1_0 env)))+((0 : FPS)*(entry_direction_2_0 env)))+((entry_K_3_3 env)*(entry_direction_3_0 env)))+((entry_K_3_4 env)*(entry_direction_4_0 env)))+((entry_K_3_5 env)*(entry_direction_5_0 env)))))+((entry_alpha_0_4 env)*(((((((0 : FPS)+((entry_K_4_0 env)*(entry_direction_0_0 env)))+((entry_K_4_1 env)*(entry_direction_1_0 env)))+((0 : FPS)*(entry_direction_2_0 env)))+((0 : FPS)*(entry_direction_3_0 env)))+((entry_K_4_4 env)*(entry_direction_4_0 env)))+((0 : FPS)*(entry_direction_5_0 env)))))+((entry_alpha_0_5 env)*(((((((0 : FPS)+((entry_K_5_0 env)*(entry_direction_0_0 env)))+((entry_K_5_1 env)*(entry_direction_1_0 env)))+((0 : FPS)*(entry_direction_2_0 env)))+(((-2) : FPS)*(entry_direction_3_0 env)))+((entry_K_5_4 env)*(entry_direction_4_0 env)))+((0 : FPS)*(entry_direction_5_0 env)))))-(((((((0 : FPS)+((entry_K_0_0 env)*(entry_direction_0_0 env)))+((entry_K_0_1 env)*(entry_direction_1_0 env)))+((0 : FPS)*(entry_direction_2_0 env)))+((0 : FPS)*(entry_direction_3_0 env)))+((entry_K_0_4 env)*(entry_direction_4_0 env)))+((0 : FPS)*(entry_direction_5_0 env)))) = (2*env 9-1)*exprEval env revWitness_empty_0 + (env 2*env 8-1)*exprEval env revWitness_empty_1 + (env 1*env 7-1)*exprEval env revWitness_empty_2 + (env 4*env 6-1)*exprEval env revWitness_empty_3
  dsimp [entry_T_1_0, entry_T_1_1, entry_T_1_2, entry_T_1_4, entry_T_2_0, entry_T_2_1, entry_T_2_2, entry_T_2_4, entry_T_3_1, entry_T_3_3, entry_T_3_4, entry_T_3_5, entry_T_4_0, entry_T_4_1, entry_T_4_2, entry_T_4_4, entry_T_5_0, entry_T_5_1, entry_T_5_3, entry_T_5_4, entry_T_5_5, entry_K_0_0, entry_K_0_1, entry_K_0_4, entry_K_3_1, entry_K_3_3, entry_K_3_4, entry_K_3_5, entry_K_4_0, entry_K_4_1, entry_K_4_4, entry_K_5_0, entry_K_5_1, entry_K_5_4, entry_direction_0_0, entry_direction_1_0, entry_direction_2_0, entry_direction_3_0, entry_direction_4_0, entry_direction_5_0, entry_den_0_0, entry_alpha_0_1, entry_alpha_0_3, entry_alpha_0_4, entry_alpha_0_5, revWitness_empty_0, revWitness_empty_1, revWitness_empty_2, revWitness_empty_3, exprEval, changedP0, changedP0Expr, changedP1, changedP1Expr, changedP2, changedP2Expr, changedP3, changedP3Expr, changedP4, changedP4Expr, changedP5, changedP5Expr, cDen, cDenExpr, cNum, cNumExpr, IExpr.eval, polyArgs]
  grind

#print axioms reversalCertificate_empty
end StackSorting.RationalLift
