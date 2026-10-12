import GraphTransition_t5_Part05
import UnitSplitFactorCertificates
import DirectionPolynomialIdentities
import GraphUnitWitness
import LiteralEntryNormalization
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem trans_t_5_8_binding (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_t_5_8_res=(((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) dataT_5_0)*(exprEval (chartVars y beta) dataH_0_8)))+((exprEval (chartVars y (fun _ => 0)) dataT_5_1)*(exprEval (chartVars y beta) dataH_1_8)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y beta) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataT_5_3)*(exprEval (chartVars y beta) dataH_3_8)))+((exprEval (chartVars y (fun _ => 0)) dataT_5_4)*(exprEval (chartVars y beta) dataH_4_8)))+((exprEval (chartVars y (fun _ => 0)) dataT_5_5)*(exprEval (chartVars y beta) dataH_5_8)))+(-1)*(((((((((((0 : R)+((exprEval (chartVars y beta) (.int 0))*(exprEval (chartVars y beta) (.int 0))))+((exprEval (chartVars y beta) dataH_5_1)*(exprEval (chartVars y beta) (.int 0))))+((exprEval (chartVars y beta) (.int 0))*(exprEval (chartVars y beta) (.int 0))))+((exprEval (chartVars y beta) dataH_5_3)*(exprEval (chartVars y beta) dataN9t_3_8)))+((exprEval (chartVars y beta) dataH_5_4)*(exprEval (chartVars y beta) dataN9t_4_8)))+((exprEval (chartVars y beta) dataH_5_5)*(exprEval (chartVars y beta) dataN9t_5_8)))+((exprEval (chartVars y beta) (.int 0))*(exprEval (chartVars y beta) (.int 0))))+((exprEval (chartVars y beta) (.int 0))*(exprEval (chartVars y beta) (.int 0))))+((exprEval (chartVars y beta) dataH_5_8)*(exprEval (chartVars y beta) (.int 0))))-(exprEval (chartVars y beta) dataCSt_5_8)) := by
  dsimp only [trans_t_5_8_res, exprEval, chartVars, dataCSt_5_8, dataH_0_8, dataH_1_8, dataH_3_8, dataH_4_8, dataH_5_1, dataH_5_3, dataH_5_4, dataH_5_5, dataH_5_8, dataN9t_3_8, dataN9t_4_8, dataN9t_5_8, dataT_5_0, dataT_5_1, dataT_5_3, dataT_5_4, dataT_5_5] <;> grind

theorem trans_t_5_8_num_zero (y : Chart R) (scale : R) :
    exprEval (chartVars y (betaDirection y scale)) trans_t_5_8_num=0 := by
  exact certified_trans_t_5_8_zero y scale

theorem trans_t_5_8 (y : Chart R) (scale : R) :
    mm (litT y) (litH y (betaDirection y scale)) 5 8=mm (litH y (betaDirection y scale)) (litN9t y (betaDirection y scale)) 5 8-litCSt y (betaDirection y scale) 5 8 := by
  have hz := trans_t_5_8_zero y (betaDirection y scale)
  have hn := mul_zero_of_left_eq_zero _ (exprEval (chartVars y (betaDirection y scale)) trans_t_5_8_mul) (trans_t_5_8_num_zero y scale)
  rw [trans_t_5_8_binding] at hz
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) dataT_5_0)*(exprEval (chartVars y (betaDirection y scale)) dataH_0_8)))+((exprEval (chartVars y (fun _ => 0)) dataT_5_1)*(exprEval (chartVars y (betaDirection y scale)) dataH_1_8)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataT_5_3)*(exprEval (chartVars y (betaDirection y scale)) dataH_3_8)))+((exprEval (chartVars y (fun _ => 0)) dataT_5_4)*(exprEval (chartVars y (betaDirection y scale)) dataH_4_8)))+((exprEval (chartVars y (fun _ => 0)) dataT_5_5)*(exprEval (chartVars y (betaDirection y scale)) dataH_5_8)))=(((((((((((0 : R)+((exprEval (chartVars y (betaDirection y scale)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (betaDirection y scale)) dataH_5_1)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (betaDirection y scale)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (betaDirection y scale)) dataH_5_3)*(exprEval (chartVars y (betaDirection y scale)) dataN9t_3_8)))+((exprEval (chartVars y (betaDirection y scale)) dataH_5_4)*(exprEval (chartVars y (betaDirection y scale)) dataN9t_4_8)))+((exprEval (chartVars y (betaDirection y scale)) dataH_5_5)*(exprEval (chartVars y (betaDirection y scale)) dataN9t_5_8)))+((exprEval (chartVars y (betaDirection y scale)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (betaDirection y scale)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (betaDirection y scale)) dataH_5_8)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))-(exprEval (chartVars y (betaDirection y scale)) dataCSt_5_8))
  exact signedResidual_zero _ _ _ hn hz

end StackSorting.FiniteGraph
