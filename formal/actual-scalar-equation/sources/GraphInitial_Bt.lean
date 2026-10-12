import GraphUnitWitness
import LiteralEntryNormalization
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem initial_B_t_0 (y : Chart R) (scale : R) :
    vm (litT y 0) (litH y (betaDirection y scale)) 0=(litinitialBt y) 0 0 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_1_0)))+((exprEval (chartVars y (fun _ => 0)) dataT_0_2)*(exprEval (chartVars y (betaDirection y scale)) dataH_2_0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_3_0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_4_0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))=(exprEval (chartVars y (fun _ => 0)) datainitialBt_0_0)
  dsimp only [exprEval, chartVars, dataH_0_0, dataH_1_0, dataH_2_0, dataH_3_0, dataH_4_0, dataT_0_2, datainitialBt_0_0] <;> grind

theorem initial_B_t_1 (y : Chart R) (scale : R) :
    vm (litT y 0) (litH y (betaDirection y scale)) 1=(litinitialBt y) 0 1 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_1_1)))+((exprEval (chartVars y (fun _ => 0)) dataT_0_2)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_4_1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_5_1)))=(exprEval (chartVars y (fun _ => 0)) (.int 0))
  dsimp only [exprEval, chartVars, dataH_0_1, dataH_1_1, dataH_4_1, dataH_5_1, dataT_0_2] <;> grind

theorem initial_B_t_2 (y : Chart R) (scale : R) :
    vm (litT y 0) (litH y (betaDirection y scale)) 2=(litinitialBt y) 0 2 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_1_2)))+((exprEval (chartVars y (fun _ => 0)) dataT_0_2)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_4_2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))=(exprEval (chartVars y (fun _ => 0)) (.int 0))
  dsimp only [exprEval, chartVars, dataH_0_2, dataH_1_2, dataH_4_2, dataT_0_2] <;> grind

theorem initial_B_t_3 (y : Chart R) (scale : R) :
    vm (litT y 0) (litH y (betaDirection y scale)) 3=(litinitialBt y) 0 3 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataT_0_2)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_3_3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_5_3)))=(exprEval (chartVars y (fun _ => 0)) (.int 0))
  dsimp only [exprEval, chartVars, dataH_3_3, dataH_5_3, dataT_0_2] <;> grind

theorem initial_B_t_4 (y : Chart R) (scale : R) :
    vm (litT y 0) (litH y (betaDirection y scale)) 4=(litinitialBt y) 0 4 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataT_0_2)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_3_4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_5_4)))=(exprEval (chartVars y (fun _ => 0)) (.int 0))
  dsimp only [exprEval, chartVars, dataH_3_4, dataH_5_4, dataT_0_2] <;> grind

theorem initial_B_t_5 (y : Chart R) (scale : R) :
    vm (litT y 0) (litH y (betaDirection y scale)) 5=(litinitialBt y) 0 5 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataT_0_2)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_3_5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_5_5)))=(exprEval (chartVars y (fun _ => 0)) (.int 0))
  dsimp only [exprEval, chartVars, dataH_3_5, dataH_5_5, dataT_0_2] <;> grind

theorem initial_B_t_6 (y : Chart R) (scale : R) :
    vm (litT y 0) (litH y (betaDirection y scale)) 6=(litinitialBt y) 0 6 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_6)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_1_6)))+((exprEval (chartVars y (fun _ => 0)) dataT_0_2)*(exprEval (chartVars y (betaDirection y scale)) dataH_2_6)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))=(exprEval (chartVars y (fun _ => 0)) datainitialBt_0_6)
  dsimp only [exprEval, chartVars, dataH_0_6, dataH_1_6, dataH_2_6, dataT_0_2, datainitialBt_0_6] <;> grind

theorem initial_B_t_7 (y : Chart R) (scale : R) :
    vm (litT y 0) (litH y (betaDirection y scale)) 7=(litinitialBt y) 0 7 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_7)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataT_0_2)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_4_7)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))=(exprEval (chartVars y (fun _ => 0)) (.int 0))
  dsimp only [exprEval, chartVars, dataH_0_7, dataH_4_7, dataT_0_2] <;> grind

theorem initial_B_t_8 (y : Chart R) (scale : R) :
    vm (litT y 0) (litH y (betaDirection y scale)) 8=(litinitialBt y) 0 8 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_8)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_1_8)))+((exprEval (chartVars y (fun _ => 0)) dataT_0_2)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_3_8)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_4_8)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_5_8)))=(exprEval (chartVars y (fun _ => 0)) (.int 0))
  dsimp only [exprEval, chartVars, dataH_0_8, dataH_1_8, dataH_3_8, dataH_4_8, dataH_5_8, dataT_0_2] <;> grind

end StackSorting.FiniteGraph
