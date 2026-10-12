import GraphUnitWitness
import LiteralEntryNormalization
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem initial_B_z_0 (y : Chart R) (scale : R) :
    vm (litZ y 0) (litH y (betaDirection y scale)) 0=(litinitialBz y (betaDirection y scale)) 0 0 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_1_0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_2_0)))+((exprEval (chartVars y (fun _ => 0)) dataZ_0_3)*(exprEval (chartVars y (betaDirection y scale)) dataH_3_0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_4_0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))=(exprEval (chartVars y (betaDirection y scale)) datainitialBz_0_0)
  dsimp only [exprEval, chartVars, dataH_0_0, dataH_1_0, dataH_2_0, dataH_3_0, dataH_4_0, dataZ_0_3, datainitialBz_0_0] <;> grind

theorem initial_B_z_1 (y : Chart R) (scale : R) :
    vm (litZ y 0) (litH y (betaDirection y scale)) 1=(litinitialBz y (betaDirection y scale)) 0 1 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_1_1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataZ_0_3)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_4_1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_5_1)))=(exprEval (chartVars y (betaDirection y scale)) (.int 0))
  dsimp only [exprEval, chartVars, dataH_0_1, dataH_1_1, dataH_4_1, dataH_5_1, dataZ_0_3] <;> grind

theorem initial_B_z_2 (y : Chart R) (scale : R) :
    vm (litZ y 0) (litH y (betaDirection y scale)) 2=(litinitialBz y (betaDirection y scale)) 0 2 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_1_2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataZ_0_3)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_4_2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))=(exprEval (chartVars y (betaDirection y scale)) (.int 0))
  dsimp only [exprEval, chartVars, dataH_0_2, dataH_1_2, dataH_4_2, dataZ_0_3] <;> grind

theorem initial_B_z_3 (y : Chart R) (scale : R) :
    vm (litZ y 0) (litH y (betaDirection y scale)) 3=(litinitialBz y (betaDirection y scale)) 0 3 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataZ_0_3)*(exprEval (chartVars y (betaDirection y scale)) dataH_3_3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_5_3)))=(exprEval (chartVars y (betaDirection y scale)) datainitialBz_0_3)
  dsimp only [exprEval, chartVars, dataH_3_3, dataH_5_3, dataZ_0_3, datainitialBz_0_3] <;> grind

theorem initial_B_z_4 (y : Chart R) (scale : R) :
    vm (litZ y 0) (litH y (betaDirection y scale)) 4=(litinitialBz y (betaDirection y scale)) 0 4 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataZ_0_3)*(exprEval (chartVars y (betaDirection y scale)) dataH_3_4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_5_4)))=(exprEval (chartVars y (betaDirection y scale)) datainitialBz_0_4)
  dsimp only [exprEval, chartVars, dataH_3_4, dataH_5_4, dataZ_0_3, datainitialBz_0_4] <;> grind

theorem initial_B_z_5 (y : Chart R) (scale : R) :
    vm (litZ y 0) (litH y (betaDirection y scale)) 5=(litinitialBz y (betaDirection y scale)) 0 5 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataZ_0_3)*(exprEval (chartVars y (betaDirection y scale)) dataH_3_5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_5_5)))=(exprEval (chartVars y (betaDirection y scale)) datainitialBz_0_5)
  dsimp only [exprEval, chartVars, dataH_3_5, dataH_5_5, dataZ_0_3, datainitialBz_0_5] <;> grind

theorem initial_B_z_6 (y : Chart R) (scale : R) :
    vm (litZ y 0) (litH y (betaDirection y scale)) 6=(litinitialBz y (betaDirection y scale)) 0 6 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_6)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_1_6)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_2_6)))+((exprEval (chartVars y (fun _ => 0)) dataZ_0_3)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))=(exprEval (chartVars y (betaDirection y scale)) (.int 0))
  dsimp only [exprEval, chartVars, dataH_0_6, dataH_1_6, dataH_2_6, dataZ_0_3] <;> grind

theorem initial_B_z_7 (y : Chart R) (scale : R) :
    vm (litZ y 0) (litH y (betaDirection y scale)) 7=(litinitialBz y (betaDirection y scale)) 0 7 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_7)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataZ_0_3)*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_4_7)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))=(exprEval (chartVars y (betaDirection y scale)) (.int 0))
  dsimp only [exprEval, chartVars, dataH_0_7, dataH_4_7, dataZ_0_3] <;> grind

theorem initial_B_z_8 (y : Chart R) (scale : R) :
    vm (litZ y 0) (litH y (betaDirection y scale)) 8=(litinitialBz y (betaDirection y scale)) 0 8 := by
  change (((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_0_8)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_1_8)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) (.int 0))))+((exprEval (chartVars y (fun _ => 0)) dataZ_0_3)*(exprEval (chartVars y (betaDirection y scale)) dataH_3_8)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_4_8)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(exprEval (chartVars y (betaDirection y scale)) dataH_5_8)))=(exprEval (chartVars y (betaDirection y scale)) datainitialBz_0_8)
  dsimp only [exprEval, chartVars, dataH_0_8, dataH_1_8, dataH_3_8, dataH_4_8, dataH_5_8, dataZ_0_3, datainitialBz_0_8] <;> grind

end StackSorting.FiniteGraph
