import SignedSuffixEvaluation
noncomputable section
namespace StackSorting.FiniteGraph
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem selected_z_0 (y : Chart R) (s : SuffixChannels R) :
    mv (litCz y) (packChannels s) 0=s.f 0 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 0
  simp only [exprEval, chartVars] <;> grind

theorem selected_z_1 (y : Chart R) (s : SuffixChannels R) :
    mv (litCz y) (packChannels s) 1=s.f 1 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 1
  simp only [exprEval, chartVars] <;> grind

theorem selected_z_2 (y : Chart R) (s : SuffixChannels R) :
    mv (litCz y) (packChannels s) 2=s.f 2 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 2
  simp only [exprEval, chartVars] <;> grind

theorem selected_z_3 (y : Chart R) (s : SuffixChannels R) :
    mv (litCz y) (packChannels s) 3=s.f 3 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 3
  simp only [exprEval, chartVars] <;> grind

theorem selected_z_4 (y : Chart R) (s : SuffixChannels R) :
    mv (litCz y) (packChannels s) 4=s.f 4 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 4
  simp only [exprEval, chartVars] <;> grind

theorem selected_z_5 (y : Chart R) (s : SuffixChannels R) :
    mv (litCz y) (packChannels s) 5=s.f 5 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 5
  simp only [exprEval, chartVars] <;> grind

theorem selected_b_0 (y : Chart R) (s : SuffixChannels R) :
    mv (litCb y) (packChannels s) 0=s.f 0+s.k 0 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 0+s.k 0
  simp only [exprEval, chartVars] <;> grind

theorem selected_b_1 (y : Chart R) (s : SuffixChannels R) :
    mv (litCb y) (packChannels s) 1=s.f 1+s.k 1 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 1+s.k 1
  simp only [exprEval, chartVars] <;> grind

theorem selected_b_2 (y : Chart R) (s : SuffixChannels R) :
    mv (litCb y) (packChannels s) 2=s.f 2+s.k 2 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 2+s.k 2
  simp only [exprEval, chartVars] <;> grind

theorem selected_b_3 (y : Chart R) (s : SuffixChannels R) :
    mv (litCb y) (packChannels s) 3=s.f 3+s.k 3 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 3+s.k 3
  simp only [exprEval, chartVars] <;> grind

theorem selected_b_4 (y : Chart R) (s : SuffixChannels R) :
    mv (litCb y) (packChannels s) 4=s.f 4+s.k 4 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 4+s.k 4
  simp only [exprEval, chartVars] <;> grind

theorem selected_b_5 (y : Chart R) (s : SuffixChannels R) :
    mv (litCb y) (packChannels s) 5=s.f 5+s.k 5 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 5+s.k 5
  simp only [exprEval, chartVars] <;> grind

theorem selected_t_0 (y : Chart R) (s : SuffixChannels R) :
    mv (litCt y) (packChannels s) 0=s.f 0+s.k 0 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 0+s.k 0
  simp only [exprEval, chartVars] <;> grind

theorem selected_t_1 (y : Chart R) (s : SuffixChannels R) :
    mv (litCt y) (packChannels s) 1=s.f 1+s.k 1 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 1+s.k 1
  simp only [exprEval, chartVars] <;> grind

theorem selected_t_2 (y : Chart R) (s : SuffixChannels R) :
    mv (litCt y) (packChannels s) 2=s.f 2+s.k 2 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 2+s.k 2
  simp only [exprEval, chartVars] <;> grind

theorem selected_t_3 (y : Chart R) (s : SuffixChannels R) :
    mv (litCt y) (packChannels s) 3=s.f 3+s.k 3 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 3+s.k 3
  simp only [exprEval, chartVars] <;> grind

theorem selected_t_4 (y : Chart R) (s : SuffixChannels R) :
    mv (litCt y) (packChannels s) 4=s.f 4+s.k 4 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 4+s.k 4
  simp only [exprEval, chartVars] <;> grind

theorem selected_t_5 (y : Chart R) (s : SuffixChannels R) :
    mv (litCt y) (packChannels s) 5=s.f 5+s.k 5 := by
  change ((((((((((((((((((((0 : R)+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4)))+((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 5)))+((exprEval (chartVars y (fun _ => 0)) (.int 0))*s.e))=s.f 5+s.k 5
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_0 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 0 0=packChannels (channelBase beta) 0 := by
  change (exprEval (chartVars y beta) (.var 11))=beta 0
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_1 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 1 0=packChannels (channelBase beta) 1 := by
  change (exprEval (chartVars y beta) (.var 12))=beta 1
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_2 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 2 0=packChannels (channelBase beta) 2 := by
  change (exprEval (chartVars y beta) (.var 13))=beta 2
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_3 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 3 0=packChannels (channelBase beta) 3 := by
  change (exprEval (chartVars y beta) (.var 14))=beta 3
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_4 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 4 0=packChannels (channelBase beta) 4 := by
  change (exprEval (chartVars y beta) (.var 15))=beta 4
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_5 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 5 0=packChannels (channelBase beta) 5 := by
  change (exprEval (chartVars y beta) (.var 16))=beta 5
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_6 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 6 0=packChannels (channelBase beta) 6 := by
  change (exprEval (chartVars y beta) (.var 11))=beta 0
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_7 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 7 0=packChannels (channelBase beta) 7 := by
  change (exprEval (chartVars y beta) (.var 12))=beta 1
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_8 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 8 0=packChannels (channelBase beta) 8 := by
  change (exprEval (chartVars y beta) (.var 13))=beta 2
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_9 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 9 0=packChannels (channelBase beta) 9 := by
  change (exprEval (chartVars y beta) (.var 14))=beta 3
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_10 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 10 0=packChannels (channelBase beta) 10 := by
  change (exprEval (chartVars y beta) (.var 15))=beta 4
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_11 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 11 0=packChannels (channelBase beta) 11 := by
  change (exprEval (chartVars y beta) (.var 16))=beta 5
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_12 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 12 0=packChannels (channelBase beta) 12 := by
  change (exprEval (chartVars y beta) (.int 0))=(0 : R)
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_13 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 13 0=packChannels (channelBase beta) 13 := by
  change (exprEval (chartVars y beta) (.int 0))=(0 : R)
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_14 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 14 0=packChannels (channelBase beta) 14 := by
  change (exprEval (chartVars y beta) (.int 0))=(0 : R)
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_15 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 15 0=packChannels (channelBase beta) 15 := by
  change (exprEval (chartVars y beta) (.int 0))=(0 : R)
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_16 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 16 0=packChannels (channelBase beta) 16 := by
  change (exprEval (chartVars y beta) (.int 0))=(0 : R)
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_17 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 17 0=packChannels (channelBase beta) 17 := by
  change (exprEval (chartVars y beta) (.int 0))=(0 : R)
  simp only [exprEval, chartVars] <;> grind

theorem channel_base_18 (y : Chart R) (beta : Vec R 6) :
    litnu19 y beta 18 0=packChannels (channelBase beta) 18 := by
  change (exprEval (chartVars y beta) (.int 1))=(1 : R)
  simp only [exprEval, chartVars] <;> grind

end StackSorting.FiniteGraph
