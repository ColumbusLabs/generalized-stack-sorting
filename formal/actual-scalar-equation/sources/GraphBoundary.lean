import ChartScalars
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem literal_T_row_zero (y : Chart R) (v : Vec R 6) : mv (litT y) v 0=v 2 := by
  change (((((((0 : R)+(exprEval (chartVars y (fun _ => 0)) (.int 0))*v 0)+(exprEval (chartVars y (fun _ => 0)) (.int 0))*v 1)+(exprEval (chartVars y (fun _ => 0)) (.int 1))*v 2)+(exprEval (chartVars y (fun _ => 0)) (.int 0))*v 3)+(exprEval (chartVars y (fun _ => 0)) (.int 0))*v 4)+(exprEval (chartVars y (fun _ => 0)) (.int 0))*v 5)=v 2
  simp only [exprEval] <;> grind

theorem literal_K_row_two (y : Chart R) (v : Vec R 6) : mv (litK y) v 2= -3*v 0 := by
  change (((((((0 : R)+(exprEval (chartVars y (fun _ => 0)) (.int (-3)))*v 0)+(exprEval (chartVars y (fun _ => 0)) (.int 0))*v 1)+(exprEval (chartVars y (fun _ => 0)) (.int 0))*v 2)+(exprEval (chartVars y (fun _ => 0)) (.int 0))*v 3)+(exprEval (chartVars y (fun _ => 0)) (.int 0))*v 4)+(exprEval (chartVars y (fun _ => 0)) (.int 0))*v 5)=-3*v 0
  simp only [exprEval] <;> grind

theorem record_row_zero (y : Chart R) (beta : Vec R 6) :
    recordFromScalar (litT y) (litK y) beta 0=beta 2-2*beta 0 := by
  dsimp [recordFromScalar, exprEval, chartVars]
  rw [literal_T_row_zero, literal_K_row_two]
  grind

def d0 (x : R) (beta : Vec R 6) : R := 1+x*beta 0
def generatingFunction (x : R) (beta : Vec R 6) : R := 1+x*d0 x beta

theorem empty_B_boundary (y : Chart R) (x : R) (beta : Vec R 6)
    (hn : beta 0-x*beta 2=2) : kappa y x beta 0=2*d0 x beta := by
  dsimp [kappa, d0, exprEval, chartVars]
  rw [record_row_zero]
  grind

theorem dot_neg {n} (v w : Vec R n) : dot v (fun i => -w i)= -dot v w := by
  unfold dot
  have h : (fun i => v i * -w i)=(fun i => -(v i*w i)) := by funext i; grind
  rw [h, sumFin_neg]

theorem empty_Z_boundary (y : Chart R) (x : R) (beta : Vec R 6)
    (hs : SevenScalarEquations y x beta) (hn : beta 0-x*beta 2=2) :
    dot (litalpha y 0) (kappa y x beta)=2*d0 x beta := by
  have hk := scalar_constructs_terminal x (litT y) (litK y) beta hs.1
  have heq : kappa y x beta=(fun i => -mv (litK y) beta i) := by
    funext i
    have h := hk i
    dsimp [kappa, exprEval, chartVars]
    grind
  have h0 := empty_B_boundary y x beta hn
  rw [heq] at h0
  rw [heq, dot_neg]
  have h7 := hs.2
  grind

theorem height_one_boundary (y : Chart R) (x : R) (beta : Vec R 6)
    (hn : beta 0-x*beta 2=2) :
    d0 x beta=1+2*x*d0 x beta+x^2*recordFromScalar (litT y) (litK y) beta 0 := by
  dsimp [d0, exprEval, chartVars]
  rw [record_row_zero]
  grind

theorem root_normalization (x : R) (beta : Vec R 6) :
    generatingFunction x beta=1+x+x^2*beta 0 := by
  dsimp [generatingFunction, d0, exprEval, chartVars]
  grind

#print axioms empty_B_boundary
#print axioms empty_Z_boundary
#print axioms height_one_boundary
#print axioms root_normalization
end StackSorting.FiniteGraph
