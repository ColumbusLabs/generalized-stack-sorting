import SignedWordBoundaryEvaluation
import LiteralResidualDefinitions

/-! Exact literal pF/pJ/pK binding. Every 19-coordinate equality is checked
against the literal source expressions; no row-identity hypothesis is used. -/
noncomputable section
namespace StackSorting.SignedWord
open StackSorting.FiniteGraph
attribute [local instance] Lean.Grind.Ring.intCast
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
variable {R : Type} [Lean.Grind.CommRing R]

def originRow : Vec R 6 := fun i => if i.val = 0 then 1 else 0

theorem dot_originRow (v : Vec R 6) : dot originRow v = v 0 := by
  change (((((((0:R)+1*v 0)+0*v 1)+0*v 2)+0*v 3)+0*v 4)+0*v 5)=v 0
  grind

theorem literal_boundary_F_z (y : Chart R) (s : SuffixChannels R) :
    dot (boundaryF y .z) (packChannels s) = dot (litalpha y 0) s.j := by
  change ((((((((((((((((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.j 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2))*(s.j 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2)))*(s.j 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3))*(s.j 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3)))*(s.j 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.e))) = (((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 1)) * (s.j 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2)) * (s.j 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0)) * (s.j 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2))) * (s.j 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3)) * (s.j 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3))) * (s.j 5)))
  simp only [exprEval, chartVars] <;> grind

theorem literal_boundary_F_b (y : Chart R) (s : SuffixChannels R) :
    dot (boundaryF y .b) (packChannels s) = dot (litalpha y 0) s.f + dot (litalpha y 0) s.k := by
  change ((((((((((((((((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2))*(s.f 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2)))*(s.f 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3))*(s.f 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3)))*(s.f 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2))*(s.k 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2)))*(s.k 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3))*(s.k 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3)))*(s.k 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.e))) = (((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 1)) * (s.f 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2)) * (s.f 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0)) * (s.f 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2))) * (s.f 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3)) * (s.f 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3))) * (s.f 5))) + (((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 1)) * (s.k 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2)) * (s.k 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0)) * (s.k 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2))) * (s.k 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3)) * (s.k 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3))) * (s.k 5)))
  simp only [exprEval, chartVars] <;> grind

theorem literal_boundary_F_t (y : Chart R) (s : SuffixChannels R) :
    dot (boundaryF y .t) (packChannels s) = s.f 0 + dot (litalpha y 0) s.k := by
  change ((((((((((((((((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.f 0))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 1))*(s.k 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2))*(s.k 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2)))*(s.k 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3))*(s.k 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3)))*(s.k 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.e))) = s.f 0 + (((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 1)) * (s.k 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2)) * (s.k 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0)) * (s.k 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2))) * (s.k 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3)) * (s.k 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3))) * (s.k 5)))
  simp only [exprEval, chartVars] <;> grind

theorem literal_boundary_J_z (y : Chart R) (beta : Vec R 6) (s : SuffixChannels R) :
    dot (boundaryJ y beta .z) (packChannels s) = dot (litalpha y 0) beta * s.e := by
  change ((((((((((((((((((((0 : R) + ((exprEval (chartVars y beta) (.int 0))*(s.f 0))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 2))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 3))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 4))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 5))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 0))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 2))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 3))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 4))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 5))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 0))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 2))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 3))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 4))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 5))) + ((exprEval (chartVars y beta) (.add (.var 11) (.add (.mul (.var 12) (.var 2)) (.add (.mul (.var 15) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 14) (.var 2))) (.mul (.int (-1)) (.mul (.var 16) (.var 3))))))))*(s.e))) = ((((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 1)) * (beta 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2)) * (beta 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0)) * (beta 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2))) * (beta 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3)) * (beta 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3))) * (beta 5))))*s.e
  simp only [exprEval, chartVars] <;> grind

theorem literal_boundary_J_b (y : Chart R) (beta : Vec R 6) (s : SuffixChannels R) :
    dot (boundaryJ y beta .b) (packChannels s) = beta 0*s.e := by
  change ((((((((((((((((((((0 : R) + ((exprEval (chartVars y beta) (.int 0))*(s.f 0))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 2))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 3))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 4))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 5))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 0))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 2))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 3))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 4))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 5))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 0))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 2))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 3))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 4))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 5))) + ((exprEval (chartVars y beta) (.var 11))*(s.e))) = beta 0*s.e
  simp only [exprEval, chartVars] <;> grind

theorem literal_boundary_J_t (y : Chart R) (beta : Vec R 6) (s : SuffixChannels R) :
    dot (boundaryJ y beta .t) (packChannels s) = dot (litalpha y 0) s.j + (beta 0-dot (litalpha y 0) beta)*s.e := by
  change ((((((((((((((((((((0 : R) + ((exprEval (chartVars y beta) (.int 0))*(s.f 0))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 2))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 3))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 4))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 5))) + ((exprEval (chartVars y beta) (.int 1))*(s.j 0))) + ((exprEval (chartVars y beta) (.var 2))*(s.j 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 2))) + ((exprEval (chartVars y beta) (.mul (.int (-1)) (.var 2)))*(s.j 3))) + ((exprEval (chartVars y beta) (.var 3))*(s.j 4))) + ((exprEval (chartVars y beta) (.mul (.int (-1)) (.var 3)))*(s.j 5))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 0))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 2))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 3))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 4))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 5))) + ((exprEval (chartVars y beta) (.add (.mul (.var 14) (.var 2)) (.add (.mul (.var 16) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 12) (.var 2))) (.mul (.int (-1)) (.mul (.var 15) (.var 3)))))))*(s.e))) = (((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 1)) * (s.j 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2)) * (s.j 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0)) * (s.j 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2))) * (s.j 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3)) * (s.j 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3))) * (s.j 5))) + (beta 0-((((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 1)) * (beta 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2)) * (beta 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0)) * (beta 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2))) * (beta 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3)) * (beta 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3))) * (beta 5)))))*s.e
  simp only [exprEval, chartVars] <;> grind

theorem literal_boundary_K_z (y : Chart R) (beta : Vec R 6) (s : SuffixChannels R) :
    dot (boundaryK y beta .z) (packChannels s) = 0 := by
  change ((((((((((((((((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 3))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 4))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.e))) = 0
  simp only [exprEval, chartVars] <;> grind

theorem literal_boundary_K_b (y : Chart R) (beta : Vec R 6) (s : SuffixChannels R) :
    dot (boundaryK y beta .b) (packChannels s) = (beta 0-dot (litalpha y 0) beta)*s.e := by
  change ((((((((((((((((((((0 : R) + ((exprEval (chartVars y beta) (.int 0))*(s.f 0))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 2))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 3))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 4))) + ((exprEval (chartVars y beta) (.int 0))*(s.f 5))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 0))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 2))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 3))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 4))) + ((exprEval (chartVars y beta) (.int 0))*(s.j 5))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 0))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 1))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 2))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 3))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 4))) + ((exprEval (chartVars y beta) (.int 0))*(s.k 5))) + ((exprEval (chartVars y beta) (.add (.mul (.var 14) (.var 2)) (.add (.mul (.var 16) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 12) (.var 2))) (.mul (.int (-1)) (.mul (.var 15) (.var 3)))))))*(s.e))) = (beta 0-((((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 1)) * (beta 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2)) * (beta 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0)) * (beta 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2))) * (beta 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3)) * (beta 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3))) * (beta 5)))))*s.e
  simp only [exprEval, chartVars] <;> grind

theorem literal_boundary_K_t (y : Chart R) (beta : Vec R 6) (s : SuffixChannels R) :
    dot (boundaryK y beta .t) (packChannels s) = s.k 0-dot (litalpha y 0) s.k := by
  change ((((((((((((((((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 0))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 2))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 3))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 4))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.f 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 0))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 2))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 3))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 4))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.j 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 0))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2)))*(s.k 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.k 2))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2))*(s.k 3))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3)))*(s.k 4))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3))*(s.k 5))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0))*(s.e))) = s.k 0-((((((((0 : R) + ((exprEval (chartVars y (fun _ => 0)) (.int 1)) * (s.k 0))) + ((exprEval (chartVars y (fun _ => 0)) (.var 2)) * (s.k 1))) + ((exprEval (chartVars y (fun _ => 0)) (.int 0)) * (s.k 2))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 2))) * (s.k 3))) + ((exprEval (chartVars y (fun _ => 0)) (.var 3)) * (s.k 4))) + ((exprEval (chartVars y (fun _ => 0)) (.mul (.int (-1)) (.var 3))) * (s.k 5))))
  simp only [exprEval, chartVars] <;> grind

theorem literal_boundary_F_pack (y : Chart R) (a : Letter) (s : SuffixChannels R) :
    dot (boundaryF y a) (packChannels s) = match a with
      | .z => dot (litalpha y 0) s.j
      | .b => dot (litalpha y 0) s.f + dot (litalpha y 0) s.k
      | .t => s.f 0 + dot (litalpha y 0) s.k := by
  cases a with
  | z => exact literal_boundary_F_z y s
  | b => exact literal_boundary_F_b y s
  | t => exact literal_boundary_F_t y s

theorem literal_boundary_F_concrete (y : Chart R) (beta : Vec R 6) (d0 : R)
    (a : Letter) (w : Word) :
    dot (boundaryF y a) (packChannels (evalChannels y beta w)) =
      eval (boundaryValue y beta (litalpha y 0) originRow d0) (F (a::w)) := by
  rw [←concrete_four_channel_evaluation, literal_boundary_F_pack, boundary_F_cons]
  cases a <;> simp only [evaluatedChannels, dot_sub_left, dot_originRow]

#print axioms literal_boundary_F_concrete

theorem literal_boundary_J_pack (y : Chart R) (beta : Vec R 6) (a : Letter) (s : SuffixChannels R) :
    dot (boundaryJ y beta a) (packChannels s) = match a with
      | .z => dot (litalpha y 0) beta*s.e
      | .b => beta 0*s.e
      | .t => dot (litalpha y 0) s.j + (beta 0-dot (litalpha y 0) beta)*s.e := by
  cases a with
  | z => exact literal_boundary_J_z y beta s
  | b => exact literal_boundary_J_b y beta s
  | t => exact literal_boundary_J_t y beta s

theorem literal_boundary_J_concrete (y : Chart R) (beta : Vec R 6) (d0 : R)
    (a : Letter) (w : Word) :
    dot (boundaryJ y beta a) (packChannels (evalChannels y beta w)) =
      eval (boundaryValue y beta (litalpha y 0) originRow d0) (J (a::w)) := by
  rw [←concrete_four_channel_evaluation, literal_boundary_J_pack, boundary_J_cons]
  cases a <;> simp only [evaluatedChannels, dot_sub_left, dot_originRow]

#print axioms literal_boundary_J_concrete

theorem literal_boundary_K_pack (y : Chart R) (beta : Vec R 6) (a : Letter) (s : SuffixChannels R) :
    dot (boundaryK y beta a) (packChannels s) = match a with
      | .z => 0
      | .b => (beta 0-dot (litalpha y 0) beta)*s.e
      | .t => s.k 0-dot (litalpha y 0) s.k := by
  cases a with
  | z => exact literal_boundary_K_z y beta s
  | b => exact literal_boundary_K_b y beta s
  | t => exact literal_boundary_K_t y beta s

theorem literal_boundary_K_concrete (y : Chart R) (beta : Vec R 6) (d0 : R)
    (a : Letter) (w : Word) :
    dot (boundaryK y beta a) (packChannels (evalChannels y beta w)) =
      eval (boundaryValue y beta (litalpha y 0) originRow d0) (K (a::w)) := by
  rw [←concrete_four_channel_evaluation, literal_boundary_K_pack, boundary_K_cons]
  cases a <;> simp only [evaluatedChannels, dot_sub_left, dot_originRow]

#print axioms literal_boundary_K_concrete

end StackSorting.SignedWord
