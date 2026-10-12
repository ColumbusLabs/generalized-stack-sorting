import ReducedWitnessEnvironment
noncomputable section
namespace StackSorting.RationalLift
open StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

def witness_den_0_0_0 : RingExpr := (.int (0))

def witness_den_0_0_1 : RingExpr := (.int (0))

def witness_den_0_0_2 : RingExpr := (.mul (.int (-8)) (.mul (.var 2) (.mul (.pow (.var 4) 4) (.mul (.pow (.var 6) 2) (.mul (.add (.int (-1)) (.mul (.int (3)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 6) (.var 1)))))) (.add (.int (-1)) (.add (.mul (.int (2)) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))) (.mul (.int (2)) (.mul (.var 1) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))))))))))))

def witness_den_0_0_3 : RingExpr := (.mul (.int (-8)) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.add (.int (1)) (.add (.mul (.int (-2)) (.var 2)) (.add (.mul (.var 4) (.var 6)) (.add (.mul (.int (-3)) (.mul (.var 0) (.var 1))) (.add (.mul (.int (-2)) (.mul (.var 4) (.mul (.var 6) (.var 2)))) (.add (.mul (.int (-2)) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))) (.add (.mul (.int (-2)) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))) (.add (.mul (.int (6)) (.mul (.var 0) (.mul (.var 1) (.var 2)))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 6) (.var 1))))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2))))) (.add (.mul (.int (6)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 6) (.mul (.var 1) (.var 2)))))) (.add (.mul (.int (6)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))))) (.add (.mul (.int (6)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))))) (.mul (.int (6)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 4) 4) (.pow (.var 6) 4))))))))))))))))))))))

theorem certificate_den_0_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4)))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 12) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 16) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2)))) (.add (.mul (.int 24) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 48) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 48) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int (-64)) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-40)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))) (.add (.mul (.int (-24)) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))) (.add (.mul (.int 24) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 24) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 7) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 72) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 96) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3)))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.mul (.int 96) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))))))))))))))))))))))))))))-((((-8) * (env 2) * ((env 4)^2)) + (16 * ((env 4)^2) * ((env 2)^2)) + ((-48) * (env 0) * (env 1) * ((env 4)^2) * ((env 2)^2)) + (24 * (env 0) * (env 1) * (env 2) * ((env 4)^2))))) = (2*env 9-1)*exprEval env witness_den_0_0_0 + (env 2*env 8-1)*exprEval env witness_den_0_0_1 + (env 1*env 7-1)*exprEval env witness_den_0_0_2 + (env 4*env 6-1)*exprEval env witness_den_0_0_3 := by
  dsimp only [reducedOriginalVars, witness_den_0_0_0, witness_den_0_0_1, witness_den_0_0_2, witness_den_0_0_3, exprEval]
  grind

theorem original_den_0_0 (z : ReducedChart R) :
    litden (originalChart z) 0 0=reduced_den z 0 0 := by
  have h := certificate_den_0_0 (reducedVars z)
  change 1*(litden (originalChart z) 0 0-reduced_den z 0 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_den_0_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_den_0_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_den_0_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_den_0_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

theorem original_den (z : ReducedChart R) : litden (originalChart z)=reduced_den z := by
  funext r c
  exact (Fin.cases ((Fin.cases (original_den_0_0 z) (fun c => (Fin.elim0 c)) c)) (fun r => (Fin.elim0 r)) r)

#print axioms original_den
end StackSorting.RationalLift
