import ReducedWitnessEnvironment
noncomputable section
namespace StackSorting.RationalLift
open StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

def witness_alpha_0_0_0 : RingExpr := (.int (0))

def witness_alpha_0_0_1 : RingExpr := (.int (0))

def witness_alpha_0_0_2 : RingExpr := (.int (0))

def witness_alpha_0_0_3 : RingExpr := (.int (0))

theorem certificate_alpha_0_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 1))-(1)) = (2*env 9-1)*exprEval env witness_alpha_0_0_0 + (env 2*env 8-1)*exprEval env witness_alpha_0_0_1 + (env 1*env 7-1)*exprEval env witness_alpha_0_0_2 + (env 4*env 6-1)*exprEval env witness_alpha_0_0_3 := by
  dsimp only [reducedOriginalVars, witness_alpha_0_0_0, witness_alpha_0_0_1, witness_alpha_0_0_2, witness_alpha_0_0_3, exprEval]
  grind

theorem original_alpha_0_0 (z : ReducedChart R) :
    litalpha (originalChart z) 0 0=reduced_alpha z 0 0 := by
  have h := certificate_alpha_0_0 (reducedVars z)
  change 1*(litalpha (originalChart z) 0 0-reduced_alpha z 0 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_alpha_0_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_alpha_0_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_alpha_0_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_alpha_0_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_alpha_0_1_0 : RingExpr := (.int (0))

def witness_alpha_0_1_1 : RingExpr := (.int (0))

def witness_alpha_0_1_2 : RingExpr := (.int (0))

def witness_alpha_0_1_3 : RingExpr := (.int (0))

theorem certificate_alpha_0_1 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.var 2))-(((-1) * (env 3) * (env 4)))) = (2*env 9-1)*exprEval env witness_alpha_0_1_0 + (env 2*env 8-1)*exprEval env witness_alpha_0_1_1 + (env 1*env 7-1)*exprEval env witness_alpha_0_1_2 + (env 4*env 6-1)*exprEval env witness_alpha_0_1_3 := by
  dsimp only [reducedOriginalVars, witness_alpha_0_1_0, witness_alpha_0_1_1, witness_alpha_0_1_2, witness_alpha_0_1_3, exprEval]
  grind

theorem original_alpha_0_1 (z : ReducedChart R) :
    litalpha (originalChart z) 0 1=reduced_alpha z 0 1 := by
  have h := certificate_alpha_0_1 (reducedVars z)
  change 1*(litalpha (originalChart z) 0 1-reduced_alpha z 0 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_alpha_0_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_alpha_0_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_alpha_0_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_alpha_0_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_alpha_0_2_0 : RingExpr := (.int (0))

def witness_alpha_0_2_1 : RingExpr := (.int (0))

def witness_alpha_0_2_2 : RingExpr := (.int (0))

def witness_alpha_0_2_3 : RingExpr := (.int (0))

theorem certificate_alpha_0_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_alpha_0_2_0 + (env 2*env 8-1)*exprEval env witness_alpha_0_2_1 + (env 1*env 7-1)*exprEval env witness_alpha_0_2_2 + (env 4*env 6-1)*exprEval env witness_alpha_0_2_3 := by
  dsimp only [reducedOriginalVars, witness_alpha_0_2_0, witness_alpha_0_2_1, witness_alpha_0_2_2, witness_alpha_0_2_3, exprEval]
  grind

theorem original_alpha_0_2 (z : ReducedChart R) :
    litalpha (originalChart z) 0 2=reduced_alpha z 0 2 := by
  have h := certificate_alpha_0_2 (reducedVars z)
  change 1*(litalpha (originalChart z) 0 2-reduced_alpha z 0 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_alpha_0_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_alpha_0_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_alpha_0_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_alpha_0_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_alpha_0_3_0 : RingExpr := (.int (0))

def witness_alpha_0_3_1 : RingExpr := (.int (0))

def witness_alpha_0_3_2 : RingExpr := (.int (0))

def witness_alpha_0_3_3 : RingExpr := (.int (0))

theorem certificate_alpha_0_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.int (-1)) (.var 2)))-(((env 3) * (env 4)))) = (2*env 9-1)*exprEval env witness_alpha_0_3_0 + (env 2*env 8-1)*exprEval env witness_alpha_0_3_1 + (env 1*env 7-1)*exprEval env witness_alpha_0_3_2 + (env 4*env 6-1)*exprEval env witness_alpha_0_3_3 := by
  dsimp only [reducedOriginalVars, witness_alpha_0_3_0, witness_alpha_0_3_1, witness_alpha_0_3_2, witness_alpha_0_3_3, exprEval]
  grind

theorem original_alpha_0_3 (z : ReducedChart R) :
    litalpha (originalChart z) 0 3=reduced_alpha z 0 3 := by
  have h := certificate_alpha_0_3 (reducedVars z)
  change 1*(litalpha (originalChart z) 0 3-reduced_alpha z 0 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_alpha_0_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_alpha_0_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_alpha_0_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_alpha_0_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_alpha_0_4_0 : RingExpr := (.int (0))

def witness_alpha_0_4_1 : RingExpr := (.int (0))

def witness_alpha_0_4_2 : RingExpr := (.int (0))

def witness_alpha_0_4_3 : RingExpr := (.int (0))

theorem certificate_alpha_0_4 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.var 3))-((env 4))) = (2*env 9-1)*exprEval env witness_alpha_0_4_0 + (env 2*env 8-1)*exprEval env witness_alpha_0_4_1 + (env 1*env 7-1)*exprEval env witness_alpha_0_4_2 + (env 4*env 6-1)*exprEval env witness_alpha_0_4_3 := by
  dsimp only [reducedOriginalVars, witness_alpha_0_4_0, witness_alpha_0_4_1, witness_alpha_0_4_2, witness_alpha_0_4_3, exprEval]
  grind

theorem original_alpha_0_4 (z : ReducedChart R) :
    litalpha (originalChart z) 0 4=reduced_alpha z 0 4 := by
  have h := certificate_alpha_0_4 (reducedVars z)
  change 1*(litalpha (originalChart z) 0 4-reduced_alpha z 0 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_alpha_0_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_alpha_0_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_alpha_0_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_alpha_0_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_alpha_0_5_0 : RingExpr := (.int (0))

def witness_alpha_0_5_1 : RingExpr := (.int (0))

def witness_alpha_0_5_2 : RingExpr := (.int (0))

def witness_alpha_0_5_3 : RingExpr := (.int (0))

theorem certificate_alpha_0_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.int (-1)) (.var 3)))-(((-1) * (env 4)))) = (2*env 9-1)*exprEval env witness_alpha_0_5_0 + (env 2*env 8-1)*exprEval env witness_alpha_0_5_1 + (env 1*env 7-1)*exprEval env witness_alpha_0_5_2 + (env 4*env 6-1)*exprEval env witness_alpha_0_5_3 := by
  dsimp only [reducedOriginalVars, witness_alpha_0_5_0, witness_alpha_0_5_1, witness_alpha_0_5_2, witness_alpha_0_5_3, exprEval]
  grind

theorem original_alpha_0_5 (z : ReducedChart R) :
    litalpha (originalChart z) 0 5=reduced_alpha z 0 5 := by
  have h := certificate_alpha_0_5 (reducedVars z)
  change 1*(litalpha (originalChart z) 0 5-reduced_alpha z 0 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_alpha_0_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_alpha_0_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_alpha_0_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_alpha_0_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

theorem original_alpha (z : ReducedChart R) : litalpha (originalChart z)=reduced_alpha z := by
  funext r c
  exact (Fin.cases ((Fin.cases (original_alpha_0_0 z) (fun c => (Fin.cases (original_alpha_0_1 z) (fun c => (Fin.cases (original_alpha_0_2 z) (fun c => (Fin.cases (original_alpha_0_3 z) (fun c => (Fin.cases (original_alpha_0_4 z) (fun c => (Fin.cases (original_alpha_0_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.elim0 r)) r)

#print axioms original_alpha
end StackSorting.RationalLift
