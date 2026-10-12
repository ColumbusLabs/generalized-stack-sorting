import ReducedWitnessEnvironment
noncomputable section
namespace StackSorting.RationalLift
open StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

def witness_K_0_0_0 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 8) (.mul (.pow (.var 4) 3) (.mul (.pow (.var 6) 3) (.pow (.var 1) 2))))))

def witness_K_0_0_1 : RingExpr := (.int (0))

def witness_K_0_0_2 : RingExpr := (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 8) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))))

def witness_K_0_0_3 : RingExpr := (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 8) (.add (.int (1)) (.add (.mul (.var 4) (.var 6)) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))))))

theorem certificate_K_0_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.int 3) (.var 2)) (.add (.mul (.int (-4)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 3) (.mul (.var 1) (.var 3))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))-(((-2) * (env 1) * (env 8)))) = (2*env 9-1)*exprEval env witness_K_0_0_0 + (env 2*env 8-1)*exprEval env witness_K_0_0_1 + (env 1*env 7-1)*exprEval env witness_K_0_0_2 + (env 4*env 6-1)*exprEval env witness_K_0_0_3 := by
  dsimp only [reducedOriginalVars, witness_K_0_0_0, witness_K_0_0_1, witness_K_0_0_2, witness_K_0_0_3, exprEval]
  grind

theorem original_K_0_0 (z : ReducedChart R) :
    litK (originalChart z) 0 0=reduced_K z 0 0 := by
  have h := certificate_K_0_0 (reducedVars z)
  change 1*(litK (originalChart z) 0 0-reduced_K z 0 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_0_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_0_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_0_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_0_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_0_1_0 : RingExpr := (.int (0))

def witness_K_0_1_1 : RingExpr := (.int (0))

def witness_K_0_1_2 : RingExpr := (.int (0))

def witness_K_0_1_3 : RingExpr := (.mul (.int (2)) (.mul (.var 3) (.mul (.var 4) (.mul (.var 1) (.var 8)))))

theorem certificate_K_0_1 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.var 7) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 3) (.mul (.var 1) (.var 3))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))-((2 * (env 3) * (env 4) * (env 1) * (env 8)))) = (2*env 9-1)*exprEval env witness_K_0_1_0 + (env 2*env 8-1)*exprEval env witness_K_0_1_1 + (env 1*env 7-1)*exprEval env witness_K_0_1_2 + (env 4*env 6-1)*exprEval env witness_K_0_1_3 := by
  dsimp only [reducedOriginalVars, witness_K_0_1_0, witness_K_0_1_1, witness_K_0_1_2, witness_K_0_1_3, exprEval]
  grind

theorem original_K_0_1 (z : ReducedChart R) :
    litK (originalChart z) 0 1=reduced_K z 0 1 := by
  have h := certificate_K_0_1 (reducedVars z)
  change 1*(litK (originalChart z) 0 1-reduced_K z 0 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_0_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_0_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_0_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_0_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_0_2_0 : RingExpr := (.int (0))

def witness_K_0_2_1 : RingExpr := (.int (0))

def witness_K_0_2_2 : RingExpr := (.int (0))

def witness_K_0_2_3 : RingExpr := (.int (0))

theorem certificate_K_0_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_0_2_0 + (env 2*env 8-1)*exprEval env witness_K_0_2_1 + (env 1*env 7-1)*exprEval env witness_K_0_2_2 + (env 4*env 6-1)*exprEval env witness_K_0_2_3 := by
  dsimp only [reducedOriginalVars, witness_K_0_2_0, witness_K_0_2_1, witness_K_0_2_2, witness_K_0_2_3, exprEval]
  grind

theorem original_K_0_2 (z : ReducedChart R) :
    litK (originalChart z) 0 2=reduced_K z 0 2 := by
  have h := certificate_K_0_2 (reducedVars z)
  change 1*(litK (originalChart z) 0 2-reduced_K z 0 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_0_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_0_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_0_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_0_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_0_3_0 : RingExpr := (.int (0))

def witness_K_0_3_1 : RingExpr := (.int (0))

def witness_K_0_3_2 : RingExpr := (.int (0))

def witness_K_0_3_3 : RingExpr := (.int (0))

theorem certificate_K_0_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_0_3_0 + (env 2*env 8-1)*exprEval env witness_K_0_3_1 + (env 1*env 7-1)*exprEval env witness_K_0_3_2 + (env 4*env 6-1)*exprEval env witness_K_0_3_3 := by
  dsimp only [reducedOriginalVars, witness_K_0_3_0, witness_K_0_3_1, witness_K_0_3_2, witness_K_0_3_3, exprEval]
  grind

theorem original_K_0_3 (z : ReducedChart R) :
    litK (originalChart z) 0 3=reduced_K z 0 3 := by
  have h := certificate_K_0_3 (reducedVars z)
  change 1*(litK (originalChart z) 0 3-reduced_K z 0 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_0_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_0_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_0_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_0_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_0_4_0 : RingExpr := (.int (0))

def witness_K_0_4_1 : RingExpr := (.int (0))

def witness_K_0_4_2 : RingExpr := (.int (0))

def witness_K_0_4_3 : RingExpr := (.int (0))

theorem certificate_K_0_4 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.var 7) (.add (.int (-2)) (.add (.mul (.int 2) (.mul (.var 2) (.var 4))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))-(((-2) * (env 4) * (env 1) * (env 8)))) = (2*env 9-1)*exprEval env witness_K_0_4_0 + (env 2*env 8-1)*exprEval env witness_K_0_4_1 + (env 1*env 7-1)*exprEval env witness_K_0_4_2 + (env 4*env 6-1)*exprEval env witness_K_0_4_3 := by
  dsimp only [reducedOriginalVars, witness_K_0_4_0, witness_K_0_4_1, witness_K_0_4_2, witness_K_0_4_3, exprEval]
  grind

theorem original_K_0_4 (z : ReducedChart R) :
    litK (originalChart z) 0 4=reduced_K z 0 4 := by
  have h := certificate_K_0_4 (reducedVars z)
  change 1*(litK (originalChart z) 0 4-reduced_K z 0 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_0_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_0_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_0_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_0_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_0_5_0 : RingExpr := (.int (0))

def witness_K_0_5_1 : RingExpr := (.int (0))

def witness_K_0_5_2 : RingExpr := (.int (0))

def witness_K_0_5_3 : RingExpr := (.int (0))

theorem certificate_K_0_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_0_5_0 + (env 2*env 8-1)*exprEval env witness_K_0_5_1 + (env 1*env 7-1)*exprEval env witness_K_0_5_2 + (env 4*env 6-1)*exprEval env witness_K_0_5_3 := by
  dsimp only [reducedOriginalVars, witness_K_0_5_0, witness_K_0_5_1, witness_K_0_5_2, witness_K_0_5_3, exprEval]
  grind

theorem original_K_0_5 (z : ReducedChart R) :
    litK (originalChart z) 0 5=reduced_K z 0 5 := by
  have h := certificate_K_0_5 (reducedVars z)
  change 1*(litK (originalChart z) 0 5-reduced_K z 0 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_0_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_0_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_0_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_0_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_1_0_0 : RingExpr := (.int (0))

def witness_K_1_0_1 : RingExpr := (.int (0))

def witness_K_1_0_2 : RingExpr := (.int (0))

def witness_K_1_0_3 : RingExpr := (.int (0))

theorem certificate_K_1_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int (-3)))-((-3))) = (2*env 9-1)*exprEval env witness_K_1_0_0 + (env 2*env 8-1)*exprEval env witness_K_1_0_1 + (env 1*env 7-1)*exprEval env witness_K_1_0_2 + (env 4*env 6-1)*exprEval env witness_K_1_0_3 := by
  dsimp only [reducedOriginalVars, witness_K_1_0_0, witness_K_1_0_1, witness_K_1_0_2, witness_K_1_0_3, exprEval]
  grind

theorem original_K_1_0 (z : ReducedChart R) :
    litK (originalChart z) 1 0=reduced_K z 1 0 := by
  have h := certificate_K_1_0 (reducedVars z)
  change 1*(litK (originalChart z) 1 0-reduced_K z 1 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_1_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_1_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_1_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_1_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_1_1_0 : RingExpr := (.int (0))

def witness_K_1_1_1 : RingExpr := (.int (0))

def witness_K_1_1_2 : RingExpr := (.int (0))

def witness_K_1_1_3 : RingExpr := (.int (0))

theorem certificate_K_1_1 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_1_1_0 + (env 2*env 8-1)*exprEval env witness_K_1_1_1 + (env 1*env 7-1)*exprEval env witness_K_1_1_2 + (env 4*env 6-1)*exprEval env witness_K_1_1_3 := by
  dsimp only [reducedOriginalVars, witness_K_1_1_0, witness_K_1_1_1, witness_K_1_1_2, witness_K_1_1_3, exprEval]
  grind

theorem original_K_1_1 (z : ReducedChart R) :
    litK (originalChart z) 1 1=reduced_K z 1 1 := by
  have h := certificate_K_1_1 (reducedVars z)
  change 1*(litK (originalChart z) 1 1-reduced_K z 1 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_1_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_1_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_1_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_1_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_1_2_0 : RingExpr := (.int (0))

def witness_K_1_2_1 : RingExpr := (.int (0))

def witness_K_1_2_2 : RingExpr := (.int (0))

def witness_K_1_2_3 : RingExpr := (.int (0))

theorem certificate_K_1_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_1_2_0 + (env 2*env 8-1)*exprEval env witness_K_1_2_1 + (env 1*env 7-1)*exprEval env witness_K_1_2_2 + (env 4*env 6-1)*exprEval env witness_K_1_2_3 := by
  dsimp only [reducedOriginalVars, witness_K_1_2_0, witness_K_1_2_1, witness_K_1_2_2, witness_K_1_2_3, exprEval]
  grind

theorem original_K_1_2 (z : ReducedChart R) :
    litK (originalChart z) 1 2=reduced_K z 1 2 := by
  have h := certificate_K_1_2 (reducedVars z)
  change 1*(litK (originalChart z) 1 2-reduced_K z 1 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_1_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_1_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_1_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_1_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_1_3_0 : RingExpr := (.int (0))

def witness_K_1_3_1 : RingExpr := (.int (0))

def witness_K_1_3_2 : RingExpr := (.int (0))

def witness_K_1_3_3 : RingExpr := (.int (0))

theorem certificate_K_1_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_1_3_0 + (env 2*env 8-1)*exprEval env witness_K_1_3_1 + (env 1*env 7-1)*exprEval env witness_K_1_3_2 + (env 4*env 6-1)*exprEval env witness_K_1_3_3 := by
  dsimp only [reducedOriginalVars, witness_K_1_3_0, witness_K_1_3_1, witness_K_1_3_2, witness_K_1_3_3, exprEval]
  grind

theorem original_K_1_3 (z : ReducedChart R) :
    litK (originalChart z) 1 3=reduced_K z 1 3 := by
  have h := certificate_K_1_3 (reducedVars z)
  change 1*(litK (originalChart z) 1 3-reduced_K z 1 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_1_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_1_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_1_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_1_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_1_4_0 : RingExpr := (.int (0))

def witness_K_1_4_1 : RingExpr := (.int (0))

def witness_K_1_4_2 : RingExpr := (.int (0))

def witness_K_1_4_3 : RingExpr := (.int (0))

theorem certificate_K_1_4 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_1_4_0 + (env 2*env 8-1)*exprEval env witness_K_1_4_1 + (env 1*env 7-1)*exprEval env witness_K_1_4_2 + (env 4*env 6-1)*exprEval env witness_K_1_4_3 := by
  dsimp only [reducedOriginalVars, witness_K_1_4_0, witness_K_1_4_1, witness_K_1_4_2, witness_K_1_4_3, exprEval]
  grind

theorem original_K_1_4 (z : ReducedChart R) :
    litK (originalChart z) 1 4=reduced_K z 1 4 := by
  have h := certificate_K_1_4 (reducedVars z)
  change 1*(litK (originalChart z) 1 4-reduced_K z 1 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_1_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_1_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_1_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_1_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_1_5_0 : RingExpr := (.int (0))

def witness_K_1_5_1 : RingExpr := (.int (0))

def witness_K_1_5_2 : RingExpr := (.int (0))

def witness_K_1_5_3 : RingExpr := (.int (0))

theorem certificate_K_1_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_1_5_0 + (env 2*env 8-1)*exprEval env witness_K_1_5_1 + (env 1*env 7-1)*exprEval env witness_K_1_5_2 + (env 4*env 6-1)*exprEval env witness_K_1_5_3 := by
  dsimp only [reducedOriginalVars, witness_K_1_5_0, witness_K_1_5_1, witness_K_1_5_2, witness_K_1_5_3, exprEval]
  grind

theorem original_K_1_5 (z : ReducedChart R) :
    litK (originalChart z) 1 5=reduced_K z 1 5 := by
  have h := certificate_K_1_5 (reducedVars z)
  change 1*(litK (originalChart z) 1 5-reduced_K z 1 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_1_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_1_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_1_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_1_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_2_0_0 : RingExpr := (.int (0))

def witness_K_2_0_1 : RingExpr := (.int (0))

def witness_K_2_0_2 : RingExpr := (.int (0))

def witness_K_2_0_3 : RingExpr := (.int (0))

theorem certificate_K_2_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int (-3)))-((-3))) = (2*env 9-1)*exprEval env witness_K_2_0_0 + (env 2*env 8-1)*exprEval env witness_K_2_0_1 + (env 1*env 7-1)*exprEval env witness_K_2_0_2 + (env 4*env 6-1)*exprEval env witness_K_2_0_3 := by
  dsimp only [reducedOriginalVars, witness_K_2_0_0, witness_K_2_0_1, witness_K_2_0_2, witness_K_2_0_3, exprEval]
  grind

theorem original_K_2_0 (z : ReducedChart R) :
    litK (originalChart z) 2 0=reduced_K z 2 0 := by
  have h := certificate_K_2_0 (reducedVars z)
  change 1*(litK (originalChart z) 2 0-reduced_K z 2 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_2_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_2_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_2_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_2_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_2_1_0 : RingExpr := (.int (0))

def witness_K_2_1_1 : RingExpr := (.int (0))

def witness_K_2_1_2 : RingExpr := (.int (0))

def witness_K_2_1_3 : RingExpr := (.int (0))

theorem certificate_K_2_1 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_2_1_0 + (env 2*env 8-1)*exprEval env witness_K_2_1_1 + (env 1*env 7-1)*exprEval env witness_K_2_1_2 + (env 4*env 6-1)*exprEval env witness_K_2_1_3 := by
  dsimp only [reducedOriginalVars, witness_K_2_1_0, witness_K_2_1_1, witness_K_2_1_2, witness_K_2_1_3, exprEval]
  grind

theorem original_K_2_1 (z : ReducedChart R) :
    litK (originalChart z) 2 1=reduced_K z 2 1 := by
  have h := certificate_K_2_1 (reducedVars z)
  change 1*(litK (originalChart z) 2 1-reduced_K z 2 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_2_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_2_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_2_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_2_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_2_2_0 : RingExpr := (.int (0))

def witness_K_2_2_1 : RingExpr := (.int (0))

def witness_K_2_2_2 : RingExpr := (.int (0))

def witness_K_2_2_3 : RingExpr := (.int (0))

theorem certificate_K_2_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_2_2_0 + (env 2*env 8-1)*exprEval env witness_K_2_2_1 + (env 1*env 7-1)*exprEval env witness_K_2_2_2 + (env 4*env 6-1)*exprEval env witness_K_2_2_3 := by
  dsimp only [reducedOriginalVars, witness_K_2_2_0, witness_K_2_2_1, witness_K_2_2_2, witness_K_2_2_3, exprEval]
  grind

theorem original_K_2_2 (z : ReducedChart R) :
    litK (originalChart z) 2 2=reduced_K z 2 2 := by
  have h := certificate_K_2_2 (reducedVars z)
  change 1*(litK (originalChart z) 2 2-reduced_K z 2 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_2_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_2_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_2_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_2_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_2_3_0 : RingExpr := (.int (0))

def witness_K_2_3_1 : RingExpr := (.int (0))

def witness_K_2_3_2 : RingExpr := (.int (0))

def witness_K_2_3_3 : RingExpr := (.int (0))

theorem certificate_K_2_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_2_3_0 + (env 2*env 8-1)*exprEval env witness_K_2_3_1 + (env 1*env 7-1)*exprEval env witness_K_2_3_2 + (env 4*env 6-1)*exprEval env witness_K_2_3_3 := by
  dsimp only [reducedOriginalVars, witness_K_2_3_0, witness_K_2_3_1, witness_K_2_3_2, witness_K_2_3_3, exprEval]
  grind

theorem original_K_2_3 (z : ReducedChart R) :
    litK (originalChart z) 2 3=reduced_K z 2 3 := by
  have h := certificate_K_2_3 (reducedVars z)
  change 1*(litK (originalChart z) 2 3-reduced_K z 2 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_2_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_2_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_2_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_2_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_2_4_0 : RingExpr := (.int (0))

def witness_K_2_4_1 : RingExpr := (.int (0))

def witness_K_2_4_2 : RingExpr := (.int (0))

def witness_K_2_4_3 : RingExpr := (.int (0))

theorem certificate_K_2_4 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_2_4_0 + (env 2*env 8-1)*exprEval env witness_K_2_4_1 + (env 1*env 7-1)*exprEval env witness_K_2_4_2 + (env 4*env 6-1)*exprEval env witness_K_2_4_3 := by
  dsimp only [reducedOriginalVars, witness_K_2_4_0, witness_K_2_4_1, witness_K_2_4_2, witness_K_2_4_3, exprEval]
  grind

theorem original_K_2_4 (z : ReducedChart R) :
    litK (originalChart z) 2 4=reduced_K z 2 4 := by
  have h := certificate_K_2_4 (reducedVars z)
  change 1*(litK (originalChart z) 2 4-reduced_K z 2 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_2_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_2_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_2_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_2_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_2_5_0 : RingExpr := (.int (0))

def witness_K_2_5_1 : RingExpr := (.int (0))

def witness_K_2_5_2 : RingExpr := (.int (0))

def witness_K_2_5_3 : RingExpr := (.int (0))

theorem certificate_K_2_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_2_5_0 + (env 2*env 8-1)*exprEval env witness_K_2_5_1 + (env 1*env 7-1)*exprEval env witness_K_2_5_2 + (env 4*env 6-1)*exprEval env witness_K_2_5_3 := by
  dsimp only [reducedOriginalVars, witness_K_2_5_0, witness_K_2_5_1, witness_K_2_5_2, witness_K_2_5_3, exprEval]
  grind

theorem original_K_2_5 (z : ReducedChart R) :
    litK (originalChart z) 2 5=reduced_K z 2 5 := by
  have h := certificate_K_2_5 (reducedVars z)
  change 1*(litK (originalChart z) 2 5-reduced_K z 2 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_2_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_2_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_2_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_2_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_3_0_0 : RingExpr := (.int (0))

def witness_K_3_0_1 : RingExpr := (.int (0))

def witness_K_3_0_2 : RingExpr := (.int (0))

def witness_K_3_0_3 : RingExpr := (.int (0))

theorem certificate_K_3_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int (-3)))-((-3))) = (2*env 9-1)*exprEval env witness_K_3_0_0 + (env 2*env 8-1)*exprEval env witness_K_3_0_1 + (env 1*env 7-1)*exprEval env witness_K_3_0_2 + (env 4*env 6-1)*exprEval env witness_K_3_0_3 := by
  dsimp only [reducedOriginalVars, witness_K_3_0_0, witness_K_3_0_1, witness_K_3_0_2, witness_K_3_0_3, exprEval]
  grind

theorem original_K_3_0 (z : ReducedChart R) :
    litK (originalChart z) 3 0=reduced_K z 3 0 := by
  have h := certificate_K_3_0 (reducedVars z)
  change 1*(litK (originalChart z) 3 0-reduced_K z 3 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_3_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_3_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_3_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_3_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_3_1_0 : RingExpr := (.int (0))

def witness_K_3_1_1 : RingExpr := (.int (0))

def witness_K_3_1_2 : RingExpr := (.int (0))

def witness_K_3_1_3 : RingExpr := (.int (0))

theorem certificate_K_3_1 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.int (-2)) (.var 2)))-((2 * (env 3) * (env 4)))) = (2*env 9-1)*exprEval env witness_K_3_1_0 + (env 2*env 8-1)*exprEval env witness_K_3_1_1 + (env 1*env 7-1)*exprEval env witness_K_3_1_2 + (env 4*env 6-1)*exprEval env witness_K_3_1_3 := by
  dsimp only [reducedOriginalVars, witness_K_3_1_0, witness_K_3_1_1, witness_K_3_1_2, witness_K_3_1_3, exprEval]
  grind

theorem original_K_3_1 (z : ReducedChart R) :
    litK (originalChart z) 3 1=reduced_K z 3 1 := by
  have h := certificate_K_3_1 (reducedVars z)
  change 1*(litK (originalChart z) 3 1-reduced_K z 3 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_3_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_3_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_3_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_3_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_3_2_0 : RingExpr := (.int (0))

def witness_K_3_2_1 : RingExpr := (.int (0))

def witness_K_3_2_2 : RingExpr := (.int (0))

def witness_K_3_2_3 : RingExpr := (.int (0))

theorem certificate_K_3_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_3_2_0 + (env 2*env 8-1)*exprEval env witness_K_3_2_1 + (env 1*env 7-1)*exprEval env witness_K_3_2_2 + (env 4*env 6-1)*exprEval env witness_K_3_2_3 := by
  dsimp only [reducedOriginalVars, witness_K_3_2_0, witness_K_3_2_1, witness_K_3_2_2, witness_K_3_2_3, exprEval]
  grind

theorem original_K_3_2 (z : ReducedChart R) :
    litK (originalChart z) 3 2=reduced_K z 3 2 := by
  have h := certificate_K_3_2 (reducedVars z)
  change 1*(litK (originalChart z) 3 2-reduced_K z 3 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_3_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_3_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_3_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_3_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_3_3_0 : RingExpr := (.int (0))

def witness_K_3_3_1 : RingExpr := (.int (0))

def witness_K_3_3_2 : RingExpr := (.int (0))

def witness_K_3_3_3 : RingExpr := (.int (0))

theorem certificate_K_3_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.int 2) (.var 2)))-(((-2) * (env 3) * (env 4)))) = (2*env 9-1)*exprEval env witness_K_3_3_0 + (env 2*env 8-1)*exprEval env witness_K_3_3_1 + (env 1*env 7-1)*exprEval env witness_K_3_3_2 + (env 4*env 6-1)*exprEval env witness_K_3_3_3 := by
  dsimp only [reducedOriginalVars, witness_K_3_3_0, witness_K_3_3_1, witness_K_3_3_2, witness_K_3_3_3, exprEval]
  grind

theorem original_K_3_3 (z : ReducedChart R) :
    litK (originalChart z) 3 3=reduced_K z 3 3 := by
  have h := certificate_K_3_3 (reducedVars z)
  change 1*(litK (originalChart z) 3 3-reduced_K z 3 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_3_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_3_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_3_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_3_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_3_4_0 : RingExpr := (.int (0))

def witness_K_3_4_1 : RingExpr := (.int (0))

def witness_K_3_4_2 : RingExpr := (.int (0))

def witness_K_3_4_3 : RingExpr := (.int (0))

theorem certificate_K_3_4 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.int (-2)) (.var 3)))-(((-2) * (env 4)))) = (2*env 9-1)*exprEval env witness_K_3_4_0 + (env 2*env 8-1)*exprEval env witness_K_3_4_1 + (env 1*env 7-1)*exprEval env witness_K_3_4_2 + (env 4*env 6-1)*exprEval env witness_K_3_4_3 := by
  dsimp only [reducedOriginalVars, witness_K_3_4_0, witness_K_3_4_1, witness_K_3_4_2, witness_K_3_4_3, exprEval]
  grind

theorem original_K_3_4 (z : ReducedChart R) :
    litK (originalChart z) 3 4=reduced_K z 3 4 := by
  have h := certificate_K_3_4 (reducedVars z)
  change 1*(litK (originalChart z) 3 4-reduced_K z 3 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_3_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_3_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_3_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_3_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_3_5_0 : RingExpr := (.int (0))

def witness_K_3_5_1 : RingExpr := (.int (0))

def witness_K_3_5_2 : RingExpr := (.int (0))

def witness_K_3_5_3 : RingExpr := (.int (0))

theorem certificate_K_3_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.int 2) (.var 3)))-((2 * (env 4)))) = (2*env 9-1)*exprEval env witness_K_3_5_0 + (env 2*env 8-1)*exprEval env witness_K_3_5_1 + (env 1*env 7-1)*exprEval env witness_K_3_5_2 + (env 4*env 6-1)*exprEval env witness_K_3_5_3 := by
  dsimp only [reducedOriginalVars, witness_K_3_5_0, witness_K_3_5_1, witness_K_3_5_2, witness_K_3_5_3, exprEval]
  grind

theorem original_K_3_5 (z : ReducedChart R) :
    litK (originalChart z) 3 5=reduced_K z 3 5 := by
  have h := certificate_K_3_5 (reducedVars z)
  change 1*(litK (originalChart z) 3 5-reduced_K z 3 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_3_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_3_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_3_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_3_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_4_0_0 : RingExpr := (.int (0))

def witness_K_4_0_1 : RingExpr := (.int (0))

def witness_K_4_0_2 : RingExpr := (.int (0))

def witness_K_4_0_3 : RingExpr := (.int (0))

theorem certificate_K_4_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.int (-2)) (.var 4)))-(((-2) * (env 6) * (env 1)))) = (2*env 9-1)*exprEval env witness_K_4_0_0 + (env 2*env 8-1)*exprEval env witness_K_4_0_1 + (env 1*env 7-1)*exprEval env witness_K_4_0_2 + (env 4*env 6-1)*exprEval env witness_K_4_0_3 := by
  dsimp only [reducedOriginalVars, witness_K_4_0_0, witness_K_4_0_1, witness_K_4_0_2, witness_K_4_0_3, exprEval]
  grind

theorem original_K_4_0 (z : ReducedChart R) :
    litK (originalChart z) 4 0=reduced_K z 4 0 := by
  have h := certificate_K_4_0 (reducedVars z)
  change 1*(litK (originalChart z) 4 0-reduced_K z 4 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_4_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_4_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_4_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_4_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_4_1_0 : RingExpr := (.int (0))

def witness_K_4_1_1 : RingExpr := (.int (0))

def witness_K_4_1_2 : RingExpr := (.int (0))

def witness_K_4_1_3 : RingExpr := (.mul (.int (2)) (.mul (.var 3) (.var 1)))

theorem certificate_K_4_1 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.add (.int (-3)) (.mul (.int (-2)) (.mul (.var 2) (.var 4)))))-(((-3) + (2 * (env 3) * (env 1))))) = (2*env 9-1)*exprEval env witness_K_4_1_0 + (env 2*env 8-1)*exprEval env witness_K_4_1_1 + (env 1*env 7-1)*exprEval env witness_K_4_1_2 + (env 4*env 6-1)*exprEval env witness_K_4_1_3 := by
  dsimp only [reducedOriginalVars, witness_K_4_1_0, witness_K_4_1_1, witness_K_4_1_2, witness_K_4_1_3, exprEval]
  grind

theorem original_K_4_1 (z : ReducedChart R) :
    litK (originalChart z) 4 1=reduced_K z 4 1 := by
  have h := certificate_K_4_1 (reducedVars z)
  change 1*(litK (originalChart z) 4 1-reduced_K z 4 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_4_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_4_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_4_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_4_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_4_2_0 : RingExpr := (.int (0))

def witness_K_4_2_1 : RingExpr := (.int (0))

def witness_K_4_2_2 : RingExpr := (.int (0))

def witness_K_4_2_3 : RingExpr := (.int (0))

theorem certificate_K_4_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_4_2_0 + (env 2*env 8-1)*exprEval env witness_K_4_2_1 + (env 1*env 7-1)*exprEval env witness_K_4_2_2 + (env 4*env 6-1)*exprEval env witness_K_4_2_3 := by
  dsimp only [reducedOriginalVars, witness_K_4_2_0, witness_K_4_2_1, witness_K_4_2_2, witness_K_4_2_3, exprEval]
  grind

theorem original_K_4_2 (z : ReducedChart R) :
    litK (originalChart z) 4 2=reduced_K z 4 2 := by
  have h := certificate_K_4_2 (reducedVars z)
  change 1*(litK (originalChart z) 4 2-reduced_K z 4 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_4_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_4_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_4_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_4_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_4_3_0 : RingExpr := (.int (0))

def witness_K_4_3_1 : RingExpr := (.int (0))

def witness_K_4_3_2 : RingExpr := (.int (0))

def witness_K_4_3_3 : RingExpr := (.int (0))

theorem certificate_K_4_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_4_3_0 + (env 2*env 8-1)*exprEval env witness_K_4_3_1 + (env 1*env 7-1)*exprEval env witness_K_4_3_2 + (env 4*env 6-1)*exprEval env witness_K_4_3_3 := by
  dsimp only [reducedOriginalVars, witness_K_4_3_0, witness_K_4_3_1, witness_K_4_3_2, witness_K_4_3_3, exprEval]
  grind

theorem original_K_4_3 (z : ReducedChart R) :
    litK (originalChart z) 4 3=reduced_K z 4 3 := by
  have h := certificate_K_4_3 (reducedVars z)
  change 1*(litK (originalChart z) 4 3-reduced_K z 4 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_4_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_4_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_4_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_4_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_4_4_0 : RingExpr := (.int (0))

def witness_K_4_4_1 : RingExpr := (.int (0))

def witness_K_4_4_2 : RingExpr := (.int (0))

def witness_K_4_4_3 : RingExpr := (.mul (.int (-2)) (.var 1))

theorem certificate_K_4_4 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.int (-2)) (.mul (.var 3) (.var 4))))-(((-2) * (env 1)))) = (2*env 9-1)*exprEval env witness_K_4_4_0 + (env 2*env 8-1)*exprEval env witness_K_4_4_1 + (env 1*env 7-1)*exprEval env witness_K_4_4_2 + (env 4*env 6-1)*exprEval env witness_K_4_4_3 := by
  dsimp only [reducedOriginalVars, witness_K_4_4_0, witness_K_4_4_1, witness_K_4_4_2, witness_K_4_4_3, exprEval]
  grind

theorem original_K_4_4 (z : ReducedChart R) :
    litK (originalChart z) 4 4=reduced_K z 4 4 := by
  have h := certificate_K_4_4 (reducedVars z)
  change 1*(litK (originalChart z) 4 4-reduced_K z 4 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_4_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_4_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_4_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_4_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_4_5_0 : RingExpr := (.int (0))

def witness_K_4_5_1 : RingExpr := (.int (0))

def witness_K_4_5_2 : RingExpr := (.int (0))

def witness_K_4_5_3 : RingExpr := (.int (0))

theorem certificate_K_4_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_4_5_0 + (env 2*env 8-1)*exprEval env witness_K_4_5_1 + (env 1*env 7-1)*exprEval env witness_K_4_5_2 + (env 4*env 6-1)*exprEval env witness_K_4_5_3 := by
  dsimp only [reducedOriginalVars, witness_K_4_5_0, witness_K_4_5_1, witness_K_4_5_2, witness_K_4_5_3, exprEval]
  grind

theorem original_K_4_5 (z : ReducedChart R) :
    litK (originalChart z) 4 5=reduced_K z 4 5 := by
  have h := certificate_K_4_5 (reducedVars z)
  change 1*(litK (originalChart z) 4 5-reduced_K z 4 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_4_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_4_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_4_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_4_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_5_0_0 : RingExpr := (.int (0))

def witness_K_5_0_1 : RingExpr := (.int (0))

def witness_K_5_0_2 : RingExpr := (.int (0))

def witness_K_5_0_3 : RingExpr := (.int (0))

theorem certificate_K_5_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.int (-2)) (.var 4)))-(((-2) * (env 6) * (env 1)))) = (2*env 9-1)*exprEval env witness_K_5_0_0 + (env 2*env 8-1)*exprEval env witness_K_5_0_1 + (env 1*env 7-1)*exprEval env witness_K_5_0_2 + (env 4*env 6-1)*exprEval env witness_K_5_0_3 := by
  dsimp only [reducedOriginalVars, witness_K_5_0_0, witness_K_5_0_1, witness_K_5_0_2, witness_K_5_0_3, exprEval]
  grind

theorem original_K_5_0 (z : ReducedChart R) :
    litK (originalChart z) 5 0=reduced_K z 5 0 := by
  have h := certificate_K_5_0 (reducedVars z)
  change 1*(litK (originalChart z) 5 0-reduced_K z 5 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_5_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_5_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_5_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_5_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_5_1_0 : RingExpr := (.int (0))

def witness_K_5_1_1 : RingExpr := (.int (0))

def witness_K_5_1_2 : RingExpr := (.int (0))

def witness_K_5_1_3 : RingExpr := (.mul (.int (2)) (.mul (.var 3) (.var 1)))

theorem certificate_K_5_1 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.add (.int (-1)) (.mul (.int (-2)) (.mul (.var 2) (.var 4)))))-(((-1) + (2 * (env 3) * (env 1))))) = (2*env 9-1)*exprEval env witness_K_5_1_0 + (env 2*env 8-1)*exprEval env witness_K_5_1_1 + (env 1*env 7-1)*exprEval env witness_K_5_1_2 + (env 4*env 6-1)*exprEval env witness_K_5_1_3 := by
  dsimp only [reducedOriginalVars, witness_K_5_1_0, witness_K_5_1_1, witness_K_5_1_2, witness_K_5_1_3, exprEval]
  grind

theorem original_K_5_1 (z : ReducedChart R) :
    litK (originalChart z) 5 1=reduced_K z 5 1 := by
  have h := certificate_K_5_1 (reducedVars z)
  change 1*(litK (originalChart z) 5 1-reduced_K z 5 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_5_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_5_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_5_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_5_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_5_2_0 : RingExpr := (.int (0))

def witness_K_5_2_1 : RingExpr := (.int (0))

def witness_K_5_2_2 : RingExpr := (.int (0))

def witness_K_5_2_3 : RingExpr := (.int (0))

theorem certificate_K_5_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_5_2_0 + (env 2*env 8-1)*exprEval env witness_K_5_2_1 + (env 1*env 7-1)*exprEval env witness_K_5_2_2 + (env 4*env 6-1)*exprEval env witness_K_5_2_3 := by
  dsimp only [reducedOriginalVars, witness_K_5_2_0, witness_K_5_2_1, witness_K_5_2_2, witness_K_5_2_3, exprEval]
  grind

theorem original_K_5_2 (z : ReducedChart R) :
    litK (originalChart z) 5 2=reduced_K z 5 2 := by
  have h := certificate_K_5_2 (reducedVars z)
  change 1*(litK (originalChart z) 5 2-reduced_K z 5 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_5_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_5_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_5_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_5_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_5_3_0 : RingExpr := (.int (0))

def witness_K_5_3_1 : RingExpr := (.int (0))

def witness_K_5_3_2 : RingExpr := (.int (0))

def witness_K_5_3_3 : RingExpr := (.int (0))

theorem certificate_K_5_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int (-2)))-((-2))) = (2*env 9-1)*exprEval env witness_K_5_3_0 + (env 2*env 8-1)*exprEval env witness_K_5_3_1 + (env 1*env 7-1)*exprEval env witness_K_5_3_2 + (env 4*env 6-1)*exprEval env witness_K_5_3_3 := by
  dsimp only [reducedOriginalVars, witness_K_5_3_0, witness_K_5_3_1, witness_K_5_3_2, witness_K_5_3_3, exprEval]
  grind

theorem original_K_5_3 (z : ReducedChart R) :
    litK (originalChart z) 5 3=reduced_K z 5 3 := by
  have h := certificate_K_5_3 (reducedVars z)
  change 1*(litK (originalChart z) 5 3-reduced_K z 5 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_5_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_5_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_5_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_5_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_5_4_0 : RingExpr := (.int (0))

def witness_K_5_4_1 : RingExpr := (.int (0))

def witness_K_5_4_2 : RingExpr := (.int (0))

def witness_K_5_4_3 : RingExpr := (.mul (.int (-2)) (.var 1))

theorem certificate_K_5_4 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.int (-2)) (.mul (.var 3) (.var 4))))-(((-2) * (env 1)))) = (2*env 9-1)*exprEval env witness_K_5_4_0 + (env 2*env 8-1)*exprEval env witness_K_5_4_1 + (env 1*env 7-1)*exprEval env witness_K_5_4_2 + (env 4*env 6-1)*exprEval env witness_K_5_4_3 := by
  dsimp only [reducedOriginalVars, witness_K_5_4_0, witness_K_5_4_1, witness_K_5_4_2, witness_K_5_4_3, exprEval]
  grind

theorem original_K_5_4 (z : ReducedChart R) :
    litK (originalChart z) 5 4=reduced_K z 5 4 := by
  have h := certificate_K_5_4 (reducedVars z)
  change 1*(litK (originalChart z) 5 4-reduced_K z 5 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_5_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_5_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_5_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_5_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_K_5_5_0 : RingExpr := (.int (0))

def witness_K_5_5_1 : RingExpr := (.int (0))

def witness_K_5_5_2 : RingExpr := (.int (0))

def witness_K_5_5_3 : RingExpr := (.int (0))

theorem certificate_K_5_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_K_5_5_0 + (env 2*env 8-1)*exprEval env witness_K_5_5_1 + (env 1*env 7-1)*exprEval env witness_K_5_5_2 + (env 4*env 6-1)*exprEval env witness_K_5_5_3 := by
  dsimp only [reducedOriginalVars, witness_K_5_5_0, witness_K_5_5_1, witness_K_5_5_2, witness_K_5_5_3, exprEval]
  grind

theorem original_K_5_5 (z : ReducedChart R) :
    litK (originalChart z) 5 5=reduced_K z 5 5 := by
  have h := certificate_K_5_5 (reducedVars z)
  change 1*(litK (originalChart z) 5 5-reduced_K z 5 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_K_5_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_K_5_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_K_5_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_K_5_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

theorem original_K (z : ReducedChart R) : litK (originalChart z)=reduced_K z := by
  funext r c
  exact (Fin.cases ((Fin.cases (original_K_0_0 z) (fun c => (Fin.cases (original_K_0_1 z) (fun c => (Fin.cases (original_K_0_2 z) (fun c => (Fin.cases (original_K_0_3 z) (fun c => (Fin.cases (original_K_0_4 z) (fun c => (Fin.cases (original_K_0_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.cases ((Fin.cases (original_K_1_0 z) (fun c => (Fin.cases (original_K_1_1 z) (fun c => (Fin.cases (original_K_1_2 z) (fun c => (Fin.cases (original_K_1_3 z) (fun c => (Fin.cases (original_K_1_4 z) (fun c => (Fin.cases (original_K_1_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.cases ((Fin.cases (original_K_2_0 z) (fun c => (Fin.cases (original_K_2_1 z) (fun c => (Fin.cases (original_K_2_2 z) (fun c => (Fin.cases (original_K_2_3 z) (fun c => (Fin.cases (original_K_2_4 z) (fun c => (Fin.cases (original_K_2_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.cases ((Fin.cases (original_K_3_0 z) (fun c => (Fin.cases (original_K_3_1 z) (fun c => (Fin.cases (original_K_3_2 z) (fun c => (Fin.cases (original_K_3_3 z) (fun c => (Fin.cases (original_K_3_4 z) (fun c => (Fin.cases (original_K_3_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.cases ((Fin.cases (original_K_4_0 z) (fun c => (Fin.cases (original_K_4_1 z) (fun c => (Fin.cases (original_K_4_2 z) (fun c => (Fin.cases (original_K_4_3 z) (fun c => (Fin.cases (original_K_4_4 z) (fun c => (Fin.cases (original_K_4_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.cases ((Fin.cases (original_K_5_0 z) (fun c => (Fin.cases (original_K_5_1 z) (fun c => (Fin.cases (original_K_5_2 z) (fun c => (Fin.cases (original_K_5_3 z) (fun c => (Fin.cases (original_K_5_4 z) (fun c => (Fin.cases (original_K_5_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.elim0 r)) r)) r)) r)) r)) r)) r)

#print axioms original_K
end StackSorting.RationalLift
