import ReducedWitnessEnvironment
noncomputable section
namespace StackSorting.RationalLift
open StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

def witness_T_0_0_0 : RingExpr := (.int (0))

def witness_T_0_0_1 : RingExpr := (.int (0))

def witness_T_0_0_2 : RingExpr := (.int (0))

def witness_T_0_0_3 : RingExpr := (.int (0))

theorem certificate_T_0_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_0_0_0 + (env 2*env 8-1)*exprEval env witness_T_0_0_1 + (env 1*env 7-1)*exprEval env witness_T_0_0_2 + (env 4*env 6-1)*exprEval env witness_T_0_0_3 := by
  dsimp only [reducedOriginalVars, witness_T_0_0_0, witness_T_0_0_1, witness_T_0_0_2, witness_T_0_0_3, exprEval]
  grind

theorem original_T_0_0 (z : ReducedChart R) :
    litT (originalChart z) 0 0=reduced_T z 0 0 := by
  have h := certificate_T_0_0 (reducedVars z)
  change 1*(litT (originalChart z) 0 0-reduced_T z 0 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_0_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_0_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_0_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_0_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_0_1_0 : RingExpr := (.int (0))

def witness_T_0_1_1 : RingExpr := (.int (0))

def witness_T_0_1_2 : RingExpr := (.int (0))

def witness_T_0_1_3 : RingExpr := (.int (0))

theorem certificate_T_0_1 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_0_1_0 + (env 2*env 8-1)*exprEval env witness_T_0_1_1 + (env 1*env 7-1)*exprEval env witness_T_0_1_2 + (env 4*env 6-1)*exprEval env witness_T_0_1_3 := by
  dsimp only [reducedOriginalVars, witness_T_0_1_0, witness_T_0_1_1, witness_T_0_1_2, witness_T_0_1_3, exprEval]
  grind

theorem original_T_0_1 (z : ReducedChart R) :
    litT (originalChart z) 0 1=reduced_T z 0 1 := by
  have h := certificate_T_0_1 (reducedVars z)
  change 1*(litT (originalChart z) 0 1-reduced_T z 0 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_0_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_0_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_0_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_0_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_0_2_0 : RingExpr := (.int (0))

def witness_T_0_2_1 : RingExpr := (.int (0))

def witness_T_0_2_2 : RingExpr := (.int (0))

def witness_T_0_2_3 : RingExpr := (.int (0))

theorem certificate_T_0_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 1))-(1)) = (2*env 9-1)*exprEval env witness_T_0_2_0 + (env 2*env 8-1)*exprEval env witness_T_0_2_1 + (env 1*env 7-1)*exprEval env witness_T_0_2_2 + (env 4*env 6-1)*exprEval env witness_T_0_2_3 := by
  dsimp only [reducedOriginalVars, witness_T_0_2_0, witness_T_0_2_1, witness_T_0_2_2, witness_T_0_2_3, exprEval]
  grind

theorem original_T_0_2 (z : ReducedChart R) :
    litT (originalChart z) 0 2=reduced_T z 0 2 := by
  have h := certificate_T_0_2 (reducedVars z)
  change 1*(litT (originalChart z) 0 2-reduced_T z 0 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_0_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_0_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_0_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_0_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_0_3_0 : RingExpr := (.int (0))

def witness_T_0_3_1 : RingExpr := (.int (0))

def witness_T_0_3_2 : RingExpr := (.int (0))

def witness_T_0_3_3 : RingExpr := (.int (0))

theorem certificate_T_0_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_0_3_0 + (env 2*env 8-1)*exprEval env witness_T_0_3_1 + (env 1*env 7-1)*exprEval env witness_T_0_3_2 + (env 4*env 6-1)*exprEval env witness_T_0_3_3 := by
  dsimp only [reducedOriginalVars, witness_T_0_3_0, witness_T_0_3_1, witness_T_0_3_2, witness_T_0_3_3, exprEval]
  grind

theorem original_T_0_3 (z : ReducedChart R) :
    litT (originalChart z) 0 3=reduced_T z 0 3 := by
  have h := certificate_T_0_3 (reducedVars z)
  change 1*(litT (originalChart z) 0 3-reduced_T z 0 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_0_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_0_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_0_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_0_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_0_4_0 : RingExpr := (.int (0))

def witness_T_0_4_1 : RingExpr := (.int (0))

def witness_T_0_4_2 : RingExpr := (.int (0))

def witness_T_0_4_3 : RingExpr := (.int (0))

theorem certificate_T_0_4 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_0_4_0 + (env 2*env 8-1)*exprEval env witness_T_0_4_1 + (env 1*env 7-1)*exprEval env witness_T_0_4_2 + (env 4*env 6-1)*exprEval env witness_T_0_4_3 := by
  dsimp only [reducedOriginalVars, witness_T_0_4_0, witness_T_0_4_1, witness_T_0_4_2, witness_T_0_4_3, exprEval]
  grind

theorem original_T_0_4 (z : ReducedChart R) :
    litT (originalChart z) 0 4=reduced_T z 0 4 := by
  have h := certificate_T_0_4 (reducedVars z)
  change 1*(litT (originalChart z) 0 4-reduced_T z 0 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_0_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_0_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_0_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_0_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_0_5_0 : RingExpr := (.int (0))

def witness_T_0_5_1 : RingExpr := (.int (0))

def witness_T_0_5_2 : RingExpr := (.int (0))

def witness_T_0_5_3 : RingExpr := (.int (0))

theorem certificate_T_0_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_0_5_0 + (env 2*env 8-1)*exprEval env witness_T_0_5_1 + (env 1*env 7-1)*exprEval env witness_T_0_5_2 + (env 4*env 6-1)*exprEval env witness_T_0_5_3 := by
  dsimp only [reducedOriginalVars, witness_T_0_5_0, witness_T_0_5_1, witness_T_0_5_2, witness_T_0_5_3, exprEval]
  grind

theorem original_T_0_5 (z : ReducedChart R) :
    litT (originalChart z) 0 5=reduced_T z 0 5 := by
  have h := certificate_T_0_5 (reducedVars z)
  change 1*(litT (originalChart z) 0 5-reduced_T z 0 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_0_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_0_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_0_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_0_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_1_0_0 : RingExpr := (.mul (.var 6) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (3)) (.mul (.var 0) (.var 1))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 6) (.var 1))))) (.mul (.var 1) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))))))))

def witness_T_1_0_1 : RingExpr := (.int (0))

def witness_T_1_0_2 : RingExpr := (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 3)))

def witness_T_1_0_3 : RingExpr := (.mul (.var 6) (.add (.var 2) (.add (.mul (.int (-3)) (.mul (.var 0) (.var 1))) (.mul (.var 4) (.mul (.var 6) (.var 2))))))

theorem certificate_T_1_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.var 10) (.mul (.var 8) (.add (.int 3) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 6) (.mul (.var 3) (.var 4))))))))))-(((3 * (env 9) * (env 6)) + (2 * (env 9) * (env 6) * (env 2)) + ((-6) * (env 0) * (env 9) * (env 6) * (env 1))))) = (2*env 9-1)*exprEval env witness_T_1_0_0 + (env 2*env 8-1)*exprEval env witness_T_1_0_1 + (env 1*env 7-1)*exprEval env witness_T_1_0_2 + (env 4*env 6-1)*exprEval env witness_T_1_0_3 := by
  dsimp only [reducedOriginalVars, witness_T_1_0_0, witness_T_1_0_1, witness_T_1_0_2, witness_T_1_0_3, exprEval]
  grind

theorem original_T_1_0 (z : ReducedChart R) :
    litT (originalChart z) 1 0=reduced_T z 1 0 := by
  have h := certificate_T_1_0 (reducedVars z)
  change 1*(litT (originalChart z) 1 0-reduced_T z 1 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_1_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_1_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_1_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_1_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_1_1_0 : RingExpr := (.mul (.int (3)) (.add (.mul (.int (-1)) (.var 0)) (.add (.mul (.var 0) (.mul (.var 4) (.var 6))) (.add (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 4) (.var 6)))) (.mul (.int (2)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 1) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2))))))))))

def witness_T_1_1_1 : RingExpr := (.int (0))

def witness_T_1_1_2 : RingExpr := (.int (0))

def witness_T_1_1_3 : RingExpr := (.mul (.int (3)) (.add (.var 0) (.add (.mul (.int (-2)) (.var 3)) (.add (.mul (.int (2)) (.mul (.var 0) (.mul (.var 3) (.var 1)))) (.mul (.int (2)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.mul (.var 6) (.var 1))))))))))

theorem certificate_T_1_1 (env : Nat → R) :
    2*(exprEval (reducedOriginalVars env) ((.mul (.var 10) (.mul (.var 8) (.add (.mul (.int 4) (.var 2)) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-3)) (.mul (.var 6) (.var 3))) (.add (.mul (.int 8) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 6) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))-((((-3) * (env 3)) + ((3 * (env 9)^1) * (env 0)) + (3 * (env 0) * (env 3) * (env 1))))) = (2*env 9-1)*exprEval env witness_T_1_1_0 + (env 2*env 8-1)*exprEval env witness_T_1_1_1 + (env 1*env 7-1)*exprEval env witness_T_1_1_2 + (env 4*env 6-1)*exprEval env witness_T_1_1_3 := by
  dsimp only [reducedOriginalVars, witness_T_1_1_0, witness_T_1_1_1, witness_T_1_1_2, witness_T_1_1_3, exprEval]
  grind

theorem original_T_1_1 (z : ReducedChart R) :
    litT (originalChart z) 1 1=reduced_T z 1 1 := by
  have h := certificate_T_1_1 (reducedVars z)
  change 2*(litT (originalChart z) 1 1-reduced_T z 1 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_1_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_1_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_1_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_1_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  have hz : 2*(litT (originalChart z) 1 1-reduced_T z 1 1)=0 := by grind
  have hz0 := half_cancel_two z.half _ z.half_unit hz
  grind

def witness_T_1_2_0 : RingExpr := (.int (0))

def witness_T_1_2_1 : RingExpr := (.int (0))

def witness_T_1_2_2 : RingExpr := (.int (0))

def witness_T_1_2_3 : RingExpr := (.int (0))

theorem certificate_T_1_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.var 6))-(((env 3) + ((-1) * (env 0))))) = (2*env 9-1)*exprEval env witness_T_1_2_0 + (env 2*env 8-1)*exprEval env witness_T_1_2_1 + (env 1*env 7-1)*exprEval env witness_T_1_2_2 + (env 4*env 6-1)*exprEval env witness_T_1_2_3 := by
  dsimp only [reducedOriginalVars, witness_T_1_2_0, witness_T_1_2_1, witness_T_1_2_2, witness_T_1_2_3, exprEval]
  grind

theorem original_T_1_2 (z : ReducedChart R) :
    litT (originalChart z) 1 2=reduced_T z 1 2 := by
  have h := certificate_T_1_2 (reducedVars z)
  change 1*(litT (originalChart z) 1 2-reduced_T z 1 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_1_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_1_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_1_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_1_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_1_3_0 : RingExpr := (.int (0))

def witness_T_1_3_1 : RingExpr := (.int (0))

def witness_T_1_3_2 : RingExpr := (.int (0))

def witness_T_1_3_3 : RingExpr := (.int (0))

theorem certificate_T_1_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_1_3_0 + (env 2*env 8-1)*exprEval env witness_T_1_3_1 + (env 1*env 7-1)*exprEval env witness_T_1_3_2 + (env 4*env 6-1)*exprEval env witness_T_1_3_3 := by
  dsimp only [reducedOriginalVars, witness_T_1_3_0, witness_T_1_3_1, witness_T_1_3_2, witness_T_1_3_3, exprEval]
  grind

theorem original_T_1_3 (z : ReducedChart R) :
    litT (originalChart z) 1 3=reduced_T z 1 3 := by
  have h := certificate_T_1_3 (reducedVars z)
  change 1*(litT (originalChart z) 1 3-reduced_T z 1 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_1_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_1_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_1_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_1_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_1_4_0 : RingExpr := (.int (0))

def witness_T_1_4_1 : RingExpr := (.int (0))

def witness_T_1_4_2 : RingExpr := (.int (0))

def witness_T_1_4_3 : RingExpr := (.mul (.int (-3)) (.mul (.var 0) (.var 1)))

theorem certificate_T_1_4 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.add (.int 3) (.add (.mul (.int 4) (.mul (.var 2) (.var 4))) (.add (.mul (.var 1) (.mul (.var 3) (.var 4))) (.mul (.int 3) (.mul (.var 6) (.mul (.var 3) (.var 4))))))))-((3 + ((-3) * (env 0) * (env 1))))) = (2*env 9-1)*exprEval env witness_T_1_4_0 + (env 2*env 8-1)*exprEval env witness_T_1_4_1 + (env 1*env 7-1)*exprEval env witness_T_1_4_2 + (env 4*env 6-1)*exprEval env witness_T_1_4_3 := by
  dsimp only [reducedOriginalVars, witness_T_1_4_0, witness_T_1_4_1, witness_T_1_4_2, witness_T_1_4_3, exprEval]
  grind

theorem original_T_1_4 (z : ReducedChart R) :
    litT (originalChart z) 1 4=reduced_T z 1 4 := by
  have h := certificate_T_1_4 (reducedVars z)
  change 1*(litT (originalChart z) 1 4-reduced_T z 1 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_1_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_1_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_1_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_1_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_1_5_0 : RingExpr := (.int (0))

def witness_T_1_5_1 : RingExpr := (.int (0))

def witness_T_1_5_2 : RingExpr := (.int (0))

def witness_T_1_5_3 : RingExpr := (.int (0))

theorem certificate_T_1_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_1_5_0 + (env 2*env 8-1)*exprEval env witness_T_1_5_1 + (env 1*env 7-1)*exprEval env witness_T_1_5_2 + (env 4*env 6-1)*exprEval env witness_T_1_5_3 := by
  dsimp only [reducedOriginalVars, witness_T_1_5_0, witness_T_1_5_1, witness_T_1_5_2, witness_T_1_5_3, exprEval]
  grind

theorem original_T_1_5 (z : ReducedChart R) :
    litT (originalChart z) 1 5=reduced_T z 1 5 := by
  have h := certificate_T_1_5 (reducedVars z)
  change 1*(litT (originalChart z) 1 5-reduced_T z 1 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_1_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_1_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_1_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_1_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_2_0_0 : RingExpr := (.mul (.int (-3)) (.mul (.var 6) (.mul (.add (.int (1)) (.mul (.int (2)) (.var 9))) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-3)) (.mul (.var 0) (.var 1))) (.add (.mul (.int (3)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 6) (.var 1))))) (.mul (.var 1) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))))))))))

def witness_T_2_0_1 : RingExpr := (.int (0))

def witness_T_2_0_2 : RingExpr := (.mul (.int (-3)) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 3))))

def witness_T_2_0_3 : RingExpr := (.mul (.int (-3)) (.mul (.var 6) (.add (.var 2) (.add (.mul (.int (3)) (.mul (.var 0) (.var 1))) (.mul (.var 4) (.mul (.var 6) (.var 2)))))))

theorem certificate_T_2_0 (env : Nat → R) :
    2*(exprEval (reducedOriginalVars env) ((.mul (.var 8) (.mul (.pow (.var 10) 2) (.add (.int 3) (.add (.mul (.int 4) (.var 5)) (.add (.mul (.int 30) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 18) (.mul (.var 6) (.mul (.var 3) (.var 4))))))))))))-(((3 * (env 6) * ((env 9)^2)) + ((-6) * (env 6) * (env 2) * ((env 9)^2)) + (4 * (env 5) * (env 6) * ((env 9)^2)) + ((-18) * (env 0) * (env 6) * (env 1) * ((env 9)^2))))) = (2*env 9-1)*exprEval env witness_T_2_0_0 + (env 2*env 8-1)*exprEval env witness_T_2_0_1 + (env 1*env 7-1)*exprEval env witness_T_2_0_2 + (env 4*env 6-1)*exprEval env witness_T_2_0_3 := by
  dsimp only [reducedOriginalVars, witness_T_2_0_0, witness_T_2_0_1, witness_T_2_0_2, witness_T_2_0_3, exprEval]
  grind

theorem original_T_2_0 (z : ReducedChart R) :
    litT (originalChart z) 2 0=reduced_T z 2 0 := by
  have h := certificate_T_2_0 (reducedVars z)
  change 2*(litT (originalChart z) 2 0-reduced_T z 2 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_2_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_2_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_2_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_2_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  have hz : 2*(litT (originalChart z) 2 0-reduced_T z 2 0)=0 := by grind
  have hz0 := half_cancel_two z.half _ z.half_unit hz
  grind

def witness_T_2_1_0 : RingExpr := (.add (.mul (.int (-9)) (.var 0)) (.add (.mul (.int (-18)) (.mul (.var 0) (.var 9))) (.add (.mul (.int (-18)) (.mul (.var 0) (.mul (.var 3) (.var 1)))) (.add (.mul (.int (-12)) (.mul (.var 3) (.mul (.var 4) (.var 6)))) (.add (.mul (.int (9)) (.mul (.var 0) (.mul (.var 4) (.var 6)))) (.add (.mul (.int (-24)) (.mul (.var 9) (.mul (.var 3) (.mul (.var 4) (.var 6))))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 3) (.mul (.var 4) (.var 6))))) (.add (.mul (.int (18)) (.mul (.var 0) (.mul (.var 9) (.mul (.var 4) (.var 6))))) (.add (.mul (.int (-8)) (.mul (.var 5) (.mul (.var 9) (.mul (.var 3) (.mul (.var 4) (.var 6)))))) (.add (.mul (.int (18)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 1) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))))) (.mul (.int (36)) (.mul (.var 0) (.mul (.var 9) (.mul (.var 3) (.mul (.var 1) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))))))))))))))))

def witness_T_2_1_1 : RingExpr := (.int (0))

def witness_T_2_1_2 : RingExpr := (.int (0))

def witness_T_2_1_3 : RingExpr := (.add (.mul (.int (-12)) (.var 3)) (.add (.mul (.int (9)) (.var 0)) (.add (.mul (.int (-4)) (.mul (.var 5) (.var 3))) (.add (.mul (.int (18)) (.mul (.var 0) (.mul (.var 3) (.var 1)))) (.mul (.int (18)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.mul (.var 6) (.var 1))))))))))

theorem certificate_T_2_1 (env : Nat → R) :
    4*(exprEval (reducedOriginalVars env) ((.mul (.var 8) (.mul (.pow (.var 10) 2) (.add (.mul (.int (-9)) (.mul (.var 6) (.var 3))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int 4) (.mul (.var 5) (.var 2))) (.add (.mul (.int 24) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 18) (.mul (.var 6) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))-((((-3) * (env 3)) + ((9 * (env 9)^2) * (env 0)) + ((-1) * (env 5) * (env 3)) + ((9 * (env 9)^1) * (env 0) * (env 3) * (env 1))))) = (2*env 9-1)*exprEval env witness_T_2_1_0 + (env 2*env 8-1)*exprEval env witness_T_2_1_1 + (env 1*env 7-1)*exprEval env witness_T_2_1_2 + (env 4*env 6-1)*exprEval env witness_T_2_1_3 := by
  dsimp only [reducedOriginalVars, witness_T_2_1_0, witness_T_2_1_1, witness_T_2_1_2, witness_T_2_1_3, exprEval]
  grind

theorem original_T_2_1 (z : ReducedChart R) :
    litT (originalChart z) 2 1=reduced_T z 2 1 := by
  have h := certificate_T_2_1 (reducedVars z)
  change 4*(litT (originalChart z) 2 1-reduced_T z 2 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_2_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_2_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_2_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_2_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  have hz : 4*(litT (originalChart z) 2 1-reduced_T z 2 1)=0 := by grind
  have hz0 := half_cancel_four z.half _ z.half_unit hz
  grind

def witness_T_2_2_0 : RingExpr := (.int (0))

def witness_T_2_2_1 : RingExpr := (.int (0))

def witness_T_2_2_2 : RingExpr := (.int (0))

def witness_T_2_2_3 : RingExpr := (.int (0))

theorem certificate_T_2_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.int 3) (.mul (.var 10) (.var 6))))-((((-3 * (env 9)^1) * (env 0)) + ((3 * (env 9)^1) * (env 3))))) = (2*env 9-1)*exprEval env witness_T_2_2_0 + (env 2*env 8-1)*exprEval env witness_T_2_2_1 + (env 1*env 7-1)*exprEval env witness_T_2_2_2 + (env 4*env 6-1)*exprEval env witness_T_2_2_3 := by
  dsimp only [reducedOriginalVars, witness_T_2_2_0, witness_T_2_2_1, witness_T_2_2_2, witness_T_2_2_3, exprEval]
  grind

theorem original_T_2_2 (z : ReducedChart R) :
    litT (originalChart z) 2 2=reduced_T z 2 2 := by
  have h := certificate_T_2_2 (reducedVars z)
  change 1*(litT (originalChart z) 2 2-reduced_T z 2 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_2_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_2_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_2_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_2_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_2_3_0 : RingExpr := (.int (0))

def witness_T_2_3_1 : RingExpr := (.int (0))

def witness_T_2_3_2 : RingExpr := (.int (0))

def witness_T_2_3_3 : RingExpr := (.int (0))

theorem certificate_T_2_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_2_3_0 + (env 2*env 8-1)*exprEval env witness_T_2_3_1 + (env 1*env 7-1)*exprEval env witness_T_2_3_2 + (env 4*env 6-1)*exprEval env witness_T_2_3_3 := by
  dsimp only [reducedOriginalVars, witness_T_2_3_0, witness_T_2_3_1, witness_T_2_3_2, witness_T_2_3_3, exprEval]
  grind

theorem original_T_2_3 (z : ReducedChart R) :
    litT (originalChart z) 2 3=reduced_T z 2 3 := by
  have h := certificate_T_2_3 (reducedVars z)
  change 1*(litT (originalChart z) 2 3-reduced_T z 2 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_2_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_2_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_2_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_2_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_2_4_0 : RingExpr := (.mul (.int (-3)) (.mul (.var 1) (.add (.mul (.int (-3)) (.var 0)) (.add (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 4) (.var 6)))) (.mul (.int (3)) (.mul (.var 0) (.mul (.var 4) (.var 6))))))))

def witness_T_2_4_1 : RingExpr := (.int (0))

def witness_T_2_4_2 : RingExpr := (.int (0))

def witness_T_2_4_3 : RingExpr := (.mul (.int (-9)) (.mul (.var 0) (.var 1)))

theorem certificate_T_2_4 (env : Nat → R) :
    2*(exprEval (reducedOriginalVars env) ((.add (.int 3) (.add (.var 5) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.mul (.int (3)) (.pow (.var 10) 1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.mul (.int (9)) (.pow (.var 10) 1)) (.mul (.var 6) (.mul (.var 3) (.var 4)))))))))-((3 + (env 5) + ((-9 * (env 9)^1) * (env 0) * (env 1))))) = (2*env 9-1)*exprEval env witness_T_2_4_0 + (env 2*env 8-1)*exprEval env witness_T_2_4_1 + (env 1*env 7-1)*exprEval env witness_T_2_4_2 + (env 4*env 6-1)*exprEval env witness_T_2_4_3 := by
  dsimp only [reducedOriginalVars, witness_T_2_4_0, witness_T_2_4_1, witness_T_2_4_2, witness_T_2_4_3, exprEval]
  grind

theorem original_T_2_4 (z : ReducedChart R) :
    litT (originalChart z) 2 4=reduced_T z 2 4 := by
  have h := certificate_T_2_4 (reducedVars z)
  change 2*(litT (originalChart z) 2 4-reduced_T z 2 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_2_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_2_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_2_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_2_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  have hz : 2*(litT (originalChart z) 2 4-reduced_T z 2 4)=0 := by grind
  have hz0 := half_cancel_two z.half _ z.half_unit hz
  grind

def witness_T_2_5_0 : RingExpr := (.int (0))

def witness_T_2_5_1 : RingExpr := (.int (0))

def witness_T_2_5_2 : RingExpr := (.int (0))

def witness_T_2_5_3 : RingExpr := (.int (0))

theorem certificate_T_2_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_2_5_0 + (env 2*env 8-1)*exprEval env witness_T_2_5_1 + (env 1*env 7-1)*exprEval env witness_T_2_5_2 + (env 4*env 6-1)*exprEval env witness_T_2_5_3 := by
  dsimp only [reducedOriginalVars, witness_T_2_5_0, witness_T_2_5_1, witness_T_2_5_2, witness_T_2_5_3, exprEval]
  grind

theorem original_T_2_5 (z : ReducedChart R) :
    litT (originalChart z) 2 5=reduced_T z 2 5 := by
  have h := certificate_T_2_5 (reducedVars z)
  change 1*(litT (originalChart z) 2 5-reduced_T z 2 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_2_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_2_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_2_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_2_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_3_0_0 : RingExpr := (.int (0))

def witness_T_3_0_1 : RingExpr := (.int (0))

def witness_T_3_0_2 : RingExpr := (.int (0))

def witness_T_3_0_3 : RingExpr := (.int (0))

theorem certificate_T_3_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_3_0_0 + (env 2*env 8-1)*exprEval env witness_T_3_0_1 + (env 1*env 7-1)*exprEval env witness_T_3_0_2 + (env 4*env 6-1)*exprEval env witness_T_3_0_3 := by
  dsimp only [reducedOriginalVars, witness_T_3_0_0, witness_T_3_0_1, witness_T_3_0_2, witness_T_3_0_3, exprEval]
  grind

theorem original_T_3_0 (z : ReducedChart R) :
    litT (originalChart z) 3 0=reduced_T z 3 0 := by
  have h := certificate_T_3_0 (reducedVars z)
  change 1*(litT (originalChart z) 3 0-reduced_T z 3 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_3_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_3_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_3_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_3_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_3_1_0 : RingExpr := (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 1) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))))))

def witness_T_3_1_1 : RingExpr := (.int (0))

def witness_T_3_1_2 : RingExpr := (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))))

def witness_T_3_1_3 : RingExpr := (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 2) (.add (.int (1)) (.add (.mul (.var 4) (.var 6)) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))))))

theorem certificate_T_3_1 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))-(((-1) * (env 3) * (env 2)))) = (2*env 9-1)*exprEval env witness_T_3_1_0 + (env 2*env 8-1)*exprEval env witness_T_3_1_1 + (env 1*env 7-1)*exprEval env witness_T_3_1_2 + (env 4*env 6-1)*exprEval env witness_T_3_1_3 := by
  dsimp only [reducedOriginalVars, witness_T_3_1_0, witness_T_3_1_1, witness_T_3_1_2, witness_T_3_1_3, exprEval]
  grind

theorem original_T_3_1 (z : ReducedChart R) :
    litT (originalChart z) 3 1=reduced_T z 3 1 := by
  have h := certificate_T_3_1 (reducedVars z)
  change 1*(litT (originalChart z) 3 1-reduced_T z 3 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_3_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_3_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_3_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_3_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_3_2_0 : RingExpr := (.int (0))

def witness_T_3_2_1 : RingExpr := (.int (0))

def witness_T_3_2_2 : RingExpr := (.int (0))

def witness_T_3_2_3 : RingExpr := (.int (0))

theorem certificate_T_3_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_3_2_0 + (env 2*env 8-1)*exprEval env witness_T_3_2_1 + (env 1*env 7-1)*exprEval env witness_T_3_2_2 + (env 4*env 6-1)*exprEval env witness_T_3_2_3 := by
  dsimp only [reducedOriginalVars, witness_T_3_2_0, witness_T_3_2_1, witness_T_3_2_2, witness_T_3_2_3, exprEval]
  grind

theorem original_T_3_2 (z : ReducedChart R) :
    litT (originalChart z) 3 2=reduced_T z 3 2 := by
  have h := certificate_T_3_2 (reducedVars z)
  change 1*(litT (originalChart z) 3 2-reduced_T z 3 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_3_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_3_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_3_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_3_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_3_3_0 : RingExpr := (.mul (.var 3) (.mul (.var 1) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3))))))

def witness_T_3_3_1 : RingExpr := (.int (0))

def witness_T_3_3_2 : RingExpr := (.mul (.var 3) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3))))

def witness_T_3_3_3 : RingExpr := (.mul (.var 3) (.mul (.var 2) (.add (.int (1)) (.add (.mul (.var 4) (.var 6)) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2))))))

theorem certificate_T_3_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))-(((env 3) * (env 2)))) = (2*env 9-1)*exprEval env witness_T_3_3_0 + (env 2*env 8-1)*exprEval env witness_T_3_3_1 + (env 1*env 7-1)*exprEval env witness_T_3_3_2 + (env 4*env 6-1)*exprEval env witness_T_3_3_3 := by
  dsimp only [reducedOriginalVars, witness_T_3_3_0, witness_T_3_3_1, witness_T_3_3_2, witness_T_3_3_3, exprEval]
  grind

theorem original_T_3_3 (z : ReducedChart R) :
    litT (originalChart z) 3 3=reduced_T z 3 3 := by
  have h := certificate_T_3_3 (reducedVars z)
  change 1*(litT (originalChart z) 3 3-reduced_T z 3 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_3_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_3_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_3_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_3_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_3_4_0 : RingExpr := (.int (0))

def witness_T_3_4_1 : RingExpr := (.int (0))

def witness_T_3_4_2 : RingExpr := (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))

def witness_T_3_4_3 : RingExpr := (.mul (.var 2) (.add (.int (1)) (.mul (.var 4) (.var 6))))

theorem certificate_T_3_4 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))-(((1 * (env 9)^1) + (env 2)))) = (2*env 9-1)*exprEval env witness_T_3_4_0 + (env 2*env 8-1)*exprEval env witness_T_3_4_1 + (env 1*env 7-1)*exprEval env witness_T_3_4_2 + (env 4*env 6-1)*exprEval env witness_T_3_4_3 := by
  dsimp only [reducedOriginalVars, witness_T_3_4_0, witness_T_3_4_1, witness_T_3_4_2, witness_T_3_4_3, exprEval]
  grind

theorem original_T_3_4 (z : ReducedChart R) :
    litT (originalChart z) 3 4=reduced_T z 3 4 := by
  have h := certificate_T_3_4 (reducedVars z)
  change 1*(litT (originalChart z) 3 4-reduced_T z 3 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_3_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_3_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_3_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_3_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_3_5_0 : RingExpr := (.int (0))

def witness_T_3_5_1 : RingExpr := (.int (0))

def witness_T_3_5_2 : RingExpr := (.mul (.int (-1)) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2))))

def witness_T_3_5_3 : RingExpr := (.mul (.int (-1)) (.mul (.var 2) (.add (.int (1)) (.mul (.var 4) (.var 6)))))

theorem certificate_T_3_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.var 2) (.var 4)) (.add (.mul (.var 1) (.mul (.var 3) (.var 4))) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))-(((1 * (env 9)^1) + ((-1) * (env 2))))) = (2*env 9-1)*exprEval env witness_T_3_5_0 + (env 2*env 8-1)*exprEval env witness_T_3_5_1 + (env 1*env 7-1)*exprEval env witness_T_3_5_2 + (env 4*env 6-1)*exprEval env witness_T_3_5_3 := by
  dsimp only [reducedOriginalVars, witness_T_3_5_0, witness_T_3_5_1, witness_T_3_5_2, witness_T_3_5_3, exprEval]
  grind

theorem original_T_3_5 (z : ReducedChart R) :
    litT (originalChart z) 3 5=reduced_T z 3 5 := by
  have h := certificate_T_3_5 (reducedVars z)
  change 1*(litT (originalChart z) 3 5-reduced_T z 3 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_3_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_3_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_3_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_3_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_4_0_0 : RingExpr := (.mul (.var 6) (.add (.mul (.int (-2)) (.mul (.var 7) (.var 2))) (.add (.mul (.int (-3)) (.mul (.var 3) (.mul (.var 1) (.var 7)))) (.add (.mul (.int (3)) (.mul (.var 3) (.mul (.var 4) (.var 6)))) (.add (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 1) (.mul (.var 7) (.var 2))))) (.add (.mul (.int (2)) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2))))) (.add (.mul (.int (6)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 7) (.pow (.var 1) 2))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 1) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))))) (.mul (.int (2)) (.mul (.var 3) (.mul (.var 1) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))))))))))))))

def witness_T_4_0_1 : RingExpr := (.int (0))

def witness_T_4_0_2 : RingExpr := (.mul (.var 3) (.mul (.var 6) (.add (.int (-3)) (.add (.mul (.int (-2)) (.var 2)) (.add (.mul (.int (6)) (.mul (.var 0) (.var 1))) (.mul (.int (2)) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))))))))

def witness_T_4_0_3 : RingExpr := (.mul (.var 6) (.add (.mul (.int (3)) (.var 3)) (.add (.mul (.int (2)) (.mul (.var 3) (.var 2))) (.add (.mul (.int (2)) (.mul (.var 7) (.var 2))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 3) (.var 1)))) (.add (.mul (.int (2)) (.mul (.var 3) (.mul (.var 4) (.mul (.var 6) (.var 2))))) (.add (.mul (.int (2)) (.mul (.var 3) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2))))) (.add (.mul (.int (2)) (.mul (.var 4) (.mul (.var 6) (.mul (.var 7) (.var 2))))) (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.mul (.var 6) (.var 1))))))))))))))

theorem certificate_T_4_0 (env : Nat → R) :
    2*(exprEval (reducedOriginalVars env) ((.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-6)) (.mul (.var 6) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))-(((2 * (env 9) * (env 6) * (env 7) * (env 2)) + (3 * (env 9) * (env 3) * (env 6) * (env 1) * (env 7)) + ((-6) * (env 0) * (env 9) * (env 3) * (env 6) * (env 7) * ((env 1)^2)) + (2 * (env 9) * (env 3) * (env 6) * (env 1) * (env 7) * (env 2))))) = (2*env 9-1)*exprEval env witness_T_4_0_0 + (env 2*env 8-1)*exprEval env witness_T_4_0_1 + (env 1*env 7-1)*exprEval env witness_T_4_0_2 + (env 4*env 6-1)*exprEval env witness_T_4_0_3 := by
  dsimp only [reducedOriginalVars, witness_T_4_0_0, witness_T_4_0_1, witness_T_4_0_2, witness_T_4_0_3, exprEval]
  grind

theorem original_T_4_0 (z : ReducedChart R) :
    litT (originalChart z) 4 0=reduced_T z 4 0 := by
  have h := certificate_T_4_0 (reducedVars z)
  change 2*(litT (originalChart z) 4 0-reduced_T z 4 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_4_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_4_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_4_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_4_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  have hz : 2*(litT (originalChart z) 4 0-reduced_T z 4 0)=0 := by grind
  have hz0 := half_cancel_two z.half _ z.half_unit hz
  grind

def witness_T_4_1_0 : RingExpr := (.mul (.int (3)) (.mul (.var 3) (.add (.mul (.int (-1)) (.var 0)) (.add (.mul (.var 0) (.mul (.var 1) (.mul (.var 7) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3))))) (.add (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 1) (.mul (.var 7) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))))) (.mul (.int (2)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 7) (.mul (.pow (.var 4) 4) (.mul (.pow (.var 6) 4) (.pow (.var 1) 2))))))))))))

def witness_T_4_1_1 : RingExpr := (.int (0))

def witness_T_4_1_2 : RingExpr := (.mul (.int (3)) (.mul (.var 3) (.mul (.pow (.var 4) 3) (.mul (.pow (.var 6) 3) (.add (.var 0) (.add (.mul (.int (-2)) (.var 3)) (.mul (.int (2)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.mul (.var 6) (.var 1))))))))))))

def witness_T_4_1_3 : RingExpr := (.mul (.int (3)) (.mul (.var 3) (.add (.var 0) (.add (.mul (.int (-2)) (.var 3)) (.add (.mul (.var 0) (.mul (.var 4) (.var 6))) (.add (.mul (.var 0) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 4) (.var 6)))) (.add (.mul (.int (-2)) (.mul (.var 3) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))) (.add (.mul (.int (2)) (.mul (.var 0) (.mul (.var 3) (.var 1)))) (.add (.mul (.int (2)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.mul (.var 6) (.var 1)))))) (.add (.mul (.int (2)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 1) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))))) (.mul (.int (2)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 1) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))))))))))))))))

theorem certificate_T_4_1 (env : Nat → R) :
    2*(exprEval (reducedOriginalVars env) ((.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-8)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 6) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 6) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))-((((-3) * ((env 3)^2)) + ((3 * (env 9)^1) * (env 0) * (env 3)) + (3 * (env 0) * (env 1) * ((env 3)^2))))) = (2*env 9-1)*exprEval env witness_T_4_1_0 + (env 2*env 8-1)*exprEval env witness_T_4_1_1 + (env 1*env 7-1)*exprEval env witness_T_4_1_2 + (env 4*env 6-1)*exprEval env witness_T_4_1_3 := by
  dsimp only [reducedOriginalVars, witness_T_4_1_0, witness_T_4_1_1, witness_T_4_1_2, witness_T_4_1_3, exprEval]
  grind

theorem original_T_4_1 (z : ReducedChart R) :
    litT (originalChart z) 4 1=reduced_T z 4 1 := by
  have h := certificate_T_4_1 (reducedVars z)
  change 2*(litT (originalChart z) 4 1-reduced_T z 4 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_4_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_4_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_4_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_4_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  have hz : 2*(litT (originalChart z) 4 1-reduced_T z 4 1)=0 := by grind
  have hz0 := half_cancel_two z.half _ z.half_unit hz
  grind

def witness_T_4_2_0 : RingExpr := (.int (0))

def witness_T_4_2_1 : RingExpr := (.int (0))

def witness_T_4_2_2 : RingExpr := (.int (0))

def witness_T_4_2_3 : RingExpr := (.int (0))

theorem certificate_T_4_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.var 8) (.add (.int (-1)) (.mul (.int (-1)) (.mul (.var 6) (.var 2))))))-((((-1) * (env 6)) + ((env 4) * (env 6) * ((env 3)^2)) + ((-1) * (env 0) * (env 3) * (env 4) * (env 6))))) = (2*env 9-1)*exprEval env witness_T_4_2_0 + (env 2*env 8-1)*exprEval env witness_T_4_2_1 + (env 1*env 7-1)*exprEval env witness_T_4_2_2 + (env 4*env 6-1)*exprEval env witness_T_4_2_3 := by
  dsimp only [reducedOriginalVars, witness_T_4_2_0, witness_T_4_2_1, witness_T_4_2_2, witness_T_4_2_3, exprEval]
  grind

theorem original_T_4_2 (z : ReducedChart R) :
    litT (originalChart z) 4 2=reduced_T z 4 2 := by
  have h := certificate_T_4_2 (reducedVars z)
  change 1*(litT (originalChart z) 4 2-reduced_T z 4 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_4_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_4_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_4_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_4_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_4_3_0 : RingExpr := (.int (0))

def witness_T_4_3_1 : RingExpr := (.int (0))

def witness_T_4_3_2 : RingExpr := (.int (0))

def witness_T_4_3_3 : RingExpr := (.int (0))

theorem certificate_T_4_3 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_4_3_0 + (env 2*env 8-1)*exprEval env witness_T_4_3_1 + (env 1*env 7-1)*exprEval env witness_T_4_3_2 + (env 4*env 6-1)*exprEval env witness_T_4_3_3 := by
  dsimp only [reducedOriginalVars, witness_T_4_3_0, witness_T_4_3_1, witness_T_4_3_2, witness_T_4_3_3, exprEval]
  grind

theorem original_T_4_3 (z : ReducedChart R) :
    litT (originalChart z) 4 3=reduced_T z 4 3 := by
  have h := certificate_T_4_3 (reducedVars z)
  change 1*(litT (originalChart z) 4 3-reduced_T z 4 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_4_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_4_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_4_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_4_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_4_4_0 : RingExpr := (.int (0))

def witness_T_4_4_1 : RingExpr := (.int (0))

def witness_T_4_4_2 : RingExpr := (.int (0))

def witness_T_4_4_3 : RingExpr := (.mul (.int (-3)) (.mul (.var 3) (.add (.int (-1)) (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 6) (.var 1))))))))

theorem certificate_T_4_4 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.mul (.var 8) (.add (.mul (.int (-2)) (.var 2)) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int (-3)) (.mul (.var 6) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))-(((3 * (env 3)) + ((-3) * (env 0) * (env 3) * (env 1))))) = (2*env 9-1)*exprEval env witness_T_4_4_0 + (env 2*env 8-1)*exprEval env witness_T_4_4_1 + (env 1*env 7-1)*exprEval env witness_T_4_4_2 + (env 4*env 6-1)*exprEval env witness_T_4_4_3 := by
  dsimp only [reducedOriginalVars, witness_T_4_4_0, witness_T_4_4_1, witness_T_4_4_2, witness_T_4_4_3, exprEval]
  grind

theorem original_T_4_4 (z : ReducedChart R) :
    litT (originalChart z) 4 4=reduced_T z 4 4 := by
  have h := certificate_T_4_4 (reducedVars z)
  change 1*(litT (originalChart z) 4 4-reduced_T z 4 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_4_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_4_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_4_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_4_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_4_5_0 : RingExpr := (.int (0))

def witness_T_4_5_1 : RingExpr := (.int (0))

def witness_T_4_5_2 : RingExpr := (.int (0))

def witness_T_4_5_3 : RingExpr := (.int (0))

theorem certificate_T_4_5 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_4_5_0 + (env 2*env 8-1)*exprEval env witness_T_4_5_1 + (env 1*env 7-1)*exprEval env witness_T_4_5_2 + (env 4*env 6-1)*exprEval env witness_T_4_5_3 := by
  dsimp only [reducedOriginalVars, witness_T_4_5_0, witness_T_4_5_1, witness_T_4_5_2, witness_T_4_5_3, exprEval]
  grind

theorem original_T_4_5 (z : ReducedChart R) :
    litT (originalChart z) 4 5=reduced_T z 4 5 := by
  have h := certificate_T_4_5 (reducedVars z)
  change 1*(litT (originalChart z) 4 5-reduced_T z 4 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_4_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_4_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_4_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_4_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_5_0_0 : RingExpr := (.int (0))

def witness_T_5_0_1 : RingExpr := (.int (0))

def witness_T_5_0_2 : RingExpr := (.int (0))

def witness_T_5_0_3 : RingExpr := (.int (0))

theorem certificate_T_5_0 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.var 0))-(((env 6) * (env 7) * (env 2)))) = (2*env 9-1)*exprEval env witness_T_5_0_0 + (env 2*env 8-1)*exprEval env witness_T_5_0_1 + (env 1*env 7-1)*exprEval env witness_T_5_0_2 + (env 4*env 6-1)*exprEval env witness_T_5_0_3 := by
  dsimp only [reducedOriginalVars, witness_T_5_0_0, witness_T_5_0_1, witness_T_5_0_2, witness_T_5_0_3, exprEval]
  grind

theorem original_T_5_0 (z : ReducedChart R) :
    litT (originalChart z) 5 0=reduced_T z 5 0 := by
  have h := certificate_T_5_0 (reducedVars z)
  change 1*(litT (originalChart z) 5 0-reduced_T z 5 0) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_5_0_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_5_0_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_5_0_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_5_0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_5_1_0 : RingExpr := (.mul (.int (-1)) (.mul (.var 6) (.mul (.add (.int (-1)) (.mul (.var 1) (.mul (.var 7) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2))))) (.add (.int (1)) (.add (.mul (.int (2)) (.mul (.var 4) (.mul (.var 2) (.pow (.var 3) 2)))) (.mul (.int (2)) (.mul (.var 1) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 2))))))))))))

def witness_T_5_1_1 : RingExpr := (.int (0))

def witness_T_5_1_2 : RingExpr := (.mul (.int (-1)) (.mul (.pow (.var 4) 2) (.mul (.pow (.var 6) 3) (.add (.int (1)) (.add (.mul (.int (2)) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 2))))) (.mul (.int (2)) (.mul (.var 1) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 2))))))))))))

def witness_T_5_1_3 : RingExpr := (.mul (.int (-1)) (.mul (.var 6) (.mul (.add (.int (1)) (.mul (.var 4) (.var 6))) (.add (.int (1)) (.add (.mul (.int (2)) (.mul (.var 4) (.mul (.var 2) (.pow (.var 3) 2)))) (.mul (.int (2)) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 2))))))))))

theorem certificate_T_5_1 (env : Nat → R) :
    2*(exprEval (reducedOriginalVars env) ((.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))-((((-1) * (env 9) * (env 6)) + ((-2) * (env 9) * (env 4) * (env 6) * (env 2) * ((env 3)^2))))) = (2*env 9-1)*exprEval env witness_T_5_1_0 + (env 2*env 8-1)*exprEval env witness_T_5_1_1 + (env 1*env 7-1)*exprEval env witness_T_5_1_2 + (env 4*env 6-1)*exprEval env witness_T_5_1_3 := by
  dsimp only [reducedOriginalVars, witness_T_5_1_0, witness_T_5_1_1, witness_T_5_1_2, witness_T_5_1_3, exprEval]
  grind

theorem original_T_5_1 (z : ReducedChart R) :
    litT (originalChart z) 5 1=reduced_T z 5 1 := by
  have h := certificate_T_5_1 (reducedVars z)
  change 2*(litT (originalChart z) 5 1-reduced_T z 5 1) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_5_1_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_5_1_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_5_1_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_5_1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  have hz : 2*(litT (originalChart z) 5 1-reduced_T z 5 1)=0 := by grind
  have hz0 := half_cancel_two z.half _ z.half_unit hz
  grind

def witness_T_5_2_0 : RingExpr := (.int (0))

def witness_T_5_2_1 : RingExpr := (.int (0))

def witness_T_5_2_2 : RingExpr := (.int (0))

def witness_T_5_2_3 : RingExpr := (.int (0))

theorem certificate_T_5_2 (env : Nat → R) :
    1*(exprEval (reducedOriginalVars env) ((.int 0))-(0)) = (2*env 9-1)*exprEval env witness_T_5_2_0 + (env 2*env 8-1)*exprEval env witness_T_5_2_1 + (env 1*env 7-1)*exprEval env witness_T_5_2_2 + (env 4*env 6-1)*exprEval env witness_T_5_2_3 := by
  dsimp only [reducedOriginalVars, witness_T_5_2_0, witness_T_5_2_1, witness_T_5_2_2, witness_T_5_2_3, exprEval]
  grind

theorem original_T_5_2 (z : ReducedChart R) :
    litT (originalChart z) 5 2=reduced_T z 5 2 := by
  have h := certificate_T_5_2 (reducedVars z)
  change 1*(litT (originalChart z) 5 2-reduced_T z 5 2) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_5_2_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_5_2_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_5_2_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_5_2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

def witness_T_5_3_0 : RingExpr := (.mul (.var 6) (.add (.int (1)) (.add (.mul (.int (-1)) (.mul (.var 4) (.var 6))) (.add (.mul (.int (-2)) (.mul (.var 4) (.mul (.var 2) (.pow (.var 3) 2)))) (.mul (.int (2)) (.mul (.var 1) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 4) 4) (.pow (.var 6) 3)))))))))))

def witness_T_5_3_1 : RingExpr := (.int (0))

def witness_T_5_3_2 : RingExpr := (.mul (.int (2)) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 4) 4) (.pow (.var 6) 4)))))

def witness_T_5_3_3 : RingExpr := (.mul (.var 6) (.add (.int (-1)) (.add (.mul (.int (2)) (.mul (.var 4) (.mul (.var 2) (.pow (.var 3) 2)))) (.add (.mul (.int (2)) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int (2)) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 2)))))))))

theorem certificate_T_5_3 (env : Nat → R) :
    2*(exprEval (reducedOriginalVars env) ((.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.var 3)) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))))))))))-((((-1) * (env 9) * (env 6)) + (2 * (env 9) * (env 4) * (env 6) * (env 2) * ((env 3)^2))))) = (2*env 9-1)*exprEval env witness_T_5_3_0 + (env 2*env 8-1)*exprEval env witness_T_5_3_1 + (env 1*env 7-1)*exprEval env witness_T_5_3_2 + (env 4*env 6-1)*exprEval env witness_T_5_3_3 := by
  dsimp only [reducedOriginalVars, witness_T_5_3_0, witness_T_5_3_1, witness_T_5_3_2, witness_T_5_3_3, exprEval]
  grind

theorem original_T_5_3 (z : ReducedChart R) :
    litT (originalChart z) 5 3=reduced_T z 5 3 := by
  have h := certificate_T_5_3 (reducedVars z)
  change 2*(litT (originalChart z) 5 3-reduced_T z 5 3) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_5_3_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_5_3_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_5_3_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_5_3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  have hz : 2*(litT (originalChart z) 5 3-reduced_T z 5 3)=0 := by grind
  have hz0 := half_cancel_two z.half _ z.half_unit hz
  grind

def witness_T_5_4_0 : RingExpr := (.mul (.var 3) (.add (.int (-1)) (.add (.mul (.var 4) (.var 6)) (.mul (.int (2)) (.mul (.var 1) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))))))))

def witness_T_5_4_1 : RingExpr := (.int (0))

def witness_T_5_4_2 : RingExpr := (.mul (.int (2)) (.mul (.var 3) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))))

def witness_T_5_4_3 : RingExpr := (.mul (.var 3) (.add (.int (1)) (.add (.mul (.int (2)) (.var 2)) (.add (.mul (.int (2)) (.mul (.var 4) (.mul (.var 6) (.var 2)))) (.mul (.int (2)) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2))))))))

theorem certificate_T_5_4 (env : Nat → R) :
    2*(exprEval (reducedOriginalVars env) ((.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))-((((1 * (env 9)^1) * (env 3)) + ((env 3) * (env 2))))) = (2*env 9-1)*exprEval env witness_T_5_4_0 + (env 2*env 8-1)*exprEval env witness_T_5_4_1 + (env 1*env 7-1)*exprEval env witness_T_5_4_2 + (env 4*env 6-1)*exprEval env witness_T_5_4_3 := by
  dsimp only [reducedOriginalVars, witness_T_5_4_0, witness_T_5_4_1, witness_T_5_4_2, witness_T_5_4_3, exprEval]
  grind

theorem original_T_5_4 (z : ReducedChart R) :
    litT (originalChart z) 5 4=reduced_T z 5 4 := by
  have h := certificate_T_5_4 (reducedVars z)
  change 2*(litT (originalChart z) 5 4-reduced_T z 5 4) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_5_4_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_5_4_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_5_4_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_5_4_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  have hz : 2*(litT (originalChart z) 5 4-reduced_T z 5 4)=0 := by grind
  have hz0 := half_cancel_two z.half _ z.half_unit hz
  grind

def witness_T_5_5_0 : RingExpr := (.mul (.int (-1)) (.mul (.var 3) (.add (.int (1)) (.add (.mul (.int (-1)) (.mul (.var 4) (.var 6))) (.mul (.int (2)) (.mul (.var 1) (.mul (.var 7) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3))))))))))

def witness_T_5_5_1 : RingExpr := (.int (0))

def witness_T_5_5_2 : RingExpr := (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 2) (.mul (.pow (.var 4) 3) (.pow (.var 6) 3)))))

def witness_T_5_5_3 : RingExpr := (.mul (.int (-1)) (.mul (.var 3) (.add (.int (-1)) (.add (.mul (.int (2)) (.var 2)) (.add (.mul (.int (2)) (.mul (.var 4) (.mul (.var 6) (.var 2)))) (.mul (.int (2)) (.mul (.var 2) (.mul (.pow (.var 4) 2) (.pow (.var 6) 2)))))))))

theorem certificate_T_5_5 (env : Nat → R) :
    2*(exprEval (reducedOriginalVars env) ((.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))-((((1 * (env 9)^1) * (env 3)) + ((-1) * (env 3) * (env 2))))) = (2*env 9-1)*exprEval env witness_T_5_5_0 + (env 2*env 8-1)*exprEval env witness_T_5_5_1 + (env 1*env 7-1)*exprEval env witness_T_5_5_2 + (env 4*env 6-1)*exprEval env witness_T_5_5_3 := by
  dsimp only [reducedOriginalVars, witness_T_5_5_0, witness_T_5_5_1, witness_T_5_5_2, witness_T_5_5_3, exprEval]
  grind

theorem original_T_5_5 (z : ReducedChart R) :
    litT (originalChart z) 5 5=reduced_T z 5 5 := by
  have h := certificate_T_5_5 (reducedVars z)
  change 2*(litT (originalChart z) 5 5-reduced_T z 5 5) =
    (2*z.half-1)*exprEval (reducedVars z) witness_T_5_5_0 +
    (z.u*z.ui-1)*exprEval (reducedVars z) witness_T_5_5_1 +
    (z.t*z.ti-1)*exprEval (reducedVars z) witness_T_5_5_2 +
    (z.q*z.qi-1)*exprEval (reducedVars z) witness_T_5_5_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  have hz : 2*(litT (originalChart z) 5 5-reduced_T z 5 5)=0 := by grind
  have hz0 := half_cancel_two z.half _ z.half_unit hz
  grind

theorem original_T (z : ReducedChart R) : litT (originalChart z)=reduced_T z := by
  funext r c
  exact (Fin.cases ((Fin.cases (original_T_0_0 z) (fun c => (Fin.cases (original_T_0_1 z) (fun c => (Fin.cases (original_T_0_2 z) (fun c => (Fin.cases (original_T_0_3 z) (fun c => (Fin.cases (original_T_0_4 z) (fun c => (Fin.cases (original_T_0_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.cases ((Fin.cases (original_T_1_0 z) (fun c => (Fin.cases (original_T_1_1 z) (fun c => (Fin.cases (original_T_1_2 z) (fun c => (Fin.cases (original_T_1_3 z) (fun c => (Fin.cases (original_T_1_4 z) (fun c => (Fin.cases (original_T_1_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.cases ((Fin.cases (original_T_2_0 z) (fun c => (Fin.cases (original_T_2_1 z) (fun c => (Fin.cases (original_T_2_2 z) (fun c => (Fin.cases (original_T_2_3 z) (fun c => (Fin.cases (original_T_2_4 z) (fun c => (Fin.cases (original_T_2_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.cases ((Fin.cases (original_T_3_0 z) (fun c => (Fin.cases (original_T_3_1 z) (fun c => (Fin.cases (original_T_3_2 z) (fun c => (Fin.cases (original_T_3_3 z) (fun c => (Fin.cases (original_T_3_4 z) (fun c => (Fin.cases (original_T_3_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.cases ((Fin.cases (original_T_4_0 z) (fun c => (Fin.cases (original_T_4_1 z) (fun c => (Fin.cases (original_T_4_2 z) (fun c => (Fin.cases (original_T_4_3 z) (fun c => (Fin.cases (original_T_4_4 z) (fun c => (Fin.cases (original_T_4_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.cases ((Fin.cases (original_T_5_0 z) (fun c => (Fin.cases (original_T_5_1 z) (fun c => (Fin.cases (original_T_5_2 z) (fun c => (Fin.cases (original_T_5_3 z) (fun c => (Fin.cases (original_T_5_4 z) (fun c => (Fin.cases (original_T_5_5 z) (fun c => (Fin.elim0 c)) c)) c)) c)) c)) c)) c)) (fun r => (Fin.elim0 r)) r)) r)) r)) r)) r)) r)

#print axioms original_T
end StackSorting.RationalLift
