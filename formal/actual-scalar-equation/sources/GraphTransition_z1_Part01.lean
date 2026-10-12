import GraphTransition_z1_Part00
import UnitSplitFactorCertificates
import GraphUnitWitness
import LiteralEntryNormalization
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem trans_z_1_8_coef5_cert (e : Nat → R) :
    (2:R)^2*exprEval e trans_z_1_8_coef5=(2*e 10-1)*exprEval e trans_z_1_8_coef5_w0 + (e 4*e 9-1)*exprEval e trans_z_1_8_coef5_w1 + (e 3*e 8-1)*exprEval e trans_z_1_8_coef5_w2 + (e 0*e 7-1)*exprEval e trans_z_1_8_coef5_w3 := by
  dsimp only [trans_z_1_8_coef5, trans_z_1_8_coef5_w0, trans_z_1_8_coef5_w1, trans_z_1_8_coef5_w2, trans_z_1_8_coef5_w3, exprEval] <;> grind

theorem trans_z_1_8_coef5_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_z_1_8_coef5=0 :=
  unitIdealClearZero 2 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_z_1_8_coef5_cert (chartVars y beta))

def trans_z_1_8_coef6 : RingExpr := (.mul (.int (-2)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.var 8)) (.add (.mul (.int (-4)) (.pow (.var 4) 2)) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 8) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 3))))))))))))))))
def trans_z_1_8_coef6_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.var 8)) (.add (.mul (.int (-4)) (.pow (.var 4) 2)) (.add (.mul (.int (-8)) (.mul (.var 10) (.pow (.var 4) 2))) (.add (.mul (.int (-2)) (.mul (.var 10) (.var 8))) (.add (.mul (.var 8) (.mul (.var 4) (.var 9))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 3))))) (.add (.mul (.int 4) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2))))) (.add (.mul (.int 8) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 3)))))) (.mul (.int 16) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 4) 3)))))))))))))))))))))
def trans_z_1_8_coef6_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-4)) (.var 4)) (.add (.mul (.var 8) (.var 9)) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))))))))))
def trans_z_1_8_coef6_w2 : RingExpr := (.mul (.int (-4)) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2)))))
def trans_z_1_8_coef6_w3 : RingExpr := (.int 0)

theorem trans_z_1_8_coef6_cert (e : Nat → R) :
    (2:R)^1*exprEval e trans_z_1_8_coef6=(2*e 10-1)*exprEval e trans_z_1_8_coef6_w0 + (e 4*e 9-1)*exprEval e trans_z_1_8_coef6_w1 + (e 3*e 8-1)*exprEval e trans_z_1_8_coef6_w2 + (e 0*e 7-1)*exprEval e trans_z_1_8_coef6_w3 := by
  dsimp only [trans_z_1_8_coef6, trans_z_1_8_coef6_w0, trans_z_1_8_coef6_w1, trans_z_1_8_coef6_w2, trans_z_1_8_coef6_w3, exprEval] <;> grind

theorem trans_z_1_8_coef6_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_z_1_8_coef6=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_z_1_8_coef6_cert (chartVars y beta))

def trans_z_1_8_coef7 : RingExpr := (.mul (.int (-8)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.add (.int 1) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 8))) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def trans_z_1_8_coef7_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.add (.int 1) (.add (.mul (.int 2) (.var 10)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-4)) (.mul (.var 10) (.mul (.var 3) (.var 8)))) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))))))))))))))
def trans_z_1_8_coef7_w1 : RingExpr := (.mul (.int (-2)) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 8))) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))
def trans_z_1_8_coef7_w2 : RingExpr := (.mul (.int 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2))))
def trans_z_1_8_coef7_w3 : RingExpr := (.int 0)

theorem trans_z_1_8_coef7_cert (e : Nat → R) :
    (2:R)^0*exprEval e trans_z_1_8_coef7=(2*e 10-1)*exprEval e trans_z_1_8_coef7_w0 + (e 4*e 9-1)*exprEval e trans_z_1_8_coef7_w1 + (e 3*e 8-1)*exprEval e trans_z_1_8_coef7_w2 + (e 0*e 7-1)*exprEval e trans_z_1_8_coef7_w3 := by
  dsimp only [trans_z_1_8_coef7, trans_z_1_8_coef7_w0, trans_z_1_8_coef7_w1, trans_z_1_8_coef7_w2, trans_z_1_8_coef7_w3, exprEval] <;> grind

theorem trans_z_1_8_coef7_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_z_1_8_coef7=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_z_1_8_coef7_cert (chartVars y beta))

def trans_z_1_8_coef8 : RingExpr := (.mul (.int (-8)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int 1) (.add (.mul (.int (-3)) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))) (.mul (.int 4) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))))
def trans_z_1_8_coef8_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int 1) (.add (.mul (.int 2) (.var 10)) (.add (.mul (.int (-3)) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.var 8)))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 4) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.mul (.int 8) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))))))))))))))))))
def trans_z_1_8_coef8_w1 : RingExpr := (.mul (.int (-2)) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 4) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))) (.mul (.int 2) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))
def trans_z_1_8_coef8_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 4) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))
def trans_z_1_8_coef8_w3 : RingExpr := (.int 0)

theorem trans_z_1_8_coef8_cert (e : Nat → R) :
    (2:R)^0*exprEval e trans_z_1_8_coef8=(2*e 10-1)*exprEval e trans_z_1_8_coef8_w0 + (e 4*e 9-1)*exprEval e trans_z_1_8_coef8_w1 + (e 3*e 8-1)*exprEval e trans_z_1_8_coef8_w2 + (e 0*e 7-1)*exprEval e trans_z_1_8_coef8_w3 := by
  dsimp only [trans_z_1_8_coef8, trans_z_1_8_coef8_w0, trans_z_1_8_coef8_w1, trans_z_1_8_coef8_w2, trans_z_1_8_coef8_w3, exprEval] <;> grind

theorem trans_z_1_8_coef8_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_z_1_8_coef8=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_z_1_8_coef8_cert (chartVars y beta))

def trans_z_1_8_coef9 : RingExpr := (.mul (.int (-8)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9))))))))))))
def trans_z_1_8_coef9_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 4) (.var 9)) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.mul (.int 4) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2))))))))))))))
def trans_z_1_8_coef9_w1 : RingExpr := (.mul (.int (-2)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.pow (.var 4) 3))))))
def trans_z_1_8_coef9_w2 : RingExpr := (.int 0)
def trans_z_1_8_coef9_w3 : RingExpr := (.int 0)

theorem trans_z_1_8_coef9_cert (e : Nat → R) :
    (2:R)^0*exprEval e trans_z_1_8_coef9=(2*e 10-1)*exprEval e trans_z_1_8_coef9_w0 + (e 4*e 9-1)*exprEval e trans_z_1_8_coef9_w1 + (e 3*e 8-1)*exprEval e trans_z_1_8_coef9_w2 + (e 0*e 7-1)*exprEval e trans_z_1_8_coef9_w3 := by
  dsimp only [trans_z_1_8_coef9, trans_z_1_8_coef9_w0, trans_z_1_8_coef9_w1, trans_z_1_8_coef9_w2, trans_z_1_8_coef9_w3, exprEval] <;> grind

theorem trans_z_1_8_coef9_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_z_1_8_coef9=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_z_1_8_coef9_cert (chartVars y beta))

def trans_z_1_8_coef10 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.mul (.int 2) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 10) (.var 8)))) (.add (.mul (.int 6) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.pow (.var 8) 2))))) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))) (.add (.mul (.int (-10)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))))))))
def trans_z_1_8_coef10_w0 : RingExpr := (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.mul (.var 7) (.var 8))) (.add (.mul (.int 4) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.var 8)))) (.add (.mul (.int 6) (.mul (.var 7) (.mul (.var 3) (.pow (.var 8) 2)))) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 3) (.mul (.var 8) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.pow (.var 8) 2))))) (.add (.mul (.int (-16)) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.add (.mul (.int (-5)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 7) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 16) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.pow (.var 4) 2)))))) (.add (.mul (.int (-24)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))) (.add (.mul (.int (-20)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))))) (.add (.mul (.int (-10)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2))))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))))))))))))))))
def trans_z_1_8_coef10_w1 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.mul (.var 7) (.var 8))) (.add (.mul (.int 4) (.mul (.var 3) (.var 4))) (.add (.mul (.var 7) (.mul (.var 3) (.pow (.var 8) 2))) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 3) (.mul (.var 8) (.pow (.var 4) 2))))) (.add (.mul (.int (-10)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.add (.mul (.int (-5)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 7) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))))))))))))
def trans_z_1_8_coef10_w2 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-4)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 7) (.pow (.var 8) 2))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.var 4)))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.mul (.var 8) (.var 4)))))) (.mul (.int 10) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))))
def trans_z_1_8_coef10_w3 : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 4) (.pow (.var 8) 2))))

theorem trans_z_1_8_coef10_cert (e : Nat → R) :
    (2:R)^1*exprEval e trans_z_1_8_coef10=(2*e 10-1)*exprEval e trans_z_1_8_coef10_w0 + (e 4*e 9-1)*exprEval e trans_z_1_8_coef10_w1 + (e 3*e 8-1)*exprEval e trans_z_1_8_coef10_w2 + (e 0*e 7-1)*exprEval e trans_z_1_8_coef10_w3 := by
  dsimp only [trans_z_1_8_coef10, trans_z_1_8_coef10_w0, trans_z_1_8_coef10_w1, trans_z_1_8_coef10_w2, trans_z_1_8_coef10_w3, exprEval] <;> grind

theorem trans_z_1_8_coef10_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_z_1_8_coef10=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_z_1_8_coef10_cert (chartVars y beta))

def trans_z_1_8_coef11 : RingExpr := (.mul (.int (-8)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int (-1)) (.var 8)) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))))
def trans_z_1_8_coef11_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int (-1)) (.var 8)) (.add (.mul (.int (-2)) (.mul (.var 10) (.var 8))) (.add (.mul (.var 8) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 3) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))))))))))))))))
def trans_z_1_8_coef11_w1 : RingExpr := (.mul (.int (-2)) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.var 8) (.var 9)) (.add (.mul (.int (-3)) (.mul (.var 0) (.var 3))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))))))))))
def trans_z_1_8_coef11_w2 : RingExpr := (.mul (.int (-6)) (.mul (.var 0) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2))))))
def trans_z_1_8_coef11_w3 : RingExpr := (.int 0)

theorem trans_z_1_8_coef11_cert (e : Nat → R) :
    (2:R)^0*exprEval e trans_z_1_8_coef11=(2*e 10-1)*exprEval e trans_z_1_8_coef11_w0 + (e 4*e 9-1)*exprEval e trans_z_1_8_coef11_w1 + (e 3*e 8-1)*exprEval e trans_z_1_8_coef11_w2 + (e 0*e 7-1)*exprEval e trans_z_1_8_coef11_w3 := by
  dsimp only [trans_z_1_8_coef11, trans_z_1_8_coef11_w0, trans_z_1_8_coef11_w1, trans_z_1_8_coef11_w2, trans_z_1_8_coef11_w3, exprEval] <;> grind

theorem trans_z_1_8_coef11_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_z_1_8_coef11=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_z_1_8_coef11_cert (chartVars y beta))

def trans_z_1_8_coef12 : RingExpr := (.mul (.int (-8)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8))))))))))
def trans_z_1_8_coef12_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.mul (.add (.int 1) (.mul (.int 2) (.var 10))) (.add (.int (-1)) (.mul (.var 3) (.var 8))))))))))
def trans_z_1_8_coef12_w1 : RingExpr := (.mul (.int (-2)) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.var 3) (.var 8))))))))
def trans_z_1_8_coef12_w2 : RingExpr := (.mul (.int (-2)) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2)))))
def trans_z_1_8_coef12_w3 : RingExpr := (.int 0)

theorem trans_z_1_8_coef12_cert (e : Nat → R) :
    (2:R)^0*exprEval e trans_z_1_8_coef12=(2*e 10-1)*exprEval e trans_z_1_8_coef12_w0 + (e 4*e 9-1)*exprEval e trans_z_1_8_coef12_w1 + (e 3*e 8-1)*exprEval e trans_z_1_8_coef12_w2 + (e 0*e 7-1)*exprEval e trans_z_1_8_coef12_w3 := by
  dsimp only [trans_z_1_8_coef12, trans_z_1_8_coef12_w0, trans_z_1_8_coef12_w1, trans_z_1_8_coef12_w2, trans_z_1_8_coef12_w3, exprEval] <;> grind

theorem trans_z_1_8_coef12_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_z_1_8_coef12=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_z_1_8_coef12_cert (chartVars y beta))

def trans_z_1_8_coef13 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.mul (.int 2) (.var 4)) (.add (.mul (.var 7) (.mul (.var 10) (.pow (.var 8) 2))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.pow (.var 4) 2))))) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2)))))) (.add (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 4)))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4)))))))))))))))))))))))))
def trans_z_1_8_coef13_w0 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.mul (.int 4) (.var 4)) (.add (.mul (.var 7) (.pow (.var 8) 2)) (.add (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.pow (.var 8) 2)))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 8) (.pow (.var 4) 2)))) (.add (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2))))) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.pow (.var 4) 2))))) (.add (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.mul (.var 8) (.var 4))))) (.add (.mul (.int (-16)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))) (.add (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 4))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4))))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int 16) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.add (.mul (.int 16) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4)))))))) (.mul (.int 32) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4))))))))))))))))))))))))))))))))))))))
def trans_z_1_8_coef13_w1 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.add (.int 4) (.add (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 9) (.pow (.var 8) 2)))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 8) (.var 4)))) (.add (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.var 8)))) (.add (.mul (.int (-5)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.add (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))))))))))))))))
def trans_z_1_8_coef13_w2 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.int 4) (.add (.mul (.int (-4)) (.mul (.var 0) (.var 7))) (.add (.mul (.int (-5)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.var 8))))) (.add (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))))))))
def trans_z_1_8_coef13_w3 : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.pow (.var 8) 2)))

theorem trans_z_1_8_coef13_cert (e : Nat → R) :
    (2:R)^1*exprEval e trans_z_1_8_coef13=(2*e 10-1)*exprEval e trans_z_1_8_coef13_w0 + (e 4*e 9-1)*exprEval e trans_z_1_8_coef13_w1 + (e 3*e 8-1)*exprEval e trans_z_1_8_coef13_w2 + (e 0*e 7-1)*exprEval e trans_z_1_8_coef13_w3 := by
  dsimp only [trans_z_1_8_coef13, trans_z_1_8_coef13_w0, trans_z_1_8_coef13_w1, trans_z_1_8_coef13_w2, trans_z_1_8_coef13_w3, exprEval] <;> grind

theorem trans_z_1_8_coef13_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_z_1_8_coef13=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_z_1_8_coef13_cert (chartVars y beta))

def trans_z_1_8_coef14 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-2)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 10) (.pow (.var 8) 2)))) (.add (.mul (.int 2) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 4))))))) (.mul (.int 10) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))))))))))
def trans_z_1_8_coef14_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-4)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 7) (.pow (.var 8) 2))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.pow (.var 8) 2)))) (.add (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.mul (.var 8) (.var 4)))))) (.add (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 10) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-16)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 4))))))) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.mul (.int 20) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))))))))))))))))))
def trans_z_1_8_coef14_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-4)) (.add (.mul (.var 7) (.mul (.var 9) (.pow (.var 8) 2))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.var 8))))) (.add (.mul (.int 10) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))))))))))
def trans_z_1_8_coef14_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 8) (.mul (.var 4) (.add (.int (-2)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 8))) (.add (.mul (.int 2) (.mul (.var 0) (.var 7))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.var 8))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.mul (.int 5) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))))))))))))
def trans_z_1_8_coef14_w3 : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 8) (.var 4))))

theorem trans_z_1_8_coef14_cert (e : Nat → R) :
    (2:R)^1*exprEval e trans_z_1_8_coef14=(2*e 10-1)*exprEval e trans_z_1_8_coef14_w0 + (e 4*e 9-1)*exprEval e trans_z_1_8_coef14_w1 + (e 3*e 8-1)*exprEval e trans_z_1_8_coef14_w2 + (e 0*e 7-1)*exprEval e trans_z_1_8_coef14_w3 := by
  dsimp only [trans_z_1_8_coef14, trans_z_1_8_coef14_w0, trans_z_1_8_coef14_w1, trans_z_1_8_coef14_w2, trans_z_1_8_coef14_w3, exprEval] <;> grind

theorem trans_z_1_8_coef14_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_z_1_8_coef14=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_z_1_8_coef14_cert (chartVars y beta))

def trans_z_1_8_coef15 : RingExpr := (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))))))))))))
def trans_z_1_8_coef15_w0 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 4) (.var 9)) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.mul (.int 4) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))))))))))))
def trans_z_1_8_coef15_w1 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.pow (.var 4) 2)))))))
def trans_z_1_8_coef15_w2 : RingExpr := (.int 0)
def trans_z_1_8_coef15_w3 : RingExpr := (.int 0)

end StackSorting.FiniteGraph
