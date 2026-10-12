import UnitSplitFactorCertificates
import GraphUnitWitness
import LiteralEntryNormalization
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

def quotient_b_2_0_res : RingExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.int 0) (.mul dataN19b_2_0 dataS_0_0)) (.mul dataN19b_2_1 (.int 0))) (.mul (.int 0) dataS_2_0)) (.mul dataN19b_2_3 dataS_3_0)) (.mul dataN19b_2_4 (.int 0))) (.mul dataN19b_2_5 dataS_5_0)) (.mul (.int 0) (.int 0))) (.mul (.int 0) (.int 0))) (.mul (.int 0) (.int 0))) (.mul (.int 0) (.int 0))) (.mul (.int 0) (.int 0))) (.mul (.int 0) (.int 0))) (.mul dataN19b_2_12 (.int 0))) (.mul dataN19b_2_13 (.int 0))) (.mul (.int 0) (.int 0))) (.mul dataN19b_2_15 (.int 0))) (.mul dataN19b_2_16 (.int 0))) (.mul dataN19b_2_17 (.int 0))) (.mul (.int 0) (.int 0))) (.mul (.int (-1)) (.add (.add (.add (.add (.add (.add (.add (.add (.add (.int 0) (.mul dataS_2_0 dataN9b_0_0)) (.mul dataS_2_1 dataN9b_1_0)) (.mul dataS_2_2 dataN9b_2_0)) (.mul (.int 0) (.int 0))) (.mul (.int 0) (.int 0))) (.mul (.int 0) (.int 0))) (.mul (.int 0) (.int 0))) (.mul (.int 0) (.int 0))) (.mul dataS_2_8 (.int 0)))))

def quotient_b_2_0_coef0 : RingExpr := (.mul (.int 24) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def quotient_b_2_0_coef0_w0 : RingExpr := (.mul (.int 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.add (.mul (.int (-4)) (.pow (.var 10) 2)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.mul (.int 8) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 3))))))))))))))))))
def quotient_b_2_0_coef0_w1 : RingExpr := (.mul (.int 3) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))
def quotient_b_2_0_coef0_w2 : RingExpr := (.mul (.int 3) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.pow (.var 4) 2)))))
def quotient_b_2_0_coef0_w3 : RingExpr := (.int 0)

theorem quotient_b_2_0_coef0_cert (e : Nat → R) :
    (2:R)^0*exprEval e quotient_b_2_0_coef0=(2*e 10-1)*exprEval e quotient_b_2_0_coef0_w0 + (e 4*e 9-1)*exprEval e quotient_b_2_0_coef0_w1 + (e 3*e 8-1)*exprEval e quotient_b_2_0_coef0_w2 + (e 0*e 7-1)*exprEval e quotient_b_2_0_coef0_w3 := by
  dsimp only [quotient_b_2_0_coef0, quotient_b_2_0_coef0_w0, quotient_b_2_0_coef0_w1, quotient_b_2_0_coef0_w2, quotient_b_2_0_coef0_w3, exprEval] <;> grind

theorem quotient_b_2_0_coef0_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) quotient_b_2_0_coef0=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (quotient_b_2_0_coef0_cert (chartVars y beta))

def quotient_b_2_0_coef1 : RingExpr := (.mul (.int 24) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def quotient_b_2_0_coef1_w0 : RingExpr := (.mul (.int 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.int (-4)) (.pow (.var 10) 2)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.mul (.int 8) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 3))))))))))))))))))
def quotient_b_2_0_coef1_w1 : RingExpr := (.mul (.int 3) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))
def quotient_b_2_0_coef1_w2 : RingExpr := (.mul (.int 3) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 5)))))
def quotient_b_2_0_coef1_w3 : RingExpr := (.int 0)

theorem quotient_b_2_0_coef1_cert (e : Nat → R) :
    (2:R)^0*exprEval e quotient_b_2_0_coef1=(2*e 10-1)*exprEval e quotient_b_2_0_coef1_w0 + (e 4*e 9-1)*exprEval e quotient_b_2_0_coef1_w1 + (e 3*e 8-1)*exprEval e quotient_b_2_0_coef1_w2 + (e 0*e 7-1)*exprEval e quotient_b_2_0_coef1_w3 := by
  dsimp only [quotient_b_2_0_coef1, quotient_b_2_0_coef1_w0, quotient_b_2_0_coef1_w1, quotient_b_2_0_coef1_w2, quotient_b_2_0_coef1_w3, exprEval] <;> grind

theorem quotient_b_2_0_coef1_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) quotient_b_2_0_coef1=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (quotient_b_2_0_coef1_cert (chartVars y beta))

def quotient_b_2_0_coef2 : RingExpr := (.mul (.int (-6)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.add (.int (-1)) (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def quotient_b_2_0_coef2_w0 : RingExpr := (.mul (.int (-3)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.add (.int (-1)) (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.int (-1)) (.add (.mul (.int (-4)) (.pow (.var 10) 2)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.mul (.int 8) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 3)))))))))))))))))))
def quotient_b_2_0_coef2_w1 : RingExpr := (.mul (.int (-3)) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.add (.int (-1)) (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))
def quotient_b_2_0_coef2_w2 : RingExpr := (.mul (.int (-3)) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2))))))))
def quotient_b_2_0_coef2_w3 : RingExpr := (.int 0)

theorem quotient_b_2_0_coef2_cert (e : Nat → R) :
    (2:R)^2*exprEval e quotient_b_2_0_coef2=(2*e 10-1)*exprEval e quotient_b_2_0_coef2_w0 + (e 4*e 9-1)*exprEval e quotient_b_2_0_coef2_w1 + (e 3*e 8-1)*exprEval e quotient_b_2_0_coef2_w2 + (e 0*e 7-1)*exprEval e quotient_b_2_0_coef2_w3 := by
  dsimp only [quotient_b_2_0_coef2, quotient_b_2_0_coef2_w0, quotient_b_2_0_coef2_w1, quotient_b_2_0_coef2_w2, quotient_b_2_0_coef2_w3, exprEval] <;> grind

theorem quotient_b_2_0_coef2_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) quotient_b_2_0_coef2=0 :=
  unitIdealClearZero 2 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (quotient_b_2_0_coef2_cert (chartVars y beta))

def quotient_b_2_0_coef3 : RingExpr := (.mul (.int (-12)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def quotient_b_2_0_coef3_w0 : RingExpr := (.mul (.int (-3)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.int (-4)) (.pow (.var 10) 2)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.mul (.int 8) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 3))))))))))))))))))
def quotient_b_2_0_coef3_w1 : RingExpr := (.mul (.int (-3)) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))
def quotient_b_2_0_coef3_w2 : RingExpr := (.mul (.int (-3)) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 5)))))
def quotient_b_2_0_coef3_w3 : RingExpr := (.int 0)

theorem quotient_b_2_0_coef3_cert (e : Nat → R) :
    (2:R)^1*exprEval e quotient_b_2_0_coef3=(2*e 10-1)*exprEval e quotient_b_2_0_coef3_w0 + (e 4*e 9-1)*exprEval e quotient_b_2_0_coef3_w1 + (e 3*e 8-1)*exprEval e quotient_b_2_0_coef3_w2 + (e 0*e 7-1)*exprEval e quotient_b_2_0_coef3_w3 := by
  dsimp only [quotient_b_2_0_coef3, quotient_b_2_0_coef3_w0, quotient_b_2_0_coef3_w1, quotient_b_2_0_coef3_w2, quotient_b_2_0_coef3_w3, exprEval] <;> grind

theorem quotient_b_2_0_coef3_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) quotient_b_2_0_coef3=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (quotient_b_2_0_coef3_cert (chartVars y beta))

def quotient_b_2_0_coef4 : RingExpr := (.mul (.int 48) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def quotient_b_2_0_coef4_w0 : RingExpr := (.mul (.int 6) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.add (.mul (.int (-4)) (.pow (.var 10) 2)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.mul (.int 8) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 3))))))))))))))))))
def quotient_b_2_0_coef4_w1 : RingExpr := (.mul (.int 6) (.mul (.var 3) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))
def quotient_b_2_0_coef4_w2 : RingExpr := (.mul (.int 6) (.mul (.var 3) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.pow (.var 4) 2)))))
def quotient_b_2_0_coef4_w3 : RingExpr := (.int 0)

theorem quotient_b_2_0_coef4_cert (e : Nat → R) :
    (2:R)^0*exprEval e quotient_b_2_0_coef4=(2*e 10-1)*exprEval e quotient_b_2_0_coef4_w0 + (e 4*e 9-1)*exprEval e quotient_b_2_0_coef4_w1 + (e 3*e 8-1)*exprEval e quotient_b_2_0_coef4_w2 + (e 0*e 7-1)*exprEval e quotient_b_2_0_coef4_w3 := by
  dsimp only [quotient_b_2_0_coef4, quotient_b_2_0_coef4_w0, quotient_b_2_0_coef4_w1, quotient_b_2_0_coef4_w2, quotient_b_2_0_coef4_w3, exprEval] <;> grind

theorem quotient_b_2_0_coef4_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) quotient_b_2_0_coef4=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (quotient_b_2_0_coef4_cert (chartVars y beta))

def quotient_b_2_0_coef5 : RingExpr := (.mul (.int 8) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def quotient_b_2_0_coef5_w0 : RingExpr := (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.int (-4)) (.pow (.var 10) 2)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.mul (.int 8) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 3)))))))))))))))))
def quotient_b_2_0_coef5_w1 : RingExpr := (.mul (.var 3) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))
def quotient_b_2_0_coef5_w2 : RingExpr := (.mul (.var 3) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.pow (.var 8) 5))))
def quotient_b_2_0_coef5_w3 : RingExpr := (.int 0)

theorem quotient_b_2_0_coef5_cert (e : Nat → R) :
    (2:R)^0*exprEval e quotient_b_2_0_coef5=(2*e 10-1)*exprEval e quotient_b_2_0_coef5_w0 + (e 4*e 9-1)*exprEval e quotient_b_2_0_coef5_w1 + (e 3*e 8-1)*exprEval e quotient_b_2_0_coef5_w2 + (e 0*e 7-1)*exprEval e quotient_b_2_0_coef5_w3 := by
  dsimp only [quotient_b_2_0_coef5, quotient_b_2_0_coef5_w0, quotient_b_2_0_coef5_w1, quotient_b_2_0_coef5_w2, quotient_b_2_0_coef5_w3, exprEval] <;> grind

theorem quotient_b_2_0_coef5_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) quotient_b_2_0_coef5=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (quotient_b_2_0_coef5_cert (chartVars y beta))

def quotient_b_2_0_coef6 : RingExpr := (.mul (.int (-12)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 3) (.mul (.var 7) (.mul (.var 10) (.var 8)))) (.add (.mul (.int (-6)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))))))
def quotient_b_2_0_coef6_w0 : RingExpr := (.mul (.int (-3)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int 3) (.mul (.var 7) (.var 8))) (.add (.mul (.int 6) (.mul (.var 7) (.mul (.var 10) (.var 8)))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.var 4) (.pow (.var 10) 2)))) (.add (.mul (.int 12) (.mul (.var 7) (.mul (.var 8) (.pow (.var 10) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int (-3)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))))) (.add (.mul (.int (-24)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 3) (.pow (.var 8) 2))))))) (.add (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 8) (.mul (.var 4) (.mul (.pow (.var 10) 2) (.pow (.var 3) 2))))))) (.add (.mul (.int (-12)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))) (.add (.mul (.int (-6)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.add (.mul (.int 16) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.mul (.int 32) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))))))))))))))
def quotient_b_2_0_coef6_w1 : RingExpr := (.mul (.int (-3)) (.mul (.var 3) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.mul (.add (.int (-3)) (.mul (.int 4) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))
def quotient_b_2_0_coef6_w2 : RingExpr := (.mul (.int (-3)) (.mul (.var 3) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.add (.int (-3)) (.mul (.int 4) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))))
def quotient_b_2_0_coef6_w3 : RingExpr := (.int 0)

theorem quotient_b_2_0_coef6_cert (e : Nat → R) :
    (2:R)^1*exprEval e quotient_b_2_0_coef6=(2*e 10-1)*exprEval e quotient_b_2_0_coef6_w0 + (e 4*e 9-1)*exprEval e quotient_b_2_0_coef6_w1 + (e 3*e 8-1)*exprEval e quotient_b_2_0_coef6_w2 + (e 0*e 7-1)*exprEval e quotient_b_2_0_coef6_w3 := by
  dsimp only [quotient_b_2_0_coef6, quotient_b_2_0_coef6_w0, quotient_b_2_0_coef6_w1, quotient_b_2_0_coef6_w2, quotient_b_2_0_coef6_w3, exprEval] <;> grind

theorem quotient_b_2_0_coef6_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) quotient_b_2_0_coef6=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (quotient_b_2_0_coef6_cert (chartVars y beta))

def quotient_b_2_0_coef7 : RingExpr := (.mul (.int 8) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def quotient_b_2_0_coef7_w0 : RingExpr := (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.add (.mul (.int (-4)) (.pow (.var 10) 2)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.mul (.int 8) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 3)))))))))))))))))
def quotient_b_2_0_coef7_w1 : RingExpr := (.mul (.var 3) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))
def quotient_b_2_0_coef7_w2 : RingExpr := (.mul (.var 3) (.mul (.pow (.var 7) 2) (.pow (.var 8) 5)))
def quotient_b_2_0_coef7_w3 : RingExpr := (.int 0)

theorem quotient_b_2_0_coef7_cert (e : Nat → R) :
    (2:R)^0*exprEval e quotient_b_2_0_coef7=(2*e 10-1)*exprEval e quotient_b_2_0_coef7_w0 + (e 4*e 9-1)*exprEval e quotient_b_2_0_coef7_w1 + (e 3*e 8-1)*exprEval e quotient_b_2_0_coef7_w2 + (e 0*e 7-1)*exprEval e quotient_b_2_0_coef7_w3 := by
  dsimp only [quotient_b_2_0_coef7, quotient_b_2_0_coef7_w0, quotient_b_2_0_coef7_w1, quotient_b_2_0_coef7_w2, quotient_b_2_0_coef7_w3, exprEval] <;> grind

theorem quotient_b_2_0_coef7_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) quotient_b_2_0_coef7=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (quotient_b_2_0_coef7_cert (chartVars y beta))

def quotient_b_2_0_coef8 : RingExpr := (.mul (.int (-12)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.int 3) (.var 10)) (.add (.mul (.int (-6)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.var 4))))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.var 8)))))) (.add (.mul (.int 12) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))))))))))
def quotient_b_2_0_coef8_w0 : RingExpr := (.mul (.int (-3)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int 1) (.add (.mul (.int 2) (.var 10)) (.add (.mul (.int 12) (.pow (.var 10) 2)) (.add (.mul (.int (-6)) (.mul (.var 7) (.mul (.var 8) (.var 4)))) (.add (.mul (.int (-24)) (.mul (.var 7) (.mul (.var 8) (.mul (.var 4) (.pow (.var 10) 2))))) (.add (.mul (.int (-12)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.var 4))))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.var 8))))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.mul (.var 8) (.pow (.var 10) 2)))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.var 8)))))) (.add (.mul (.int 6) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))) (.add (.mul (.int 12) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 24) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 48) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))))))))))))))))))))
def quotient_b_2_0_coef8_w1 : RingExpr := (.mul (.int (-3)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.add (.int 1) (.add (.mul (.int (-6)) (.mul (.var 7) (.mul (.var 8) (.var 4)))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.var 8))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.add (.mul (.int 6) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2))))) (.add (.mul (.int 6) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))))))))
def quotient_b_2_0_coef8_w2 : RingExpr := (.mul (.int (-3)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 8) 2) (.add (.int 1) (.add (.mul (.var 3) (.var 8)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 7))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.var 8))))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))) (.mul (.int 6) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 3)))))))))))))))
def quotient_b_2_0_coef8_w3 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.var 4) (.pow (.var 8) 2))))

theorem quotient_b_2_0_coef8_cert (e : Nat → R) :
    (2:R)^1*exprEval e quotient_b_2_0_coef8=(2*e 10-1)*exprEval e quotient_b_2_0_coef8_w0 + (e 4*e 9-1)*exprEval e quotient_b_2_0_coef8_w1 + (e 3*e 8-1)*exprEval e quotient_b_2_0_coef8_w2 + (e 0*e 7-1)*exprEval e quotient_b_2_0_coef8_w3 := by
  dsimp only [quotient_b_2_0_coef8, quotient_b_2_0_coef8_w0, quotient_b_2_0_coef8_w1, quotient_b_2_0_coef8_w2, quotient_b_2_0_coef8_w3, exprEval] <;> grind

theorem quotient_b_2_0_coef8_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) quotient_b_2_0_coef8=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (quotient_b_2_0_coef8_cert (chartVars y beta))

def quotient_b_2_0_coef9 : RingExpr := (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.add (.int (-1)) (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def quotient_b_2_0_coef9_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.mul (.add (.int (-1)) (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.int (-1)) (.add (.mul (.int (-4)) (.pow (.var 10) 2)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.mul (.int 8) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 3))))))))))))))))))
def quotient_b_2_0_coef9_w1 : RingExpr := (.mul (.int (-1)) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.add (.mul (.int (-4)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 8) (.var 9))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))))))))))
def quotient_b_2_0_coef9_w2 : RingExpr := (.mul (.int (-1)) (.mul (.var 3) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.add (.mul (.int (-1)) (.var 9)) (.mul (.int 4) (.mul (.var 3) (.var 4))))))))
def quotient_b_2_0_coef9_w3 : RingExpr := (.int 0)

theorem quotient_b_2_0_coef9_cert (e : Nat → R) :
    (2:R)^2*exprEval e quotient_b_2_0_coef9=(2*e 10-1)*exprEval e quotient_b_2_0_coef9_w0 + (e 4*e 9-1)*exprEval e quotient_b_2_0_coef9_w1 + (e 3*e 8-1)*exprEval e quotient_b_2_0_coef9_w2 + (e 0*e 7-1)*exprEval e quotient_b_2_0_coef9_w3 := by
  dsimp only [quotient_b_2_0_coef9, quotient_b_2_0_coef9_w0, quotient_b_2_0_coef9_w1, quotient_b_2_0_coef9_w2, quotient_b_2_0_coef9_w3, exprEval] <;> grind

end StackSorting.FiniteGraph
