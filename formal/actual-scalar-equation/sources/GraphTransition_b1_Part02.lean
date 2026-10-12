import GraphTransition_b1_Part01
import UnitSplitFactorCertificates
import GraphUnitWitness
import LiteralEntryNormalization
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem trans_b_1_8_coef13_cert (e : Nat → R) :
    (2:R)^1*exprEval e trans_b_1_8_coef13=(2*e 10-1)*exprEval e trans_b_1_8_coef13_w0 + (e 4*e 9-1)*exprEval e trans_b_1_8_coef13_w1 + (e 3*e 8-1)*exprEval e trans_b_1_8_coef13_w2 + (e 0*e 7-1)*exprEval e trans_b_1_8_coef13_w3 := by
  dsimp only [trans_b_1_8_coef13, trans_b_1_8_coef13_w0, trans_b_1_8_coef13_w1, trans_b_1_8_coef13_w2, trans_b_1_8_coef13_w3, exprEval] <;> grind

theorem trans_b_1_8_coef13_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_b_1_8_coef13=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_b_1_8_coef13_cert (chartVars y beta))

def trans_b_1_8_coef14 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-2)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 10) (.pow (.var 8) 2)))) (.add (.mul (.int 2) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 4))))))) (.mul (.int 10) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))))))))))
def trans_b_1_8_coef14_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-4)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 7) (.pow (.var 8) 2))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.pow (.var 8) 2)))) (.add (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.mul (.var 8) (.var 4)))))) (.add (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 10) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-16)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 4))))))) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.mul (.int 20) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))))))))))))))))))
def trans_b_1_8_coef14_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-4)) (.add (.mul (.var 7) (.mul (.var 9) (.pow (.var 8) 2))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.var 8))))) (.add (.mul (.int 10) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))))))))))
def trans_b_1_8_coef14_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 8) (.mul (.var 4) (.add (.int (-2)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 8))) (.add (.mul (.int 2) (.mul (.var 0) (.var 7))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.var 8))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.mul (.int 5) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))))))))))))
def trans_b_1_8_coef14_w3 : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 8) (.var 4))))

theorem trans_b_1_8_coef14_cert (e : Nat → R) :
    (2:R)^1*exprEval e trans_b_1_8_coef14=(2*e 10-1)*exprEval e trans_b_1_8_coef14_w0 + (e 4*e 9-1)*exprEval e trans_b_1_8_coef14_w1 + (e 3*e 8-1)*exprEval e trans_b_1_8_coef14_w2 + (e 0*e 7-1)*exprEval e trans_b_1_8_coef14_w3 := by
  dsimp only [trans_b_1_8_coef14, trans_b_1_8_coef14_w0, trans_b_1_8_coef14_w1, trans_b_1_8_coef14_w2, trans_b_1_8_coef14_w3, exprEval] <;> grind

theorem trans_b_1_8_coef14_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_b_1_8_coef14=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_b_1_8_coef14_cert (chartVars y beta))

def trans_b_1_8_coef15 : RingExpr := (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))))))))))))
def trans_b_1_8_coef15_w0 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 4) (.var 9)) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.mul (.int 4) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))))))))))))
def trans_b_1_8_coef15_w1 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.pow (.var 4) 2)))))))
def trans_b_1_8_coef15_w2 : RingExpr := (.int 0)
def trans_b_1_8_coef15_w3 : RingExpr := (.int 0)

theorem trans_b_1_8_coef15_cert (e : Nat → R) :
    (2:R)^0*exprEval e trans_b_1_8_coef15=(2*e 10-1)*exprEval e trans_b_1_8_coef15_w0 + (e 4*e 9-1)*exprEval e trans_b_1_8_coef15_w1 + (e 3*e 8-1)*exprEval e trans_b_1_8_coef15_w2 + (e 0*e 7-1)*exprEval e trans_b_1_8_coef15_w3 := by
  dsimp only [trans_b_1_8_coef15, trans_b_1_8_coef15_w0, trans_b_1_8_coef15_w1, trans_b_1_8_coef15_w2, trans_b_1_8_coef15_w3, exprEval] <;> grind

theorem trans_b_1_8_coef15_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_b_1_8_coef15=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_b_1_8_coef15_cert (chartVars y beta))

def trans_b_1_8_coef16 : RingExpr := (.mul (.int (-4)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.int 2) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))) (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))))
def trans_b_1_8_coef16_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.int 2) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 10) (.mul (.var 3) (.var 8)))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))))))))))))))))))))
def trans_b_1_8_coef16_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))))))))))))
def trans_b_1_8_coef16_w2 : RingExpr := (.mul (.int (-1)) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.add (.int 1) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))))
def trans_b_1_8_coef16_w3 : RingExpr := (.int 0)

theorem trans_b_1_8_coef16_cert (e : Nat → R) :
    (2:R)^0*exprEval e trans_b_1_8_coef16=(2*e 10-1)*exprEval e trans_b_1_8_coef16_w0 + (e 4*e 9-1)*exprEval e trans_b_1_8_coef16_w1 + (e 3*e 8-1)*exprEval e trans_b_1_8_coef16_w2 + (e 0*e 7-1)*exprEval e trans_b_1_8_coef16_w3 := by
  dsimp only [trans_b_1_8_coef16, trans_b_1_8_coef16_w0, trans_b_1_8_coef16_w1, trans_b_1_8_coef16_w2, trans_b_1_8_coef16_w3, exprEval] <;> grind

theorem trans_b_1_8_coef16_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_b_1_8_coef16=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_b_1_8_coef16_cert (chartVars y beta))

def trans_b_1_8_coef17 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.pow (.var 4) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 16) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))))))))))))))))
def trans_b_1_8_coef17_w0 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.add (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 8) (.pow (.var 4) 3))))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2))))) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.pow (.var 4) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4))))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 16) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))))))))))))))))))))))))
def trans_b_1_8_coef17_w1 : RingExpr := (.mul (.int 2) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-2)) (.var 4)) (.add (.mul (.var 8) (.var 9)) (.add (.mul (.int 2) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))))))))))))
def trans_b_1_8_coef17_w2 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.var 9) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.var 9)))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.mul (.var 8) (.var 9)))))) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))
def trans_b_1_8_coef17_w3 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 9) (.pow (.var 8) 2))))

theorem trans_b_1_8_coef17_cert (e : Nat → R) :
    (2:R)^1*exprEval e trans_b_1_8_coef17=(2*e 10-1)*exprEval e trans_b_1_8_coef17_w0 + (e 4*e 9-1)*exprEval e trans_b_1_8_coef17_w1 + (e 3*e 8-1)*exprEval e trans_b_1_8_coef17_w2 + (e 0*e 7-1)*exprEval e trans_b_1_8_coef17_w3 := by
  dsimp only [trans_b_1_8_coef17, trans_b_1_8_coef17_w0, trans_b_1_8_coef17_w1, trans_b_1_8_coef17_w2, trans_b_1_8_coef17_w3, exprEval] <;> grind

theorem trans_b_1_8_coef17_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_b_1_8_coef17=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_b_1_8_coef17_cert (chartVars y beta))

def trans_b_1_8_coef18 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))))))))))))))))
def trans_b_1_8_coef18_w0 : RingExpr := (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.add (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2))))) (.add (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))))))))))))))))))))
def trans_b_1_8_coef18_w1 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.add (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))))))))))
def trans_b_1_8_coef18_w2 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.int 1) (.add (.mul (.var 3) (.var 8)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 7))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.var 8))))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2))))))))))))))
def trans_b_1_8_coef18_w3 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.var 8)))

theorem trans_b_1_8_coef18_cert (e : Nat → R) :
    (2:R)^0*exprEval e trans_b_1_8_coef18=(2*e 10-1)*exprEval e trans_b_1_8_coef18_w0 + (e 4*e 9-1)*exprEval e trans_b_1_8_coef18_w1 + (e 3*e 8-1)*exprEval e trans_b_1_8_coef18_w2 + (e 0*e 7-1)*exprEval e trans_b_1_8_coef18_w3 := by
  dsimp only [trans_b_1_8_coef18, trans_b_1_8_coef18_w0, trans_b_1_8_coef18_w1, trans_b_1_8_coef18_w2, trans_b_1_8_coef18_w3, exprEval] <;> grind

theorem trans_b_1_8_coef18_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_b_1_8_coef18=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_b_1_8_coef18_cert (chartVars y beta))

def trans_b_1_8_coef19 : RingExpr := (.mul (.int 4) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))))))))))))
def trans_b_1_8_coef19_w0 : RingExpr := (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 4) (.var 9)) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.mul (.int 4) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2))))))))))))))
def trans_b_1_8_coef19_w1 : RingExpr := (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 4) (.pow (.var 8) 5))))))
def trans_b_1_8_coef19_w2 : RingExpr := (.int 0)
def trans_b_1_8_coef19_w3 : RingExpr := (.int 0)

theorem trans_b_1_8_coef19_cert (e : Nat → R) :
    (2:R)^0*exprEval e trans_b_1_8_coef19=(2*e 10-1)*exprEval e trans_b_1_8_coef19_w0 + (e 4*e 9-1)*exprEval e trans_b_1_8_coef19_w1 + (e 3*e 8-1)*exprEval e trans_b_1_8_coef19_w2 + (e 0*e 7-1)*exprEval e trans_b_1_8_coef19_w3 := by
  dsimp only [trans_b_1_8_coef19, trans_b_1_8_coef19_w0, trans_b_1_8_coef19_w1, trans_b_1_8_coef19_w2, trans_b_1_8_coef19_w3, exprEval] <;> grind

theorem trans_b_1_8_coef19_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_b_1_8_coef19=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_b_1_8_coef19_cert (chartVars y beta))

def trans_b_1_8_coef20 : RingExpr := (.mul (.int (-2)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.add (.var 8) (.add (.mul (.int 4) (.pow (.var 4) 2)) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 3)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))))
def trans_b_1_8_coef20_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.add (.var 8) (.add (.mul (.int 4) (.pow (.var 4) 2)) (.add (.mul (.int 2) (.mul (.var 10) (.var 8))) (.add (.mul (.int 8) (.mul (.var 10) (.pow (.var 4) 2))) (.add (.mul (.int (-1)) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 3))))) (.add (.mul (.int (-4)) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2))))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-16)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 3)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))))
def trans_b_1_8_coef20_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.add (.mul (.int 4) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 8) (.var 9))) (.add (.mul (.int (-4)) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))))))))))))))
def trans_b_1_8_coef20_w2 : RingExpr := (.mul (.int (-4)) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.var 4)) (.mul (.var 0) (.var 3))))))))
def trans_b_1_8_coef20_w3 : RingExpr := (.int 0)

theorem trans_b_1_8_coef20_cert (e : Nat → R) :
    (2:R)^1*exprEval e trans_b_1_8_coef20=(2*e 10-1)*exprEval e trans_b_1_8_coef20_w0 + (e 4*e 9-1)*exprEval e trans_b_1_8_coef20_w1 + (e 3*e 8-1)*exprEval e trans_b_1_8_coef20_w2 + (e 0*e 7-1)*exprEval e trans_b_1_8_coef20_w3 := by
  dsimp only [trans_b_1_8_coef20, trans_b_1_8_coef20_w0, trans_b_1_8_coef20_w1, trans_b_1_8_coef20_w2, trans_b_1_8_coef20_w3, exprEval] <;> grind

theorem trans_b_1_8_coef20_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_b_1_8_coef20=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_b_1_8_coef20_cert (chartVars y beta))

def trans_b_1_8_coef21 : RingExpr := (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def trans_b_1_8_coef21_w0 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))))))))))))))
def trans_b_1_8_coef21_w1 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 4) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))
def trans_b_1_8_coef21_w2 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 3) 4) (.pow (.var 8) 4))))))
def trans_b_1_8_coef21_w3 : RingExpr := (.int 0)

theorem trans_b_1_8_coef21_cert (e : Nat → R) :
    (2:R)^0*exprEval e trans_b_1_8_coef21=(2*e 10-1)*exprEval e trans_b_1_8_coef21_w0 + (e 4*e 9-1)*exprEval e trans_b_1_8_coef21_w1 + (e 3*e 8-1)*exprEval e trans_b_1_8_coef21_w2 + (e 0*e 7-1)*exprEval e trans_b_1_8_coef21_w3 := by
  dsimp only [trans_b_1_8_coef21, trans_b_1_8_coef21_w0, trans_b_1_8_coef21_w1, trans_b_1_8_coef21_w2, trans_b_1_8_coef21_w3, exprEval] <;> grind

theorem trans_b_1_8_coef21_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_b_1_8_coef21=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_b_1_8_coef21_cert (chartVars y beta))

def trans_b_1_8_coef22 : RingExpr := (.mul (.int (-8)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))))))))))
def trans_b_1_8_coef22_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.add (.mul (.int (-2)) (.var 10)) (.add (.mul (.var 4) (.var 9)) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.mul (.int 4) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))))))))))
def trans_b_1_8_coef22_w1 : RingExpr := (.mul (.int (-2)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 5) (.pow (.var 4) 3)))))
def trans_b_1_8_coef22_w2 : RingExpr := (.int 0)
def trans_b_1_8_coef22_w3 : RingExpr := (.int 0)

theorem trans_b_1_8_coef22_cert (e : Nat → R) :
    (2:R)^0*exprEval e trans_b_1_8_coef22=(2*e 10-1)*exprEval e trans_b_1_8_coef22_w0 + (e 4*e 9-1)*exprEval e trans_b_1_8_coef22_w1 + (e 3*e 8-1)*exprEval e trans_b_1_8_coef22_w2 + (e 0*e 7-1)*exprEval e trans_b_1_8_coef22_w3 := by
  dsimp only [trans_b_1_8_coef22, trans_b_1_8_coef22_w0, trans_b_1_8_coef22_w1, trans_b_1_8_coef22_w2, trans_b_1_8_coef22_w3, exprEval] <;> grind

theorem trans_b_1_8_coef22_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) trans_b_1_8_coef22=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (trans_b_1_8_coef22_cert (chartVars y beta))

def trans_b_1_8_coef23 : RingExpr := (.mul (.int 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int 3) (.var 8)) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))
def trans_b_1_8_coef23_w0 : RingExpr := (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int 3) (.var 8)) (.add (.mul (.int 6) (.mul (.var 10) (.var 8))) (.add (.mul (.int (-3)) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-12)) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2))))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))))))
def trans_b_1_8_coef23_w1 : RingExpr := (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int (-3)) (.mul (.var 8) (.var 9))) (.add (.mul (.int 2) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))))))))))
def trans_b_1_8_coef23_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2))))))
def trans_b_1_8_coef23_w3 : RingExpr := (.int 0)

end StackSorting.FiniteGraph
