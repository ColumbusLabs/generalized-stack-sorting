import GraphInitial_Zt_Part01
import UnitSplitFactorCertificates
import GraphUnitWitness
import LiteralEntryNormalization
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem initial_Z_t_8_coef10_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef10=(2*e 10-1)*exprEval e initial_Z_t_8_coef10_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef10_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef10_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef10_w3 := by
  dsimp only [initial_Z_t_8_coef10, initial_Z_t_8_coef10_w0, initial_Z_t_8_coef10_w1, initial_Z_t_8_coef10_w2, initial_Z_t_8_coef10_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef10_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef10=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef10_cert (chartVars y beta))

def initial_Z_t_8_coef11 : RingExpr := (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8))))))))))
def initial_Z_t_8_coef11_w0 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef11_w1 : RingExpr := (.int 0)
def initial_Z_t_8_coef11_w2 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))))
def initial_Z_t_8_coef11_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef11_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef11=(2*e 10-1)*exprEval e initial_Z_t_8_coef11_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef11_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef11_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef11_w3 := by
  dsimp only [initial_Z_t_8_coef11, initial_Z_t_8_coef11_w0, initial_Z_t_8_coef11_w1, initial_Z_t_8_coef11_w2, initial_Z_t_8_coef11_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef11_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef11=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef11_cert (chartVars y beta))

def initial_Z_t_8_coef12 : RingExpr := (.mul (.int (-12)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.mul (.add (.int 1) (.var 10)) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))))))
def initial_Z_t_8_coef12_w0 : RingExpr := (.mul (.int (-3)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.mul (.add (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.int 3) (.mul (.int 2) (.var 10))))))))))
def initial_Z_t_8_coef12_w1 : RingExpr := (.mul (.int (-9)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8))))))))
def initial_Z_t_8_coef12_w2 : RingExpr := (.mul (.int (-9)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 3)))))
def initial_Z_t_8_coef12_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef12_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef12=(2*e 10-1)*exprEval e initial_Z_t_8_coef12_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef12_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef12_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef12_w3 := by
  dsimp only [initial_Z_t_8_coef12, initial_Z_t_8_coef12_w0, initial_Z_t_8_coef12_w1, initial_Z_t_8_coef12_w2, initial_Z_t_8_coef12_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef12_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef12=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef12_cert (chartVars y beta))

def initial_Z_t_8_coef13 : RingExpr := (.mul (.int (-12)) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def initial_Z_t_8_coef13_w0 : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int 1) (.add (.mul (.int (-2)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def initial_Z_t_8_coef13_w1 : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-2)) (.mul (.var 3) (.var 8))))))))
def initial_Z_t_8_coef13_w2 : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2)))))
def initial_Z_t_8_coef13_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef13_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef13=(2*e 10-1)*exprEval e initial_Z_t_8_coef13_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef13_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef13_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef13_w3 := by
  dsimp only [initial_Z_t_8_coef13, initial_Z_t_8_coef13_w0, initial_Z_t_8_coef13_w1, initial_Z_t_8_coef13_w2, initial_Z_t_8_coef13_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef13_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef13=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef13_cert (chartVars y beta))

def initial_Z_t_8_coef14 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.add (.int (-5)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 8))) (.add (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2))) (.add (.mul (.int 17) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3)))) (.add (.mul (.int 4) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 4) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 24) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3))))) (.add (.mul (.int (-24)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-20)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))
def initial_Z_t_8_coef14_w0 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.add (.int (-5)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 8))) (.add (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2))) (.add (.mul (.int 19) (.mul (.var 4) (.var 9))) (.add (.mul (.int 4) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 4) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3)))) (.add (.mul (.int (-16)) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-12)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 24) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3))))) (.add (.mul (.int (-24)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-20)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))
def initial_Z_t_8_coef14_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.add (.int (-19)) (.add (.mul (.int (-8)) (.mul (.var 3) (.pow (.var 4) 2))) (.add (.mul (.int 12) (.mul (.var 3) (.var 8))) (.add (.mul (.int 16) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3)))))))))))))
def initial_Z_t_8_coef14_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.add (.int 7) (.mul (.int 6) (.mul (.var 3) (.pow (.var 4) 2))))))))
def initial_Z_t_8_coef14_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef14_cert (e : Nat → R) :
    (2:R)^1*exprEval e initial_Z_t_8_coef14=(2*e 10-1)*exprEval e initial_Z_t_8_coef14_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef14_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef14_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef14_w3 := by
  dsimp only [initial_Z_t_8_coef14, initial_Z_t_8_coef14_w0, initial_Z_t_8_coef14_w1, initial_Z_t_8_coef14_w2, initial_Z_t_8_coef14_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef14_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef14=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef14_cert (chartVars y beta))

def initial_Z_t_8_coef15 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 4) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-10)) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2))) (.add (.mul (.var 3) (.mul (.var 8) (.var 4))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 8) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 3) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 12) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))))))))))))))))))))))
def initial_Z_t_8_coef15_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 4) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-14)) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2))) (.add (.mul (.var 3) (.mul (.var 8) (.var 4))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 8) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int 9) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 12) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))))))))))))))))))))
def initial_Z_t_8_coef15_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-14)) (.add (.mul (.int 9) (.mul (.var 3) (.var 8))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3)))))))))))))
def initial_Z_t_8_coef15_w2 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 10) (.var 4)) (.mul (.var 0) (.var 3)))))))
def initial_Z_t_8_coef15_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef15_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef15=(2*e 10-1)*exprEval e initial_Z_t_8_coef15_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef15_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef15_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef15_w3 := by
  dsimp only [initial_Z_t_8_coef15, initial_Z_t_8_coef15_w0, initial_Z_t_8_coef15_w1, initial_Z_t_8_coef15_w2, initial_Z_t_8_coef15_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef15_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef15=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef15_cert (chartVars y beta))

def initial_Z_t_8_coef16 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef16_w0 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))
def initial_Z_t_8_coef16_w1 : RingExpr := (.int 0)
def initial_Z_t_8_coef16_w2 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))
def initial_Z_t_8_coef16_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef16_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef16=(2*e 10-1)*exprEval e initial_Z_t_8_coef16_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef16_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef16_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef16_w3 := by
  dsimp only [initial_Z_t_8_coef16, initial_Z_t_8_coef16_w0, initial_Z_t_8_coef16_w1, initial_Z_t_8_coef16_w2, initial_Z_t_8_coef16_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef16_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef16=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef16_cert (chartVars y beta))

def initial_Z_t_8_coef17 : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 4)) (.add (.mul (.var 9) (.pow (.var 4) 2)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))) (.mul (.int 6) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))))))))))))))))
def initial_Z_t_8_coef17_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.mul (.int 6) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))))))))))))))))
def initial_Z_t_8_coef17_w1 : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef17_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.mul (.int 3) (.var 4)) (.mul (.var 0) (.var 3))))))))
def initial_Z_t_8_coef17_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef17_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef17=(2*e 10-1)*exprEval e initial_Z_t_8_coef17_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef17_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef17_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef17_w3 := by
  dsimp only [initial_Z_t_8_coef17, initial_Z_t_8_coef17_w0, initial_Z_t_8_coef17_w1, initial_Z_t_8_coef17_w2, initial_Z_t_8_coef17_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef17_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef17=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef17_cert (chartVars y beta))

def initial_Z_t_8_coef18 : RingExpr := (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8))))))))))
def initial_Z_t_8_coef18_w0 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef18_w1 : RingExpr := (.int 0)
def initial_Z_t_8_coef18_w2 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.pow (.var 8) 3))))))
def initial_Z_t_8_coef18_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef18_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef18=(2*e 10-1)*exprEval e initial_Z_t_8_coef18_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef18_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef18_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef18_w3 := by
  dsimp only [initial_Z_t_8_coef18, initial_Z_t_8_coef18_w0, initial_Z_t_8_coef18_w1, initial_Z_t_8_coef18_w2, initial_Z_t_8_coef18_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef18_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef18=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef18_cert (chartVars y beta))

def initial_Z_t_8_coef19 : RingExpr := (.mul (.int (-3)) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.add (.mul (.int (-1)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3))))) (.add (.mul (.int 2) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.mul (.int 8) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))))))))))))))
def initial_Z_t_8_coef19_w0 : RingExpr := (.mul (.int (-3)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3)))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3))))) (.add (.mul (.int 3) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 4) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.mul (.int 8) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))))))))))))))))
def initial_Z_t_8_coef19_w1 : RingExpr := (.mul (.int (-3)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-2)) (.add (.mul (.int (-4)) (.mul (.var 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 3) (.var 8))) (.mul (.int 4) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))
def initial_Z_t_8_coef19_w2 : RingExpr := (.mul (.int (-3)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int 3) (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2))))))))
def initial_Z_t_8_coef19_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef19_cert (e : Nat → R) :
    (2:R)^1*exprEval e initial_Z_t_8_coef19=(2*e 10-1)*exprEval e initial_Z_t_8_coef19_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef19_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef19_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef19_w3 := by
  dsimp only [initial_Z_t_8_coef19, initial_Z_t_8_coef19_w0, initial_Z_t_8_coef19_w1, initial_Z_t_8_coef19_w2, initial_Z_t_8_coef19_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef19_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef19=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef19_cert (chartVars y beta))

def initial_Z_t_8_coef20 : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.add (.mul (.int (-1)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))))
def initial_Z_t_8_coef20_w0 : RingExpr := (.mul (.int (-3)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 3) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def initial_Z_t_8_coef20_w1 : RingExpr := (.mul (.int (-3)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-2)) (.mul (.int 3) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef20_w2 : RingExpr := (.mul (.int (-9)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3)))))
def initial_Z_t_8_coef20_w3 : RingExpr := (.int 0)

end StackSorting.FiniteGraph
