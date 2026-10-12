import GraphInitial_Zz_Part00
import UnitSplitFactorCertificates
import DirectionPolynomialIdentities
import GraphUnitWitness
import LiteralEntryNormalization
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

def initial_Z_z_8_coef1_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 3)))))
def initial_Z_z_8_coef1_w3 : RingExpr := (.int 0)

theorem initial_Z_z_8_coef1_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_z_8_coef1=(2*e 10-1)*exprEval e initial_Z_z_8_coef1_w0 + (e 4*e 9-1)*exprEval e initial_Z_z_8_coef1_w1 + (e 3*e 8-1)*exprEval e initial_Z_z_8_coef1_w2 + (e 0*e 7-1)*exprEval e initial_Z_z_8_coef1_w3 := by
  dsimp only [initial_Z_z_8_coef1, initial_Z_z_8_coef1_w0, initial_Z_z_8_coef1_w1, initial_Z_z_8_coef1_w2, initial_Z_z_8_coef1_w3, exprEval] <;> grind

theorem initial_Z_z_8_coef1_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_z_8_coef1=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_z_8_coef1_cert (chartVars y beta))

def initial_Z_z_8_coef2 : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def initial_Z_z_8_coef2_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 4) (.var 9))) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))
def initial_Z_z_8_coef2_w1 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2)))))
def initial_Z_z_8_coef2_w2 : RingExpr := (.int 0)
def initial_Z_z_8_coef2_w3 : RingExpr := (.int 0)

theorem initial_Z_z_8_coef2_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_z_8_coef2=(2*e 10-1)*exprEval e initial_Z_z_8_coef2_w0 + (e 4*e 9-1)*exprEval e initial_Z_z_8_coef2_w1 + (e 3*e 8-1)*exprEval e initial_Z_z_8_coef2_w2 + (e 0*e 7-1)*exprEval e initial_Z_z_8_coef2_w3 := by
  dsimp only [initial_Z_z_8_coef2, initial_Z_z_8_coef2_w0, initial_Z_z_8_coef2_w1, initial_Z_z_8_coef2_w2, initial_Z_z_8_coef2_w3, exprEval] <;> grind

theorem initial_Z_z_8_coef2_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_z_8_coef2=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_z_8_coef2_cert (chartVars y beta))

def initial_Z_z_8_coef3 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.int (-5)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 10) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def initial_Z_z_8_coef3_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.int (-5)) (.mul (.var 4) (.var 9))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 10) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))
def initial_Z_z_8_coef3_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-5)) (.mul (.int 4) (.mul (.var 3) (.var 8))))))))
def initial_Z_z_8_coef3_w2 : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.pow (.var 8) 3))))
def initial_Z_z_8_coef3_w3 : RingExpr := (.int 0)

theorem initial_Z_z_8_coef3_cert (e : Nat → R) :
    (2:R)^1*exprEval e initial_Z_z_8_coef3=(2*e 10-1)*exprEval e initial_Z_z_8_coef3_w0 + (e 4*e 9-1)*exprEval e initial_Z_z_8_coef3_w1 + (e 3*e 8-1)*exprEval e initial_Z_z_8_coef3_w2 + (e 0*e 7-1)*exprEval e initial_Z_z_8_coef3_w3 := by
  dsimp only [initial_Z_z_8_coef3, initial_Z_z_8_coef3_w0, initial_Z_z_8_coef3_w1, initial_Z_z_8_coef3_w2, initial_Z_z_8_coef3_w3, exprEval] <;> grind

theorem initial_Z_z_8_coef3_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_z_8_coef3=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_z_8_coef3_cert (chartVars y beta))

def initial_Z_z_8_coef4 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.int (-3)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 6) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def initial_Z_z_8_coef4_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.int (-3)) (.mul (.var 4) (.var 9))) (.add (.mul (.int 2) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 6) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def initial_Z_z_8_coef4_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-3)) (.mul (.int 2) (.mul (.var 3) (.var 8)))))))))
def initial_Z_z_8_coef4_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3)))))
def initial_Z_z_8_coef4_w3 : RingExpr := (.int 0)

theorem initial_Z_z_8_coef4_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_z_8_coef4=(2*e 10-1)*exprEval e initial_Z_z_8_coef4_w0 + (e 4*e 9-1)*exprEval e initial_Z_z_8_coef4_w1 + (e 3*e 8-1)*exprEval e initial_Z_z_8_coef4_w2 + (e 0*e 7-1)*exprEval e initial_Z_z_8_coef4_w3 := by
  dsimp only [initial_Z_z_8_coef4, initial_Z_z_8_coef4_w0, initial_Z_z_8_coef4_w1, initial_Z_z_8_coef4_w2, initial_Z_z_8_coef4_w3, exprEval] <;> grind

theorem initial_Z_z_8_coef4_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_z_8_coef4=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_z_8_coef4_cert (chartVars y beta))

def initial_Z_z_8_coef5 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.var 8)))))))))))
def initial_Z_z_8_coef5_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.var 8)))))))))))
def initial_Z_z_8_coef5_w1 : RingExpr := (.int 0)
def initial_Z_z_8_coef5_w2 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 3)))))
def initial_Z_z_8_coef5_w3 : RingExpr := (.int 0)

theorem initial_Z_z_8_coef5_cert (e : Nat → R) :
    (2:R)^1*exprEval e initial_Z_z_8_coef5=(2*e 10-1)*exprEval e initial_Z_z_8_coef5_w0 + (e 4*e 9-1)*exprEval e initial_Z_z_8_coef5_w1 + (e 3*e 8-1)*exprEval e initial_Z_z_8_coef5_w2 + (e 0*e 7-1)*exprEval e initial_Z_z_8_coef5_w3 := by
  dsimp only [initial_Z_z_8_coef5, initial_Z_z_8_coef5_w0, initial_Z_z_8_coef5_w1, initial_Z_z_8_coef5_w2, initial_Z_z_8_coef5_w3, exprEval] <;> grind

theorem initial_Z_z_8_coef5_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_z_8_coef5=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_z_8_coef5_cert (chartVars y beta))

def initial_Z_z_8_coef6 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.var 8))))))))))))
def initial_Z_z_8_coef6_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.var 8))))))))))))
def initial_Z_z_8_coef6_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))
def initial_Z_z_8_coef6_w2 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))
def initial_Z_z_8_coef6_w3 : RingExpr := (.int 0)

theorem initial_Z_z_8_coef6_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_z_8_coef6=(2*e 10-1)*exprEval e initial_Z_z_8_coef6_w0 + (e 4*e 9-1)*exprEval e initial_Z_z_8_coef6_w1 + (e 3*e 8-1)*exprEval e initial_Z_z_8_coef6_w2 + (e 0*e 7-1)*exprEval e initial_Z_z_8_coef6_w3 := by
  dsimp only [initial_Z_z_8_coef6, initial_Z_z_8_coef6_w0, initial_Z_z_8_coef6_w1, initial_Z_z_8_coef6_w2, initial_Z_z_8_coef6_w3, exprEval] <;> grind

theorem initial_Z_z_8_coef6_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_z_8_coef6=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_z_8_coef6_cert (chartVars y beta))

def initial_Z_z_8_coef7 : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int 3) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-3)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 6) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))))
def initial_Z_z_8_coef7_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int 3) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-3)) (.mul (.var 4) (.var 9))) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.mul (.int 6) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def initial_Z_z_8_coef7_w1 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-3)) (.mul (.var 3) (.var 8))))))))
def initial_Z_z_8_coef7_w2 : RingExpr := (.int 0)
def initial_Z_z_8_coef7_w3 : RingExpr := (.int 0)

theorem initial_Z_z_8_coef7_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_z_8_coef7=(2*e 10-1)*exprEval e initial_Z_z_8_coef7_w0 + (e 4*e 9-1)*exprEval e initial_Z_z_8_coef7_w1 + (e 3*e 8-1)*exprEval e initial_Z_z_8_coef7_w2 + (e 0*e 7-1)*exprEval e initial_Z_z_8_coef7_w3 := by
  dsimp only [initial_Z_z_8_coef7, initial_Z_z_8_coef7_w0, initial_Z_z_8_coef7_w1, initial_Z_z_8_coef7_w2, initial_Z_z_8_coef7_w3, exprEval] <;> grind

theorem initial_Z_z_8_coef7_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_z_8_coef7=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_z_8_coef7_cert (chartVars y beta))

def initial_Z_z_8_coef8 : RingExpr := (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.pow (.var 8) 3) (.add (.int (-3)) (.add (.mul (.var 3) (.var 8)) (.add (.mul (.int 5) (.mul (.var 4) (.var 9))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.add (.mul (.var 10) (.mul (.var 4) (.var 9))) (.add (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-11)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))
def initial_Z_z_8_coef8_w0 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.pow (.var 8) 3) (.add (.int (-6)) (.add (.mul (.int 2) (.mul (.var 3) (.var 8))) (.add (.mul (.int 11) (.mul (.var 4) (.var 9))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int (-7)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-22)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))
def initial_Z_z_8_coef8_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.pow (.var 8) 3) (.add (.int (-11)) (.add (.mul (.int 7) (.mul (.var 3) (.var 8))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3)))))))))))))
def initial_Z_z_8_coef8_w2 : RingExpr := (.mul (.int (-5)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 3)))))
def initial_Z_z_8_coef8_w3 : RingExpr := (.int 0)

theorem initial_Z_z_8_coef8_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_z_8_coef8=(2*e 10-1)*exprEval e initial_Z_z_8_coef8_w0 + (e 4*e 9-1)*exprEval e initial_Z_z_8_coef8_w1 + (e 3*e 8-1)*exprEval e initial_Z_z_8_coef8_w2 + (e 0*e 7-1)*exprEval e initial_Z_z_8_coef8_w3 := by
  dsimp only [initial_Z_z_8_coef8, initial_Z_z_8_coef8_w0, initial_Z_z_8_coef8_w1, initial_Z_z_8_coef8_w2, initial_Z_z_8_coef8_w3, exprEval] <;> grind

theorem initial_Z_z_8_coef8_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_z_8_coef8=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_z_8_coef8_cert (chartVars y beta))

def initial_Z_z_8_coef9 : RingExpr := (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-2)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int 2) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.var 3) (.mul (.var 8) (.var 4))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))) (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))))))))))))))))
def initial_Z_z_8_coef9_w0 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-2)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int 3) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.var 3) (.mul (.var 8) (.var 4))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))) (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))))))))))))))))
def initial_Z_z_8_coef9_w1 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 3) (.var 4)) (.add (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2))) (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 8) (.var 4)))))))))))
def initial_Z_z_8_coef9_w2 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 4)) (.mul (.var 0) (.var 3))))))))
def initial_Z_z_8_coef9_w3 : RingExpr := (.int 0)

theorem initial_Z_z_8_coef9_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_z_8_coef9=(2*e 10-1)*exprEval e initial_Z_z_8_coef9_w0 + (e 4*e 9-1)*exprEval e initial_Z_z_8_coef9_w1 + (e 3*e 8-1)*exprEval e initial_Z_z_8_coef9_w2 + (e 0*e 7-1)*exprEval e initial_Z_z_8_coef9_w3 := by
  dsimp only [initial_Z_z_8_coef9, initial_Z_z_8_coef9_w0, initial_Z_z_8_coef9_w1, initial_Z_z_8_coef9_w2, initial_Z_z_8_coef9_w3, exprEval] <;> grind

theorem initial_Z_z_8_coef9_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_z_8_coef9=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_z_8_coef9_cert (chartVars y beta))

def initial_Z_z_8_coef10 : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))
def initial_Z_z_8_coef10_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))
def initial_Z_z_8_coef10_w1 : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.pow (.var 8) 4))))))
def initial_Z_z_8_coef10_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))))
def initial_Z_z_8_coef10_w3 : RingExpr := (.int 0)

theorem initial_Z_z_8_coef10_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_z_8_coef10=(2*e 10-1)*exprEval e initial_Z_z_8_coef10_w0 + (e 4*e 9-1)*exprEval e initial_Z_z_8_coef10_w1 + (e 3*e 8-1)*exprEval e initial_Z_z_8_coef10_w2 + (e 0*e 7-1)*exprEval e initial_Z_z_8_coef10_w3 := by
  dsimp only [initial_Z_z_8_coef10, initial_Z_z_8_coef10_w0, initial_Z_z_8_coef10_w1, initial_Z_z_8_coef10_w2, initial_Z_z_8_coef10_w3, exprEval] <;> grind

theorem initial_Z_z_8_coef10_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_z_8_coef10=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_z_8_coef10_cert (chartVars y beta))

def initial_Z_z_8_coef11 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-3)) (.mul (.var 10) (.var 8))) (.add (.mul (.var 10) (.mul (.var 3) (.pow (.var 8) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-4)) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2))))) (.add (.mul (.int 11) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-26)) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))
def initial_Z_z_8_coef11_w0 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.add (.int (-3)) (.add (.mul (.var 3) (.var 8)) (.add (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2))) (.add (.mul (.int 13) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-4)) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int (-11)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 8) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3))))) (.add (.mul (.int (-26)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))))))))))))))))))))
def initial_Z_z_8_coef11_w1 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.add (.int 13) (.add (.mul (.int (-11)) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3)))))))))))
end StackSorting.FiniteGraph
