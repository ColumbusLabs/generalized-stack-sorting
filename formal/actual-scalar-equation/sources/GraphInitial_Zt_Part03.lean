import GraphInitial_Zt_Part02
import UnitSplitFactorCertificates
import GraphUnitWitness
import LiteralEntryNormalization
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem initial_Z_t_8_coef20_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef20=(2*e 10-1)*exprEval e initial_Z_t_8_coef20_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef20_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef20_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef20_w3 := by
  dsimp only [initial_Z_t_8_coef20, initial_Z_t_8_coef20_w0, initial_Z_t_8_coef20_w1, initial_Z_t_8_coef20_w2, initial_Z_t_8_coef20_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef20_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef20=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef20_cert (chartVars y beta))

def initial_Z_t_8_coef21 : RingExpr := (.mul (.int (-24)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8))))))))))
def initial_Z_t_8_coef21_w0 : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 3) (.mul (.add (.int 1) (.mul (.int 2) (.var 10))) (.add (.int (-1)) (.mul (.var 3) (.var 8))))))))))
def initial_Z_t_8_coef21_w1 : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.var 3) (.var 8))))))))
def initial_Z_t_8_coef21_w2 : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2)))))
def initial_Z_t_8_coef21_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef21_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef21=(2*e 10-1)*exprEval e initial_Z_t_8_coef21_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef21_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef21_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef21_w3 := by
  dsimp only [initial_Z_t_8_coef21, initial_Z_t_8_coef21_w0, initial_Z_t_8_coef21_w1, initial_Z_t_8_coef21_w2, initial_Z_t_8_coef21_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef21_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef21=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef21_cert (chartVars y beta))

def initial_Z_t_8_coef22 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-2)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 8) (.mul (.var 9) (.pow (.var 10) 2)))) (.add (.mul (.int (-3)) (.mul (.var 10) (.mul (.var 8) (.var 9)))) (.add (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.pow (.var 3) 2)))) (.add (.mul (.var 0) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))) (.add (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2)))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 4))))) (.add (.mul (.int 5) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))) (.add (.mul (.int (-12)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 3) 2))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))))))))))))))))))))))))
def initial_Z_t_8_coef22_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-7)) (.mul (.var 8) (.var 9))) (.add (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 8) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))) (.add (.mul (.int 7) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2)))) (.add (.mul (.int (-8)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 10) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2))))) (.add (.mul (.int 20) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-24)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))) (.add (.mul (.int 8) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))))))))))))))))))))))))
def initial_Z_t_8_coef22_w1 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-2)) (.var 0)) (.add (.mul (.int 4) (.mul (.var 8) (.var 4))) (.add (.mul (.var 0) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-10)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2)))) (.mul (.int 3) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))
def initial_Z_t_8_coef22_w2 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-8)) (.var 4)) (.add (.mul (.int (-7)) (.mul (.var 8) (.var 9))) (.add (.mul (.int 4) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-20)) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))))))))))
def initial_Z_t_8_coef22_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef22_cert (e : Nat → R) :
    (2:R)^2*exprEval e initial_Z_t_8_coef22=(2*e 10-1)*exprEval e initial_Z_t_8_coef22_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef22_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef22_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef22_w3 := by
  dsimp only [initial_Z_t_8_coef22, initial_Z_t_8_coef22_w0, initial_Z_t_8_coef22_w1, initial_Z_t_8_coef22_w2, initial_Z_t_8_coef22_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef22_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef22=0 :=
  unitIdealClearZero 2 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef22_cert (chartVars y beta))

def initial_Z_t_8_coef23 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.mul (.int 3) (.mul (.var 8) (.var 9))) (.add (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2))) (.add (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))) (.add (.mul (.var 10) (.mul (.var 8) (.var 9))) (.add (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2)))) (.add (.mul (.int (-3)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))))) (.mul (.int 14) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))))))))))))))))))))
def initial_Z_t_8_coef23_w0 : RingExpr := (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.mul (.int 7) (.mul (.var 8) (.var 9))) (.add (.mul (.int (-7)) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 8) (.var 9)))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))))) (.mul (.int 28) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))))))))))))))))))
def initial_Z_t_8_coef23_w1 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.mul (.int 7) (.var 8)) (.add (.mul (.int (-7)) (.mul (.var 3) (.pow (.var 8) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))))))))
def initial_Z_t_8_coef23_w2 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-7)) (.var 8)) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))))))
def initial_Z_t_8_coef23_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef23_cert (e : Nat → R) :
    (2:R)^1*exprEval e initial_Z_t_8_coef23=(2*e 10-1)*exprEval e initial_Z_t_8_coef23_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef23_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef23_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef23_w3 := by
  dsimp only [initial_Z_t_8_coef23, initial_Z_t_8_coef23_w0, initial_Z_t_8_coef23_w1, initial_Z_t_8_coef23_w2, initial_Z_t_8_coef23_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef23_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef23=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef23_cert (chartVars y beta))

def initial_Z_t_8_coef24 : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.var 8)))))))))))))
def initial_Z_t_8_coef24_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.var 8)))))))))))))
def initial_Z_t_8_coef24_w1 : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef24_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.pow (.var 8) 3))))))
def initial_Z_t_8_coef24_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef24_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef24=(2*e 10-1)*exprEval e initial_Z_t_8_coef24_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef24_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef24_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef24_w3 := by
  dsimp only [initial_Z_t_8_coef24, initial_Z_t_8_coef24_w0, initial_Z_t_8_coef24_w1, initial_Z_t_8_coef24_w2, initial_Z_t_8_coef24_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef24_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef24=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef24_cert (chartVars y beta))

def initial_Z_t_8_coef25 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 4)) (.add (.mul (.var 9) (.pow (.var 4) 2)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int 3) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))))))))))))))))))))
def initial_Z_t_8_coef25_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))))))))))))))))
def initial_Z_t_8_coef25_w1 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef25_w2 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.mul (.int 3) (.var 4)) (.mul (.var 0) (.var 3)))))))
def initial_Z_t_8_coef25_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef25_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef25=(2*e 10-1)*exprEval e initial_Z_t_8_coef25_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef25_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef25_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef25_w3 := by
  dsimp only [initial_Z_t_8_coef25, initial_Z_t_8_coef25_w0, initial_Z_t_8_coef25_w1, initial_Z_t_8_coef25_w2, initial_Z_t_8_coef25_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef25_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef25=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef25_cert (chartVars y beta))

def initial_Z_t_8_coef26 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef26_w0 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))
def initial_Z_t_8_coef26_w1 : RingExpr := (.int 0)
def initial_Z_t_8_coef26_w2 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 4) (.pow (.var 8) 3))))
def initial_Z_t_8_coef26_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef26_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef26=(2*e 10-1)*exprEval e initial_Z_t_8_coef26_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef26_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef26_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef26_w3 := by
  dsimp only [initial_Z_t_8_coef26, initial_Z_t_8_coef26_w0, initial_Z_t_8_coef26_w1, initial_Z_t_8_coef26_w2, initial_Z_t_8_coef26_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef26_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef26=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef26_cert (chartVars y beta))

def initial_Z_t_8_coef27 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 3) (.var 9))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-3)) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))))
def initial_Z_t_8_coef27_w0 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 9))) (.add (.mul (.int (-1)) (.mul (.var 3) (.pow (.var 8) 2))) (.add (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))))
def initial_Z_t_8_coef27_w1 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.pow (.var 8) 2)) (.add (.mul (.int (-4)) (.mul (.var 0) (.var 4))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))
def initial_Z_t_8_coef27_w2 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.mul (.add (.int 1) (.mul (.var 3) (.var 8))) (.add (.int (-2)) (.add (.mul (.var 0) (.mul (.var 3) (.var 9))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))))
def initial_Z_t_8_coef27_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef27_cert (e : Nat → R) :
    (2:R)^1*exprEval e initial_Z_t_8_coef27=(2*e 10-1)*exprEval e initial_Z_t_8_coef27_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef27_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef27_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef27_w3 := by
  dsimp only [initial_Z_t_8_coef27, initial_Z_t_8_coef27_w0, initial_Z_t_8_coef27_w1, initial_Z_t_8_coef27_w2, initial_Z_t_8_coef27_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef27_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef27=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef27_cert (chartVars y beta))

def initial_Z_t_8_coef28 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 3) (.var 9))))) (.add (.mul (.int (-1)) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))))))))))))
def initial_Z_t_8_coef28_w0 : RingExpr := (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 9))) (.add (.mul (.int (-1)) (.mul (.var 3) (.pow (.var 8) 2))) (.add (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))))
def initial_Z_t_8_coef28_w1 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.var 0)) (.add (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))) (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2)))))))))
def initial_Z_t_8_coef28_w2 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.mul (.add (.int 1) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-2)) (.var 4)) (.mul (.var 0) (.var 3)))))))
def initial_Z_t_8_coef28_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef28_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef28=(2*e 10-1)*exprEval e initial_Z_t_8_coef28_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef28_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef28_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef28_w3 := by
  dsimp only [initial_Z_t_8_coef28, initial_Z_t_8_coef28_w0, initial_Z_t_8_coef28_w1, initial_Z_t_8_coef28_w2, initial_Z_t_8_coef28_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef28_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef28=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef28_cert (chartVars y beta))

def initial_Z_t_8_coef29 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.pow (.var 8) 2)) (.add (.mul (.int (-2)) (.mul (.var 0) (.var 4))) (.add (.mul (.int 2) (.mul (.var 10) (.pow (.var 8) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))))))))
def initial_Z_t_8_coef29_w0 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.add (.mul (.var 10) (.pow (.var 8) 2)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))))))
def initial_Z_t_8_coef29_w1 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.mul (.add (.int 1) (.mul (.var 3) (.var 8))) (.add (.int (-1)) (.mul (.var 3) (.var 8))))))))))
def initial_Z_t_8_coef29_w2 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.add (.int 1) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef29_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef29_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef29=(2*e 10-1)*exprEval e initial_Z_t_8_coef29_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef29_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef29_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef29_w3 := by
  dsimp only [initial_Z_t_8_coef29, initial_Z_t_8_coef29_w0, initial_Z_t_8_coef29_w1, initial_Z_t_8_coef29_w2, initial_Z_t_8_coef29_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef29_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef29=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef29_cert (chartVars y beta))

def initial_Z_t_8_coef30 : RingExpr := (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.mul (.add (.int (-1)) (.mul (.var 4) (.var 9))) (.add (.int 4) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef30_w0 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.mul (.add (.int (-1)) (.mul (.var 4) (.var 9))) (.add (.int 4) (.mul (.var 3) (.var 8))))))))
def initial_Z_t_8_coef30_w1 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int 4) (.mul (.var 3) (.var 8)))))))
def initial_Z_t_8_coef30_w2 : RingExpr := (.int 0)
def initial_Z_t_8_coef30_w3 : RingExpr := (.int 0)

end StackSorting.FiniteGraph
