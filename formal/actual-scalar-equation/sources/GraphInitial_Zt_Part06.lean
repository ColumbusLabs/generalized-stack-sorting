import GraphInitial_Zt_Part05
import UnitSplitFactorCertificates
import GraphUnitWitness
import LiteralEntryNormalization
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem initial_Z_t_8_coef50_cert (e : Nat → R) :
    (2:R)^1*exprEval e initial_Z_t_8_coef50=(2*e 10-1)*exprEval e initial_Z_t_8_coef50_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef50_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef50_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef50_w3 := by
  dsimp only [initial_Z_t_8_coef50, initial_Z_t_8_coef50_w0, initial_Z_t_8_coef50_w1, initial_Z_t_8_coef50_w2, initial_Z_t_8_coef50_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef50_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef50=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef50_cert (chartVars y beta))

def initial_Z_t_8_coef51 : RingExpr := (.mul (.int 6) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 4) (.var 9))) (.mul (.int 3) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def initial_Z_t_8_coef51_w0 : RingExpr := (.mul (.int 3) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 4) (.var 9))) (.mul (.int 3) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))
def initial_Z_t_8_coef51_w1 : RingExpr := (.mul (.int 3) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.add (.int (-2)) (.mul (.int 3) (.mul (.var 3) (.var 8))))))))))
def initial_Z_t_8_coef51_w2 : RingExpr := (.mul (.int 9) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.pow (.var 8) 3))))))
def initial_Z_t_8_coef51_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef51_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef51=(2*e 10-1)*exprEval e initial_Z_t_8_coef51_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef51_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef51_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef51_w3 := by
  dsimp only [initial_Z_t_8_coef51, initial_Z_t_8_coef51_w0, initial_Z_t_8_coef51_w1, initial_Z_t_8_coef51_w2, initial_Z_t_8_coef51_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef51_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef51=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef51_cert (chartVars y beta))

def initial_Z_t_8_coef52 : RingExpr := (.mul (.int 6) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.add (.mul (.int (-1)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))))))))))))
def initial_Z_t_8_coef52_w0 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.add (.mul (.int (-1)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))
def initial_Z_t_8_coef52_w1 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.add (.mul (.int 2) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3)))))))))))))
def initial_Z_t_8_coef52_w2 : RingExpr := (.mul (.int 6) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int 1) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))
def initial_Z_t_8_coef52_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef52_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef52=(2*e 10-1)*exprEval e initial_Z_t_8_coef52_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef52_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef52_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef52_w3 := by
  dsimp only [initial_Z_t_8_coef52, initial_Z_t_8_coef52_w0, initial_Z_t_8_coef52_w1, initial_Z_t_8_coef52_w2, initial_Z_t_8_coef52_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef52_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef52=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef52_cert (chartVars y beta))

def initial_Z_t_8_coef53 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 3) (.var 9))))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.pow (.var 8) 2)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.add (.mul (.int 3) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.mul (.int 10) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))))))))
def initial_Z_t_8_coef53_w0 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 9))) (.add (.mul (.int (-1)) (.mul (.var 3) (.pow (.var 8) 2))) (.add (.mul (.int (-4)) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))) (.add (.mul (.int 3) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2))))) (.add (.mul (.int 4) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int 14) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))))))))
def initial_Z_t_8_coef53_w1 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-4)) (.var 8)) (.add (.mul (.int 3) (.mul (.var 3) (.pow (.var 8) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 14) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))))))))
def initial_Z_t_8_coef53_w2 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.int (-2)) (.add (.mul (.int 2) (.mul (.var 3) (.var 8))) (.add (.mul (.var 0) (.mul (.var 3) (.var 9))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.pow (.var 3) 2)))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))))))))))
def initial_Z_t_8_coef53_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef53_cert (e : Nat → R) :
    (2:R)^1*exprEval e initial_Z_t_8_coef53=(2*e 10-1)*exprEval e initial_Z_t_8_coef53_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef53_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef53_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef53_w3 := by
  dsimp only [initial_Z_t_8_coef53, initial_Z_t_8_coef53_w0, initial_Z_t_8_coef53_w1, initial_Z_t_8_coef53_w2, initial_Z_t_8_coef53_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef53_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef53=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef53_cert (chartVars y beta))

def initial_Z_t_8_coef54 : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.add (.mul (.int 12) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))))))
def initial_Z_t_8_coef54_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.mul (.var 4) (.var 9)) (.add (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.add (.mul (.int 5) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-4)) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))))))
def initial_Z_t_8_coef54_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.mul (.add (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.int (-1)) (.add (.mul (.int (-6)) (.mul (.var 3) (.var 8))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3)))))))))))))
def initial_Z_t_8_coef54_w2 : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-5)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))))
def initial_Z_t_8_coef54_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef54_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef54=(2*e 10-1)*exprEval e initial_Z_t_8_coef54_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef54_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef54_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef54_w3 := by
  dsimp only [initial_Z_t_8_coef54, initial_Z_t_8_coef54_w0, initial_Z_t_8_coef54_w1, initial_Z_t_8_coef54_w2, initial_Z_t_8_coef54_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef54_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef54=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef54_cert (chartVars y beta))

def initial_Z_t_8_coef55 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))) (.add (.mul (.int (-4)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))
def initial_Z_t_8_coef55_w0 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.mul (.var 3) (.var 8)) (.add (.mul (.var 4) (.var 9)) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))))))))))))))
def initial_Z_t_8_coef55_w1 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.add (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))))
def initial_Z_t_8_coef55_w2 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.int 1) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))))))))
def initial_Z_t_8_coef55_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef55_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef55=(2*e 10-1)*exprEval e initial_Z_t_8_coef55_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef55_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef55_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef55_w3 := by
  dsimp only [initial_Z_t_8_coef55, initial_Z_t_8_coef55_w0, initial_Z_t_8_coef55_w1, initial_Z_t_8_coef55_w2, initial_Z_t_8_coef55_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef55_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef55=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef55_cert (chartVars y beta))

def initial_Z_t_8_coef56 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-3)) (.var 8)) (.add (.mul (.int 2) (.mul (.var 10) (.var 8))) (.add (.mul (.int 2) (.mul (.var 3) (.pow (.var 8) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))))))))))))))))
def initial_Z_t_8_coef56_w0 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.var 8)) (.add (.mul (.var 10) (.var 8)) (.add (.mul (.var 3) (.pow (.var 8) 2)) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))))))))))))))))
def initial_Z_t_8_coef56_w1 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.mul (.add (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.var 8) (.add (.mul (.var 0) (.mul (.var 3) (.var 4))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
def initial_Z_t_8_coef56_w2 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.var 8) (.add (.mul (.var 0) (.mul (.var 3) (.var 4))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
def initial_Z_t_8_coef56_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef56_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef56=(2*e 10-1)*exprEval e initial_Z_t_8_coef56_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef56_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef56_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef56_w3 := by
  dsimp only [initial_Z_t_8_coef56, initial_Z_t_8_coef56_w0, initial_Z_t_8_coef56_w1, initial_Z_t_8_coef56_w2, initial_Z_t_8_coef56_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef56_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef56=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef56_cert (chartVars y beta))

def initial_Z_t_8_coef57 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.mul (.add (.mul (.int (-2)) (.var 4)) (.mul (.var 0) (.var 3))) (.add (.int (-1)) (.add (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))
def initial_Z_t_8_coef57_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.mul (.add (.int 1) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-2)) (.var 4)) (.mul (.var 0) (.var 3))))))))
def initial_Z_t_8_coef57_w1 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-2)) (.var 4)) (.mul (.var 0) (.var 3)))))))
def initial_Z_t_8_coef57_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.mul (.add (.int 1) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-2)) (.var 4)) (.mul (.var 0) (.var 3))))))))
def initial_Z_t_8_coef57_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef57_cert (e : Nat → R) :
    (2:R)^1*exprEval e initial_Z_t_8_coef57=(2*e 10-1)*exprEval e initial_Z_t_8_coef57_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef57_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef57_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef57_w3 := by
  dsimp only [initial_Z_t_8_coef57, initial_Z_t_8_coef57_w0, initial_Z_t_8_coef57_w1, initial_Z_t_8_coef57_w2, initial_Z_t_8_coef57_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef57_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef57=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef57_cert (chartVars y beta))

def initial_Z_t_8_coef58 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.add (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))))
def initial_Z_t_8_coef58_w0 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 4) (.add (.int 1) (.mul (.var 4) (.var 9))))))))
def initial_Z_t_8_coef58_w1 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 5) (.pow (.var 8) 4)))))
def initial_Z_t_8_coef58_w2 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.add (.int 1) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef58_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef58_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef58=(2*e 10-1)*exprEval e initial_Z_t_8_coef58_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef58_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef58_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef58_w3 := by
  dsimp only [initial_Z_t_8_coef58, initial_Z_t_8_coef58_w0, initial_Z_t_8_coef58_w1, initial_Z_t_8_coef58_w2, initial_Z_t_8_coef58_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef58_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef58=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef58_cert (chartVars y beta))

def initial_Z_t_8_coef59 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.mul (.int 2) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))) (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))
def initial_Z_t_8_coef59_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.var 4)) (.add (.mul (.var 0) (.var 3)) (.mul (.int (-1)) (.mul (.var 9) (.pow (.var 4) 2)))))))))
def initial_Z_t_8_coef59_w1 : RingExpr := (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.pow (.var 8) 4))))
def initial_Z_t_8_coef59_w2 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.mul (.add (.int 1) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-2)) (.var 4)) (.mul (.var 0) (.var 3))))))))
def initial_Z_t_8_coef59_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef59_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef59=(2*e 10-1)*exprEval e initial_Z_t_8_coef59_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef59_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef59_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef59_w3 := by
  dsimp only [initial_Z_t_8_coef59, initial_Z_t_8_coef59_w0, initial_Z_t_8_coef59_w1, initial_Z_t_8_coef59_w2, initial_Z_t_8_coef59_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef59_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef59=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef59_cert (chartVars y beta))

def initial_Z_t_8_coef60 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))
def initial_Z_t_8_coef60_w0 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 5) (.pow (.var 8) 4))))
def initial_Z_t_8_coef60_w1 : RingExpr := (.int 0)
def initial_Z_t_8_coef60_w2 : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.add (.int 1) (.mul (.var 3) (.var 8)))))))
def initial_Z_t_8_coef60_w3 : RingExpr := (.int 0)

end StackSorting.FiniteGraph
