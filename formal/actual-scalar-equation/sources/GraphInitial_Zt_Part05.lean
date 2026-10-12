import GraphInitial_Zt_Part04
import UnitSplitFactorCertificates
import GraphUnitWitness
import LiteralEntryNormalization
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem initial_Z_t_8_coef40_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef40=(2*e 10-1)*exprEval e initial_Z_t_8_coef40_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef40_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef40_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef40_w3 := by
  dsimp only [initial_Z_t_8_coef40, initial_Z_t_8_coef40_w0, initial_Z_t_8_coef40_w1, initial_Z_t_8_coef40_w2, initial_Z_t_8_coef40_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef40_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef40=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef40_cert (chartVars y beta))

def initial_Z_t_8_coef41 : RingExpr := (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8))))))))))
def initial_Z_t_8_coef41_w0 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef41_w1 : RingExpr := (.int 0)
def initial_Z_t_8_coef41_w2 : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))))
def initial_Z_t_8_coef41_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef41_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef41=(2*e 10-1)*exprEval e initial_Z_t_8_coef41_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef41_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef41_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef41_w3 := by
  dsimp only [initial_Z_t_8_coef41, initial_Z_t_8_coef41_w0, initial_Z_t_8_coef41_w1, initial_Z_t_8_coef41_w2, initial_Z_t_8_coef41_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef41_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef41=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef41_cert (chartVars y beta))

def initial_Z_t_8_coef42 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.var 4) (.var 9)) (.add (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 8) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))))))))))))))))))
def initial_Z_t_8_coef42_w0 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.int 2) (.mul (.var 4) (.var 9))) (.add (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int (-4)) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-3)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))
def initial_Z_t_8_coef42_w1 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.add (.int 2) (.add (.mul (.int (-3)) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-4)) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3)))))))))))))
def initial_Z_t_8_coef42_w2 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.add (.int (-3)) (.add (.mul (.int (-4)) (.mul (.var 3) (.pow (.var 4) 2))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))))
def initial_Z_t_8_coef42_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef42_cert (e : Nat → R) :
    (2:R)^1*exprEval e initial_Z_t_8_coef42=(2*e 10-1)*exprEval e initial_Z_t_8_coef42_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef42_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef42_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef42_w3 := by
  dsimp only [initial_Z_t_8_coef42, initial_Z_t_8_coef42_w0, initial_Z_t_8_coef42_w1, initial_Z_t_8_coef42_w2, initial_Z_t_8_coef42_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef42_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef42=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef42_cert (chartVars y beta))

def initial_Z_t_8_coef43 : RingExpr := (.mul (.int 12) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.mul (.var 0) (.pow (.var 3) 2)) (.add (.mul (.var 10) (.var 9)) (.add (.mul (.int (-1)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 9))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 3)))))))))))))))
def initial_Z_t_8_coef43_w0 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.var 9) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 10) (.var 9))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.var 9)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 9))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 3)))))))))))))))))
def initial_Z_t_8_coef43_w1 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3)))))))))))))
def initial_Z_t_8_coef43_w2 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))))
def initial_Z_t_8_coef43_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef43_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef43=(2*e 10-1)*exprEval e initial_Z_t_8_coef43_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef43_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef43_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef43_w3 := by
  dsimp only [initial_Z_t_8_coef43, initial_Z_t_8_coef43_w0, initial_Z_t_8_coef43_w1, initial_Z_t_8_coef43_w2, initial_Z_t_8_coef43_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef43_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef43=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef43_cert (chartVars y beta))

def initial_Z_t_8_coef44 : RingExpr := (.mul (.int (-12)) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.var 4) (.var 9)) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def initial_Z_t_8_coef44_w0 : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def initial_Z_t_8_coef44_w1 : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2)))))
def initial_Z_t_8_coef44_w2 : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2)))))
def initial_Z_t_8_coef44_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef44_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef44=(2*e 10-1)*exprEval e initial_Z_t_8_coef44_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef44_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef44_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef44_w3 := by
  dsimp only [initial_Z_t_8_coef44, initial_Z_t_8_coef44_w0, initial_Z_t_8_coef44_w1, initial_Z_t_8_coef44_w2, initial_Z_t_8_coef44_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef44_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef44=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef44_cert (chartVars y beta))

def initial_Z_t_8_coef45 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-2)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 8) (.mul (.var 9) (.pow (.var 10) 2)))) (.add (.mul (.int (-3)) (.mul (.var 10) (.mul (.var 8) (.var 9)))) (.add (.mul (.var 0) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 4))))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2))))) (.add (.mul (.int 3) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.pow (.var 3) 2))))) (.add (.mul (.int (-20)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 8) 2)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 12) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 20) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.add (.mul (.int (-20)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int (-9)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 3) 2))))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))))))))))))))))))))))))))))))
def initial_Z_t_8_coef45_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-7)) (.mul (.var 8) (.var 9))) (.add (.mul (.int (-16)) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 8) (.var 9)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))) (.add (.mul (.int 7) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2)))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 8) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 6) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 20) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.int (-40)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.add (.mul (.int (-32)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-20)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))) (.add (.mul (.int 24) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 24) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))))))))))))))))))))))))))))
def initial_Z_t_8_coef45_w1 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int 2) (.var 0)) (.add (.mul (.int 10) (.mul (.var 8) (.var 4))) (.add (.mul (.int (-10)) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))) (.add (.mul (.int 2) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2)))) (.add (.mul (.int 3) (.mul (.var 0) (.mul (.var 3) (.var 8)))) (.add (.mul (.int (-16)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 8) 2))))) (.mul (.int 12) (.mul (.var 0) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))
def initial_Z_t_8_coef45_w2 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-8)) (.var 4)) (.add (.mul (.int (-7)) (.mul (.var 8) (.var 9))) (.add (.mul (.int 4) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.add (.mul (.int 18) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))) (.mul (.int 24) (.mul (.var 0) (.mul (.var 8) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))))))))
def initial_Z_t_8_coef45_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef45_cert (e : Nat → R) :
    (2:R)^2*exprEval e initial_Z_t_8_coef45=(2*e 10-1)*exprEval e initial_Z_t_8_coef45_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef45_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef45_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef45_w3 := by
  dsimp only [initial_Z_t_8_coef45, initial_Z_t_8_coef45_w0, initial_Z_t_8_coef45_w1, initial_Z_t_8_coef45_w2, initial_Z_t_8_coef45_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef45_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef45=0 :=
  unitIdealClearZero 2 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef45_cert (chartVars y beta))

def initial_Z_t_8_coef46 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.pow (.var 8) 2) (.add (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))) (.add (.mul (.int 3) (.mul (.var 10) (.mul (.var 8) (.var 9)))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))) (.add (.mul (.int (-3)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-2)) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 8) 2))))) (.add (.mul (.int (-22)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 11) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))) (.mul (.int 10) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))))))))))))))))))))
def initial_Z_t_8_coef46_w0 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.pow (.var 8) 2) (.add (.mul (.int 3) (.mul (.var 8) (.var 9))) (.add (.mul (.int (-3)) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))) (.add (.mul (.int 6) (.mul (.var 10) (.mul (.var 8) (.var 9)))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-4)) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 8) 2))))) (.add (.mul (.int (-34)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 28) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))) (.mul (.int 20) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))))))))))))))))))))
def initial_Z_t_8_coef46_w1 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int 3) (.var 8)) (.add (.mul (.int (-3)) (.mul (.var 3) (.pow (.var 8) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-34)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))) (.mul (.int 28) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))))))))))
def initial_Z_t_8_coef46_w2 : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-3)) (.var 8)) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.mul (.int 30) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))))))
def initial_Z_t_8_coef46_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef46_cert (e : Nat → R) :
    (2:R)^1*exprEval e initial_Z_t_8_coef46=(2*e 10-1)*exprEval e initial_Z_t_8_coef46_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef46_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef46_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef46_w3 := by
  dsimp only [initial_Z_t_8_coef46, initial_Z_t_8_coef46_w0, initial_Z_t_8_coef46_w1, initial_Z_t_8_coef46_w2, initial_Z_t_8_coef46_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef46_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef46=0 :=
  unitIdealClearZero 1 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef46_cert (chartVars y beta))

def initial_Z_t_8_coef47 : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.var 8)))))))))))))
def initial_Z_t_8_coef47_w0 : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.var 3) (.var 8)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.var 8)))))))))))))
def initial_Z_t_8_coef47_w1 : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))))
def initial_Z_t_8_coef47_w2 : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))))
def initial_Z_t_8_coef47_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef47_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef47=(2*e 10-1)*exprEval e initial_Z_t_8_coef47_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef47_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef47_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef47_w3 := by
  dsimp only [initial_Z_t_8_coef47, initial_Z_t_8_coef47_w0, initial_Z_t_8_coef47_w1, initial_Z_t_8_coef47_w2, initial_Z_t_8_coef47_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef47_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef47=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef47_cert (chartVars y beta))

def initial_Z_t_8_coef48 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 4) (.var 4)) (.add (.mul (.var 0) (.var 3)) (.add (.mul (.int (-10)) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.var 3) (.mul (.var 8) (.var 4))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 3)))) (.add (.mul (.int 10) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 8) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 4))))) (.add (.mul (.int 3) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 10) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))))))))))))))))))))))
def initial_Z_t_8_coef48_w0 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 4) (.var 4)) (.add (.mul (.var 0) (.var 3)) (.add (.mul (.int (-5)) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.var 3) (.mul (.var 8) (.var 4))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 3)))) (.add (.mul (.int 10) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 8) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 4))))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))))))))))))))))))))
def initial_Z_t_8_coef48_w1 : RingExpr := (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-5)) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3)))))))))))
def initial_Z_t_8_coef48_w2 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.var 4) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 3)))) (.mul (.int 6) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))
def initial_Z_t_8_coef48_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef48_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef48=(2*e 10-1)*exprEval e initial_Z_t_8_coef48_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef48_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef48_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef48_w3 := by
  dsimp only [initial_Z_t_8_coef48, initial_Z_t_8_coef48_w0, initial_Z_t_8_coef48_w1, initial_Z_t_8_coef48_w2, initial_Z_t_8_coef48_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef48_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef48=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef48_cert (chartVars y beta))

def initial_Z_t_8_coef49 : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.add (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
def initial_Z_t_8_coef49_w0 : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.add (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
def initial_Z_t_8_coef49_w1 : RingExpr := (.int 0)
def initial_Z_t_8_coef49_w2 : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))))
def initial_Z_t_8_coef49_w3 : RingExpr := (.int 0)

theorem initial_Z_t_8_coef49_cert (e : Nat → R) :
    (2:R)^0*exprEval e initial_Z_t_8_coef49=(2*e 10-1)*exprEval e initial_Z_t_8_coef49_w0 + (e 4*e 9-1)*exprEval e initial_Z_t_8_coef49_w1 + (e 3*e 8-1)*exprEval e initial_Z_t_8_coef49_w2 + (e 0*e 7-1)*exprEval e initial_Z_t_8_coef49_w3 := by
  dsimp only [initial_Z_t_8_coef49, initial_Z_t_8_coef49_w0, initial_Z_t_8_coef49_w1, initial_Z_t_8_coef49_w2, initial_Z_t_8_coef49_w3, exprEval] <;> grind

theorem initial_Z_t_8_coef49_zero (y : Chart R) (beta : Vec R 6) :
    exprEval (chartVars y beta) initial_Z_t_8_coef49=0 :=
  unitIdealClearZero 0 _ y.g y.gi y.q y.qi y.s y.si y.half _ _ _ _
    y.g_unit y.q_unit y.s_unit y.half_unit (initial_Z_t_8_coef49_cert (chartVars y beta))

def initial_Z_t_8_coef50 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-2)) (.var 4)) (.add (.mul (.var 0) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))))))))))))))
def initial_Z_t_8_coef50_w0 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-2)) (.var 4)) (.add (.mul (.var 0) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))))))))))))
def initial_Z_t_8_coef50_w1 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-2)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 8) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))
def initial_Z_t_8_coef50_w2 : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 4) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))
def initial_Z_t_8_coef50_w3 : RingExpr := (.int 0)

end StackSorting.FiniteGraph
