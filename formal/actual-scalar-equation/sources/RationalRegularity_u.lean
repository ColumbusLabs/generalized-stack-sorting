import FPSDivision
import ScalarJetSemantics
import RationalMapLiterals
namespace StackSorting.RationalLift
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics StackSorting.ConcreteScalar StackSorting.ScalarJet
open StackSorting.FPSDivision
set_option maxRecDepth 12000
set_option maxHeartbeats 30000000
def uNExpr : Expr := (.add (.add (.scalar (-2353392 : Rat)) (.mul (.x) (.add (.scalar (-15067542 : Rat)) (.mul (.x) (.add (.scalar (110200308 : Rat)) (.mul (.x) (.add (.scalar (-13450326 : Rat)) (.mul (.x) (.scalar (-52857648 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (8955200 : Rat)) (.mul (.x) (.add (.scalar (45090875 : Rat)) (.mul (.x) (.add (.scalar (-428781429 : Rat)) (.mul (.x) (.add (.scalar (124214965 : Rat)) (.mul (.x) (.add (.scalar (81932205 : Rat)) (.mul (.x) (.scalar (-14682680 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-12632580 : Rat)) (.mul (.x) (.add (.scalar (-43955705 : Rat)) (.mul (.x) (.add (.scalar (613384190 : Rat)) (.mul (.x) (.add (.scalar (-118328303 : Rat)) (.mul (.x) (.add (.scalar (14400648 : Rat)) (.mul (.x) (.scalar (-25943080 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (7533714 : Rat)) (.mul (.x) (.add (.scalar (7834996 : Rat)) (.mul (.x) (.add (.scalar (-385089686 : Rat)) (.mul (.x) (.add (.scalar (-201090179 : Rat)) (.mul (.x) (.add (.scalar (-9267693 : Rat)) (.mul (.x) (.scalar (32794536 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-1039982 : Rat)) (.mul (.x) (.add (.scalar (12842468 : Rat)) (.mul (.x) (.add (.scalar (88631730 : Rat)) (.mul (.x) (.add (.scalar (351530481 : Rat)) (.mul (.x) (.add (.scalar (-22108722 : Rat)) (.mul (.x) (.scalar (11649564 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-646506 : Rat)) (.mul (.x) (.add (.scalar (-8477943 : Rat)) (.mul (.x) (.add (.scalar (2455167 : Rat)) (.mul (.x) (.add (.scalar (-165359808 : Rat)) (.mul (.x) (.add (.scalar (-40716774 : Rat)) (.mul (.x) (.scalar (-11807352 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (183546 : Rat)) (.mul (.x) (.add (.scalar (1832967 : Rat)) (.mul (.x) (.add (.scalar (140238 : Rat)) (.mul (.x) (.add (.scalar (18827064 : Rat)) (.mul (.x) (.add (.scalar (44370288 : Rat)) (.mul (.x) (.scalar (1086264 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (-100116 : Rat)) (.mul (.x) (.add (.scalar (-918918 : Rat)) (.mul (.x) (.add (.scalar (1939680 : Rat)) (.mul (.x) (.scalar (-9470520 : Rat))))))))))))))))))))))))

theorem uNEval (x y : FPS) : ringEval uNExpr x (fun _ => y) = uN x y := by
  simp only [uNExpr, uN, ringEval, C_neg, C_zero]
  rfl

theorem uNLow : (splitAt 13 family12 uNExpr).low = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -172800, 895104, 50016960] := by
  decide +kernel

theorem uNJet (j : Nat) (hj : j<13) : (uN X G) j = ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -172800, 895104, 50016960] : List Rat).getD j 0 := by
  rw [← uNEval, scalar_map_jet uNExpr j hj, uNLow]

theorem uNVanishing (j : Nat) (hj : j<10) : (uN X G) j = 0 := by
  rw [uNJet j (by omega)]
  have h : ∀ l : Fin 10, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -172800, 895104, 50016960] : List Rat).getD l.val 0 = 0 := by decide +kernel
  exact h ⟨j,hj⟩

theorem uNLeading : (uN X G) 10 = -172800 := by
  rw [uNJet 10 (by decide)]
  decide +kernel

def uDExpr : Expr := (.add (.add (.scalar (8706816 : Rat)) (.mul (.x) (.add (.scalar (-9664188 : Rat)) (.mul (.x) (.add (.scalar (90904872 : Rat)) (.mul (.x) (.add (.scalar (-48917244 : Rat)) (.mul (.x) (.scalar (-105715296 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-32256464 : Rat)) (.mul (.x) (.add (.scalar (36644638 : Rat)) (.mul (.x) (.add (.scalar (-473549634 : Rat)) (.mul (.x) (.add (.scalar (135326642 : Rat)) (.mul (.x) (.add (.scalar (288699378 : Rat)) (.mul (.x) (.scalar (-29365360 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (47168280 : Rat)) (.mul (.x) (.add (.scalar (-13402306 : Rat)) (.mul (.x) (.add (.scalar (893344012 : Rat)) (.mul (.x) (.add (.scalar (-80551390 : Rat)) (.mul (.x) (.add (.scalar (-257964480 : Rat)) (.mul (.x) (.scalar (-15132416 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-35069628 : Rat)) (.mul (.x) (.add (.scalar (-74148088 : Rat)) (.mul (.x) (.add (.scalar (-763715548 : Rat)) (.mul (.x) (.add (.scalar (-276429286 : Rat)) (.mul (.x) (.add (.scalar (-25390242 : Rat)) (.mul (.x) (.scalar (120027336 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (14493284 : Rat)) (.mul (.x) (.add (.scalar (98211592 : Rat)) (.mul (.x) (.add (.scalar (316578468 : Rat)) (.mul (.x) (.add (.scalar (522692754 : Rat)) (.mul (.x) (.add (.scalar (172213548 : Rat)) (.mul (.x) (.scalar (-77904504 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-3409380 : Rat)) (.mul (.x) (.add (.scalar (-44925366 : Rat)) (.mul (.x) (.add (.scalar (-81601050 : Rat)) (.mul (.x) (.add (.scalar (-315486648 : Rat)) (.mul (.x) (.add (.scalar (-135404604 : Rat)) (.mul (.x) (.scalar (-37586880 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (367092 : Rat)) (.mul (.x) (.add (.scalar (7483950 : Rat)) (.mul (.x) (.add (.scalar (22107276 : Rat)) (.mul (.x) (.add (.scalar (70552224 : Rat)) (.mul (.x) (.add (.scalar (64107504 : Rat)) (.mul (.x) (.scalar (41239152 : Rat)))))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (-200232 : Rat)) (.mul (.x) (.add (.scalar (-3517452 : Rat)) (.mul (.x) (.add (.scalar (-3445632 : Rat)) (.mul (.x) (.scalar (-18941040 : Rat))))))))))))))))))))))))

theorem uDEval (x y : FPS) : ringEval uDExpr x (fun _ => y) = uD x y := by
  simp only [uDExpr, uD, ringEval, C_neg, C_zero]
  rfl

theorem uDLow : (splitAt 13 family12 uDExpr).low = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1036800, 5370624, 300792960] := by
  decide +kernel

theorem uDJet (j : Nat) (hj : j<13) : (uD X G) j = ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1036800, 5370624, 300792960] : List Rat).getD j 0 := by
  rw [← uDEval, scalar_map_jet uDExpr j hj, uDLow]

theorem uDVanishing (j : Nat) (hj : j<10) : (uD X G) j = 0 := by
  rw [uDJet j (by omega)]
  have h : ∀ l : Fin 10, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1036800, 5370624, 300792960] : List Rat).getD l.val 0 = 0 := by decide +kernel
  exact h ⟨j,hj⟩

theorem uDLeading : (uD X G) 10 = -1036800 := by
  rw [uDJet 10 (by decide)]
  decide +kernel

theorem uD_cancellable : Cancellable (uD X G) := by
  intro b c h
  exact regular_cancel 10 _ uDVanishing (by rw [uDLeading]; decide +kernel) h

def lifted_u : FPS := regularQuotient 10 (uN X G) (uD X G)

theorem lifted_u_cross : uD X G * lifted_u = uN X G := by
  apply regularQuotient_cross 10 _ _ uNVanishing uDVanishing
  rw [uDLeading]
  decide +kernel

theorem lifted_u_constant : lifted_u 0 = (1/6 : Rat) := by
  unfold lifted_u
  rw [regularQuotient_constant, uNLeading, uDLeading]
  decide +kernel

#print axioms lifted_u_cross
#print axioms lifted_u_constant
end StackSorting.RationalLift
