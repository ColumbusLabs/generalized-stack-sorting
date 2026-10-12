import FPSDivision
import ScalarJetSemantics
import RationalMapLiterals
namespace StackSorting.RationalLift
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics StackSorting.ConcreteScalar StackSorting.ScalarJet
open StackSorting.FPSDivision
set_option maxRecDepth 12000
set_option maxHeartbeats 30000000
def tNExpr : Expr := (.add (.add (.scalar (126 : Rat)) (.mul (.x) (.add (.scalar (-36 : Rat)) (.mul (.x) (.scalar (414 : Rat)))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-545 : Rat)) (.mul (.x) (.add (.scalar (669 : Rat)) (.mul (.x) (.add (.scalar (-1451 : Rat)) (.mul (.x) (.scalar (-137 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (934 : Rat)) (.mul (.x) (.add (.scalar (-2195 : Rat)) (.mul (.x) (.add (.scalar (1824 : Rat)) (.mul (.x) (.add (.scalar (681 : Rat)) (.mul (.x) (.scalar (-70 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-792 : Rat)) (.mul (.x) (.add (.scalar (3090 : Rat)) (.mul (.x) (.add (.scalar (-340 : Rat)) (.mul (.x) (.add (.scalar (-1115 : Rat)) (.mul (.x) (.scalar (-45 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (332 : Rat)) (.mul (.x) (.add (.scalar (-2204 : Rat)) (.mul (.x) (.add (.scalar (-1654 : Rat)) (.mul (.x) (.add (.scalar (485 : Rat)) (.mul (.x) (.scalar (254 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-55 : Rat)) (.mul (.x) (.add (.scalar (789 : Rat)) (.mul (.x) (.add (.scalar (2063 : Rat)) (.mul (.x) (.add (.scalar (356 : Rat)) (.mul (.x) (.scalar (-214 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (-113 : Rat)) (.mul (.x) (.add (.scalar (-1066 : Rat)) (.mul (.x) (.add (.scalar (-444 : Rat)) (.mul (.x) (.scalar (-96 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (210 : Rat)) (.mul (.x) (.add (.scalar (264 : Rat)) (.mul (.x) (.scalar (72 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.scalar (-72 : Rat))))))))))))))))))))))))

theorem tNEval (x y : FPS) : ringEval tNExpr x (fun _ => y) = tN x y := by
  simp only [tNExpr, tN, ringEval, C_neg, C_zero]
  rfl

theorem tNLow : (splitAt 13 family12 tNExpr).low = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 576] := by
  decide +kernel

theorem tNJet (j : Nat) (hj : j<13) : (tN X G) j = ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 576] : List Rat).getD j 0 := by
  rw [← tNEval, scalar_map_jet tNExpr j hj, tNLow]

theorem tNVanishing (j : Nat) (hj : j<12) : (tN X G) j = 0 := by
  rw [tNJet j (by omega)]
  have h : ∀ l : Fin 12, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 576] : List Rat).getD l.val 0 = 0 := by decide +kernel
  exact h ⟨j,hj⟩

theorem tNLeading : (tN X G) 12 = 576 := by
  rw [tNJet 12 (by decide)]
  decide +kernel

def tDExpr : Expr := (.add (.add (.scalar (1296 : Rat)) (.mul (.x) (.scalar (1296 : Rat)))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-5640 : Rat)) (.mul (.x) (.add (.scalar (-3552 : Rat)) (.mul (.x) (.scalar (-264 : Rat)))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (9664 : Rat)) (.mul (.x) (.add (.scalar (4368 : Rat)) (.mul (.x) (.add (.scalar (2704 : Rat)) (.mul (.x) (.scalar (-176 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-8112 : Rat)) (.mul (.x) (.add (.scalar (-5192 : Rat)) (.mul (.x) (.add (.scalar (-4424 : Rat)) (.mul (.x) (.scalar (136 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (3312 : Rat)) (.mul (.x) (.add (.scalar (5608 : Rat)) (.mul (.x) (.add (.scalar (2128 : Rat)) (.mul (.x) (.scalar (952 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-520 : Rat)) (.mul (.x) (.add (.scalar (-3128 : Rat)) (.mul (.x) (.add (.scalar (-528 : Rat)) (.mul (.x) (.scalar (-1056 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (600 : Rat)) (.mul (.x) (.add (.scalar (528 : Rat)) (.mul (.x) (.scalar (144 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.scalar (-144 : Rat))))))))))))))))))))

theorem tDEval (x y : FPS) : ringEval tDExpr x (fun _ => y) = tD x y := by
  simp only [tDExpr, tD, ringEval, C_neg, C_zero]
  rfl

theorem tDLow : (splitAt 13 family12 tDExpr).low = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2304] := by
  decide +kernel

theorem tDJet (j : Nat) (hj : j<13) : (tD X G) j = ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2304] : List Rat).getD j 0 := by
  rw [← tDEval, scalar_map_jet tDExpr j hj, tDLow]

theorem tDVanishing (j : Nat) (hj : j<12) : (tD X G) j = 0 := by
  rw [tDJet j (by omega)]
  have h : ∀ l : Fin 12, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2304] : List Rat).getD l.val 0 = 0 := by decide +kernel
  exact h ⟨j,hj⟩

theorem tDLeading : (tD X G) 12 = 2304 := by
  rw [tDJet 12 (by decide)]
  decide +kernel

theorem tD_cancellable : Cancellable (tD X G) := by
  intro b c h
  exact regular_cancel 12 _ tDVanishing (by rw [tDLeading]; decide +kernel) h

def lifted_t : FPS := regularQuotient 12 (tN X G) (tD X G)

theorem lifted_t_cross : tD X G * lifted_t = tN X G := by
  apply regularQuotient_cross 12 _ _ tNVanishing tDVanishing
  rw [tDLeading]
  decide +kernel

theorem lifted_t_constant : lifted_t 0 = (1/4 : Rat) := by
  unfold lifted_t
  rw [regularQuotient_constant, tNLeading, tDLeading]
  decide +kernel

#print axioms lifted_t_cross
#print axioms lifted_t_constant
end StackSorting.RationalLift
