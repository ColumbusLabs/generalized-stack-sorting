import FPSDivision
import ScalarJetSemantics
import RationalMapLiterals
namespace StackSorting.RationalLift
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics StackSorting.ConcreteScalar StackSorting.ScalarJet
open StackSorting.FPSDivision
set_option maxRecDepth 12000
set_option maxHeartbeats 30000000
def aNExpr : Expr := (.add (.scalar 0) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-4823712 : Rat)) (.mul (.x) (.scalar (1739232 : Rat)))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (19903008 : Rat)) (.mul (.x) (.add (.scalar (-6163728 : Rat)) (.mul (.x) (.scalar (440880 : Rat)))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-32166392 : Rat)) (.mul (.x) (.add (.scalar (239448 : Rat)) (.mul (.x) (.add (.scalar (2054656 : Rat)) (.mul (.x) (.scalar (-12320 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (24635292 : Rat)) (.mul (.x) (.add (.scalar (20543536 : Rat)) (.mul (.x) (.add (.scalar (-6790820 : Rat)) (.mul (.x) (.scalar (450976 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-7510080 : Rat)) (.mul (.x) (.add (.scalar (-28676000 : Rat)) (.mul (.x) (.add (.scalar (1720144 : Rat)) (.mul (.x) (.scalar (605752 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-991528 : Rat)) (.mul (.x) (.add (.scalar (14248240 : Rat)) (.mul (.x) (.add (.scalar (8415540 : Rat)) (.mul (.x) (.scalar (-1604640 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (1148136 : Rat)) (.mul (.x) (.add (.scalar (-887376 : Rat)) (.mul (.x) (.add (.scalar (-8145624 : Rat)) (.mul (.x) (.scalar (108144 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-194724 : Rat)) (.mul (.x) (.add (.scalar (-1349856 : Rat)) (.mul (.x) (.add (.scalar (2219256 : Rat)) (.mul (.x) (.scalar (1008288 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (302616 : Rat)) (.mul (.x) (.add (.scalar (157248 : Rat)) (.mul (.x) (.scalar (-547776 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (-106272 : Rat)) (.mul (.x) (.scalar (82944 : Rat))))))))))))))))))))))))))))

theorem aNEval (x y : FPS) : ringEval aNExpr x (fun _ => y) = aN x y := by
  simp only [aNExpr, aN, ringEval, C_neg, C_zero]
  rfl

theorem aNLow : (splitAt 13 family12 aNExpr).low = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -373248, -11826432, -216312192] := by
  decide +kernel

theorem aNJet (j : Nat) (hj : j<13) : (aN X G) j = ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -373248, -11826432, -216312192] : List Rat).getD j 0 := by
  rw [← aNEval, scalar_map_jet aNExpr j hj, aNLow]

theorem aNVanishing (j : Nat) (hj : j<10) : (aN X G) j = 0 := by
  rw [aNJet j (by omega)]
  have h : ∀ l : Fin 10, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -373248, -11826432, -216312192] : List Rat).getD l.val 0 = 0 := by decide +kernel
  exact h ⟨j,hj⟩

theorem aNLeading : (aN X G) 10 = -373248 := by
  rw [aNJet 10 (by decide)]
  decide +kernel

def aDExpr : Expr := (.add (.add (.scalar (9647424 : Rat)) (.mul (.x) (.scalar (-3478464 : Rat)))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-46677636 : Rat)) (.mul (.x) (.add (.scalar (19929132 : Rat)) (.mul (.x) (.scalar (-1911888 : Rat)))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (92361738 : Rat)) (.mul (.x) (.add (.scalar (-25826328 : Rat)) (.mul (.x) (.add (.scalar (2014626 : Rat)) (.mul (.x) (.scalar (-262680 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-93931284 : Rat)) (.mul (.x) (.add (.scalar (-22305702 : Rat)) (.mul (.x) (.add (.scalar (13586376 : Rat)) (.mul (.x) (.scalar (-751746 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (48459621 : Rat)) (.mul (.x) (.add (.scalar (80868789 : Rat)) (.mul (.x) (.add (.scalar (-21660051 : Rat)) (.mul (.x) (.scalar (1443339 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-7523526 : Rat)) (.mul (.x) (.add (.scalar (-73657059 : Rat)) (.mul (.x) (.add (.scalar (-4560792 : Rat)) (.mul (.x) (.scalar (3042231 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-4166142 : Rat)) (.mul (.x) (.add (.scalar (26529657 : Rat)) (.mul (.x) (.add (.scalar (26221053 : Rat)) (.mul (.x) (.scalar (-3803550 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (2114430 : Rat)) (.mul (.x) (.add (.scalar (-295215 : Rat)) (.mul (.x) (.add (.scalar (-17394768 : Rat)) (.mul (.x) (.scalar (-1085328 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-284625 : Rat)) (.mul (.x) (.add (.scalar (-2155878 : Rat)) (.mul (.x) (.add (.scalar (3599604 : Rat)) (.mul (.x) (.scalar (2616696 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (391068 : Rat)) (.mul (.x) (.add (.scalar (269460 : Rat)) (.mul (.x) (.scalar (-1010556 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (-128628 : Rat)) (.mul (.x) (.scalar (114048 : Rat))))))))))))))))))))))))))))

theorem aDEval (x y : FPS) : ringEval aDExpr x (fun _ => y) = aD x y := by
  simp only [aDExpr, aD, ringEval, C_neg, C_zero]
  rfl

theorem aDLow : (splitAt 13 family12 aDExpr).low = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -186624, -5726592, -102056256] := by
  decide +kernel

theorem aDJet (j : Nat) (hj : j<13) : (aD X G) j = ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -186624, -5726592, -102056256] : List Rat).getD j 0 := by
  rw [← aDEval, scalar_map_jet aDExpr j hj, aDLow]

theorem aDVanishing (j : Nat) (hj : j<10) : (aD X G) j = 0 := by
  rw [aDJet j (by omega)]
  have h : ∀ l : Fin 10, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -186624, -5726592, -102056256] : List Rat).getD l.val 0 = 0 := by decide +kernel
  exact h ⟨j,hj⟩

theorem aDLeading : (aD X G) 10 = -186624 := by
  rw [aDJet 10 (by decide)]
  decide +kernel

theorem aD_cancellable : Cancellable (aD X G) := by
  intro b c h
  exact regular_cancel 10 _ aDVanishing (by rw [aDLeading]; decide +kernel) h

def lifted_a : FPS := regularQuotient 10 (aN X G) (aD X G)

theorem lifted_a_cross : aD X G * lifted_a = aN X G := by
  apply regularQuotient_cross 10 _ _ aNVanishing aDVanishing
  rw [aDLeading]
  decide +kernel

theorem lifted_a_constant : lifted_a 0 = 2 := by
  unfold lifted_a
  rw [regularQuotient_constant, aNLeading, aDLeading]
  decide +kernel

#print axioms lifted_a_cross
#print axioms lifted_a_constant
end StackSorting.RationalLift
