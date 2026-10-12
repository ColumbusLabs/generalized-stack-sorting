import FPSDivision
import ScalarJetSemantics
import RationalMapLiterals
namespace StackSorting.RationalLift
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics StackSorting.ConcreteScalar StackSorting.ScalarJet
open StackSorting.FPSDivision
set_option maxRecDepth 12000
set_option maxHeartbeats 30000000
def iNExpr : Expr := (.add (.add (.scalar (-192 : Rat)) (.mul (.x) (.add (.scalar (-300 : Rat)) (.mul (.x) (.scalar (1236 : Rat)))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (622 : Rat)) (.mul (.x) (.add (.scalar (108 : Rat)) (.mul (.x) (.add (.scalar (-3638 : Rat)) (.mul (.x) (.scalar (400 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-726 : Rat)) (.mul (.x) (.add (.scalar (1060 : Rat)) (.mul (.x) (.add (.scalar (2766 : Rat)) (.mul (.x) (.add (.scalar (1104 : Rat)) (.mul (.x) (.scalar (16 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (354 : Rat)) (.mul (.x) (.add (.scalar (-1366 : Rat)) (.mul (.x) (.add (.scalar (-384 : Rat)) (.mul (.x) (.add (.scalar (-3318 : Rat)) (.mul (.x) (.scalar (312 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-58 : Rat)) (.mul (.x) (.add (.scalar (588 : Rat)) (.mul (.x) (.add (.scalar (444 : Rat)) (.mul (.x) (.add (.scalar (1356 : Rat)) (.mul (.x) (.scalar (384 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (-90 : Rat)) (.mul (.x) (.add (.scalar (-552 : Rat)) (.mul (.x) (.add (.scalar (324 : Rat)) (.mul (.x) (.scalar (-720 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.scalar (108 : Rat))))))))))))))))))

theorem iNEval (x y : FPS) : ringEval iNExpr x (fun _ => y) = iN x y := by
  simp only [iNExpr, iN, ringEval, C_neg, C_zero]
  rfl

theorem iNLow : (splitAt 13 family12 iNExpr).low = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2304] := by
  decide +kernel

theorem iNJet (j : Nat) (hj : j<13) : (iN X G) j = ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2304] : List Rat).getD j 0 := by
  rw [← iNEval, scalar_map_jet iNExpr j hj, iNLow]

theorem iNVanishing (j : Nat) (hj : j<12) : (iN X G) j = 0 := by
  rw [iNJet j (by omega)]
  have h : ∀ l : Fin 12, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2304] : List Rat).getD l.val 0 = 0 := by decide +kernel
  exact h ⟨j,hj⟩

theorem iNLeading : (iN X G) 12 = 2304 := by
  rw [iNJet 12 (by decide)]
  decide +kernel

def iDExpr : Expr := (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (-162 : Rat)) (.mul (.x) (.scalar (-162 : Rat)))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (543 : Rat)) (.mul (.x) (.add (.scalar (282 : Rat)) (.mul (.x) (.scalar (33 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (-665 : Rat)) (.mul (.x) (.add (.scalar (-264 : Rat)) (.mul (.x) (.add (.scalar (-305 : Rat)) (.mul (.x) (.scalar (22 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (349 : Rat)) (.mul (.x) (.add (.scalar (385 : Rat)) (.mul (.x) (.add (.scalar (248 : Rat)) (.mul (.x) (.scalar (5 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (-65 : Rat)) (.mul (.x) (.add (.scalar (-316 : Rat)) (.mul (.x) (.add (.scalar (-18 : Rat)) (.mul (.x) (.scalar (-114 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (75 : Rat)) (.mul (.x) (.add (.scalar (48 : Rat)) (.mul (.x) (.scalar (18 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.scalar (-18 : Rat))))))))))))))))))))

theorem iDEval (x y : FPS) : ringEval iDExpr x (fun _ => y) = iD x y := by
  simp only [iDExpr, iD, ringEval, C_neg, C_zero]
  rfl

theorem iDLow : (splitAt 13 family12 iDExpr).low = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 288] := by
  decide +kernel

theorem iDJet (j : Nat) (hj : j<13) : (iD X G) j = ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 288] : List Rat).getD j 0 := by
  rw [← iDEval, scalar_map_jet iDExpr j hj, iDLow]

theorem iDVanishing (j : Nat) (hj : j<12) : (iD X G) j = 0 := by
  rw [iDJet j (by omega)]
  have h : ∀ l : Fin 12, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 288] : List Rat).getD l.val 0 = 0 := by decide +kernel
  exact h ⟨j,hj⟩

theorem iDLeading : (iD X G) 12 = 288 := by
  rw [iDJet 12 (by decide)]
  decide +kernel

theorem iD_cancellable : Cancellable (iD X G) := by
  intro b c h
  exact regular_cancel 12 _ iDVanishing (by rw [iDLeading]; decide +kernel) h

def lifted_i : FPS := regularQuotient 12 (iN X G) (iD X G)

theorem lifted_i_cross : iD X G * lifted_i = iN X G := by
  apply regularQuotient_cross 12 _ _ iNVanishing iDVanishing
  rw [iDLeading]
  decide +kernel

theorem lifted_i_constant : lifted_i 0 = 8 := by
  unfold lifted_i
  rw [regularQuotient_constant, iNLeading, iDLeading]
  decide +kernel

#print axioms lifted_i_cross
#print axioms lifted_i_constant
end StackSorting.RationalLift
