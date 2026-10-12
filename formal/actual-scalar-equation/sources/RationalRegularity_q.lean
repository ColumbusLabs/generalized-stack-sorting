import FPSDivision
import ScalarJetSemantics
import RationalMapLiterals
namespace StackSorting.RationalLift
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics StackSorting.ConcreteScalar StackSorting.ScalarJet
open StackSorting.FPSDivision
set_option maxRecDepth 12000
set_option maxHeartbeats 30000000
def qNExpr : Expr := (.add (.add (.scalar (-268839000 : Rat)) (.mul (.x) (.add (.scalar (-802397340 : Rat)) (.mul (.x) (.scalar (962654220 : Rat)))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (1169748360 : Rat)) (.mul (.x) (.add (.scalar (3193476012 : Rat)) (.mul (.x) (.add (.scalar (-4188154752 : Rat)) (.mul (.x) (.scalar (433720224 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-2066177070 : Rat)) (.mul (.x) (.add (.scalar (-5515330239 : Rat)) (.mul (.x) (.add (.scalar (5374037010 : Rat)) (.mul (.x) (.add (.scalar (-161720925 : Rat)) (.mul (.x) (.scalar (46059312 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (1892029140 : Rat)) (.mul (.x) (.add (.scalar (5444283330 : Rat)) (.mul (.x) (.add (.scalar (-156751152 : Rat)) (.mul (.x) (.add (.scalar (-2586728298 : Rat)) (.mul (.x) (.scalar (166292490 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-946246900 : Rat)) (.mul (.x) (.add (.scalar (-3301090402 : Rat)) (.mul (.x) (.add (.scalar (-5301533755 : Rat)) (.mul (.x) (.add (.scalar (3365954191 : Rat)) (.mul (.x) (.scalar (-144462961 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (245406860 : Rat)) (.mul (.x) (.add (.scalar (1187147458 : Rat)) (.mul (.x) (.add (.scalar (4875114360 : Rat)) (.mul (.x) (.add (.scalar (-44259028 : Rat)) (.mul (.x) (.scalar (-537084452 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-25921390 : Rat)) (.mul (.x) (.add (.scalar (-220890927 : Rat)) (.mul (.x) (.add (.scalar (-1837805783 : Rat)) (.mul (.x) (.add (.scalar (-1917712992 : Rat)) (.mul (.x) (.scalar (441424332 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (14802108 : Rat)) (.mul (.x) (.add (.scalar (275782650 : Rat)) (.mul (.x) (.add (.scalar (1046220384 : Rat)) (.mul (.x) (.scalar (145620858 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (-6329898 : Rat)) (.mul (.x) (.add (.scalar (-173703666 : Rat)) (.mul (.x) (.scalar (-185354088 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (2180628 : Rat)) (.mul (.x) (.scalar (36446580 : Rat))))))))))))))))))))))))))))

theorem qNEval (x y : FPS) : ringEval qNExpr x (fun _ => y) = qN x y := by
  simp only [qNExpr, qN, ringEval, C_neg, C_zero]
  rfl

theorem qNLow : (splitAt 13 family12 qNExpr).low = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31543776, 825010368, 12851318832] := by
  decide +kernel

theorem qNJet (j : Nat) (hj : j<13) : (qN X G) j = ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31543776, 825010368, 12851318832] : List Rat).getD j 0 := by
  rw [← qNEval, scalar_map_jet qNExpr j hj, qNLow]

theorem qNVanishing (j : Nat) (hj : j<10) : (qN X G) j = 0 := by
  rw [qNJet j (by omega)]
  have h : ∀ l : Fin 10, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31543776, 825010368, 12851318832] : List Rat).getD l.val 0 = 0 := by decide +kernel
  exact h ⟨j,hj⟩

theorem qNLeading : (qN X G) 10 = 31543776 := by
  rw [qNJet 10 (by decide)]
  decide +kernel

def qDExpr : Expr := (.add (.add (.scalar (472261338 : Rat)) (.mul (.x) (.add (.scalar (1217015676 : Rat)) (.mul (.x) (.scalar (-2450153790 : Rat)))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-2306280714 : Rat)) (.mul (.x) (.add (.scalar (-6703599180 : Rat)) (.mul (.x) (.add (.scalar (10748750526 : Rat)) (.mul (.x) (.scalar (-670962072 : Rat)))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (5320050962 : Rat)) (.mul (.x) (.add (.scalar (12293004262 : Rat)) (.mul (.x) (.add (.scalar (-16403256160 : Rat)) (.mul (.x) (.add (.scalar (117391062 : Rat)) (.mul (.x) (.scalar (3405160 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-7419367907 : Rat)) (.mul (.x) (.add (.scalar (-8377521067 : Rat)) (.mul (.x) (.add (.scalar (4036034801 : Rat)) (.mul (.x) (.add (.scalar (4035733571 : Rat)) (.mul (.x) (.scalar (-123557268 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (6517991433 : Rat)) (.mul (.x) (.add (.scalar (402433922 : Rat)) (.mul (.x) (.add (.scalar (12339545263 : Rat)) (.mul (.x) (.add (.scalar (-5980552106 : Rat)) (.mul (.x) (.scalar (-206952322 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-3504802105 : Rat)) (.mul (.x) (.add (.scalar (987248176 : Rat)) (.mul (.x) (.add (.scalar (-10739512339 : Rat)) (.mul (.x) (.add (.scalar (583467373 : Rat)) (.mul (.x) (.scalar (377382165 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (1074940707 : Rat)) (.mul (.x) (.add (.scalar (858249577 : Rat)) (.mul (.x) (.add (.scalar (2281968902 : Rat)) (.mul (.x) (.add (.scalar (2850082835 : Rat)) (.mul (.x) (.scalar (90990270 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (-162483782 : Rat)) (.mul (.x) (.add (.scalar (-936223363 : Rat)) (.mul (.x) (.add (.scalar (334049373 : Rat)) (.mul (.x) (.add (.scalar (-1338212760 : Rat)) (.mul (.x) (.scalar (-249725646 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.add (.scalar (7690068 : Rat)) (.mul (.x) (.add (.scalar (298735941 : Rat)) (.mul (.x) (.add (.scalar (-165027066 : Rat)) (.mul (.x) (.add (.scalar (144652032 : Rat)) (.mul (.x) (.scalar (71389728 : Rat)))))))))) (.mul (.unknown ⟨0, by decide⟩) (.add (.scalar (0 : Rat)) (.mul (.x) (.add (.scalar (-36794952 : Rat)) (.mul (.x) (.scalar (23061006 : Rat))))))))))))))))))))))))

theorem qDEval (x y : FPS) : ringEval qDExpr x (fun _ => y) = qD x y := by
  simp only [qDExpr, qD, ringEval, C_neg, C_zero]
  rfl

theorem qDLow : (splitAt 13 family12 qDExpr).low = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 567787968, 15985762560, 265187890656] := by
  decide +kernel

theorem qDJet (j : Nat) (hj : j<13) : (qD X G) j = ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 567787968, 15985762560, 265187890656] : List Rat).getD j 0 := by
  rw [← qDEval, scalar_map_jet qDExpr j hj, qDLow]

theorem qDVanishing (j : Nat) (hj : j<10) : (qD X G) j = 0 := by
  rw [qDJet j (by omega)]
  have h : ∀ l : Fin 10, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 567787968, 15985762560, 265187890656] : List Rat).getD l.val 0 = 0 := by decide +kernel
  exact h ⟨j,hj⟩

theorem qDLeading : (qD X G) 10 = 567787968 := by
  rw [qDJet 10 (by decide)]
  decide +kernel

theorem qD_cancellable : Cancellable (qD X G) := by
  intro b c h
  exact regular_cancel 10 _ qDVanishing (by rw [qDLeading]; decide +kernel) h

def lifted_q : FPS := regularQuotient 10 (qN X G) (qD X G)

theorem lifted_q_cross : qD X G * lifted_q = qN X G := by
  apply regularQuotient_cross 10 _ _ qNVanishing qDVanishing
  rw [qDLeading]
  decide +kernel

theorem lifted_q_constant : lifted_q 0 = (1/18 : Rat) := by
  unfold lifted_q
  rw [regularQuotient_constant, qNLeading, qDLeading]
  decide +kernel

#print axioms lifted_q_cross
#print axioms lifted_q_constant
end StackSorting.RationalLift
