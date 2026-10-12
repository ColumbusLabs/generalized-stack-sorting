import BivariateRowEquality
import Horner5Base
import Horner5Node160
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p161 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4839101999), (Int.negSucc 19282254119), (Int.ofNat 2884623840), (Int.ofNat 17327775960)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 25894572480), (Int.ofNat 92981190816), (Int.negSucc 35231993279), (Int.negSucc 67579821503), (Int.ofNat 7806964032)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 58246657739), (Int.negSucc 193949699777), (Int.ofNat 72843507414), (Int.ofNat 86014725498), (Int.negSucc 2081909033), (Int.ofNat 829067616)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 71247711780), (Int.ofNat 231329568762), (Int.negSucc 1557086975), (Int.negSucc 46471653449), (Int.negSucc 44396912159), (Int.ofNat 2993264820)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 51088968719), (Int.negSucc 174449171375), (Int.negSucc 152025714089), (Int.ofNat 11720677212), (Int.ofNat 54993577320), (Int.negSucc 2600333297)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 21449767680), (Int.ofNat 85205604960), (Int.ofNat 204548320314), (Int.ofNat 26368220538), (Int.negSucc 7863849341), (Int.negSucc 9667520135)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4883908499), (Int.negSucc 25811275949), (Int.negSucc 124808599259), (Int.negSucc 66802675445), (Int.negSucc 16905675743), (Int.ofNat 7945637976)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 466585020), (Int.ofNat 4242474630), (Int.ofNat 38311029738), (Int.ofNat 58314888468), (Int.ofNat 13507504380), (Int.ofNat 2621175444)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 266437943), (Int.negSucc 5078025863), (Int.negSucc 22072571063), (Int.negSucc 9084215015), (Int.negSucc 3336373583)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 113938164), (Int.ofNat 3165917292), (Int.ofNat 4031663328), (Int.ofNat 656038440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 39251303), (Int.negSucc 656038439)]]

theorem h5n161_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p160).getD 0 []=h5p161.getD 0 [] := by
  decide +kernel

theorem h5n161_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p160).getD 1 []=h5p161.getD 1 [] := by
  decide +kernel

theorem h5n161_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p160).getD 2 []=h5p161.getD 2 [] := by
  decide +kernel

theorem h5n161_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p160).getD 3 []=h5p161.getD 3 [] := by
  decide +kernel

theorem h5n161_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p160).getD 4 []=h5p161.getD 4 [] := by
  decide +kernel

theorem h5n161_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p160).getD 5 []=h5p161.getD 5 [] := by
  decide +kernel

theorem h5n161_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p160).getD 6 []=h5p161.getD 6 [] := by
  decide +kernel

theorem h5n161_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p160).getD 7 []=h5p161.getD 7 [] := by
  decide +kernel

theorem h5n161_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p160).getD 8 []=h5p161.getD 8 [] := by
  decide +kernel

theorem h5n161_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p160).getD 9 []=h5p161.getD 9 [] := by
  decide +kernel

theorem h5n161_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p160).getD 10 []=h5p161.getD 10 [] := by
  decide +kernel

theorem h5n161_arithmetic : BiPoly.mul h5p6 h5p160=h5p161 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p160).getD j.val []=h5p161.getD j.val [] :=
      (fun j => Fin.cases h5n161_arithmetic_row0 (fun j => Fin.cases h5n161_arithmetic_row1 (fun j => Fin.cases h5n161_arithmetic_row2 (fun j => Fin.cases h5n161_arithmetic_row3 (fun j => Fin.cases h5n161_arithmetic_row4 (fun j => Fin.cases h5n161_arithmetic_row5 (fun j => Fin.cases h5n161_arithmetic_row6 (fun j => Fin.cases h5n161_arithmetic_row7 (fun j => Fin.cases h5n161_arithmetic_row8 (fun j => Fin.cases h5n161_arithmetic_row9 (fun j => Fin.cases h5n161_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n161 : h5e161.toBi mapPolyEnv=h5p161 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e160.toBi mapPolyEnv)=h5p161
  rw [h5n6, h5n160]
  exact h5n161_arithmetic

#print axioms h5n161_arithmetic
end StackSorting.RationalLift
