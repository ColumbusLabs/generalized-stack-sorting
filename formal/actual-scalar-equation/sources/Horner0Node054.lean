import BivariateRowEquality
import Horner0Base
import Horner0Node040
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p54 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 126962265846581999), (Int.negSucc 706122518716204919), (Int.ofNat 136791123557654520), (Int.ofNat 3137562159994471320), (Int.negSucc 2358650885592493799)], [(Int.ofNat 0), (Int.ofNat 1172445126487951680), (Int.ofNat 6584499755552236176), (Int.negSucc 688340631034744343), (Int.negSucc 27614364145197010559), (Int.ofNat 21675175785720349704), (Int.negSucc 1708585720703992799)], [(Int.ofNat 0), (Int.negSucc 5103780811097366699), (Int.negSucc 27899457119128385549), (Int.ofNat 1380099356270844804), (Int.ofNat 105558052629782932776), (Int.negSucc 79295673909443351759), (Int.ofNat 8034614228054541870), (Int.negSucc 400584226381161407)], [(Int.ofNat 0), (Int.ofNat 13876452878107312620), (Int.ofNat 71019138490340621670), (Int.ofNat 568998518981218524), (Int.negSucc 222112510172731024415), (Int.ofNat 134847385735998283884), (Int.negSucc 2723616938197280573), (Int.ofNat 113857101607964220), (Int.negSucc 29427164656458623)], [(Int.ofNat 0), (Int.negSucc 26233677192202369019), (Int.negSucc 121522760674375390577), (Int.negSucc 13642862756080489571), (Int.ofNat 264493731667966412868), (Int.negSucc 52972756238322690095), (Int.negSucc 54543049690742822429), (Int.ofNat 5189414412160151316), (Int.negSucc 160308973676530967), (Int.ofNat 156839326849920)], [(Int.ofNat 0), (Int.ofNat 36260263720288485330), (Int.ofNat 149100730849458406611), (Int.ofNat 47523862080881797815), (Int.negSucc 140295160361028480149), (Int.negSucc 198004776432865355579), (Int.ofNat 135963715854007583463), (Int.negSucc 8021831702029809596), (Int.ofNat 223747695824157816), (Int.negSucc 5124710221431215)], [(Int.ofNat 0), (Int.negSucc 37506007730183357749), (Int.negSucc 137868015859706674298), (Int.negSucc 95396270457656023111), (Int.negSucc 61328156949462179043), (Int.ofNat 371798029091482246994), (Int.negSucc 101872177407626432672), (Int.negSucc 14643440240401361387), (Int.ofNat 1267274197671458914), (Int.negSucc 30570646817718543)], [(Int.ofNat 0), (Int.ofNat 29260776461744388570), (Int.ofNat 100798197238154994241), (Int.ofNat 129101737736999519265), (Int.ofNat 167251113973673051224), (Int.negSucc 247450596472335401189), (Int.negSucc 77166684228839387014), (Int.ofNat 47760284966230129199), (Int.negSucc 1812164373601093079), (Int.negSucc 1012063759913071)], [(Int.ofNat 0), (Int.negSucc 17170634165468804609), (Int.negSucc 60904704369926738514), (Int.negSucc 125664337866546969773), (Int.negSucc 142123675555392903573), (Int.negSucc 20019853920649675841), (Int.ofNat 194091882905500232921), (Int.negSucc 32606085231310186005), (Int.negSucc 2918014042100905469), (Int.ofNat 164707522409030788)], [(Int.ofNat 0), (Int.ofNat 7486823117582754810), (Int.ofNat 31097406869231646833), (Int.ofNat 90984839743325113756), (Int.ofNat 79668477366691466368), (Int.ofNat 147626152199396746003), (Int.negSucc 117614322716390861475), (Int.negSucc 24171258463805253306), (Int.ofNat 6818915923719958582), (Int.ofNat 6216614417746031)], [(Int.ofNat 0), (Int.negSucc 2369530281633198709), (Int.negSucc 13197716069296704892), (Int.negSucc 49627937925712468804), (Int.negSucc 43332618723203757574), (Int.negSucc 107034110540576662051), (Int.negSucc 14337450770184843999), (Int.ofNat 45754635799045322415), (Int.negSucc 1848453007136245926), (Int.negSucc 364047621043928381)], [(Int.ofNat 0), (Int.ofNat 522946773589933290), (Int.ofNat 4437182624523751369), (Int.ofNat 20275390543173531989), (Int.ofNat 26838860756780552822), (Int.ofNat 37845673172738214742), (Int.ofNat 55886249927170423588), (Int.negSucc 17664838245301527509), (Int.negSucc 4618472797626484029), (Int.ofNat 158553269149429374)], [(Int.ofNat 0), (Int.negSucc 75015295040356449), (Int.negSucc 1111898664203112610), (Int.negSucc 6066513475467792851), (Int.negSucc 14428598835870711001), (Int.negSucc 8539446753639653107), (Int.negSucc 30656932788569153977), (Int.negSucc 7767597642961729907), (Int.ofNat 3803863608612128334), (Int.ofNat 252786843105887490)], [(Int.ofNat 0), (Int.ofNat 6099000922963460), (Int.ofNat 193328995780142044), (Int.ofNat 1279373653468888495), (Int.ofNat 5419509984752528858), (Int.ofNat 3043617531946048659), (Int.ofNat 7200551175469887468), (Int.ofNat 9262422425887824096), (Int.negSucc 74562857318721635), (Int.negSucc 212819239604075147)], [(Int.ofNat 0), (Int.negSucc 199337251754519), (Int.negSucc 20877153206474201), (Int.negSucc 179337436447149056), (Int.negSucc 1306105181004025430), (Int.negSucc 1605152762484244829), (Int.negSucc 535067423731126031), (Int.negSucc 3222889348928502419), (Int.negSucc 1051183361505495035), (Int.negSucc 7963229086540631)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1067605517886624), (Int.ofNat 15101112486480228), (Int.ofNat 187011228275205270), (Int.ofNat 530150926575378966), (Int.ofNat 11564529259455564), (Int.ofNat 418674974925025836), (Int.ofNat 491249395520223984), (Int.ofNat 59999786963064072)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 593320199411879), (Int.negSucc 13387135591210553), (Int.negSucc 92371645666771613), (Int.negSucc 42246674360370395), (Int.ofNat 17624939827152960), (Int.negSucc 88530340087396151), (Int.negSucc 22334023660998743)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 249677470677600), (Int.ofNat 7177152873055032), (Int.ofNat 13342354218770112), (Int.negSucc 9973691627390711), (Int.ofNat 5427746296239744), (Int.ofNat 2601911432730240)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 80236102589855), (Int.negSucc 1290762686272391), (Int.ofNat 840494800059480)]]

theorem h0n54_arithmetic_row0 :
    (BiPoly.mul h0p7 h0p40).getD 0 []=h0p54.getD 0 [] := by
  decide +kernel

theorem h0n54_arithmetic_row1 :
    (BiPoly.mul h0p7 h0p40).getD 1 []=h0p54.getD 1 [] := by
  decide +kernel

theorem h0n54_arithmetic_row2 :
    (BiPoly.mul h0p7 h0p40).getD 2 []=h0p54.getD 2 [] := by
  decide +kernel

theorem h0n54_arithmetic_row3 :
    (BiPoly.mul h0p7 h0p40).getD 3 []=h0p54.getD 3 [] := by
  decide +kernel

theorem h0n54_arithmetic_row4 :
    (BiPoly.mul h0p7 h0p40).getD 4 []=h0p54.getD 4 [] := by
  decide +kernel

theorem h0n54_arithmetic_row5 :
    (BiPoly.mul h0p7 h0p40).getD 5 []=h0p54.getD 5 [] := by
  decide +kernel

theorem h0n54_arithmetic_row6 :
    (BiPoly.mul h0p7 h0p40).getD 6 []=h0p54.getD 6 [] := by
  decide +kernel

theorem h0n54_arithmetic_row7 :
    (BiPoly.mul h0p7 h0p40).getD 7 []=h0p54.getD 7 [] := by
  decide +kernel

theorem h0n54_arithmetic_row8 :
    (BiPoly.mul h0p7 h0p40).getD 8 []=h0p54.getD 8 [] := by
  decide +kernel

theorem h0n54_arithmetic_row9 :
    (BiPoly.mul h0p7 h0p40).getD 9 []=h0p54.getD 9 [] := by
  decide +kernel

theorem h0n54_arithmetic_row10 :
    (BiPoly.mul h0p7 h0p40).getD 10 []=h0p54.getD 10 [] := by
  decide +kernel

theorem h0n54_arithmetic_row11 :
    (BiPoly.mul h0p7 h0p40).getD 11 []=h0p54.getD 11 [] := by
  decide +kernel

theorem h0n54_arithmetic_row12 :
    (BiPoly.mul h0p7 h0p40).getD 12 []=h0p54.getD 12 [] := by
  decide +kernel

theorem h0n54_arithmetic_row13 :
    (BiPoly.mul h0p7 h0p40).getD 13 []=h0p54.getD 13 [] := by
  decide +kernel

theorem h0n54_arithmetic_row14 :
    (BiPoly.mul h0p7 h0p40).getD 14 []=h0p54.getD 14 [] := by
  decide +kernel

theorem h0n54_arithmetic_row15 :
    (BiPoly.mul h0p7 h0p40).getD 15 []=h0p54.getD 15 [] := by
  decide +kernel

theorem h0n54_arithmetic_row16 :
    (BiPoly.mul h0p7 h0p40).getD 16 []=h0p54.getD 16 [] := by
  decide +kernel

theorem h0n54_arithmetic_row17 :
    (BiPoly.mul h0p7 h0p40).getD 17 []=h0p54.getD 17 [] := by
  decide +kernel

theorem h0n54_arithmetic_row18 :
    (BiPoly.mul h0p7 h0p40).getD 18 []=h0p54.getD 18 [] := by
  decide +kernel

theorem h0n54_arithmetic : BiPoly.mul h0p7 h0p40=h0p54 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p7 h0p40).getD j.val []=h0p54.getD j.val [] :=
      (fun j => Fin.cases h0n54_arithmetic_row0 (fun j => Fin.cases h0n54_arithmetic_row1 (fun j => Fin.cases h0n54_arithmetic_row2 (fun j => Fin.cases h0n54_arithmetic_row3 (fun j => Fin.cases h0n54_arithmetic_row4 (fun j => Fin.cases h0n54_arithmetic_row5 (fun j => Fin.cases h0n54_arithmetic_row6 (fun j => Fin.cases h0n54_arithmetic_row7 (fun j => Fin.cases h0n54_arithmetic_row8 (fun j => Fin.cases h0n54_arithmetic_row9 (fun j => Fin.cases h0n54_arithmetic_row10 (fun j => Fin.cases h0n54_arithmetic_row11 (fun j => Fin.cases h0n54_arithmetic_row12 (fun j => Fin.cases h0n54_arithmetic_row13 (fun j => Fin.cases h0n54_arithmetic_row14 (fun j => Fin.cases h0n54_arithmetic_row15 (fun j => Fin.cases h0n54_arithmetic_row16 (fun j => Fin.cases h0n54_arithmetic_row17 (fun j => Fin.cases h0n54_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n54 : h0e54.toBi mapPolyEnv=h0p54 := by
  change BiPoly.mul (h0e7.toBi mapPolyEnv) (h0e40.toBi mapPolyEnv)=h0p54
  rw [h0n7, h0n40]
  exact h0n54_arithmetic

#print axioms h0n54_arithmetic
end StackSorting.RationalLift
