import BivariateRowEquality
import Horner2Base
import Horner2Node011
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p12 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 918076041071), (Int.negSucc 6956258679503), (Int.negSucc 10738597567247), (Int.ofNat 14351980942224), (Int.ofNat 19052395871040)], [(Int.ofNat 0), (Int.ofNat 7560664586424), (Int.ofNat 57286071372240), (Int.ofNat 88650072331344), (Int.negSucc 105494922071567), (Int.negSucc 109268322521831), (Int.ofNat 1336357468512)], [(Int.ofNat 0), (Int.negSucc 29138549679791), (Int.negSucc 213486993280943), (Int.negSucc 319332011832287), (Int.ofNat 338036031879120), (Int.ofNat 268797461590368), (Int.ofNat 43240825631664), (Int.negSucc 3676644848447)], [(Int.ofNat 0), (Int.ofNat 69470653860864), (Int.ofNat 474775763626512), (Int.ofNat 673504870008816), (Int.negSucc 534279063225743), (Int.negSucc 371917416127535), (Int.negSucc 234094319850383), (Int.ofNat 21602563840224), (Int.negSucc 703142174591)], [(Int.ofNat 0), (Int.negSucc 113496650778395), (Int.negSucc 703556851217435), (Int.negSucc 951182002385543), (Int.ofNat 255255198035448), (Int.ofNat 384148332524532), (Int.ofNat 465656925285396), (Int.negSucc 4825050675119), (Int.negSucc 281733228479), (Int.ofNat 3595848960)], [(Int.ofNat 0), (Int.ofNat 132570395753184), (Int.ofNat 740673022265556), (Int.ofNat 989189742554136), (Int.ofNat 521474805875832), (Int.negSucc 362712670319879), (Int.negSucc 379336302888347), (Int.negSucc 128924455874711), (Int.ofNat 9450599104800), (Int.negSucc 129659236607)], [(Int.ofNat 0), (Int.negSucc 112162499430803), (Int.negSucc 582896247574919), (Int.negSucc 821030232086279), (Int.negSucc 1102026855147719), (Int.ofNat 127204220915316), (Int.ofNat 25503301561872), (Int.ofNat 251502714460776), (Int.negSucc 4481881629407), (Int.negSucc 266828431871)], [(Int.ofNat 0), (Int.ofNat 68372958005784), (Int.ofNat 359337914020596), (Int.ofNat 575938587447348), (Int.ofNat 1005602971948656), (Int.ofNat 345101474867568), (Int.ofNat 142720846957596), (Int.negSucc 133673178199595), (Int.negSucc 30274033353887), (Int.ofNat 1027894437696)], [(Int.ofNat 0), (Int.negSucc 29413865191043), (Int.negSucc 178920816714911), (Int.negSucc 347608040001563), (Int.negSucc 551963698462955), (Int.negSucc 591744131667335), (Int.negSucc 119080287657851), (Int.negSucc 71653484313683), (Int.ofNat 42321144459036), (Int.ofNat 1212347071152)], [(Int.ofNat 0), (Int.ofNat 8582326386264), (Int.ofNat 71306156160924), (Int.ofNat 176598056053452), (Int.ofNat 212727299159064), (Int.ofNat 417304171983120), (Int.ofNat 128194073451600), (Int.ofNat 104416125926940), (Int.negSucc 5554401836639), (Int.negSucc 2485714630463)], [(Int.ofNat 0), (Int.negSucc 1580302573115), (Int.negSucc 21540751386887), (Int.negSucc 71724677137487), (Int.negSucc 74375581544111), (Int.negSucc 151242920470055), (Int.negSucc 119489161446983), (Int.negSucc 45976909575023), (Int.negSucc 18347252758559), (Int.negSucc 156387169151)], [(Int.ofNat 0), (Int.ofNat 158943354744), (Int.ofNat 4529870731788), (Int.ofNat 21694165868364), (Int.ofNat 28034254100784), (Int.ofNat 27515042455464), (Int.ofNat 56675748526704), (Int.ofNat 17196027775776), (Int.ofNat 11134619917344), (Int.ofNat 1462247862912)], [(Int.ofNat 0), (Int.negSucc 5998253039), (Int.negSucc 586500446771), (Int.negSucc 4497568432883), (Int.negSucc 9014306261075), (Int.negSucc 2714522065199), (Int.negSucc 12085505387279), (Int.negSucc 7121217426767), (Int.negSucc 2815017837839), (Int.negSucc 606407549759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 35621123760), (Int.ofNat 572411691324), (Int.ofNat 1867642003728), (Int.ofNat 664590728880), (Int.ofNat 660862397376), (Int.ofNat 1604029979088), (Int.ofNat 520644428352), (Int.ofNat 61680724992)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 34776511487), (Int.negSucc 204071996159), (Int.negSucc 218882524751), (Int.ofNat 137661442704), (Int.negSucc 120474827711), (Int.negSucc 61680724991)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7947709632), (Int.ofNat 26809661232), (Int.negSucc 19924709183)]]

theorem h2n12_arithmetic_row0 :
    (BiPoly.mul h2p4 h2p11).getD 0 []=h2p12.getD 0 [] := by
  decide +kernel

theorem h2n12_arithmetic_row1 :
    (BiPoly.mul h2p4 h2p11).getD 1 []=h2p12.getD 1 [] := by
  decide +kernel

theorem h2n12_arithmetic_row2 :
    (BiPoly.mul h2p4 h2p11).getD 2 []=h2p12.getD 2 [] := by
  decide +kernel

theorem h2n12_arithmetic_row3 :
    (BiPoly.mul h2p4 h2p11).getD 3 []=h2p12.getD 3 [] := by
  decide +kernel

theorem h2n12_arithmetic_row4 :
    (BiPoly.mul h2p4 h2p11).getD 4 []=h2p12.getD 4 [] := by
  decide +kernel

theorem h2n12_arithmetic_row5 :
    (BiPoly.mul h2p4 h2p11).getD 5 []=h2p12.getD 5 [] := by
  decide +kernel

theorem h2n12_arithmetic_row6 :
    (BiPoly.mul h2p4 h2p11).getD 6 []=h2p12.getD 6 [] := by
  decide +kernel

theorem h2n12_arithmetic_row7 :
    (BiPoly.mul h2p4 h2p11).getD 7 []=h2p12.getD 7 [] := by
  decide +kernel

theorem h2n12_arithmetic_row8 :
    (BiPoly.mul h2p4 h2p11).getD 8 []=h2p12.getD 8 [] := by
  decide +kernel

theorem h2n12_arithmetic_row9 :
    (BiPoly.mul h2p4 h2p11).getD 9 []=h2p12.getD 9 [] := by
  decide +kernel

theorem h2n12_arithmetic_row10 :
    (BiPoly.mul h2p4 h2p11).getD 10 []=h2p12.getD 10 [] := by
  decide +kernel

theorem h2n12_arithmetic_row11 :
    (BiPoly.mul h2p4 h2p11).getD 11 []=h2p12.getD 11 [] := by
  decide +kernel

theorem h2n12_arithmetic_row12 :
    (BiPoly.mul h2p4 h2p11).getD 12 []=h2p12.getD 12 [] := by
  decide +kernel

theorem h2n12_arithmetic_row13 :
    (BiPoly.mul h2p4 h2p11).getD 13 []=h2p12.getD 13 [] := by
  decide +kernel

theorem h2n12_arithmetic_row14 :
    (BiPoly.mul h2p4 h2p11).getD 14 []=h2p12.getD 14 [] := by
  decide +kernel

theorem h2n12_arithmetic_row15 :
    (BiPoly.mul h2p4 h2p11).getD 15 []=h2p12.getD 15 [] := by
  decide +kernel

theorem h2n12_arithmetic : BiPoly.mul h2p4 h2p11=h2p12 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h2p4 h2p11).getD j.val []=h2p12.getD j.val [] :=
      (fun j => Fin.cases h2n12_arithmetic_row0 (fun j => Fin.cases h2n12_arithmetic_row1 (fun j => Fin.cases h2n12_arithmetic_row2 (fun j => Fin.cases h2n12_arithmetic_row3 (fun j => Fin.cases h2n12_arithmetic_row4 (fun j => Fin.cases h2n12_arithmetic_row5 (fun j => Fin.cases h2n12_arithmetic_row6 (fun j => Fin.cases h2n12_arithmetic_row7 (fun j => Fin.cases h2n12_arithmetic_row8 (fun j => Fin.cases h2n12_arithmetic_row9 (fun j => Fin.cases h2n12_arithmetic_row10 (fun j => Fin.cases h2n12_arithmetic_row11 (fun j => Fin.cases h2n12_arithmetic_row12 (fun j => Fin.cases h2n12_arithmetic_row13 (fun j => Fin.cases h2n12_arithmetic_row14 (fun j => Fin.cases h2n12_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n12 : h2e12.toBi mapPolyEnv=h2p12 := by
  change BiPoly.mul (h2e4.toBi mapPolyEnv) (h2e11.toBi mapPolyEnv)=h2p12
  rw [h2n4, h2n11]
  exact h2n12_arithmetic

#print axioms h2n12_arithmetic
end StackSorting.RationalLift
