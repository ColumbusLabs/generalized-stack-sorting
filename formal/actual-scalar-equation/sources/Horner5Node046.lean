import BivariateRowEquality
import Horner5Base
import Horner5Node045
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p46 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 7432860671999), (Int.negSucc 26365665784319), (Int.ofNat 73599465818880), (Int.ofNat 144599611104000), (Int.negSucc 355737599159039), (Int.ofNat 171337048692480)], [(Int.ofNat 0), (Int.ofNat 63853434881280), (Int.ofNat 177388693911936), (Int.negSucc 722888240608511), (Int.negSucc 861348880799999), (Int.ofNat 3011989071389184), (Int.negSucc 1790005168185983), (Int.ofNat 132644143420416)], [(Int.ofNat 0), (Int.negSucc 246423763365119), (Int.negSucc 500854253796863), (Int.ofNat 2965709828806848), (Int.ofNat 1866022478924544), (Int.negSucc 10287821603046527), (Int.ofNat 6712252541277696), (Int.negSucc 648721248141887), (Int.ofNat 35398060812288)], [(Int.ofNat 0), (Int.ofNat 563371868036160), (Int.ofNat 737166226841568), (Int.negSucc 6822742605872543), (Int.negSucc 1410172934602175), (Int.ofNat 18184515064157952), (Int.negSucc 10323766857642911), (Int.negSucc 421539546289823), (Int.ofNat 24256390550400), (Int.ofNat 3652307767296)], [(Int.ofNat 0), (Int.negSucc 846876630516479), (Int.negSucc 508527021374783), (Int.ofNat 9853300448788896), (Int.negSucc 747487344144383), (Int.negSucc 17219100418114751), (Int.ofNat 672373891331136), (Int.ofNat 7808691822921504), (Int.negSucc 828740205384191), (Int.ofNat 28603613631744), (Int.ofNat 106120654848)], [(Int.ofNat 0), (Int.ofNat 877941877875840), (Int.negSucc 91349894743487), (Int.negSucc 9426262729298399), (Int.ofNat 1384841742336576), (Int.ofNat 7530027420968064), (Int.ofNat 19777371016761216), (Int.negSucc 16875740410625951), (Int.ofNat 1125158613757056), (Int.negSucc 67509018327167), (Int.ofNat 2240249356800)], [(Int.ofNat 0), (Int.negSucc 639760426709759), (Int.ofNat 531784696093056), (Int.ofNat 6168903555288960), (Int.ofNat 1247344174586592), (Int.negSucc 796234758785279), (Int.negSucc 27880047794708927), (Int.ofNat 10890643747692672), (Int.ofNat 3262858022121696), (Int.negSucc 307698561648575), (Int.ofNat 4780260711936)], [(Int.ofNat 0), (Int.ofNat 327342151653120), (Int.negSucc 535421435189759), (Int.negSucc 2892032052801119), (Int.negSucc 4169977281268991), (Int.ofNat 1613183097838176), (Int.ofNat 15526251714546720), (Int.ofNat 9131828463314496), (Int.negSucc 9321544921568831), (Int.ofNat 655001397110880), (Int.negSucc 22678478520191)], [(Int.ofNat 0), (Int.negSucc 115138491183359), (Int.ofNat 303634937613312), (Int.ofNat 1100728800832320), (Int.ofNat 4430767309154784), (Int.negSucc 3270474028916927), (Int.negSucc 1973592452044223), (Int.negSucc 18759241409265503), (Int.ofNat 6502324801992480), (Int.ofNat 670590362467584), (Int.negSucc 41726528992511)], [(Int.ofNat 0), (Int.ofNat 26493846871680), (Int.negSucc 109400429393855), (Int.negSucc 417017033851103), (Int.negSucc 2746472747402303), (Int.ofNat 1825720559455104), (Int.negSucc 356827763077631), (Int.ofNat 10656190825782912), (Int.ofNat 2932065952921728), (Int.negSucc 2324290804338239), (Int.ofNat 102132156489984)], [(Int.ofNat 0), (Int.negSucc 3587502320639), (Int.ofNat 25152992281728), (Int.ofNat 156172346407872), (Int.ofNat 1123644267471456), (Int.ofNat 136932504424128), (Int.negSucc 1618934299456319), (Int.negSucc 1429737585238655), (Int.negSucc 6335867056299839), (Int.ofNat 1319034172533696), (Int.ofNat 75315072367872)], [(Int.ofNat 0), (Int.ofNat 216495449280), (Int.negSucc 3421160466911), (Int.negSucc 44414223359615), (Int.negSucc 313919477023679), (Int.negSucc 615783892967711), (Int.ofNat 1479516549250176), (Int.negSucc 441063353837951), (Int.ofNat 2973168637726464), (Int.ofNat 705746433883392), (Int.negSucc 218376867193343)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 212314008384), (Int.ofNat 7484537316384), (Int.ofNat 58234947939360), (Int.ofNat 304265366644608), (Int.negSucc 401286696600959), (Int.negSucc 256087243308671), (Int.negSucc 265213529061119), (Int.negSucc 971571631357439), (Int.ofNat 68206640385024)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 542097468863), (Int.negSucc 6369891532415), (Int.negSucc 67816291887935), (Int.negSucc 16340382602495), (Int.ofNat 267171916921344), (Int.negSucc 101751135849215), (Int.ofNat 301240409197824), (Int.ofNat 68652538454016)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 294025256640), (Int.ofNat 6462211513536), (Int.ofNat 24783763435776), (Int.negSucc 56183960358143), (Int.negSucc 15165583706879), (Int.negSucc 6711994056959), (Int.negSucc 46244505277439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 126703512575), (Int.negSucc 3127626950399), (Int.ofNat 483384464640), (Int.ofNat 13397087632896), (Int.negSucc 6727509665279), (Int.ofNat 7557562828800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 33913126656), (Int.ofNat 498990958848), (Int.negSucc 1133634424319)]]

theorem h5n46_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p45).getD 0 []=h5p46.getD 0 [] := by
  decide +kernel

theorem h5n46_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p45).getD 1 []=h5p46.getD 1 [] := by
  decide +kernel

theorem h5n46_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p45).getD 2 []=h5p46.getD 2 [] := by
  decide +kernel

theorem h5n46_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p45).getD 3 []=h5p46.getD 3 [] := by
  decide +kernel

theorem h5n46_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p45).getD 4 []=h5p46.getD 4 [] := by
  decide +kernel

theorem h5n46_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p45).getD 5 []=h5p46.getD 5 [] := by
  decide +kernel

theorem h5n46_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p45).getD 6 []=h5p46.getD 6 [] := by
  decide +kernel

theorem h5n46_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p45).getD 7 []=h5p46.getD 7 [] := by
  decide +kernel

theorem h5n46_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p45).getD 8 []=h5p46.getD 8 [] := by
  decide +kernel

theorem h5n46_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p45).getD 9 []=h5p46.getD 9 [] := by
  decide +kernel

theorem h5n46_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p45).getD 10 []=h5p46.getD 10 [] := by
  decide +kernel

theorem h5n46_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p45).getD 11 []=h5p46.getD 11 [] := by
  decide +kernel

theorem h5n46_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p45).getD 12 []=h5p46.getD 12 [] := by
  decide +kernel

theorem h5n46_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p45).getD 13 []=h5p46.getD 13 [] := by
  decide +kernel

theorem h5n46_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p45).getD 14 []=h5p46.getD 14 [] := by
  decide +kernel

theorem h5n46_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p45).getD 15 []=h5p46.getD 15 [] := by
  decide +kernel

theorem h5n46_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p45).getD 16 []=h5p46.getD 16 [] := by
  decide +kernel

theorem h5n46_arithmetic : BiPoly.mul h5p34 h5p45=h5p46 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p45).getD j.val []=h5p46.getD j.val [] :=
      (fun j => Fin.cases h5n46_arithmetic_row0 (fun j => Fin.cases h5n46_arithmetic_row1 (fun j => Fin.cases h5n46_arithmetic_row2 (fun j => Fin.cases h5n46_arithmetic_row3 (fun j => Fin.cases h5n46_arithmetic_row4 (fun j => Fin.cases h5n46_arithmetic_row5 (fun j => Fin.cases h5n46_arithmetic_row6 (fun j => Fin.cases h5n46_arithmetic_row7 (fun j => Fin.cases h5n46_arithmetic_row8 (fun j => Fin.cases h5n46_arithmetic_row9 (fun j => Fin.cases h5n46_arithmetic_row10 (fun j => Fin.cases h5n46_arithmetic_row11 (fun j => Fin.cases h5n46_arithmetic_row12 (fun j => Fin.cases h5n46_arithmetic_row13 (fun j => Fin.cases h5n46_arithmetic_row14 (fun j => Fin.cases h5n46_arithmetic_row15 (fun j => Fin.cases h5n46_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n46 : h5e46.toBi mapPolyEnv=h5p46 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e45.toBi mapPolyEnv)=h5p46
  rw [h5n34, h5n45]
  exact h5n46_arithmetic

#print axioms h5n46_arithmetic
end StackSorting.RationalLift
