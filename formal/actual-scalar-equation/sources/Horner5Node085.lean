import BivariateRowEquality
import Horner5Base
import Horner5Node084
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p85 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 7432860672000), (Int.ofNat 26365665784320), (Int.negSucc 73599465818879), (Int.negSucc 144599611103999), (Int.ofNat 355737599159040), (Int.negSucc 171337048692479)], [(Int.ofNat 0), (Int.negSucc 63853434881279), (Int.negSucc 177388693911935), (Int.ofNat 722888240608512), (Int.ofNat 861348880800000), (Int.negSucc 3011989071389183), (Int.ofNat 1790005168185984), (Int.negSucc 132644143420415)], [(Int.ofNat 0), (Int.ofNat 246423763365120), (Int.ofNat 500854253796864), (Int.negSucc 2965709828806847), (Int.negSucc 1866022478924543), (Int.ofNat 10287821603046528), (Int.negSucc 6712252541277695), (Int.ofNat 648721248141888), (Int.negSucc 35398060812287)], [(Int.ofNat 0), (Int.negSucc 563371868036159), (Int.negSucc 737166226841567), (Int.ofNat 6822742605872544), (Int.ofNat 1410172934602176), (Int.negSucc 18184515064157951), (Int.ofNat 10323766857642912), (Int.ofNat 421539546289824), (Int.negSucc 24256390550399), (Int.negSucc 3652307767295)], [(Int.ofNat 0), (Int.ofNat 846876630516480), (Int.ofNat 508527021374784), (Int.negSucc 9853300448788895), (Int.ofNat 747487344144384), (Int.ofNat 17219100418114752), (Int.negSucc 672373891331135), (Int.negSucc 7808691822921503), (Int.ofNat 828740205384192), (Int.negSucc 28603613631743), (Int.negSucc 106120654847)], [(Int.ofNat 0), (Int.negSucc 877941877875839), (Int.ofNat 91349894743488), (Int.ofNat 9426262729298400), (Int.negSucc 1384841742336575), (Int.negSucc 7530027420968063), (Int.negSucc 19777371016761215), (Int.ofNat 16875740410625952), (Int.negSucc 1125158613757055), (Int.ofNat 67509018327168), (Int.negSucc 2240249356799)], [(Int.ofNat 0), (Int.ofNat 639760426709760), (Int.negSucc 531784696093055), (Int.negSucc 6168903555288959), (Int.negSucc 1247344174586591), (Int.ofNat 796234758785280), (Int.ofNat 27880047794708928), (Int.negSucc 10890643747692671), (Int.negSucc 3262858022121695), (Int.ofNat 307698561648576), (Int.negSucc 4780260711935)], [(Int.ofNat 0), (Int.negSucc 327342151653119), (Int.ofNat 535421435189760), (Int.ofNat 2892032052801120), (Int.ofNat 4169977281268992), (Int.negSucc 1613183097838175), (Int.negSucc 15526251714546719), (Int.negSucc 9131828463314495), (Int.ofNat 9321544921568832), (Int.negSucc 655001397110879), (Int.ofNat 22678478520192)], [(Int.ofNat 0), (Int.ofNat 115138491183360), (Int.negSucc 303634937613311), (Int.negSucc 1100728800832319), (Int.negSucc 4430767309154783), (Int.ofNat 3270474028916928), (Int.ofNat 1973592452044224), (Int.ofNat 18759241409265504), (Int.negSucc 6502324801992479), (Int.negSucc 670590362467583), (Int.ofNat 41726528992512)], [(Int.ofNat 0), (Int.negSucc 26493846871679), (Int.ofNat 109400429393856), (Int.ofNat 417017033851104), (Int.ofNat 2746472747402304), (Int.negSucc 1825720559455103), (Int.ofNat 356827763077632), (Int.negSucc 10656190825782911), (Int.negSucc 2932065952921727), (Int.ofNat 2324290804338240), (Int.negSucc 102132156489983)], [(Int.ofNat 0), (Int.ofNat 3587502320640), (Int.negSucc 25152992281727), (Int.negSucc 156172346407871), (Int.negSucc 1123644267471455), (Int.negSucc 136932504424127), (Int.ofNat 1618934299456320), (Int.ofNat 1429737585238656), (Int.ofNat 6335867056299840), (Int.negSucc 1319034172533695), (Int.negSucc 75315072367871)], [(Int.ofNat 0), (Int.negSucc 216495449279), (Int.ofNat 3421160466912), (Int.ofNat 44414223359616), (Int.ofNat 313919477023680), (Int.ofNat 615783892967712), (Int.negSucc 1479516549250175), (Int.ofNat 441063353837952), (Int.negSucc 2973168637726463), (Int.negSucc 705746433883391), (Int.ofNat 218376867193344)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 212314008383), (Int.negSucc 7484537316383), (Int.negSucc 58234947939359), (Int.negSucc 304265366644607), (Int.ofNat 401286696600960), (Int.ofNat 256087243308672), (Int.ofNat 265213529061120), (Int.ofNat 971571631357440), (Int.negSucc 68206640385023)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 542097468864), (Int.ofNat 6369891532416), (Int.ofNat 67816291887936), (Int.ofNat 16340382602496), (Int.negSucc 267171916921343), (Int.ofNat 101751135849216), (Int.negSucc 301240409197823), (Int.negSucc 68652538454015)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 294025256639), (Int.negSucc 6462211513535), (Int.negSucc 24783763435775), (Int.ofNat 56183960358144), (Int.ofNat 15165583706880), (Int.ofNat 6711994056960), (Int.ofNat 46244505277440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 126703512576), (Int.ofNat 3127626950400), (Int.negSucc 483384464639), (Int.negSucc 13397087632895), (Int.ofNat 6727509665280), (Int.negSucc 7557562828799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 33913126655), (Int.negSucc 498990958847), (Int.ofNat 1133634424320)]]

theorem h5n85_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p84).getD 0 []=h5p85.getD 0 [] := by
  decide +kernel

theorem h5n85_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p84).getD 1 []=h5p85.getD 1 [] := by
  decide +kernel

theorem h5n85_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p84).getD 2 []=h5p85.getD 2 [] := by
  decide +kernel

theorem h5n85_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p84).getD 3 []=h5p85.getD 3 [] := by
  decide +kernel

theorem h5n85_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p84).getD 4 []=h5p85.getD 4 [] := by
  decide +kernel

theorem h5n85_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p84).getD 5 []=h5p85.getD 5 [] := by
  decide +kernel

theorem h5n85_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p84).getD 6 []=h5p85.getD 6 [] := by
  decide +kernel

theorem h5n85_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p84).getD 7 []=h5p85.getD 7 [] := by
  decide +kernel

theorem h5n85_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p84).getD 8 []=h5p85.getD 8 [] := by
  decide +kernel

theorem h5n85_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p84).getD 9 []=h5p85.getD 9 [] := by
  decide +kernel

theorem h5n85_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p84).getD 10 []=h5p85.getD 10 [] := by
  decide +kernel

theorem h5n85_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p84).getD 11 []=h5p85.getD 11 [] := by
  decide +kernel

theorem h5n85_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p84).getD 12 []=h5p85.getD 12 [] := by
  decide +kernel

theorem h5n85_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p84).getD 13 []=h5p85.getD 13 [] := by
  decide +kernel

theorem h5n85_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p84).getD 14 []=h5p85.getD 14 [] := by
  decide +kernel

theorem h5n85_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p84).getD 15 []=h5p85.getD 15 [] := by
  decide +kernel

theorem h5n85_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p84).getD 16 []=h5p85.getD 16 [] := by
  decide +kernel

theorem h5n85_arithmetic : BiPoly.mul h5p34 h5p84=h5p85 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p84).getD j.val []=h5p85.getD j.val [] :=
      (fun j => Fin.cases h5n85_arithmetic_row0 (fun j => Fin.cases h5n85_arithmetic_row1 (fun j => Fin.cases h5n85_arithmetic_row2 (fun j => Fin.cases h5n85_arithmetic_row3 (fun j => Fin.cases h5n85_arithmetic_row4 (fun j => Fin.cases h5n85_arithmetic_row5 (fun j => Fin.cases h5n85_arithmetic_row6 (fun j => Fin.cases h5n85_arithmetic_row7 (fun j => Fin.cases h5n85_arithmetic_row8 (fun j => Fin.cases h5n85_arithmetic_row9 (fun j => Fin.cases h5n85_arithmetic_row10 (fun j => Fin.cases h5n85_arithmetic_row11 (fun j => Fin.cases h5n85_arithmetic_row12 (fun j => Fin.cases h5n85_arithmetic_row13 (fun j => Fin.cases h5n85_arithmetic_row14 (fun j => Fin.cases h5n85_arithmetic_row15 (fun j => Fin.cases h5n85_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n85 : h5e85.toBi mapPolyEnv=h5p85 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e84.toBi mapPolyEnv)=h5p85
  rw [h5n34, h5n84]
  exact h5n85_arithmetic

#print axioms h5n85_arithmetic
end StackSorting.RationalLift
