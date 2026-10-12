import BivariateRowEquality
import Horner2Base
import Horner2Node016
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p87 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 906741768960), (Int.ofNat 3753454111920), (Int.negSucc 6890398386479), (Int.negSucc 22392775125359), (Int.ofNat 30283900844400)], [(Int.ofNat 0), (Int.negSucc 7365524493239), (Int.negSucc 27869632317359), (Int.ofNat 60138880215120), (Int.ofNat 158846641298640), (Int.negSucc 228872100301559), (Int.ofNat 18093706369920)], [(Int.ofNat 0), (Int.ofNat 27988181202000), (Int.ofNat 87579454764720), (Int.negSucc 247642133754239), (Int.negSucc 455917780707599), (Int.ofNat 675941376078720), (Int.negSucc 41990364996239), (Int.ofNat 3033785116800)], [(Int.ofNat 0), (Int.negSucc 65751306485239), (Int.negSucc 142629785812599), (Int.ofNat 596612540421920), (Int.ofNat 645276331500480), (Int.negSucc 870408825495879), (Int.negSucc 164500315526839), (Int.ofNat 14513584320800), (Int.ofNat 93733291520)], [(Int.ofNat 0), (Int.ofNat 105724727220620), (Int.ofNat 103458335519060), (Int.negSucc 887334099431559), (Int.negSucc 458488704899079), (Int.ofNat 131266148310060), (Int.ofNat 783483015610500), (Int.negSucc 63235712694879), (Int.ofNat 2531255200320), (Int.negSucc 544825599)], [(Int.ofNat 0), (Int.negSucc 121306360979279), (Int.ofNat 38915576639780), (Int.ofNat 814934697556120), (Int.ofNat 268958130602760), (Int.ofNat 900423272104840), (Int.negSucc 1108770842818619), (Int.negSucc 24785623909639), (Int.ofNat 3869381607200), (Int.ofNat 9145063680)], [(Int.ofNat 0), (Int.ofNat 100534565002860), (Int.negSucc 161571625848199), (Int.negSucc 444976248664279), (Int.negSucc 486565217333159), (Int.negSucc 934260243310779), (Int.ofNat 321894890478800), (Int.ofNat 341831157409480), (Int.negSucc 20286888147999), (Int.ofNat 405535233280)], [(Int.ofNat 0), (Int.negSucc 59819886400159), (Int.ofNat 166700189366300), (Int.ofNat 146643957166300), (Int.ofNat 713247033067000), (Int.ofNat 306822115096480), (Int.ofNat 694177320090780), (Int.negSucc 446033163352899), (Int.negSucc 5818567865079), (Int.ofNat 1084287159360)], [(Int.ofNat 0), (Int.ofNat 25016918070260), (Int.negSucc 94708308916959), (Int.negSucc 69101078820899), (Int.negSucc 527771192250619), (Int.negSucc 104601051117879), (Int.negSucc 700928815290699), (Int.ofNat 65283769219060), (Int.ofNat 65468679613420), (Int.negSucc 1286906211119)], [(Int.ofNat 0), (Int.negSucc 7065539803959), (Int.ofNat 31680776503740), (Int.ofNat 73416055107340), (Int.ofNat 193002674427960), (Int.ofNat 226447317378400), (Int.ofNat 189581683063360), (Int.ofNat 250306903383900), (Int.negSucc 52934941534799), (Int.negSucc 3183137771039)], [(Int.ofNat 0), (Int.ofNat 1254488092020), (Int.negSucc 5566313441799), (Int.negSucc 53269506603199), (Int.negSucc 30044676259599), (Int.negSucc 188553905991479), (Int.ofNat 6873856183800), (Int.negSucc 174670419576239), (Int.negSucc 14121859321919), (Int.ofNat 3135470610240)], [(Int.ofNat 0), (Int.negSucc 121463434279), (Int.ofNat 160231470140), (Int.ofNat 22163361621780), (Int.ofNat 5271278121240), (Int.ofNat 62024795681640), (Int.ofNat 15319748097840), (Int.ofNat 30847684224960), (Int.ofNat 30668201530560), (Int.ofNat 1391340473280)], [(Int.ofNat 0), (Int.ofNat 4460239440), (Int.ofNat 112067972220), (Int.negSucc 5371129405739), (Int.negSucc 5470457464739), (Int.negSucc 5250604091759), (Int.negSucc 17604346352399), (Int.ofNat 3547511418960), (Int.negSucc 10349529293519), (Int.negSucc 2072161206719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14420010959), (Int.ofNat 716523708060), (Int.ofNat 2514474318240), (Int.negSucc 1657523175119), (Int.ofNat 4822171596000), (Int.negSucc 1081646725679), (Int.ofNat 810191911680), (Int.ofNat 514006041600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 41420730239), (Int.negSucc 504988045919), (Int.ofNat 424741628880), (Int.negSucc 495865508399), (Int.ofNat 88938336960)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 39738548160), (Int.negSucc 24905886479)]]

theorem h2n87_arithmetic_row0 :
    (BiPoly.mul h2p86 h2p16).getD 0 []=h2p87.getD 0 [] := by
  decide +kernel

theorem h2n87_arithmetic_row1 :
    (BiPoly.mul h2p86 h2p16).getD 1 []=h2p87.getD 1 [] := by
  decide +kernel

theorem h2n87_arithmetic_row2 :
    (BiPoly.mul h2p86 h2p16).getD 2 []=h2p87.getD 2 [] := by
  decide +kernel

theorem h2n87_arithmetic_row3 :
    (BiPoly.mul h2p86 h2p16).getD 3 []=h2p87.getD 3 [] := by
  decide +kernel

theorem h2n87_arithmetic_row4 :
    (BiPoly.mul h2p86 h2p16).getD 4 []=h2p87.getD 4 [] := by
  decide +kernel

theorem h2n87_arithmetic_row5 :
    (BiPoly.mul h2p86 h2p16).getD 5 []=h2p87.getD 5 [] := by
  decide +kernel

theorem h2n87_arithmetic_row6 :
    (BiPoly.mul h2p86 h2p16).getD 6 []=h2p87.getD 6 [] := by
  decide +kernel

theorem h2n87_arithmetic_row7 :
    (BiPoly.mul h2p86 h2p16).getD 7 []=h2p87.getD 7 [] := by
  decide +kernel

theorem h2n87_arithmetic_row8 :
    (BiPoly.mul h2p86 h2p16).getD 8 []=h2p87.getD 8 [] := by
  decide +kernel

theorem h2n87_arithmetic_row9 :
    (BiPoly.mul h2p86 h2p16).getD 9 []=h2p87.getD 9 [] := by
  decide +kernel

theorem h2n87_arithmetic_row10 :
    (BiPoly.mul h2p86 h2p16).getD 10 []=h2p87.getD 10 [] := by
  decide +kernel

theorem h2n87_arithmetic_row11 :
    (BiPoly.mul h2p86 h2p16).getD 11 []=h2p87.getD 11 [] := by
  decide +kernel

theorem h2n87_arithmetic_row12 :
    (BiPoly.mul h2p86 h2p16).getD 12 []=h2p87.getD 12 [] := by
  decide +kernel

theorem h2n87_arithmetic_row13 :
    (BiPoly.mul h2p86 h2p16).getD 13 []=h2p87.getD 13 [] := by
  decide +kernel

theorem h2n87_arithmetic_row14 :
    (BiPoly.mul h2p86 h2p16).getD 14 []=h2p87.getD 14 [] := by
  decide +kernel

theorem h2n87_arithmetic_row15 :
    (BiPoly.mul h2p86 h2p16).getD 15 []=h2p87.getD 15 [] := by
  decide +kernel

theorem h2n87_arithmetic : BiPoly.mul h2p86 h2p16=h2p87 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h2p86 h2p16).getD j.val []=h2p87.getD j.val [] :=
      (fun j => Fin.cases h2n87_arithmetic_row0 (fun j => Fin.cases h2n87_arithmetic_row1 (fun j => Fin.cases h2n87_arithmetic_row2 (fun j => Fin.cases h2n87_arithmetic_row3 (fun j => Fin.cases h2n87_arithmetic_row4 (fun j => Fin.cases h2n87_arithmetic_row5 (fun j => Fin.cases h2n87_arithmetic_row6 (fun j => Fin.cases h2n87_arithmetic_row7 (fun j => Fin.cases h2n87_arithmetic_row8 (fun j => Fin.cases h2n87_arithmetic_row9 (fun j => Fin.cases h2n87_arithmetic_row10 (fun j => Fin.cases h2n87_arithmetic_row11 (fun j => Fin.cases h2n87_arithmetic_row12 (fun j => Fin.cases h2n87_arithmetic_row13 (fun j => Fin.cases h2n87_arithmetic_row14 (fun j => Fin.cases h2n87_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n87 : h2e87.toBi mapPolyEnv=h2p87 := by
  change BiPoly.mul (h2e86.toBi mapPolyEnv) (h2e16.toBi mapPolyEnv)=h2p87
  rw [h2n86, h2n16]
  exact h2n87_arithmetic

#print axioms h2n87_arithmetic
end StackSorting.RationalLift
