import BivariateRowEquality
import Horner5Base
import Horner5Node400
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p401 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 348415344000), (Int.ofNat 1736737640640), (Int.ofNat 1877460068160), (Int.ofNat 1321351807680), (Int.negSucc 1662985702079), (Int.negSucc 2495199738239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3032245834559), (Int.negSucc 13819006402271), (Int.negSucc 11317129996031), (Int.negSucc 7830753506495), (Int.ofNat 13697084841984), (Int.ofNat 13343363645472), (Int.negSucc 615921392447)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11873206329120), (Int.ofNat 50109816839184), (Int.ofNat 32695024502880), (Int.ofNat 28654817410656), (Int.negSucc 42293758176863), (Int.negSucc 29441309020847), (Int.negSucc 4710565201247), (Int.ofNat 448472827008)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 27590578559279), (Int.negSucc 110230659508967), (Int.negSucc 68321386520999), (Int.negSucc 78008536462751), (Int.ofNat 64174608444672), (Int.ofNat 41668118914392), (Int.ofNat 30444932742552), (Int.negSucc 3733877577167), (Int.ofNat 176988835584)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 42244309000800), (Int.ofNat 165243113777952), (Int.ofNat 125940882512040), (Int.ofNat 148613993363568), (Int.negSucc 31362519407855), (Int.negSucc 51558661431359), (Int.negSucc 58368594633431), (Int.ofNat 1803848808624), (Int.negSucc 151088716607), (Int.ofNat 16212877824)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 44714280655679), (Int.negSucc 179447787622079), (Int.negSucc 199549789990727), (Int.negSucc 199028680603679), (Int.negSucc 73649718934559), (Int.ofNat 50969402787024), (Int.ofNat 48311737777992), (Int.ofNat 21059842321968), (Int.negSucc 2388482317343), (Int.ofNat 62219701440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 33361806840160), (Int.ofNat 145734862385648), (Int.ofNat 244995949361600), (Int.ofNat 206530369259816), (Int.ofNat 188167450434464), (Int.negSucc 11994058602063), (Int.negSucc 12650797190255), (Int.negSucc 40245616541911), (Int.ofNat 2404970306512), (Int.negSucc 121559748159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17534575975519), (Int.negSucc 89311702514223), (Int.negSucc 219930246333687), (Int.negSucc 190301611849407), (Int.negSucc 220431830088759), (Int.negSucc 62886880171287), (Int.negSucc 9591914191055), (Int.ofNat 21800716833184), (Int.ofNat 6948278812936), (Int.negSucc 490663183887)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6359069646880), (Int.ofNat 40779581921648), (Int.ofNat 141047264556512), (Int.ofNat 160479252988232), (Int.ofNat 165067609455488), (Int.ofNat 115515187874480), (Int.ofNat 20139457390488), (Int.ofNat 7737698116936), (Int.negSucc 11403511395727), (Int.ofNat 423807286688)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1515110223999), (Int.negSucc 13389201564511), (Int.negSucc 63387521374567), (Int.negSucc 110545977106815), (Int.negSucc 94223590106111), (Int.negSucc 102697795257695), (Int.negSucc 31389277320287), (Int.negSucc 14815204013375), (Int.ofNat 2716195942896), (Int.ofNat 1024609196256)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 213463210880), (Int.ofNat 2963209204480), (Int.ofNat 19282582067200), (Int.ofNat 54859727181800), (Int.ofNat 49624491118320), (Int.ofNat 54502158810000), (Int.ofNat 32445732078720), (Int.ofNat 9529864346064), (Int.ofNat 4004588774832), (Int.negSucc 1013433274079)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 13479122799), (Int.negSucc 392214087655), (Int.negSucc 3709415592415), (Int.negSucc 17881467779103), (Int.negSucc 24074493481175), (Int.negSucc 19515546672719), (Int.negSucc 19476551706527), (Int.negSucc 6027555995327), (Int.negSucc 3005565647999), (Int.negSucc 140481368255)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 23249930160), (Int.ofNat 392232231960), (Int.ofNat 3452893391304), (Int.ofNat 8620016960016), (Int.ofNat 6195170587776), (Int.ofNat 6579709148448), (Int.ofNat 3504081244800), (Int.ofNat 992500220736), (Int.ofNat 382940390016)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 15905491919), (Int.negSucc 322441463711), (Int.negSucc 1823195788751), (Int.negSucc 2027817711263), (Int.negSucc 1288504482623), (Int.negSucc 1219661937791), (Int.negSucc 308721752639), (Int.negSucc 119860539263)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7063368912), (Int.ofNat 173050313328), (Int.ofNat 471871384992), (Int.ofNat 217554628608), (Int.ofNat 201616337088), (Int.ofNat 87249279168), (Int.ofNat 10496615040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2219882111), (Int.negSucc 48032647487), (Int.negSucc 46562803775), (Int.negSucc 11124635903), (Int.negSucc 10496615039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 314010432), (Int.ofNat 5248307520)]]

theorem h5n401_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p400).getD 0 []=h5p401.getD 0 [] := by
  decide +kernel

theorem h5n401_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p400).getD 1 []=h5p401.getD 1 [] := by
  decide +kernel

theorem h5n401_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p400).getD 2 []=h5p401.getD 2 [] := by
  decide +kernel

theorem h5n401_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p400).getD 3 []=h5p401.getD 3 [] := by
  decide +kernel

theorem h5n401_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p400).getD 4 []=h5p401.getD 4 [] := by
  decide +kernel

theorem h5n401_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p400).getD 5 []=h5p401.getD 5 [] := by
  decide +kernel

theorem h5n401_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p400).getD 6 []=h5p401.getD 6 [] := by
  decide +kernel

theorem h5n401_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p400).getD 7 []=h5p401.getD 7 [] := by
  decide +kernel

theorem h5n401_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p400).getD 8 []=h5p401.getD 8 [] := by
  decide +kernel

theorem h5n401_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p400).getD 9 []=h5p401.getD 9 [] := by
  decide +kernel

theorem h5n401_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p400).getD 10 []=h5p401.getD 10 [] := by
  decide +kernel

theorem h5n401_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p400).getD 11 []=h5p401.getD 11 [] := by
  decide +kernel

theorem h5n401_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p400).getD 12 []=h5p401.getD 12 [] := by
  decide +kernel

theorem h5n401_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p400).getD 13 []=h5p401.getD 13 [] := by
  decide +kernel

theorem h5n401_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p400).getD 14 []=h5p401.getD 14 [] := by
  decide +kernel

theorem h5n401_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p400).getD 15 []=h5p401.getD 15 [] := by
  decide +kernel

theorem h5n401_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p400).getD 16 []=h5p401.getD 16 [] := by
  decide +kernel

theorem h5n401_arithmetic : BiPoly.mul h5p5 h5p400=h5p401 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p400).getD j.val []=h5p401.getD j.val [] :=
      (fun j => Fin.cases h5n401_arithmetic_row0 (fun j => Fin.cases h5n401_arithmetic_row1 (fun j => Fin.cases h5n401_arithmetic_row2 (fun j => Fin.cases h5n401_arithmetic_row3 (fun j => Fin.cases h5n401_arithmetic_row4 (fun j => Fin.cases h5n401_arithmetic_row5 (fun j => Fin.cases h5n401_arithmetic_row6 (fun j => Fin.cases h5n401_arithmetic_row7 (fun j => Fin.cases h5n401_arithmetic_row8 (fun j => Fin.cases h5n401_arithmetic_row9 (fun j => Fin.cases h5n401_arithmetic_row10 (fun j => Fin.cases h5n401_arithmetic_row11 (fun j => Fin.cases h5n401_arithmetic_row12 (fun j => Fin.cases h5n401_arithmetic_row13 (fun j => Fin.cases h5n401_arithmetic_row14 (fun j => Fin.cases h5n401_arithmetic_row15 (fun j => Fin.cases h5n401_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n401 : h5e401.toBi mapPolyEnv=h5p401 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e400.toBi mapPolyEnv)=h5p401
  rw [h5n5, h5n400]
  exact h5n401_arithmetic

#print axioms h5n401_arithmetic
end StackSorting.RationalLift
