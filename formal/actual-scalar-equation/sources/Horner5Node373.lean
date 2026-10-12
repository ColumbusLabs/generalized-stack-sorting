import BivariateRowEquality
import Horner5Base
import Horner5Node372
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p373 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 348415343999), (Int.negSucc 691491608639), (Int.ofNat 4709866915368), (Int.ofNat 8523582167232), (Int.negSucc 1372791622319), (Int.negSucc 11988079061183), (Int.negSucc 7144648451639)], [(Int.ofNat 0), (Int.ofNat 3032245834560), (Int.ofNat 4722268898592), (Int.negSucc 42858000152027), (Int.negSucc 66849701730515), (Int.ofNat 13607857191816), (Int.ofNat 83740663350648), (Int.ofNat 40291809711444), (Int.negSucc 501134050691)], [(Int.ofNat 0), (Int.negSucc 11873206329119), (Int.negSucc 14490197851823), (Int.ofNat 172683247413996), (Int.ofNat 243966136968792), (Int.negSucc 45268241346287), (Int.negSucc 258192931663439), (Int.negSucc 114736838325875), (Int.negSucc 14957016834743), (Int.ofNat 1378741818168)], [(Int.ofNat 0), (Int.ofNat 27590578559280), (Int.ofNat 27458923831128), (Int.negSucc 410284397316887), (Int.negSucc 561493301684471), (Int.ofNat 44095610016000), (Int.ofNat 440413005650544), (Int.ofNat 234949580271072), (Int.ofNat 78547270199616), (Int.negSucc 7814708285687), (Int.ofNat 263678315472)], [(Int.ofNat 0), (Int.negSucc 42244309000799), (Int.negSucc 38510186775551), (Int.ofNat 644239415780706), (Int.ofNat 926090087090028), (Int.ofNat 125344973953374), (Int.negSucc 410757281031527), (Int.negSucc 386975114733809), (Int.negSucc 164612407910675), (Int.ofNat 1561821291402), (Int.ofNat 112745067072), (Int.negSucc 1348443359)], [(Int.ofNat 0), (Int.ofNat 44714280655680), (Int.ofNat 45304945655040), (Int.negSucc 707894142672881), (Int.negSucc 1163191767779687), (Int.negSucc 522816124117373), (Int.ofNat 110037036119364), (Int.ofNat 448264096413342), (Int.ofNat 186314508628932), (Int.ofNat 44401690518870), (Int.negSucc 3475049709923), (Int.ofNat 48622213728)], [(Int.ofNat 0), (Int.negSucc 33361806840159), (Int.negSucc 45649441865167), (Int.ofNat 559307980571326), (Int.ofNat 1138713966840616), (Int.ofNat 947826330837316), (Int.ofNat 259754875856860), (Int.negSucc 241454488292093), (Int.negSucc 144351294789999), (Int.negSucc 88497634080927), (Int.ofNat 1646349019684), (Int.ofNat 100060661952)], [(Int.ofNat 0), (Int.ofNat 17534575975520), (Int.ofNat 36707974587664), (Int.negSucc 318808047363865), (Int.negSucc 871923400868317), (Int.negSucc 1081005341260231), (Int.negSucc 511216221903457), (Int.negSucc 125004232706561), (Int.ofNat 89529761392766), (Int.ofNat 60347078728532), (Int.ofNat 10718274943210), (Int.negSucc 385460414135)], [(Int.ofNat 0), (Int.negSucc 6359069646879), (Int.negSucc 21702372981007), (Int.ofNat 127971716003674), (Int.ofNat 519559738574644), (Int.ofNat 847268787606016), (Int.ofNat 590272517276548), (Int.ofNat 321365184138654), (Int.ofNat 4177904413208), (Int.negSucc 1044555176289), (Int.negSucc 15614037728419), (Int.negSucc 454630151681)], [(Int.ofNat 0), (Int.ofNat 1515110224000), (Int.ofNat 8843870892512), (Int.negSucc 33774370684929), (Int.negSucc 238653481917709), (Int.negSucc 474250926275933), (Int.negSucc 489160908695711), (Int.negSucc 279922508898887), (Int.negSucc 97378074535817), (Int.negSucc 20521032943175), (Int.ofNat 3748942678368), (Int.ofNat 932142986424)], [(Int.ofNat 0), (Int.negSucc 213463210879), (Int.negSucc 2322819571839), (Int.ofNat 4850988985310), (Int.ofNat 83572185708112), (Int.ofNat 194875966648398), (Int.ofNat 284213373107484), (Int.ofNat 170618198718972), (Int.ofNat 102441768669888), (Int.ofNat 20245950651486), (Int.ofNat 5485344052320), (Int.ofNat 58645188432)], [(Int.ofNat 0), (Int.ofNat 13479122800), (Int.ofNat 351776719256), (Int.negSucc 76095562341), (Int.negSucc 22155651641113), (Int.negSucc 60717990309755), (Int.negSucc 111455655462137), (Int.negSucc 86506026497303), (Int.negSucc 53494484358767), (Int.negSucc 16430860391231), (Int.negSucc 4715625553007), (Int.negSucc 548342948591)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 23249930159), (Int.negSucc 75070029803), (Int.ofNat 4417707805272), (Int.ofNat 15130397333142), (Int.ofNat 28321704055884), (Int.ofNat 33970313358162), (Int.ofNat 18149780989248), (Int.ofNat 8452116458208), (Int.ofNat 1965996956160), (Int.ofNat 227402831160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6908112360), (Int.negSucc 622467849605), (Int.negSucc 3213759124103), (Int.negSucc 4344787502303), (Int.negSucc 9010629245159), (Int.negSucc 4705063463231), (Int.negSucc 2561053408847), (Int.negSucc 499922465327), (Int.negSucc 23130271871)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 46368316728), (Int.ofNat 545195355066), (Int.ofNat 418793075424), (Int.ofNat 1343323319328), (Int.ofNat 969798303360), (Int.ofNat 483272766720), (Int.ofNat 51508851264)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 49944885119), (Int.negSucc 67997488607), (Int.negSucc 40513023071), (Int.negSucc 160487501903), (Int.negSucc 44123501951)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11607554016), (Int.negSucc 11778042167), (Int.ofNat 15744922560)]]

theorem h5n373_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p372).getD 0 []=h5p373.getD 0 [] := by
  decide +kernel

theorem h5n373_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p372).getD 1 []=h5p373.getD 1 [] := by
  decide +kernel

theorem h5n373_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p372).getD 2 []=h5p373.getD 2 [] := by
  decide +kernel

theorem h5n373_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p372).getD 3 []=h5p373.getD 3 [] := by
  decide +kernel

theorem h5n373_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p372).getD 4 []=h5p373.getD 4 [] := by
  decide +kernel

theorem h5n373_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p372).getD 5 []=h5p373.getD 5 [] := by
  decide +kernel

theorem h5n373_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p372).getD 6 []=h5p373.getD 6 [] := by
  decide +kernel

theorem h5n373_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p372).getD 7 []=h5p373.getD 7 [] := by
  decide +kernel

theorem h5n373_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p372).getD 8 []=h5p373.getD 8 [] := by
  decide +kernel

theorem h5n373_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p372).getD 9 []=h5p373.getD 9 [] := by
  decide +kernel

theorem h5n373_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p372).getD 10 []=h5p373.getD 10 [] := by
  decide +kernel

theorem h5n373_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p372).getD 11 []=h5p373.getD 11 [] := by
  decide +kernel

theorem h5n373_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p372).getD 12 []=h5p373.getD 12 [] := by
  decide +kernel

theorem h5n373_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p372).getD 13 []=h5p373.getD 13 [] := by
  decide +kernel

theorem h5n373_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p372).getD 14 []=h5p373.getD 14 [] := by
  decide +kernel

theorem h5n373_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p372).getD 15 []=h5p373.getD 15 [] := by
  decide +kernel

theorem h5n373_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p372).getD 16 []=h5p373.getD 16 [] := by
  decide +kernel

theorem h5n373_arithmetic : BiPoly.mul h5p5 h5p372=h5p373 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p372).getD j.val []=h5p373.getD j.val [] :=
      (fun j => Fin.cases h5n373_arithmetic_row0 (fun j => Fin.cases h5n373_arithmetic_row1 (fun j => Fin.cases h5n373_arithmetic_row2 (fun j => Fin.cases h5n373_arithmetic_row3 (fun j => Fin.cases h5n373_arithmetic_row4 (fun j => Fin.cases h5n373_arithmetic_row5 (fun j => Fin.cases h5n373_arithmetic_row6 (fun j => Fin.cases h5n373_arithmetic_row7 (fun j => Fin.cases h5n373_arithmetic_row8 (fun j => Fin.cases h5n373_arithmetic_row9 (fun j => Fin.cases h5n373_arithmetic_row10 (fun j => Fin.cases h5n373_arithmetic_row11 (fun j => Fin.cases h5n373_arithmetic_row12 (fun j => Fin.cases h5n373_arithmetic_row13 (fun j => Fin.cases h5n373_arithmetic_row14 (fun j => Fin.cases h5n373_arithmetic_row15 (fun j => Fin.cases h5n373_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n373 : h5e373.toBi mapPolyEnv=h5p373 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e372.toBi mapPolyEnv)=h5p373
  rw [h5n5, h5n372]
  exact h5n373_arithmetic

#print axioms h5n373_arithmetic
end StackSorting.RationalLift
