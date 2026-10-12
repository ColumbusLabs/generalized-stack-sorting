import BivariateRowEquality
import Horner5Base
import Horner5Node391
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p392 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 619405055999), (Int.negSucc 3435948927359), (Int.ofNat 500201075520), (Int.ofNat 18683457485760), (Int.ofNat 1088625147840), (Int.negSucc 14278087391039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5321119573440), (Int.ofNat 25424630306208), (Int.negSucc 18794855139839), (Int.negSucc 145181527514495), (Int.ofNat 27404998474176), (Int.ofNat 98503565330016), (Int.negSucc 11053678618367)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 20535313613759), (Int.negSucc 82808481710591), (Int.ofNat 113192720505360), (Int.ofNat 480024335648160), (Int.negSucc 155023293807935), (Int.negSucc 260126716558175), (Int.ofNat 26053069973040), (Int.negSucc 2949838401023)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 46947655669680), (Int.ofNat 155325830242824), (Int.negSucc 320138336483783), (Int.negSucc 908077610129615), (Int.ofNat 232030735816320), (Int.ofNat 377658578977128), (Int.ofNat 82582985750616), (Int.negSucc 8529760642463), (Int.negSucc 304358980607)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 70573052543039), (Int.negSucc 183523356867311), (Int.ofNat 532979648937144), (Int.ofNat 1141510881712320), (Int.ofNat 177104935586448), (Int.negSucc 427877929497455), (Int.negSucc 358728329989223), (Int.ofNat 47217206782656), (Int.negSucc 3010039206335), (Int.negSucc 8843387903)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 73161823156320), (Int.ofNat 138711155084016), (Int.negSucc 575505238313447), (Int.negSucc 1107781458043535), (Int.negSucc 1035867487430111), (Int.ofNat 401630090766048), (Int.ofNat 489735851706216), (Int.ofNat 10922919176928), (Int.negSucc 767701778207), (Int.negSucc 204374222207)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 53313368892479), (Int.negSucc 62311346443871), (Int.ofNat 428673686798016), (Int.ofNat 974519871009624), (Int.ofNat 1564305465902688), (Int.negSucc 133932658991), (Int.negSucc 323130232184063), (Int.negSucc 205983753414791), (Int.ofNat 23291746353168), (Int.negSucc 807103503743)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 27278512637760), (Int.ofNat 9938572343040), (Int.negSucc 236461468244519), (Int.negSucc 811735096552319), (Int.negSucc 1343182658056007), (Int.negSucc 720303971929223), (Int.ofNat 104120030385408), (Int.ofNat 256682201307408), (Int.negSucc 4628959077287), (Int.ofNat 275666202528)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9594874265279), (Int.ofNat 6113162937216), (Int.ofNat 107807532610512), (Int.ofNat 577451488485240), (Int.ofNat 819998205400512), (Int.ofNat 1055199699957648), (Int.ofNat 111205813816152), (Int.negSucc 84966352789271), (Int.negSucc 59800233868943), (Int.ofNat 4028543154432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2207820572640), (Int.negSucc 4701061304207), (Int.negSucc 44715376574567), (Int.negSucc 315733710844367), (Int.negSucc 454828329000191), (Int.negSucc 752751269141759), (Int.negSucc 330394482576671), (Int.negSucc 47278131605567), (Int.ofNat 57619738947024), (Int.negSucc 453926731967)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 298958526719), (Int.ofNat 1498165636704), (Int.ofNat 16046776048944), (Int.ofNat 125267931793848), (Int.ofNat 254811708852432), (Int.ofNat 317952595048176), (Int.ofNat 350988758215200), (Int.ofNat 73027042224624), (Int.ofNat 824537763792), (Int.negSucc 7184109494591)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 18041287440), (Int.negSucc 249014130695), (Int.negSucc 4199213541359), (Int.negSucc 34522997833295), (Int.negSucc 119133475436519), (Int.negSucc 103915385114975), (Int.negSucc 183149251941887), (Int.negSucc 73102031131967), (Int.negSucc 21674836227743), (Int.ofNat 3829853276928)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 17692834032), (Int.ofNat 659097111096), (Int.ofNat 6171106550472), (Int.ofNat 37607310743184), (Int.ofNat 40580719900704), (Int.ofNat 47236356016128), (Int.ofNat 49227044593248), (Int.ofNat 11878637770944), (Int.ofNat 1975819855104)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 45174789071), (Int.negSucc 621173872511), (Int.negSucc 6893705402351), (Int.negSucc 15100105145471), (Int.negSucc 6781957461791), (Int.negSucc 16141432389695), (Int.negSucc 5128475079743), (Int.negSucc 1769405160959)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 24502104720), (Int.ofNat 587521835568), (Int.ofNat 3240357290784), (Int.ofNat 1777600632960), (Int.ofNat 1733549148864), (Int.ofNat 1961439935040), (Int.ofNat 314898451200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10558626047), (Int.negSucc 281752831295), (Int.negSucc 523223623871), (Int.ofNat 75628909440), (Int.negSucc 314898451199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2826093888), (Int.ofNat 47234767680)]]

theorem h5n392_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p391).getD 0 []=h5p392.getD 0 [] := by
  decide +kernel

theorem h5n392_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p391).getD 1 []=h5p392.getD 1 [] := by
  decide +kernel

theorem h5n392_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p391).getD 2 []=h5p392.getD 2 [] := by
  decide +kernel

theorem h5n392_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p391).getD 3 []=h5p392.getD 3 [] := by
  decide +kernel

theorem h5n392_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p391).getD 4 []=h5p392.getD 4 [] := by
  decide +kernel

theorem h5n392_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p391).getD 5 []=h5p392.getD 5 [] := by
  decide +kernel

theorem h5n392_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p391).getD 6 []=h5p392.getD 6 [] := by
  decide +kernel

theorem h5n392_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p391).getD 7 []=h5p392.getD 7 [] := by
  decide +kernel

theorem h5n392_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p391).getD 8 []=h5p392.getD 8 [] := by
  decide +kernel

theorem h5n392_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p391).getD 9 []=h5p392.getD 9 [] := by
  decide +kernel

theorem h5n392_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p391).getD 10 []=h5p392.getD 10 [] := by
  decide +kernel

theorem h5n392_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p391).getD 11 []=h5p392.getD 11 [] := by
  decide +kernel

theorem h5n392_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p391).getD 12 []=h5p392.getD 12 [] := by
  decide +kernel

theorem h5n392_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p391).getD 13 []=h5p392.getD 13 [] := by
  decide +kernel

theorem h5n392_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p391).getD 14 []=h5p392.getD 14 [] := by
  decide +kernel

theorem h5n392_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p391).getD 15 []=h5p392.getD 15 [] := by
  decide +kernel

theorem h5n392_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p391).getD 16 []=h5p392.getD 16 [] := by
  decide +kernel

theorem h5n392_arithmetic : BiPoly.mul h5p34 h5p391=h5p392 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p391).getD j.val []=h5p392.getD j.val [] :=
      (fun j => Fin.cases h5n392_arithmetic_row0 (fun j => Fin.cases h5n392_arithmetic_row1 (fun j => Fin.cases h5n392_arithmetic_row2 (fun j => Fin.cases h5n392_arithmetic_row3 (fun j => Fin.cases h5n392_arithmetic_row4 (fun j => Fin.cases h5n392_arithmetic_row5 (fun j => Fin.cases h5n392_arithmetic_row6 (fun j => Fin.cases h5n392_arithmetic_row7 (fun j => Fin.cases h5n392_arithmetic_row8 (fun j => Fin.cases h5n392_arithmetic_row9 (fun j => Fin.cases h5n392_arithmetic_row10 (fun j => Fin.cases h5n392_arithmetic_row11 (fun j => Fin.cases h5n392_arithmetic_row12 (fun j => Fin.cases h5n392_arithmetic_row13 (fun j => Fin.cases h5n392_arithmetic_row14 (fun j => Fin.cases h5n392_arithmetic_row15 (fun j => Fin.cases h5n392_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n392 : h5e392.toBi mapPolyEnv=h5p392 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e391.toBi mapPolyEnv)=h5p392
  rw [h5n34, h5n391]
  exact h5n392_arithmetic

#print axioms h5n392_arithmetic
end StackSorting.RationalLift
