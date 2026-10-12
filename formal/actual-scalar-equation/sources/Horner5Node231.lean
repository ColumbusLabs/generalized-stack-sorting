import BivariateRowEquality
import Horner5Base
import Horner5Node230
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p231 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 11149291007999), (Int.negSucc 61847080692479), (Int.ofNat 9003619359360), (Int.ofNat 336302234743680), (Int.ofNat 19595252661120), (Int.negSucc 257005573038719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 95780152321920), (Int.ofNat 457643345511744), (Int.negSucc 338307392517119), (Int.negSucc 2613267495260927), (Int.ofNat 493289972535168), (Int.ofNat 1773064175940288), (Int.negSucc 198966215130623)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 369635645047679), (Int.negSucc 1490552670790655), (Int.ofNat 2037468969096480), (Int.ofNat 8640438041666880), (Int.negSucc 2790419288542847), (Int.negSucc 4682280898047167), (Int.ofNat 468955259514720), (Int.negSucc 53097091218431)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 845057802054240), (Int.ofNat 2795864944370832), (Int.negSucc 5762490056708111), (Int.negSucc 16345396982333087), (Int.ofNat 4176553244693760), (Int.ofNat 6797854421588304), (Int.ofNat 1486493743511088), (Int.negSucc 153535691564351), (Int.negSucc 5478461650943)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1270314945774719), (Int.negSucc 3303420423611615), (Int.ofNat 9593633680868592), (Int.ofNat 20547195870821760), (Int.ofNat 3187888840556064), (Int.negSucc 7701802730954207), (Int.negSucc 6457109939806031), (Int.ofNat 849909722087808), (Int.negSucc 54180705714047), (Int.negSucc 159180982271)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1316912816813760), (Int.ofNat 2496800791512288), (Int.negSucc 10359094289642063), (Int.negSucc 19940066244783647), (Int.negSucc 18645614773742015), (Int.ofNat 7229341633788864), (Int.ofNat 8815245330711888), (Int.ofNat 196612545184704), (Int.negSucc 13818632007743), (Int.negSucc 3678735999743)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 959640640064639), (Int.negSucc 1121604235989695), (Int.ofNat 7716126362364288), (Int.ofNat 17541357678173232), (Int.ofNat 28157498386248384), (Int.negSucc 2410787861855), (Int.negSucc 5816344179313151), (Int.negSucc 3707707561466255), (Int.ofNat 419251434357024), (Int.negSucc 14527863067391)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 491013227479680), (Int.ofNat 178894302174720), (Int.negSucc 4256306428401359), (Int.negSucc 14611231737941759), (Int.negSucc 24177287845008143), (Int.negSucc 12965471494726031), (Int.ofNat 1874160546937344), (Int.ofNat 4620279623533344), (Int.negSucc 83321263391183), (Int.ofNat 4961991645504)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 172707736775039), (Int.ofNat 110036932869888), (Int.ofNat 1940535586989216), (Int.ofNat 10394126792734320), (Int.ofNat 14759967697209216), (Int.ofNat 18993594599237664), (Int.ofNat 2001704648690736), (Int.negSucc 1529394350206895), (Int.negSucc 1076404209640991), (Int.ofNat 72513776779776)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 39740770307520), (Int.negSucc 84619103475743), (Int.negSucc 804876778342223), (Int.negSucc 5683206795198623), (Int.negSucc 8186909922003455), (Int.negSucc 13549522844551679), (Int.negSucc 5947100686380095), (Int.negSucc 851006368900223), (Int.ofNat 1037155301046432), (Int.negSucc 8170681175423)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5381253480959), (Int.ofNat 26966981460672), (Int.ofNat 288841968880992), (Int.ofNat 2254822772289264), (Int.ofNat 4586610759343776), (Int.ofNat 5723146710867168), (Int.ofNat 6317797647873600), (Int.ofNat 1314486760043232), (Int.ofNat 14841679748256), (Int.negSucc 129313970902655)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 324743173920), (Int.negSucc 4482254352527), (Int.negSucc 75585843744479), (Int.negSucc 621413960999327), (Int.negSucc 2144402557857359), (Int.negSucc 1870476932069567), (Int.negSucc 3296686534953983), (Int.negSucc 1315836560375423), (Int.negSucc 390147052099391), (Int.ofNat 68937358984704)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 318471012576), (Int.ofNat 11863747999728), (Int.ofNat 111079917908496), (Int.ofNat 676931593377312), (Int.ofNat 730452958212672), (Int.ofNat 850254408290304), (Int.ofNat 886086802678464), (Int.ofNat 213815479876992), (Int.ofNat 35564757391872)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 813146203295), (Int.negSucc 11181129705215), (Int.negSucc 124086697242335), (Int.negSucc 271801892618495), (Int.negSucc 122075234312255), (Int.negSucc 290545783014527), (Int.negSucc 92312551435391), (Int.negSucc 31849292897279)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 441037884960), (Int.ofNat 10575393040224), (Int.ofNat 58326431234112), (Int.ofNat 31996811393280), (Int.ofNat 31203884679552), (Int.ofNat 35305918830720), (Int.ofNat 5668172121600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 190055268863), (Int.negSucc 5071550963327), (Int.negSucc 9418025229695), (Int.ofNat 1361320369920), (Int.negSucc 5668172121599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 50869689984), (Int.ofNat 850225818240)]]

theorem h5n231_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p230).getD 0 []=h5p231.getD 0 [] := by
  decide +kernel

theorem h5n231_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p230).getD 1 []=h5p231.getD 1 [] := by
  decide +kernel

theorem h5n231_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p230).getD 2 []=h5p231.getD 2 [] := by
  decide +kernel

theorem h5n231_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p230).getD 3 []=h5p231.getD 3 [] := by
  decide +kernel

theorem h5n231_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p230).getD 4 []=h5p231.getD 4 [] := by
  decide +kernel

theorem h5n231_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p230).getD 5 []=h5p231.getD 5 [] := by
  decide +kernel

theorem h5n231_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p230).getD 6 []=h5p231.getD 6 [] := by
  decide +kernel

theorem h5n231_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p230).getD 7 []=h5p231.getD 7 [] := by
  decide +kernel

theorem h5n231_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p230).getD 8 []=h5p231.getD 8 [] := by
  decide +kernel

theorem h5n231_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p230).getD 9 []=h5p231.getD 9 [] := by
  decide +kernel

theorem h5n231_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p230).getD 10 []=h5p231.getD 10 [] := by
  decide +kernel

theorem h5n231_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p230).getD 11 []=h5p231.getD 11 [] := by
  decide +kernel

theorem h5n231_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p230).getD 12 []=h5p231.getD 12 [] := by
  decide +kernel

theorem h5n231_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p230).getD 13 []=h5p231.getD 13 [] := by
  decide +kernel

theorem h5n231_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p230).getD 14 []=h5p231.getD 14 [] := by
  decide +kernel

theorem h5n231_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p230).getD 15 []=h5p231.getD 15 [] := by
  decide +kernel

theorem h5n231_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p230).getD 16 []=h5p231.getD 16 [] := by
  decide +kernel

theorem h5n231_arithmetic : BiPoly.mul h5p34 h5p230=h5p231 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p230).getD j.val []=h5p231.getD j.val [] :=
      (fun j => Fin.cases h5n231_arithmetic_row0 (fun j => Fin.cases h5n231_arithmetic_row1 (fun j => Fin.cases h5n231_arithmetic_row2 (fun j => Fin.cases h5n231_arithmetic_row3 (fun j => Fin.cases h5n231_arithmetic_row4 (fun j => Fin.cases h5n231_arithmetic_row5 (fun j => Fin.cases h5n231_arithmetic_row6 (fun j => Fin.cases h5n231_arithmetic_row7 (fun j => Fin.cases h5n231_arithmetic_row8 (fun j => Fin.cases h5n231_arithmetic_row9 (fun j => Fin.cases h5n231_arithmetic_row10 (fun j => Fin.cases h5n231_arithmetic_row11 (fun j => Fin.cases h5n231_arithmetic_row12 (fun j => Fin.cases h5n231_arithmetic_row13 (fun j => Fin.cases h5n231_arithmetic_row14 (fun j => Fin.cases h5n231_arithmetic_row15 (fun j => Fin.cases h5n231_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n231 : h5e231.toBi mapPolyEnv=h5p231 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e230.toBi mapPolyEnv)=h5p231
  rw [h5n34, h5n230]
  exact h5n231_arithmetic

#print axioms h5n231_arithmetic
end StackSorting.RationalLift
