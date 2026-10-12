import BivariateRowEquality
import Horner5Base
import Horner5Node213
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p214 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11149291008000), (Int.ofNat 61847080692480), (Int.negSucc 9003619359359), (Int.negSucc 336302234743679), (Int.negSucc 19595252661119), (Int.ofNat 257005573038720)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 95780152321919), (Int.negSucc 457643345511743), (Int.ofNat 338307392517120), (Int.ofNat 2613267495260928), (Int.negSucc 493289972535167), (Int.negSucc 1773064175940287), (Int.ofNat 198966215130624)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 369635645047680), (Int.ofNat 1490552670790656), (Int.negSucc 2037468969096479), (Int.negSucc 8640438041666879), (Int.ofNat 2790419288542848), (Int.ofNat 4682280898047168), (Int.negSucc 468955259514719), (Int.ofNat 53097091218432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 845057802054239), (Int.negSucc 2795864944370831), (Int.ofNat 5762490056708112), (Int.ofNat 16345396982333088), (Int.negSucc 4176553244693759), (Int.negSucc 6797854421588303), (Int.negSucc 1486493743511087), (Int.ofNat 153535691564352), (Int.ofNat 5478461650944)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1270314945774720), (Int.ofNat 3303420423611616), (Int.negSucc 9593633680868591), (Int.negSucc 20547195870821759), (Int.negSucc 3187888840556063), (Int.ofNat 7701802730954208), (Int.ofNat 6457109939806032), (Int.negSucc 849909722087807), (Int.ofNat 54180705714048), (Int.ofNat 159180982272)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1316912816813759), (Int.negSucc 2496800791512287), (Int.ofNat 10359094289642064), (Int.ofNat 19940066244783648), (Int.ofNat 18645614773742016), (Int.negSucc 7229341633788863), (Int.negSucc 8815245330711887), (Int.negSucc 196612545184703), (Int.ofNat 13818632007744), (Int.ofNat 3678735999744)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 959640640064640), (Int.ofNat 1121604235989696), (Int.negSucc 7716126362364287), (Int.negSucc 17541357678173231), (Int.negSucc 28157498386248383), (Int.ofNat 2410787861856), (Int.ofNat 5816344179313152), (Int.ofNat 3707707561466256), (Int.negSucc 419251434357023), (Int.ofNat 14527863067392)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 491013227479679), (Int.negSucc 178894302174719), (Int.ofNat 4256306428401360), (Int.ofNat 14611231737941760), (Int.ofNat 24177287845008144), (Int.ofNat 12965471494726032), (Int.negSucc 1874160546937343), (Int.negSucc 4620279623533343), (Int.ofNat 83321263391184), (Int.negSucc 4961991645503)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 172707736775040), (Int.negSucc 110036932869887), (Int.negSucc 1940535586989215), (Int.negSucc 10394126792734319), (Int.negSucc 14759967697209215), (Int.negSucc 18993594599237663), (Int.negSucc 2001704648690735), (Int.ofNat 1529394350206896), (Int.ofNat 1076404209640992), (Int.negSucc 72513776779775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 39740770307519), (Int.ofNat 84619103475744), (Int.ofNat 804876778342224), (Int.ofNat 5683206795198624), (Int.ofNat 8186909922003456), (Int.ofNat 13549522844551680), (Int.ofNat 5947100686380096), (Int.ofNat 851006368900224), (Int.negSucc 1037155301046431), (Int.ofNat 8170681175424)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5381253480960), (Int.negSucc 26966981460671), (Int.negSucc 288841968880991), (Int.negSucc 2254822772289263), (Int.negSucc 4586610759343775), (Int.negSucc 5723146710867167), (Int.negSucc 6317797647873599), (Int.negSucc 1314486760043231), (Int.negSucc 14841679748255), (Int.ofNat 129313970902656)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 324743173919), (Int.ofNat 4482254352528), (Int.ofNat 75585843744480), (Int.ofNat 621413960999328), (Int.ofNat 2144402557857360), (Int.ofNat 1870476932069568), (Int.ofNat 3296686534953984), (Int.ofNat 1315836560375424), (Int.ofNat 390147052099392), (Int.negSucc 68937358984703)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 318471012575), (Int.negSucc 11863747999727), (Int.negSucc 111079917908495), (Int.negSucc 676931593377311), (Int.negSucc 730452958212671), (Int.negSucc 850254408290303), (Int.negSucc 886086802678463), (Int.negSucc 213815479876991), (Int.negSucc 35564757391871)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 813146203296), (Int.ofNat 11181129705216), (Int.ofNat 124086697242336), (Int.ofNat 271801892618496), (Int.ofNat 122075234312256), (Int.ofNat 290545783014528), (Int.ofNat 92312551435392), (Int.ofNat 31849292897280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 441037884959), (Int.negSucc 10575393040223), (Int.negSucc 58326431234111), (Int.negSucc 31996811393279), (Int.negSucc 31203884679551), (Int.negSucc 35305918830719), (Int.negSucc 5668172121599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 190055268864), (Int.ofNat 5071550963328), (Int.ofNat 9418025229696), (Int.negSucc 1361320369919), (Int.ofNat 5668172121600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 50869689983), (Int.negSucc 850225818239)]]

theorem h5n214_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p213).getD 0 []=h5p214.getD 0 [] := by
  decide +kernel

theorem h5n214_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p213).getD 1 []=h5p214.getD 1 [] := by
  decide +kernel

theorem h5n214_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p213).getD 2 []=h5p214.getD 2 [] := by
  decide +kernel

theorem h5n214_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p213).getD 3 []=h5p214.getD 3 [] := by
  decide +kernel

theorem h5n214_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p213).getD 4 []=h5p214.getD 4 [] := by
  decide +kernel

theorem h5n214_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p213).getD 5 []=h5p214.getD 5 [] := by
  decide +kernel

theorem h5n214_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p213).getD 6 []=h5p214.getD 6 [] := by
  decide +kernel

theorem h5n214_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p213).getD 7 []=h5p214.getD 7 [] := by
  decide +kernel

theorem h5n214_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p213).getD 8 []=h5p214.getD 8 [] := by
  decide +kernel

theorem h5n214_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p213).getD 9 []=h5p214.getD 9 [] := by
  decide +kernel

theorem h5n214_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p213).getD 10 []=h5p214.getD 10 [] := by
  decide +kernel

theorem h5n214_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p213).getD 11 []=h5p214.getD 11 [] := by
  decide +kernel

theorem h5n214_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p213).getD 12 []=h5p214.getD 12 [] := by
  decide +kernel

theorem h5n214_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p213).getD 13 []=h5p214.getD 13 [] := by
  decide +kernel

theorem h5n214_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p213).getD 14 []=h5p214.getD 14 [] := by
  decide +kernel

theorem h5n214_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p213).getD 15 []=h5p214.getD 15 [] := by
  decide +kernel

theorem h5n214_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p213).getD 16 []=h5p214.getD 16 [] := by
  decide +kernel

theorem h5n214_arithmetic : BiPoly.mul h5p34 h5p213=h5p214 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p213).getD j.val []=h5p214.getD j.val [] :=
      (fun j => Fin.cases h5n214_arithmetic_row0 (fun j => Fin.cases h5n214_arithmetic_row1 (fun j => Fin.cases h5n214_arithmetic_row2 (fun j => Fin.cases h5n214_arithmetic_row3 (fun j => Fin.cases h5n214_arithmetic_row4 (fun j => Fin.cases h5n214_arithmetic_row5 (fun j => Fin.cases h5n214_arithmetic_row6 (fun j => Fin.cases h5n214_arithmetic_row7 (fun j => Fin.cases h5n214_arithmetic_row8 (fun j => Fin.cases h5n214_arithmetic_row9 (fun j => Fin.cases h5n214_arithmetic_row10 (fun j => Fin.cases h5n214_arithmetic_row11 (fun j => Fin.cases h5n214_arithmetic_row12 (fun j => Fin.cases h5n214_arithmetic_row13 (fun j => Fin.cases h5n214_arithmetic_row14 (fun j => Fin.cases h5n214_arithmetic_row15 (fun j => Fin.cases h5n214_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n214 : h5e214.toBi mapPolyEnv=h5p214 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e213.toBi mapPolyEnv)=h5p214
  rw [h5n34, h5n213]
  exact h5n214_arithmetic

#print axioms h5n214_arithmetic
end StackSorting.RationalLift
