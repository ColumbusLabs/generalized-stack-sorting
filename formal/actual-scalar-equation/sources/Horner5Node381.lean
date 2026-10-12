import BivariateRowEquality
import Horner5Base
import Horner5Node380
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p381 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 619405056000), (Int.ofNat 2197138815360), (Int.negSucc 6133288818239), (Int.negSucc 12049967591999), (Int.ofNat 29644799929920), (Int.negSucc 14278087391039)], [(Int.ofNat 0), (Int.negSucc 5321119573439), (Int.negSucc 14782391159327), (Int.ofNat 60240686717376), (Int.ofNat 71779073400000), (Int.negSucc 250999089282431), (Int.ofNat 149167097348832), (Int.negSucc 11053678618367)], [(Int.ofNat 0), (Int.ofNat 20535313613760), (Int.ofNat 41737854483072), (Int.negSucc 247142485733903), (Int.negSucc 155501873243711), (Int.ofNat 857318466920544), (Int.negSucc 559354378439807), (Int.ofNat 54060104011824), (Int.negSucc 2949838401023)], [(Int.ofNat 0), (Int.negSucc 46947655669679), (Int.negSucc 61430518903463), (Int.ofNat 568561883822712), (Int.ofNat 117514411216848), (Int.negSucc 1515376255346495), (Int.ofNat 860313904803576), (Int.ofNat 35128295524152), (Int.negSucc 2021365879199), (Int.negSucc 304358980607)], [(Int.ofNat 0), (Int.ofNat 70573052543040), (Int.ofNat 42377251781232), (Int.negSucc 821108370732407), (Int.ofNat 62290612012032), (Int.ofNat 1434925034842896), (Int.negSucc 56031157610927), (Int.negSucc 650724318576791), (Int.ofNat 69061683782016), (Int.negSucc 2383634469311), (Int.negSucc 8843387903)], [(Int.ofNat 0), (Int.negSucc 73161823156319), (Int.ofNat 7612491228624), (Int.ofNat 785521894108200), (Int.negSucc 115403478528047), (Int.negSucc 627502285080671), (Int.negSucc 1648114251396767), (Int.ofNat 1406311700885496), (Int.negSucc 93763217813087), (Int.ofNat 5625751527264), (Int.negSucc 186687446399)], [(Int.ofNat 0), (Int.ofNat 53313368892480), (Int.negSucc 44315391341087), (Int.negSucc 514075296274079), (Int.negSucc 103945347882215), (Int.ofNat 66352896565440), (Int.ofNat 2323337316225744), (Int.negSucc 907553645641055), (Int.negSucc 271904835176807), (Int.ofNat 25641546804048), (Int.negSucc 398355059327)], [(Int.ofNat 0), (Int.negSucc 27278512637759), (Int.ofNat 44618452932480), (Int.ofNat 241002671066760), (Int.ofNat 347498106772416), (Int.negSucc 134431924819847), (Int.negSucc 1293854309545559), (Int.negSucc 760985705276207), (Int.ofNat 776795410130736), (Int.negSucc 54583449759239), (Int.ofNat 1889873210016)], [(Int.ofNat 0), (Int.ofNat 9594874265280), (Int.negSucc 25302911467775), (Int.negSucc 91727400069359), (Int.negSucc 369230609096231), (Int.ofNat 272539502409744), (Int.ofNat 164466037670352), (Int.ofNat 1563270117438792), (Int.negSucc 541860400166039), (Int.negSucc 55882530205631), (Int.ofNat 3477210749376)], [(Int.ofNat 0), (Int.negSucc 2207820572639), (Int.ofNat 9116702449488), (Int.ofNat 34751419487592), (Int.ofNat 228872728950192), (Int.negSucc 152143379954591), (Int.ofNat 29735646923136), (Int.negSucc 888015902148575), (Int.negSucc 244338829410143), (Int.ofNat 193690900361520), (Int.negSucc 8511013040831)], [(Int.ofNat 0), (Int.ofNat 298958526720), (Int.negSucc 2096082690143), (Int.negSucc 13014362200655), (Int.negSucc 93637022289287), (Int.negSucc 11411042035343), (Int.ofNat 134911191621360), (Int.ofNat 119144798769888), (Int.ofNat 527988921358320), (Int.negSucc 109919514377807), (Int.negSucc 6276256030655)], [(Int.ofNat 0), (Int.negSucc 18041287439), (Int.ofNat 285096705576), (Int.ofNat 3701185279968), (Int.ofNat 26159956418640), (Int.ofNat 51315324413976), (Int.negSucc 123293045770847), (Int.ofNat 36755279486496), (Int.negSucc 247764053143871), (Int.negSucc 58812202823615), (Int.ofNat 18198072266112)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17692834031), (Int.negSucc 623711443031), (Int.negSucc 4852912328279), (Int.negSucc 25355447220383), (Int.ofNat 33440558050080), (Int.ofNat 21340603609056), (Int.ofNat 22101127421760), (Int.ofNat 80964302613120), (Int.negSucc 5683886698751)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 45174789072), (Int.ofNat 530824294368), (Int.ofNat 5651357657328), (Int.ofNat 1361698550208), (Int.negSucc 22264326410111), (Int.ofNat 8479261320768), (Int.negSucc 25103367433151), (Int.negSucc 5721044871167)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 24502104719), (Int.negSucc 538517626127), (Int.negSucc 2065313619647), (Int.ofNat 4681996696512), (Int.ofNat 1263798642240), (Int.ofNat 559332838080), (Int.ofNat 3853708773120)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10558626048), (Int.ofNat 260635579200), (Int.negSucc 40282038719), (Int.negSucc 1116423969407), (Int.ofNat 560625805440), (Int.negSucc 629796902399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2826093887), (Int.negSucc 41582579903), (Int.ofNat 94469535360)]]

theorem h5n381_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p380).getD 0 []=h5p381.getD 0 [] := by
  decide +kernel

theorem h5n381_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p380).getD 1 []=h5p381.getD 1 [] := by
  decide +kernel

theorem h5n381_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p380).getD 2 []=h5p381.getD 2 [] := by
  decide +kernel

theorem h5n381_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p380).getD 3 []=h5p381.getD 3 [] := by
  decide +kernel

theorem h5n381_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p380).getD 4 []=h5p381.getD 4 [] := by
  decide +kernel

theorem h5n381_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p380).getD 5 []=h5p381.getD 5 [] := by
  decide +kernel

theorem h5n381_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p380).getD 6 []=h5p381.getD 6 [] := by
  decide +kernel

theorem h5n381_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p380).getD 7 []=h5p381.getD 7 [] := by
  decide +kernel

theorem h5n381_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p380).getD 8 []=h5p381.getD 8 [] := by
  decide +kernel

theorem h5n381_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p380).getD 9 []=h5p381.getD 9 [] := by
  decide +kernel

theorem h5n381_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p380).getD 10 []=h5p381.getD 10 [] := by
  decide +kernel

theorem h5n381_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p380).getD 11 []=h5p381.getD 11 [] := by
  decide +kernel

theorem h5n381_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p380).getD 12 []=h5p381.getD 12 [] := by
  decide +kernel

theorem h5n381_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p380).getD 13 []=h5p381.getD 13 [] := by
  decide +kernel

theorem h5n381_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p380).getD 14 []=h5p381.getD 14 [] := by
  decide +kernel

theorem h5n381_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p380).getD 15 []=h5p381.getD 15 [] := by
  decide +kernel

theorem h5n381_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p380).getD 16 []=h5p381.getD 16 [] := by
  decide +kernel

theorem h5n381_arithmetic : BiPoly.mul h5p34 h5p380=h5p381 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p380).getD j.val []=h5p381.getD j.val [] :=
      (fun j => Fin.cases h5n381_arithmetic_row0 (fun j => Fin.cases h5n381_arithmetic_row1 (fun j => Fin.cases h5n381_arithmetic_row2 (fun j => Fin.cases h5n381_arithmetic_row3 (fun j => Fin.cases h5n381_arithmetic_row4 (fun j => Fin.cases h5n381_arithmetic_row5 (fun j => Fin.cases h5n381_arithmetic_row6 (fun j => Fin.cases h5n381_arithmetic_row7 (fun j => Fin.cases h5n381_arithmetic_row8 (fun j => Fin.cases h5n381_arithmetic_row9 (fun j => Fin.cases h5n381_arithmetic_row10 (fun j => Fin.cases h5n381_arithmetic_row11 (fun j => Fin.cases h5n381_arithmetic_row12 (fun j => Fin.cases h5n381_arithmetic_row13 (fun j => Fin.cases h5n381_arithmetic_row14 (fun j => Fin.cases h5n381_arithmetic_row15 (fun j => Fin.cases h5n381_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n381 : h5e381.toBi mapPolyEnv=h5p381 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e380.toBi mapPolyEnv)=h5p381
  rw [h5n34, h5n380]
  exact h5n381_arithmetic

#print axioms h5n381_arithmetic
end StackSorting.RationalLift
