import BivariateRowEquality
import Horner2Base
import Horner2Node084
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p85 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 306025347023), (Int.negSucc 3542854281263), (Int.negSucc 7958138542703), (Int.ofNat 7980287638896), (Int.ofNat 12701597247360)], [(Int.ofNat 0), (Int.ofNat 2520221528808), (Int.ofNat 29176243239312), (Int.ofNat 65607908145840), (Int.negSucc 61196413723631), (Int.negSucc 72956911470263), (Int.ofNat 890904979008)], [(Int.ofNat 0), (Int.negSucc 9712849893263), (Int.negSucc 110013730666703), (Int.negSucc 235687730026463), (Int.ofNat 203877565846128), (Int.ofNat 175518308823264), (Int.ofNat 29133604158480), (Int.negSucc 2451096565631)], [(Int.ofNat 0), (Int.ofNat 23156884620288), (Int.ofNat 250886126356656), (Int.ofNat 487025820913680), (Int.negSucc 330183318039791), (Int.negSucc 227983368485327), (Int.negSucc 157877742348911), (Int.ofNat 14460304408032), (Int.negSucc 468761449727)], [(Int.ofNat 0), (Int.negSucc 37832216926131), (Int.negSucc 385847818110339), (Int.negSucc 649820998266983), (Int.ofNat 147883719384968), (Int.ofNat 217195094729500), (Int.ofNat 310834149575884), (Int.negSucc 3193147767519), (Int.negSucc 188121806399), (Int.ofNat 2397232640)], [(Int.ofNat 0), (Int.ofNat 44190131917728), (Int.ofNat 423651535092764), (Int.ofNat 610251833188472), (Int.ofNat 370656916015752), (Int.negSucc 212932405167415), (Int.negSucc 241949601146131), (Int.negSucc 86739888409303), (Int.ofNat 6311204339584), (Int.negSucc 86439491071)], [(Int.ofNat 0), (Int.negSucc 37387499810267), (Int.negSucc 343848748432711), (Int.negSucc 452671743831031), (Int.negSucc 746069261955191), (Int.ofNat 87940174398620), (Int.negSucc 4048341299679), (Int.ofNat 168036407517304), (Int.negSucc 2965685383615), (Int.negSucc 177885621247)], [(Int.ofNat 0), (Int.ofNat 22790986001928), (Int.ofNat 210943248681244), (Int.ofNat 306440971812396), (Int.ofNat 645273336592896), (Int.ofNat 215548403780688), (Int.ofNat 105650600176628), (Int.negSucc 86571201552787), (Int.negSucc 20268346772399), (Int.ofNat 685262958464)], [(Int.ofNat 0), (Int.negSucc 9804621730347), (Int.negSucc 98858759159695), (Int.negSucc 197556487934835), (Int.negSucc 320716721085811), (Int.negSucc 386284355447079), (Int.negSucc 72540358543859), (Int.negSucc 51270494350059), (Int.ofNat 28113067383428), (Int.ofNat 808231380768)], [(Int.ofNat 0), (Int.ofNat 2860775462088), (Int.ofNat 35211820568660), (Int.ofNat 108168486172308), (Int.ofNat 109163304506328), (Int.ofNat 269720970393232), (Int.ofNat 76658601532592), (Int.ofNat 70021831716212), (Int.negSucc 3495791671887), (Int.negSucc 1657143086975)], [(Int.ofNat 0), (Int.negSucc 526767524371), (Int.negSucc 9287320559783), (Int.negSucc 44200947171727), (Int.negSucc 39253877527759), (Int.negSucc 91733680829943), (Int.negSucc 76209451749367), (Int.negSucc 29125593386159), (Int.negSucc 12218469574943), (Int.negSucc 104258112767)], [(Int.ofNat 0), (Int.ofNat 52981118248), (Int.ofNat 1721881383588), (Int.ofNat 12423518373204), (Int.ofNat 17501786856416), (Int.ofNat 13922544328248), (Int.ofNat 36575185410480), (Int.ofNat 10566597021216), (Int.ofNat 7301225956320), (Int.ofNat 974831908608)], [(Int.ofNat 0), (Int.negSucc 1999417679), (Int.negSucc 203497819643), (Int.negSucc 2249199390443), (Int.negSucc 6001487012939), (Int.negSucc 937042666175), (Int.negSucc 7519056638255), (Int.negSucc 4525526955311), (Int.negSucc 1826144596079), (Int.negSucc 404271699839)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11873707920), (Int.ofNat 238298728788), (Int.ofNat 1195783596288), (Int.ofNat 418774534416), (Int.ofNat 317431271808), (Int.ofNat 1027251298800), (Int.ofNat 341956225152), (Int.ofNat 41120483328)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 11592170495), (Int.negSucc 114392680703), (Int.negSucc 159582108527), (Int.ofNat 100528849008), (Int.negSucc 75176491391), (Int.negSucc 41120483327)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2649236544), (Int.ofNat 19533499920), (Int.negSucc 13283139455)]]

theorem h2n85_arithmetic_row0 :
    (BiPoly.mul h2p4 h2p84).getD 0 []=h2p85.getD 0 [] := by
  decide +kernel

theorem h2n85_arithmetic_row1 :
    (BiPoly.mul h2p4 h2p84).getD 1 []=h2p85.getD 1 [] := by
  decide +kernel

theorem h2n85_arithmetic_row2 :
    (BiPoly.mul h2p4 h2p84).getD 2 []=h2p85.getD 2 [] := by
  decide +kernel

theorem h2n85_arithmetic_row3 :
    (BiPoly.mul h2p4 h2p84).getD 3 []=h2p85.getD 3 [] := by
  decide +kernel

theorem h2n85_arithmetic_row4 :
    (BiPoly.mul h2p4 h2p84).getD 4 []=h2p85.getD 4 [] := by
  decide +kernel

theorem h2n85_arithmetic_row5 :
    (BiPoly.mul h2p4 h2p84).getD 5 []=h2p85.getD 5 [] := by
  decide +kernel

theorem h2n85_arithmetic_row6 :
    (BiPoly.mul h2p4 h2p84).getD 6 []=h2p85.getD 6 [] := by
  decide +kernel

theorem h2n85_arithmetic_row7 :
    (BiPoly.mul h2p4 h2p84).getD 7 []=h2p85.getD 7 [] := by
  decide +kernel

theorem h2n85_arithmetic_row8 :
    (BiPoly.mul h2p4 h2p84).getD 8 []=h2p85.getD 8 [] := by
  decide +kernel

theorem h2n85_arithmetic_row9 :
    (BiPoly.mul h2p4 h2p84).getD 9 []=h2p85.getD 9 [] := by
  decide +kernel

theorem h2n85_arithmetic_row10 :
    (BiPoly.mul h2p4 h2p84).getD 10 []=h2p85.getD 10 [] := by
  decide +kernel

theorem h2n85_arithmetic_row11 :
    (BiPoly.mul h2p4 h2p84).getD 11 []=h2p85.getD 11 [] := by
  decide +kernel

theorem h2n85_arithmetic_row12 :
    (BiPoly.mul h2p4 h2p84).getD 12 []=h2p85.getD 12 [] := by
  decide +kernel

theorem h2n85_arithmetic_row13 :
    (BiPoly.mul h2p4 h2p84).getD 13 []=h2p85.getD 13 [] := by
  decide +kernel

theorem h2n85_arithmetic_row14 :
    (BiPoly.mul h2p4 h2p84).getD 14 []=h2p85.getD 14 [] := by
  decide +kernel

theorem h2n85_arithmetic_row15 :
    (BiPoly.mul h2p4 h2p84).getD 15 []=h2p85.getD 15 [] := by
  decide +kernel

theorem h2n85_arithmetic : BiPoly.mul h2p4 h2p84=h2p85 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h2p4 h2p84).getD j.val []=h2p85.getD j.val [] :=
      (fun j => Fin.cases h2n85_arithmetic_row0 (fun j => Fin.cases h2n85_arithmetic_row1 (fun j => Fin.cases h2n85_arithmetic_row2 (fun j => Fin.cases h2n85_arithmetic_row3 (fun j => Fin.cases h2n85_arithmetic_row4 (fun j => Fin.cases h2n85_arithmetic_row5 (fun j => Fin.cases h2n85_arithmetic_row6 (fun j => Fin.cases h2n85_arithmetic_row7 (fun j => Fin.cases h2n85_arithmetic_row8 (fun j => Fin.cases h2n85_arithmetic_row9 (fun j => Fin.cases h2n85_arithmetic_row10 (fun j => Fin.cases h2n85_arithmetic_row11 (fun j => Fin.cases h2n85_arithmetic_row12 (fun j => Fin.cases h2n85_arithmetic_row13 (fun j => Fin.cases h2n85_arithmetic_row14 (fun j => Fin.cases h2n85_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n85 : h2e85.toBi mapPolyEnv=h2p85 := by
  change BiPoly.mul (h2e4.toBi mapPolyEnv) (h2e84.toBi mapPolyEnv)=h2p85
  rw [h2n4, h2n84]
  exact h2n85_arithmetic

#print axioms h2n85_arithmetic
end StackSorting.RationalLift
