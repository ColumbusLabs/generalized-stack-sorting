import BivariateRowEquality
import Horner5Base
import Horner5Node172
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p173 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 522623015999), (Int.negSucc 3127729476959), (Int.negSucc 5421296563199), (Int.negSucc 3752971781759), (Int.ofNat 4677417731520), (Int.ofNat 5614199411040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4548368751840), (Int.ofNat 25276878355248), (Int.ofNat 37704204597456), (Int.ofNat 20670333782112), (Int.negSucc 38040057848447), (Int.negSucc 29791597680143), (Int.ofNat 1385823133008)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17809809493679), (Int.negSucc 92974534752455), (Int.negSucc 124207262013095), (Int.negSucc 64456635354623), (Int.ofNat 113979173305968), (Int.ofNat 67799732168232), (Int.ofNat 10430594392680), (Int.negSucc 1009063860767)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 41385867838920), (Int.ofNat 206731857102372), (Int.ofNat 267828069044952), (Int.ofNat 164291276313468), (Int.negSucc 161216716180967), (Int.negSucc 111156294697523), (Int.negSucc 66664983739031), (Int.ofNat 8334853735284), (Int.negSucc 398224880063)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 63366463501199), (Int.negSucc 311231134168127), (Int.negSucc 436775994434987), (Int.negSucc 340302994973171), (Int.ofNat 66355203351960), (Int.ofNat 164521163170008), (Int.ofNat 127633237452036), (Int.negSucc 3860140180211), (Int.ofNat 333869783184), (Int.negSucc 36478975103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 67071420983520), (Int.ofNat 336243102416640), (Int.ofNat 568496366419212), (Int.ofNat 535254182764812), (Int.ofNat 175520173853448), (Int.negSucc 165765032132183), (Int.negSucc 116485042042403), (Int.negSucc 46579441969187), (Int.ofNat 5362912484352), (Int.negSucc 139994328239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 50042710260239), (Int.negSucc 268645003838711), (Int.negSucc 586096217620871), (Int.negSucc 639817580538443), (Int.negSucc 425811465232067), (Int.ofNat 29763194886000), (Int.ofNat 62501249019744), (Int.ofNat 87744369481932), (Int.negSucc 5318933508011), (Int.ofNat 273509433360)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 26301863963280), (Int.ofNat 160269417734616), (Int.ofNat 463862923271868), (Int.ofNat 600215956741764), (Int.ofNat 529532150206812), (Int.ofNat 176042282789808), (Int.negSucc 14580870672299), (Int.negSucc 50038317929447), (Int.negSucc 15540798446267), (Int.ofNat 1103992163748)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9538604470319), (Int.negSucc 70707977352791), (Int.negSucc 272740269717239), (Int.negSucc 448344397909355), (Int.negSucc 456494939008835), (Int.negSucc 286384296397943), (Int.negSucc 43483880059067), (Int.negSucc 7315905893327), (Int.ofNat 25130975519964), (Int.negSucc 953566395047)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2272665336000), (Int.ofNat 22356467682768), (Int.ofNat 115165084408620), (Int.ofNat 260300295457836), (Int.ofNat 299412053046840), (Int.ofNat 248651615820048), (Int.ofNat 91705823155680), (Int.ofNat 24021489212592), (Int.negSucc 6177813855095), (Int.negSucc 2305370691575)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 320194816319), (Int.negSucc 4765008623039), (Int.negSucc 33368686907519), (Int.negSucc 111173026505099), (Int.negSucc 155619434977691), (Int.negSucc 146260458125831), (Int.negSucc 87410742210599), (Int.negSucc 22245281725895), (Int.negSucc 7861830368399), (Int.ofNat 2280224866680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 20218684200), (Int.ofNat 608539815684), (Int.ofNat 6152444520108), (Int.ofNat 32386325057280), (Int.ofNat 62864192099940), (Int.ofNat 64256080010724), (Int.ofNat 49123318155120), (Int.ofNat 18373583874528), (Int.ofNat 6055128265536), (Int.ofNat 316083078576)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 34874895239), (Int.negSucc 623223243179), (Int.negSucc 5767688434895), (Int.negSucc 18109365526979), (Int.negSucc 22175064845927), (Int.negSucc 18216185319935), (Int.negSucc 10189779623999), (Int.negSucc 2482089169103), (Int.negSucc 861615877535)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 23858237880), (Int.ofNat 507520433448), (Int.ofNat 3218455878696), (Int.ofNat 5776520250024), (Int.ofNat 4953293184096), (Int.ofNat 3249758336976), (Int.ofNat 1026776938176), (Int.ofNat 269686213344)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10595053367), (Int.negSucc 270170523359), (Int.negSucc 967382547479), (Int.negSucc 1034139020399), (Int.negSucc 622096802207), (Int.negSucc 290142513215), (Int.negSucc 23617383839)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3329823168), (Int.ofNat 75378794400), (Int.ofNat 141893176896), (Int.ofNat 86531159520), (Int.ofNat 31489845120)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 471015647), (Int.negSucc 8343476927), (Int.negSucc 7872461279)]]

theorem h5n173_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p172).getD 0 []=h5p173.getD 0 [] := by
  decide +kernel

theorem h5n173_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p172).getD 1 []=h5p173.getD 1 [] := by
  decide +kernel

theorem h5n173_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p172).getD 2 []=h5p173.getD 2 [] := by
  decide +kernel

theorem h5n173_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p172).getD 3 []=h5p173.getD 3 [] := by
  decide +kernel

theorem h5n173_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p172).getD 4 []=h5p173.getD 4 [] := by
  decide +kernel

theorem h5n173_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p172).getD 5 []=h5p173.getD 5 [] := by
  decide +kernel

theorem h5n173_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p172).getD 6 []=h5p173.getD 6 [] := by
  decide +kernel

theorem h5n173_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p172).getD 7 []=h5p173.getD 7 [] := by
  decide +kernel

theorem h5n173_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p172).getD 8 []=h5p173.getD 8 [] := by
  decide +kernel

theorem h5n173_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p172).getD 9 []=h5p173.getD 9 [] := by
  decide +kernel

theorem h5n173_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p172).getD 10 []=h5p173.getD 10 [] := by
  decide +kernel

theorem h5n173_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p172).getD 11 []=h5p173.getD 11 [] := by
  decide +kernel

theorem h5n173_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p172).getD 12 []=h5p173.getD 12 [] := by
  decide +kernel

theorem h5n173_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p172).getD 13 []=h5p173.getD 13 [] := by
  decide +kernel

theorem h5n173_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p172).getD 14 []=h5p173.getD 14 [] := by
  decide +kernel

theorem h5n173_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p172).getD 15 []=h5p173.getD 15 [] := by
  decide +kernel

theorem h5n173_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p172).getD 16 []=h5p173.getD 16 [] := by
  decide +kernel

theorem h5n173_arithmetic : BiPoly.mul h5p5 h5p172=h5p173 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p172).getD j.val []=h5p173.getD j.val [] :=
      (fun j => Fin.cases h5n173_arithmetic_row0 (fun j => Fin.cases h5n173_arithmetic_row1 (fun j => Fin.cases h5n173_arithmetic_row2 (fun j => Fin.cases h5n173_arithmetic_row3 (fun j => Fin.cases h5n173_arithmetic_row4 (fun j => Fin.cases h5n173_arithmetic_row5 (fun j => Fin.cases h5n173_arithmetic_row6 (fun j => Fin.cases h5n173_arithmetic_row7 (fun j => Fin.cases h5n173_arithmetic_row8 (fun j => Fin.cases h5n173_arithmetic_row9 (fun j => Fin.cases h5n173_arithmetic_row10 (fun j => Fin.cases h5n173_arithmetic_row11 (fun j => Fin.cases h5n173_arithmetic_row12 (fun j => Fin.cases h5n173_arithmetic_row13 (fun j => Fin.cases h5n173_arithmetic_row14 (fun j => Fin.cases h5n173_arithmetic_row15 (fun j => Fin.cases h5n173_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n173 : h5e173.toBi mapPolyEnv=h5p173 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e172.toBi mapPolyEnv)=h5p173
  rw [h5n5, h5n172]
  exact h5n173_arithmetic

#print axioms h5n173_arithmetic
end StackSorting.RationalLift
