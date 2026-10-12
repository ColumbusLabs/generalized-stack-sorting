import BivariateRowEquality
import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p290 : BiPoly.Poly := [[(Int.ofNat 93072789835776), (Int.negSucc 67116434153471), (Int.ofNat 12099711799296)], [(Int.negSucc 900637891619327), (Int.ofNat 709262525574144), (Int.negSucc 175535124779519), (Int.ofNat 13300867160064)], [(Int.ofNat 3960907398274320), (Int.negSucc 3001358572962911), (Int.ofNat 794198933394192), (Int.negSucc 95288515343999), (Int.ofNat 5482761571584)], [(Int.negSucc 10434845020607567), (Int.ofNat 6315490462016304), (Int.negSucc 1153312932271247), (Int.ofNat 94551886575216), (Int.negSucc 12943604539007), (Int.ofNat 1004429479680)], [(Int.ofNat 18234692234842500), (Int.negSucc 5209091221151375), (Int.negSucc 1739631995301095), (Int.ofNat 722953297165392), (Int.negSucc 74328916909355), (Int.ofNat 1816104397536), (Int.ofNat 69000782400)], [(Int.negSucc 22020439675689143), (Int.negSucc 6255459063061415), (Int.ofNat 8767896365255328), (Int.negSucc 2098036079215487), (Int.ofNat 224478721860552), (Int.negSucc 15685717597415), (Int.ofNat 394937278560)], [(Int.ofNat 18396691490143908), (Int.ofNat 23742971470735020), (Int.negSucc 12197712697852859), (Int.ofNat 780965012553192), (Int.ofNat 178973250497460), (Int.negSucc 14864916563459), (Int.negSucc 193150528523)], [(Int.negSucc 10063791794805839), (Int.negSucc 33234792571562615), (Int.ofNat 3001914363341844), (Int.ofNat 4723259564721168), (Int.negSucc 1155673354207319), (Int.ofNat 100983102328152), (Int.negSucc 3768315117947)], [(Int.ofNat 2789254566601857), (Int.ofNat 27198843965085294), (Int.ofNat 13523821223017203), (Int.negSucc 8234905668583139), (Int.ofNat 846922606376787), (Int.ofNat 2046407384646), (Int.negSucc 492509473730)], [(Int.ofNat 470643801337044), (Int.negSucc 13119980797863053), (Int.negSucc 21859766521065701), (Int.ofNat 3580008946279236), (Int.ofNat 1402976095660152), (Int.negSucc 292971563505485), (Int.ofNat 15070736213298)], [(Int.negSucc 796975050244427), (Int.ofNat 2546818383979962), (Int.ofNat 16608175468990425), (Int.ofNat 4701367807022232), (Int.negSucc 2687283449542673), (Int.ofNat 221889870540738), (Int.negSucc 1467380094722)], [(Int.ofNat 321087491592444), (Int.ofNat 1017854917345674), (Int.negSucc 6636177329696531), (Int.negSucc 7897630425756983), (Int.ofNat 1102144159088640), (Int.ofNat 252080240319702), (Int.negSucc 29678823702755)], [(Int.negSucc 42044838250445), (Int.negSucc 856543570098497), (Int.ofNat 691970042919537), (Int.ofNat 5161880264010012), (Int.ofNat 1108952319504735), (Int.negSucc 425706320985299), (Int.ofNat 16876361009124)], [(Int.negSucc 13335264082619), (Int.ofNat 226920923859942), (Int.ofNat 619714108760706), (Int.negSucc 1584179083712411), (Int.negSucc 1581559053068231), (Int.ofNat 121287717458280), (Int.ofNat 21088765977768)], [(Int.ofNat 6842390558400), (Int.negSucc 4271462918333), (Int.negSucc 306912496081652), (Int.ofNat 26169477002136), (Int.ofNat 820038380317416), (Int.ofNat 153146070901728), (Int.negSucc 24547001002343)], [(Int.negSucc 1203639277499), (Int.negSucc 12207344739641), (Int.ofNat 46837142868348), (Int.ofNat 145018811146608), (Int.negSucc 180184700288591), (Int.negSucc 155715566340383), (Int.ofNat 2701374397200)], [(Int.ofNat 81011390625), (Int.ofNat 2881005373980), (Int.ofNat 4579110736596), (Int.negSucc 42823033487855), (Int.negSucc 8646220180943), (Int.ofNat 60369411516912), (Int.ofNat 8173092860352)], [(Int.ofNat 0), (Int.negSucc 222615458999), (Int.negSucc 2383529704487), (Int.ofNat 2787031960704), (Int.ofNat 12751352702640), (Int.negSucc 9553482893087), (Int.negSucc 5536194661439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 226155669624), (Int.ofNat 700445093328), (Int.negSucc 2135550410927), (Int.negSucc 396714311711), (Int.ofNat 1618081319952)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 100604589407), (Int.ofNat 19880844768), (Int.ofNat 321434342496), (Int.negSucc 230503781375)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 16545162384), (Int.negSucc 29339532287), (Int.ofNat 13006946304)]]

theorem h5n290_arithmetic_row0 :
    (BiPoly.mul h5p1 h5p1).getD 0 []=h5p290.getD 0 [] := by
  decide +kernel

theorem h5n290_arithmetic_row1 :
    (BiPoly.mul h5p1 h5p1).getD 1 []=h5p290.getD 1 [] := by
  decide +kernel

theorem h5n290_arithmetic_row2 :
    (BiPoly.mul h5p1 h5p1).getD 2 []=h5p290.getD 2 [] := by
  decide +kernel

theorem h5n290_arithmetic_row3 :
    (BiPoly.mul h5p1 h5p1).getD 3 []=h5p290.getD 3 [] := by
  decide +kernel

theorem h5n290_arithmetic_row4 :
    (BiPoly.mul h5p1 h5p1).getD 4 []=h5p290.getD 4 [] := by
  decide +kernel

theorem h5n290_arithmetic_row5 :
    (BiPoly.mul h5p1 h5p1).getD 5 []=h5p290.getD 5 [] := by
  decide +kernel

theorem h5n290_arithmetic_row6 :
    (BiPoly.mul h5p1 h5p1).getD 6 []=h5p290.getD 6 [] := by
  decide +kernel

theorem h5n290_arithmetic_row7 :
    (BiPoly.mul h5p1 h5p1).getD 7 []=h5p290.getD 7 [] := by
  decide +kernel

theorem h5n290_arithmetic_row8 :
    (BiPoly.mul h5p1 h5p1).getD 8 []=h5p290.getD 8 [] := by
  decide +kernel

theorem h5n290_arithmetic_row9 :
    (BiPoly.mul h5p1 h5p1).getD 9 []=h5p290.getD 9 [] := by
  decide +kernel

theorem h5n290_arithmetic_row10 :
    (BiPoly.mul h5p1 h5p1).getD 10 []=h5p290.getD 10 [] := by
  decide +kernel

theorem h5n290_arithmetic_row11 :
    (BiPoly.mul h5p1 h5p1).getD 11 []=h5p290.getD 11 [] := by
  decide +kernel

theorem h5n290_arithmetic_row12 :
    (BiPoly.mul h5p1 h5p1).getD 12 []=h5p290.getD 12 [] := by
  decide +kernel

theorem h5n290_arithmetic_row13 :
    (BiPoly.mul h5p1 h5p1).getD 13 []=h5p290.getD 13 [] := by
  decide +kernel

theorem h5n290_arithmetic_row14 :
    (BiPoly.mul h5p1 h5p1).getD 14 []=h5p290.getD 14 [] := by
  decide +kernel

theorem h5n290_arithmetic_row15 :
    (BiPoly.mul h5p1 h5p1).getD 15 []=h5p290.getD 15 [] := by
  decide +kernel

theorem h5n290_arithmetic_row16 :
    (BiPoly.mul h5p1 h5p1).getD 16 []=h5p290.getD 16 [] := by
  decide +kernel

theorem h5n290_arithmetic_row17 :
    (BiPoly.mul h5p1 h5p1).getD 17 []=h5p290.getD 17 [] := by
  decide +kernel

theorem h5n290_arithmetic_row18 :
    (BiPoly.mul h5p1 h5p1).getD 18 []=h5p290.getD 18 [] := by
  decide +kernel

theorem h5n290_arithmetic_row19 :
    (BiPoly.mul h5p1 h5p1).getD 19 []=h5p290.getD 19 [] := by
  decide +kernel

theorem h5n290_arithmetic_row20 :
    (BiPoly.mul h5p1 h5p1).getD 20 []=h5p290.getD 20 [] := by
  decide +kernel

theorem h5n290_arithmetic : BiPoly.mul h5p1 h5p1=h5p290 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<21 at hk
    have hf : ∀ j : Fin 21, (BiPoly.mul h5p1 h5p1).getD j.val []=h5p290.getD j.val [] :=
      (fun j => Fin.cases h5n290_arithmetic_row0 (fun j => Fin.cases h5n290_arithmetic_row1 (fun j => Fin.cases h5n290_arithmetic_row2 (fun j => Fin.cases h5n290_arithmetic_row3 (fun j => Fin.cases h5n290_arithmetic_row4 (fun j => Fin.cases h5n290_arithmetic_row5 (fun j => Fin.cases h5n290_arithmetic_row6 (fun j => Fin.cases h5n290_arithmetic_row7 (fun j => Fin.cases h5n290_arithmetic_row8 (fun j => Fin.cases h5n290_arithmetic_row9 (fun j => Fin.cases h5n290_arithmetic_row10 (fun j => Fin.cases h5n290_arithmetic_row11 (fun j => Fin.cases h5n290_arithmetic_row12 (fun j => Fin.cases h5n290_arithmetic_row13 (fun j => Fin.cases h5n290_arithmetic_row14 (fun j => Fin.cases h5n290_arithmetic_row15 (fun j => Fin.cases h5n290_arithmetic_row16 (fun j => Fin.cases h5n290_arithmetic_row17 (fun j => Fin.cases h5n290_arithmetic_row18 (fun j => Fin.cases h5n290_arithmetic_row19 (fun j => Fin.cases h5n290_arithmetic_row20 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n290 : h5e290.toBi mapPolyEnv=h5p290 := by
  change BiPoly.mul (h5e1.toBi mapPolyEnv) (h5e1.toBi mapPolyEnv)=h5p290
  rw [h5n1]
  exact h5n290_arithmetic

#print axioms h5n290_arithmetic
end StackSorting.RationalLift
