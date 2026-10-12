import BivariateRowEquality
import Horner1Base
import Horner1Node097
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p98 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 174207671999), (Int.negSucc 2087822524319), (Int.negSucc 5449442728319), (Int.ofNat 1454571600480), (Int.ofNat 4990399476480)], [(Int.ofNat 0), (Int.ofNat 1341915245280), (Int.ofNat 15608748769776), (Int.ofNat 37192568618448), (Int.negSucc 17771597820143), (Int.negSucc 27148668335279), (Int.ofNat 1231842784896)], [(Int.ofNat 0), (Int.negSucc 4594687919279), (Int.negSucc 52344297047015), (Int.negSucc 118060538104151), (Int.ofNat 59870027661192), (Int.ofNat 55629989657640), (Int.ofNat 9757485022752), (Int.negSucc 896945654015)], [(Int.ofNat 0), (Int.ofNat 9200601360360), (Int.ofNat 103932745584228), (Int.ofNat 234688844887272), (Int.negSucc 70394494079159), (Int.negSucc 63406364409071), (Int.negSucc 63579655645739), (Int.ofNat 7600496781024), (Int.negSucc 353977671167)], [(Int.ofNat 0), (Int.negSucc 11921553140039), (Int.negSucc 135744494167907), (Int.negSucc 329666451032567), (Int.negSucc 47309581440719), (Int.ofNat 64461405346440), (Int.ofNat 117807510236364), (Int.negSucc 3710881106063), (Int.ofNat 314337091584), (Int.negSucc 32425755647)], [(Int.ofNat 0), (Int.ofNat 10435587187800), (Int.ofNat 122400935078052), (Int.ofNat 344627484997464), (Int.ofNat 260974563670464), (Int.negSucc 52828546436951), (Int.negSucc 82198896322883), (Int.negSucc 43888371946367), (Int.ofNat 4823629410768), (Int.negSucc 124439402879)], [(Int.ofNat 0), (Int.negSucc 6245316232279), (Int.negSucc 77668407243131), (Int.negSucc 270650899518235), (Int.negSucc 396286704401343), (Int.negSucc 35445245255631), (Int.negSucc 853014701387), (Int.ofNat 82156766269668), (Int.negSucc 4901110424143), (Int.ofNat 243119496320)], [(Int.ofNat 0), (Int.ofNat 2521971755480), (Int.ofNat 34603776160580), (Int.ofNat 156913314033964), (Int.ofNat 352464220502988), (Int.ofNat 169686268615464), (Int.ofNat 37703036117856), (Int.negSucc 38575329298435), (Int.negSucc 14264555013787), (Int.ofNat 981326367776)], [(Int.ofNat 0), (Int.negSucc 657563067959), (Int.negSucc 10564730319803), (Int.negSucc 64848789475159), (Int.negSucc 205986214102407), (Int.negSucc 219080755012479), (Int.negSucc 49271812424039), (Int.negSucc 23272487042599), (Int.ofNat 23124878256472), (Int.negSucc 847614573375)], [(Int.ofNat 0), (Int.ofNat 99992044040), (Int.ofNat 2090319314412), (Int.ofNat 18111474067680), (Int.ofNat 80544747252768), (Int.ofNat 153447253079712), (Int.ofNat 64434698044008), (Int.ofNat 31884128444896), (Int.negSucc 4663934988599), (Int.negSucc 2049218392511)], [(Int.ofNat 0), (Int.negSucc 6739561399), (Int.negSucc 238398569947), (Int.negSucc 3130776091091), (Int.negSucc 20407871375943), (Int.negSucc 64134477648519), (Int.negSucc 56364125433863), (Int.negSucc 17714292103559), (Int.negSucc 8769252505223), (Int.ofNat 2026866548160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11624965080), (Int.ofNat 281163090660), (Int.ofNat 3066111862452), (Int.ofNat 15800202164712), (Int.ofNat 27759195937584), (Int.ofNat 10726570173576), (Int.ofNat 5905770269808), (Int.ofNat 280962736512)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7952745959), (Int.negSucc 221311015079), (Int.negSucc 2084163373511), (Int.negSucc 7291671792695), (Int.negSucc 5883968212031), (Int.negSucc 1697795148959), (Int.negSucc 765880780031)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3531684456), (Int.ofNat 113668691256), (Int.ofNat 894288157776), (Int.ofNat 1749929334048), (Int.ofNat 527548100832), (Int.ofNat 239721078528)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1109941055), (Int.negSucc 32738846975), (Int.negSucc 211374791135), (Int.negSucc 166626097055), (Int.negSucc 20993230079)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 157005216), (Int.ofNat 3880195488), (Int.ofNat 20993230080)]]

theorem h1n98_arithmetic_row0 :
    (BiPoly.mul h1p5 h1p97).getD 0 []=h1p98.getD 0 [] := by
  decide +kernel

theorem h1n98_arithmetic_row1 :
    (BiPoly.mul h1p5 h1p97).getD 1 []=h1p98.getD 1 [] := by
  decide +kernel

theorem h1n98_arithmetic_row2 :
    (BiPoly.mul h1p5 h1p97).getD 2 []=h1p98.getD 2 [] := by
  decide +kernel

theorem h1n98_arithmetic_row3 :
    (BiPoly.mul h1p5 h1p97).getD 3 []=h1p98.getD 3 [] := by
  decide +kernel

theorem h1n98_arithmetic_row4 :
    (BiPoly.mul h1p5 h1p97).getD 4 []=h1p98.getD 4 [] := by
  decide +kernel

theorem h1n98_arithmetic_row5 :
    (BiPoly.mul h1p5 h1p97).getD 5 []=h1p98.getD 5 [] := by
  decide +kernel

theorem h1n98_arithmetic_row6 :
    (BiPoly.mul h1p5 h1p97).getD 6 []=h1p98.getD 6 [] := by
  decide +kernel

theorem h1n98_arithmetic_row7 :
    (BiPoly.mul h1p5 h1p97).getD 7 []=h1p98.getD 7 [] := by
  decide +kernel

theorem h1n98_arithmetic_row8 :
    (BiPoly.mul h1p5 h1p97).getD 8 []=h1p98.getD 8 [] := by
  decide +kernel

theorem h1n98_arithmetic_row9 :
    (BiPoly.mul h1p5 h1p97).getD 9 []=h1p98.getD 9 [] := by
  decide +kernel

theorem h1n98_arithmetic_row10 :
    (BiPoly.mul h1p5 h1p97).getD 10 []=h1p98.getD 10 [] := by
  decide +kernel

theorem h1n98_arithmetic_row11 :
    (BiPoly.mul h1p5 h1p97).getD 11 []=h1p98.getD 11 [] := by
  decide +kernel

theorem h1n98_arithmetic_row12 :
    (BiPoly.mul h1p5 h1p97).getD 12 []=h1p98.getD 12 [] := by
  decide +kernel

theorem h1n98_arithmetic_row13 :
    (BiPoly.mul h1p5 h1p97).getD 13 []=h1p98.getD 13 [] := by
  decide +kernel

theorem h1n98_arithmetic_row14 :
    (BiPoly.mul h1p5 h1p97).getD 14 []=h1p98.getD 14 [] := by
  decide +kernel

theorem h1n98_arithmetic_row15 :
    (BiPoly.mul h1p5 h1p97).getD 15 []=h1p98.getD 15 [] := by
  decide +kernel

theorem h1n98_arithmetic : BiPoly.mul h1p5 h1p97=h1p98 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h1p5 h1p97).getD j.val []=h1p98.getD j.val [] :=
      (fun j => Fin.cases h1n98_arithmetic_row0 (fun j => Fin.cases h1n98_arithmetic_row1 (fun j => Fin.cases h1n98_arithmetic_row2 (fun j => Fin.cases h1n98_arithmetic_row3 (fun j => Fin.cases h1n98_arithmetic_row4 (fun j => Fin.cases h1n98_arithmetic_row5 (fun j => Fin.cases h1n98_arithmetic_row6 (fun j => Fin.cases h1n98_arithmetic_row7 (fun j => Fin.cases h1n98_arithmetic_row8 (fun j => Fin.cases h1n98_arithmetic_row9 (fun j => Fin.cases h1n98_arithmetic_row10 (fun j => Fin.cases h1n98_arithmetic_row11 (fun j => Fin.cases h1n98_arithmetic_row12 (fun j => Fin.cases h1n98_arithmetic_row13 (fun j => Fin.cases h1n98_arithmetic_row14 (fun j => Fin.cases h1n98_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n98 : h1e98.toBi mapPolyEnv=h1p98 := by
  change BiPoly.mul (h1e5.toBi mapPolyEnv) (h1e97.toBi mapPolyEnv)=h1p98
  rw [h1n5, h1n97]
  exact h1n98_arithmetic

#print axioms h1n98_arithmetic
end StackSorting.RationalLift
