import BivariateRowEquality
import Horner5Base
import Horner5Node416
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p417 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 696830687999), (Int.negSucc 3473475281279), (Int.negSucc 3754920136319), (Int.negSucc 2642703615359), (Int.ofNat 3325971404160), (Int.ofNat 4990399476480)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6064491669120), (Int.ofNat 27638012804544), (Int.ofNat 22634259992064), (Int.ofNat 15661507012992), (Int.negSucc 27394169683967), (Int.negSucc 26686727290943), (Int.ofNat 1231842784896)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 23746412658239), (Int.negSucc 100219633678367), (Int.negSucc 65390049005759), (Int.negSucc 57309634821311), (Int.ofNat 84587516353728), (Int.ofNat 58882618041696), (Int.ofNat 9421130402496), (Int.negSucc 896945654015)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 55181157118560), (Int.ofNat 220461319017936), (Int.ofNat 136642773042000), (Int.ofNat 156017072925504), (Int.negSucc 128349216889343), (Int.negSucc 83336237828783), (Int.negSucc 60889865485103), (Int.ofNat 7467755154336), (Int.negSucc 353977671167)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 84488618001599), (Int.negSucc 330486227555903), (Int.negSucc 251881765024079), (Int.negSucc 297227986727135), (Int.ofNat 62725038815712), (Int.ofNat 103117322862720), (Int.ofNat 116737189266864), (Int.negSucc 3607697617247), (Int.ofNat 302177433216), (Int.negSucc 32425755647)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 89428561311360), (Int.ofNat 358895575244160), (Int.ofNat 399099579981456), (Int.ofNat 398057361207360), (Int.ofNat 147299437869120), (Int.negSucc 101938805574047), (Int.negSucc 96623475555983), (Int.negSucc 42119684643935), (Int.ofNat 4776964634688), (Int.negSucc 124439402879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 66723613680319), (Int.negSucc 291469724771295), (Int.negSucc 489991898723199), (Int.negSucc 413060738519631), (Int.negSucc 376334900868927), (Int.ofNat 23988117204128), (Int.ofNat 25301594380512), (Int.ofNat 80491233083824), (Int.negSucc 4809940613023), (Int.ofNat 243119496320)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 35069151951040), (Int.ofNat 178623405028448), (Int.ofNat 439860492667376), (Int.ofNat 380603223698816), (Int.ofNat 440863660177520), (Int.ofNat 125773760342576), (Int.ofNat 19183828382112), (Int.negSucc 43601433666367), (Int.negSucc 13896557625871), (Int.ofNat 981326367776)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 12718139293759), (Int.negSucc 81559163843295), (Int.negSucc 282094529113023), (Int.negSucc 320958505976463), (Int.negSucc 330135218910975), (Int.negSucc 231030375748959), (Int.negSucc 40278914780975), (Int.negSucc 15475396233871), (Int.ofNat 22807022791456), (Int.negSucc 847614573375)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3030220448000), (Int.ofNat 26778403129024), (Int.ofNat 126775042749136), (Int.ofNat 221091954213632), (Int.ofNat 188447180212224), (Int.ofNat 205395590515392), (Int.ofNat 62778554640576), (Int.ofNat 29630408026752), (Int.negSucc 5432391885791), (Int.negSucc 2049218392511)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 426926421759), (Int.negSucc 5926418408959), (Int.negSucc 38565164134399), (Int.negSucc 109719454363599), (Int.negSucc 99248982236639), (Int.negSucc 109004317619999), (Int.negSucc 64891464157439), (Int.negSucc 19059728692127), (Int.negSucc 8009177549663), (Int.ofNat 2026866548160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 26958245600), (Int.ofNat 784428175312), (Int.ofNat 7418831184832), (Int.ofNat 35762935558208), (Int.ofNat 48148986962352), (Int.ofNat 39031093345440), (Int.ofNat 38953103413056), (Int.ofNat 12055111990656), (Int.ofNat 6011131296000), (Int.ofNat 280962736512)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 46499860319), (Int.negSucc 784464463919), (Int.negSucc 6905786782607), (Int.negSucc 17240033920031), (Int.negSucc 12390341175551), (Int.negSucc 13159418296895), (Int.negSucc 7008162489599), (Int.negSucc 1985000441471), (Int.negSucc 765880780031)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 31810983840), (Int.ofNat 644882927424), (Int.ofNat 3646391577504), (Int.ofNat 4055635422528), (Int.ofNat 2577008965248), (Int.ofNat 2439323875584), (Int.ofNat 617443505280), (Int.ofNat 239721078528)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14126737823), (Int.negSucc 346100626655), (Int.negSucc 943742769983), (Int.negSucc 435109257215), (Int.negSucc 403232674175), (Int.negSucc 174498558335), (Int.negSucc 20993230079)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4439764224), (Int.ofNat 96065294976), (Int.ofNat 93125607552), (Int.ofNat 22249271808), (Int.ofNat 20993230080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 628020863), (Int.negSucc 10496615039)]]

theorem h5n417_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p416).getD 0 []=h5p417.getD 0 [] := by
  decide +kernel

theorem h5n417_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p416).getD 1 []=h5p417.getD 1 [] := by
  decide +kernel

theorem h5n417_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p416).getD 2 []=h5p417.getD 2 [] := by
  decide +kernel

theorem h5n417_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p416).getD 3 []=h5p417.getD 3 [] := by
  decide +kernel

theorem h5n417_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p416).getD 4 []=h5p417.getD 4 [] := by
  decide +kernel

theorem h5n417_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p416).getD 5 []=h5p417.getD 5 [] := by
  decide +kernel

theorem h5n417_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p416).getD 6 []=h5p417.getD 6 [] := by
  decide +kernel

theorem h5n417_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p416).getD 7 []=h5p417.getD 7 [] := by
  decide +kernel

theorem h5n417_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p416).getD 8 []=h5p417.getD 8 [] := by
  decide +kernel

theorem h5n417_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p416).getD 9 []=h5p417.getD 9 [] := by
  decide +kernel

theorem h5n417_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p416).getD 10 []=h5p417.getD 10 [] := by
  decide +kernel

theorem h5n417_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p416).getD 11 []=h5p417.getD 11 [] := by
  decide +kernel

theorem h5n417_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p416).getD 12 []=h5p417.getD 12 [] := by
  decide +kernel

theorem h5n417_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p416).getD 13 []=h5p417.getD 13 [] := by
  decide +kernel

theorem h5n417_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p416).getD 14 []=h5p417.getD 14 [] := by
  decide +kernel

theorem h5n417_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p416).getD 15 []=h5p417.getD 15 [] := by
  decide +kernel

theorem h5n417_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p416).getD 16 []=h5p417.getD 16 [] := by
  decide +kernel

theorem h5n417_arithmetic : BiPoly.mul h5p5 h5p416=h5p417 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p416).getD j.val []=h5p417.getD j.val [] :=
      (fun j => Fin.cases h5n417_arithmetic_row0 (fun j => Fin.cases h5n417_arithmetic_row1 (fun j => Fin.cases h5n417_arithmetic_row2 (fun j => Fin.cases h5n417_arithmetic_row3 (fun j => Fin.cases h5n417_arithmetic_row4 (fun j => Fin.cases h5n417_arithmetic_row5 (fun j => Fin.cases h5n417_arithmetic_row6 (fun j => Fin.cases h5n417_arithmetic_row7 (fun j => Fin.cases h5n417_arithmetic_row8 (fun j => Fin.cases h5n417_arithmetic_row9 (fun j => Fin.cases h5n417_arithmetic_row10 (fun j => Fin.cases h5n417_arithmetic_row11 (fun j => Fin.cases h5n417_arithmetic_row12 (fun j => Fin.cases h5n417_arithmetic_row13 (fun j => Fin.cases h5n417_arithmetic_row14 (fun j => Fin.cases h5n417_arithmetic_row15 (fun j => Fin.cases h5n417_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n417 : h5e417.toBi mapPolyEnv=h5p417 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e416.toBi mapPolyEnv)=h5p417
  rw [h5n5, h5n416]
  exact h5n417_arithmetic

#print axioms h5n417_arithmetic
end StackSorting.RationalLift
