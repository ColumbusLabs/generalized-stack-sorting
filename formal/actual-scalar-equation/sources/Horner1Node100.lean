import BivariateRowEquality
import Horner1Base
import Horner1Node016
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p100 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 516170880000), (Int.ofNat 2347119892800), (Int.negSucc 2763954122399), (Int.negSucc 12805593782399), (Int.ofNat 11898406159200)], [(Int.ofNat 0), (Int.negSucc 3918095431199), (Int.negSucc 14921976597839), (Int.ofNat 27820401758640), (Int.ofNat 80358610721040), (Int.negSucc 91297703290319), (Int.ofNat 9211398848640)], [(Int.ofNat 0), (Int.ofNat 13194665913600), (Int.ofNat 40890425580720), (Int.negSucc 107397290909879), (Int.negSucc 212264378075879), (Int.ofNat 250152752958840), (Int.negSucc 24169090311719), (Int.ofNat 2458198667520)], [(Int.ofNat 0), (Int.negSucc 25928380477799), (Int.negSucc 62619385810499), (Int.ofNat 222004041970440), (Int.ofNat 322462921728360), (Int.negSucc 265669115283119), (Int.negSucc 73215457509539), (Int.ofNat 6854501384880), (Int.ofNat 253632483840)], [(Int.ofNat 0), (Int.ofNat 32882496641400), (Int.ofNat 57434248270860), (Int.negSucc 279579913748039), (Int.negSucc 349216232617199), (Int.negSucc 64040328987959), (Int.ofNat 347389812726300), (Int.negSucc 41595036350399), (Int.ofNat 2500996515360), (Int.ofNat 7369489920)], [(Int.ofNat 0), (Int.negSucc 28085689322199), (Int.negSucc 30072691643619), (Int.ofNat 230080476490120), (Int.ofNat 343854505928960), (Int.ofNat 455328071274840), (Int.negSucc 442630000853579), (Int.negSucc 7078245251999), (Int.ofNat 476809119920), (Int.ofNat 170311851840)], [(Int.ofNat 0), (Int.ofNat 16342118088200), (Int.ofNat 5511312304740), (Int.negSucc 132658908146299), (Int.negSucc 335586478432759), (Int.negSucc 512673338544639), (Int.ofNat 70154948240220), (Int.ofNat 192041999994500), (Int.negSucc 19912063028919), (Int.ofNat 672586253120)], [(Int.ofNat 0), (Int.negSucc 6389975776599), (Int.ofNat 3619144462140), (Int.ofNat 60773170928660), (Int.ofNat 280086264432180), (Int.ofNat 326559278736520), (Int.ofNat 343848979444720), (Int.negSucc 238573671438059), (Int.ofNat 4759773986300), (Int.negSucc 229721835439)], [(Int.ofNat 0), (Int.ofNat 1605752777800), (Int.negSucc 3080910763339), (Int.negSucc 25985528816759), (Int.negSucc 175137780488759), (Int.negSucc 181634778608479), (Int.negSucc 353849325244839), (Int.ofNat 22604142293320), (Int.ofNat 52960925684040), (Int.negSucc 3357119295359)], [(Int.ofNat 0), (Int.negSucc 234097699399), (Int.ofNat 1070738022900), (Int.ofNat 10206546972480), (Int.ofNat 77767098242400), (Int.ofNat 119621730649280), (Int.ofNat 153821668390680), (Int.ofNat 144111209383200), (Int.negSucc 51751840694519), (Int.ofNat 378272276640)], [(Int.ofNat 0), (Int.ofNat 15034406200), (Int.negSucc 192767747219), (Int.negSucc 2972998654419), (Int.negSucc 23649846264719), (Int.negSucc 69071513796359), (Int.negSucc 42067313686439), (Int.negSucc 106312108776359), (Int.negSucc 6295600438679), (Int.ofNat 5986757912160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14744028360), (Int.ofNat 511601935020), (Int.ofNat 4607716661340), (Int.ofNat 25598665739400), (Int.ofNat 18930174836640), (Int.ofNat 27382093005240), (Int.ofNat 27240665832720), (Int.negSucc 3191544397439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 37645657559), (Int.negSucc 497226473159), (Int.negSucc 5243533406759), (Int.negSucc 9643558340519), (Int.negSucc 2337978667679), (Int.negSucc 11443892660639), (Int.negSucc 1646516545919)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 20418420600), (Int.ofNat 480802674600), (Int.ofNat 2459059939440), (Int.ofNat 854592611040), (Int.ofNat 1152708386400), (Int.ofNat 1474504300800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8798855039), (Int.negSucc 232438947839), (Int.negSucc 394302301919), (Int.ofNat 102386397600), (Int.negSucc 262415375999)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2355078240), (Int.ofNat 39362306400)]]

theorem h1n100_arithmetic_row0 :
    (BiPoly.mul h1p99 h1p16).getD 0 []=h1p100.getD 0 [] := by
  decide +kernel

theorem h1n100_arithmetic_row1 :
    (BiPoly.mul h1p99 h1p16).getD 1 []=h1p100.getD 1 [] := by
  decide +kernel

theorem h1n100_arithmetic_row2 :
    (BiPoly.mul h1p99 h1p16).getD 2 []=h1p100.getD 2 [] := by
  decide +kernel

theorem h1n100_arithmetic_row3 :
    (BiPoly.mul h1p99 h1p16).getD 3 []=h1p100.getD 3 [] := by
  decide +kernel

theorem h1n100_arithmetic_row4 :
    (BiPoly.mul h1p99 h1p16).getD 4 []=h1p100.getD 4 [] := by
  decide +kernel

theorem h1n100_arithmetic_row5 :
    (BiPoly.mul h1p99 h1p16).getD 5 []=h1p100.getD 5 [] := by
  decide +kernel

theorem h1n100_arithmetic_row6 :
    (BiPoly.mul h1p99 h1p16).getD 6 []=h1p100.getD 6 [] := by
  decide +kernel

theorem h1n100_arithmetic_row7 :
    (BiPoly.mul h1p99 h1p16).getD 7 []=h1p100.getD 7 [] := by
  decide +kernel

theorem h1n100_arithmetic_row8 :
    (BiPoly.mul h1p99 h1p16).getD 8 []=h1p100.getD 8 [] := by
  decide +kernel

theorem h1n100_arithmetic_row9 :
    (BiPoly.mul h1p99 h1p16).getD 9 []=h1p100.getD 9 [] := by
  decide +kernel

theorem h1n100_arithmetic_row10 :
    (BiPoly.mul h1p99 h1p16).getD 10 []=h1p100.getD 10 [] := by
  decide +kernel

theorem h1n100_arithmetic_row11 :
    (BiPoly.mul h1p99 h1p16).getD 11 []=h1p100.getD 11 [] := by
  decide +kernel

theorem h1n100_arithmetic_row12 :
    (BiPoly.mul h1p99 h1p16).getD 12 []=h1p100.getD 12 [] := by
  decide +kernel

theorem h1n100_arithmetic_row13 :
    (BiPoly.mul h1p99 h1p16).getD 13 []=h1p100.getD 13 [] := by
  decide +kernel

theorem h1n100_arithmetic_row14 :
    (BiPoly.mul h1p99 h1p16).getD 14 []=h1p100.getD 14 [] := by
  decide +kernel

theorem h1n100_arithmetic_row15 :
    (BiPoly.mul h1p99 h1p16).getD 15 []=h1p100.getD 15 [] := by
  decide +kernel

theorem h1n100_arithmetic : BiPoly.mul h1p99 h1p16=h1p100 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h1p99 h1p16).getD j.val []=h1p100.getD j.val [] :=
      (fun j => Fin.cases h1n100_arithmetic_row0 (fun j => Fin.cases h1n100_arithmetic_row1 (fun j => Fin.cases h1n100_arithmetic_row2 (fun j => Fin.cases h1n100_arithmetic_row3 (fun j => Fin.cases h1n100_arithmetic_row4 (fun j => Fin.cases h1n100_arithmetic_row5 (fun j => Fin.cases h1n100_arithmetic_row6 (fun j => Fin.cases h1n100_arithmetic_row7 (fun j => Fin.cases h1n100_arithmetic_row8 (fun j => Fin.cases h1n100_arithmetic_row9 (fun j => Fin.cases h1n100_arithmetic_row10 (fun j => Fin.cases h1n100_arithmetic_row11 (fun j => Fin.cases h1n100_arithmetic_row12 (fun j => Fin.cases h1n100_arithmetic_row13 (fun j => Fin.cases h1n100_arithmetic_row14 (fun j => Fin.cases h1n100_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n100 : h1e100.toBi mapPolyEnv=h1p100 := by
  change BiPoly.mul (h1e99.toBi mapPolyEnv) (h1e16.toBi mapPolyEnv)=h1p100
  rw [h1n99, h1n16]
  exact h1n100_arithmetic

#print axioms h1n100_arithmetic
end StackSorting.RationalLift
