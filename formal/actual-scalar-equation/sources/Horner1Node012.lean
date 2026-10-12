import BivariateRowEquality
import Horner1Base
import Horner1Node011
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p12 : BiPoly.Poly := [[(Int.negSucc 6452135999), (Int.negSucc 45066080159), (Int.negSucc 53926443359), (Int.ofNat 92414805120)], [(Int.ofNat 28073960640), (Int.ofNat 188939266848), (Int.ofNat 206057983104), (Int.negSucc 391653570815), (Int.ofNat 41637141504)], [(Int.negSucc 49588249679), (Int.negSucc 330720924455), (Int.negSucc 400494814703), (Int.ofNat 512026250760), (Int.negSucc 14419785311), (Int.ofNat 4421693952)], [(Int.ofNat 45408699360), (Int.ofNat 312297597360), (Int.ofNat 518889172032), (Int.negSucc 77129589743), (Int.negSucc 244334896847), (Int.ofNat 15964079040)], [(Int.negSucc 22709925599), (Int.negSucc 170065872047), (Int.negSucc 444141488711), (Int.negSucc 428164339895), (Int.ofNat 319664491272), (Int.negSucc 13868444255)], [(Int.ofNat 5889764640), (Int.ofNat 52050597552), (Int.ofNat 230968900608), (Int.ofNat 466948761888), (Int.negSucc 17138893535), (Int.negSucc 51560107391)], [(Int.negSucc 622113359), (Int.negSucc 7789835687), (Int.negSucc 65312867783), (Int.negSucc 222454466975), (Int.negSucc 173506263263), (Int.ofNat 42376735872)], [(Int.ofNat 0), (Int.ofNat 355250592), (Int.ofNat 8039785968), (Int.ofNat 51584423616), (Int.ofNat 103932057456), (Int.ofNat 13979602368)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 151917551), (Int.negSucc 4776558191), (Int.negSucc 21124050047), (Int.negSucc 17793992447)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 52335072), (Int.ofNat 1084058208), (Int.ofNat 3498871680)]]

theorem h1n12_arithmetic_row0 :
    (BiPoly.mul h1p6 h1p11).getD 0 []=h1p12.getD 0 [] := by
  decide +kernel

theorem h1n12_arithmetic_row1 :
    (BiPoly.mul h1p6 h1p11).getD 1 []=h1p12.getD 1 [] := by
  decide +kernel

theorem h1n12_arithmetic_row2 :
    (BiPoly.mul h1p6 h1p11).getD 2 []=h1p12.getD 2 [] := by
  decide +kernel

theorem h1n12_arithmetic_row3 :
    (BiPoly.mul h1p6 h1p11).getD 3 []=h1p12.getD 3 [] := by
  decide +kernel

theorem h1n12_arithmetic_row4 :
    (BiPoly.mul h1p6 h1p11).getD 4 []=h1p12.getD 4 [] := by
  decide +kernel

theorem h1n12_arithmetic_row5 :
    (BiPoly.mul h1p6 h1p11).getD 5 []=h1p12.getD 5 [] := by
  decide +kernel

theorem h1n12_arithmetic_row6 :
    (BiPoly.mul h1p6 h1p11).getD 6 []=h1p12.getD 6 [] := by
  decide +kernel

theorem h1n12_arithmetic_row7 :
    (BiPoly.mul h1p6 h1p11).getD 7 []=h1p12.getD 7 [] := by
  decide +kernel

theorem h1n12_arithmetic_row8 :
    (BiPoly.mul h1p6 h1p11).getD 8 []=h1p12.getD 8 [] := by
  decide +kernel

theorem h1n12_arithmetic_row9 :
    (BiPoly.mul h1p6 h1p11).getD 9 []=h1p12.getD 9 [] := by
  decide +kernel

theorem h1n12_arithmetic : BiPoly.mul h1p6 h1p11=h1p12 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h1p6 h1p11).getD j.val []=h1p12.getD j.val [] :=
      (fun j => Fin.cases h1n12_arithmetic_row0 (fun j => Fin.cases h1n12_arithmetic_row1 (fun j => Fin.cases h1n12_arithmetic_row2 (fun j => Fin.cases h1n12_arithmetic_row3 (fun j => Fin.cases h1n12_arithmetic_row4 (fun j => Fin.cases h1n12_arithmetic_row5 (fun j => Fin.cases h1n12_arithmetic_row6 (fun j => Fin.cases h1n12_arithmetic_row7 (fun j => Fin.cases h1n12_arithmetic_row8 (fun j => Fin.cases h1n12_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n12 : h1e12.toBi mapPolyEnv=h1p12 := by
  change BiPoly.mul (h1e6.toBi mapPolyEnv) (h1e11.toBi mapPolyEnv)=h1p12
  rw [h1n6, h1n11]
  exact h1n12_arithmetic

#print axioms h1n12_arithmetic
end StackSorting.RationalLift
