import BivariateRowEquality
import Horner5Base
import Horner5Node415
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p416 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 4301424000), (Int.ofNat 17139781440), (Int.ofNat 6038737920), (Int.ofNat 10274247360), (Int.negSucc 30804935039)], [(Int.ofNat 0), (Int.negSucc 23017397759), (Int.negSucc 82649947391), (Int.negSucc 6114620159), (Int.negSucc 42120279935), (Int.ofNat 127081428480), (Int.negSucc 13879047167)], [(Int.ofNat 0), (Int.ofNat 51774806880), (Int.ofNat 172399733136), (Int.ofNat 1367881872), (Int.ofNat 100033033872), (Int.negSucc 170118598511), (Int.ofNat 4438120608), (Int.negSucc 1473897983)], [(Int.ofNat 0), (Int.negSucc 63331299359), (Int.negSucc 205626283343), (Int.negSucc 59160855167), (Int.negSucc 132908930159), (Int.ofNat 44479958784), (Int.ofNat 80114625696), (Int.negSucc 5321359679)], [(Int.ofNat 0), (Int.ofNat 45412416640), (Int.ofNat 155065930112), (Int.ofNat 165413868880), (Int.ofNat 95216513120), (Int.ofNat 120765900320), (Int.negSucc 105399126735), (Int.ofNat 4622814752)], [(Int.ofNat 0), (Int.negSucc 19066460159), (Int.negSucc 75738315519), (Int.negSucc 189673748687), (Int.negSucc 61427136911), (Int.negSucc 149013571215), (Int.ofNat 10009640128), (Int.ofNat 17186702464)], [(Int.ofNat 0), (Int.ofNat 4341252000), (Int.ofNat 22943356400), (Int.ofNat 111770461600), (Int.ofNat 66448665616), (Int.ofNat 73837052384), (Int.ofNat 54304026432), (Int.negSucc 14125578623)], [(Int.ofNat 0), (Int.negSucc 414742239), (Int.negSucc 3771088559), (Int.negSucc 34054248655), (Int.negSucc 52309123871), (Int.negSucc 20831715359), (Int.negSucc 35808986015), (Int.negSucc 4659867455)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 236833728), (Int.ofNat 4513800768), (Int.ofNat 19620063168), (Int.ofNat 8277414528), (Int.ofNat 8524182720), (Int.ofNat 5931330816)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 101278367), (Int.negSucc 2814148703), (Int.negSucc 3583700735), (Int.negSucc 652925375), (Int.negSucc 1166290559)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 34890048), (Int.ofNat 583145280)]]

theorem h5n416_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p415).getD 0 []=h5p416.getD 0 [] := by
  decide +kernel

theorem h5n416_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p415).getD 1 []=h5p416.getD 1 [] := by
  decide +kernel

theorem h5n416_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p415).getD 2 []=h5p416.getD 2 [] := by
  decide +kernel

theorem h5n416_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p415).getD 3 []=h5p416.getD 3 [] := by
  decide +kernel

theorem h5n416_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p415).getD 4 []=h5p416.getD 4 [] := by
  decide +kernel

theorem h5n416_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p415).getD 5 []=h5p416.getD 5 [] := by
  decide +kernel

theorem h5n416_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p415).getD 6 []=h5p416.getD 6 [] := by
  decide +kernel

theorem h5n416_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p415).getD 7 []=h5p416.getD 7 [] := by
  decide +kernel

theorem h5n416_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p415).getD 8 []=h5p416.getD 8 [] := by
  decide +kernel

theorem h5n416_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p415).getD 9 []=h5p416.getD 9 [] := by
  decide +kernel

theorem h5n416_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p415).getD 10 []=h5p416.getD 10 [] := by
  decide +kernel

theorem h5n416_arithmetic : BiPoly.mul h5p6 h5p415=h5p416 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p415).getD j.val []=h5p416.getD j.val [] :=
      (fun j => Fin.cases h5n416_arithmetic_row0 (fun j => Fin.cases h5n416_arithmetic_row1 (fun j => Fin.cases h5n416_arithmetic_row2 (fun j => Fin.cases h5n416_arithmetic_row3 (fun j => Fin.cases h5n416_arithmetic_row4 (fun j => Fin.cases h5n416_arithmetic_row5 (fun j => Fin.cases h5n416_arithmetic_row6 (fun j => Fin.cases h5n416_arithmetic_row7 (fun j => Fin.cases h5n416_arithmetic_row8 (fun j => Fin.cases h5n416_arithmetic_row9 (fun j => Fin.cases h5n416_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n416 : h5e416.toBi mapPolyEnv=h5p416 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e415.toBi mapPolyEnv)=h5p416
  rw [h5n6, h5n415]
  exact h5n416_arithmetic

#print axioms h5n416_arithmetic
end StackSorting.RationalLift
