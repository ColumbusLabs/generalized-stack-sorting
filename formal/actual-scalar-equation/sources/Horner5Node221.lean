import BivariateRowEquality
import Horner5Base
import Horner5Node220
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p221 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 38712816000), (Int.ofNat 154258032960), (Int.ofNat 54348641280), (Int.ofNat 92468226240), (Int.negSucc 277244415359)], [(Int.ofNat 0), (Int.negSucc 207156579839), (Int.negSucc 743849526527), (Int.negSucc 55031581439), (Int.negSucc 379082519423), (Int.ofNat 1143732856320), (Int.negSucc 124911424511)], [(Int.ofNat 0), (Int.ofNat 465973261920), (Int.ofNat 1551597598224), (Int.ofNat 12310936848), (Int.ofNat 900297304848), (Int.negSucc 1531067386607), (Int.ofNat 39943085472), (Int.negSucc 13265081855)], [(Int.ofNat 0), (Int.negSucc 569981694239), (Int.negSucc 1850636550095), (Int.negSucc 532447696511), (Int.negSucc 1196180371439), (Int.ofNat 400319629056), (Int.ofNat 721031631264), (Int.negSucc 47892237119)], [(Int.ofNat 0), (Int.ofNat 408711749760), (Int.ofNat 1395593371008), (Int.ofNat 1488724819920), (Int.ofNat 856948618080), (Int.ofNat 1086893102880), (Int.negSucc 948592140623), (Int.ofNat 41605332768)], [(Int.ofNat 0), (Int.negSucc 171598141439), (Int.negSucc 681644839679), (Int.negSucc 1707063738191), (Int.negSucc 552844232207), (Int.negSucc 1341122140943), (Int.ofNat 90086761152), (Int.ofNat 154680322176)], [(Int.ofNat 0), (Int.ofNat 39071268000), (Int.ofNat 206490207600), (Int.ofNat 1005934154400), (Int.ofNat 598037990544), (Int.ofNat 664533471456), (Int.ofNat 488736237888), (Int.negSucc 127130207615)], [(Int.ofNat 0), (Int.negSucc 3732680159), (Int.negSucc 33939797039), (Int.negSucc 306488237903), (Int.negSucc 470782114847), (Int.negSucc 187485438239), (Int.negSucc 322280874143), (Int.negSucc 41938807103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2131503552), (Int.ofNat 40624206912), (Int.ofNat 176580568512), (Int.ofNat 74496730752), (Int.ofNat 76717644480), (Int.ofNat 53381977344)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 911505311), (Int.negSucc 25327338335), (Int.negSucc 32253306623), (Int.negSucc 5876328383), (Int.negSucc 10496615039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 314010432), (Int.ofNat 5248307520)]]

theorem h5n221_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p220).getD 0 []=h5p221.getD 0 [] := by
  decide +kernel

theorem h5n221_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p220).getD 1 []=h5p221.getD 1 [] := by
  decide +kernel

theorem h5n221_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p220).getD 2 []=h5p221.getD 2 [] := by
  decide +kernel

theorem h5n221_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p220).getD 3 []=h5p221.getD 3 [] := by
  decide +kernel

theorem h5n221_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p220).getD 4 []=h5p221.getD 4 [] := by
  decide +kernel

theorem h5n221_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p220).getD 5 []=h5p221.getD 5 [] := by
  decide +kernel

theorem h5n221_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p220).getD 6 []=h5p221.getD 6 [] := by
  decide +kernel

theorem h5n221_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p220).getD 7 []=h5p221.getD 7 [] := by
  decide +kernel

theorem h5n221_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p220).getD 8 []=h5p221.getD 8 [] := by
  decide +kernel

theorem h5n221_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p220).getD 9 []=h5p221.getD 9 [] := by
  decide +kernel

theorem h5n221_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p220).getD 10 []=h5p221.getD 10 [] := by
  decide +kernel

theorem h5n221_arithmetic : BiPoly.mul h5p6 h5p220=h5p221 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p220).getD j.val []=h5p221.getD j.val [] :=
      (fun j => Fin.cases h5n221_arithmetic_row0 (fun j => Fin.cases h5n221_arithmetic_row1 (fun j => Fin.cases h5n221_arithmetic_row2 (fun j => Fin.cases h5n221_arithmetic_row3 (fun j => Fin.cases h5n221_arithmetic_row4 (fun j => Fin.cases h5n221_arithmetic_row5 (fun j => Fin.cases h5n221_arithmetic_row6 (fun j => Fin.cases h5n221_arithmetic_row7 (fun j => Fin.cases h5n221_arithmetic_row8 (fun j => Fin.cases h5n221_arithmetic_row9 (fun j => Fin.cases h5n221_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n221 : h5e221.toBi mapPolyEnv=h5p221 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e220.toBi mapPolyEnv)=h5p221
  rw [h5n6, h5n220]
  exact h5n221_arithmetic

#print axioms h5n221_arithmetic
end StackSorting.RationalLift
