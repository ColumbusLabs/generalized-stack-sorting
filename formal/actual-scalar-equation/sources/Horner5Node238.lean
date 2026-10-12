import BivariateRowEquality
import Horner5Base
import Horner5Node237
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p238 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 38712815999), (Int.negSucc 154258032959), (Int.negSucc 54348641279), (Int.negSucc 92468226239), (Int.ofNat 277244415360)], [(Int.ofNat 0), (Int.ofNat 207156579840), (Int.ofNat 743849526528), (Int.ofNat 55031581440), (Int.ofNat 379082519424), (Int.negSucc 1143732856319), (Int.ofNat 124911424512)], [(Int.ofNat 0), (Int.negSucc 465973261919), (Int.negSucc 1551597598223), (Int.negSucc 12310936847), (Int.negSucc 900297304847), (Int.ofNat 1531067386608), (Int.negSucc 39943085471), (Int.ofNat 13265081856)], [(Int.ofNat 0), (Int.ofNat 569981694240), (Int.ofNat 1850636550096), (Int.ofNat 532447696512), (Int.ofNat 1196180371440), (Int.negSucc 400319629055), (Int.negSucc 721031631263), (Int.ofNat 47892237120)], [(Int.ofNat 0), (Int.negSucc 408711749759), (Int.negSucc 1395593371007), (Int.negSucc 1488724819919), (Int.negSucc 856948618079), (Int.negSucc 1086893102879), (Int.ofNat 948592140624), (Int.negSucc 41605332767)], [(Int.ofNat 0), (Int.ofNat 171598141440), (Int.ofNat 681644839680), (Int.ofNat 1707063738192), (Int.ofNat 552844232208), (Int.ofNat 1341122140944), (Int.negSucc 90086761151), (Int.negSucc 154680322175)], [(Int.ofNat 0), (Int.negSucc 39071267999), (Int.negSucc 206490207599), (Int.negSucc 1005934154399), (Int.negSucc 598037990543), (Int.negSucc 664533471455), (Int.negSucc 488736237887), (Int.ofNat 127130207616)], [(Int.ofNat 0), (Int.ofNat 3732680160), (Int.ofNat 33939797040), (Int.ofNat 306488237904), (Int.ofNat 470782114848), (Int.ofNat 187485438240), (Int.ofNat 322280874144), (Int.ofNat 41938807104)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2131503551), (Int.negSucc 40624206911), (Int.negSucc 176580568511), (Int.negSucc 74496730751), (Int.negSucc 76717644479), (Int.negSucc 53381977343)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 911505312), (Int.ofNat 25327338336), (Int.ofNat 32253306624), (Int.ofNat 5876328384), (Int.ofNat 10496615040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 314010431), (Int.negSucc 5248307519)]]

theorem h5n238_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p237).getD 0 []=h5p238.getD 0 [] := by
  decide +kernel

theorem h5n238_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p237).getD 1 []=h5p238.getD 1 [] := by
  decide +kernel

theorem h5n238_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p237).getD 2 []=h5p238.getD 2 [] := by
  decide +kernel

theorem h5n238_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p237).getD 3 []=h5p238.getD 3 [] := by
  decide +kernel

theorem h5n238_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p237).getD 4 []=h5p238.getD 4 [] := by
  decide +kernel

theorem h5n238_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p237).getD 5 []=h5p238.getD 5 [] := by
  decide +kernel

theorem h5n238_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p237).getD 6 []=h5p238.getD 6 [] := by
  decide +kernel

theorem h5n238_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p237).getD 7 []=h5p238.getD 7 [] := by
  decide +kernel

theorem h5n238_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p237).getD 8 []=h5p238.getD 8 [] := by
  decide +kernel

theorem h5n238_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p237).getD 9 []=h5p238.getD 9 [] := by
  decide +kernel

theorem h5n238_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p237).getD 10 []=h5p238.getD 10 [] := by
  decide +kernel

theorem h5n238_arithmetic : BiPoly.mul h5p6 h5p237=h5p238 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p237).getD j.val []=h5p238.getD j.val [] :=
      (fun j => Fin.cases h5n238_arithmetic_row0 (fun j => Fin.cases h5n238_arithmetic_row1 (fun j => Fin.cases h5n238_arithmetic_row2 (fun j => Fin.cases h5n238_arithmetic_row3 (fun j => Fin.cases h5n238_arithmetic_row4 (fun j => Fin.cases h5n238_arithmetic_row5 (fun j => Fin.cases h5n238_arithmetic_row6 (fun j => Fin.cases h5n238_arithmetic_row7 (fun j => Fin.cases h5n238_arithmetic_row8 (fun j => Fin.cases h5n238_arithmetic_row9 (fun j => Fin.cases h5n238_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n238 : h5e238.toBi mapPolyEnv=h5p238 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e237.toBi mapPolyEnv)=h5p238
  rw [h5n6, h5n237]
  exact h5n238_arithmetic

#print axioms h5n238_arithmetic
end StackSorting.RationalLift
