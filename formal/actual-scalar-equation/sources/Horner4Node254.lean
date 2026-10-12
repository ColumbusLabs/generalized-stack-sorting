import BivariateRowEquality
import Horner4Base
import Horner4Node253
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p254 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 7556181407), (Int.negSucc 34584613631), (Int.ofNat 257959008), (Int.ofNat 78404921280)], [(Int.ofNat 0), (Int.ofNat 36900491424), (Int.ofNat 181058569728), (Int.ofNat 42535165344), (Int.negSucc 333224623679), (Int.ofNat 21470786304)], [(Int.ofNat 0), (Int.negSucc 85120815391), (Int.negSucc 366929698975), (Int.negSucc 130924037823), (Int.ofNat 523025940128), (Int.negSucc 3810996543), (Int.negSucc 108965119)], [(Int.ofNat 0), (Int.ofNat 118709886512), (Int.ofNat 371460110096), (Int.ofNat 203504117328), (Int.negSucc 193724850767), (Int.negSucc 127166557983), (Int.ofNat 3953832576)], [(Int.ofNat 0), (Int.negSucc 104287862927), (Int.negSucc 215014668607), (Int.negSucc 210310609711), (Int.negSucc 299176614719), (Int.ofNat 194688904544), (Int.ofNat 6622474304)], [(Int.ofNat 0), (Int.ofNat 56076833680), (Int.ofNat 96357696544), (Int.ofNat 140240255792), (Int.ofNat 334328916880), (Int.negSucc 24709070575), (Int.negSucc 12076229279)], [(Int.ofNat 0), (Int.negSucc 17199051311), (Int.negSucc 48130095855), (Int.negSucc 63975488895), (Int.negSucc 118624330223), (Int.negSucc 92658495039), (Int.negSucc 2911688639)], [(Int.ofNat 0), (Int.ofNat 2599740512), (Int.ofNat 20179054832), (Int.ofNat 24614357648), (Int.ofNat 10721824224), (Int.ofNat 46818418656), (Int.ofNat 7991220672)], [(Int.ofNat 0), (Int.negSucc 123041087), (Int.negSucc 5025857231), (Int.negSucc 6919117055), (Int.ofNat 2966433600), (Int.negSucc 5771100671), (Int.negSucc 2284471295)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 588719232), (Int.ofNat 808462368), (Int.negSucc 737952191)]]

theorem h4n254_arithmetic_row0 :
    (BiPoly.mul h4p7 h4p253).getD 0 []=h4p254.getD 0 [] := by
  decide +kernel

theorem h4n254_arithmetic_row1 :
    (BiPoly.mul h4p7 h4p253).getD 1 []=h4p254.getD 1 [] := by
  decide +kernel

theorem h4n254_arithmetic_row2 :
    (BiPoly.mul h4p7 h4p253).getD 2 []=h4p254.getD 2 [] := by
  decide +kernel

theorem h4n254_arithmetic_row3 :
    (BiPoly.mul h4p7 h4p253).getD 3 []=h4p254.getD 3 [] := by
  decide +kernel

theorem h4n254_arithmetic_row4 :
    (BiPoly.mul h4p7 h4p253).getD 4 []=h4p254.getD 4 [] := by
  decide +kernel

theorem h4n254_arithmetic_row5 :
    (BiPoly.mul h4p7 h4p253).getD 5 []=h4p254.getD 5 [] := by
  decide +kernel

theorem h4n254_arithmetic_row6 :
    (BiPoly.mul h4p7 h4p253).getD 6 []=h4p254.getD 6 [] := by
  decide +kernel

theorem h4n254_arithmetic_row7 :
    (BiPoly.mul h4p7 h4p253).getD 7 []=h4p254.getD 7 [] := by
  decide +kernel

theorem h4n254_arithmetic_row8 :
    (BiPoly.mul h4p7 h4p253).getD 8 []=h4p254.getD 8 [] := by
  decide +kernel

theorem h4n254_arithmetic_row9 :
    (BiPoly.mul h4p7 h4p253).getD 9 []=h4p254.getD 9 [] := by
  decide +kernel

theorem h4n254_arithmetic : BiPoly.mul h4p7 h4p253=h4p254 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<10 at hk
    have hf : ∀ j : Fin 10, (BiPoly.mul h4p7 h4p253).getD j.val []=h4p254.getD j.val [] :=
      (fun j => Fin.cases h4n254_arithmetic_row0 (fun j => Fin.cases h4n254_arithmetic_row1 (fun j => Fin.cases h4n254_arithmetic_row2 (fun j => Fin.cases h4n254_arithmetic_row3 (fun j => Fin.cases h4n254_arithmetic_row4 (fun j => Fin.cases h4n254_arithmetic_row5 (fun j => Fin.cases h4n254_arithmetic_row6 (fun j => Fin.cases h4n254_arithmetic_row7 (fun j => Fin.cases h4n254_arithmetic_row8 (fun j => Fin.cases h4n254_arithmetic_row9 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n254 : h4e254.toBi mapPolyEnv=h4p254 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e253.toBi mapPolyEnv)=h4p254
  rw [h4n7, h4n253]
  exact h4n254_arithmetic

#print axioms h4n254_arithmetic
end StackSorting.RationalLift
