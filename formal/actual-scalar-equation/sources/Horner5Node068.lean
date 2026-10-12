import BivariateRowEquality
import Horner5Base
import Horner5Node067
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p68 : BiPoly.Poly := [[(Int.ofNat 25808544000), (Int.ofNat 25413056640), (Int.negSucc 272283638399), (Int.ofNat 107799465600), (Int.ofNat 92414805120)], [(Int.negSucc 138104386559), (Int.negSucc 81586524671), (Int.ofNat 1451011332096), (Int.negSucc 816433572095), (Int.negSucc 318788573183), (Int.ofNat 41637141504)], [(Int.ofNat 310648841280), (Int.ofNat 102451874976), (Int.negSucc 3094987905215), (Int.ofNat 1765694321856), (Int.ofNat 355524016896), (Int.negSucc 6681820895), (Int.ofNat 4421693952)], [(Int.negSucc 379987796159), (Int.negSucc 93794311583), (Int.ofNat 3346307969184), (Int.negSucc 822366972575), (Int.negSucc 476666702495), (Int.negSucc 229662840383), (Int.ofNat 15964079040)], [(Int.ofNat 272474499840), (Int.ofNat 112972081152), (Int.negSucc 1798703528735), (Int.negSucc 1861112346719), (Int.ofNat 912126237312), (Int.ofNat 247502476704), (Int.negSucc 13868444255)], [(Int.negSucc 114398760959), (Int.negSucc 111233610239), (Int.ofNat 225247187232), (Int.ofNat 2904210303552), (Int.negSucc 472189898687), (Int.negSucc 65763748703), (Int.negSucc 51560107391)], [(Int.ofNat 26047512000), (Int.ofNat 59517602400), (Int.ofNat 257642354400), (Int.negSucc 1598245594463), (Int.negSucc 625820492831), (Int.ofNat 55333346688), (Int.ofNat 42376735872)], [(Int.negSucc 2488453439), (Int.negSucc 15161171039), (Int.negSucc 136445897855), (Int.ofNat 299121732576), (Int.ofNat 808047923328), (Int.ofNat 1266153984), (Int.ofNat 13979602368)], [(Int.ofNat 0), (Int.ofNat 1421002368), (Int.ofNat 22819797504), (Int.ofNat 36471965184), (Int.negSucc 303496649855), (Int.negSucc 94202343935), (Int.negSucc 17793992447)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 607670207), (Int.negSucc 15061881599), (Int.ofNat 29152472256), (Int.ofNat 60589060992), (Int.ofNat 3498871680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 209340288), (Int.ofNat 2870850816), (Int.negSucc 10496615039)]]

theorem h5n68_arithmetic_row0 :
    (BiPoly.mul h5p6 h5p67).getD 0 []=h5p68.getD 0 [] := by
  decide +kernel

theorem h5n68_arithmetic_row1 :
    (BiPoly.mul h5p6 h5p67).getD 1 []=h5p68.getD 1 [] := by
  decide +kernel

theorem h5n68_arithmetic_row2 :
    (BiPoly.mul h5p6 h5p67).getD 2 []=h5p68.getD 2 [] := by
  decide +kernel

theorem h5n68_arithmetic_row3 :
    (BiPoly.mul h5p6 h5p67).getD 3 []=h5p68.getD 3 [] := by
  decide +kernel

theorem h5n68_arithmetic_row4 :
    (BiPoly.mul h5p6 h5p67).getD 4 []=h5p68.getD 4 [] := by
  decide +kernel

theorem h5n68_arithmetic_row5 :
    (BiPoly.mul h5p6 h5p67).getD 5 []=h5p68.getD 5 [] := by
  decide +kernel

theorem h5n68_arithmetic_row6 :
    (BiPoly.mul h5p6 h5p67).getD 6 []=h5p68.getD 6 [] := by
  decide +kernel

theorem h5n68_arithmetic_row7 :
    (BiPoly.mul h5p6 h5p67).getD 7 []=h5p68.getD 7 [] := by
  decide +kernel

theorem h5n68_arithmetic_row8 :
    (BiPoly.mul h5p6 h5p67).getD 8 []=h5p68.getD 8 [] := by
  decide +kernel

theorem h5n68_arithmetic_row9 :
    (BiPoly.mul h5p6 h5p67).getD 9 []=h5p68.getD 9 [] := by
  decide +kernel

theorem h5n68_arithmetic_row10 :
    (BiPoly.mul h5p6 h5p67).getD 10 []=h5p68.getD 10 [] := by
  decide +kernel

theorem h5n68_arithmetic : BiPoly.mul h5p6 h5p67=h5p68 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<11 at hk
    have hf : ∀ j : Fin 11, (BiPoly.mul h5p6 h5p67).getD j.val []=h5p68.getD j.val [] :=
      (fun j => Fin.cases h5n68_arithmetic_row0 (fun j => Fin.cases h5n68_arithmetic_row1 (fun j => Fin.cases h5n68_arithmetic_row2 (fun j => Fin.cases h5n68_arithmetic_row3 (fun j => Fin.cases h5n68_arithmetic_row4 (fun j => Fin.cases h5n68_arithmetic_row5 (fun j => Fin.cases h5n68_arithmetic_row6 (fun j => Fin.cases h5n68_arithmetic_row7 (fun j => Fin.cases h5n68_arithmetic_row8 (fun j => Fin.cases h5n68_arithmetic_row9 (fun j => Fin.cases h5n68_arithmetic_row10 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n68 : h5e68.toBi mapPolyEnv=h5p68 := by
  change BiPoly.mul (h5e6.toBi mapPolyEnv) (h5e67.toBi mapPolyEnv)=h5p68
  rw [h5n6, h5n67]
  exact h5n68_arithmetic

#print axioms h5n68_arithmetic
end StackSorting.RationalLift
