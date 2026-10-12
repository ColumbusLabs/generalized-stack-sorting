import BivariateRowEquality
import Horner2Base
import Horner2Node075
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p76 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 153012673512), (Int.ofNat 1771427140632), (Int.ofNat 3979069271352), (Int.negSucc 3990143819447), (Int.negSucc 6350798623679)], [(Int.ofNat 0), (Int.negSucc 1260110764403), (Int.negSucc 14588121619655), (Int.negSucc 32803954072919), (Int.ofNat 30598206861816), (Int.ofNat 36478455735132), (Int.negSucc 445452489503)], [(Int.ofNat 0), (Int.ofNat 4856424946632), (Int.ofNat 55006865333352), (Int.ofNat 117843865013232), (Int.negSucc 101938782923063), (Int.negSucc 87759154411631), (Int.negSucc 14566802079239), (Int.ofNat 1225548282816)], [(Int.ofNat 0), (Int.negSucc 11578442310143), (Int.negSucc 125443063178327), (Int.negSucc 243512910456839), (Int.ofNat 165091659019896), (Int.ofNat 113991684242664), (Int.ofNat 78938871174456), (Int.negSucc 7230152204015), (Int.ofNat 234380724864)], [(Int.ofNat 0), (Int.ofNat 18916108463066), (Int.ofNat 192923909055170), (Int.ofNat 324910499133492), (Int.negSucc 73941859692483), (Int.negSucc 108597547364749), (Int.negSucc 155417074787941), (Int.ofNat 1596573883760), (Int.ofNat 94060903200), (Int.negSucc 1198616319)], [(Int.ofNat 0), (Int.negSucc 22095065958863), (Int.negSucc 211825767546381), (Int.negSucc 305125916594235), (Int.negSucc 185328458007875), (Int.ofNat 106466202583708), (Int.ofNat 120974800573066), (Int.ofNat 43369944204652), (Int.negSucc 3155602169791), (Int.ofNat 43219745536)], [(Int.ofNat 0), (Int.ofNat 18693749905134), (Int.ofNat 171924374216356), (Int.ofNat 226335871915516), (Int.ofNat 373034630977596), (Int.negSucc 43970087199309), (Int.ofNat 2024170649840), (Int.negSucc 84018203758651), (Int.ofNat 1482842691808), (Int.ofNat 88942810624)], [(Int.ofNat 0), (Int.negSucc 11395493000963), (Int.negSucc 105471624340621), (Int.negSucc 153220485906197), (Int.negSucc 322636668296447), (Int.negSucc 107774201890343), (Int.negSucc 52825300088313), (Int.ofNat 43285600776394), (Int.ofNat 10134173386200), (Int.negSucc 342631479231)], [(Int.ofNat 0), (Int.ofNat 4902310865174), (Int.ofNat 49429379579848), (Int.ofNat 98778243967418), (Int.ofNat 160358360542906), (Int.ofNat 193142177723540), (Int.ofNat 36270179271930), (Int.ofNat 25635247175030), (Int.negSucc 14056533691713), (Int.negSucc 404115690383)], [(Int.ofNat 0), (Int.negSucc 1430387731043), (Int.negSucc 17605910284329), (Int.negSucc 54084243086153), (Int.negSucc 54581652253163), (Int.negSucc 134860485196615), (Int.negSucc 38329300766295), (Int.negSucc 35010915858105), (Int.ofNat 1747895835944), (Int.ofNat 828571543488)], [(Int.ofNat 0), (Int.ofNat 263383762186), (Int.ofNat 4643660279892), (Int.ofNat 22100473585864), (Int.ofNat 19626938763880), (Int.ofNat 45866840414972), (Int.ofNat 38104725874684), (Int.ofNat 14562796693080), (Int.ofNat 6109234787472), (Int.ofNat 52129056384)], [(Int.ofNat 0), (Int.negSucc 26490559123), (Int.negSucc 860940691793), (Int.negSucc 6211759186601), (Int.negSucc 8750893428207), (Int.negSucc 6961272164123), (Int.negSucc 18287592705239), (Int.negSucc 5283298510607), (Int.negSucc 3650612978159), (Int.negSucc 487415954303)], [(Int.ofNat 0), (Int.ofNat 999708840), (Int.ofNat 101748909822), (Int.ofNat 1124599695222), (Int.ofNat 3000743506470), (Int.ofNat 468521333088), (Int.ofNat 3759528319128), (Int.ofNat 2262763477656), (Int.ofNat 913072298040), (Int.ofNat 202135849920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5936853959), (Int.negSucc 119149364393), (Int.negSucc 597891798143), (Int.negSucc 209387267207), (Int.negSucc 158715635903), (Int.negSucc 513625649399), (Int.negSucc 170978112575), (Int.negSucc 20560241663)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5796085248), (Int.ofNat 57196340352), (Int.ofNat 79791054264), (Int.negSucc 50264424503), (Int.ofNat 37588245696), (Int.ofNat 20560241664)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1324618271), (Int.negSucc 9766749959), (Int.ofNat 6641569728)]]

theorem h2n76_arithmetic_row0 :
    (BiPoly.mul h2p4 h2p75).getD 0 []=h2p76.getD 0 [] := by
  decide +kernel

theorem h2n76_arithmetic_row1 :
    (BiPoly.mul h2p4 h2p75).getD 1 []=h2p76.getD 1 [] := by
  decide +kernel

theorem h2n76_arithmetic_row2 :
    (BiPoly.mul h2p4 h2p75).getD 2 []=h2p76.getD 2 [] := by
  decide +kernel

theorem h2n76_arithmetic_row3 :
    (BiPoly.mul h2p4 h2p75).getD 3 []=h2p76.getD 3 [] := by
  decide +kernel

theorem h2n76_arithmetic_row4 :
    (BiPoly.mul h2p4 h2p75).getD 4 []=h2p76.getD 4 [] := by
  decide +kernel

theorem h2n76_arithmetic_row5 :
    (BiPoly.mul h2p4 h2p75).getD 5 []=h2p76.getD 5 [] := by
  decide +kernel

theorem h2n76_arithmetic_row6 :
    (BiPoly.mul h2p4 h2p75).getD 6 []=h2p76.getD 6 [] := by
  decide +kernel

theorem h2n76_arithmetic_row7 :
    (BiPoly.mul h2p4 h2p75).getD 7 []=h2p76.getD 7 [] := by
  decide +kernel

theorem h2n76_arithmetic_row8 :
    (BiPoly.mul h2p4 h2p75).getD 8 []=h2p76.getD 8 [] := by
  decide +kernel

theorem h2n76_arithmetic_row9 :
    (BiPoly.mul h2p4 h2p75).getD 9 []=h2p76.getD 9 [] := by
  decide +kernel

theorem h2n76_arithmetic_row10 :
    (BiPoly.mul h2p4 h2p75).getD 10 []=h2p76.getD 10 [] := by
  decide +kernel

theorem h2n76_arithmetic_row11 :
    (BiPoly.mul h2p4 h2p75).getD 11 []=h2p76.getD 11 [] := by
  decide +kernel

theorem h2n76_arithmetic_row12 :
    (BiPoly.mul h2p4 h2p75).getD 12 []=h2p76.getD 12 [] := by
  decide +kernel

theorem h2n76_arithmetic_row13 :
    (BiPoly.mul h2p4 h2p75).getD 13 []=h2p76.getD 13 [] := by
  decide +kernel

theorem h2n76_arithmetic_row14 :
    (BiPoly.mul h2p4 h2p75).getD 14 []=h2p76.getD 14 [] := by
  decide +kernel

theorem h2n76_arithmetic_row15 :
    (BiPoly.mul h2p4 h2p75).getD 15 []=h2p76.getD 15 [] := by
  decide +kernel

theorem h2n76_arithmetic : BiPoly.mul h2p4 h2p75=h2p76 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h2p4 h2p75).getD j.val []=h2p76.getD j.val [] :=
      (fun j => Fin.cases h2n76_arithmetic_row0 (fun j => Fin.cases h2n76_arithmetic_row1 (fun j => Fin.cases h2n76_arithmetic_row2 (fun j => Fin.cases h2n76_arithmetic_row3 (fun j => Fin.cases h2n76_arithmetic_row4 (fun j => Fin.cases h2n76_arithmetic_row5 (fun j => Fin.cases h2n76_arithmetic_row6 (fun j => Fin.cases h2n76_arithmetic_row7 (fun j => Fin.cases h2n76_arithmetic_row8 (fun j => Fin.cases h2n76_arithmetic_row9 (fun j => Fin.cases h2n76_arithmetic_row10 (fun j => Fin.cases h2n76_arithmetic_row11 (fun j => Fin.cases h2n76_arithmetic_row12 (fun j => Fin.cases h2n76_arithmetic_row13 (fun j => Fin.cases h2n76_arithmetic_row14 (fun j => Fin.cases h2n76_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n76 : h2e76.toBi mapPolyEnv=h2p76 := by
  change BiPoly.mul (h2e4.toBi mapPolyEnv) (h2e75.toBi mapPolyEnv)=h2p76
  rw [h2n4, h2n75]
  exact h2n76_arithmetic

#print axioms h2n76_arithmetic
end StackSorting.RationalLift
