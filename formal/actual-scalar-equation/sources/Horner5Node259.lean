import BivariateRowEquality
import Horner5Base
import Horner5Node258
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p259 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1567869048000), (Int.ofNat 7815319382880), (Int.ofNat 8448570306720), (Int.ofNat 5946083134560), (Int.negSucc 7483435659359), (Int.negSucc 11228398822079)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 13645106255519), (Int.negSucc 62185528810223), (Int.negSucc 50927084982143), (Int.negSucc 35238390779231), (Int.ofNat 61636881788928), (Int.ofNat 60045136404624), (Int.negSucc 2771646266015)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 53429428481040), (Int.ofNat 225494175776328), (Int.ofNat 147127610262960), (Int.ofNat 128946678347952), (Int.negSucc 190321911795887), (Int.negSucc 132485890593815), (Int.negSucc 21197543405615), (Int.ofNat 2018127721536)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 124157603516759), (Int.negSucc 496037967790355), (Int.negSucc 307446239344499), (Int.negSucc 351038414082383), (Int.ofNat 288785738001024), (Int.ofNat 187506535114764), (Int.ofNat 137002197341484), (Int.negSucc 16802449097255), (Int.ofNat 796449760128)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 190099390503600), (Int.ofNat 743594012000784), (Int.ofNat 566733971304180), (Int.ofNat 668762970136056), (Int.negSucc 141131337335351), (Int.negSucc 232013976441119), (Int.negSucc 262658675850443), (Int.ofNat 8117319638808), (Int.negSucc 679899224735), (Int.ofNat 72957950208)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 201214262950559), (Int.negSucc 807515044299359), (Int.negSucc 897974054958275), (Int.negSucc 895629062716559), (Int.negSucc 331423735205519), (Int.ofNat 229362312541608), (Int.ofNat 217402820000964), (Int.ofNat 94769290448856), (Int.negSucc 10748170428047), (Int.ofNat 279988656480)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 150128130780720), (Int.ofNat 655806880735416), (Int.ofNat 1102481772127200), (Int.ofNat 929386661669172), (Int.ofNat 846753526955088), (Int.negSucc 53973263709287), (Int.negSucc 56928587356151), (Int.negSucc 181105274438603), (Int.ofNat 10822366379304), (Int.negSucc 547018866719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 78905591889839), (Int.negSucc 401902661314007), (Int.negSucc 989686108501595), (Int.negSucc 856357253322335), (Int.negSucc 991943235399419), (Int.negSucc 282990960770795), (Int.negSucc 43163613859751), (Int.ofNat 98103225749328), (Int.ofNat 31267254658212), (Int.negSucc 2207984327495)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 28615813410960), (Int.ofNat 183508118647416), (Int.ofNat 634712690504304), (Int.ofNat 722156638447044), (Int.ofNat 742804242549696), (Int.ofNat 519818345435160), (Int.ofNat 90627558257196), (Int.ofNat 34819641526212), (Int.negSucc 51315801280775), (Int.ofNat 1907132790096)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6817996007999), (Int.negSucc 60251407040303), (Int.negSucc 285243846185555), (Int.negSucc 497456896980671), (Int.negSucc 424006155477503), (Int.negSucc 462140078659631), (Int.negSucc 141251747941295), (Int.negSucc 66668418060191), (Int.ofNat 12222881743032), (Int.ofNat 4610741383152)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 960584448960), (Int.ofNat 13334441420160), (Int.ofNat 86771619302400), (Int.ofNat 246868772318100), (Int.ofNat 223310210032440), (Int.ofNat 245259714645000), (Int.ofNat 146005794354240), (Int.ofNat 42884389557288), (Int.ofNat 18020649486744), (Int.negSucc 4560449733359)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 60656052599), (Int.negSucc 1764963394451), (Int.negSucc 16692370165871), (Int.negSucc 80466605005967), (Int.negSucc 108335220665291), (Int.negSucc 87819960027239), (Int.negSucc 87644482679375), (Int.negSucc 27124001978975), (Int.negSucc 13525045415999), (Int.negSucc 632166157151)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 104624685720), (Int.ofNat 1765045043820), (Int.ofNat 15538020260868), (Int.ofNat 38790076320072), (Int.ofNat 27878267644992), (Int.ofNat 29608691168016), (Int.ofNat 15768365601600), (Int.ofNat 4466250993312), (Int.ofNat 1723231755072)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 71574713639), (Int.negSucc 1450986586703), (Int.negSucc 8204381049383), (Int.negSucc 9125179700687), (Int.negSucc 5798270171807), (Int.negSucc 5488478720063), (Int.negSucc 1389247886879), (Int.negSucc 539372426687)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 31785160104), (Int.ofNat 778726409976), (Int.ofNat 2123421232464), (Int.ofNat 978995828736), (Int.ofNat 907273516896), (Int.ofNat 392621756256), (Int.ofNat 47234767680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9989469503), (Int.negSucc 216146913695), (Int.negSucc 209532616991), (Int.negSucc 50060861567), (Int.negSucc 47234767679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1413046944), (Int.ofNat 23617383840)]]

theorem h5n259_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p258).getD 0 []=h5p259.getD 0 [] := by
  decide +kernel

theorem h5n259_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p258).getD 1 []=h5p259.getD 1 [] := by
  decide +kernel

theorem h5n259_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p258).getD 2 []=h5p259.getD 2 [] := by
  decide +kernel

theorem h5n259_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p258).getD 3 []=h5p259.getD 3 [] := by
  decide +kernel

theorem h5n259_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p258).getD 4 []=h5p259.getD 4 [] := by
  decide +kernel

theorem h5n259_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p258).getD 5 []=h5p259.getD 5 [] := by
  decide +kernel

theorem h5n259_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p258).getD 6 []=h5p259.getD 6 [] := by
  decide +kernel

theorem h5n259_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p258).getD 7 []=h5p259.getD 7 [] := by
  decide +kernel

theorem h5n259_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p258).getD 8 []=h5p259.getD 8 [] := by
  decide +kernel

theorem h5n259_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p258).getD 9 []=h5p259.getD 9 [] := by
  decide +kernel

theorem h5n259_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p258).getD 10 []=h5p259.getD 10 [] := by
  decide +kernel

theorem h5n259_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p258).getD 11 []=h5p259.getD 11 [] := by
  decide +kernel

theorem h5n259_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p258).getD 12 []=h5p259.getD 12 [] := by
  decide +kernel

theorem h5n259_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p258).getD 13 []=h5p259.getD 13 [] := by
  decide +kernel

theorem h5n259_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p258).getD 14 []=h5p259.getD 14 [] := by
  decide +kernel

theorem h5n259_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p258).getD 15 []=h5p259.getD 15 [] := by
  decide +kernel

theorem h5n259_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p258).getD 16 []=h5p259.getD 16 [] := by
  decide +kernel

theorem h5n259_arithmetic : BiPoly.mul h5p5 h5p258=h5p259 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p258).getD j.val []=h5p259.getD j.val [] :=
      (fun j => Fin.cases h5n259_arithmetic_row0 (fun j => Fin.cases h5n259_arithmetic_row1 (fun j => Fin.cases h5n259_arithmetic_row2 (fun j => Fin.cases h5n259_arithmetic_row3 (fun j => Fin.cases h5n259_arithmetic_row4 (fun j => Fin.cases h5n259_arithmetic_row5 (fun j => Fin.cases h5n259_arithmetic_row6 (fun j => Fin.cases h5n259_arithmetic_row7 (fun j => Fin.cases h5n259_arithmetic_row8 (fun j => Fin.cases h5n259_arithmetic_row9 (fun j => Fin.cases h5n259_arithmetic_row10 (fun j => Fin.cases h5n259_arithmetic_row11 (fun j => Fin.cases h5n259_arithmetic_row12 (fun j => Fin.cases h5n259_arithmetic_row13 (fun j => Fin.cases h5n259_arithmetic_row14 (fun j => Fin.cases h5n259_arithmetic_row15 (fun j => Fin.cases h5n259_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n259 : h5e259.toBi mapPolyEnv=h5p259 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e258.toBi mapPolyEnv)=h5p259
  rw [h5n5, h5n258]
  exact h5n259_arithmetic

#print axioms h5n259_arithmetic
end StackSorting.RationalLift
