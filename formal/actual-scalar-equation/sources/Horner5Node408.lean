import BivariateRowEquality
import Horner5Base
import Horner5Node407
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p408 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1238810112000), (Int.ofNat 6871897854720), (Int.negSucc 1000402151039), (Int.negSucc 37366914971519), (Int.negSucc 2177250295679), (Int.ofNat 28556174782080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10642239146879), (Int.negSucc 50849260612415), (Int.ofNat 37589710279680), (Int.ofNat 290363055028992), (Int.negSucc 54809996948351), (Int.negSucc 197007130660031), (Int.ofNat 22107357236736)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 41070627227520), (Int.ofNat 165616963421184), (Int.negSucc 226385441010719), (Int.negSucc 960048671296319), (Int.ofNat 310046587615872), (Int.ofNat 520253433116352), (Int.negSucc 52106139946079), (Int.ofNat 5899676802048)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 93895311339359), (Int.negSucc 310651660485647), (Int.ofNat 640276672967568), (Int.ofNat 1816155220259232), (Int.negSucc 464061471632639), (Int.negSucc 755317157954255), (Int.negSucc 165165971501231), (Int.ofNat 17059521284928), (Int.ofNat 608717961216)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 141146105086080), (Int.ofNat 367046713734624), (Int.negSucc 1065959297874287), (Int.negSucc 2283021763424639), (Int.negSucc 354209871172895), (Int.ofNat 855755858994912), (Int.ofNat 717456659978448), (Int.negSucc 94434413565311), (Int.ofNat 6020078412672), (Int.ofNat 17686775808)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 146323646312639), (Int.negSucc 277422310168031), (Int.ofNat 1151010476626896), (Int.ofNat 2215562916087072), (Int.ofNat 2071734974860224), (Int.negSucc 803260181532095), (Int.negSucc 979471703412431), (Int.negSucc 21845838353855), (Int.ofNat 1535403556416), (Int.ofNat 408748444416)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 106626737784960), (Int.ofNat 124622692887744), (Int.negSucc 857347373596031), (Int.negSucc 1949039742019247), (Int.negSucc 3128610931805375), (Int.ofNat 267865317984), (Int.ofNat 646260464368128), (Int.ofNat 411967506829584), (Int.negSucc 46583492706335), (Int.ofNat 1614207007488)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 54557025275519), (Int.negSucc 19877144686079), (Int.ofNat 472922936489040), (Int.ofNat 1623470193104640), (Int.ofNat 2686365316112016), (Int.ofNat 1440607943858448), (Int.negSucc 208240060770815), (Int.negSucc 513364402614815), (Int.ofNat 9257918154576), (Int.negSucc 551332405055)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 19189748530560), (Int.negSucc 12226325874431), (Int.negSucc 215615065221023), (Int.negSucc 1154902976970479), (Int.negSucc 1639996410801023), (Int.negSucc 2110399399915295), (Int.negSucc 222411627632303), (Int.ofNat 169932705578544), (Int.ofNat 119600467737888), (Int.negSucc 8057086308863)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4415641145279), (Int.ofNat 9402122608416), (Int.ofNat 89430753149136), (Int.ofNat 631467421688736), (Int.ofNat 909656658000384), (Int.ofNat 1505502538283520), (Int.ofNat 660788965153344), (Int.ofNat 94556263211136), (Int.negSucc 115239477894047), (Int.ofNat 907853463936)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 597917053440), (Int.negSucc 2996331273407), (Int.negSucc 32093552097887), (Int.negSucc 250535863587695), (Int.negSucc 509623417704863), (Int.negSucc 635905190096351), (Int.negSucc 701977516430399), (Int.negSucc 146054084449247), (Int.negSucc 1649075527583), (Int.ofNat 14368218989184)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 36082574879), (Int.ofNat 498028261392), (Int.ofNat 8398427082720), (Int.ofNat 69045995666592), (Int.ofNat 238266950873040), (Int.ofNat 207830770229952), (Int.ofNat 366298503883776), (Int.ofNat 146204062263936), (Int.ofNat 43349672455488), (Int.negSucc 7659706553855)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 35385668063), (Int.negSucc 1318194222191), (Int.negSucc 12342213100943), (Int.negSucc 75214621486367), (Int.negSucc 81161439801407), (Int.negSucc 94472712032255), (Int.negSucc 98454089186495), (Int.negSucc 23757275541887), (Int.negSucc 3951639710207)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 90349578144), (Int.ofNat 1242347745024), (Int.ofNat 13787410804704), (Int.ofNat 30200210290944), (Int.ofNat 13563914923584), (Int.ofNat 32282864779392), (Int.ofNat 10256950159488), (Int.ofNat 3538810321920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 49004209439), (Int.negSucc 1175043671135), (Int.negSucc 6480714581567), (Int.negSucc 3555201265919), (Int.negSucc 3467098297727), (Int.negSucc 3922879870079), (Int.negSucc 629796902399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 21117252096), (Int.ofNat 563505662592), (Int.ofNat 1046447247744), (Int.negSucc 151257818879), (Int.ofNat 629796902400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5652187775), (Int.negSucc 94469535359)]]

theorem h5n408_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p407).getD 0 []=h5p408.getD 0 [] := by
  decide +kernel

theorem h5n408_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p407).getD 1 []=h5p408.getD 1 [] := by
  decide +kernel

theorem h5n408_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p407).getD 2 []=h5p408.getD 2 [] := by
  decide +kernel

theorem h5n408_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p407).getD 3 []=h5p408.getD 3 [] := by
  decide +kernel

theorem h5n408_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p407).getD 4 []=h5p408.getD 4 [] := by
  decide +kernel

theorem h5n408_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p407).getD 5 []=h5p408.getD 5 [] := by
  decide +kernel

theorem h5n408_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p407).getD 6 []=h5p408.getD 6 [] := by
  decide +kernel

theorem h5n408_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p407).getD 7 []=h5p408.getD 7 [] := by
  decide +kernel

theorem h5n408_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p407).getD 8 []=h5p408.getD 8 [] := by
  decide +kernel

theorem h5n408_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p407).getD 9 []=h5p408.getD 9 [] := by
  decide +kernel

theorem h5n408_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p407).getD 10 []=h5p408.getD 10 [] := by
  decide +kernel

theorem h5n408_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p407).getD 11 []=h5p408.getD 11 [] := by
  decide +kernel

theorem h5n408_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p407).getD 12 []=h5p408.getD 12 [] := by
  decide +kernel

theorem h5n408_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p407).getD 13 []=h5p408.getD 13 [] := by
  decide +kernel

theorem h5n408_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p407).getD 14 []=h5p408.getD 14 [] := by
  decide +kernel

theorem h5n408_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p407).getD 15 []=h5p408.getD 15 [] := by
  decide +kernel

theorem h5n408_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p407).getD 16 []=h5p408.getD 16 [] := by
  decide +kernel

theorem h5n408_arithmetic : BiPoly.mul h5p34 h5p407=h5p408 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p407).getD j.val []=h5p408.getD j.val [] :=
      (fun j => Fin.cases h5n408_arithmetic_row0 (fun j => Fin.cases h5n408_arithmetic_row1 (fun j => Fin.cases h5n408_arithmetic_row2 (fun j => Fin.cases h5n408_arithmetic_row3 (fun j => Fin.cases h5n408_arithmetic_row4 (fun j => Fin.cases h5n408_arithmetic_row5 (fun j => Fin.cases h5n408_arithmetic_row6 (fun j => Fin.cases h5n408_arithmetic_row7 (fun j => Fin.cases h5n408_arithmetic_row8 (fun j => Fin.cases h5n408_arithmetic_row9 (fun j => Fin.cases h5n408_arithmetic_row10 (fun j => Fin.cases h5n408_arithmetic_row11 (fun j => Fin.cases h5n408_arithmetic_row12 (fun j => Fin.cases h5n408_arithmetic_row13 (fun j => Fin.cases h5n408_arithmetic_row14 (fun j => Fin.cases h5n408_arithmetic_row15 (fun j => Fin.cases h5n408_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n408 : h5e408.toBi mapPolyEnv=h5p408 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e407.toBi mapPolyEnv)=h5p408
  rw [h5n34, h5n407]
  exact h5n408_arithmetic

#print axioms h5n408_arithmetic
end StackSorting.RationalLift
