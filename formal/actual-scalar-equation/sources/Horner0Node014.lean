import BivariateRowEquality
import Horner0Base
import Horner0Node013
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p14 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 223030771369550244), (Int.ofNat 1149498903029468976), (Int.negSucc 833098658712605063), (Int.negSucc 5963751142081624079), (Int.ofNat 6003253594651364100)], [(Int.ofNat 0), (Int.negSucc 2178334431594470663), (Int.negSucc 11945261000713951007), (Int.ofNat 5137152899534448336), (Int.ofNat 58378754758406330880), (Int.negSucc 54305326397337668423), (Int.ofNat 3287920527314105760)], [(Int.ofNat 0), (Int.ofNat 10343839502852964108), (Int.ofNat 55480955123809834776), (Int.negSucc 16282605783779592623), (Int.negSucc 241070439865637490911), (Int.ofNat 205201309735243555380), (Int.negSucc 14990971893416373383), (Int.ofNat 433503770703420384)], [(Int.ofNat 0), (Int.negSucc 31546823092063652867), (Int.negSucc 154000948540093464011), (Int.ofNat 44992243483580588136), (Int.ofNat 531198109925536822968), (Int.negSucc 380786300070657191603), (Int.ofNat 4412808231682352148), (Int.ofNat 521141147239118832), (Int.negSucc 4569466418183039)], [(Int.ofNat 0), (Int.ofNat 68681623176688651348), (Int.ofNat 285158689535625058972), (Int.negSucc 108515250492865386875), (Int.negSucc 622494047135958145015), (Int.ofNat 241238027016833178848), (Int.ofNat 108034035292098025964), (Int.negSucc 7155621546347366755), (Int.ofNat 166603951793238432), (Int.ofNat 11595114625600)], [(Int.ofNat 0), (Int.negSucc 112317831677089832371), (Int.negSucc 368392895781532839655), (Int.ofNat 167619596086184370976), (Int.ofNat 246890490936009135320), (Int.ofNat 363752189942677788044), (Int.negSucc 278837205579514264991), (Int.ofNat 6755688644967266704), (Int.ofNat 276189916785237856), (Int.negSucc 841464533405759)], [(Int.ofNat 0), (Int.ofNat 141580534201713555613), (Int.ofNat 334708062515606980746), (Int.negSucc 102418319075225206876), (Int.ofNat 271827923277157345364), (Int.negSucc 849334411454018088696), (Int.ofNat 236809954128120741050), (Int.ofNat 27643000240310550029), (Int.negSucc 1593024846890205663), (Int.ofNat 13856986938060784)], [(Int.ofNat 0), (Int.negSucc 139121904191928521709), (Int.negSucc 210495951945845142053), (Int.negSucc 112340013803797862455), (Int.negSucc 375788526468044280579), (Int.ofNat 579556435986317376190), (Int.ofNat 105250237464863381614), (Int.negSucc 65953187883795838411), (Int.negSucc 222053362689561967), (Int.ofNat 53711020331095392)], [(Int.ofNat 0), (Int.ofNat 106685253390978844891), (Int.ofNat 91677798951330119810), (Int.ofNat 293716597259997286098), (Int.ofNat 121515061785996661590), (Int.ofNat 76666653836442168351), (Int.negSucc 353428037360445995769), (Int.ofNat 34846277919806143252), (Int.ofNat 5753108504711856470), (Int.negSucc 49807682161872355)], [(Int.ofNat 0), (Int.negSucc 63403616268900607099), (Int.negSucc 36169301247421170579), (Int.negSucc 282544993974757249535), (Int.ofNat 33169784754225607808), (Int.negSucc 347100238184740019263), (Int.ofNat 222647622975606137160), (Int.ofNat 39175893382077435756), (Int.negSucc 4888823555753868547), (Int.negSucc 180385960569305699)], [(Int.ofNat 0), (Int.ofNat 28789423456110416667), (Int.ofNat 25285254693284047272), (Int.ofNat 148362927171596538916), (Int.ofNat 13993177596279927078), (Int.ofNat 194582991683125314187), (Int.ofNat 24225058579973154346), (Int.negSucc 55763366617709371480), (Int.negSucc 3494840624428849749), (Int.ofNat 166953027179256561)], [(Int.ofNat 0), (Int.negSucc 9767155590886151033), (Int.negSucc 21182106193270026405), (Int.negSucc 40952327307458726085), (Int.negSucc 66123738508607363413), (Int.negSucc 30205843905009933103), (Int.negSucc 95990782214983070007), (Int.ofNat 14583817649098788718), (Int.ofNat 6338681745312455586), (Int.ofNat 154397375268482916)], [(Int.ofNat 0), (Int.ofNat 2394692120615956957), (Int.ofNat 12533363074935228070), (Int.ofNat 3495666150998170947), (Int.ofNat 48353822134637977886), (Int.negSucc 5699747138114930753), (Int.ofNat 46770220206575080652), (Int.ofNat 12686873286503671855), (Int.negSucc 1696561301208686759), (Int.negSucc 209753320605431111)], [(Int.ofNat 0), (Int.negSucc 403225196026214027), (Int.negSucc 4850167544134567815), (Int.ofNat 222034139988060488), (Int.negSucc 16139539512839691899), (Int.negSucc 1982074149921987543), (Int.negSucc 7996143217375637963), (Int.negSucc 10205660112457940519), (Int.negSucc 1474520886821155571), (Int.ofNat 8437212311873400)], [(Int.ofNat 0), (Int.ofNat 42933713678619676), (Int.ofNat 1217607118545848698), (Int.ofNat 726747311243115295), (Int.ofNat 2080202452263999618), (Int.ofNat 3513053667404470419), (Int.negSucc 530915330087739887), (Int.ofNat 2761704735586216776), (Int.ofNat 1101629223584580960), (Int.ofNat 75354439522010436)], [(Int.ofNat 0), (Int.negSucc 2499022664954351), (Int.negSucc 190583517109157219), (Int.negSucc 514181042036365337), (Int.ofNat 312654709148114010), (Int.negSucc 1312180581350898251), (Int.ofNat 380202567438389832), (Int.negSucc 252835366557083039), (Int.negSucc 263315934157883903), (Int.negSucc 35655691885128575)], [(Int.ofNat 0), (Int.ofNat 59137145844624), (Int.ofNat 16551765319604904), (Int.ofNat 148107532188912273), (Int.negSucc 164137430252418407), (Int.ofNat 228643415762449104), (Int.negSucc 48433424379963263), (Int.negSucc 14156113588546823), (Int.ofNat 20653338438254592), (Int.ofNat 5096493263913984)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 565911365873471), (Int.negSucc 21629267810962847), (Int.ofNat 25922628599974956), (Int.negSucc 18256309466661719), (Int.ofNat 1418079525622272), (Int.ofNat 3292637891492736)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1353868492682304), (Int.negSucc 1697057217683423), (Int.ofNat 531809997732036)]]

theorem h0n14_arithmetic_row0 :
    (BiPoly.mul h0p12 h0p13).getD 0 []=h0p14.getD 0 [] := by
  decide +kernel

theorem h0n14_arithmetic_row1 :
    (BiPoly.mul h0p12 h0p13).getD 1 []=h0p14.getD 1 [] := by
  decide +kernel

theorem h0n14_arithmetic_row2 :
    (BiPoly.mul h0p12 h0p13).getD 2 []=h0p14.getD 2 [] := by
  decide +kernel

theorem h0n14_arithmetic_row3 :
    (BiPoly.mul h0p12 h0p13).getD 3 []=h0p14.getD 3 [] := by
  decide +kernel

theorem h0n14_arithmetic_row4 :
    (BiPoly.mul h0p12 h0p13).getD 4 []=h0p14.getD 4 [] := by
  decide +kernel

theorem h0n14_arithmetic_row5 :
    (BiPoly.mul h0p12 h0p13).getD 5 []=h0p14.getD 5 [] := by
  decide +kernel

theorem h0n14_arithmetic_row6 :
    (BiPoly.mul h0p12 h0p13).getD 6 []=h0p14.getD 6 [] := by
  decide +kernel

theorem h0n14_arithmetic_row7 :
    (BiPoly.mul h0p12 h0p13).getD 7 []=h0p14.getD 7 [] := by
  decide +kernel

theorem h0n14_arithmetic_row8 :
    (BiPoly.mul h0p12 h0p13).getD 8 []=h0p14.getD 8 [] := by
  decide +kernel

theorem h0n14_arithmetic_row9 :
    (BiPoly.mul h0p12 h0p13).getD 9 []=h0p14.getD 9 [] := by
  decide +kernel

theorem h0n14_arithmetic_row10 :
    (BiPoly.mul h0p12 h0p13).getD 10 []=h0p14.getD 10 [] := by
  decide +kernel

theorem h0n14_arithmetic_row11 :
    (BiPoly.mul h0p12 h0p13).getD 11 []=h0p14.getD 11 [] := by
  decide +kernel

theorem h0n14_arithmetic_row12 :
    (BiPoly.mul h0p12 h0p13).getD 12 []=h0p14.getD 12 [] := by
  decide +kernel

theorem h0n14_arithmetic_row13 :
    (BiPoly.mul h0p12 h0p13).getD 13 []=h0p14.getD 13 [] := by
  decide +kernel

theorem h0n14_arithmetic_row14 :
    (BiPoly.mul h0p12 h0p13).getD 14 []=h0p14.getD 14 [] := by
  decide +kernel

theorem h0n14_arithmetic_row15 :
    (BiPoly.mul h0p12 h0p13).getD 15 []=h0p14.getD 15 [] := by
  decide +kernel

theorem h0n14_arithmetic_row16 :
    (BiPoly.mul h0p12 h0p13).getD 16 []=h0p14.getD 16 [] := by
  decide +kernel

theorem h0n14_arithmetic_row17 :
    (BiPoly.mul h0p12 h0p13).getD 17 []=h0p14.getD 17 [] := by
  decide +kernel

theorem h0n14_arithmetic_row18 :
    (BiPoly.mul h0p12 h0p13).getD 18 []=h0p14.getD 18 [] := by
  decide +kernel

theorem h0n14_arithmetic : BiPoly.mul h0p12 h0p13=h0p14 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p12 h0p13).getD j.val []=h0p14.getD j.val [] :=
      (fun j => Fin.cases h0n14_arithmetic_row0 (fun j => Fin.cases h0n14_arithmetic_row1 (fun j => Fin.cases h0n14_arithmetic_row2 (fun j => Fin.cases h0n14_arithmetic_row3 (fun j => Fin.cases h0n14_arithmetic_row4 (fun j => Fin.cases h0n14_arithmetic_row5 (fun j => Fin.cases h0n14_arithmetic_row6 (fun j => Fin.cases h0n14_arithmetic_row7 (fun j => Fin.cases h0n14_arithmetic_row8 (fun j => Fin.cases h0n14_arithmetic_row9 (fun j => Fin.cases h0n14_arithmetic_row10 (fun j => Fin.cases h0n14_arithmetic_row11 (fun j => Fin.cases h0n14_arithmetic_row12 (fun j => Fin.cases h0n14_arithmetic_row13 (fun j => Fin.cases h0n14_arithmetic_row14 (fun j => Fin.cases h0n14_arithmetic_row15 (fun j => Fin.cases h0n14_arithmetic_row16 (fun j => Fin.cases h0n14_arithmetic_row17 (fun j => Fin.cases h0n14_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n14 : h0e14.toBi mapPolyEnv=h0p14 := by
  change BiPoly.mul (h0e12.toBi mapPolyEnv) (h0e13.toBi mapPolyEnv)=h0p14
  rw [h0n12, h0n13]
  exact h0n14_arithmetic

#print axioms h0n14_arithmetic
end StackSorting.RationalLift
