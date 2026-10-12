import BivariateRowEquality
import Horner0Base
import Horner0Node009
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p10 : BiPoly.Poly := [[(Int.ofNat 9141283140953904000), (Int.ofNat 50840821347566754240), (Int.negSucc 9848960896151125439), (Int.negSucc 225904475519601935039), (Int.ofNat 169822863762659553600)], [(Int.negSucc 84416049107132520959), (Int.negSucc 474083982399761004671), (Int.ofNat 49560525434501592768), (Int.ofNat 1988234218454184760320), (Int.negSucc 1560612656571865178687), (Int.ofNat 123018171890687481600)], [(Int.ofNat 367472218399010402400), (Int.ofNat 2008760912577243759600), (Int.negSucc 99367153651500825887), (Int.negSucc 7600179789344371159871), (Int.ofNat 5709288521479921326720), (Int.negSucc 578492224419927014639), (Int.ofNat 28842064299443621376)], [(Int.negSucc 999104607223726508639), (Int.negSucc 5113377971304524760239), (Int.negSucc 40967893366647733727), (Int.ofNat 15992100732436633757952), (Int.negSucc 9709011772991876439647), (Int.ofNat 196100419550204201328), (Int.negSucc 8197711315773423839), (Int.ofNat 2118755855265020928)], [(Int.ofNat 1888824757838570569440), (Int.ofNat 8749638768555028121616), (Int.ofNat 982286118437795249184), (Int.negSucc 19043548680093581726495), (Int.ofNat 3814038449159233686912), (Int.ofNat 3927099577733483214960), (Int.negSucc 373637837675530894751), (Int.ofNat 11542246104710229696), (Int.negSucc 11292431533194239)], [(Int.negSucc 2610738987860770943759), (Int.negSucc 10735252621161005275991), (Int.negSucc 3421718069823489442679), (Int.ofNat 10101251545994050570800), (Int.ofNat 14256343903166305601760), (Int.negSucc 9789387541488546009335), (Int.ofNat 577571882546146290984), (Int.negSucc 16109834099339362751), (Int.ofNat 368979135943047552)], [(Int.ofNat 2700432556573201758000), (Int.ofNat 9926497141898880549528), (Int.ofNat 6868531472951233664064), (Int.ofNat 4415627300361276891168), (Int.negSucc 26769458094586721783567), (Int.ofNat 7334796773349103152456), (Int.ofNat 1054327697308898019936), (Int.negSucc 91243742232345041807), (Int.ofNat 2201086570875735168)], [(Int.negSucc 2106775905245595977039), (Int.negSucc 7257470201147159585351), (Int.negSucc 9295325117063965387079), (Int.negSucc 12042080206104459688127), (Int.ofNat 17816442946008148885680), (Int.ofNat 5556001264476435865080), (Int.negSucc 3438740517568569302327), (Int.ofNat 130475834899278701760), (Int.ofNat 72868590713741184)], [(Int.ofNat 1236285659913753931920), (Int.ofNat 4385138714634725173080), (Int.ofNat 9047832326391381823728), (Int.ofNat 10232904639988289057328), (Int.ofNat 1441429482286776660624), (Int.negSucc 13974615569196016770311), (Int.ofNat 2347638136654333392432), (Int.ofNat 210097011031265193840), (Int.negSucc 11858941613450216735)], [(Int.negSucc 539051264465958346319), (Int.negSucc 2239013294584678571975), (Int.negSucc 6550908461519408190431), (Int.negSucc 5736130370401785578495), (Int.negSucc 10629082958356565712215), (Int.ofNat 8468231235580142026272), (Int.ofNat 1740330609393978238104), (Int.negSucc 490961946507837017903), (Int.negSucc 447596238077714231)], [(Int.ofNat 170606180277590307120), (Int.ofNat 950235556989362752296), (Int.ofNat 3573211530651297753960), (Int.ofNat 3119948548070670545400), (Int.ofNat 7706455958921519667744), (Int.ofNat 1032296455453308768000), (Int.negSucc 3294333777531263213879), (Int.ofNat 133088616513809706744), (Int.ofNat 26211428715162843504)], [(Int.negSucc 37652167698475196879), (Int.negSucc 319477148965710098567), (Int.negSucc 1459828119108494303207), (Int.negSucc 1932397974488199803183), (Int.negSucc 2724888468437151461423), (Int.negSucc 4023809994756270498335), (Int.ofNat 1271868353661709980720), (Int.ofNat 332530041429106850160), (Int.negSucc 11415835378758914927)], [(Int.ofNat 5401101242905664400), (Int.ofNat 80056703822624107992), (Int.ofNat 436788970233681085344), (Int.ofNat 1038859116182691192144), (Int.ofNat 614840166262055023776), (Int.ofNat 2207299160776979086416), (Int.ofNat 559267030293244553376), (Int.negSucc 273878179820073240047), (Int.negSucc 18200652703623899279)], [(Int.negSucc 439128066453369119), (Int.negSucc 13919687696170227167), (Int.negSucc 92114903049759971639), (Int.negSucc 390204718902182077775), (Int.negSucc 219140462300115503447), (Int.negSucc 518439684633831897695), (Int.negSucc 666894414663923334911), (Int.ofNat 5368525726947957792), (Int.ofNat 15322985251493410656)], [(Int.ofNat 14352282126325440), (Int.ofNat 1503155030866142544), (Int.ofNat 12912295424194732104), (Int.ofNat 94039573032289831032), (Int.ofNat 115570998898865627760), (Int.ofNat 38524854508641074304), (Int.ofNat 232048033122852174240), (Int.ofNat 75685202028395642592), (Int.ofNat 573352494230925504)], [(Int.ofNat 0), (Int.negSucc 76867597287836927), (Int.negSucc 1087280099026576415), (Int.negSucc 13464808435814779439), (Int.negSucc 38170866713427285551), (Int.negSucc 832646106680800607), (Int.negSucc 30144598194601860191), (Int.negSucc 35369956477456126847), (Int.negSucc 4319984661340613183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 42719054357655360), (Int.ofNat 963873762567159888), (Int.ofNat 6650758488007556208), (Int.ofNat 3041760553946668512), (Int.negSucc 1268995667555013119), (Int.ofNat 6374184486292522944), (Int.ofNat 1608049703591909568)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17976777888787199), (Int.negSucc 516755006859962303), (Int.negSucc 960649503751448063), (Int.ofNat 718105797172131264), (Int.negSucc 390797733329261567), (Int.negSucc 187337623156577279)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5776999386469632), (Int.ofNat 92934913411612224), (Int.negSucc 60515625604282559)]]

theorem h0n10_arithmetic_row0 :
    (BiPoly.mul h0p6 h0p9).getD 0 []=h0p10.getD 0 [] := by
  decide +kernel

theorem h0n10_arithmetic_row1 :
    (BiPoly.mul h0p6 h0p9).getD 1 []=h0p10.getD 1 [] := by
  decide +kernel

theorem h0n10_arithmetic_row2 :
    (BiPoly.mul h0p6 h0p9).getD 2 []=h0p10.getD 2 [] := by
  decide +kernel

theorem h0n10_arithmetic_row3 :
    (BiPoly.mul h0p6 h0p9).getD 3 []=h0p10.getD 3 [] := by
  decide +kernel

theorem h0n10_arithmetic_row4 :
    (BiPoly.mul h0p6 h0p9).getD 4 []=h0p10.getD 4 [] := by
  decide +kernel

theorem h0n10_arithmetic_row5 :
    (BiPoly.mul h0p6 h0p9).getD 5 []=h0p10.getD 5 [] := by
  decide +kernel

theorem h0n10_arithmetic_row6 :
    (BiPoly.mul h0p6 h0p9).getD 6 []=h0p10.getD 6 [] := by
  decide +kernel

theorem h0n10_arithmetic_row7 :
    (BiPoly.mul h0p6 h0p9).getD 7 []=h0p10.getD 7 [] := by
  decide +kernel

theorem h0n10_arithmetic_row8 :
    (BiPoly.mul h0p6 h0p9).getD 8 []=h0p10.getD 8 [] := by
  decide +kernel

theorem h0n10_arithmetic_row9 :
    (BiPoly.mul h0p6 h0p9).getD 9 []=h0p10.getD 9 [] := by
  decide +kernel

theorem h0n10_arithmetic_row10 :
    (BiPoly.mul h0p6 h0p9).getD 10 []=h0p10.getD 10 [] := by
  decide +kernel

theorem h0n10_arithmetic_row11 :
    (BiPoly.mul h0p6 h0p9).getD 11 []=h0p10.getD 11 [] := by
  decide +kernel

theorem h0n10_arithmetic_row12 :
    (BiPoly.mul h0p6 h0p9).getD 12 []=h0p10.getD 12 [] := by
  decide +kernel

theorem h0n10_arithmetic_row13 :
    (BiPoly.mul h0p6 h0p9).getD 13 []=h0p10.getD 13 [] := by
  decide +kernel

theorem h0n10_arithmetic_row14 :
    (BiPoly.mul h0p6 h0p9).getD 14 []=h0p10.getD 14 [] := by
  decide +kernel

theorem h0n10_arithmetic_row15 :
    (BiPoly.mul h0p6 h0p9).getD 15 []=h0p10.getD 15 [] := by
  decide +kernel

theorem h0n10_arithmetic_row16 :
    (BiPoly.mul h0p6 h0p9).getD 16 []=h0p10.getD 16 [] := by
  decide +kernel

theorem h0n10_arithmetic_row17 :
    (BiPoly.mul h0p6 h0p9).getD 17 []=h0p10.getD 17 [] := by
  decide +kernel

theorem h0n10_arithmetic_row18 :
    (BiPoly.mul h0p6 h0p9).getD 18 []=h0p10.getD 18 [] := by
  decide +kernel

theorem h0n10_arithmetic : BiPoly.mul h0p6 h0p9=h0p10 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p6 h0p9).getD j.val []=h0p10.getD j.val [] :=
      (fun j => Fin.cases h0n10_arithmetic_row0 (fun j => Fin.cases h0n10_arithmetic_row1 (fun j => Fin.cases h0n10_arithmetic_row2 (fun j => Fin.cases h0n10_arithmetic_row3 (fun j => Fin.cases h0n10_arithmetic_row4 (fun j => Fin.cases h0n10_arithmetic_row5 (fun j => Fin.cases h0n10_arithmetic_row6 (fun j => Fin.cases h0n10_arithmetic_row7 (fun j => Fin.cases h0n10_arithmetic_row8 (fun j => Fin.cases h0n10_arithmetic_row9 (fun j => Fin.cases h0n10_arithmetic_row10 (fun j => Fin.cases h0n10_arithmetic_row11 (fun j => Fin.cases h0n10_arithmetic_row12 (fun j => Fin.cases h0n10_arithmetic_row13 (fun j => Fin.cases h0n10_arithmetic_row14 (fun j => Fin.cases h0n10_arithmetic_row15 (fun j => Fin.cases h0n10_arithmetic_row16 (fun j => Fin.cases h0n10_arithmetic_row17 (fun j => Fin.cases h0n10_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n10 : h0e10.toBi mapPolyEnv=h0p10 := by
  change BiPoly.mul (h0e6.toBi mapPolyEnv) (h0e9.toBi mapPolyEnv)=h0p10
  rw [h0n6, h0n9]
  exact h0n10_arithmetic

#print axioms h0n10_arithmetic
end StackSorting.RationalLift
