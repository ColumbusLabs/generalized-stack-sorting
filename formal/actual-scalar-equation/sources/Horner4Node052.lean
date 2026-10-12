import BivariateRowEquality
import Horner4Base
import Horner4Node011
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p52 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 12043661653955713176), (Int.ofNat 62072940763591324704), (Int.negSucc 44987327570480673455), (Int.negSucc 322042561672407700319), (Int.ofNat 324175694111173661400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 117630059306101415855), (Int.negSucc 645044094038553354431), (Int.ofNat 277406256574860210144), (Int.ofNat 3152452756953941867520), (Int.negSucc 2932487625456234094895), (Int.ofNat 177547708474961711040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 558567333154060061832), (Int.ofNat 2995971576685731077904), (Int.negSucc 879260712324098001695), (Int.negSucc 13017803752744424509247), (Int.ofNat 11080870725703151990520), (Int.negSucc 809512482244484162735), (Int.ofNat 23409203617984700736)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1703528446971437254871), (Int.negSucc 8316051221165047056647), (Int.ofNat 2429581148113351759344), (Int.ofNat 28684697935978988440272), (Int.negSucc 20562460203815488346615), (Int.ofNat 238291644510847015992), (Int.ofNat 28141621950912416928), (Int.negSucc 246751186581884159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3708807651541187172792), (Int.ofNat 15398569234923753184488), (Int.negSucc 5859823526614730891303), (Int.negSucc 33614678545341739830863), (Int.ofNat 13026853458908991657792), (Int.ofNat 5833837905773293402056), (Int.negSucc 386403563502757804823), (Int.ofNat 8996613396834875328), (Int.ofNat 626136189782400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6065162910562850948087), (Int.negSucc 19893216372202773341423), (Int.ofNat 9051458188653956032704), (Int.ofNat 13332086510544493307280), (Int.ofNat 19642618256904600554376), (Int.negSucc 15057209101293770309567), (Int.ofNat 364807186828232402016), (Int.ofNat 14914255506402844224), (Int.negSucc 45439084803911039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7645348846892532003102), (Int.ofNat 18074235375842776960284), (Int.negSucc 5530589230062161171357), (Int.ofNat 14678707856966496649656), (Int.negSucc 45864058218516976789637), (Int.ofNat 12787737522918520016700), (Int.ofNat 1492722012976769701566), (Int.negSucc 86023341732071105855), (Int.ofNat 748277294655282336)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7512582826364140172339), (Int.negSucc 11366781405075637670915), (Int.negSucc 6066360745405084572623), (Int.negSucc 20292580429274391151319), (Int.ofNat 31296047543261138314260), (Int.ofNat 5683512823102622607156), (Int.negSucc 3561472145724975274247), (Int.negSucc 11990881585236346271), (Int.ofNat 2900395097879151168)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5761003683112857624114), (Int.ofNat 4950601143371826469740), (Int.ofNat 15860696252039853449292), (Int.ofNat 6561813336443819725860), (Int.ofNat 4139999307167877090954), (Int.negSucc 19085114017464083771579), (Int.ofNat 1881699007669531735608), (Int.ofNat 310667859254440249380), (Int.negSucc 2689614836741107223)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3423795278520632783399), (Int.negSucc 1953142267360743211319), (Int.negSucc 15257429674636891474943), (Int.ofNat 1791168376728182821632), (Int.negSucc 18743412861975961040255), (Int.ofNat 12022971640682731406640), (Int.ofNat 2115498242632181530824), (Int.negSucc 263996472010708901591), (Int.negSucc 9740841870742507799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1554628866629962500018), (Int.ofNat 1365403753437338552688), (Int.ofNat 8011598067266213101464), (Int.ofNat 755631590199116062212), (Int.ofNat 10507481550888766966098), (Int.ofNat 1308153163318550334684), (Int.negSucc 3011221797356306059973), (Int.negSucc 188721393719157886499), (Int.ofNat 9015463467679854294)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 527426401907852155835), (Int.negSucc 1143833734436581425923), (Int.negSucc 2211425674602771208643), (Int.negSucc 3570681879464797624355), (Int.negSucc 1631115570870536387615), (Int.negSucc 5183502239609085780431), (Int.ofNat 787526153051334590772), (Int.ofNat 342288814246872601644), (Int.ofNat 8337458264498077464)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 129313374513261675678), (Int.ofNat 676801606046502315780), (Int.ofNat 188765972153901231138), (Int.ofNat 2611106395270450805844), (Int.negSucc 307786345458206260715), (Int.ofNat 2525591891155054355208), (Int.ofNat 685091157471198280170), (Int.negSucc 91614310265269085039), (Int.negSucc 11326679312693280047)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 21774160585415557511), (Int.negSucc 261909047383266662063), (Int.ofNat 11989843559355266352), (Int.negSucc 871535133693343362599), (Int.negSucc 107032004095787327375), (Int.negSucc 431791733738284450055), (Int.negSucc 551105646072728788079), (Int.negSucc 79624127888342400887), (Int.ofNat 455609464841163600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2318420538645462504), (Int.ofNat 65750784401475829692), (Int.ofNat 39244354807128225930), (Int.ofNat 112330932422255979372), (Int.ofNat 189704898039841402626), (Int.negSucc 28669427824737953951), (Int.ofNat 149132055721655705904), (Int.ofNat 59487978073567371840), (Int.ofNat 4069139734188563544)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 134947223907535007), (Int.negSucc 10291509923894489879), (Int.negSucc 27765776269963728251), (Int.ofNat 16883354293998156540), (Int.negSucc 70857751392948505607), (Int.ofNat 20530938641673050928), (Int.negSucc 13653109794082484159), (Int.negSucc 14219060444525730815), (Int.negSucc 1925407361796943103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3193405875609696), (Int.ofNat 893795327258664816), (Int.ofNat 7997806738201262742), (Int.negSucc 8863421233630594031), (Int.ofNat 12346744451172251616), (Int.negSucc 2615404916518016255), (Int.negSucc 764430133781528495), (Int.ofNat 1115280275665747968), (Int.ofNat 275210636251355136)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 30559213757167487), (Int.negSucc 1167980461791993791), (Int.ofNat 1399821944398647624), (Int.negSucc 985840711199732879), (Int.ofNat 76576294383602688), (Int.ofNat 177802446140607744)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 73108898604844416), (Int.negSucc 91641089754904895), (Int.ofNat 28717739877529944)]]

theorem h4n52_arithmetic_row0 :
    (BiPoly.mul h4p51 h4p11).getD 0 []=h4p52.getD 0 [] := by
  decide +kernel

theorem h4n52_arithmetic_row1 :
    (BiPoly.mul h4p51 h4p11).getD 1 []=h4p52.getD 1 [] := by
  decide +kernel

theorem h4n52_arithmetic_row2 :
    (BiPoly.mul h4p51 h4p11).getD 2 []=h4p52.getD 2 [] := by
  decide +kernel

theorem h4n52_arithmetic_row3 :
    (BiPoly.mul h4p51 h4p11).getD 3 []=h4p52.getD 3 [] := by
  decide +kernel

theorem h4n52_arithmetic_row4 :
    (BiPoly.mul h4p51 h4p11).getD 4 []=h4p52.getD 4 [] := by
  decide +kernel

theorem h4n52_arithmetic_row5 :
    (BiPoly.mul h4p51 h4p11).getD 5 []=h4p52.getD 5 [] := by
  decide +kernel

theorem h4n52_arithmetic_row6 :
    (BiPoly.mul h4p51 h4p11).getD 6 []=h4p52.getD 6 [] := by
  decide +kernel

theorem h4n52_arithmetic_row7 :
    (BiPoly.mul h4p51 h4p11).getD 7 []=h4p52.getD 7 [] := by
  decide +kernel

theorem h4n52_arithmetic_row8 :
    (BiPoly.mul h4p51 h4p11).getD 8 []=h4p52.getD 8 [] := by
  decide +kernel

theorem h4n52_arithmetic_row9 :
    (BiPoly.mul h4p51 h4p11).getD 9 []=h4p52.getD 9 [] := by
  decide +kernel

theorem h4n52_arithmetic_row10 :
    (BiPoly.mul h4p51 h4p11).getD 10 []=h4p52.getD 10 [] := by
  decide +kernel

theorem h4n52_arithmetic_row11 :
    (BiPoly.mul h4p51 h4p11).getD 11 []=h4p52.getD 11 [] := by
  decide +kernel

theorem h4n52_arithmetic_row12 :
    (BiPoly.mul h4p51 h4p11).getD 12 []=h4p52.getD 12 [] := by
  decide +kernel

theorem h4n52_arithmetic_row13 :
    (BiPoly.mul h4p51 h4p11).getD 13 []=h4p52.getD 13 [] := by
  decide +kernel

theorem h4n52_arithmetic_row14 :
    (BiPoly.mul h4p51 h4p11).getD 14 []=h4p52.getD 14 [] := by
  decide +kernel

theorem h4n52_arithmetic_row15 :
    (BiPoly.mul h4p51 h4p11).getD 15 []=h4p52.getD 15 [] := by
  decide +kernel

theorem h4n52_arithmetic_row16 :
    (BiPoly.mul h4p51 h4p11).getD 16 []=h4p52.getD 16 [] := by
  decide +kernel

theorem h4n52_arithmetic_row17 :
    (BiPoly.mul h4p51 h4p11).getD 17 []=h4p52.getD 17 [] := by
  decide +kernel

theorem h4n52_arithmetic_row18 :
    (BiPoly.mul h4p51 h4p11).getD 18 []=h4p52.getD 18 [] := by
  decide +kernel

theorem h4n52_arithmetic : BiPoly.mul h4p51 h4p11=h4p52 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p51 h4p11).getD j.val []=h4p52.getD j.val [] :=
      (fun j => Fin.cases h4n52_arithmetic_row0 (fun j => Fin.cases h4n52_arithmetic_row1 (fun j => Fin.cases h4n52_arithmetic_row2 (fun j => Fin.cases h4n52_arithmetic_row3 (fun j => Fin.cases h4n52_arithmetic_row4 (fun j => Fin.cases h4n52_arithmetic_row5 (fun j => Fin.cases h4n52_arithmetic_row6 (fun j => Fin.cases h4n52_arithmetic_row7 (fun j => Fin.cases h4n52_arithmetic_row8 (fun j => Fin.cases h4n52_arithmetic_row9 (fun j => Fin.cases h4n52_arithmetic_row10 (fun j => Fin.cases h4n52_arithmetic_row11 (fun j => Fin.cases h4n52_arithmetic_row12 (fun j => Fin.cases h4n52_arithmetic_row13 (fun j => Fin.cases h4n52_arithmetic_row14 (fun j => Fin.cases h4n52_arithmetic_row15 (fun j => Fin.cases h4n52_arithmetic_row16 (fun j => Fin.cases h4n52_arithmetic_row17 (fun j => Fin.cases h4n52_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n52 : h4e52.toBi mapPolyEnv=h4p52 := by
  change BiPoly.mul (h4e51.toBi mapPolyEnv) (h4e11.toBi mapPolyEnv)=h4p52
  rw [h4n51, h4n11]
  exact h4n52_arithmetic

#print axioms h4n52_arithmetic
end StackSorting.RationalLift
