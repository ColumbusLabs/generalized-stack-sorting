import BivariateRowEquality
import Horner4Base
import Horner4Node011
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p12 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 16058215538607617568), (Int.ofNat 82763921018121766272), (Int.negSucc 59983103427307564607), (Int.negSucc 429390082229876933759), (Int.ofNat 432234258814898215200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 156840079074801887807), (Int.negSucc 860058792051404472575), (Int.ofNat 369875008766480280192), (Int.ofNat 4203270342605255823360), (Int.negSucc 3909983500608312126527), (Int.ofNat 236730277966615614720)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 744756444205413415776), (Int.ofNat 3994628768914308103872), (Int.negSucc 1172347616432130668927), (Int.negSucc 17357071670325899345663), (Int.ofNat 14774494300937535987360), (Int.negSucc 1079349976325978883647), (Int.ofNat 31212271490646267648)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2271371262628583006495), (Int.negSucc 11088068294886729408863), (Int.ofNat 3239441530817802345792), (Int.ofNat 38246263914638651253696), (Int.negSucc 27416613605087317795487), (Int.ofNat 317722192681129354656), (Int.ofNat 37522162601216555904), (Int.negSucc 329001582109178879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4945076868721582897056), (Int.ofNat 20531425646565004245984), (Int.negSucc 7813098035486307855071), (Int.negSucc 44819571393788986441151), (Int.ofNat 17369137945211988877056), (Int.ofNat 7778450541031057869408), (Int.negSucc 515204751337010406431), (Int.ofNat 11995484529113167104), (Int.ofNat 834848253043200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8086883880750467930783), (Int.negSucc 26524288496270364455231), (Int.ofNat 12068610918205274710272), (Int.ofNat 17776115347392657743040), (Int.ofNat 26190157675872800739168), (Int.negSucc 20076278801725027079423), (Int.ofNat 486409582437643202688), (Int.ofNat 19885674008537125632), (Int.negSucc 60585446405214719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10193798462523376004136), (Int.ofNat 24098980501123702613712), (Int.negSucc 7374118973416214895143), (Int.ofNat 19571610475955328866208), (Int.negSucc 61152077624689302386183), (Int.ofNat 17050316697224693355600), (Int.ofNat 1990296017302359602088), (Int.negSucc 114697788976094807807), (Int.ofNat 997703059540376448)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10016777101818853563119), (Int.negSucc 15155708540100850227887), (Int.negSucc 8088480993873446096831), (Int.negSucc 27056773905699188201759), (Int.ofNat 41728063391014851085680), (Int.ofNat 7578017097470163476208), (Int.negSucc 4748629527633300365663), (Int.negSucc 15987842113648461695), (Int.ofNat 3867193463838868224)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7681338244150476832152), (Int.ofNat 6600801524495768626320), (Int.ofNat 21147595002719804599056), (Int.ofNat 8749084448591759634480), (Int.ofNat 5519999076223836121272), (Int.negSucc 25446818689952111695439), (Int.ofNat 2508932010226042314144), (Int.ofNat 414223812339253665840), (Int.negSucc 3586153115654809631)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4565060371360843711199), (Int.negSucc 2604189689814324281759), (Int.negSucc 20343239566182521966591), (Int.ofNat 2388224502304243762176), (Int.negSucc 24991217149301281387007), (Int.ofNat 16030628854243641875520), (Int.ofNat 2820664323509575374432), (Int.negSucc 351995296014278535455), (Int.negSucc 12987789160990010399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2072838488839950000024), (Int.ofNat 1820538337916451403584), (Int.ofNat 10682130756354950801952), (Int.ofNat 1007508786932154749616), (Int.ofNat 14009975401185022621464), (Int.ofNat 1744204217758067112912), (Int.negSucc 4014962396475074746631), (Int.negSucc 251628524958877181999), (Int.ofNat 12020617956906472392)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 703235202543802874447), (Int.negSucc 1525111645915441901231), (Int.negSucc 2948567566137028278191), (Int.negSucc 4760909172619730165807), (Int.negSucc 2174820761160715183487), (Int.negSucc 6911336319478781040575), (Int.ofNat 1050034870735112787696), (Int.ofNat 456385085662496802192), (Int.ofNat 11116611019330769952)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 172417832684348900904), (Int.ofNat 902402141395336421040), (Int.ofNat 251687962871868308184), (Int.ofNat 3481475193693934407792), (Int.negSucc 410381793944275014287), (Int.ofNat 3367455854873405806944), (Int.ofNat 913454876628264373560), (Int.negSucc 122152413687025446719), (Int.negSucc 15102239083591040063)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 29032214113887410015), (Int.negSucc 349212063177688882751), (Int.ofNat 15986458079140355136), (Int.negSucc 1162046844924457816799), (Int.negSucc 142709338794383103167), (Int.negSucc 575722311651045933407), (Int.negSucc 734807528096971717439), (Int.negSucc 106165503851123201183), (Int.ofNat 607479286454884800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3091227384860616672), (Int.ofNat 87667712535301106256), (Int.ofNat 52325806409504301240), (Int.ofNat 149774576563007972496), (Int.ofNat 252939864053121870168), (Int.negSucc 38225903766317271935), (Int.ofNat 198842740962207607872), (Int.ofNat 79317304098089829120), (Int.ofNat 5425519645584751392)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 179929631876713343), (Int.negSucc 13722013231859319839), (Int.negSucc 37021035026618304335), (Int.ofNat 22511139058664208720), (Int.negSucc 94477001857264674143), (Int.ofNat 27374584855564067904), (Int.negSucc 18204146392109978879), (Int.negSucc 18958747259367641087), (Int.negSucc 2567209815729257471)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4257874500812928), (Int.ofNat 1191727103011553088), (Int.ofNat 10663742317601683656), (Int.negSucc 11817894978174125375), (Int.ofNat 16462325934896335488), (Int.negSucc 3487206555357355007), (Int.negSucc 1019240178375371327), (Int.ofNat 1487040367554330624), (Int.ofNat 366947515001806848)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 40745618342889983), (Int.negSucc 1557307282389325055), (Int.ofNat 1866429259198196832), (Int.negSucc 1314454281599643839), (Int.ofNat 102101725844803584), (Int.ofNat 237069928187476992)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 97478531473125888), (Int.negSucc 122188119673206527), (Int.ofNat 38290319836706592)]]

theorem h4n12_arithmetic_row0 :
    (BiPoly.mul h4p6 h4p11).getD 0 []=h4p12.getD 0 [] := by
  decide +kernel

theorem h4n12_arithmetic_row1 :
    (BiPoly.mul h4p6 h4p11).getD 1 []=h4p12.getD 1 [] := by
  decide +kernel

theorem h4n12_arithmetic_row2 :
    (BiPoly.mul h4p6 h4p11).getD 2 []=h4p12.getD 2 [] := by
  decide +kernel

theorem h4n12_arithmetic_row3 :
    (BiPoly.mul h4p6 h4p11).getD 3 []=h4p12.getD 3 [] := by
  decide +kernel

theorem h4n12_arithmetic_row4 :
    (BiPoly.mul h4p6 h4p11).getD 4 []=h4p12.getD 4 [] := by
  decide +kernel

theorem h4n12_arithmetic_row5 :
    (BiPoly.mul h4p6 h4p11).getD 5 []=h4p12.getD 5 [] := by
  decide +kernel

theorem h4n12_arithmetic_row6 :
    (BiPoly.mul h4p6 h4p11).getD 6 []=h4p12.getD 6 [] := by
  decide +kernel

theorem h4n12_arithmetic_row7 :
    (BiPoly.mul h4p6 h4p11).getD 7 []=h4p12.getD 7 [] := by
  decide +kernel

theorem h4n12_arithmetic_row8 :
    (BiPoly.mul h4p6 h4p11).getD 8 []=h4p12.getD 8 [] := by
  decide +kernel

theorem h4n12_arithmetic_row9 :
    (BiPoly.mul h4p6 h4p11).getD 9 []=h4p12.getD 9 [] := by
  decide +kernel

theorem h4n12_arithmetic_row10 :
    (BiPoly.mul h4p6 h4p11).getD 10 []=h4p12.getD 10 [] := by
  decide +kernel

theorem h4n12_arithmetic_row11 :
    (BiPoly.mul h4p6 h4p11).getD 11 []=h4p12.getD 11 [] := by
  decide +kernel

theorem h4n12_arithmetic_row12 :
    (BiPoly.mul h4p6 h4p11).getD 12 []=h4p12.getD 12 [] := by
  decide +kernel

theorem h4n12_arithmetic_row13 :
    (BiPoly.mul h4p6 h4p11).getD 13 []=h4p12.getD 13 [] := by
  decide +kernel

theorem h4n12_arithmetic_row14 :
    (BiPoly.mul h4p6 h4p11).getD 14 []=h4p12.getD 14 [] := by
  decide +kernel

theorem h4n12_arithmetic_row15 :
    (BiPoly.mul h4p6 h4p11).getD 15 []=h4p12.getD 15 [] := by
  decide +kernel

theorem h4n12_arithmetic_row16 :
    (BiPoly.mul h4p6 h4p11).getD 16 []=h4p12.getD 16 [] := by
  decide +kernel

theorem h4n12_arithmetic_row17 :
    (BiPoly.mul h4p6 h4p11).getD 17 []=h4p12.getD 17 [] := by
  decide +kernel

theorem h4n12_arithmetic_row18 :
    (BiPoly.mul h4p6 h4p11).getD 18 []=h4p12.getD 18 [] := by
  decide +kernel

theorem h4n12_arithmetic : BiPoly.mul h4p6 h4p11=h4p12 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p6 h4p11).getD j.val []=h4p12.getD j.val [] :=
      (fun j => Fin.cases h4n12_arithmetic_row0 (fun j => Fin.cases h4n12_arithmetic_row1 (fun j => Fin.cases h4n12_arithmetic_row2 (fun j => Fin.cases h4n12_arithmetic_row3 (fun j => Fin.cases h4n12_arithmetic_row4 (fun j => Fin.cases h4n12_arithmetic_row5 (fun j => Fin.cases h4n12_arithmetic_row6 (fun j => Fin.cases h4n12_arithmetic_row7 (fun j => Fin.cases h4n12_arithmetic_row8 (fun j => Fin.cases h4n12_arithmetic_row9 (fun j => Fin.cases h4n12_arithmetic_row10 (fun j => Fin.cases h4n12_arithmetic_row11 (fun j => Fin.cases h4n12_arithmetic_row12 (fun j => Fin.cases h4n12_arithmetic_row13 (fun j => Fin.cases h4n12_arithmetic_row14 (fun j => Fin.cases h4n12_arithmetic_row15 (fun j => Fin.cases h4n12_arithmetic_row16 (fun j => Fin.cases h4n12_arithmetic_row17 (fun j => Fin.cases h4n12_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n12 : h4e12.toBi mapPolyEnv=h4p12 := by
  change BiPoly.mul (h4e6.toBi mapPolyEnv) (h4e11.toBi mapPolyEnv)=h4p12
  rw [h4n6, h4n11]
  exact h4n12_arithmetic

#print axioms h4n12_arithmetic
end StackSorting.RationalLift
