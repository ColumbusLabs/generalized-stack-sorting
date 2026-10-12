import BivariateRowEquality
import Horner4Base
import Horner4Node011
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p194 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5352738512869205855), (Int.negSucc 27587973672707255423), (Int.ofNat 19994367809102521536), (Int.ofNat 143130027409958977920), (Int.negSucc 144078086271632738399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 52280026358267295936), (Int.ofNat 286686264017134824192), (Int.negSucc 123291669588826760063), (Int.negSucc 1401090114201751941119), (Int.ofNat 1303327833536104042176), (Int.negSucc 78910092655538538239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 248252148068471138591), (Int.negSucc 1331542922971436034623), (Int.ofNat 390782538810710222976), (Int.ofNat 5785690556775299781888), (Int.negSucc 4924831433645845329119), (Int.ofNat 359783325441992961216), (Int.negSucc 10404090496882089215)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 757123754209527668832), (Int.ofNat 3696022764962243136288), (Int.negSucc 1079813843605934115263), (Int.negSucc 12748754638212883751231), (Int.ofNat 9138871201695772598496), (Int.negSucc 105907397560376451551), (Int.negSucc 12507387533738851967), (Int.ofNat 109667194036392960)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1648358956240527632351), (Int.negSucc 6843808548855001415327), (Int.ofNat 2604366011828769285024), (Int.ofNat 14939857131262995480384), (Int.negSucc 5789712648403996292351), (Int.negSucc 2592816847010352623135), (Int.ofNat 171734917112336802144), (Int.negSucc 3998494843037722367), (Int.negSucc 278282751014399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2695627960250155976928), (Int.ofNat 8841429498756788151744), (Int.negSucc 4022870306068424903423), (Int.negSucc 5925371782464219247679), (Int.negSucc 8730052558624266913055), (Int.ofNat 6692092933908342359808), (Int.negSucc 162136527479214400895), (Int.negSucc 6628558002845708543), (Int.ofNat 20195148801738240)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3397932820841125334711), (Int.negSucc 8032993500374567537903), (Int.ofNat 2458039657805404965048), (Int.negSucc 6523870158651776288735), (Int.ofNat 20384025874896434128728), (Int.negSucc 5683438899074897785199), (Int.negSucc 663432005767453200695), (Int.ofNat 38232596325364935936), (Int.negSucc 332567686513458815)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3338925700606284521040), (Int.ofNat 5051902846700283409296), (Int.ofNat 2696160331291148698944), (Int.ofNat 9018924635233062733920), (Int.negSucc 13909354463671617028559), (Int.negSucc 2526005699156721158735), (Int.ofNat 1582876509211100121888), (Int.ofNat 5329280704549487232), (Int.negSucc 1289064487946289407)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2560446081383492277383), (Int.negSucc 2200267174831922875439), (Int.negSucc 7049198334239934866351), (Int.negSucc 2916361482863919878159), (Int.negSucc 1839999692074612040423), (Int.ofNat 8482272896650703898480), (Int.negSucc 836310670075347438047), (Int.negSucc 138074604113084555279), (Int.ofNat 1195384371884936544)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1521686790453614570400), (Int.ofNat 868063229938108093920), (Int.ofNat 6781079855394173988864), (Int.negSucc 796074834101414587391), (Int.ofNat 8330405716433760462336), (Int.negSucc 5343542951414547291839), (Int.negSucc 940221441169858458143), (Int.ofNat 117331765338092845152), (Int.ofNat 4329263053663336800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 690946162946650000007), (Int.negSucc 606846112638817134527), (Int.negSucc 3560710252118316933983), (Int.negSucc 335836262310718249871), (Int.negSucc 4669991800395007540487), (Int.negSucc 581401405919355704303), (Int.ofNat 1338320798825024915544), (Int.ofNat 83876174986292394000), (Int.negSucc 4006872652302157463)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 234411734181267624816), (Int.ofNat 508370548638480633744), (Int.ofNat 982855855379009426064), (Int.ofNat 1586969724206576721936), (Int.ofNat 724940253720238394496), (Int.ofNat 2303778773159593680192), (Int.negSucc 350011623578370929231), (Int.negSucc 152128361887498934063), (Int.negSucc 3705537006443589983)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 57472610894782966967), (Int.negSucc 300800713798445473679), (Int.negSucc 83895987623956102727), (Int.negSucc 1160491731231311469263), (Int.ofNat 136793931314758338096), (Int.negSucc 1122485284957801935647), (Int.negSucc 304484958876088124519), (Int.ofNat 40717471229008482240), (Int.ofNat 5034079694530346688)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9677404704629136672), (Int.ofNat 116404021059229627584), (Int.negSucc 5328819359713451711), (Int.ofNat 387348948308152605600), (Int.ofNat 47569779598127701056), (Int.ofNat 191907437217015311136), (Int.ofNat 244935842698990572480), (Int.ofNat 35388501283707733728), (Int.negSucc 202493095484961599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1030409128286872223), (Int.negSucc 29222570845100368751), (Int.negSucc 17441935469834767079), (Int.negSucc 49924858854335990831), (Int.negSucc 84313288017707290055), (Int.ofNat 12741967922105757312), (Int.negSucc 66280913654069202623), (Int.negSucc 26439101366029943039), (Int.negSucc 1808506548528250463)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 59976543958904448), (Int.ofNat 4574004410619773280), (Int.ofNat 12340345008872768112), (Int.negSucc 7503713019554736239), (Int.ofNat 31492333952421558048), (Int.negSucc 9124861618521355967), (Int.ofNat 6068048797369992960), (Int.ofNat 6319582419789213696), (Int.ofNat 855736605243085824)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1419291500270975), (Int.negSucc 397242367670517695), (Int.negSucc 3554580772533894551), (Int.ofNat 3939298326058041792), (Int.negSucc 5487441978298778495), (Int.ofNat 1162402185119118336), (Int.ofNat 339746726125123776), (Int.negSucc 495680122518110207), (Int.negSucc 122315838333935615)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 13581872780963328), (Int.ofNat 519102427463108352), (Int.negSucc 622143086399398943), (Int.ofNat 438151427199881280), (Int.negSucc 34033908614934527), (Int.negSucc 79023309395825663)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 32492843824375295), (Int.ofNat 40729373224402176), (Int.negSucc 12763439945568863)]]

theorem h4n194_arithmetic_row0 :
    (BiPoly.mul h4p54 h4p11).getD 0 []=h4p194.getD 0 [] := by
  decide +kernel

theorem h4n194_arithmetic_row1 :
    (BiPoly.mul h4p54 h4p11).getD 1 []=h4p194.getD 1 [] := by
  decide +kernel

theorem h4n194_arithmetic_row2 :
    (BiPoly.mul h4p54 h4p11).getD 2 []=h4p194.getD 2 [] := by
  decide +kernel

theorem h4n194_arithmetic_row3 :
    (BiPoly.mul h4p54 h4p11).getD 3 []=h4p194.getD 3 [] := by
  decide +kernel

theorem h4n194_arithmetic_row4 :
    (BiPoly.mul h4p54 h4p11).getD 4 []=h4p194.getD 4 [] := by
  decide +kernel

theorem h4n194_arithmetic_row5 :
    (BiPoly.mul h4p54 h4p11).getD 5 []=h4p194.getD 5 [] := by
  decide +kernel

theorem h4n194_arithmetic_row6 :
    (BiPoly.mul h4p54 h4p11).getD 6 []=h4p194.getD 6 [] := by
  decide +kernel

theorem h4n194_arithmetic_row7 :
    (BiPoly.mul h4p54 h4p11).getD 7 []=h4p194.getD 7 [] := by
  decide +kernel

theorem h4n194_arithmetic_row8 :
    (BiPoly.mul h4p54 h4p11).getD 8 []=h4p194.getD 8 [] := by
  decide +kernel

theorem h4n194_arithmetic_row9 :
    (BiPoly.mul h4p54 h4p11).getD 9 []=h4p194.getD 9 [] := by
  decide +kernel

theorem h4n194_arithmetic_row10 :
    (BiPoly.mul h4p54 h4p11).getD 10 []=h4p194.getD 10 [] := by
  decide +kernel

theorem h4n194_arithmetic_row11 :
    (BiPoly.mul h4p54 h4p11).getD 11 []=h4p194.getD 11 [] := by
  decide +kernel

theorem h4n194_arithmetic_row12 :
    (BiPoly.mul h4p54 h4p11).getD 12 []=h4p194.getD 12 [] := by
  decide +kernel

theorem h4n194_arithmetic_row13 :
    (BiPoly.mul h4p54 h4p11).getD 13 []=h4p194.getD 13 [] := by
  decide +kernel

theorem h4n194_arithmetic_row14 :
    (BiPoly.mul h4p54 h4p11).getD 14 []=h4p194.getD 14 [] := by
  decide +kernel

theorem h4n194_arithmetic_row15 :
    (BiPoly.mul h4p54 h4p11).getD 15 []=h4p194.getD 15 [] := by
  decide +kernel

theorem h4n194_arithmetic_row16 :
    (BiPoly.mul h4p54 h4p11).getD 16 []=h4p194.getD 16 [] := by
  decide +kernel

theorem h4n194_arithmetic_row17 :
    (BiPoly.mul h4p54 h4p11).getD 17 []=h4p194.getD 17 [] := by
  decide +kernel

theorem h4n194_arithmetic_row18 :
    (BiPoly.mul h4p54 h4p11).getD 18 []=h4p194.getD 18 [] := by
  decide +kernel

theorem h4n194_arithmetic : BiPoly.mul h4p54 h4p11=h4p194 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p54 h4p11).getD j.val []=h4p194.getD j.val [] :=
      (fun j => Fin.cases h4n194_arithmetic_row0 (fun j => Fin.cases h4n194_arithmetic_row1 (fun j => Fin.cases h4n194_arithmetic_row2 (fun j => Fin.cases h4n194_arithmetic_row3 (fun j => Fin.cases h4n194_arithmetic_row4 (fun j => Fin.cases h4n194_arithmetic_row5 (fun j => Fin.cases h4n194_arithmetic_row6 (fun j => Fin.cases h4n194_arithmetic_row7 (fun j => Fin.cases h4n194_arithmetic_row8 (fun j => Fin.cases h4n194_arithmetic_row9 (fun j => Fin.cases h4n194_arithmetic_row10 (fun j => Fin.cases h4n194_arithmetic_row11 (fun j => Fin.cases h4n194_arithmetic_row12 (fun j => Fin.cases h4n194_arithmetic_row13 (fun j => Fin.cases h4n194_arithmetic_row14 (fun j => Fin.cases h4n194_arithmetic_row15 (fun j => Fin.cases h4n194_arithmetic_row16 (fun j => Fin.cases h4n194_arithmetic_row17 (fun j => Fin.cases h4n194_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n194 : h4e194.toBi mapPolyEnv=h4p194 := by
  change BiPoly.mul (h4e54.toBi mapPolyEnv) (h4e11.toBi mapPolyEnv)=h4p194
  rw [h4n54, h4n11]
  exact h4n194_arithmetic

#print axioms h4n194_arithmetic
end StackSorting.RationalLift
