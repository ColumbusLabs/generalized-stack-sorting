import BivariateRowEquality
import Horner4Base
import Horner4Node073
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p74 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 5203757370311999999), (Int.negSucc 26492419011832487999), (Int.ofNat 16330878995053453920), (Int.ofNat 106305610259284008480), (Int.negSucc 179674864364235172319), (Int.ofNat 84911431881329776800)], [(Int.ofNat 0), (Int.ofNat 45284253026981760000), (Int.ofNat 216579252744207717120), (Int.negSucc 192339476923745975615), (Int.negSucc 885037150494015585695), (Int.ofNat 1624802664436835074560), (Int.negSucc 840429583252276709663), (Int.ofNat 61509085945343740800)], [(Int.ofNat 0), (Int.negSucc 178505940986362771199), (Int.negSucc 806435852547097936079), (Int.ofNat 832764299211295513272), (Int.ofNat 3182456939711285111472), (Int.negSucc 6024330678072289584095), (Int.ofNat 3143958493664091739392), (Int.negSucc 309175108478501356151), (Int.ofNat 14421032149721810688)], [(Int.ofNat 0), (Int.ofNat 421280418394161388800), (Int.ofNat 1809002451928843054800), (Int.negSucc 1811013450629662856087), (Int.negSucc 6534720197062569803375), (Int.ofNat 11377458676763459720640), (Int.negSucc 4931066732342079800879), (Int.ofNat 112876881053709624120), (Int.negSucc 6975522794868039791), (Int.ofNat 1059377927632510464)], [(Int.ofNat 0), (Int.negSucc 662706705057581210399), (Int.negSucc 2720814995896297913519), (Int.ofNat 1991968385717168084736), (Int.ofNat 8359520292891061297488), (Int.negSucc 9870691339531158985439), (Int.negSucc 41260958824196353823), (Int.ofNat 2207894988188534015088), (Int.negSucc 196132214089562686415), (Int.ofNat 5618377916377354080), (Int.negSucc 5646215766597119)], [(Int.ofNat 0), (Int.ofNat 731824260351183907200), (Int.ofNat 2882632346718034197240), (Int.negSucc 422286426965351444939), (Int.negSucc 6437799333563326445627), (Int.negSucc 1935149799484722752423), (Int.ofNat 11593861240624615755216), (Int.negSucc 5305476705146938225115), (Int.ofNat 318837648146722544052), (Int.negSucc 9157858795613712095), (Int.ofNat 184489567971523776)], [(Int.ofNat 0), (Int.negSucc 581620857584704185599), (Int.negSucc 2191145799303742291559), (Int.negSucc 1907167534200739480211), (Int.ofNat 1795665340749382035696), (Int.ofNat 13878107703498320638848), (Int.negSucc 16161913510679388734855), (Int.ofNat 3032391313248345132372), (Int.ofNat 596960887768479950112), (Int.negSucc 46654744455348760295), (Int.ofNat 1100543285437867584)], [(Int.ofNat 0), (Int.ofNat 335189122391345270400), (Int.ofNat 1185653317762549459800), (Int.ofNat 2993619328458331320828), (Int.ofNat 2217165508865276107452), (Int.negSucc 14087487200331805585631), (Int.ofNat 5542113192031811155608), (Int.ofNat 4903541569896840714492), (Int.negSucc 1893566086357191551963), (Int.ofNat 72259479250956458496), (Int.ofNat 36434295356870592)], [(Int.ofNat 0), (Int.negSucc 139041606210657508799), (Int.negSucc 436298344577787102839), (Int.negSucc 2323486759401980820323), (Int.negSucc 3390691833070012706615), (Int.ofNat 5059434154215923642016), (Int.ofNat 7771979428295859258696), (Int.negSucc 8384574051830897213435), (Int.ofNat 1058746001987424886344), (Int.ofNat 113479221140088264432), (Int.negSucc 5929470806725108367)], [(Int.ofNat 0), (Int.ofNat 40501368826997558400), (Int.ofNat 93798473898377413080), (Int.ofNat 1064619983909836591164), (Int.ofNat 2323030639001772303792), (Int.ofNat 2219324829271558557696), (Int.negSucc 9713392632092533280075), (Int.ofNat 3090462404504211095472), (Int.ofNat 1347943987113880366188), (Int.negSucc 268189997618904248663), (Int.negSucc 223798119038857115)], [(Int.ofNat 0), (Int.negSucc 7868202969415795199), (Int.negSucc 3102305174390073959), (Int.negSucc 262467859896130833035), (Int.negSucc 894211207789268552507), (Int.negSucc 3316125640854579161795), (Int.ofNat 3591553249073955758544), (Int.ofNat 2668989315422684424816), (Int.negSucc 1880692119888795646235), (Int.ofNat 52700326595865996156), (Int.ofNat 13105714357581421752)], [(Int.ofNat 0), (Int.ofNat 916025317449897600), (Int.negSucc 4571940030499048679), (Int.ofNat 7504165327980620124), (Int.ofNat 144820781999137802412), (Int.ofNat 1552437439348508098632), (Int.ofNat 780422505230708131464), (Int.negSucc 2963232558374155306127), (Int.ofNat 377564887585396312632), (Int.ofNat 207630929320415102808), (Int.negSucc 5707917689379457463)], [(Int.ofNat 0), (Int.negSucc 48378129086311199), (Int.ofNat 1352949846940757160), (Int.ofNat 16516641508687217412), (Int.ofNat 30998840577672291264), (Int.negSucc 284909733550601134271), (Int.negSucc 1188679866971763242159), (Int.ofNat 825643539406764746280), (Int.ofNat 583126952779056141360), (Int.negSucc 144434954419383477239), (Int.negSucc 9100326351811949639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 164312498368907279), (Int.negSucc 5235915969961576559), (Int.negSucc 21945115559073600827), (Int.negSucc 37517349085311901895), (Int.ofNat 419732873238639893364), (Int.ofNat 205994292908457047472), (Int.negSucc 391972803561613028735), (Int.negSucc 20149271071567609391), (Int.ofNat 7661492625746705328)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7176141063162720), (Int.ofNat 712174657864103784), (Int.ofNat 4941532218787458948), (Int.ofNat 29760725205037782108), (Int.negSucc 45447923025122637095), (Int.negSucc 187521199209288946943), (Int.ofNat 54342170050775910480), (Int.ofNat 50916645958966423632), (Int.ofNat 286676247115462752)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 38433798643918463), (Int.negSucc 522008262570550031), (Int.negSucc 5905371404922528023), (Int.negSucc 9102079466415377495), (Int.ofNat 43494328040477854032), (Int.ofNat 26420955263203050000), (Int.negSucc 16114944208589719487), (Int.negSucc 2159992330670306591)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 21359527178827680), (Int.ofNat 474403997130280200), (Int.ofNat 3002762785938047352), (Int.negSucc 2596440607359603119), (Int.negSucc 10807433192721656447), (Int.negSucc 50812732522436255), (Int.ofNat 804024851795954784)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8988388944393599), (Int.negSucc 256389849424485215), (Int.negSucc 392558737400847359), (Int.ofNat 1328906272351279968), (Int.ofNat 777396387248510976), (Int.negSucc 93668811578288639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2888499693234816), (Int.ofNat 46125086735650464), (Int.negSucc 41702419132863839), (Int.negSucc 95641429946140799)]]

theorem h4n74_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p73).getD 0 []=h4p74.getD 0 [] := by
  decide +kernel

theorem h4n74_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p73).getD 1 []=h4p74.getD 1 [] := by
  decide +kernel

theorem h4n74_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p73).getD 2 []=h4p74.getD 2 [] := by
  decide +kernel

theorem h4n74_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p73).getD 3 []=h4p74.getD 3 [] := by
  decide +kernel

theorem h4n74_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p73).getD 4 []=h4p74.getD 4 [] := by
  decide +kernel

theorem h4n74_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p73).getD 5 []=h4p74.getD 5 [] := by
  decide +kernel

theorem h4n74_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p73).getD 6 []=h4p74.getD 6 [] := by
  decide +kernel

theorem h4n74_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p73).getD 7 []=h4p74.getD 7 [] := by
  decide +kernel

theorem h4n74_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p73).getD 8 []=h4p74.getD 8 [] := by
  decide +kernel

theorem h4n74_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p73).getD 9 []=h4p74.getD 9 [] := by
  decide +kernel

theorem h4n74_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p73).getD 10 []=h4p74.getD 10 [] := by
  decide +kernel

theorem h4n74_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p73).getD 11 []=h4p74.getD 11 [] := by
  decide +kernel

theorem h4n74_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p73).getD 12 []=h4p74.getD 12 [] := by
  decide +kernel

theorem h4n74_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p73).getD 13 []=h4p74.getD 13 [] := by
  decide +kernel

theorem h4n74_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p73).getD 14 []=h4p74.getD 14 [] := by
  decide +kernel

theorem h4n74_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p73).getD 15 []=h4p74.getD 15 [] := by
  decide +kernel

theorem h4n74_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p73).getD 16 []=h4p74.getD 16 [] := by
  decide +kernel

theorem h4n74_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p73).getD 17 []=h4p74.getD 17 [] := by
  decide +kernel

theorem h4n74_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p73).getD 18 []=h4p74.getD 18 [] := by
  decide +kernel

theorem h4n74_arithmetic : BiPoly.mul h4p13 h4p73=h4p74 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p73).getD j.val []=h4p74.getD j.val [] :=
      (fun j => Fin.cases h4n74_arithmetic_row0 (fun j => Fin.cases h4n74_arithmetic_row1 (fun j => Fin.cases h4n74_arithmetic_row2 (fun j => Fin.cases h4n74_arithmetic_row3 (fun j => Fin.cases h4n74_arithmetic_row4 (fun j => Fin.cases h4n74_arithmetic_row5 (fun j => Fin.cases h4n74_arithmetic_row6 (fun j => Fin.cases h4n74_arithmetic_row7 (fun j => Fin.cases h4n74_arithmetic_row8 (fun j => Fin.cases h4n74_arithmetic_row9 (fun j => Fin.cases h4n74_arithmetic_row10 (fun j => Fin.cases h4n74_arithmetic_row11 (fun j => Fin.cases h4n74_arithmetic_row12 (fun j => Fin.cases h4n74_arithmetic_row13 (fun j => Fin.cases h4n74_arithmetic_row14 (fun j => Fin.cases h4n74_arithmetic_row15 (fun j => Fin.cases h4n74_arithmetic_row16 (fun j => Fin.cases h4n74_arithmetic_row17 (fun j => Fin.cases h4n74_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n74 : h4e74.toBi mapPolyEnv=h4p74 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e73.toBi mapPolyEnv)=h4p74
  rw [h4n13, h4n73]
  exact h4n74_arithmetic

#print axioms h4n74_arithmetic
end StackSorting.RationalLift
