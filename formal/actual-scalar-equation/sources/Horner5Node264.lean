import BivariateRowEquality
import Horner5Node059
import Horner5Node030
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p264 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5458222429765632), (Int.negSucc 6658557735813119), (Int.ofNat 108582617109861504), (Int.negSucc 67139273808261503), (Int.ofNat 342678884055766272), (Int.ofNat 37294038586858752), (Int.negSucc 1704780054782994815), (Int.negSucc 466889204459537279), (Int.ofNat 1549319447973316608), (Int.ofNat 804652114202468352)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 45900780377407487), (Int.ofNat 62508076215929856), (Int.negSucc 1096836413488600319), (Int.ofNat 656456485374397440), (Int.negSucc 4787284471004928383), (Int.negSucc 1188368193871793663), (Int.ofNat 15397943652700632576), (Int.ofNat 4852854226497010176), (Int.negSucc 9470773130144549759), (Int.negSucc 3740990399347894271), (Int.ofNat 447028952334704640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 174495796811532288), (Int.negSucc 209437396875371519), (Int.ofNat 4866759534813221664), (Int.negSucc 2462473396341427103), (Int.ofNat 27191252941748419104), (Int.ofNat 7896015223103196000), (Int.negSucc 59357953234180048031), (Int.negSucc 19959157692414876383), (Int.ofNat 24123993551551969632), (Int.ofNat 8024886181538265888), (Int.negSucc 928349445045044735), (Int.ofNat 62087354490931200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 397116287112167423), (Int.ofNat 256584315768606720), (Int.negSucc 12535573547554394975), (Int.ofNat 3143128372258463424), (Int.negSucc 86497789762300185503), (Int.negSucc 28732371574520552831), (Int.ofNat 125051114252439409248), (Int.ofNat 50573668816497145536), (Int.negSucc 25763149102720007519), (Int.negSucc 11512518367644781055), (Int.negSucc 1363538585982375935), (Int.ofNat 63989113465405440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 604319413409957376), (Int.ofNat 245556954576809856), (Int.ofNat 20999686255533132768), (Int.ofNat 5918287720611629664), (Int.ofNat 174206506829153318784), (Int.ofNat 75643784685090084096), (Int.negSucc 146341437561463262111), (Int.negSucc 94208223789786459167), (Int.negSucc 9602460795167355455), (Int.ofNat 13557052048654987200), (Int.ofNat 6290238902356627200), (Int.negSucc 491061733125470207)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 651052344974404607), (Int.negSucc 1348325629829142911), (Int.negSucc 24526131112975794335), (Int.negSucc 29888068670468430335), (Int.negSucc 237238109657033243903), (Int.negSucc 156337839218642062463), (Int.ofNat 64128235284245647584), (Int.ofNat 128838848714762797440), (Int.ofNat 62555496193706356800), (Int.negSucc 8733042287497609343), (Int.negSucc 7239113135939494655), (Int.ofNat 67880192523503616)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 513085593385987200), (Int.ofNat 2283639674649508224), (Int.ofNat 21268099661492892096), (Int.ofNat 55168528092662182464), (Int.ofNat 230413930623645892416), (Int.ofNat 245164087873937014848), (Int.ofNat 77390062319784574368), (Int.negSucc 109225478807648570015), (Int.negSucc 81714925236892864031), (Int.negSucc 9397770471040442975), (Int.ofNat 1760094389509588224), (Int.ofNat 1365971949922595328)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 301343498830014335), (Int.negSucc 2293526149381617407), (Int.negSucc 14696496094973594687), (Int.negSucc 60219340741247081471), (Int.negSucc 170571363746285640383), (Int.negSucc 277472352272606161919), (Int.negSucc 175415245559624453471), (Int.ofNat 22522063595245201728), (Int.ofNat 54143690515086024864), (Int.ofNat 27051647252345018496), (Int.ofNat 3591042524690238720), (Int.negSucc 1438976493762333695)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 132888698759832192), (Int.ofNat 1536497989344579456), (Int.ofNat 8579189076905376576), (Int.ofNat 43174153350524981952), (Int.ofNat 104382931903655545728), (Int.ofNat 221193798993720554112), (Int.ofNat 186916970751736736160), (Int.ofNat 66087044377528172832), (Int.negSucc 12021676587731403647), (Int.negSucc 23098638900987634175), (Int.negSucc 4589899950414574079), (Int.negSucc 302536109773426175)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 43804126021021055), (Int.negSucc 713323303542888191), (Int.negSucc 4221685385558146367), (Int.negSucc 21321080408647281023), (Int.negSucc 55042749510467582591), (Int.negSucc 124355674719447159167), (Int.negSucc 139373376523610776415), (Int.negSucc 89979092738301799295), (Int.negSucc 17037804512793504383), (Int.ofNat 4718604465527010048), (Int.ofNat 3022390241962541568), (Int.ofNat 1134433842734389248)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10572364380675456), (Int.ofNat 230532703260181632), (Int.ofNat 1634383943077356576), (Int.ofNat 7551943036435894752), (Int.ofNat 23724393635082904992), (Int.ofNat 50708390148758862432), (Int.ofNat 76374181562770697472), (Int.ofNat 61437063607543774080), (Int.ofNat 25038484384007889792), (Int.ofNat 6063230686004620416), (Int.negSucc 786336522376412159), (Int.negSucc 360911362733770751)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1783275944441471), (Int.negSucc 50525331246800639), (Int.negSucc 454217357970654047), (Int.negSucc 2010556695110272703), (Int.negSucc 7532745825466035359), (Int.negSucc 15847330089741798527), (Int.negSucc 29525972257813632767), (Int.negSucc 27774253006367970815), (Int.negSucc 17239980595434675839), (Int.negSucc 5584005452104409087), (Int.negSucc 800885077777658879), (Int.negSucc 223207352283709439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 189926552331648), (Int.ofNat 6970569777554688), (Int.ofNat 82472957848766304), (Int.ofNat 410914965850878816), (Int.ofNat 1609486181888420736), (Int.ofNat 3930135197520817152), (Int.ofNat 7582913589193037568), (Int.ofNat 9148914976240887552), (Int.ofNat 6768547336871000064), (Int.ofNat 2524646589090674688), (Int.ofNat 828872436343265280), (Int.ofNat 122448071352895488)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9702470625407), (Int.negSucc 504499494946175), (Int.negSucc 8635858945724447), (Int.negSucc 59366011922432639), (Int.negSucc 219185898523355519), (Int.negSucc 709504002856984319), (Int.negSucc 1253614919042532095), (Int.negSucc 2103391636851474431), (Int.negSucc 1543284337278210047), (Int.negSucc 791012716746928127), (Int.negSucc 234928260927019007)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10584513409536), (Int.ofNat 404611371777024), (Int.ofNat 4714593955394688), (Int.ofNat 19038038901183360), (Int.ofNat 72247158236783232), (Int.ofNat 141704222716283904), (Int.ofNat 264975025576790016), (Int.ofNat 230544445107787776), (Int.ofNat 138311125306398720)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2886685475327), (Int.negSucc 101420128636415), (Int.negSucc 990167050479743), (Int.negSucc 2291392438695935), (Int.negSucc 10448696011650047), (Int.negSucc 9397994909368319), (Int.negSucc 25830935732275199)]]

theorem h5n264_arithmetic_row0 :
    (BiPoly.mul h5p59 h5p30).getD 0 []=h5p264.getD 0 [] := by
  decide +kernel

theorem h5n264_arithmetic_row1 :
    (BiPoly.mul h5p59 h5p30).getD 1 []=h5p264.getD 1 [] := by
  decide +kernel

theorem h5n264_arithmetic_row2 :
    (BiPoly.mul h5p59 h5p30).getD 2 []=h5p264.getD 2 [] := by
  decide +kernel

theorem h5n264_arithmetic_row3 :
    (BiPoly.mul h5p59 h5p30).getD 3 []=h5p264.getD 3 [] := by
  decide +kernel

theorem h5n264_arithmetic_row4 :
    (BiPoly.mul h5p59 h5p30).getD 4 []=h5p264.getD 4 [] := by
  decide +kernel

theorem h5n264_arithmetic_row5 :
    (BiPoly.mul h5p59 h5p30).getD 5 []=h5p264.getD 5 [] := by
  decide +kernel

theorem h5n264_arithmetic_row6 :
    (BiPoly.mul h5p59 h5p30).getD 6 []=h5p264.getD 6 [] := by
  decide +kernel

theorem h5n264_arithmetic_row7 :
    (BiPoly.mul h5p59 h5p30).getD 7 []=h5p264.getD 7 [] := by
  decide +kernel

theorem h5n264_arithmetic_row8 :
    (BiPoly.mul h5p59 h5p30).getD 8 []=h5p264.getD 8 [] := by
  decide +kernel

theorem h5n264_arithmetic_row9 :
    (BiPoly.mul h5p59 h5p30).getD 9 []=h5p264.getD 9 [] := by
  decide +kernel

theorem h5n264_arithmetic_row10 :
    (BiPoly.mul h5p59 h5p30).getD 10 []=h5p264.getD 10 [] := by
  decide +kernel

theorem h5n264_arithmetic_row11 :
    (BiPoly.mul h5p59 h5p30).getD 11 []=h5p264.getD 11 [] := by
  decide +kernel

theorem h5n264_arithmetic_row12 :
    (BiPoly.mul h5p59 h5p30).getD 12 []=h5p264.getD 12 [] := by
  decide +kernel

theorem h5n264_arithmetic_row13 :
    (BiPoly.mul h5p59 h5p30).getD 13 []=h5p264.getD 13 [] := by
  decide +kernel

theorem h5n264_arithmetic_row14 :
    (BiPoly.mul h5p59 h5p30).getD 14 []=h5p264.getD 14 [] := by
  decide +kernel

theorem h5n264_arithmetic_row15 :
    (BiPoly.mul h5p59 h5p30).getD 15 []=h5p264.getD 15 [] := by
  decide +kernel

theorem h5n264_arithmetic : BiPoly.mul h5p59 h5p30=h5p264 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h5p59 h5p30).getD j.val []=h5p264.getD j.val [] :=
      (fun j => Fin.cases h5n264_arithmetic_row0 (fun j => Fin.cases h5n264_arithmetic_row1 (fun j => Fin.cases h5n264_arithmetic_row2 (fun j => Fin.cases h5n264_arithmetic_row3 (fun j => Fin.cases h5n264_arithmetic_row4 (fun j => Fin.cases h5n264_arithmetic_row5 (fun j => Fin.cases h5n264_arithmetic_row6 (fun j => Fin.cases h5n264_arithmetic_row7 (fun j => Fin.cases h5n264_arithmetic_row8 (fun j => Fin.cases h5n264_arithmetic_row9 (fun j => Fin.cases h5n264_arithmetic_row10 (fun j => Fin.cases h5n264_arithmetic_row11 (fun j => Fin.cases h5n264_arithmetic_row12 (fun j => Fin.cases h5n264_arithmetic_row13 (fun j => Fin.cases h5n264_arithmetic_row14 (fun j => Fin.cases h5n264_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n264 : h5e264.toBi mapPolyEnv=h5p264 := by
  change BiPoly.mul (h5e59.toBi mapPolyEnv) (h5e30.toBi mapPolyEnv)=h5p264
  rw [h5n59, h5n30]
  exact h5n264_arithmetic

#print axioms h5n264_arithmetic
end StackSorting.RationalLift
