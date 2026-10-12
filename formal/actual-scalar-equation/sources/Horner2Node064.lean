import BivariateRowEquality
import Horner2Base
import Horner2Node063
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p64 : BiPoly.Poly := [[(Int.negSucc 175489289551871), (Int.negSucc 331682371153919), (Int.negSucc 1774334706020351), (Int.negSucc 4101856558276607), (Int.negSucc 213312575692799), (Int.ofNat 7517815049097216), (Int.ofNat 7378145922207744), (Int.ofNat 2130733231276032)], [(Int.ofNat 2177548455886848), (Int.ofNat 3533237579483136), (Int.ofNat 24290732773711872), (Int.ofNat 54891520978176000), (Int.ofNat 8406385669767168), (Int.negSucc 72607992999929855), (Int.negSucc 66642342838935551), (Int.negSucc 17860647656908799), (Int.negSucc 276206159609855)], [(Int.negSucc 12550033303658495), (Int.negSucc 18367643000318975), (Int.negSucc 157363422403286015), (Int.negSucc 340182989084795903), (Int.negSucc 83756483025767423), (Int.ofNat 314414855431621632), (Int.ofNat 290731468434158592), (Int.ofNat 90852276631495680), (Int.ofNat 8923535446477824), (Int.negSucc 731434830077951)], [(Int.ofNat 44576551580295168), (Int.ofNat 64047370351209984), (Int.ofNat 633409456827386880), (Int.ofNat 1304751355116125184), (Int.ofNat 465197465536920576), (Int.negSucc 765523851027720191), (Int.negSucc 820638170652331007), (Int.negSucc 342552782242446335), (Int.negSucc 57361906646313983), (Int.ofNat 4442996250966528), (Int.negSucc 18308197822463)], [(Int.negSucc 109176722969610239), (Int.negSucc 171646106283348479), (Int.negSucc 1760422560576099839), (Int.negSucc 3505131230779565567), (Int.negSucc 1750017114840107519), (Int.ofNat 987766504073980416), (Int.ofNat 1661281200263278080), (Int.ofNat 936247192257406464), (Int.ofNat 206893100168667648), (Int.negSucc 289235101575167), (Int.negSucc 1538735865034751), (Int.ofNat 72042014195712)], [(Int.ofNat 195460306244736000), (Int.ofNat 372784293523356672), (Int.ofNat 3570934187947917312), (Int.ofNat 7090170270366097920), (Int.ofNat 4787525650588922880), (Int.ofNat 29962430016219648), (Int.negSucc 2406791975141065727), (Int.negSucc 1820593987141028351), (Int.negSucc 541554512203229183), (Int.negSucc 56747632090424831), (Int.ofNat 9489843055690752), (Int.negSucc 500958724552703), (Int.ofNat 10915456696320)], [(Int.negSucc 264580806300503039), (Int.negSucc 658481543550133247), (Int.negSucc 5474015690302946303), (Int.negSucc 11315238098792142335), (Int.negSucc 9849534926037668351), (Int.negSucc 3162149039895883775), (Int.ofNat 2096725742330397696), (Int.ofNat 2505449894961403392), (Int.ofNat 1084791499669421568), (Int.ofNat 209166331860341760), (Int.negSucc 14467110661521407), (Int.ofNat 159919672043520), (Int.negSucc 11244441550847)], [(Int.ofNat 276269335314951168), (Int.ofNat 932475103746077184), (Int.ofNat 6506077816213106688), (Int.ofNat 14643642062428778496), (Int.ofNat 15603608432081452032), (Int.ofNat 8133202356248558592), (Int.ofNat 201256548593430528), (Int.negSucc 2312704849236773375), (Int.negSucc 1591070746032829439), (Int.negSucc 428573187633495551), (Int.negSucc 23132774303634431), (Int.ofNat 4802249989200384), (Int.negSucc 164876324130815)], [(Int.negSucc 225009441091722239), (Int.negSucc 1043766711215325695), (Int.negSucc 6130203393958267391), (Int.negSucc 15533266820301080063), (Int.negSucc 19448963282090503679), (Int.negSucc 13241461751438676479), (Int.negSucc 4174298957253302783), (Int.ofNat 915223944503181312), (Int.ofNat 1565641965167520768), (Int.ofNat 616447857281991168), (Int.ofNat 115937455846030848), (Int.negSucc 9809522029661183), (Int.ofNat 262650180673536)], [(Int.ofNat 143564689835329536), (Int.ofNat 914243524630646784), (Int.ofNat 4679338988789277696), (Int.ofNat 13484420829894305280), (Int.ofNat 19449908126439475200), (Int.ofNat 16188140150595436032), (Int.ofNat 7985201813740747776), (Int.ofNat 1328145507291445248), (Int.negSucc 792169800668439551), (Int.negSucc 637468749676323839), (Int.negSucc 192631189481548799), (Int.negSucc 3528586745081855), (Int.ofNat 740047335585792)], [(Int.negSucc 71637074659842047), (Int.negSucc 621363377833337855), (Int.negSucc 2952690403818424319), (Int.negSucc 9511925048808930815), (Int.negSucc 15827747751178563071), (Int.negSucc 15594484783561832447), (Int.negSucc 9719362032274922495), (Int.negSucc 3414983842930477055), (Int.negSucc 322004553026024447), (Int.ofNat 394556036427902976), (Int.ofNat 180721925842105344), (Int.ofNat 33648374503784448), (Int.negSucc 1832753087219711)], [(Int.ofNat 27726701278574592), (Int.ofNat 324395738205245952), (Int.ofNat 1559569928760142848), (Int.ofNat 5418005347722212352), (Int.ofNat 10527151182248632320), (Int.ofNat 12045388944946332672), (Int.ofNat 8885720607660751872), (Int.ofNat 4307535376235630592), (Int.ofNat 1160297425798649856), (Int.ofNat 11874229083755520), (Int.negSucc 98117000600309759), (Int.negSucc 45067415358426623), (Int.negSucc 216624311691263)], [(Int.negSucc 8184949945270271), (Int.negSucc 128184716241827327), (Int.negSucc 686395415846693375), (Int.negSucc 2488974421173821951), (Int.negSucc 5682408842751290879), (Int.negSucc 7519346500843620863), (Int.negSucc 6428044206845124095), (Int.negSucc 3787410215860793855), (Int.negSucc 1420509884535728639), (Int.negSucc 315957083911543295), (Int.ofNat 4976316218875392), (Int.ofNat 23263100019385344), (Int.ofNat 3957145693009920)], [(Int.ofNat 1787774917174272), (Int.ofNat 37469527244639232), (Int.ofNat 245026871207626752), (Int.ofNat 926231982279421440), (Int.ofNat 2451070219081423872), (Int.ofNat 3798257376203048448), (Int.ofNat 3735055137097780224), (Int.ofNat 2527870448075484672), (Int.ofNat 1181582840525746176), (Int.ofNat 375069155344565760), (Int.ofNat 56974016237147136), (Int.ofNat 2650634773890048), (Int.negSucc 3947735145848831)], [(Int.negSucc 273434975517695), (Int.negSucc 7811340406508543), (Int.negSucc 67655706732112895), (Int.negSucc 280073096658964991), (Int.negSucc 830249426960979455), (Int.negSucc 1537516931304830975), (Int.negSucc 1741511878230057983), (Int.negSucc 1329983598933434879), (Int.negSucc 730753876473573887), (Int.negSucc 273301099524080639), (Int.negSucc 69650442052835327), (Int.negSucc 10838571788279807), (Int.ofNat 570126808977408)], [(Int.ofNat 26236048849920), (Int.ofNat 1092045940821504), (Int.ofNat 13528767154821120), (Int.ofNat 67747370017388544), (Int.ofNat 218099139431334912), (Int.ofNat 486825655936877568), (Int.ofNat 645941557172846592), (Int.ofNat 558501209210027520), (Int.ofNat 343528396748928000), (Int.ofNat 146872162395638784), (Int.ofNat 46817995438080000), (Int.ofNat 8191719484987392), (Int.ofNat 1288070990880768)], [(Int.negSucc 1191140121599), (Int.negSucc 91118817215999), (Int.negSucc 1784305710614015), (Int.negSucc 12397317043032575), (Int.negSucc 44185251824847359), (Int.negSucc 116214073113466367), (Int.negSucc 187034334177148415), (Int.negSucc 185359602698560511), (Int.negSucc 124624697807591423), (Int.negSucc 60367904546162687), (Int.negSucc 20396403317237759), (Int.negSucc 4401485882191871), (Int.negSucc 805318123069439)], [(Int.ofNat 0), (Int.ofNat 3398497689600), (Int.ofNat 132229263504384), (Int.ofNat 1530477717373440), (Int.ofNat 6804709489870848), (Int.ofNat 20058532433238528), (Int.ofNat 40636630506875904), (Int.ofNat 47379891347905536), (Int.ofNat 35175788483715072), (Int.ofNat 18547930413232128), (Int.ofNat 6284080687878144), (Int.ofNat 1673064610762752), (Int.ofNat 159856588357632)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3744883031039), (Int.negSucc 102323364410879), (Int.negSucc 738639383035391), (Int.negSucc 2420115515329535), (Int.negSucc 6151904178665471), (Int.negSucc 8965416676331519), (Int.negSucc 7569297767817215), (Int.negSucc 4122463783403519), (Int.negSucc 1476272424517631), (Int.negSucc 339800918261759), (Int.negSucc 10261620670463)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1986045143040), (Int.ofNat 44226645967872), (Int.ofNat 200396899722240), (Int.ofNat 574710244319232), (Int.ofNat 1160770815498240), (Int.ofNat 1172458340573184), (Int.ofNat 649296565346304), (Int.ofNat 246291473055744), (Int.ofNat 25236378206208)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 506545311743), (Int.negSucc 10027956971519), (Int.negSucc 28685453985791), (Int.negSucc 84033822117887), (Int.negSucc 117099548909567), (Int.negSucc 71917663518719), (Int.negSucc 19687894401023)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 49824129024), (Int.ofNat 925078745088), (Int.ofNat 1732638117888), (Int.ofNat 5570520367104), (Int.ofNat 4713136865280)]]

theorem h2n64_arithmetic_row0 :
    (BiPoly.mul h2p2 h2p63).getD 0 []=h2p64.getD 0 [] := by
  decide +kernel

theorem h2n64_arithmetic_row1 :
    (BiPoly.mul h2p2 h2p63).getD 1 []=h2p64.getD 1 [] := by
  decide +kernel

theorem h2n64_arithmetic_row2 :
    (BiPoly.mul h2p2 h2p63).getD 2 []=h2p64.getD 2 [] := by
  decide +kernel

theorem h2n64_arithmetic_row3 :
    (BiPoly.mul h2p2 h2p63).getD 3 []=h2p64.getD 3 [] := by
  decide +kernel

theorem h2n64_arithmetic_row4 :
    (BiPoly.mul h2p2 h2p63).getD 4 []=h2p64.getD 4 [] := by
  decide +kernel

theorem h2n64_arithmetic_row5 :
    (BiPoly.mul h2p2 h2p63).getD 5 []=h2p64.getD 5 [] := by
  decide +kernel

theorem h2n64_arithmetic_row6 :
    (BiPoly.mul h2p2 h2p63).getD 6 []=h2p64.getD 6 [] := by
  decide +kernel

theorem h2n64_arithmetic_row7 :
    (BiPoly.mul h2p2 h2p63).getD 7 []=h2p64.getD 7 [] := by
  decide +kernel

theorem h2n64_arithmetic_row8 :
    (BiPoly.mul h2p2 h2p63).getD 8 []=h2p64.getD 8 [] := by
  decide +kernel

theorem h2n64_arithmetic_row9 :
    (BiPoly.mul h2p2 h2p63).getD 9 []=h2p64.getD 9 [] := by
  decide +kernel

theorem h2n64_arithmetic_row10 :
    (BiPoly.mul h2p2 h2p63).getD 10 []=h2p64.getD 10 [] := by
  decide +kernel

theorem h2n64_arithmetic_row11 :
    (BiPoly.mul h2p2 h2p63).getD 11 []=h2p64.getD 11 [] := by
  decide +kernel

theorem h2n64_arithmetic_row12 :
    (BiPoly.mul h2p2 h2p63).getD 12 []=h2p64.getD 12 [] := by
  decide +kernel

theorem h2n64_arithmetic_row13 :
    (BiPoly.mul h2p2 h2p63).getD 13 []=h2p64.getD 13 [] := by
  decide +kernel

theorem h2n64_arithmetic_row14 :
    (BiPoly.mul h2p2 h2p63).getD 14 []=h2p64.getD 14 [] := by
  decide +kernel

theorem h2n64_arithmetic_row15 :
    (BiPoly.mul h2p2 h2p63).getD 15 []=h2p64.getD 15 [] := by
  decide +kernel

theorem h2n64_arithmetic_row16 :
    (BiPoly.mul h2p2 h2p63).getD 16 []=h2p64.getD 16 [] := by
  decide +kernel

theorem h2n64_arithmetic_row17 :
    (BiPoly.mul h2p2 h2p63).getD 17 []=h2p64.getD 17 [] := by
  decide +kernel

theorem h2n64_arithmetic_row18 :
    (BiPoly.mul h2p2 h2p63).getD 18 []=h2p64.getD 18 [] := by
  decide +kernel

theorem h2n64_arithmetic_row19 :
    (BiPoly.mul h2p2 h2p63).getD 19 []=h2p64.getD 19 [] := by
  decide +kernel

theorem h2n64_arithmetic_row20 :
    (BiPoly.mul h2p2 h2p63).getD 20 []=h2p64.getD 20 [] := by
  decide +kernel

theorem h2n64_arithmetic_row21 :
    (BiPoly.mul h2p2 h2p63).getD 21 []=h2p64.getD 21 [] := by
  decide +kernel

theorem h2n64_arithmetic : BiPoly.mul h2p2 h2p63=h2p64 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h2p2 h2p63).getD j.val []=h2p64.getD j.val [] :=
      (fun j => Fin.cases h2n64_arithmetic_row0 (fun j => Fin.cases h2n64_arithmetic_row1 (fun j => Fin.cases h2n64_arithmetic_row2 (fun j => Fin.cases h2n64_arithmetic_row3 (fun j => Fin.cases h2n64_arithmetic_row4 (fun j => Fin.cases h2n64_arithmetic_row5 (fun j => Fin.cases h2n64_arithmetic_row6 (fun j => Fin.cases h2n64_arithmetic_row7 (fun j => Fin.cases h2n64_arithmetic_row8 (fun j => Fin.cases h2n64_arithmetic_row9 (fun j => Fin.cases h2n64_arithmetic_row10 (fun j => Fin.cases h2n64_arithmetic_row11 (fun j => Fin.cases h2n64_arithmetic_row12 (fun j => Fin.cases h2n64_arithmetic_row13 (fun j => Fin.cases h2n64_arithmetic_row14 (fun j => Fin.cases h2n64_arithmetic_row15 (fun j => Fin.cases h2n64_arithmetic_row16 (fun j => Fin.cases h2n64_arithmetic_row17 (fun j => Fin.cases h2n64_arithmetic_row18 (fun j => Fin.cases h2n64_arithmetic_row19 (fun j => Fin.cases h2n64_arithmetic_row20 (fun j => Fin.cases h2n64_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n64 : h2e64.toBi mapPolyEnv=h2p64 := by
  change BiPoly.mul (h2e2.toBi mapPolyEnv) (h2e63.toBi mapPolyEnv)=h2p64
  rw [h2n2, h2n63]
  exact h2n64_arithmetic

#print axioms h2n64_arithmetic
end StackSorting.RationalLift
