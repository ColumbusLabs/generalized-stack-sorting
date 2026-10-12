import BivariateRowEquality
import Horner2Base
import Horner2Node097
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p98 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5329012775748231168), (Int.ofNat 13146885504759588480), (Int.ofNat 20565782288051287680), (Int.ofNat 156875652249027372288), (Int.negSucc 286389481986038760191), (Int.negSucc 441925137204091037567), (Int.ofNat 324280365641297069184), (Int.ofNat 335688278169361904640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 63628801439874236927), (Int.negSucc 156453689121415816319), (Int.negSucc 328699862877149879039), (Int.negSucc 2269145680053659184383), (Int.ofNat 3532905056418635377152), (Int.ofNat 4833474447695361554304), (Int.negSucc 3245172072127241289983), (Int.negSucc 2790019059499711959551), (Int.ofNat 116792314826859988992)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 360592242255629402112), (Int.ofNat 866824530952341332448), (Int.ofNat 2492790029567962092576), (Int.ofNat 14512188849769188333792), (Int.negSucc 20110201368886886097887), (Int.negSucc 23665788288889616236895), (Int.ofNat 13746509391627126921312), (Int.ofNat 10661882732999892326304), (Int.ofNat 195420612596268663648), (Int.negSucc 58239163381501986047)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1289063272506195877631), (Int.negSucc 2972916087052878397727), (Int.negSucc 11860615912626908802431), (Int.negSucc 54831212035062620053535), (Int.ofNat 67644910645268783262912), (Int.ofNat 69320844295212023927136), (Int.negSucc 27859816580921928172799), (Int.negSucc 25133806480187565383903), (Int.negSucc 5412761239097648031551), (Int.ofNat 774391697243509498560), (Int.negSucc 30383147113982986751)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3254628667752684307008), (Int.ofNat 7139907154223248495584), (Int.ofNat 39118154811423828484512), (Int.ofNat 137455817808989420451456), (Int.negSucc 142233257585121822470783), (Int.negSucc 139369326691947834966239), (Int.ofNat 10406471552479875408288), (Int.ofNat 42146409280775198368320), (Int.ofNat 22587835290180517778688), (Int.negSucc 2363958116551047812927), (Int.ofNat 126197768717059233408), (Int.negSucc 3377981141816540159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6151109968545927624639), (Int.negSucc 13029871506526889672975), (Int.negSucc 93633363578020154331327), (Int.negSucc 244358910111599648316927), (Int.ofNat 174093811457945398948992), (Int.ofNat 214364466723896398136064), (Int.ofNat 84592481052971440610624), (Int.negSucc 49870560066861996110783), (Int.negSucc 45558379701516681360063), (Int.negSucc 272610656371488477871), (Int.ofNat 254520491099484720000), (Int.negSucc 5614153309405822719), (Int.ofNat 17598899869337600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8994006470914918957056), (Int.ofNat 19351144582208484796272), (Int.ofNat 166830072631973341423456), (Int.ofNat 326267909238451338191616), (Int.negSucc 59794577766985196141695), (Int.negSucc 270396049095939163286143), (Int.negSucc 229792414587733395215455), (Int.ofNat 19656683682686067363040), (Int.ofNat 48973676148414648087968), (Int.ofNat 15323808058871020862512), (Int.negSucc 1686395202689661807135), (Int.ofNat 61457297873335471104), (Int.negSucc 625512712997201919)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10370438014983958097567), (Int.negSucc 24669645483284745825711), (Int.negSucc 224944940060047870187359), (Int.negSucc 352691956946834482943551), (Int.negSucc 198218185574645200706431), (Int.ofNat 261053974008925572812800), (Int.ofNat 310027501090930708873216), (Int.ofNat 74387298813737401898016), (Int.negSucc 19335478737557277896223), (Int.negSucc 33979009874024978261103), (Int.ofNat 1374060297968411503840), (Int.ofNat 24222426290024841216), (Int.negSucc 1704861773013101567)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9529176794135050492000), (Int.ofNat 27574066136187262106576), (Int.ofNat 232527060813205680342320), (Int.ofNat 340080845689323152978912), (Int.ofNat 435127205931465676856992), (Int.negSucc 120074295637670570099423), (Int.negSucc 255809761691081875191455), (Int.negSucc 187117094289559257735071), (Int.negSucc 25453346844224494937727), (Int.ofNat 29018581319037713844528), (Int.ofNat 4775442797589602454160), (Int.negSucc 398561142172680037823), (Int.ofNat 6998252826794246656)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7010586471138472329663), (Int.negSucc 26607872353874324860031), (Int.negSucc 186875247768021269402431), (Int.negSucc 310936689299782681563887), (Int.negSucc 493120866971746217730175), (Int.negSucc 130252310031290429577375), (Int.ofNat 119424308330123600751552), (Int.ofNat 211196950317030801339776), (Int.ofNat 62986449177449399779264), (Int.ofNat 3182839148731537016320), (Int.negSucc 11403166143567317914303), (Int.ofNat 287895305387810290800), (Int.ofNat 12202726416278743936)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4130040042920080075008), (Int.ofNat 21440468693792306660576), (Int.ofNat 119321712375607478572144), (Int.ofNat 259950989592888976781440), (Int.ofNat 390619310416721297279424), (Int.ofNat 329173234138404822758816), (Int.ofNat 21475763428525590741152), (Int.negSucc 116701385031940035091295), (Int.negSucc 78471127840454201487391), (Int.negSucc 29301999855325482119455), (Int.ofNat 7389743605526307215120), (Int.ofNat 874626546293776840896), (Int.negSucc 33972084729475076351)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1940483040172584261055), (Int.negSucc 13981326725891132789631), (Int.negSucc 62870540535133787986911), (Int.negSucc 182775186957388439594735), (Int.negSucc 251268462286616539329407), (Int.negSucc 347308521587776759631199), (Int.negSucc 127103448917795124072511), (Int.negSucc 3019451818717551409535), (Int.ofNat 58339061901529176686720), (Int.ofNat 28368957766743710793536), (Int.ofNat 4202441063408639476832), (Int.negSucc 1534432720413159299695), (Int.negSucc 18721104595731314495)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 720856785225684027008), (Int.ofNat 7207184892942826742400), (Int.ofNat 28871473392565536919168), (Int.ofNat 102066770710006958142848), (Int.ofNat 147581632620443084688160), (Int.ofNat 232977202199910475408128), (Int.ofNat 165548864874947969532224), (Int.ofNat 63727035737725866263040), (Int.negSucc 13684091502359201991167), (Int.negSucc 13888869257895216320383), (Int.negSucc 9133505659036162157951), (Int.ofNat 382421333678838885216), (Int.ofNat 80502174124996135104)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 208586329175127730367), (Int.negSucc 2883653180776079219343), (Int.negSucc 12053070890884124638015), (Int.negSucc 44594604370230884018911), (Int.negSucc 80221297508919879229887), (Int.negSucc 113081377099264926379295), (Int.negSucc 131191230291375897663935), (Int.negSucc 67317290422588494604127), (Int.negSucc 19427628893427919002815), (Int.ofNat 2033354839589054517888), (Int.ofNat 4775898955268540854080), (Int.ofNat 968739553484996605920), (Int.negSucc 27896469032838069503)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 45879194757638746496), (Int.ofNat 879787229198876316080), (Int.ofNat 4504694395618446548928), (Int.ofNat 15610251310837054126208), (Int.ofNat 36993351226204318602560), (Int.ofNat 45448914643243754749216), (Int.ofNat 68962949048826003237696), (Int.ofNat 47444470287715513414368), (Int.ofNat 24392105646107914646496), (Int.ofNat 4099208513634082315872), (Int.ofNat 91387074514700280672), (Int.negSucc 861258241829523133439), (Int.negSucc 56414089614886003583)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7368215351664573855), (Int.negSucc 200318857308259326767), (Int.negSucc 1406578238567837066015), (Int.negSucc 4630319183279159074207), (Int.negSucc 13321124767043693507711), (Int.negSucc 17227230551396389988063), (Int.negSucc 24886572378193017034559), (Int.negSucc 24961225460421550128767), (Int.negSucc 14934735335377090802303), (Int.negSucc 5269926116283328341215), (Int.negSucc 1321116609936270465791), (Int.ofNat 98266039518788451648), (Int.ofNat 47377535552805489408)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 805966074519987168), (Int.ofNat 33026851347601837392), (Int.ofNat 338840255239746798384), (Int.ofNat 1220139262600316527968), (Int.ofNat 3632192450769555273312), (Int.ofNat 6054506184682293143616), (Int.ofNat 6636365986126687510464), (Int.ofNat 9346980192918149376864), (Int.ofNat 6308029244597503126752), (Int.ofNat 3323198658379649715072), (Int.ofNat 893736427204820944512), (Int.ofNat 192943044354502516608), (Int.ofNat 1127559450632055552)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 52531438619466431), (Int.negSucc 3759323739309470303), (Int.negSucc 58587327863994197951), (Int.negSucc 276846517729293987887), (Int.negSucc 766689729350894051903), (Int.negSucc 1714872741499074387455), (Int.negSucc 1567970946130513609151), (Int.negSucc 2317531892936203423583), (Int.negSucc 2037646217890326372479), (Int.negSucc 1244990654400550280255), (Int.negSucc 421108434514775100671), (Int.negSucc 114481587162914610047), (Int.negSucc 13048270566227352575)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1467940469973120), (Int.ofNat 269769398504843808), (Int.ofNat 6717558402377565264), (Int.ofNat 48346289077521176352), (Int.ofNat 133323633900665950176), (Int.ofNat 348991173249297570720), (Int.ofNat 381385258984807629984), (Int.ofNat 357928369253568451584), (Int.ofNat 480110929241212902528), (Int.ofNat 300820824872129092608), (Int.ofNat 139101296953506475392), (Int.ofNat 33157539317511843840), (Int.ofNat 4554353187847918080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9518181177340799), (Int.negSucc 451137628025453087), (Int.negSucc 5605109418962160143), (Int.negSucc 19625901986532740543), (Int.negSucc 48082075909960919327), (Int.negSucc 81163548694811731967), (Int.negSucc 37023541310155632191), (Int.negSucc 68148282311859873023), (Int.negSucc 51069406780030452479), (Int.negSucc 27086385808669694975), (Int.negSucc 6432265418241401855), (Int.negSucc 423943465569214463)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 13265778671910144), (Int.ofNat 348394460925145536), (Int.ofNat 2163099683083170528), (Int.ofNat 4472325681247444608), (Int.ofNat 11462216221546220160), (Int.ofNat 4857412422125798784), (Int.ofNat 3313557632374682112), (Int.ofNat 5587477866161750016), (Int.ofNat 3011427268527513600), (Int.ofNat 618659645452959744)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6587274048330239), (Int.negSucc 128656455461999999), (Int.negSucc 319039492018988735), (Int.negSucc 796179690027014399), (Int.negSucc 895239825819331967), (Int.ofNat 415378244714692608), (Int.negSucc 230115871680224255), (Int.negSucc 194716179883745279)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1060923863356416), (Int.ofNat 17972197365443328), (Int.ofNat 6575887061705088), (Int.ofNat 88916388106217472), (Int.negSucc 62899118940418559)]]

theorem h2n98_arithmetic_row0 :
    (BiPoly.mul h2p94 h2p97).getD 0 []=h2p98.getD 0 [] := by
  decide +kernel

theorem h2n98_arithmetic_row1 :
    (BiPoly.mul h2p94 h2p97).getD 1 []=h2p98.getD 1 [] := by
  decide +kernel

theorem h2n98_arithmetic_row2 :
    (BiPoly.mul h2p94 h2p97).getD 2 []=h2p98.getD 2 [] := by
  decide +kernel

theorem h2n98_arithmetic_row3 :
    (BiPoly.mul h2p94 h2p97).getD 3 []=h2p98.getD 3 [] := by
  decide +kernel

theorem h2n98_arithmetic_row4 :
    (BiPoly.mul h2p94 h2p97).getD 4 []=h2p98.getD 4 [] := by
  decide +kernel

theorem h2n98_arithmetic_row5 :
    (BiPoly.mul h2p94 h2p97).getD 5 []=h2p98.getD 5 [] := by
  decide +kernel

theorem h2n98_arithmetic_row6 :
    (BiPoly.mul h2p94 h2p97).getD 6 []=h2p98.getD 6 [] := by
  decide +kernel

theorem h2n98_arithmetic_row7 :
    (BiPoly.mul h2p94 h2p97).getD 7 []=h2p98.getD 7 [] := by
  decide +kernel

theorem h2n98_arithmetic_row8 :
    (BiPoly.mul h2p94 h2p97).getD 8 []=h2p98.getD 8 [] := by
  decide +kernel

theorem h2n98_arithmetic_row9 :
    (BiPoly.mul h2p94 h2p97).getD 9 []=h2p98.getD 9 [] := by
  decide +kernel

theorem h2n98_arithmetic_row10 :
    (BiPoly.mul h2p94 h2p97).getD 10 []=h2p98.getD 10 [] := by
  decide +kernel

theorem h2n98_arithmetic_row11 :
    (BiPoly.mul h2p94 h2p97).getD 11 []=h2p98.getD 11 [] := by
  decide +kernel

theorem h2n98_arithmetic_row12 :
    (BiPoly.mul h2p94 h2p97).getD 12 []=h2p98.getD 12 [] := by
  decide +kernel

theorem h2n98_arithmetic_row13 :
    (BiPoly.mul h2p94 h2p97).getD 13 []=h2p98.getD 13 [] := by
  decide +kernel

theorem h2n98_arithmetic_row14 :
    (BiPoly.mul h2p94 h2p97).getD 14 []=h2p98.getD 14 [] := by
  decide +kernel

theorem h2n98_arithmetic_row15 :
    (BiPoly.mul h2p94 h2p97).getD 15 []=h2p98.getD 15 [] := by
  decide +kernel

theorem h2n98_arithmetic_row16 :
    (BiPoly.mul h2p94 h2p97).getD 16 []=h2p98.getD 16 [] := by
  decide +kernel

theorem h2n98_arithmetic_row17 :
    (BiPoly.mul h2p94 h2p97).getD 17 []=h2p98.getD 17 [] := by
  decide +kernel

theorem h2n98_arithmetic_row18 :
    (BiPoly.mul h2p94 h2p97).getD 18 []=h2p98.getD 18 [] := by
  decide +kernel

theorem h2n98_arithmetic_row19 :
    (BiPoly.mul h2p94 h2p97).getD 19 []=h2p98.getD 19 [] := by
  decide +kernel

theorem h2n98_arithmetic_row20 :
    (BiPoly.mul h2p94 h2p97).getD 20 []=h2p98.getD 20 [] := by
  decide +kernel

theorem h2n98_arithmetic_row21 :
    (BiPoly.mul h2p94 h2p97).getD 21 []=h2p98.getD 21 [] := by
  decide +kernel

theorem h2n98_arithmetic_row22 :
    (BiPoly.mul h2p94 h2p97).getD 22 []=h2p98.getD 22 [] := by
  decide +kernel

theorem h2n98_arithmetic : BiPoly.mul h2p94 h2p97=h2p98 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<23 at hk
    have hf : ∀ j : Fin 23, (BiPoly.mul h2p94 h2p97).getD j.val []=h2p98.getD j.val [] :=
      (fun j => Fin.cases h2n98_arithmetic_row0 (fun j => Fin.cases h2n98_arithmetic_row1 (fun j => Fin.cases h2n98_arithmetic_row2 (fun j => Fin.cases h2n98_arithmetic_row3 (fun j => Fin.cases h2n98_arithmetic_row4 (fun j => Fin.cases h2n98_arithmetic_row5 (fun j => Fin.cases h2n98_arithmetic_row6 (fun j => Fin.cases h2n98_arithmetic_row7 (fun j => Fin.cases h2n98_arithmetic_row8 (fun j => Fin.cases h2n98_arithmetic_row9 (fun j => Fin.cases h2n98_arithmetic_row10 (fun j => Fin.cases h2n98_arithmetic_row11 (fun j => Fin.cases h2n98_arithmetic_row12 (fun j => Fin.cases h2n98_arithmetic_row13 (fun j => Fin.cases h2n98_arithmetic_row14 (fun j => Fin.cases h2n98_arithmetic_row15 (fun j => Fin.cases h2n98_arithmetic_row16 (fun j => Fin.cases h2n98_arithmetic_row17 (fun j => Fin.cases h2n98_arithmetic_row18 (fun j => Fin.cases h2n98_arithmetic_row19 (fun j => Fin.cases h2n98_arithmetic_row20 (fun j => Fin.cases h2n98_arithmetic_row21 (fun j => Fin.cases h2n98_arithmetic_row22 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n98 : h2e98.toBi mapPolyEnv=h2p98 := by
  change BiPoly.mul (h2e94.toBi mapPolyEnv) (h2e97.toBi mapPolyEnv)=h2p98
  rw [h2n94, h2n97]
  exact h2n98_arithmetic

#print axioms h2n98_arithmetic
end StackSorting.RationalLift
