import BivariateRowEquality
import Horner1Base
import Horner1Node086
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p87 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 383795076249944064), (Int.ofNat 1109184421963567104), (Int.ofNat 4605859347780132864), (Int.ofNat 12851230295017451520), (Int.ofNat 9437274895991095296), (Int.negSucc 15974946909335457791), (Int.negSucc 32577466644243947519), (Int.negSucc 20795918708669018111), (Int.negSucc 4659913576800681983)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7335146947144531967), (Int.negSucc 18688459753489729535), (Int.negSucc 89546334818358527999), (Int.negSucc 247114221400609228799), (Int.negSucc 174372365569066076159), (Int.ofNat 245348685521130645504), (Int.ofNat 469762064123970299904), (Int.ofNat 278922296378584885248), (Int.ofNat 62462630136349108224), (Int.ofNat 2502546180133699584)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 66834774402018729984), (Int.ofNat 151520296121144672256), (Int.ofNat 850392328963942711296), (Int.ofNat 2274016878170618148864), (Int.ofNat 1560887002973079539712), (Int.negSucc 1717252821627560404991), (Int.negSucc 3236687394846827618303), (Int.negSucc 1929492221422388336639), (Int.negSucc 517938354269026652159), (Int.negSucc 52877934234819606527), (Int.ofNat 2425839783807762432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 386301857562875695103), (Int.negSucc 794276295808114400255), (Int.negSucc 5216800419239611216895), (Int.negSucc 13321459835914624045055), (Int.negSucc 9158873264663792320511), (Int.ofNat 6946344046884657917952), (Int.ofNat 14214150680277195988992), (Int.ofNat 9252746819614957289472), (Int.ofNat 3088263575208823013376), (Int.ofNat 445510755353568697344), (Int.negSucc 12581711765064096767), (Int.negSucc 1008487875769786367)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1589893114754220023808), (Int.ofNat 3059543879196809253120), (Int.ofNat 23065760429893654903296), (Int.ofNat 55887482998033722337536), (Int.ofNat 40129533204888681750528), (Int.negSucc 16032840086298491389439), (Int.negSucc 44655731933047941583871), (Int.negSucc 33937167409053086320127), (Int.negSucc 13536137328412359186431), (Int.negSucc 2507430654235392977663), (Int.negSucc 75407207117267990015), (Int.ofNat 22634503356762070272), (Int.negSucc 594481695891240959)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4957980218308714982399), (Int.negSucc 9335956673153791942271), (Int.negSucc 77824757004378209852543), (Int.negSucc 179496934345895121883007), (Int.negSucc 140593863871242387702143), (Int.ofNat 9004962484733074686720), (Int.ofNat 105370511763795979481856), (Int.ofNat 97873358764189817606400), (Int.ofNat 45430929699855368659200), (Int.ofNat 10950841108835245733760), (Int.ofNat 965719045749259684224), (Int.negSucc 133829100788657258879), (Int.ofNat 1293886678743559296), (Int.ofNat 130747659843068928)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 12170867972242643062272), (Int.ofNat 23673037872070904107392), (Int.ofNat 207456470222309107835904), (Int.ofNat 461533372669928724080256), (Int.ofNat 407385360972088989486336), (Int.ofNat 86733469318352249205504), (Int.negSucc 184185166752422428658687), (Int.negSucc 222610484779907009796863), (Int.negSucc 121914713485291619570687), (Int.negSucc 37660660737019653640319), (Int.negSucc 5124481800977407979519), (Int.ofNat 226715110045015598208), (Int.ofNat 45580509000842068224), (Int.negSucc 3547784123841881087), (Int.ofNat 77697312310075392)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 24121240014916203906815), (Int.negSucc 51276220891116118936703), (Int.negSucc 447312334409120348661887), (Int.negSucc 981664511501421763958015), (Int.negSucc 990028821652704757571327), (Int.negSucc 418993790392333916990207), (Int.ofNat 202561101771143382293760), (Int.ofNat 396303863828836853744640), (Int.ofNat 267684189223385028955392), (Int.ofNat 101827285947536457773952), (Int.ofNat 19200415778413128676224), (Int.ofNat 802323604853211868416), (Int.negSucc 314730500401678996223), (Int.ofNat 17254076023865290752), (Int.negSucc 303466358990767103), (Int.negSucc 2485449489752063)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 39274947867977560079616), (Int.ofNat 95953729128860815634304), (Int.ofNat 793904321902032772294656), (Int.ofNat 1769296058313300831097344), (Int.ofNat 2029772311359589176964608), (Int.ofNat 1182699438000201969235200), (Int.ofNat 21041320400762935400448), (Int.negSucc 533552012895241611257855), (Int.negSucc 478935421753424814382847), (Int.negSucc 219952543510635647919743), (Int.negSucc 56202789300386330526719), (Int.negSucc 5936881928173030823423), (Int.ofNat 741760537006759418880), (Int.ofNat 18407884258537981440), (Int.negSucc 4362519062285835263), (Int.ofNat 208665215666282496), (Int.negSucc 4226464832815103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 53184435346837122516991), (Int.negSucc 155210445893937751562239), (Int.negSucc 1176455420628824567312383), (Int.negSucc 2746458995950964119863295), (Int.negSucc 3528678265714029139397887), (Int.negSucc 2522773524321727862815231), (Int.negSucc 729169839630683202940415), (Int.ofNat 463504306050406796950272), (Int.ofNat 678280679465406586447104), (Int.ofNat 387316615024609838462720), (Int.ofNat 129356467917046875183872), (Int.ofNat 20566141948056539724032), (Int.ofNat 28437635316840963072), (Int.negSucc 338635610653767311615), (Int.ofNat 28293271666785120000), (Int.negSucc 1179426579256330239), (Int.ofNat 32592343157344256), (Int.negSucc 440256753418239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 60409376467444038496256), (Int.ofNat 216057398805411570742784), (Int.ofNat 1474001873930358054970112), (Int.ofNat 3704374799761371728642816), (Int.ofNat 5238689203106679392689664), (Int.ofNat 4393938040541247740452352), (Int.ofNat 2065352583874490701189632), (Int.ofNat 23500408078222914326784), (Int.negSucc 708287258211675607641599), (Int.negSucc 556709133954912877676287), (Int.negSucc 233950456199652556712191), (Int.negSucc 52055129167710690200575), (Int.negSucc 4659909687016273234943), (Int.ofNat 915197796600382535424), (Int.negSucc 26762086312533245951), (Int.negSucc 775910755575538687), (Int.ofNat 39820986676658176), (Int.ofNat 253409103118336)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 57880925618878452618239), (Int.negSucc 257437808791823221197311), (Int.negSucc 1580155700863460173860095), (Int.negSucc 4353252086140203880293119), (Int.negSucc 6701237305906385365800959), (Int.negSucc 6453514691308920694302719), (Int.negSucc 3896335555443724728898559), (Int.negSucc 1053249092180152554914303), (Int.ofNat 409521560910825110439936), (Int.ofNat 627647787135575202763008), (Int.ofNat 335693226648961056830976), (Int.ofNat 102839596117598834456832), (Int.ofNat 15287936176682782004736), (Int.negSucc 494676960937796345087), (Int.negSucc 192103078875224381183), (Int.ofNat 17797718653238545920), (Int.negSucc 691474241200309247), (Int.ofNat 11396080199319552)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 46938009017098977152000), (Int.ofNat 261342092157011641041920), (Int.ofNat 1466047311723064404797696), (Int.ofNat 4452693832326839466517504), (Int.ofNat 7452688495722199456976896), (Int.ofNat 8108861134262400101213440), (Int.ofNat 5787478945487136092654080), (Int.ofNat 2507545658666057287812352), (Int.ofNat 266535353951661105610240), (Int.negSucc 484736491919059642825727), (Int.negSucc 382467341303253837842687), (Int.negSucc 157131366061098980274431), (Int.negSucc 32421256647363555608063), (Int.negSucc 2669833935030807267839), (Int.ofNat 610157698705015812096), (Int.negSucc 29087557085647052031), (Int.ofNat 621550025331227648), (Int.negSucc 11931027082264575)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 32257147559210225561599), (Int.negSucc 225175883286940165640959), (Int.negSucc 1189373445791540609090047), (Int.negSucc 3955221870760680233207295), (Int.negSucc 7254520413538645466649855), (Int.negSucc 8783332043045406848242815), (Int.negSucc 7172443109789591720141439), (Int.negSucc 3978258570935181643988607), (Int.negSucc 1199656956306029945010303), (Int.ofNat 94004113477452126902400), (Int.ofNat 326620222761757005261696), (Int.ofNat 182703164828098283098752), (Int.ofNat 53231219508973258800000), (Int.ofNat 8267153031281687952000), (Int.negSucc 430357208446535405951), (Int.negSucc 59278267923516591487), (Int.ofNat 4957949931195843712), (Int.negSucc 115549900583250943)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 18773404332324910894080), (Int.ofNat 164090534197569583545600), (Int.ofNat 850109151389450602256640), (Int.ofNat 3046728075980513511988992), (Int.ofNat 6196645107284857122447360), (Int.ofNat 8251806849240974800274304), (Int.ofNat 7605659160113548853263872), (Int.ofNat 4959229564758135121605504), (Int.ofNat 2122461074665362729723648), (Int.ofNat 437467272603343904853120), (Int.negSucc 150877930724594796026111), (Int.negSucc 157096352114895036255359), (Int.negSucc 67416739314140162492159), (Int.negSucc 13990962700929386914175), (Int.negSucc 1111217007480700740095), (Int.ofNat 231163991289855643776), (Int.negSucc 10220350175670914303), (Int.ofNat 180892163957102592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9227828653703896078847), (Int.negSucc 100741281741642687022847), (Int.negSucc 536715705982742071684607), (Int.negSucc 2036161727420607682958591), (Int.negSucc 4635699865410891749958911), (Int.negSucc 6764381834264203220659583), (Int.negSucc 6971299887847300059095935), (Int.negSucc 5144365711270191678228991), (Int.negSucc 2721215179973812679706367), (Int.negSucc 922741360868194864199039), (Int.negSucc 100729133927298221096063), (Int.ofNat 85498419242920960241664), (Int.ofNat 61693107145384598642688), (Int.ofNat 17826003325703780687232), (Int.ofNat 3161651324273384542080), (Int.negSucc 168025340673447924735), (Int.negSucc 9825893457420175359), (Int.ofNat 534646417623610880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3811787015402292358656), (Int.ofNat 51851652792580944475392), (Int.ofNat 298173356085218708363520), (Int.ofNat 1183487933811489396300288), (Int.ofNat 3021884202216084977838336), (Int.ofNat 4860346766435015504221056), (Int.ofNat 5544001977483954869722112), (Int.ofNat 4566964540759964203951616), (Int.ofNat 2803552287152658385455872), (Int.ofNat 1207869419167620885933696), (Int.ofNat 329566481665436885001984), (Int.ofNat 7984553895785382165504), (Int.negSucc 35169107898296793325823), (Int.negSucc 17677486069344510193535), (Int.negSucc 4090610372012182032383), (Int.negSucc 317472597392210676223), (Int.ofNat 46901791827260065792), (Int.negSucc 1240918614008279551)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1312971833942219347967), (Int.negSucc 22227570590851879736831), (Int.negSucc 144286472846289157784831), (Int.negSucc 600204412287575751417599), (Int.negSucc 1706404099824831140924927), (Int.negSucc 3063122269304770384546943), (Int.negSucc 3835372302868619208501887), (Int.negSucc 3513892258919495018517119), (Int.negSucc 2414774908970499553640831), (Int.negSucc 1232730381536543171942399), (Int.negSucc 450351863502604689648383), (Int.negSucc 92015782590353627817215), (Int.ofNat 2310659862796187199744), (Int.ofNat 11745919885503571846272), (Int.ofNat 3625288691251022072448), (Int.ofNat 785886114420773728128), (Int.negSucc 30781757197039165823), (Int.negSucc 774863806587560447)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 372834794896160473088), (Int.ofNat 7864848953413700582912), (Int.ofNat 59899592647258339181312), (Int.ofNat 265996197086481581296640), (Int.ofNat 830912126520097766865920), (Int.ofNat 1685452698067473419404160), (Int.ofNat 2315641969485349135044352), (Int.ofNat 2349692898990840976560256), (Int.ofNat 1779586852126044711159040), (Int.ofNat 1037857044055154951481856), (Int.ofNat 447613014099467554376704), (Int.ofNat 137703626800679561461504), (Int.ofNat 22430143978666235417088), (Int.negSucc 2350581514934051913599), (Int.negSucc 2427741434080793147135), (Int.negSucc 746026517312556428159), (Int.negSucc 55032745362313185023), (Int.ofNat 3947308294483201536)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 85843167521519952895), (Int.negSucc 2268655108222509217279), (Int.negSucc 20939847518977193699071), (Int.negSucc 102632897196548400253183), (Int.negSucc 348178788596004889879807), (Int.negSucc 802418455912502609818495), (Int.negSucc 1222515141499391124611199), (Int.negSucc 1363815449960109924717567), (Int.negSucc 1137303874820035423177983), (Int.negSucc 735769328530418975005695), (Int.negSucc 361775150861362218835455), (Int.negSucc 136294692896322163101183), (Int.negSucc 33961800442497298253567), (Int.negSucc 4940926232867013624959), (Int.ofNat 830473655594900228736), (Int.ofNat 371362934778339460608), (Int.ofNat 109756615183511401728), (Int.negSucc 1998505478763399167)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 15639096184480508928), (Int.ofNat 524300654949431768832), (Int.ofNat 6033146023313705246976), (Int.ofNat 34068878337021276236544), (Int.ofNat 125516189226390155668224), (Int.ofNat 327046463368135284580224), (Int.ofNat 562594585098563393683200), (Int.ofNat 686873685539604292052736), (Int.ofNat 632263849274779156113408), (Int.ofNat 445508360641194953802240), (Int.ofNat 246088145324639147718144), (Int.ofNat 104538333439085088787968), (Int.ofNat 33286423418828148967680), (Int.ofNat 7408729608883177368960), (Int.ofNat 662422341059164885248), (Int.negSucc 70113568716859014143), (Int.negSucc 71459474504295582719), (Int.negSucc 4238039699966481407)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2171645947064222719), (Int.negSucc 94682509097409335935), (Int.negSucc 1396932337816951046527), (Int.negSucc 9524082789726955537023), (Int.negSucc 38857326880416452700543), (Int.negSucc 113096619869596208585343), (Int.negSucc 223322871037396917218687), (Int.negSucc 300540029017193000360063), (Int.negSucc 304371623128843584495743), (Int.negSucc 233271404613354626926847), (Int.negSucc 141839230889992669631231), (Int.negSucc 66368602899881940052223), (Int.negSucc 24776295089164672930559), (Int.negSucc 6545241101673973163519), (Int.negSucc 1307709168826229754623), (Int.negSucc 81460025885472334847), (Int.ofNat 6728390466360238080), (Int.ofNat 6254386360510427136)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 216137369112204800), (Int.ofNat 12866815703694949760), (Int.ofNat 251826569737195536128), (Int.ofNat 2174942910438737784448), (Int.ofNat 10237682932679969521408), (Int.ofNat 33002365276486946426752), (Int.ofNat 75227063794034172309504), (Int.ofNat 114031452560916717661056), (Int.ofNat 126198300610258101604608), (Int.ofNat 106105913596023801299712), (Int.ofNat 69512759339276337099264), (Int.ofNat 35875160700395018390784), (Int.ofNat 14648960942593091154432), (Int.ofNat 4527399677238079865856), (Int.ofNat 1101573679255675766784), (Int.ofNat 147654158527765048320), (Int.ofNat 18424974785122473984), (Int.negSucc 2383075579219365887)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 13740777808991999), (Int.negSucc 1237432607134339199), (Int.negSucc 33834292609093386623), (Int.negSucc 389824568435935160831), (Int.negSucc 2244483582797191203839), (Int.negSucc 8098507378771530166655), (Int.negSucc 21131304530253668131199), (Int.negSucc 37093598159334006090239), (Int.negSucc 45002526113394300215807), (Int.negSucc 41634374389943529219839), (Int.negSucc 29239078889594958407423), (Int.negSucc 16494588126665904061439), (Int.negSucc 7163723567552311531007), (Int.negSucc 2534666135408584003583), (Int.negSucc 646922655086636851199), (Int.negSucc 132949911115372031999), (Int.negSucc 15170070449130928127), (Int.negSucc 1069408806861201407)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 419380584480000), (Int.ofNat 75101997812400000), (Int.ofNat 3167478474315160320), (Int.ofNat 51986889644176714752), (Int.ofNat 393312720984227152128), (Int.ofNat 1657369677722589373824), (Int.ofNat 4882865916617854566912), (Int.ofNat 10109692857746441244672), (Int.ofNat 13788787400348417395200), (Int.ofNat 13923922536203335227648), (Int.ofNat 10632932393153458383360), (Int.ofNat 6389646782477449863168), (Int.ofNat 2992387441883362412544), (Int.ofNat 1130015372312558389248), (Int.ofNat 313524001838002323456), (Int.ofNat 73436213142871216128), (Int.ofNat 9086711423790587904), (Int.ofNat 1309734016167591936)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2164355743679999), (Int.negSucc 183030015766291199), (Int.negSucc 4768143205164007679), (Int.negSucc 51798545609926065407), (Int.negSucc 275692611757174842239), (Int.negSucc 920886814754061962111), (Int.negSucc 2241370145159182141055), (Int.negSucc 3586078580700377787263), (Int.negSucc 3944035221594588827135), (Int.negSucc 3314904618206273656319), (Int.negSucc 2092656467889524441087), (Int.negSucc 1064329870245776160767), (Int.negSucc 407883350691526699007), (Int.negSucc 127801365421115049983), (Int.negSucc 27842420429112895487), (Int.negSucc 4687621435747694591), (Int.negSucc 486016835859652607)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4870409529024000), (Int.ofNat 262234781678880000), (Int.ofNat 4669426732917606912), (Int.ofNat 35200357215612854400), (Int.ofNat 140480829819320198400), (Int.ofNat 393525786885044508288), (Int.ofNat 765986699816197440768), (Int.ofNat 946294893521617688064), (Int.ofNat 866509163067740626944), (Int.ofNat 586969312325358514176), (Int.ofNat 312981662423869820928), (Int.ofNat 125027782397208594432), (Int.ofNat 40547895511123832832), (Int.ofNat 8609640942878189568), (Int.ofNat 1605816749290917888), (Int.ofNat 87681802037354496)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6265730225663999), (Int.negSucc 244891847295210239), (Int.negSucc 3106710816233228927), (Int.negSucc 16771796045983585151), (Int.negSucc 53873026698788633087), (Int.negSucc 127781144668791647999), (Int.negSucc 189882450457267027967), (Int.negSucc 187032770838839126015), (Int.negSucc 139826502431012818943), (Int.negSucc 75431394499068813311), (Int.negSucc 32577336725284952063), (Int.negSucc 9770617882428549119), (Int.negSucc 2303425828774748159), (Int.negSucc 312512730116861951), (Int.negSucc 7825602154954751)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5074496715859200), (Int.ofNat 155894982885475200), (Int.ofNat 1423652721914873088), (Int.ofNat 5706492624175021056), (Int.ofNat 15802116643815552000), (Int.ofNat 30253982333535876096), (Int.ofNat 33478322315644219392), (Int.ofNat 27096374686032912384), (Int.ofNat 15329411306311127040), (Int.ofNat 6703518572890785792), (Int.ofNat 1941311962226257920), (Int.ofNat 444402325159575552), (Int.ofNat 31147805798645760), (Int.ofNat 277063758102528)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2681705894515199), (Int.negSucc 68536291208599295), (Int.negSucc 445753646853829631), (Int.negSucc 1409913205733191679), (Int.negSucc 3476291044602451967), (Int.negSucc 4916587910248617983), (Int.negSucc 4126023021489444863), (Int.negSucc 2611123848834287615), (Int.negSucc 1043743426941026303), (Int.negSucc 325775788622106623), (Int.negSucc 48555550586437631), (Int.negSucc 1235509727772671)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 924673554524160), (Int.ofNat 20541737910574080), (Int.ofNat 92484397951617024), (Int.ofNat 256608886202726400), (Int.ofNat 535189520765767680), (Int.ofNat 507095369470015488), (Int.ofNat 335567800322224128), (Int.ofNat 132921915119493120), (Int.ofNat 37058987871535104), (Int.ofNat 2171401330065408)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 200666679644159), (Int.negSucc 4013834373752831), (Int.negSucc 11928015929198591), (Int.negSucc 34008469010159615), (Int.negSucc 50348142610882559), (Int.negSucc 29676558525419519), (Int.negSucc 13937685758115839), (Int.negSucc 1871783204585471)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 24887152447488), (Int.ofNat 461185078007808), (Int.ofNat 839067598393344), (Int.ofNat 2982666822598656), (Int.ofNat 2135194183876608), (Int.ofNat 786082539552768)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1345251483647), (Int.negSucc 23631874633727), (Int.negSucc 23149354549247), (Int.negSucc 127254695362559)]]

theorem h1n87_arithmetic_row0 :
    (BiPoly.mul h1p3 h1p86).getD 0 []=h1p87.getD 0 [] := by
  decide +kernel

theorem h1n87_arithmetic_row1 :
    (BiPoly.mul h1p3 h1p86).getD 1 []=h1p87.getD 1 [] := by
  decide +kernel

theorem h1n87_arithmetic_row2 :
    (BiPoly.mul h1p3 h1p86).getD 2 []=h1p87.getD 2 [] := by
  decide +kernel

theorem h1n87_arithmetic_row3 :
    (BiPoly.mul h1p3 h1p86).getD 3 []=h1p87.getD 3 [] := by
  decide +kernel

theorem h1n87_arithmetic_row4 :
    (BiPoly.mul h1p3 h1p86).getD 4 []=h1p87.getD 4 [] := by
  decide +kernel

theorem h1n87_arithmetic_row5 :
    (BiPoly.mul h1p3 h1p86).getD 5 []=h1p87.getD 5 [] := by
  decide +kernel

theorem h1n87_arithmetic_row6 :
    (BiPoly.mul h1p3 h1p86).getD 6 []=h1p87.getD 6 [] := by
  decide +kernel

theorem h1n87_arithmetic_row7 :
    (BiPoly.mul h1p3 h1p86).getD 7 []=h1p87.getD 7 [] := by
  decide +kernel

theorem h1n87_arithmetic_row8 :
    (BiPoly.mul h1p3 h1p86).getD 8 []=h1p87.getD 8 [] := by
  decide +kernel

theorem h1n87_arithmetic_row9 :
    (BiPoly.mul h1p3 h1p86).getD 9 []=h1p87.getD 9 [] := by
  decide +kernel

theorem h1n87_arithmetic_row10 :
    (BiPoly.mul h1p3 h1p86).getD 10 []=h1p87.getD 10 [] := by
  decide +kernel

theorem h1n87_arithmetic_row11 :
    (BiPoly.mul h1p3 h1p86).getD 11 []=h1p87.getD 11 [] := by
  decide +kernel

theorem h1n87_arithmetic_row12 :
    (BiPoly.mul h1p3 h1p86).getD 12 []=h1p87.getD 12 [] := by
  decide +kernel

theorem h1n87_arithmetic_row13 :
    (BiPoly.mul h1p3 h1p86).getD 13 []=h1p87.getD 13 [] := by
  decide +kernel

theorem h1n87_arithmetic_row14 :
    (BiPoly.mul h1p3 h1p86).getD 14 []=h1p87.getD 14 [] := by
  decide +kernel

theorem h1n87_arithmetic_row15 :
    (BiPoly.mul h1p3 h1p86).getD 15 []=h1p87.getD 15 [] := by
  decide +kernel

theorem h1n87_arithmetic_row16 :
    (BiPoly.mul h1p3 h1p86).getD 16 []=h1p87.getD 16 [] := by
  decide +kernel

theorem h1n87_arithmetic_row17 :
    (BiPoly.mul h1p3 h1p86).getD 17 []=h1p87.getD 17 [] := by
  decide +kernel

theorem h1n87_arithmetic_row18 :
    (BiPoly.mul h1p3 h1p86).getD 18 []=h1p87.getD 18 [] := by
  decide +kernel

theorem h1n87_arithmetic_row19 :
    (BiPoly.mul h1p3 h1p86).getD 19 []=h1p87.getD 19 [] := by
  decide +kernel

theorem h1n87_arithmetic_row20 :
    (BiPoly.mul h1p3 h1p86).getD 20 []=h1p87.getD 20 [] := by
  decide +kernel

theorem h1n87_arithmetic_row21 :
    (BiPoly.mul h1p3 h1p86).getD 21 []=h1p87.getD 21 [] := by
  decide +kernel

theorem h1n87_arithmetic_row22 :
    (BiPoly.mul h1p3 h1p86).getD 22 []=h1p87.getD 22 [] := by
  decide +kernel

theorem h1n87_arithmetic_row23 :
    (BiPoly.mul h1p3 h1p86).getD 23 []=h1p87.getD 23 [] := by
  decide +kernel

theorem h1n87_arithmetic_row24 :
    (BiPoly.mul h1p3 h1p86).getD 24 []=h1p87.getD 24 [] := by
  decide +kernel

theorem h1n87_arithmetic_row25 :
    (BiPoly.mul h1p3 h1p86).getD 25 []=h1p87.getD 25 [] := by
  decide +kernel

theorem h1n87_arithmetic_row26 :
    (BiPoly.mul h1p3 h1p86).getD 26 []=h1p87.getD 26 [] := by
  decide +kernel

theorem h1n87_arithmetic_row27 :
    (BiPoly.mul h1p3 h1p86).getD 27 []=h1p87.getD 27 [] := by
  decide +kernel

theorem h1n87_arithmetic_row28 :
    (BiPoly.mul h1p3 h1p86).getD 28 []=h1p87.getD 28 [] := by
  decide +kernel

theorem h1n87_arithmetic_row29 :
    (BiPoly.mul h1p3 h1p86).getD 29 []=h1p87.getD 29 [] := by
  decide +kernel

theorem h1n87_arithmetic_row30 :
    (BiPoly.mul h1p3 h1p86).getD 30 []=h1p87.getD 30 [] := by
  decide +kernel

theorem h1n87_arithmetic_row31 :
    (BiPoly.mul h1p3 h1p86).getD 31 []=h1p87.getD 31 [] := by
  decide +kernel

theorem h1n87_arithmetic_row32 :
    (BiPoly.mul h1p3 h1p86).getD 32 []=h1p87.getD 32 [] := by
  decide +kernel

theorem h1n87_arithmetic_row33 :
    (BiPoly.mul h1p3 h1p86).getD 33 []=h1p87.getD 33 [] := by
  decide +kernel

theorem h1n87_arithmetic : BiPoly.mul h1p3 h1p86=h1p87 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<34 at hk
    have hf : ∀ j : Fin 34, (BiPoly.mul h1p3 h1p86).getD j.val []=h1p87.getD j.val [] :=
      (fun j => Fin.cases h1n87_arithmetic_row0 (fun j => Fin.cases h1n87_arithmetic_row1 (fun j => Fin.cases h1n87_arithmetic_row2 (fun j => Fin.cases h1n87_arithmetic_row3 (fun j => Fin.cases h1n87_arithmetic_row4 (fun j => Fin.cases h1n87_arithmetic_row5 (fun j => Fin.cases h1n87_arithmetic_row6 (fun j => Fin.cases h1n87_arithmetic_row7 (fun j => Fin.cases h1n87_arithmetic_row8 (fun j => Fin.cases h1n87_arithmetic_row9 (fun j => Fin.cases h1n87_arithmetic_row10 (fun j => Fin.cases h1n87_arithmetic_row11 (fun j => Fin.cases h1n87_arithmetic_row12 (fun j => Fin.cases h1n87_arithmetic_row13 (fun j => Fin.cases h1n87_arithmetic_row14 (fun j => Fin.cases h1n87_arithmetic_row15 (fun j => Fin.cases h1n87_arithmetic_row16 (fun j => Fin.cases h1n87_arithmetic_row17 (fun j => Fin.cases h1n87_arithmetic_row18 (fun j => Fin.cases h1n87_arithmetic_row19 (fun j => Fin.cases h1n87_arithmetic_row20 (fun j => Fin.cases h1n87_arithmetic_row21 (fun j => Fin.cases h1n87_arithmetic_row22 (fun j => Fin.cases h1n87_arithmetic_row23 (fun j => Fin.cases h1n87_arithmetic_row24 (fun j => Fin.cases h1n87_arithmetic_row25 (fun j => Fin.cases h1n87_arithmetic_row26 (fun j => Fin.cases h1n87_arithmetic_row27 (fun j => Fin.cases h1n87_arithmetic_row28 (fun j => Fin.cases h1n87_arithmetic_row29 (fun j => Fin.cases h1n87_arithmetic_row30 (fun j => Fin.cases h1n87_arithmetic_row31 (fun j => Fin.cases h1n87_arithmetic_row32 (fun j => Fin.cases h1n87_arithmetic_row33 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n87 : h1e87.toBi mapPolyEnv=h1p87 := by
  change BiPoly.mul (h1e3.toBi mapPolyEnv) (h1e86.toBi mapPolyEnv)=h1p87
  rw [h1n3, h1n86]
  exact h1n87_arithmetic

#print axioms h1n87_arithmetic
end StackSorting.RationalLift
