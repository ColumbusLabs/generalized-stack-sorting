import BivariateRowEquality
import Horner4Base
import Horner4Node133
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p250 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 585042121021049856000), (Int.ofNat 4167940880339662671360), (Int.ofNat 687539983329994947840), (Int.negSucc 36389200918067139133439), (Int.negSucc 7664012381935718392319), (Int.ofNat 110054930290341952596480), (Int.negSucc 69967019870215736083199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7297919847414257437439), (Int.negSucc 49653062936767803984767), (Int.ofNat 1839965299523631211392), (Int.ofNat 435151865391900523017984), (Int.ofNat 32725613284643871908352), (Int.negSucc 1246087856282046180727679), (Int.ofNat 891333354555475945117056), (Int.negSucc 73326535320651182899199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 43232673345859653200640), (Int.ofNat 275713869086559301690368), (Int.negSucc 81234483482943592178111), (Int.negSucc 2403047640553414326998207), (Int.ofNat 132857221400870630610816), (Int.ofNat 6251946117642620037136512), (Int.negSucc 4643651004967839577362623), (Int.ofNat 537194736884755829943360), (Int.negSucc 29191075350196620506111)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 161639290104938617394879), (Int.negSucc 943616952340962354599903), (Int.ofNat 574396096880975520479616), (Int.ofNat 8063020198363776192213408), (Int.negSucc 1323582993754224008390207), (Int.negSucc 18071370718866939594070943), (Int.ofNat 12407260425279630676733952), (Int.negSucc 883675624857841875818015), (Int.ofNat 61088441625367747005312), (Int.negSucc 5374632902378671374335)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 427098575187315076233600), (Int.ofNat 2217976479171430575042240), (Int.negSucc 2176017034693122621890495), (Int.negSucc 18278865945747489414810239), (Int.ofNat 4027024289160637988203584), (Int.ofNat 32693629076759191487704128), (Int.negSucc 15240884921588776622362559), (Int.negSucc 3624611639914867620023423), (Int.ofNat 551395906298267406710976), (Int.negSucc 21416639537626568842751), (Int.negSucc 431672641840692744191)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 845480708683582576443839), (Int.negSucc 3776697314119891577281823), (Int.ofNat 5355960514382896040693376), (Int.ofNat 29625792668909048869805952), (Int.negSucc 5001215990603818133389823), (Int.negSucc 37357637664511192317946271), (Int.negSucc 5296008163551267119803775), (Int.ofNat 19069081655142318392023488), (Int.negSucc 2275220416172147467084223), (Int.ofNat 146823415970671613769984), (Int.negSucc 5440235221471359163391), (Int.negSucc 9794373690320879615)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1296215298375532761788640), (Int.ofNat 4787861198131710399357072), (Int.negSucc 9277166439678947617583567), (Int.negSucc 35814016864079123765983343), (Int.negSucc 2992451506223622882514703), (Int.ofNat 25028022040501281684960816), (Int.ofNat 48775835021163803095496400), (Int.negSucc 34739561054663273143564559), (Int.ofNat 802817338984142426933616), (Int.ofNat 108514877635091512878336), (Int.negSucc 1051699176390781168127), (Int.negSucc 326950858160874261503), (Int.ofNat 60226301510369280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1568719520225478581773439), (Int.negSucc 4570357494296202808383071), (Int.ofNat 11802883341125833063381488), (Int.ofNat 34089714396205437379191264), (Int.ofNat 22394296688612842486471248), (Int.negSucc 6003589571352074491202591), (Int.negSucc 76565790162133087978661231), (Int.ofNat 19631413617466348939039488), (Int.ofNat 11230008687917183836233840), (Int.negSucc 1434518438500317838448351), (Int.ofNat 75949170277392690642432), (Int.negSucc 1827427189920162316799), (Int.negSucc 793475845577385983)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1514016311165231978691360), (Int.ofNat 3279876551968401321621456), (Int.negSucc 11337548524904523458839823), (Int.negSucc 28067370283595906728767791), (Int.negSucc 43085510919212720237042591), (Int.negSucc 6984874955946452723245343), (Int.ofNat 54810778217016566528411568), (Int.ofNat 32012911224932051980280016), (Int.negSucc 26165494279382637807567839), (Int.ofNat 1553057028147241602683376), (Int.negSucc 23921094514398289250879), (Int.ofNat 786629375326407926784), (Int.negSucc 48667527279832003583)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1169787605591653254849599), (Int.negSucc 1743715661686326716084543), (Int.ofNat 8427014712537750291870096), (Int.ofNat 22560652428183520684681824), (Int.ofNat 50838278575736780412480960), (Int.ofNat 16047839877852565591517376), (Int.negSucc 5891713526591777053659119), (Int.negSucc 70297497571594867931828255), (Int.ofNat 18854010675362928364885536), (Int.ofNat 3631703337336137797096608), (Int.negSucc 439859617649188280236223), (Int.ofNat 17448895236838887553920), (Int.negSucc 279241148823559781375)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 722671140315565154262720), (Int.ofNat 667287780277897687792512), (Int.negSucc 5021423764692350104723727), (Int.negSucc 18403369510182312915962111), (Int.negSucc 42775482034586098989399743), (Int.negSucc 27068769628014588306636383), (Int.negSucc 22896283472850239069014895), (Int.ofNat 51787503649202927429940528), (Int.ofNat 13747042716642314046454704), (Int.negSucc 10040405295198783899073551), (Int.ofNat 523549698986983357232400), (Int.negSucc 3407543603021256418175), (Int.negSucc 137514733274923949567)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 354845201482255875608639), (Int.negSucc 179639853730641527579999), (Int.ofNat 2555292178737899186879136), (Int.ofNat 13989005615014515398517840), (Int.ofNat 28146166685592356310061296), (Int.ofNat 34578376196413784102004240), (Int.ofNat 22466120694976689861539904), (Int.negSucc 3665260215959595476305679), (Int.negSucc 35688211325258066738982431), (Int.ofNat 6754267824721370250791664), (Int.ofNat 821701413972678887279088), (Int.negSucc 74547815558955843676223), (Int.ofNat 1754650705134054585216)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 136948487508189001880640), (Int.ofNat 40953275508284795596320), (Int.negSucc 1211691917395406575169471), (Int.negSucc 9014584606375398242670623), (Int.negSucc 16126700022441545210407103), (Int.negSucc 30993230931820412084685551), (Int.negSucc 15703808545494679121754863), (Int.negSucc 21843416156381278761070943), (Int.ofNat 23608838646137589386292768), (Int.ofNat 4831964352404850100982736), (Int.negSucc 2063472982318575153865823), (Int.ofNat 51505655424722732594064), (Int.ofNat 1442188710572139407808)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 40812944156077305289919), (Int.negSucc 16727427553654858199519), (Int.ofNat 560041704384731603339712), (Int.ofNat 4716701517975474678902016), (Int.ofNat 8926852692129238536908160), (Int.ofNat 19555210788348001282447056), (Int.ofNat 13941607586689106874274272), (Int.ofNat 17481994808808484476263232), (Int.ofNat 641062856521269026421408), (Int.negSucc 10249444874040447819793295), (Int.ofNat 920442261705845722309584), (Int.ofNat 134752402594815661197696), (Int.negSucc 5453957799777659439743)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9140372873070739980000), (Int.ofNat 9779682281490694711632), (Int.negSucc 238829978696844148769615), (Int.negSucc 1989794712844746024706319), (Int.negSucc 4817428898436352039529615), (Int.negSucc 9028485633824406044282399), (Int.negSucc 11978704179452107084415711), (Int.negSucc 7385610091287831642747167), (Int.negSucc 10156808533541772381006623), (Int.ofNat 5046221653463902812184752), (Int.ofNat 1194944931450946907221536), (Int.negSucc 187759014578282680419455), (Int.negSucc 2178168945535907435519)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1474516554075962340479), (Int.negSucc 4196433745017033708767), (Int.ofNat 85114104268379742890448), (Int.ofNat 681839792933620467986112), (Int.ofNat 2320599052318583105869872), (Int.ofNat 3371716549091428294001808), (Int.ofNat 7210130612787765449408304), (Int.ofNat 3475875297269955746502000), (Int.ofNat 6404182284038122587139056), (Int.ofNat 1198100389529827286423712), (Int.negSucc 1495153447568824241981663), (Int.negSucc 5683982947561074688415), (Int.ofNat 9563115113289144220032)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 159711654812244491040), (Int.ofNat 1176785160852602388816), (Int.negSucc 23413415049966339120623), (Int.negSucc 191094995663575023135503), (Int.negSucc 912077491202707892030783), (Int.negSucc 1234034299625776792690991), (Int.negSucc 2826298337440279905029087), (Int.negSucc 2464489544889614730044399), (Int.negSucc 1886335248813057870493535), (Int.negSucc 2411015278421375287735103), (Int.ofNat 367643841417223294850496), (Int.ofNat 140673467041598433038400), (Int.negSucc 2006765290962826785791)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10183378575671538239), (Int.negSucc 210451003538268618815), (Int.ofNat 4681147236426268130352), (Int.ofNat 43506159194649204663072), (Int.ofNat 276613249812633006347808), (Int.ofNat 485825405893295674110768), (Int.ofNat 728419624666012293889392), (Int.ofNat 1345890987194796688281984), (Int.ofNat 449990575350864960280608), (Int.ofNat 1086244786384623081544608), (Int.ofNat 319518578557808063498304), (Int.negSucc 77051398947776776206143), (Int.negSucc 6366087502267092039935)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 277477454442291840), (Int.ofNat 22144484453015986848), (Int.negSucc 636297968585865734927), (Int.negSucc 7795126760132454527807), (Int.negSucc 62284733643463754278751), (Int.negSucc 173532832031243151722159), (Int.negSucc 147393770969053625661791), (Int.negSucc 433666278124520008163327), (Int.negSucc 237832143787671562849535), (Int.negSucc 208529530599741709920191), (Int.negSucc 261690240395776702436927), (Int.negSucc 12013504573269252589055), (Int.ofNat 4044829480790460346368)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1055538417108417407), (Int.ofNat 52548533302581673632), (Int.ofNat 1029035698231928033520), (Int.ofNat 9990745544695065130512), (Int.ofNat 46530699046736165742240), (Int.ofNat 39167636336962667337312), (Int.ofNat 74282809195310431838112), (Int.ofNat 114048424515779787506688), (Int.ofNat 17751875322329671400064), (Int.ofNat 75256845057055768758912), (Int.ofNat 25769126198975961760128), (Int.ofNat 524324600083630425600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1996808357601486719), (Int.negSucc 88492404103198888607), (Int.negSucc 1073015374336900891487), (Int.negSucc 8419592101100433659711), (Int.negSucc 12722880311771663434175), (Int.negSucc 5147244555801336763199), (Int.negSucc 28340220018114869694335), (Int.negSucc 6600290137209793933055), (Int.negSucc 7717519194835836195071), (Int.negSucc 9731517738378601549823), (Int.negSucc 1223143567973227551743)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3701254093908571008), (Int.ofNat 68769768183086403936), (Int.ofNat 934031100775590104544), (Int.ofNat 2932270376534902177344), (Int.ofNat 285113624899898107584), (Int.ofNat 2872100023890024688128), (Int.ofNat 3177823976733801632256), (Int.negSucc 422827664746809940991), (Int.ofNat 1490833624255197684480), (Int.ofNat 409911144626100188160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1965500638734129407), (Int.negSucc 52845383010210348095), (Int.negSucc 381628427630615809343), (Int.negSucc 217729108958779072511), (Int.ofNat 112030599276457196544), (Int.negSucc 599651466272300632319), (Int.ofNat 129937634608100956416), (Int.negSucc 73558992698112430079), (Int.negSucc 44961029557578547199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 820473985590428160), (Int.ofNat 22454195536417421952), (Int.ofNat 49244021500921582464), (Int.negSucc 45637174605086125055), (Int.ofNat 42908785183902866688), (Int.negSucc 7779595711391032319)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 207971977912906751), (Int.negSucc 3345656882818040063), (Int.ofNat 2178562521754172160)]]

theorem h4n250_arithmetic_row0 :
    (BiPoly.mul h4p53 h4p133).getD 0 []=h4p250.getD 0 [] := by
  decide +kernel

theorem h4n250_arithmetic_row1 :
    (BiPoly.mul h4p53 h4p133).getD 1 []=h4p250.getD 1 [] := by
  decide +kernel

theorem h4n250_arithmetic_row2 :
    (BiPoly.mul h4p53 h4p133).getD 2 []=h4p250.getD 2 [] := by
  decide +kernel

theorem h4n250_arithmetic_row3 :
    (BiPoly.mul h4p53 h4p133).getD 3 []=h4p250.getD 3 [] := by
  decide +kernel

theorem h4n250_arithmetic_row4 :
    (BiPoly.mul h4p53 h4p133).getD 4 []=h4p250.getD 4 [] := by
  decide +kernel

theorem h4n250_arithmetic_row5 :
    (BiPoly.mul h4p53 h4p133).getD 5 []=h4p250.getD 5 [] := by
  decide +kernel

theorem h4n250_arithmetic_row6 :
    (BiPoly.mul h4p53 h4p133).getD 6 []=h4p250.getD 6 [] := by
  decide +kernel

theorem h4n250_arithmetic_row7 :
    (BiPoly.mul h4p53 h4p133).getD 7 []=h4p250.getD 7 [] := by
  decide +kernel

theorem h4n250_arithmetic_row8 :
    (BiPoly.mul h4p53 h4p133).getD 8 []=h4p250.getD 8 [] := by
  decide +kernel

theorem h4n250_arithmetic_row9 :
    (BiPoly.mul h4p53 h4p133).getD 9 []=h4p250.getD 9 [] := by
  decide +kernel

theorem h4n250_arithmetic_row10 :
    (BiPoly.mul h4p53 h4p133).getD 10 []=h4p250.getD 10 [] := by
  decide +kernel

theorem h4n250_arithmetic_row11 :
    (BiPoly.mul h4p53 h4p133).getD 11 []=h4p250.getD 11 [] := by
  decide +kernel

theorem h4n250_arithmetic_row12 :
    (BiPoly.mul h4p53 h4p133).getD 12 []=h4p250.getD 12 [] := by
  decide +kernel

theorem h4n250_arithmetic_row13 :
    (BiPoly.mul h4p53 h4p133).getD 13 []=h4p250.getD 13 [] := by
  decide +kernel

theorem h4n250_arithmetic_row14 :
    (BiPoly.mul h4p53 h4p133).getD 14 []=h4p250.getD 14 [] := by
  decide +kernel

theorem h4n250_arithmetic_row15 :
    (BiPoly.mul h4p53 h4p133).getD 15 []=h4p250.getD 15 [] := by
  decide +kernel

theorem h4n250_arithmetic_row16 :
    (BiPoly.mul h4p53 h4p133).getD 16 []=h4p250.getD 16 [] := by
  decide +kernel

theorem h4n250_arithmetic_row17 :
    (BiPoly.mul h4p53 h4p133).getD 17 []=h4p250.getD 17 [] := by
  decide +kernel

theorem h4n250_arithmetic_row18 :
    (BiPoly.mul h4p53 h4p133).getD 18 []=h4p250.getD 18 [] := by
  decide +kernel

theorem h4n250_arithmetic_row19 :
    (BiPoly.mul h4p53 h4p133).getD 19 []=h4p250.getD 19 [] := by
  decide +kernel

theorem h4n250_arithmetic_row20 :
    (BiPoly.mul h4p53 h4p133).getD 20 []=h4p250.getD 20 [] := by
  decide +kernel

theorem h4n250_arithmetic_row21 :
    (BiPoly.mul h4p53 h4p133).getD 21 []=h4p250.getD 21 [] := by
  decide +kernel

theorem h4n250_arithmetic_row22 :
    (BiPoly.mul h4p53 h4p133).getD 22 []=h4p250.getD 22 [] := by
  decide +kernel

theorem h4n250_arithmetic_row23 :
    (BiPoly.mul h4p53 h4p133).getD 23 []=h4p250.getD 23 [] := by
  decide +kernel

theorem h4n250_arithmetic_row24 :
    (BiPoly.mul h4p53 h4p133).getD 24 []=h4p250.getD 24 [] := by
  decide +kernel

theorem h4n250_arithmetic : BiPoly.mul h4p53 h4p133=h4p250 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h4p53 h4p133).getD j.val []=h4p250.getD j.val [] :=
      (fun j => Fin.cases h4n250_arithmetic_row0 (fun j => Fin.cases h4n250_arithmetic_row1 (fun j => Fin.cases h4n250_arithmetic_row2 (fun j => Fin.cases h4n250_arithmetic_row3 (fun j => Fin.cases h4n250_arithmetic_row4 (fun j => Fin.cases h4n250_arithmetic_row5 (fun j => Fin.cases h4n250_arithmetic_row6 (fun j => Fin.cases h4n250_arithmetic_row7 (fun j => Fin.cases h4n250_arithmetic_row8 (fun j => Fin.cases h4n250_arithmetic_row9 (fun j => Fin.cases h4n250_arithmetic_row10 (fun j => Fin.cases h4n250_arithmetic_row11 (fun j => Fin.cases h4n250_arithmetic_row12 (fun j => Fin.cases h4n250_arithmetic_row13 (fun j => Fin.cases h4n250_arithmetic_row14 (fun j => Fin.cases h4n250_arithmetic_row15 (fun j => Fin.cases h4n250_arithmetic_row16 (fun j => Fin.cases h4n250_arithmetic_row17 (fun j => Fin.cases h4n250_arithmetic_row18 (fun j => Fin.cases h4n250_arithmetic_row19 (fun j => Fin.cases h4n250_arithmetic_row20 (fun j => Fin.cases h4n250_arithmetic_row21 (fun j => Fin.cases h4n250_arithmetic_row22 (fun j => Fin.cases h4n250_arithmetic_row23 (fun j => Fin.cases h4n250_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n250 : h4e250.toBi mapPolyEnv=h4p250 := by
  change BiPoly.mul (h4e53.toBi mapPolyEnv) (h4e133.toBi mapPolyEnv)=h4p250
  rw [h4n53, h4n133]
  exact h4n250_arithmetic

#print axioms h4n250_arithmetic
end StackSorting.RationalLift
