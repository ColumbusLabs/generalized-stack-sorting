import BivariateRowEquality
import Horner0Base
import Horner0Node089
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p90 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 493629289611510816000), (Int.ofNat 4226292221603137176960), (Int.ofNat 8691627749136675045120), (Int.negSucc 8303564637697777355519), (Int.negSucc 28489778167776219129599), (Int.ofNat 3113620573433838698880), (Int.ofNat 18340869286367231788800)], [(Int.ofNat 0), (Int.negSucc 6213038900297812755839), (Int.negSucc 52646548781127125389247), (Int.negSucc 106462138036205422135871), (Int.ofNat 99253787378167140042240), (Int.ofNat 316289344326208092087552), (Int.negSucc 63714531597149727435455), (Int.negSucc 177442074490808075874623), (Int.ofNat 9549859561415737833600)], [(Int.ofNat 0), (Int.ofNat 37149122444848996743360), (Int.ofNat 308433291707957491125792), (Int.ofNat 611119542133223006051232), (Int.negSucc 535231216924759722559103), (Int.negSucc 1632546317201974023368447), (Int.ofNat 390301228225700435041056), (Int.ofNat 738190693635028936645536), (Int.negSucc 11353336644072591605951), (Int.negSucc 2082192172440886939391)], [(Int.ofNat 0), (Int.negSucc 140239780477780793945759), (Int.negSucc 1128286575875305956027599), (Int.negSucc 2194279233239554359533279), (Int.ofNat 1647740635528080251397744), (Int.ofNat 5159066140546884317976768), (Int.negSucc 1035607085279238658122863), (Int.negSucc 1726487220660272303062751), (Int.negSucc 332161354066152880861487), (Int.ofNat 52879614875851754452896), (Int.negSucc 2209966303282553806847)], [(Int.ofNat 0), (Int.ofNat 374309274090075032537280), (Int.ofNat 2888195311205587577892960), (Int.ofNat 5563094905484535951065664), (Int.negSucc 2937425264735130689477471), (Int.negSucc 11101730631679954235625407), (Int.ofNat 576943336133202112982496), (Int.ofNat 2494090570885527259363968), (Int.ofNat 1830909342324299040402336), (Int.negSucc 233680352391638997423551), (Int.ofNat 14730987093697191232512), (Int.negSucc 470849154479921885183)], [(Int.ofNat 0), (Int.negSucc 748903656918928361546879), (Int.negSucc 5501348623872671604364223), (Int.negSucc 10680625841386468689499823), (Int.ofNat 2072547652942504974806928), (Int.ofNat 17011438082562068002844784), (Int.ofNat 4355524322681465436946560), (Int.negSucc 2218091835172966100297423), (Int.negSucc 4394862574064705577526127), (Int.ofNat 175465108013528257004880), (Int.ofNat 6814668051699858407520), (Int.ofNat 227536558851805316352), (Int.negSucc 30826652383490033663)], [(Int.ofNat 0), (Int.ofNat 1161247670217640987868880), (Int.ofNat 8105974929088339926999384), (Int.ofNat 16279266770595348909714216), (Int.ofNat 3813430349197264421419848), (Int.negSucc 18276195524321523787646903), (Int.negSucc 15127359861041268196814567), (Int.ofNat 310482269156573819840088), (Int.ofNat 5373766717886876988571992), (Int.ofNat 1249984154860338027142152), (Int.negSucc 190801445420173654081583), (Int.ofNat 10123363539043688267712), (Int.negSucc 186679653291219889151), (Int.ofNat 165622329153515520)], [(Int.ofNat 0), (Int.negSucc 1422638547250550377423679), (Int.negSucc 9496365223333982562496943), (Int.negSucc 20366017350790992998281559), (Int.negSucc 14366519816419230817195583), (Int.ofNat 11332567889629437423014280), (Int.ofNat 25853054824160081557353936), (Int.ofNat 4420719708731668698688152), (Int.negSucc 2161256782739759813682575), (Int.negSucc 3978543318177291546547943), (Int.ofNat 326759767695412217975664), (Int.negSucc 11490369425726164914239), (Int.ofNat 384610700259699396480), (Int.negSucc 5374052555387383295)], [(Int.ofNat 0), (Int.ofNat 1391322253199494022653200), (Int.ofNat 9033273950253498857171208), (Int.ofNat 21376911204765962924464632), (Int.ofNat 24570115404613475924166504), (Int.ofNat 2749621458780213464681136), (Int.negSucc 26500662128275016859196847), (Int.negSucc 12260497872726306695485271), (Int.negSucc 3336663959993734801928951), (Int.ofNat 4771353222679431996272208), (Int.ofNat 367280656790851641812664), (Int.negSucc 64065867384154399200815), (Int.ofNat 2611352355050448828480), (Int.negSucc 34370758289177036543)], [(Int.ofNat 0), (Int.negSucc 1090594797206657495584799), (Int.negSucc 7091415158958978245581727), (Int.negSucc 19043590512541269901554407), (Int.negSucc 28802358911054823158822735), (Int.negSucc 17605184650321597866030815), (Int.ofNat 13747140645289796039291136), (Int.ofNat 18605983723304786730446712), (Int.ofNat 6984085153279548382370880), (Int.negSucc 1115134888280971096470143), (Int.negSucc 1783038908259534560198495), (Int.ofNat 131935325658883215651600), (Int.negSucc 3045878544752954452703), (Int.ofNat 19772228943349290240)], [(Int.ofNat 0), (Int.ofNat 684421969586867495596320), (Int.ofNat 4645577254618895108017056), (Int.ofNat 14436017636768380849421448), (Int.ofNat 25810505713094221313213616), (Int.ofNat 25747582009379587431829920), (Int.ofNat 4411178978562669808942704), (Int.negSucc 16543059644112585793913639), (Int.negSucc 7840182619784891982400967), (Int.negSucc 3752984316888969511076567), (Int.ofNat 1989703858752749923378008), (Int.ofNat 76662519022715665776216), (Int.negSucc 12488325560037144264239), (Int.ofNat 336543078116796676992)], [(Int.ofNat 0), (Int.negSucc 341870675692870226570399), (Int.negSucc 2550271269935875418339567), (Int.negSucc 9274097430848200726255679), (Int.negSucc 18738874017233418362090423), (Int.negSucc 24553536179754925414384295), (Int.negSucc 16613963104002752205120695), (Int.ofNat 5938208536462243464007632), (Int.ofNat 6893074849365713545137960), (Int.ofNat 5021225553107434157428656), (Int.negSucc 100721780093724077686823), (Int.negSucc 434467879624044020876375), (Int.ofNat 18752033049000478127040), (Int.ofNat 25219524247042705824)], [(Int.ofNat 0), (Int.ofNat 134420224846411257404640), (Int.ofNat 1168021682725504629974064), (Int.ofNat 5004667380024004138305936), (Int.ofNat 11446920848109310244968512), (Int.ofNat 17570437367704696521746016), (Int.ofNat 18307539990113176534938360), (Int.ofNat 5119485645629427448942728), (Int.negSucc 4000307242749513586583999), (Int.negSucc 2996459433198005307674495), (Int.negSucc 1716965632580557195088327), (Int.ofNat 372588339834311928851856), (Int.ofNat 18980270195736192223656), (Int.negSucc 1285096286072910690095)], [(Int.ofNat 0), (Int.negSucc 40874172449438512395839), (Int.negSucc 440290205639964470266751), (Int.negSucc 2239787361749407893356543), (Int.negSucc 5986345730588100690327407), (Int.negSucc 10084107558829485845924399), (Int.negSucc 13149252161311440775321655), (Int.negSucc 9575843968448826049444271), (Int.negSucc 120714524685489186682799), (Int.ofNat 864564192873237707993808), (Int.ofNat 1588811150283917197971144), (Int.ofNat 108328599505491511463544), (Int.negSucc 50940271640670490833263), (Int.ofNat 188350808438750926464)], [(Int.ofNat 0), (Int.ofNat 9354170727044041551120), (Int.ofNat 133605334136940402300888), (Int.ofNat 817465538466514047595032), (Int.ofNat 2661298285285088712530184), (Int.ofNat 4887408128670997554459192), (Int.ofNat 7030648642759533718981104), (Int.ofNat 7759358593645813762288752), (Int.ofNat 2903662719037169333289216), (Int.ofNat 229799403796457686609920), (Int.negSucc 460732565085509884338407), (Int.negSucc 363723839999834858653823), (Int.ofNat 18102008408660925495744), (Int.ofNat 2302435428124988916288)], [(Int.ofNat 0), (Int.negSucc 1544062895853683283839), (Int.negSucc 31649463129207548371151), (Int.negSucc 238113061521504078625751), (Int.negSucc 978543633470544866769551), (Int.negSucc 2062740448540504529172887), (Int.negSucc 3015409794450140165698535), (Int.negSucc 4092354685840208814567959), (Int.negSucc 3047566467975795094420295), (Int.negSucc 716711487106019886648503), (Int.negSucc 190240663021812202774463), (Int.ofNat 200557342797528361208112), (Int.ofNat 28967411780138497820688), (Int.negSucc 1346208908044122015263)], [(Int.ofNat 0), (Int.ofNat 171290514531700142160), (Int.ofNat 5611416973562394713832), (Int.ofNat 53820466730542627199928), (Int.ofNat 286398514507217032618824), (Int.ofNat 750100960743822928504992), (Int.ofNat 1116240070383062627563224), (Int.ofNat 1555370344937587450426992), (Int.ofNat 1771941651628959348142824), (Int.ofNat 767552762235867877675296), (Int.ofNat 255834743041871069192928), (Int.ofNat 9004578448939196633568), (Int.negSucc 28446262410768191161631), (Int.negSucc 1305745368350674309055)], [(Int.ofNat 0), (Int.negSucc 11184090260518857119), (Int.negSucc 698991663539565993311), (Int.negSucc 9083391930802659337895), (Int.negSucc 63856543162345492016207), (Int.negSucc 223586079771804328953935), (Int.negSucc 373231730292151477224119), (Int.negSucc 464421883075056721092599), (Int.negSucc 662273237268614733901775), (Int.negSucc 491596824260393032337711), (Int.negSucc 166084938496259279965007), (Int.negSucc 60054146702895008685311), (Int.ofNat 4303961555125886363808), (Int.ofNat 1444403311609211909568)], [(Int.ofNat 0), (Int.ofNat 310966112737051200), (Int.ofNat 54622530424032727824), (Int.ofNat 1079431873344916052184), (Int.ofNat 10291573914967963164672), (Int.ofNat 51092254892579879253600), (Int.ofNat 109055926082913383008296), (Int.ofNat 123797439683419928980320), (Int.ofNat 166448921885839414950336), (Int.ofNat 196045231282709519791296), (Int.ofNat 87984804157001095303584), (Int.ofNat 34169318044930109811744), (Int.ofNat 5980787821995908019264), (Int.negSucc 149485813571249885951)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2024271661061269439), (Int.negSucc 81115929723352743215), (Int.negSucc 1112920216348039467047), (Int.negSucc 8309746970148808163015), (Int.negSucc 25322507070388846734239), (Int.negSucc 32018916971547622303919), (Int.negSucc 30457802125984133857679), (Int.negSucc 47914787953228092035615), (Int.negSucc 34730018543250962851391), (Int.negSucc 12282648759418571627327), (Int.negSucc 3971027977627982203583), (Int.negSucc 337811611398334273151)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2933383136036408640), (Int.ofNat 70772550898563213552), (Int.ofNat 871350778242825480720), (Int.ofNat 4198073559164110765152), (Int.ofNat 7283034163332616097952), (Int.ofNat 5246280040730343037344), (Int.ofNat 6665808930454476762624), (Int.ofNat 8694745520057036322048), (Int.ofNat 3600578372233935378816), (Int.ofNat 1192907673107261095680), (Int.ofNat 174676052152927742976)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1918678796925461567), (Int.negSucc 48903357136789266767), (Int.negSucc 439774376914186044911), (Int.negSucc 1211326679285203226687), (Int.negSucc 1044081022091215093343), (Int.negSucc 450734506213478470847), (Int.negSucc 1162963075357911032063), (Int.negSucc 788833674282997518335), (Int.negSucc 228503427398942940287), (Int.negSucc 33534255803002788095)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 830902093405787520), (Int.ofNat 23273650772560586592), (Int.ofNat 124033056791337531936), (Int.ofNat 174790390628743113024), (Int.ofNat 25941933329799808512), (Int.ofNat 41770295777285465472), (Int.ofNat 100136651939916723072), (Int.ofNat 31104998923003990272), (Int.ofNat 2248051477878927360)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 252285651994463999), (Int.negSucc 6020906170622521535), (Int.negSucc 16805296726573424831), (Int.negSucc 6825978674380840319), (Int.ofNat 7456857978113396352), (Int.negSucc 5087411031639211775), (Int.negSucc 2248051477878927359)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 34661996318817792), (Int.ofNat 626933473107308928), (Int.ofNat 752125207313651328), (Int.negSucc 726187507251390719)]]

theorem h0n90_arithmetic_row0 :
    (BiPoly.mul h0p4 h0p89).getD 0 []=h0p90.getD 0 [] := by
  decide +kernel

theorem h0n90_arithmetic_row1 :
    (BiPoly.mul h0p4 h0p89).getD 1 []=h0p90.getD 1 [] := by
  decide +kernel

theorem h0n90_arithmetic_row2 :
    (BiPoly.mul h0p4 h0p89).getD 2 []=h0p90.getD 2 [] := by
  decide +kernel

theorem h0n90_arithmetic_row3 :
    (BiPoly.mul h0p4 h0p89).getD 3 []=h0p90.getD 3 [] := by
  decide +kernel

theorem h0n90_arithmetic_row4 :
    (BiPoly.mul h0p4 h0p89).getD 4 []=h0p90.getD 4 [] := by
  decide +kernel

theorem h0n90_arithmetic_row5 :
    (BiPoly.mul h0p4 h0p89).getD 5 []=h0p90.getD 5 [] := by
  decide +kernel

theorem h0n90_arithmetic_row6 :
    (BiPoly.mul h0p4 h0p89).getD 6 []=h0p90.getD 6 [] := by
  decide +kernel

theorem h0n90_arithmetic_row7 :
    (BiPoly.mul h0p4 h0p89).getD 7 []=h0p90.getD 7 [] := by
  decide +kernel

theorem h0n90_arithmetic_row8 :
    (BiPoly.mul h0p4 h0p89).getD 8 []=h0p90.getD 8 [] := by
  decide +kernel

theorem h0n90_arithmetic_row9 :
    (BiPoly.mul h0p4 h0p89).getD 9 []=h0p90.getD 9 [] := by
  decide +kernel

theorem h0n90_arithmetic_row10 :
    (BiPoly.mul h0p4 h0p89).getD 10 []=h0p90.getD 10 [] := by
  decide +kernel

theorem h0n90_arithmetic_row11 :
    (BiPoly.mul h0p4 h0p89).getD 11 []=h0p90.getD 11 [] := by
  decide +kernel

theorem h0n90_arithmetic_row12 :
    (BiPoly.mul h0p4 h0p89).getD 12 []=h0p90.getD 12 [] := by
  decide +kernel

theorem h0n90_arithmetic_row13 :
    (BiPoly.mul h0p4 h0p89).getD 13 []=h0p90.getD 13 [] := by
  decide +kernel

theorem h0n90_arithmetic_row14 :
    (BiPoly.mul h0p4 h0p89).getD 14 []=h0p90.getD 14 [] := by
  decide +kernel

theorem h0n90_arithmetic_row15 :
    (BiPoly.mul h0p4 h0p89).getD 15 []=h0p90.getD 15 [] := by
  decide +kernel

theorem h0n90_arithmetic_row16 :
    (BiPoly.mul h0p4 h0p89).getD 16 []=h0p90.getD 16 [] := by
  decide +kernel

theorem h0n90_arithmetic_row17 :
    (BiPoly.mul h0p4 h0p89).getD 17 []=h0p90.getD 17 [] := by
  decide +kernel

theorem h0n90_arithmetic_row18 :
    (BiPoly.mul h0p4 h0p89).getD 18 []=h0p90.getD 18 [] := by
  decide +kernel

theorem h0n90_arithmetic_row19 :
    (BiPoly.mul h0p4 h0p89).getD 19 []=h0p90.getD 19 [] := by
  decide +kernel

theorem h0n90_arithmetic_row20 :
    (BiPoly.mul h0p4 h0p89).getD 20 []=h0p90.getD 20 [] := by
  decide +kernel

theorem h0n90_arithmetic_row21 :
    (BiPoly.mul h0p4 h0p89).getD 21 []=h0p90.getD 21 [] := by
  decide +kernel

theorem h0n90_arithmetic_row22 :
    (BiPoly.mul h0p4 h0p89).getD 22 []=h0p90.getD 22 [] := by
  decide +kernel

theorem h0n90_arithmetic_row23 :
    (BiPoly.mul h0p4 h0p89).getD 23 []=h0p90.getD 23 [] := by
  decide +kernel

theorem h0n90_arithmetic_row24 :
    (BiPoly.mul h0p4 h0p89).getD 24 []=h0p90.getD 24 [] := by
  decide +kernel

theorem h0n90_arithmetic : BiPoly.mul h0p4 h0p89=h0p90 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h0p4 h0p89).getD j.val []=h0p90.getD j.val [] :=
      (fun j => Fin.cases h0n90_arithmetic_row0 (fun j => Fin.cases h0n90_arithmetic_row1 (fun j => Fin.cases h0n90_arithmetic_row2 (fun j => Fin.cases h0n90_arithmetic_row3 (fun j => Fin.cases h0n90_arithmetic_row4 (fun j => Fin.cases h0n90_arithmetic_row5 (fun j => Fin.cases h0n90_arithmetic_row6 (fun j => Fin.cases h0n90_arithmetic_row7 (fun j => Fin.cases h0n90_arithmetic_row8 (fun j => Fin.cases h0n90_arithmetic_row9 (fun j => Fin.cases h0n90_arithmetic_row10 (fun j => Fin.cases h0n90_arithmetic_row11 (fun j => Fin.cases h0n90_arithmetic_row12 (fun j => Fin.cases h0n90_arithmetic_row13 (fun j => Fin.cases h0n90_arithmetic_row14 (fun j => Fin.cases h0n90_arithmetic_row15 (fun j => Fin.cases h0n90_arithmetic_row16 (fun j => Fin.cases h0n90_arithmetic_row17 (fun j => Fin.cases h0n90_arithmetic_row18 (fun j => Fin.cases h0n90_arithmetic_row19 (fun j => Fin.cases h0n90_arithmetic_row20 (fun j => Fin.cases h0n90_arithmetic_row21 (fun j => Fin.cases h0n90_arithmetic_row22 (fun j => Fin.cases h0n90_arithmetic_row23 (fun j => Fin.cases h0n90_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n90 : h0e90.toBi mapPolyEnv=h0p90 := by
  change BiPoly.mul (h0e4.toBi mapPolyEnv) (h0e89.toBi mapPolyEnv)=h0p90
  rw [h0n4, h0n89]
  exact h0n90_arithmetic

#print axioms h0n90_arithmetic
end StackSorting.RationalLift
