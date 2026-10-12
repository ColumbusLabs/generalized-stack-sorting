import BivariateRowEquality
import Horner4Base
import Horner4Node083
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p84 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 562005795993695999999), (Int.negSucc 3423187049271604703999), (Int.negSucc 603817032200624864639), (Int.ofNat 16483774481848561484160), (Int.negSucc 5710318978958281739519), (Int.negSucc 22965136274604447982079), (Int.ofNat 6142027608308727296640), (Int.ofNat 9170434643183615894400)], [(Int.ofNat 0), (Int.ofNat 6774459494966974080000), (Int.ofNat 38849820691190480184960), (Int.negSucc 4411863871525923248447), (Int.negSucc 197547149688320294169983), (Int.ofNat 98571046263898645215936), (Int.ofNat 236710685030114873220480), (Int.negSucc 82436930617521462404543), (Int.negSucc 86333572355050103478911), (Int.ofNat 4774929780707868916800)], [(Int.ofNat 0), (Int.negSucc 37978540323132896409599), (Int.negSucc 205949676489843502543679), (Int.ofNat 69425592191568135397728), (Int.ofNat 1064250052362460809195264), (Int.negSucc 638869928575230623134943), (Int.negSucc 1086369637766774485113791), (Int.ofNat 392310704129258498726304), (Int.ofNat 366666265213840615932288), (Int.negSucc 6197216365146517537823), (Int.negSucc 1041096086220443469695)], [(Int.ofNat 0), (Int.ofNat 131404195547087258764800), (Int.ofNat 677845809986850783646560), (Int.negSucc 320464904257051629475247), (Int.negSucc 3447386304646877593441487), (Int.ofNat 2122720173231789051905328), (Int.ofNat 3010696949392979391252432), (Int.negSucc 767779514553472365160655), (Int.negSucc 975612392876212556269103), (Int.negSucc 151574961919582952896175), (Int.ofNat 25887315862105238774736), (Int.negSucc 1104983151641276903423)], [(Int.ofNat 0), (Int.negSucc 313975101799183964860799), (Int.negSucc 1552674884327445188105279), (Int.ofNat 769522804075164057543360), (Int.ofNat 7546537895970277785776256), (Int.negSucc 3766061158324148321871263), (Int.negSucc 5923706656358405918038175), (Int.negSucc 117070929641455934618879), (Int.ofNat 1850948884876588724546496), (Int.ofNat 846260982089513912991456), (Int.negSucc 112759491130485331168223), (Int.ofNat 7247781258228615144960), (Int.negSucc 235424577239960942591)], [(Int.ofNat 0), (Int.ofNat 549199199404180090209600), (Int.ofNat 2628654081292160149170240), (Int.negSucc 994956371393822167439663), (Int.negSucc 11832360631252337343667535), (Int.ofNat 2221506929672901285562512), (Int.ofNat 9235482819287138892563328), (Int.ofNat 3896881142424558102940320), (Int.negSucc 2321218603861294468930703), (Int.negSucc 2153452058960182847624879), (Int.ofNat 88784392980889398096288), (Int.ofNat 3513623008111386999408), (Int.ofNat 106061616330030149760), (Int.negSucc 15413326191745016831)], [(Int.ofNat 0), (Int.negSucc 727288575564254899607999), (Int.negSucc 3407257260038858871083759), (Int.ofNat 322069546136863041665112), (Int.ofNat 13607689655829449742281712), (Int.ofNat 5594975222107954974517440), (Int.negSucc 11401573174986508880633135), (Int.negSucc 9649296076269288364647695), (Int.ofNat 707931367623370174241520), (Int.ofNat 3132645283481855244393888), (Int.ofNat 568856555065895673686688), (Int.negSucc 92707146089024009141159), (Int.ofNat 5017231415402235463392), (Int.negSucc 93298421063321565695), (Int.ofNat 82811164576757760)], [(Int.ofNat 0), (Int.ofNat 743634509260097291716800), (Int.ofNat 3452761382428559084466240), (Int.ofNat 1311479930644820307461952), (Int.negSucc 11310873595163809763393879), (Int.negSucc 16900024213090613722709447), (Int.ofNat 8837031513634658072398728), (Int.ofNat 13686970576882972266720792), (Int.ofNat 4045121248844223873973512), (Int.negSucc 2318453514191134366254791), (Int.negSucc 1892667054819729698825111), (Int.ofNat 159654250777340859790104), (Int.negSucc 5631674651834962531967), (Int.ofNat 190961836991002852416), (Int.negSucc 2687026277693691647)], [(Int.ofNat 0), (Int.negSucc 593195271099840829310399), (Int.negSucc 2765235582118212766019759), (Int.negSucc 2933627876099960278356407), (Int.ofNat 6109428970921058395564080), (Int.ofNat 23472131212427607824273472), (Int.ofNat 1204174615590132415930872), (Int.negSucc 13073314386050235540509759), (Int.negSucc 9429154237594647987528359), (Int.negSucc 731304955757457930938591), (Int.ofNat 2527440026982828518316216), (Int.ofNat 165314169790971610327128), (Int.negSucc 31368582607401685135271), (Int.ofNat 1297083487952930155104), (Int.negSucc 17185379144588518271)], [(Int.ofNat 0), (Int.ofNat 370343891021662634198400), (Int.ofNat 1754526786010764800894880), (Int.ofNat 3427050754627420188645792), (Int.negSucc 949199204276474060962103), (Int.negSucc 20203545190125795077265815), (Int.negSucc 14454095237515714569604223), (Int.ofNat 7303187215194495098241504), (Int.ofNat 10938664017232474847093928), (Int.ofNat 4450487555498992805079048), (Int.negSucc 1129784855746015712242703), (Int.negSucc 852031084768528392893423), (Int.ofNat 65022191038286707232112), (Int.negSucc 1517996215140639903791), (Int.ofNat 9886114471674645120)], [(Int.ofNat 0), (Int.negSucc 180343946494518365212799), (Int.negSucc 876613913557878039001439), (Int.negSucc 2666294900369863535446943), (Int.negSucc 1878543437747082398175575), (Int.ofNat 10669190959199157508148280), (Int.ofNat 21261563753011348343412768), (Int.ofNat 1949693793823607513367312), (Int.negSucc 7417573821770525668477943), (Int.negSucc 6129231715235320243844831), (Int.negSucc 1422414573477676092609311), (Int.ofNat 1023885991867202220363792), (Int.ofNat 34954791461928141263376), (Int.negSucc 6160027010489372962871), (Int.ofNat 168271539058398338496)], [(Int.ofNat 0), (Int.ofNat 67778036071153299792000), (Int.ofNat 339191604382758607386720), (Int.ofNat 1446984867559368820557648), (Int.ofNat 2190108182262703167777936), (Int.negSucc 2321708529538575833832071), (Int.negSucc 17338570633729188946828991), (Int.negSucc 10136855360765170137494831), (Int.ofNat 1709430488892781714157688), (Int.ofNat 4584405441695808262941720), (Int.ofNat 2851292794781431687719240), (Int.negSucc 187623315969686690988263), (Int.negSucc 211698087508060950902399), (Int.ofNat 9382321405561999739976), (Int.ofNat 12609762123521352912)], [(Int.ofNat 0), (Int.negSucc 19273517402175777715199), (Int.negSucc 98312714758643495636639), (Int.negSucc 533760982240588809520175), (Int.negSucc 1292104899654416885560127), (Int.negSucc 1180153717401756601671647), (Int.ofNat 8235398915810120022145536), (Int.ofNat 12298622095057320406845384), (Int.ofNat 3075785274836082781331472), (Int.negSucc 1476015499532675044375175), (Int.negSucc 2251810163885149527760751), (Int.negSucc 772717695722190599149895), (Int.ofNat 192035091959937140795832), (Int.ofNat 9168861026349868439304), (Int.negSucc 642548143036455345047)], [(Int.ofNat 0), (Int.ofNat 4009345313519335137600), (Int.ofNat 19926186181276627776000), (Int.ofNat 114849667676508688296912), (Int.ofNat 439887211957567141149888), (Int.ofNat 1218125517465140032871376), (Int.negSucc 1538271042617227246167887), (Int.negSucc 8446220652885669461971511), (Int.negSucc 5215585650088376360970791), (Int.negSucc 892381606398528741564623), (Int.ofNat 740674586370294032929680), (Int.ofNat 880533737524323278821272), (Int.ofNat 39018080164941729846768), (Int.negSucc 25423048118225557685015), (Int.ofNat 94175404219375463232)], [(Int.ofNat 0), (Int.negSucc 575531656429625265599), (Int.negSucc 2336895513110826125999), (Int.negSucc 1591185837601647388391), (Int.negSucc 50134687031548438533983), (Int.negSucc 422562112702616433001535), (Int.negSucc 647625130109412687418751), (Int.ofNat 3280120004082151208802168), (Int.ofNat 4478808613558723295233008), (Int.ofNat 1774612606189224098613936), (Int.ofNat 309059758877621809097184), (Int.negSucc 357686614594283988435527), (Int.negSucc 178431803656009397525975), (Int.ofNat 9626613061361709976944), (Int.ofNat 1151217714062494458144)], [(Int.ofNat 0), (Int.ofNat 50950408456910635200), (Int.ofNat 10456498760799321600), (Int.negSucc 8073744086302010832671), (Int.negSucc 30590007537612545441015), (Int.ofNat 4083489687376738017432), (Int.ofNat 500791028540062023817320), (Int.negSucc 402702563917083041592623), (Int.negSucc 2339471701393336332457103), (Int.negSucc 1579297614021920249102879), (Int.negSucc 578756054973137088105215), (Int.negSucc 68697334196698462014455), (Int.ofNat 111358615337360706924000), (Int.ofNat 14147153663058218406528), (Int.negSucc 673104454022061007631)], [(Int.ofNat 0), (Int.negSucc 2096385593740151999), (Int.ofNat 44046365459256270480), (Int.ofNat 2867621757029910320808), (Int.ofNat 18820052888081018951568), (Int.ofNat 58918669404297334361040), (Int.negSucc 96653851786045128214967), (Int.negSucc 243893452960640397619511), (Int.ofNat 657792518243419528939800), (Int.ofNat 922642279459953972601320), (Int.ofNat 445840187258239654105656), (Int.ofNat 165727580420861204726736), (Int.negSucc 3627775692565784006111), (Int.negSucc 14549567547471764158079), (Int.negSucc 652872684175337154527)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6370950629032948319), (Int.negSucc 512376201023511201023), (Int.negSucc 5235620359135922053943), (Int.negSucc 27263862180439084137287), (Int.negSucc 28248821844120104025695), (Int.ofNat 122387175444088796393112), (Int.negSucc 16567581193522542486719), (Int.negSucc 336902895897173190377351), (Int.negSucc 242308141604445275220527), (Int.negSucc 108305399160156446955935), (Int.negSucc 30843638897159440382543), (Int.ofNat 2513081605465246159296), (Int.ofNat 722201655804605954784)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 310966112737051200), (Int.ofNat 49260992858049153744), (Int.ofNat 842328420363951261192), (Int.ofNat 6507798010906266568872), (Int.ofNat 21009021136086163813776), (Int.negSucc 12650470009218513723959), (Int.negSucc 53544116789750078601479), (Int.ofNat 55866075158140082239536), (Int.ofNat 93296403091748697912864), (Int.ofNat 47661426056836081905696), (Int.ofNat 19908427353892697403648), (Int.ofNat 2953022457605141538144), (Int.negSucc 74742906785624942975)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2024271661061269439), (Int.negSucc 75521119331364451055), (Int.negSucc 896026193243342580599), (Int.negSucc 5464743340637992472063), (Int.negSucc 6208254196530796491623), (Int.ofNat 15878913991464366641664), (Int.ofNat 7805063620834053456960), (Int.negSucc 21165031966170429966383), (Int.negSucc 15985343433441382746623), (Int.negSucc 7132895522876695756031), (Int.negSucc 2069966891663574670079), (Int.negSucc 168905805699167136575)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2933383136036408640), (Int.ofNat 65958319144585964016), (Int.ofNat 730196314922116626336), (Int.ofNat 2455978947121123684848), (Int.negSucc 761981502423772372319), (Int.negSucc 5579373691630230181631), (Int.ofNat 905629879750832444448), (Int.ofNat 3722704035178066198848), (Int.ofNat 1809920501488352100096), (Int.ofNat 640122849591862483584), (Int.ofNat 87338026076463871488)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1918678796925461567), (Int.negSucc 46262321015314469327), (Int.negSucc 364110523935111884447), (Int.negSucc 462313030829504179247), (Int.ofNat 912082267520816187456), (Int.ofNat 853704026070656142816), (Int.negSucc 406461062363491437695), (Int.negSucc 334244808243948863231), (Int.negSucc 122635277650222167167), (Int.negSucc 16767127901501394047)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 830902093405787520), (Int.ofNat 22238135337000327264), (Int.ofNat 93529848175502613696), (Int.negSucc 13311424073594554271), (Int.negSucc 210345033832124047487), (Int.negSucc 41468346333302237567), (Int.ofNat 38621277543110091264), (Int.ofNat 16114512330971726976), (Int.ofNat 1124025738939463680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 252285651994463999), (Int.negSucc 5727650172054323903), (Int.negSucc 9652583530660202495), (Int.ofNat 15737296143639999168), (Int.ofNat 17608986747084638592), (Int.negSucc 1958021225935648127), (Int.negSucc 1124025738939463679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 34661996318817792), (Int.ofNat 588163037146623360), (Int.ofNat 57180450875307264), (Int.negSucc 1510790912979384959)]]

theorem h4n84_arithmetic_row0 :
    (BiPoly.mul h4p5 h4p83).getD 0 []=h4p84.getD 0 [] := by
  decide +kernel

theorem h4n84_arithmetic_row1 :
    (BiPoly.mul h4p5 h4p83).getD 1 []=h4p84.getD 1 [] := by
  decide +kernel

theorem h4n84_arithmetic_row2 :
    (BiPoly.mul h4p5 h4p83).getD 2 []=h4p84.getD 2 [] := by
  decide +kernel

theorem h4n84_arithmetic_row3 :
    (BiPoly.mul h4p5 h4p83).getD 3 []=h4p84.getD 3 [] := by
  decide +kernel

theorem h4n84_arithmetic_row4 :
    (BiPoly.mul h4p5 h4p83).getD 4 []=h4p84.getD 4 [] := by
  decide +kernel

theorem h4n84_arithmetic_row5 :
    (BiPoly.mul h4p5 h4p83).getD 5 []=h4p84.getD 5 [] := by
  decide +kernel

theorem h4n84_arithmetic_row6 :
    (BiPoly.mul h4p5 h4p83).getD 6 []=h4p84.getD 6 [] := by
  decide +kernel

theorem h4n84_arithmetic_row7 :
    (BiPoly.mul h4p5 h4p83).getD 7 []=h4p84.getD 7 [] := by
  decide +kernel

theorem h4n84_arithmetic_row8 :
    (BiPoly.mul h4p5 h4p83).getD 8 []=h4p84.getD 8 [] := by
  decide +kernel

theorem h4n84_arithmetic_row9 :
    (BiPoly.mul h4p5 h4p83).getD 9 []=h4p84.getD 9 [] := by
  decide +kernel

theorem h4n84_arithmetic_row10 :
    (BiPoly.mul h4p5 h4p83).getD 10 []=h4p84.getD 10 [] := by
  decide +kernel

theorem h4n84_arithmetic_row11 :
    (BiPoly.mul h4p5 h4p83).getD 11 []=h4p84.getD 11 [] := by
  decide +kernel

theorem h4n84_arithmetic_row12 :
    (BiPoly.mul h4p5 h4p83).getD 12 []=h4p84.getD 12 [] := by
  decide +kernel

theorem h4n84_arithmetic_row13 :
    (BiPoly.mul h4p5 h4p83).getD 13 []=h4p84.getD 13 [] := by
  decide +kernel

theorem h4n84_arithmetic_row14 :
    (BiPoly.mul h4p5 h4p83).getD 14 []=h4p84.getD 14 [] := by
  decide +kernel

theorem h4n84_arithmetic_row15 :
    (BiPoly.mul h4p5 h4p83).getD 15 []=h4p84.getD 15 [] := by
  decide +kernel

theorem h4n84_arithmetic_row16 :
    (BiPoly.mul h4p5 h4p83).getD 16 []=h4p84.getD 16 [] := by
  decide +kernel

theorem h4n84_arithmetic_row17 :
    (BiPoly.mul h4p5 h4p83).getD 17 []=h4p84.getD 17 [] := by
  decide +kernel

theorem h4n84_arithmetic_row18 :
    (BiPoly.mul h4p5 h4p83).getD 18 []=h4p84.getD 18 [] := by
  decide +kernel

theorem h4n84_arithmetic_row19 :
    (BiPoly.mul h4p5 h4p83).getD 19 []=h4p84.getD 19 [] := by
  decide +kernel

theorem h4n84_arithmetic_row20 :
    (BiPoly.mul h4p5 h4p83).getD 20 []=h4p84.getD 20 [] := by
  decide +kernel

theorem h4n84_arithmetic_row21 :
    (BiPoly.mul h4p5 h4p83).getD 21 []=h4p84.getD 21 [] := by
  decide +kernel

theorem h4n84_arithmetic_row22 :
    (BiPoly.mul h4p5 h4p83).getD 22 []=h4p84.getD 22 [] := by
  decide +kernel

theorem h4n84_arithmetic_row23 :
    (BiPoly.mul h4p5 h4p83).getD 23 []=h4p84.getD 23 [] := by
  decide +kernel

theorem h4n84_arithmetic_row24 :
    (BiPoly.mul h4p5 h4p83).getD 24 []=h4p84.getD 24 [] := by
  decide +kernel

theorem h4n84_arithmetic : BiPoly.mul h4p5 h4p83=h4p84 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h4p5 h4p83).getD j.val []=h4p84.getD j.val [] :=
      (fun j => Fin.cases h4n84_arithmetic_row0 (fun j => Fin.cases h4n84_arithmetic_row1 (fun j => Fin.cases h4n84_arithmetic_row2 (fun j => Fin.cases h4n84_arithmetic_row3 (fun j => Fin.cases h4n84_arithmetic_row4 (fun j => Fin.cases h4n84_arithmetic_row5 (fun j => Fin.cases h4n84_arithmetic_row6 (fun j => Fin.cases h4n84_arithmetic_row7 (fun j => Fin.cases h4n84_arithmetic_row8 (fun j => Fin.cases h4n84_arithmetic_row9 (fun j => Fin.cases h4n84_arithmetic_row10 (fun j => Fin.cases h4n84_arithmetic_row11 (fun j => Fin.cases h4n84_arithmetic_row12 (fun j => Fin.cases h4n84_arithmetic_row13 (fun j => Fin.cases h4n84_arithmetic_row14 (fun j => Fin.cases h4n84_arithmetic_row15 (fun j => Fin.cases h4n84_arithmetic_row16 (fun j => Fin.cases h4n84_arithmetic_row17 (fun j => Fin.cases h4n84_arithmetic_row18 (fun j => Fin.cases h4n84_arithmetic_row19 (fun j => Fin.cases h4n84_arithmetic_row20 (fun j => Fin.cases h4n84_arithmetic_row21 (fun j => Fin.cases h4n84_arithmetic_row22 (fun j => Fin.cases h4n84_arithmetic_row23 (fun j => Fin.cases h4n84_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n84 : h4e84.toBi mapPolyEnv=h4p84 := by
  change BiPoly.mul (h4e5.toBi mapPolyEnv) (h4e83.toBi mapPolyEnv)=h4p84
  rw [h4n5, h4n83]
  exact h4n84_arithmetic

#print axioms h4n84_arithmetic
end StackSorting.RationalLift
