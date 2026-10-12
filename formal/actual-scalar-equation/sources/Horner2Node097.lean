import BivariateRowEquality
import Horner2Base
import Horner2Node096
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p97 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 666126596968528895), (Int.negSucc 1643360688094948559), (Int.negSucc 2570722786006410959), (Int.negSucc 19609456531128421535), (Int.ofNat 35798685248254845024), (Int.ofNat 55240642150511379696), (Int.negSucc 40535045705162133647), (Int.negSucc 41961034771170238079)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7953600179984279616), (Int.ofNat 19556711140176977040), (Int.ofNat 41087482859643734880), (Int.ofNat 283643210006707398048), (Int.negSucc 441613132052329422143), (Int.negSucc 604184305961920194287), (Int.ofNat 405646509015905161248), (Int.ofNat 348752382437463994944), (Int.negSucc 14599039353357498623)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 45074030281953675263), (Int.negSucc 108353066369042666555), (Int.negSucc 311598753695995261571), (Int.negSucc 1814023606221148541723), (Int.ofNat 2513775171110860762236), (Int.ofNat 2958223536111202029612), (Int.negSucc 1718313673953390865163), (Int.negSucc 1332735341624986540787), (Int.negSucc 24427576574533582955), (Int.ofNat 7279895422687748256)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 161132909063274484704), (Int.ofNat 371614510881609799716), (Int.ofNat 1482576989078363600304), (Int.ofNat 6853901504382827506692), (Int.negSucc 8455613830658597907863), (Int.negSucc 8665105536901502990891), (Int.ofNat 3482477072615241021600), (Int.ofNat 3141725810023445672988), (Int.ofNat 676595154887206003944), (Int.negSucc 96798962155438687319), (Int.ofNat 3797893389247873344)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 406828583469085538375), (Int.negSucc 892488394277906061947), (Int.negSucc 4889769351427978560563), (Int.negSucc 17181977226123677556431), (Int.ofNat 17779157198140227808848), (Int.ofNat 17421165836493479370780), (Int.negSucc 1300808944059984426035), (Int.negSucc 5268301160096899796039), (Int.negSucc 2823479411272564722335), (Int.ofNat 295494764568880976616), (Int.negSucc 15774721089632404175), (Int.ofNat 422247642727067520)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 768888746068240953080), (Int.ofNat 1628733938315861209122), (Int.ofNat 11704170447252519291416), (Int.ofNat 30544863763949956039616), (Int.negSucc 21761726432243174868623), (Int.negSucc 26795558340487049767007), (Int.negSucc 10574060131621430076327), (Int.ofNat 6233820008357749513848), (Int.ofNat 5694797462689585170008), (Int.ofNat 34076332046436059734), (Int.negSucc 31815061387435589999), (Int.ofNat 701769163675727840), (Int.negSucc 2199862483667199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1124250808864364869631), (Int.negSucc 2418893072776060599533), (Int.negSucc 20853759078996667677931), (Int.negSucc 40783488654806417273951), (Int.ofNat 7474322220873149517712), (Int.ofNat 33799506136992395410768), (Int.ofNat 28724051823466674401932), (Int.negSucc 2457085460335758420379), (Int.negSucc 6121709518551831010995), (Int.negSucc 1915476007358877607813), (Int.ofNat 210799400336207725892), (Int.negSucc 7682162234166933887), (Int.ofNat 78189089124650240)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1296304751872994762196), (Int.ofNat 3083705685410593228214), (Int.ofNat 28118117507505983773420), (Int.ofNat 44086494618354310367944), (Int.ofNat 24777273196830650088304), (Int.negSucc 32631746751115696601599), (Int.negSucc 38753437636366338609151), (Int.negSucc 9298412351717175237251), (Int.ofNat 2416934842194659737028), (Int.ofNat 4247376234253122282638), (Int.negSucc 171757537246051437979), (Int.negSucc 3027803286253105151), (Int.ofNat 213107721626637696)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1191147099266881311499), (Int.negSucc 3446758267023407763321), (Int.negSucc 29065882601650710042789), (Int.negSucc 42510105711165394122363), (Int.negSucc 54390900741433209607123), (Int.ofNat 15009286954708821262428), (Int.ofNat 31976220211385234398932), (Int.ofNat 23389636786194907216884), (Int.ofNat 3181668355528061867216), (Int.negSucc 3627322664879714230565), (Int.negSucc 596930349698700306769), (Int.ofNat 49820142771585004728), (Int.negSucc 874781603349280831)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 876323308892309041208), (Int.ofNat 3325984044234290607504), (Int.ofNat 23359405971002658675304), (Int.ofNat 38867086162472835195486), (Int.ofNat 61640108371468277216272), (Int.ofNat 16281538753911303697172), (Int.negSucc 14928038541265450093943), (Int.negSucc 26399618789628850167471), (Int.negSucc 7873306147181174972407), (Int.negSucc 397854893591442127039), (Int.ofNat 1425395767945914739288), (Int.negSucc 35986913173476286349), (Int.negSucc 1525340802034842991)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 516255005365010009375), (Int.negSucc 2680058586724038332571), (Int.negSucc 14915214046950934821517), (Int.negSucc 32493873699111122097679), (Int.negSucc 48827413802090162159927), (Int.negSucc 41146654267300602844851), (Int.negSucc 2684470428565698842643), (Int.ofNat 14587673128992504386412), (Int.ofNat 9808890980056775185924), (Int.ofNat 3662749981915685264932), (Int.negSucc 923717950690788401889), (Int.negSucc 109328318286722105111), (Int.ofNat 4246510591184384544)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 242560380021573032632), (Int.ofNat 1747665840736391598704), (Int.ofNat 7858817566891723498364), (Int.ofNat 22846898369673554949342), (Int.ofNat 31408557785827067416176), (Int.ofNat 43413565198472094953900), (Int.ofNat 15887931114724390509064), (Int.ofNat 377431477339693926192), (Int.negSucc 7292382737691147085839), (Int.negSucc 3546119720842963849191), (Int.negSucc 525305132926079934603), (Int.ofNat 191804090051644912462), (Int.ofNat 2340138074466414312)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 90107098153210503375), (Int.negSucc 900898111617853342799), (Int.negSucc 3608934174070692114895), (Int.negSucc 12758346338750869767855), (Int.negSucc 18447704077555385586019), (Int.negSucc 29122150274988809426015), (Int.negSucc 20693608109368496191527), (Int.negSucc 7965879467215733282879), (Int.ofNat 1710511437794900248896), (Int.ofNat 1736108657236902040048), (Int.ofNat 1141688207379520269744), (Int.negSucc 47802666709854860651), (Int.negSucc 10062771765624516887)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 26073291146890966296), (Int.ofNat 360456647597009902418), (Int.ofNat 1506633861360515579752), (Int.ofNat 5574325546278860502364), (Int.ofNat 10027662188614984903736), (Int.ofNat 14135172137408115797412), (Int.ofNat 16398903786421987207992), (Int.ofNat 8414661302823561825516), (Int.ofNat 2428453611678489875352), (Int.negSucc 254169354948631814735), (Int.negSucc 596987369408567606759), (Int.negSucc 121092444185624575739), (Int.ofNat 3487058629104758688)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5734899344704843311), (Int.negSucc 109973403649859539509), (Int.negSucc 563086799452305818615), (Int.negSucc 1951281413854631765775), (Int.negSucc 4624168903275539825319), (Int.negSucc 5681114330405469343651), (Int.negSucc 8620368631103250404711), (Int.negSucc 5930558785964439176795), (Int.negSucc 3049013205763489330811), (Int.negSucc 512401064204260289483), (Int.negSucc 11423384314337535083), (Int.ofNat 107657280228690391680), (Int.ofNat 7051761201860750448)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 921026918958071732), (Int.ofNat 25039857163532415846), (Int.ofNat 175822279820979633252), (Int.ofNat 578789897909894884276), (Int.ofNat 1665140595880461688464), (Int.ofNat 2153403818924548748508), (Int.ofNat 3110821547274127129320), (Int.ofNat 3120153182552693766096), (Int.ofNat 1866841916922136350288), (Int.ofNat 658740764535416042652), (Int.ofNat 165139576242033808224), (Int.negSucc 12283254939848556455), (Int.negSucc 5922191944100686175)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 100745759314998395), (Int.negSucc 4128356418450229673), (Int.negSucc 42355031904968349797), (Int.negSucc 152517407825039565995), (Int.negSucc 454024056346194409163), (Int.negSucc 756813273085286642951), (Int.negSucc 829545748265835938807), (Int.negSucc 1168372524114768672107), (Int.negSucc 788503655574687890843), (Int.negSucc 415399832297456214383), (Int.negSucc 111717053400602618063), (Int.negSucc 24117880544312814575), (Int.negSucc 140944931329006943)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6566429827433304), (Int.ofNat 469915467413683788), (Int.ofNat 7323415982999274744), (Int.ofNat 34605814716161748486), (Int.ofNat 95836216168861756488), (Int.ofNat 214359092687384298432), (Int.ofNat 195996368266314201144), (Int.ofNat 289691486617025427948), (Int.ofNat 254705777236290796560), (Int.ofNat 155623831800068785032), (Int.ofNat 52638554314346887584), (Int.ofNat 14310198395364326256), (Int.ofNat 1631033820778419072)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 183492558746639), (Int.negSucc 33721174813105475), (Int.negSucc 839694800297195657), (Int.negSucc 6043286134690147043), (Int.negSucc 16665454237583243771), (Int.negSucc 43623896656162196339), (Int.negSucc 47673157373100953747), (Int.negSucc 44741046156696056447), (Int.negSucc 60013866155151612815), (Int.negSucc 37602603109016136575), (Int.negSucc 17387662119188309423), (Int.negSucc 4144692414688980479), (Int.negSucc 569294148480989759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1189772647167600), (Int.ofNat 56392203503181636), (Int.ofNat 700638677370270018), (Int.ofNat 2453237748316592568), (Int.ofNat 6010259488745114916), (Int.ofNat 10145443586851466496), (Int.ofNat 4627942663769454024), (Int.ofNat 8518535288982484128), (Int.ofNat 6383675847503806560), (Int.ofNat 3385798226083711872), (Int.ofNat 804033177280175232), (Int.ofNat 52992933196151808)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1658222333988767), (Int.negSucc 43549307615643191), (Int.negSucc 270387460385396315), (Int.negSucc 559040710155930575), (Int.negSucc 1432777027693277519), (Int.negSucc 607176552765724847), (Int.negSucc 414194704046835263), (Int.negSucc 698434733270218751), (Int.negSucc 376428408565939199), (Int.negSucc 77332455681619967)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 823409256041280), (Int.ofNat 16082056932750000), (Int.ofNat 39879936502373592), (Int.ofNat 99522461253376800), (Int.ofNat 111904978227416496), (Int.negSucc 51922280589336575), (Int.ofNat 28764483960028032), (Int.ofNat 24339522485468160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 132615482919551), (Int.negSucc 2246524670680415), (Int.negSucc 821985882713135), (Int.negSucc 11114548513277183), (Int.ofNat 7862389867552320)]]

theorem h2n97_arithmetic_row0 :
    (BiPoly.mul h2p4 h2p96).getD 0 []=h2p97.getD 0 [] := by
  decide +kernel

theorem h2n97_arithmetic_row1 :
    (BiPoly.mul h2p4 h2p96).getD 1 []=h2p97.getD 1 [] := by
  decide +kernel

theorem h2n97_arithmetic_row2 :
    (BiPoly.mul h2p4 h2p96).getD 2 []=h2p97.getD 2 [] := by
  decide +kernel

theorem h2n97_arithmetic_row3 :
    (BiPoly.mul h2p4 h2p96).getD 3 []=h2p97.getD 3 [] := by
  decide +kernel

theorem h2n97_arithmetic_row4 :
    (BiPoly.mul h2p4 h2p96).getD 4 []=h2p97.getD 4 [] := by
  decide +kernel

theorem h2n97_arithmetic_row5 :
    (BiPoly.mul h2p4 h2p96).getD 5 []=h2p97.getD 5 [] := by
  decide +kernel

theorem h2n97_arithmetic_row6 :
    (BiPoly.mul h2p4 h2p96).getD 6 []=h2p97.getD 6 [] := by
  decide +kernel

theorem h2n97_arithmetic_row7 :
    (BiPoly.mul h2p4 h2p96).getD 7 []=h2p97.getD 7 [] := by
  decide +kernel

theorem h2n97_arithmetic_row8 :
    (BiPoly.mul h2p4 h2p96).getD 8 []=h2p97.getD 8 [] := by
  decide +kernel

theorem h2n97_arithmetic_row9 :
    (BiPoly.mul h2p4 h2p96).getD 9 []=h2p97.getD 9 [] := by
  decide +kernel

theorem h2n97_arithmetic_row10 :
    (BiPoly.mul h2p4 h2p96).getD 10 []=h2p97.getD 10 [] := by
  decide +kernel

theorem h2n97_arithmetic_row11 :
    (BiPoly.mul h2p4 h2p96).getD 11 []=h2p97.getD 11 [] := by
  decide +kernel

theorem h2n97_arithmetic_row12 :
    (BiPoly.mul h2p4 h2p96).getD 12 []=h2p97.getD 12 [] := by
  decide +kernel

theorem h2n97_arithmetic_row13 :
    (BiPoly.mul h2p4 h2p96).getD 13 []=h2p97.getD 13 [] := by
  decide +kernel

theorem h2n97_arithmetic_row14 :
    (BiPoly.mul h2p4 h2p96).getD 14 []=h2p97.getD 14 [] := by
  decide +kernel

theorem h2n97_arithmetic_row15 :
    (BiPoly.mul h2p4 h2p96).getD 15 []=h2p97.getD 15 [] := by
  decide +kernel

theorem h2n97_arithmetic_row16 :
    (BiPoly.mul h2p4 h2p96).getD 16 []=h2p97.getD 16 [] := by
  decide +kernel

theorem h2n97_arithmetic_row17 :
    (BiPoly.mul h2p4 h2p96).getD 17 []=h2p97.getD 17 [] := by
  decide +kernel

theorem h2n97_arithmetic_row18 :
    (BiPoly.mul h2p4 h2p96).getD 18 []=h2p97.getD 18 [] := by
  decide +kernel

theorem h2n97_arithmetic_row19 :
    (BiPoly.mul h2p4 h2p96).getD 19 []=h2p97.getD 19 [] := by
  decide +kernel

theorem h2n97_arithmetic_row20 :
    (BiPoly.mul h2p4 h2p96).getD 20 []=h2p97.getD 20 [] := by
  decide +kernel

theorem h2n97_arithmetic_row21 :
    (BiPoly.mul h2p4 h2p96).getD 21 []=h2p97.getD 21 [] := by
  decide +kernel

theorem h2n97_arithmetic_row22 :
    (BiPoly.mul h2p4 h2p96).getD 22 []=h2p97.getD 22 [] := by
  decide +kernel

theorem h2n97_arithmetic : BiPoly.mul h2p4 h2p96=h2p97 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<23 at hk
    have hf : ∀ j : Fin 23, (BiPoly.mul h2p4 h2p96).getD j.val []=h2p97.getD j.val [] :=
      (fun j => Fin.cases h2n97_arithmetic_row0 (fun j => Fin.cases h2n97_arithmetic_row1 (fun j => Fin.cases h2n97_arithmetic_row2 (fun j => Fin.cases h2n97_arithmetic_row3 (fun j => Fin.cases h2n97_arithmetic_row4 (fun j => Fin.cases h2n97_arithmetic_row5 (fun j => Fin.cases h2n97_arithmetic_row6 (fun j => Fin.cases h2n97_arithmetic_row7 (fun j => Fin.cases h2n97_arithmetic_row8 (fun j => Fin.cases h2n97_arithmetic_row9 (fun j => Fin.cases h2n97_arithmetic_row10 (fun j => Fin.cases h2n97_arithmetic_row11 (fun j => Fin.cases h2n97_arithmetic_row12 (fun j => Fin.cases h2n97_arithmetic_row13 (fun j => Fin.cases h2n97_arithmetic_row14 (fun j => Fin.cases h2n97_arithmetic_row15 (fun j => Fin.cases h2n97_arithmetic_row16 (fun j => Fin.cases h2n97_arithmetic_row17 (fun j => Fin.cases h2n97_arithmetic_row18 (fun j => Fin.cases h2n97_arithmetic_row19 (fun j => Fin.cases h2n97_arithmetic_row20 (fun j => Fin.cases h2n97_arithmetic_row21 (fun j => Fin.cases h2n97_arithmetic_row22 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n97 : h2e97.toBi mapPolyEnv=h2p97 := by
  change BiPoly.mul (h2e4.toBi mapPolyEnv) (h2e96.toBi mapPolyEnv)=h2p97
  rw [h2n4, h2n96]
  exact h2n97_arithmetic

#print axioms h2n97_arithmetic
end StackSorting.RationalLift
