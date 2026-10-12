import BivariateRowEquality
import Horner4Base
import Horner4Node229
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p230 : BiPoly.Poly := [[(Int.ofNat 1015698126772656000), (Int.ofNat 4633282022956983360), (Int.negSucc 6743309138190875519), (Int.negSucc 24006168291494534399), (Int.ofNat 43969704364695720960), (Int.negSucc 18869207084739950399)], [(Int.negSucc 9379561011903613439), (Int.negSucc 43296437032514275967), (Int.ofNat 58182723092695844160), (Int.ofNat 215408188113298129728), (Int.negSucc 394316319447338882111), (Int.ofNat 187070092051394740032), (Int.negSucc 13668685765631942399)], [(Int.ofNat 40830246488778933600), (Int.ofNat 182365410464248150800), (Int.negSucc 234236451803193842831), (Int.negSucc 833423626188096703775), (Int.ofNat 1478829812313810276288), (Int.negSucc 698642305099983149039), (Int.ofNat 67481587635485626224), (Int.negSucc 3204673811049291263)], [(Int.negSucc 111011623024858500959), (Int.negSucc 457141484897866472399), (Int.ofNat 563601119770875225168), (Int.ofNat 1781452069533697943520), (Int.negSucc 2855679167269834466399), (Int.ofNat 1100568021393564515664), (Int.negSucc 22699792318441958351), (Int.ofNat 1146274130115382752), (Int.negSucc 235417317251668991)], [(Int.ofNat 209869417537618952160), (Int.ofNat 762312667857384172464), (Int.negSucc 863039183346359208047), (Int.negSucc 2225092755392375219519), (Int.ofNat 2539731903250312823712), (Int.ofNat 12562347619361058672), (Int.negSucc 477859712823223789967), (Int.ofNat 42797787086693458272), (Int.negSucc 1283726504027047103), (Int.ofNat 1254714614799360)], [(Int.negSucc 290082109762307882639), (Int.negSucc 902723737033359370247), (Int.ofNat 812614950148612870368), (Int.ofNat 1502552179535282223720), (Int.ofNat 461676928574695003440), (Int.negSucc 2671747938294983512343), (Int.ofNat 1151884380448299144480), (Int.negSucc 65964635182831739303), (Int.ofNat 1830979248364712256), (Int.negSucc 40997681771449727)], [(Int.ofNat 300048061841466862000), (Int.ofNat 802896065036186532392), (Int.negSucc 339773963216405209495), (Int.negSucc 272544908065550752543), (Int.negSucc 3465009488327555408303), (Int.ofNat 3789361651992869437336), (Int.negSucc 697829897337800570279), (Int.negSucc 127285715504582562415), (Int.ofNat 10382758755913419664), (Int.negSucc 244565174541748351)], [(Int.negSucc 234086211693955108559), (Int.negSucc 572299366211284845367), (Int.negSucc 226428323990756200191), (Int.negSucc 305195009893388255671), (Int.ofNat 3317613683568067619312), (Int.negSucc 1362271297947968113399), (Int.negSucc 999415753560556129711), (Int.ofNat 396579594718649778232), (Int.negSucc 14489218478729440063), (Int.negSucc 8096510079304575)], [(Int.ofNat 137365073323750436880), (Int.ofNat 349872561635663471240), (Int.ofNat 518077067972961850072), (Int.ofNat 131674701510767470400), (Int.negSucc 976830573077945821855), (Int.negSucc 1712893894609199270103), (Int.ofNat 1813583745094483351416), (Int.negSucc 237504569513674244287), (Int.negSucc 24661772516079490063), (Int.ofNat 1317660179272246304)], [(Int.negSucc 59894584940662038479), (Int.negSucc 188884670013191136183), (Int.negSucc 479099462992747735383), (Int.ofNat 90530899013069179104), (Int.negSucc 543661398661642237079), (Int.ofNat 2121923799326300859832), (Int.negSucc 747544514020684865351), (Int.negSucc 247921395100201695111), (Int.ofNat 54501594474417700408), (Int.ofNat 49732915341968248)], [(Int.ofNat 18956242253065589680), (Int.ofNat 86625486301308049464), (Int.ofNat 291441774851326111296), (Int.negSucc 50362553620069689839), (Int.ofNat 509611934538983235816), (Int.negSucc 741573278163134544415), (Int.negSucc 480736692553841331319), (Int.ofNat 380824710449452546736), (Int.negSucc 11875243088738540359), (Int.negSucc 2912380968351427055)], [(Int.negSucc 4183574188719466319), (Int.negSucc 31313886807470544631), (Int.negSucc 126705663349198244959), (Int.negSucc 52507761708856166663), (Int.negSucc 88054499327661295359), (Int.negSucc 144324614035457670767), (Int.ofNat 588408705379775608784), (Int.negSucc 104370923581400347839), (Int.negSucc 38216208534207307231), (Int.ofNat 1268426153195434992)], [(Int.ofNat 600122360322851600), (Int.ofNat 8295066953302049288), (Int.ofNat 39636918490117441928), (Int.ofNat 66896682883223345200), (Int.negSucc 47113216657848463151), (Int.ofNat 176939888279436006960), (Int.negSucc 183114681164859392559), (Int.negSucc 92571690012590865935), (Int.ofNat 28408614124049926752), (Int.ofNat 2022294744847099920)], [(Int.negSucc 48792007383707679), (Int.negSucc 1497839958857428671), (Int.negSucc 8688357261509971607), (Int.negSucc 33121090650269122903), (Int.ofNat 19007139622451841592), (Int.negSucc 33255469148190710471), (Int.negSucc 16494970003343493023), (Int.ofNat 74695882265652365856), (Int.ofNat 1106051058282828096), (Int.negSucc 1702553916832601183)], [(Int.ofNat 1594698014036160), (Int.ofNat 165422527637757456), (Int.ofNat 1267682265925398840), (Int.ofNat 9014141956455010992), (Int.ofNat 2392380651841755192), (Int.negSucc 8560682710024950383), (Int.ofNat 21502575401579011104), (Int.negSucc 17373647899384059071), (Int.negSucc 8345761059351635231), (Int.negSucc 63705832692325055)], [(Int.ofNat 0), (Int.negSucc 8540844143092991), (Int.negSucc 112268055748748831), (Int.negSucc 1375280926309800335), (Int.negSucc 2745117586401389567), (Int.ofNat 4148691178527387216), (Int.negSucc 3256883565324562175), (Int.negSucc 580595364761585183), (Int.ofNat 3449996868457279296), (Int.ofNat 479998295704512576)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4746561595295040), (Int.ofNat 102350523134389392), (Int.ofNat 631876080604488480), (Int.negSucc 400999770451209743), (Int.negSucc 478972913500186847), (Int.ofNat 849242239316392896), (Int.negSucc 529570531411179263), (Int.negSucc 178672189287989951)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1997419765420799), (Int.negSucc 55419803219019455), (Int.negSucc 49321610765720639), (Int.ofNat 186528366769286592), (Int.negSucc 123211503389043647), (Int.ofNat 22606678908076032), (Int.ofNat 20815291461841920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 641888820718848), (Int.ofNat 9684212669460288), (Int.negSucc 17050059890654975), (Int.ofNat 6723958400475840)]]

theorem h4n230_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p229).getD 0 []=h4p230.getD 0 [] := by
  decide +kernel

theorem h4n230_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p229).getD 1 []=h4p230.getD 1 [] := by
  decide +kernel

theorem h4n230_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p229).getD 2 []=h4p230.getD 2 [] := by
  decide +kernel

theorem h4n230_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p229).getD 3 []=h4p230.getD 3 [] := by
  decide +kernel

theorem h4n230_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p229).getD 4 []=h4p230.getD 4 [] := by
  decide +kernel

theorem h4n230_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p229).getD 5 []=h4p230.getD 5 [] := by
  decide +kernel

theorem h4n230_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p229).getD 6 []=h4p230.getD 6 [] := by
  decide +kernel

theorem h4n230_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p229).getD 7 []=h4p230.getD 7 [] := by
  decide +kernel

theorem h4n230_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p229).getD 8 []=h4p230.getD 8 [] := by
  decide +kernel

theorem h4n230_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p229).getD 9 []=h4p230.getD 9 [] := by
  decide +kernel

theorem h4n230_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p229).getD 10 []=h4p230.getD 10 [] := by
  decide +kernel

theorem h4n230_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p229).getD 11 []=h4p230.getD 11 [] := by
  decide +kernel

theorem h4n230_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p229).getD 12 []=h4p230.getD 12 [] := by
  decide +kernel

theorem h4n230_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p229).getD 13 []=h4p230.getD 13 [] := by
  decide +kernel

theorem h4n230_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p229).getD 14 []=h4p230.getD 14 [] := by
  decide +kernel

theorem h4n230_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p229).getD 15 []=h4p230.getD 15 [] := by
  decide +kernel

theorem h4n230_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p229).getD 16 []=h4p230.getD 16 [] := by
  decide +kernel

theorem h4n230_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p229).getD 17 []=h4p230.getD 17 [] := by
  decide +kernel

theorem h4n230_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p229).getD 18 []=h4p230.getD 18 [] := by
  decide +kernel

theorem h4n230_arithmetic : BiPoly.mul h4p13 h4p229=h4p230 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p229).getD j.val []=h4p230.getD j.val [] :=
      (fun j => Fin.cases h4n230_arithmetic_row0 (fun j => Fin.cases h4n230_arithmetic_row1 (fun j => Fin.cases h4n230_arithmetic_row2 (fun j => Fin.cases h4n230_arithmetic_row3 (fun j => Fin.cases h4n230_arithmetic_row4 (fun j => Fin.cases h4n230_arithmetic_row5 (fun j => Fin.cases h4n230_arithmetic_row6 (fun j => Fin.cases h4n230_arithmetic_row7 (fun j => Fin.cases h4n230_arithmetic_row8 (fun j => Fin.cases h4n230_arithmetic_row9 (fun j => Fin.cases h4n230_arithmetic_row10 (fun j => Fin.cases h4n230_arithmetic_row11 (fun j => Fin.cases h4n230_arithmetic_row12 (fun j => Fin.cases h4n230_arithmetic_row13 (fun j => Fin.cases h4n230_arithmetic_row14 (fun j => Fin.cases h4n230_arithmetic_row15 (fun j => Fin.cases h4n230_arithmetic_row16 (fun j => Fin.cases h4n230_arithmetic_row17 (fun j => Fin.cases h4n230_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n230 : h4e230.toBi mapPolyEnv=h4p230 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e229.toBi mapPolyEnv)=h4p230
  rw [h4n13, h4n229]
  exact h4n230_arithmetic

#print axioms h4n230_arithmetic
end StackSorting.RationalLift
