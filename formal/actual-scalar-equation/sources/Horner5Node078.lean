import BivariateRowEquality
import Horner5Base
import Horner5Node077
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p78 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 4180984127999), (Int.negSucc 8297899303679), (Int.ofNat 53764174861200), (Int.ofNat 89676894337920), (Int.negSucc 19133701532639), (Int.negSucc 122375990350079), (Int.negSucc 71446484516399)], [(Int.ofNat 0), (Int.ofNat 36386950014720), (Int.ofNat 56667226783104), (Int.negSucc 488859779941847), (Int.negSucc 688532324381639), (Int.ofNat 178662124576080), (Int.ofNat 849826115063280), (Int.ofNat 402302175721992), (Int.negSucc 5011340506919)], [(Int.ofNat 0), (Int.negSucc 142478475949439), (Int.negSucc 173882374221887), (Int.ofNat 1962101326169304), (Int.ofNat 2468249371821168), (Int.negSucc 570249041271839), (Int.negSucc 2617597773140543), (Int.negSucc 1151406239219495), (Int.negSucc 149121695520431), (Int.ofNat 13787418181680)], [(Int.ofNat 0), (Int.ofNat 331086942711360), (Int.ofNat 329507085973536), (Int.negSucc 4627585157180687), (Int.negSucc 5648029830396575), (Int.ofNat 572426097326496), (Int.ofNat 4515410283980400), (Int.ofNat 2372596275726432), (Int.ofNat 782004307672368), (Int.negSucc 77970094021295), (Int.ofNat 2636783154720)], [(Int.ofNat 0), (Int.negSucc 506931708009599), (Int.negSucc 462122241306623), (Int.ofNat 7181971075450692), (Int.ofNat 9433200903884424), (Int.ofNat 1238929081388748), (Int.negSucc 4353188171544431), (Int.negSucc 3913335340078787), (Int.negSucc 1645114308854903), (Int.ofNat 15491443514148), (Int.ofNat 1143663548544), (Int.negSucc 13484433599)], [(Int.ofNat 0), (Int.ofNat 536571367868160), (Int.ofNat 543659347860480), (Int.negSucc 7756528572479843), (Int.negSucc 12180704964026687), (Int.negSucc 5341044185111051), (Int.ofNat 1355675267426184), (Int.ofNat 4562087230079100), (Int.ofNat 1880984115590328), (Int.ofNat 441673113790044), (Int.negSucc 34688277397799), (Int.ofNat 486222137280)], [(Int.ofNat 0), (Int.negSucc 400341682081919), (Int.negSucc 547793302382015), (Int.ofNat 5977497081303948), (Int.ofNat 12294167036481408), (Int.ofNat 9676169565825720), (Int.ofNat 2574448447841112), (Int.negSucc 2563343501477867), (Int.negSucc 1472525493492431), (Int.negSucc 882940369229327), (Int.ofNat 16341930448680), (Int.ofNat 1000606619520)], [(Int.ofNat 0), (Int.ofNat 210414911706240), (Int.ofNat 440495695051968), (Int.negSucc 3284090196056627), (Int.negSucc 9597684940854971), (Int.negSucc 11164727372719487), (Int.negSucc 5313236308823507), (Int.negSucc 1114983530847971), (Int.ofNat 921045150979980), (Int.ofNat 610047750566904), (Int.ofNat 106692086248212), (Int.negSucc 3854604141359)], [(Int.ofNat 0), (Int.negSucc 76308835762559), (Int.negSucc 260428475772095), (Int.ofNat 1242300122453604), (Int.ofNat 5705140953478008), (Int.ofNat 8978126756451600), (Int.ofNat 6124140855361416), (Int.ofNat 3226471702498908), (Int.ofNat 9141082769904), (Int.negSucc 19741362676931), (Int.negSucc 155716569997511), (Int.negSucc 4546301516819)], [(Int.ofNat 0), (Int.ofNat 18181322688000), (Int.ofNat 106126450710144), (Int.negSucc 291303873487235), (Int.negSucc 2543368184153915), (Int.negSucc 5186368754097803), (Int.negSucc 5064633188175743), (Int.negSucc 2914934163049295), (Int.negSucc 951345070101539), (Int.negSucc 202228641554543), (Int.ofNat 38514035979936), (Int.ofNat 9321429864240)], [(Int.ofNat 0), (Int.negSucc 2561558530559), (Int.negSucc 27873834862079), (Int.ofNat 27723980945580), (Int.ofNat 841536145647120), (Int.ofNat 2174241477448188), (Int.ofNat 2991158293098168), (Int.ofNat 1796259099402360), (Int.ofNat 1037159898833952), (Int.ofNat 201870117789804), (Int.ofNat 53840007249120), (Int.ofNat 586451884320)], [(Int.ofNat 0), (Int.ofNat 161749473600), (Int.ofNat 4221320631072), (Int.ofNat 4304591035476), (Int.negSucc 208050074407427), (Int.negSucc 666040723647911), (Int.negSucc 1215456501282515), (Int.negSucc 905741123941295), (Int.negSucc 560218731123167), (Int.negSucc 164484591790463), (Int.negSucc 47296736898335), (Int.negSucc 5483429485919)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 278999161919), (Int.negSucc 1395665180999), (Int.ofNat 39624684661872), (Int.ofNat 154781299759212), (Int.ofNat 322355935240344), (Int.ofNat 359930201673780), (Int.ofNat 194224278430080), (Int.ofNat 86509519492608), (Int.ofNat 20042909951616), (Int.ofNat 2274028311600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 100892107440), (Int.negSucc 5675228520155), (Int.negSucc 30425848445807), (Int.negSucc 50331414333023), (Int.negSucc 99611429326991), (Int.negSucc 50292372477887), (Int.negSucc 27247867820063), (Int.negSucc 5119085192543), (Int.negSucc 231302718719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 449556429456), (Int.ofNat 5148233137476), (Int.ofNat 4282489864224), (Int.ofNat 15829352246016), (Int.ofNat 10573439545728), (Int.ofNat 5295303486720), (Int.ofNat 525585127680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 495009086975), (Int.negSucc 597228883775), (Int.negSucc 600200508095), (Int.negSucc 1862002569887), (Int.negSucc 483221479679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 115447519296), (Int.negSucc 126392974127), (Int.ofNat 188939070720)]]

theorem h5n78_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p77).getD 0 []=h5p78.getD 0 [] := by
  decide +kernel

theorem h5n78_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p77).getD 1 []=h5p78.getD 1 [] := by
  decide +kernel

theorem h5n78_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p77).getD 2 []=h5p78.getD 2 [] := by
  decide +kernel

theorem h5n78_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p77).getD 3 []=h5p78.getD 3 [] := by
  decide +kernel

theorem h5n78_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p77).getD 4 []=h5p78.getD 4 [] := by
  decide +kernel

theorem h5n78_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p77).getD 5 []=h5p78.getD 5 [] := by
  decide +kernel

theorem h5n78_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p77).getD 6 []=h5p78.getD 6 [] := by
  decide +kernel

theorem h5n78_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p77).getD 7 []=h5p78.getD 7 [] := by
  decide +kernel

theorem h5n78_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p77).getD 8 []=h5p78.getD 8 [] := by
  decide +kernel

theorem h5n78_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p77).getD 9 []=h5p78.getD 9 [] := by
  decide +kernel

theorem h5n78_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p77).getD 10 []=h5p78.getD 10 [] := by
  decide +kernel

theorem h5n78_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p77).getD 11 []=h5p78.getD 11 [] := by
  decide +kernel

theorem h5n78_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p77).getD 12 []=h5p78.getD 12 [] := by
  decide +kernel

theorem h5n78_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p77).getD 13 []=h5p78.getD 13 [] := by
  decide +kernel

theorem h5n78_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p77).getD 14 []=h5p78.getD 14 [] := by
  decide +kernel

theorem h5n78_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p77).getD 15 []=h5p78.getD 15 [] := by
  decide +kernel

theorem h5n78_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p77).getD 16 []=h5p78.getD 16 [] := by
  decide +kernel

theorem h5n78_arithmetic : BiPoly.mul h5p5 h5p77=h5p78 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p77).getD j.val []=h5p78.getD j.val [] :=
      (fun j => Fin.cases h5n78_arithmetic_row0 (fun j => Fin.cases h5n78_arithmetic_row1 (fun j => Fin.cases h5n78_arithmetic_row2 (fun j => Fin.cases h5n78_arithmetic_row3 (fun j => Fin.cases h5n78_arithmetic_row4 (fun j => Fin.cases h5n78_arithmetic_row5 (fun j => Fin.cases h5n78_arithmetic_row6 (fun j => Fin.cases h5n78_arithmetic_row7 (fun j => Fin.cases h5n78_arithmetic_row8 (fun j => Fin.cases h5n78_arithmetic_row9 (fun j => Fin.cases h5n78_arithmetic_row10 (fun j => Fin.cases h5n78_arithmetic_row11 (fun j => Fin.cases h5n78_arithmetic_row12 (fun j => Fin.cases h5n78_arithmetic_row13 (fun j => Fin.cases h5n78_arithmetic_row14 (fun j => Fin.cases h5n78_arithmetic_row15 (fun j => Fin.cases h5n78_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n78 : h5e78.toBi mapPolyEnv=h5p78 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e77.toBi mapPolyEnv)=h5p78
  rw [h5n5, h5n77]
  exact h5n78_arithmetic

#print axioms h5n78_arithmetic
end StackSorting.RationalLift
