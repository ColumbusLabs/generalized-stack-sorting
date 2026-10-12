import BivariateRowEquality
import Horner4Base
import Horner4Node150
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p151 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 18282566281907807999), (Int.negSucc 138246775258949124479), (Int.negSucc 183665363597964766079), (Int.ofNat 491204794623808371840), (Int.ofNat 563972174553088632960), (Int.negSucc 679291455050638214399)], [(Int.ofNat 0), (Int.ofNat 168832098214265041920), (Int.ofNat 1285832161228052093184), (Int.ofNat 1797214878730040833152), (Int.negSucc 4174710538646375891711), (Int.negSucc 4831711560673008683903), (Int.ofNat 5996414282506085751552), (Int.negSucc 492072687562749926399)], [(Int.ofNat 0), (Int.negSucc 734944436798020804799), (Int.negSucc 5487410698750529128799), (Int.negSucc 7836309343005973386623), (Int.ofNat 15597828193294745623296), (Int.ofNat 18982142114417641986048), (Int.negSucc 21680169637079831277599), (Int.ofNat 2256284769080820815808), (Int.negSucc 115368257197774485503)], [(Int.ofNat 0), (Int.ofNat 1998209214447453017280), (Int.ofNat 14223174371503955555040), (Int.ofNat 20535447671951394508416), (Int.negSucc 31820329891406676580991), (Int.negSucc 44550379383762782152511), (Int.ofNat 38443846252867097355936), (Int.negSucc 768006255569269957631), (Int.ofNat 28553333552563653504), (Int.negSucc 8475023421060083711)], [(Int.ofNat 0), (Int.negSucc 3777649515677141138879), (Int.negSucc 25054576568464338520991), (Int.negSucc 36963127311095702984831), (Int.ofNat 34157952886435982456256), (Int.ofNat 68546117822055859532160), (Int.negSucc 23110352952103901177567), (Int.negSucc 14961122635582871070335), (Int.ofNat 1471466858492703119616), (Int.negSucc 46146399555774530303), (Int.ofNat 45169726132776960)], [(Int.ofNat 0), (Int.ofNat 5221477975721541887520), (Int.ofNat 31913461193765094327024), (Int.ofNat 49784446624290999989328), (Int.negSucc 6515630812694143370879), (Int.negSucc 68917693990308813486719), (Int.negSucc 37446600529688130388367), (Int.ofNat 38002406400861891455376), (Int.negSucc 2278067861985906438431), (Int.ofNat 63701378125471355904), (Int.negSucc 1475916543772190207)], [(Int.ofNat 0), (Int.negSucc 5400865113146403515999), (Int.negSucc 30654724510090568131055), (Int.negSucc 53443051513497989526239), (Int.negSucc 36305380492527488438591), (Int.ofNat 35876406987728336002464), (Int.ofNat 92408238831648680829360), (Int.negSucc 31447842488014208649695), (Int.negSucc 4034823304770901996127), (Int.ofNat 360572795787628696896), (Int.negSucc 8804346283502940671)], [(Int.ofNat 0), (Int.ofNat 4213551810491191954080), (Int.ofNat 22942044023276703078864), (Int.ofNat 47620531038716569115568), (Int.ofNat 61265460880464780924576), (Int.ofNat 12535434932401540981152), (Int.negSucc 82377774312985467272879), (Int.negSucc 15346524022768604855663), (Int.ofNat 13494010400475719805792), (Int.negSucc 522049076778542289407), (Int.negSucc 291474362854964735)], [(Int.ofNat 0), (Int.negSucc 2472571319827507863839), (Int.negSucc 13715420068924466073839), (Int.negSucc 35636219511321664339775), (Int.negSucc 56657138585542105409567), (Int.negSucc 43814477524526709550559), (Int.ofNat 22183513209244926898128), (Int.ofNat 51203186003475400296384), (Int.negSucc 9810746568679863957407), (Int.negSucc 816670160898160341887), (Int.ofNat 47435766453800866944)], [(Int.ofNat 0), (Int.ofNat 1078102528931916692640), (Int.ofNat 6634231647033190529232), (Int.ofNat 22057870101377530668768), (Int.ofNat 37675894586881203918720), (Int.ofNat 44202687398320273738416), (Int.ofNat 25579869362265978796320), (Int.negSucc 37353586161108524581295), (Int.negSucc 5979398544560238916607), (Int.ofNat 1964742978507503500080), (Int.ofNat 1790384952310856928)], [(Int.ofNat 0), (Int.negSucc 341212360555180614239), (Int.negSucc 2582895835089086733071), (Int.negSucc 10947365289260046517103), (Int.negSucc 20532743218746532106639), (Int.negSucc 27892706110125721517087), (Int.negSucc 32890416746592696206975), (Int.ofNat 2459481733249291355760), (Int.ofNat 12911157877097433442032), (Int.negSucc 584777323485564513983), (Int.negSucc 104845714860651374015)], [(Int.ofNat 0), (Int.ofNat 75304335396950393760), (Int.ofNat 789562968725320984656), (Int.ofNat 4197564834079829000688), (Int.ofNat 9704108425410376819200), (Int.ofNat 13179368834827102135584), (Int.ofNat 18947173863261146842368), (Int.ofNat 13551503271701662031904), (Int.negSucc 5752533497505053623199), (Int.negSucc 1307288494958909570783), (Int.ofNat 45663341515035659712)], [(Int.ofNat 0), (Int.negSucc 10802202485811328799), (Int.negSucc 181717812616870873583), (Int.negSucc 1193804755757858602655), (Int.negSucc 3824874113300106725663), (Int.negSucc 5385116797254874816127), (Int.negSucc 6873958986602178267935), (Int.negSucc 9947730703694405452415), (Int.negSucc 1689311761532831733407), (Int.ofNat 1131914024687540758752), (Int.ofNat 72802610814495597120)], [(Int.ofNat 0), (Int.ofNat 878256132906738240), (Int.ofNat 29595887658153930816), (Int.ofNat 239908556884200851952), (Int.ofNat 1148869050003404042112), (Int.ofNat 1999099800208959318000), (Int.ofNat 1913441218468125809184), (Int.ofNat 3407547567863174260608), (Int.ofNat 2656840607201797424064), (Int.negSucc 52120073410778652479), (Int.negSucc 61291941005973642623)], [(Int.ofNat 0), (Int.negSucc 28704564252650879), (Int.negSucc 3063719190237586847), (Int.negSucc 31837210971854034383), (Int.negSucc 239728327761358590479), (Int.negSucc 607300289926890579647), (Int.negSucc 539333704612744659647), (Int.negSucc 618195484280268645695), (Int.negSucc 1079562536548199982143), (Int.negSucc 303887513102044421375), (Int.negSucc 2293409976923702015)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 153735194575673856), (Int.ofNat 2482030587204500544), (Int.ofNat 31278737267735864544), (Int.ofNat 130200967170113688864), (Int.ofNat 154348759067070743424), (Int.ofNat 63619780815926922816), (Int.ofNat 191318305733319694464), (Int.ofNat 150119795232505733760), (Int.ofNat 17279938645362452736)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 85438108715310719), (Int.negSucc 2098623742564941215), (Int.negSucc 17157012026283751967), (Int.negSucc 32686555059923561855), (Int.negSucc 9629050880676647807), (Int.negSucc 7672386302364993407), (Int.negSucc 28712837352353910911), (Int.negSucc 6432198814367638271)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 35953555777574400), (Int.ofNat 1105417125275073408), (Int.ofNat 3988319034942745344), (Int.ofNat 2406386420661529728), (Int.negSucc 2090827722030001919), (Int.ofNat 1937866179630200832), (Int.ofNat 749350492626309120)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 11553998772939263), (Int.negSucc 208977824369102975), (Int.negSucc 250708402437883775), (Int.ofNat 242062502417130240)]]

theorem h4n151_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p150).getD 0 []=h4p151.getD 0 [] := by
  decide +kernel

theorem h4n151_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p150).getD 1 []=h4p151.getD 1 [] := by
  decide +kernel

theorem h4n151_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p150).getD 2 []=h4p151.getD 2 [] := by
  decide +kernel

theorem h4n151_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p150).getD 3 []=h4p151.getD 3 [] := by
  decide +kernel

theorem h4n151_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p150).getD 4 []=h4p151.getD 4 [] := by
  decide +kernel

theorem h4n151_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p150).getD 5 []=h4p151.getD 5 [] := by
  decide +kernel

theorem h4n151_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p150).getD 6 []=h4p151.getD 6 [] := by
  decide +kernel

theorem h4n151_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p150).getD 7 []=h4p151.getD 7 [] := by
  decide +kernel

theorem h4n151_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p150).getD 8 []=h4p151.getD 8 [] := by
  decide +kernel

theorem h4n151_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p150).getD 9 []=h4p151.getD 9 [] := by
  decide +kernel

theorem h4n151_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p150).getD 10 []=h4p151.getD 10 [] := by
  decide +kernel

theorem h4n151_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p150).getD 11 []=h4p151.getD 11 [] := by
  decide +kernel

theorem h4n151_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p150).getD 12 []=h4p151.getD 12 [] := by
  decide +kernel

theorem h4n151_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p150).getD 13 []=h4p151.getD 13 [] := by
  decide +kernel

theorem h4n151_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p150).getD 14 []=h4p151.getD 14 [] := by
  decide +kernel

theorem h4n151_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p150).getD 15 []=h4p151.getD 15 [] := by
  decide +kernel

theorem h4n151_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p150).getD 16 []=h4p151.getD 16 [] := by
  decide +kernel

theorem h4n151_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p150).getD 17 []=h4p151.getD 17 [] := by
  decide +kernel

theorem h4n151_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p150).getD 18 []=h4p151.getD 18 [] := by
  decide +kernel

theorem h4n151_arithmetic : BiPoly.mul h4p13 h4p150=h4p151 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p150).getD j.val []=h4p151.getD j.val [] :=
      (fun j => Fin.cases h4n151_arithmetic_row0 (fun j => Fin.cases h4n151_arithmetic_row1 (fun j => Fin.cases h4n151_arithmetic_row2 (fun j => Fin.cases h4n151_arithmetic_row3 (fun j => Fin.cases h4n151_arithmetic_row4 (fun j => Fin.cases h4n151_arithmetic_row5 (fun j => Fin.cases h4n151_arithmetic_row6 (fun j => Fin.cases h4n151_arithmetic_row7 (fun j => Fin.cases h4n151_arithmetic_row8 (fun j => Fin.cases h4n151_arithmetic_row9 (fun j => Fin.cases h4n151_arithmetic_row10 (fun j => Fin.cases h4n151_arithmetic_row11 (fun j => Fin.cases h4n151_arithmetic_row12 (fun j => Fin.cases h4n151_arithmetic_row13 (fun j => Fin.cases h4n151_arithmetic_row14 (fun j => Fin.cases h4n151_arithmetic_row15 (fun j => Fin.cases h4n151_arithmetic_row16 (fun j => Fin.cases h4n151_arithmetic_row17 (fun j => Fin.cases h4n151_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n151 : h4e151.toBi mapPolyEnv=h4p151 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e150.toBi mapPolyEnv)=h4p151
  rw [h4n13, h4n150]
  exact h4n151_arithmetic

#print axioms h4n151_arithmetic
end StackSorting.RationalLift
