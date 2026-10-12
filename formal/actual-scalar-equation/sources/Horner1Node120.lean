import BivariateRowEquality
import Horner1Base
import Horner1Node119
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p120 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 32828467968000), (Int.ofNat 76187028574080), (Int.negSucc 960924754941119), (Int.negSucc 2481953430792959), (Int.ofNat 4994551267482240), (Int.ofNat 9548252553778560), (Int.negSucc 10437281882850239)], [(Int.ofNat 0), (Int.negSucc 353663855536319), (Int.negSucc 419604394211423), (Int.ofNat 11098735774917408), (Int.ofNat 19712834192973888), (Int.negSucc 61792307133992063), (Int.negSucc 75360004002869471), (Int.ofNat 107757285797337120), (Int.negSucc 9831684456661247)], [(Int.ofNat 0), (Int.ofNat 1750922569779840), (Int.ofNat 28837067469408), (Int.negSucc 57210835727298383), (Int.negSucc 62895518892928943), (Int.ofNat 320767228813749984), (Int.ofNat 253934161525407744), (Int.negSucc 436546629831309839), (Int.ofNat 42594278343689808), (Int.negSucc 3188613134138111)], [(Int.ofNat 0), (Int.negSucc 5276140846812719), (Int.ofNat 6357009918780072), (Int.ofNat 175251646927258992), (Int.ofNat 89936563558472568), (Int.negSucc 949084128131479919), (Int.negSucc 522609794329385447), (Int.ofNat 880128289000205712), (Int.ofNat 79470416175123528), (Int.negSucc 10677752443143647), (Int.negSucc 333783210000383)], [(Int.ofNat 0), (Int.ofNat 10802282719532400), (Int.negSucc 27008647878337415), (Int.negSucc 357465894789779375), (Int.ofNat 629254795006056), (Int.ofNat 1821242885505906240), (Int.ofNat 925364057389219560), (Int.negSucc 826103337469717007), (Int.negSucc 839783487833172551), (Int.ofNat 117987086985059280), (Int.negSucc 7192826653855103), (Int.ofNat 23063785577472)], [(Int.ofNat 0), (Int.negSucc 15882352383842399), (Int.ofNat 61994886036222000), (Int.ofNat 514874913309471864), (Int.negSucc 232661511966067607), (Int.negSucc 2465185298343703943), (Int.negSucc 1798240371116144063), (Int.negSucc 70464941158183991), (Int.ofNat 2114527534096485768), (Int.negSucc 134662943104142327), (Int.ofNat 7002044308633152), (Int.negSucc 940798154234111), (Int.ofNat 5814014644224)], [(Int.ofNat 0), (Int.ofNat 17277513498582560), (Int.negSucc 94423480073278047), (Int.negSucc 541855522007161535), (Int.ofNat 451451666154841560), (Int.ofNat 2571139104017843568), (Int.ofNat 3257336247757473360), (Int.ofNat 1241908558293301712), (Int.negSucc 2385886452658913079), (Int.negSucc 623286131661209327), (Int.ofNat 103480881359750432), (Int.negSucc 5420728828763775), (Int.negSucc 2212250742527), (Int.ofNat 200450125824)], [(Int.ofNat 0), (Int.negSucc 14113613432152319), (Int.ofNat 102534826939080416), (Int.ofNat 425992821393456568), (Int.negSucc 482831712776515999), (Int.negSucc 2319851080071716431), (Int.negSucc 4517450041823500399), (Int.negSucc 2199379312970879479), (Int.ofNat 690460547161356456), (Int.ofNat 2040589307734005584), (Int.negSucc 205224803645275047), (Int.ofNat 13170537367720960), (Int.negSucc 712360361518463), (Int.ofNat 3541797861888)], [(Int.ofNat 0), (Int.ofNat 8691049975740160), (Int.negSucc 81973923056693855), (Int.negSucc 254847797570099943), (Int.ofNat 342337747438484272), (Int.ofNat 1992677858020537192), (Int.ofNat 4605731080989815648), (Int.ofNat 3156258317802645448), (Int.ofNat 1457869438572729736), (Int.negSucc 2306661239787034375), (Int.negSucc 240097611804220071), (Int.ofNat 44872095977952464), (Int.negSucc 1767731282303999), (Int.negSucc 9670945013503)], [(Int.ofNat 0), (Int.negSucc 4010833492736799), (Int.ofNat 48878713122207408), (Int.ofNat 118744191748181832), (Int.negSucc 178202628912219959), (Int.negSucc 1607016179059069391), (Int.negSucc 3596524105174450567), (Int.negSucc 3920790206508589335), (Int.negSucc 2310523210044129503), (Int.ofNat 569198483257558216), (Int.ofNat 1085725901709093912), (Int.negSucc 109764232086212359), (Int.ofNat 5860903712377376), (Int.negSucc 166690699033727)], [(Int.ofNat 0), (Int.ofNat 1364139994149600), (Int.negSucc 21734476917187439), (Int.negSucc 44668064029783223), (Int.ofNat 80871423910159360), (Int.ofNat 1114691658077910592), (Int.ofNat 2348423643401184624), (Int.ofNat 3732531984513229704), (Int.ofNat 2206883073309118040), (Int.ofNat 1258994380230930304), (Int.negSucc 1120587432330032175), (Int.negSucc 60495222977872335), (Int.ofNat 10820180985810256), (Int.negSucc 242913858361407)], [(Int.ofNat 0), (Int.negSucc 331261744882639), (Int.ofNat 7117622044497112), (Int.ofNat 14172829162280088), (Int.negSucc 39586516907395375), (Int.negSucc 622906407920801799), (Int.negSucc 1409495553948156999), (Int.negSucc 2589419690009429983), (Int.negSucc 2001513555610454359), (Int.negSucc 1537771980547993399), (Int.ofNat 119549556960897376), (Int.ofNat 339427799617628560), (Int.negSucc 26839832023749023), (Int.ofNat 854652052039680)], [(Int.ofNat 0), (Int.ofNat 54245231246480), (Int.negSucc 1668763256205463), (Int.negSucc 3855650848435943), (Int.ofNat 19988673800713032), (Int.ofNat 273941491320783160), (Int.ofNat 788559720123702632), (Int.ofNat 1347829554107269632), (Int.ofNat 1616129142991751712), (Int.ofNat 967860578327146416), (Int.ofNat 635586009316418688), (Int.negSucc 282177745483746479), (Int.negSucc 12993270043734143), (Int.ofNat 1274445132831744)], [(Int.ofNat 0), (Int.negSucc 5357251535039), (Int.ofNat 265320024156544), (Int.ofNat 853615323624512), (Int.negSucc 8299163728545007), (Int.negSucc 94710052068707751), (Int.negSucc 379840283421992167), (Int.negSucc 583678936702093335), (Int.negSucc 958589791518242111), (Int.negSucc 570459083486421839), (Int.negSucc 548349498418215311), (Int.negSucc 30439285108398239), (Int.ofNat 57505455795162144), (Int.negSucc 2419723301020031)], [(Int.ofNat 0), (Int.ofNat 240550499200), (Int.negSucc 25644573899151), (Int.negSucc 136917458453335), (Int.ofNat 2456426761332376), (Int.ofNat 25726652790838720), (Int.ofNat 143915931246428016), (Int.ofNat 239547423595619664), (Int.ofNat 388386606567440784), (Int.ofNat 365645059116198336), (Int.ofNat 221166137988061824), (Int.ofNat 166611324707569248), (Int.negSucc 31485338850956543), (Int.negSucc 1666806580382975)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1137968825760), (Int.ofNat 13437217378080), (Int.negSucc 477367121112839), (Int.negSucc 5369320084403207), (Int.negSucc 40201439631025535), (Int.negSucc 92348495165470031), (Int.negSucc 113707923209775935), (Int.negSucc 178101380553572543), (Int.negSucc 77258135019254975), (Int.negSucc 93855404997839807), (Int.negSucc 13967372193481151), (Int.ofNat 3806356664427264)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 583670616479), (Int.ofNat 54564424353120), (Int.ofNat 805866747488688), (Int.ofNat 7820050218139296), (Int.ofNat 28529672481696144), (Int.ofNat 30647741286554496), (Int.ofNat 52361926474167360), (Int.ofNat 38814504181660800), (Int.ofNat 21276002727417600), (Int.ofNat 19301776032867840), (Int.negSucc 849781001677823)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2781300757535), (Int.negSucc 75776462096687), (Int.negSucc 976826262602447), (Int.negSucc 6040093358251295), (Int.negSucc 8994451115037023), (Int.negSucc 8843863961266559), (Int.negSucc 14799282889768703), (Int.negSucc 3437874540092159), (Int.negSucc 6285374727596927), (Int.negSucc 1153382567625215)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3252713430816), (Int.ofNat 66940856054784), (Int.ofNat 763449689343456), (Int.ofNat 2137642561471104), (Int.ofNat 1262841483651840), (Int.ofNat 2670339509109504), (Int.ofNat 1519665176651904), (Int.ofNat 528397937277696), (Int.ofNat 671535588925440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1666351077119), (Int.negSucc 46253802226751), (Int.negSucc 292582287248831), (Int.negSucc 288785250673919), (Int.negSucc 153022945074047), (Int.negSucc 400961838306815), (Int.ofNat 18755202205440), (Int.negSucc 102027098188799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 648118744704), (Int.ofNat 16958848538880), (Int.ofNat 45179231379840), (Int.ofNat 3162140011008), (Int.ofNat 27470462135040), (Int.ofNat 7557562828800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 135652506623), (Int.negSucc 2335095101951), (Int.negSucc 1133634424319)]]

theorem h1n120_arithmetic_row0 :
    (BiPoly.mul h1p4 h1p119).getD 0 []=h1p120.getD 0 [] := by
  decide +kernel

theorem h1n120_arithmetic_row1 :
    (BiPoly.mul h1p4 h1p119).getD 1 []=h1p120.getD 1 [] := by
  decide +kernel

theorem h1n120_arithmetic_row2 :
    (BiPoly.mul h1p4 h1p119).getD 2 []=h1p120.getD 2 [] := by
  decide +kernel

theorem h1n120_arithmetic_row3 :
    (BiPoly.mul h1p4 h1p119).getD 3 []=h1p120.getD 3 [] := by
  decide +kernel

theorem h1n120_arithmetic_row4 :
    (BiPoly.mul h1p4 h1p119).getD 4 []=h1p120.getD 4 [] := by
  decide +kernel

theorem h1n120_arithmetic_row5 :
    (BiPoly.mul h1p4 h1p119).getD 5 []=h1p120.getD 5 [] := by
  decide +kernel

theorem h1n120_arithmetic_row6 :
    (BiPoly.mul h1p4 h1p119).getD 6 []=h1p120.getD 6 [] := by
  decide +kernel

theorem h1n120_arithmetic_row7 :
    (BiPoly.mul h1p4 h1p119).getD 7 []=h1p120.getD 7 [] := by
  decide +kernel

theorem h1n120_arithmetic_row8 :
    (BiPoly.mul h1p4 h1p119).getD 8 []=h1p120.getD 8 [] := by
  decide +kernel

theorem h1n120_arithmetic_row9 :
    (BiPoly.mul h1p4 h1p119).getD 9 []=h1p120.getD 9 [] := by
  decide +kernel

theorem h1n120_arithmetic_row10 :
    (BiPoly.mul h1p4 h1p119).getD 10 []=h1p120.getD 10 [] := by
  decide +kernel

theorem h1n120_arithmetic_row11 :
    (BiPoly.mul h1p4 h1p119).getD 11 []=h1p120.getD 11 [] := by
  decide +kernel

theorem h1n120_arithmetic_row12 :
    (BiPoly.mul h1p4 h1p119).getD 12 []=h1p120.getD 12 [] := by
  decide +kernel

theorem h1n120_arithmetic_row13 :
    (BiPoly.mul h1p4 h1p119).getD 13 []=h1p120.getD 13 [] := by
  decide +kernel

theorem h1n120_arithmetic_row14 :
    (BiPoly.mul h1p4 h1p119).getD 14 []=h1p120.getD 14 [] := by
  decide +kernel

theorem h1n120_arithmetic_row15 :
    (BiPoly.mul h1p4 h1p119).getD 15 []=h1p120.getD 15 [] := by
  decide +kernel

theorem h1n120_arithmetic_row16 :
    (BiPoly.mul h1p4 h1p119).getD 16 []=h1p120.getD 16 [] := by
  decide +kernel

theorem h1n120_arithmetic_row17 :
    (BiPoly.mul h1p4 h1p119).getD 17 []=h1p120.getD 17 [] := by
  decide +kernel

theorem h1n120_arithmetic_row18 :
    (BiPoly.mul h1p4 h1p119).getD 18 []=h1p120.getD 18 [] := by
  decide +kernel

theorem h1n120_arithmetic_row19 :
    (BiPoly.mul h1p4 h1p119).getD 19 []=h1p120.getD 19 [] := by
  decide +kernel

theorem h1n120_arithmetic_row20 :
    (BiPoly.mul h1p4 h1p119).getD 20 []=h1p120.getD 20 [] := by
  decide +kernel

theorem h1n120_arithmetic_row21 :
    (BiPoly.mul h1p4 h1p119).getD 21 []=h1p120.getD 21 [] := by
  decide +kernel

theorem h1n120_arithmetic : BiPoly.mul h1p4 h1p119=h1p120 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p4 h1p119).getD j.val []=h1p120.getD j.val [] :=
      (fun j => Fin.cases h1n120_arithmetic_row0 (fun j => Fin.cases h1n120_arithmetic_row1 (fun j => Fin.cases h1n120_arithmetic_row2 (fun j => Fin.cases h1n120_arithmetic_row3 (fun j => Fin.cases h1n120_arithmetic_row4 (fun j => Fin.cases h1n120_arithmetic_row5 (fun j => Fin.cases h1n120_arithmetic_row6 (fun j => Fin.cases h1n120_arithmetic_row7 (fun j => Fin.cases h1n120_arithmetic_row8 (fun j => Fin.cases h1n120_arithmetic_row9 (fun j => Fin.cases h1n120_arithmetic_row10 (fun j => Fin.cases h1n120_arithmetic_row11 (fun j => Fin.cases h1n120_arithmetic_row12 (fun j => Fin.cases h1n120_arithmetic_row13 (fun j => Fin.cases h1n120_arithmetic_row14 (fun j => Fin.cases h1n120_arithmetic_row15 (fun j => Fin.cases h1n120_arithmetic_row16 (fun j => Fin.cases h1n120_arithmetic_row17 (fun j => Fin.cases h1n120_arithmetic_row18 (fun j => Fin.cases h1n120_arithmetic_row19 (fun j => Fin.cases h1n120_arithmetic_row20 (fun j => Fin.cases h1n120_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n120 : h1e120.toBi mapPolyEnv=h1p120 := by
  change BiPoly.mul (h1e4.toBi mapPolyEnv) (h1e119.toBi mapPolyEnv)=h1p120
  rw [h1n4, h1n119]
  exact h1n120_arithmetic

#print axioms h1n120_arithmetic
end StackSorting.RationalLift
