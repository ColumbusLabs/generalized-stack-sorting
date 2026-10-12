import BivariateRowEquality
import Horner5Base
import Horner5Node267
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p268 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3688299201576960), (Int.ofNat 23208703948880640), (Int.negSucc 140891016945388319), (Int.ofNat 278194134420989280), (Int.negSucc 1482599552995886399), (Int.negSucc 1109459179549477439), (Int.ofNat 3655192074303212640), (Int.ofNat 2122086126146772960), (Int.negSucc 1727175161349434879), (Int.negSucc 1005815142753085439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 31387308136012799), (Int.negSucc 174270549548782079), (Int.ofNat 1175889650543271360), (Int.negSucc 2927597866187143679), (Int.ofNat 15625388342014201440), (Int.ofNat 9027910842843692160), (Int.negSucc 28755328715118155519), (Int.negSucc 11800146342707614079), (Int.ofNat 11005627766245901280), (Int.ofNat 3546698359295301120), (Int.negSucc 558786190418380799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 119473464933527040), (Int.ofNat 590725732378334400), (Int.negSucc 4218915573916489799), (Int.ofNat 11987351293587206760), (Int.negSucc 72512190942223146119), (Int.negSucc 31880048393913640919), (Int.ofNat 96325447741685018280), (Int.ofNat 29650981766285895480), (Int.negSucc 24554151671407392599), (Int.negSucc 4571650042325414279), (Int.ofNat 480823703128402560), (Int.negSucc 77609193113663999)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 267816433591756799), (Int.negSucc 1206760339793272319), (Int.ofNat 8538169012911447480), (Int.negSucc 24656364207033928559), (Int.ofNat 192931346509170202440), (Int.ofNat 73032949273369482720), (Int.negSucc 169238145174789963959), (Int.negSucc 54798229659721319279), (Int.ofNat 14499072591645621240), (Int.ofNat 5522697818203777920), (Int.ofNat 2632185037151622720), (Int.negSucc 177122214983462399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 391337617467214080), (Int.ofNat 1675769145331376160), (Int.negSucc 10735350623299135799), (Int.ofNat 24295288751825823720), (Int.negSucc 325077156033384620159), (Int.negSucc 146132518632444935999), (Int.ofNat 145321090210583618760), (Int.ofNat 100001515508510972040), (Int.ofNat 30453969596541603120), (Int.negSucc 11325008032573140719), (Int.negSucc 4678348234426230239), (Int.ofNat 419897671655788800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 388834217732989439), (Int.negSucc 1680249000799308959), (Int.ofNat 8764629946787732040), (Int.negSucc 60223185672791039), (Int.ofNat 364883887031023872000), (Int.ofNat 270053970782012650080), (Int.ofNat 1878121830942449640), (Int.negSucc 145118113281582029279), (Int.negSucc 66139770510575001359), (Int.ofNat 8520264686684244960), (Int.ofNat 1452969278089980480), (Int.ofNat 505509494260711680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 264490736744607840), (Int.ofNat 1229202920713946400), (Int.negSucc 4925990291972534639), (Int.negSucc 30087230235738489359), (Int.negSucc 283887856806621593039), (Int.negSucc 392092210125996143759), (Int.negSucc 162143948971160866439), (Int.ofNat 111762395064428080680), (Int.ofNat 61693736831834064840), (Int.ofNat 12943011978821047320), (Int.ofNat 1136965788741601440), (Int.negSucc 1202335343238044159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 118960440649391519), (Int.negSucc 611885122243185599), (Int.ofNat 2385507922320718800), (Int.ofNat 39634121003909529600), (Int.ofNat 163804534632184803120), (Int.ofNat 398659116755226974400), (Int.ofNat 239931750733699234680), (Int.ofNat 6273245916323201520), (Int.negSucc 38863414839111095879), (Int.negSucc 26358587660205012959), (Int.negSucc 752787974941807679), (Int.ofNat 115232856677677440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 30539998563510240), (Int.ofNat 146222409898559520), (Int.negSucc 1467913243161301199), (Int.negSucc 27638314005564442799), (Int.negSucc 80384403896937395999), (Int.negSucc 273425968455512217119), (Int.negSucc 233254487375061539399), (Int.negSucc 98884856720035605959), (Int.ofNat 11397818695844810880), (Int.ofNat 14760424277819792640), (Int.ofNat 1875452600585116800), (Int.ofNat 835868019330034560)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 822504293851679), (Int.ofNat 45465944313706560), (Int.ofNat 996054088435900560), (Int.ofNat 12049997363706180960), (Int.ofNat 37955816619021433440), (Int.ofNat 126093800604209444640), (Int.ofNat 169690972195340669880), (Int.ofNat 103822313637091442400), (Int.ofNat 16544433967882745760), (Int.ofNat 584104910564134080), (Int.negSucc 2637659833167162239), (Int.negSucc 353659565876267519)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2516080481053919), (Int.negSucc 55838545961194079), (Int.negSucc 515891991889551239), (Int.negSucc 3520436581964054519), (Int.negSucc 15781801276947773159), (Int.negSucc 40549340269846661399), (Int.negSucc 87533648495762217119), (Int.negSucc 64341881970616389599), (Int.negSucc 26691460260315982559), (Int.negSucc 4774450055450326559), (Int.ofNat 573907414101701760), (Int.negSucc 151127064924917759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 962226918185760), (Int.ofNat 22684764859318080), (Int.ofNat 180549115779595320), (Int.ofNat 777306324409726320), (Int.ofNat 4693101517783473480), (Int.ofNat 10334282271972225120), (Int.ofNat 29429613727623852480), (Int.ofNat 29318922664622496000), (Int.ofNat 17423958244647129120), (Int.ofNat 3671077114918149120), (Int.ofNat 918197800734723840), (Int.ofNat 94995802523128320)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 167487031847519), (Int.negSucc 4729177329883199), (Int.negSucc 41157502685291159), (Int.negSucc 156916127099459159), (Int.negSucc 846181682400239999), (Int.negSucc 2412703683013622399), (Int.negSucc 5948934652397649599), (Int.negSucc 9943734899319906239), (Int.negSucc 6279118823042991359), (Int.negSucc 2147698334841131519), (Int.negSucc 549286670666603519), (Int.negSucc 8063389117463039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 12128088281760), (Int.ofNat 466344873266400), (Int.ofNat 5688367317029160), (Int.ofNat 27614474887963680), (Int.ofNat 83682896626850400), (Int.ofNat 438509940793611840), (Int.ofNat 707172030815060160), (Int.ofNat 2141136814456903680), (Int.ofNat 1473334467235453440), (Int.ofNat 767065615212096000), (Int.ofNat 82067002178711040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 13230641761919), (Int.negSucc 381468582846719), (Int.negSucc 2887644489524639), (Int.negSucc 6141345146189279), (Int.negSucc 38318374594231199), (Int.negSucc 72637598468338559), (Int.negSucc 204290757190195199), (Int.negSucc 278383819444439039), (Int.negSucc 106292282726591999)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3608356844160), (Int.ofNat 96507002413440), (Int.ofNat 573988832007840), (Int.ofNat 24502372577280), (Int.ofNat 7926108953760000), (Int.negSucc 739373345740799), (Int.ofNat 32288669665344000)]]

theorem h5n268_arithmetic_row0 :
    (BiPoly.mul h5p3 h5p267).getD 0 []=h5p268.getD 0 [] := by
  decide +kernel

theorem h5n268_arithmetic_row1 :
    (BiPoly.mul h5p3 h5p267).getD 1 []=h5p268.getD 1 [] := by
  decide +kernel

theorem h5n268_arithmetic_row2 :
    (BiPoly.mul h5p3 h5p267).getD 2 []=h5p268.getD 2 [] := by
  decide +kernel

theorem h5n268_arithmetic_row3 :
    (BiPoly.mul h5p3 h5p267).getD 3 []=h5p268.getD 3 [] := by
  decide +kernel

theorem h5n268_arithmetic_row4 :
    (BiPoly.mul h5p3 h5p267).getD 4 []=h5p268.getD 4 [] := by
  decide +kernel

theorem h5n268_arithmetic_row5 :
    (BiPoly.mul h5p3 h5p267).getD 5 []=h5p268.getD 5 [] := by
  decide +kernel

theorem h5n268_arithmetic_row6 :
    (BiPoly.mul h5p3 h5p267).getD 6 []=h5p268.getD 6 [] := by
  decide +kernel

theorem h5n268_arithmetic_row7 :
    (BiPoly.mul h5p3 h5p267).getD 7 []=h5p268.getD 7 [] := by
  decide +kernel

theorem h5n268_arithmetic_row8 :
    (BiPoly.mul h5p3 h5p267).getD 8 []=h5p268.getD 8 [] := by
  decide +kernel

theorem h5n268_arithmetic_row9 :
    (BiPoly.mul h5p3 h5p267).getD 9 []=h5p268.getD 9 [] := by
  decide +kernel

theorem h5n268_arithmetic_row10 :
    (BiPoly.mul h5p3 h5p267).getD 10 []=h5p268.getD 10 [] := by
  decide +kernel

theorem h5n268_arithmetic_row11 :
    (BiPoly.mul h5p3 h5p267).getD 11 []=h5p268.getD 11 [] := by
  decide +kernel

theorem h5n268_arithmetic_row12 :
    (BiPoly.mul h5p3 h5p267).getD 12 []=h5p268.getD 12 [] := by
  decide +kernel

theorem h5n268_arithmetic_row13 :
    (BiPoly.mul h5p3 h5p267).getD 13 []=h5p268.getD 13 [] := by
  decide +kernel

theorem h5n268_arithmetic_row14 :
    (BiPoly.mul h5p3 h5p267).getD 14 []=h5p268.getD 14 [] := by
  decide +kernel

theorem h5n268_arithmetic_row15 :
    (BiPoly.mul h5p3 h5p267).getD 15 []=h5p268.getD 15 [] := by
  decide +kernel

theorem h5n268_arithmetic : BiPoly.mul h5p3 h5p267=h5p268 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h5p3 h5p267).getD j.val []=h5p268.getD j.val [] :=
      (fun j => Fin.cases h5n268_arithmetic_row0 (fun j => Fin.cases h5n268_arithmetic_row1 (fun j => Fin.cases h5n268_arithmetic_row2 (fun j => Fin.cases h5n268_arithmetic_row3 (fun j => Fin.cases h5n268_arithmetic_row4 (fun j => Fin.cases h5n268_arithmetic_row5 (fun j => Fin.cases h5n268_arithmetic_row6 (fun j => Fin.cases h5n268_arithmetic_row7 (fun j => Fin.cases h5n268_arithmetic_row8 (fun j => Fin.cases h5n268_arithmetic_row9 (fun j => Fin.cases h5n268_arithmetic_row10 (fun j => Fin.cases h5n268_arithmetic_row11 (fun j => Fin.cases h5n268_arithmetic_row12 (fun j => Fin.cases h5n268_arithmetic_row13 (fun j => Fin.cases h5n268_arithmetic_row14 (fun j => Fin.cases h5n268_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n268 : h5e268.toBi mapPolyEnv=h5p268 := by
  change BiPoly.mul (h5e3.toBi mapPolyEnv) (h5e267.toBi mapPolyEnv)=h5p268
  rw [h5n3, h5n267]
  exact h5n268_arithmetic

#print axioms h5n268_arithmetic
end StackSorting.RationalLift
