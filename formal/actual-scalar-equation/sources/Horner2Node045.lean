import BivariateRowEquality
import Horner2Base
import Horner2Node044
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p45 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 180049400870876352), (Int.ofNat 1796798466043274808), (Int.negSucc 4777728286780023047), (Int.negSucc 33072836372195045903), (Int.ofNat 23758653500713272240), (Int.ofNat 55519473996826326936), (Int.negSucc 15898055909714688743), (Int.negSucc 20980517385585119039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2167896842948460383), (Int.negSucc 20697475379696285687), (Int.ofNat 61558467016327051248), (Int.ofNat 390163579958946994128), (Int.negSucc 316588358215252044575), (Int.negSucc 515965085524340657207), (Int.ofNat 189467440577890019280), (Int.ofNat 149907616304833778976), (Int.negSucc 7299519676678749311)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 12323280187274548752), (Int.ofNat 111008569688009484858), (Int.negSucc 379822924214164714265), (Int.negSucc 2110489261812839405429), (Int.ofNat 1844879590227417073830), (Int.ofNat 2099892512049679809630), (Int.negSucc 769923081401497370765), (Int.negSucc 463860896533464469553), (Int.negSucc 22088977993582407629), (Int.ofNat 3639947711343874128)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 43905036974021380367), (Int.negSucc 366495827889088086317), (Int.ofNat 1477886270038123991112), (Int.ofNat 6889328674306350935778), (Int.negSucc 6034110650132463309275), (Int.negSucc 4947753756841445789909), (Int.ofNat 1002570346361087035488), (Int.ofNat 973260478725929481582), (Int.ofNat 315737381262885396228), (Int.negSucc 44291388292956760427), (Int.ofNat 1898946694623936672)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 109602953044901656236), (Int.ofNat 829423254258937165866), (Int.negSucc 4019845445764495889537), (Int.negSucc 15099296294892967313567), (Int.ofNat 11603360200329179979384), (Int.ofNat 8002798250277306121950), (Int.ofNat 2017075740618715116798), (Int.negSucc 1914908508679726721627), (Int.negSucc 951713002312801763327), (Int.ofNat 89892028784342573196), (Int.negSucc 5564585932911355559), (Int.ofNat 211123821363533760)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 202729985122833002155), (Int.negSucc 1355486939737418476178), (Int.ofNat 8030219662683710170444), (Int.ofNat 23557285840645524072496), (Int.negSucc 11252175577596214415831), (Int.negSucc 11251364239994267618615), (Int.negSucc 9618597858336489271843), (Int.ofNat 2772790675607964360108), (Int.ofNat 1330658945772452816836), (Int.ofNat 158884100695311752663), (Int.negSucc 23918868174188010503), (Int.ofNat 615407704657689328), (Int.negSucc 1099931241833599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 286127611512434263536), (Int.ofNat 1639972455545951046777), (Int.negSucc 12093134188528239691737), (Int.negSucc 27472377254375856215099), (Int.negSucc 2540998615441757328891), (Int.ofNat 15828491479943081011724), (Int.ofNat 16004250374518820106002), (Int.negSucc 191442923993249197161), (Int.negSucc 1178360584558948850701), (Int.negSucc 775802809333905212046), (Int.ofNat 77548602232753400866), (Int.negSucc 3154801913082292511), (Int.ofNat 37717868394215680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 312260473066501637981), (Int.negSucc 1477530978381748647112), (Int.ofNat 13921549751554860167042), (Int.ofNat 25674190095641576864312), (Int.ofNat 24787498589019878698112), (Int.negSucc 17350689412169669157003), (Int.negSucc 14464933222854192377607), (Int.negSucc 7738804936574140946021), (Int.ofNat 1068221365356953977378), (Int.ofNat 946224221449410372727), (Int.ofNat 25268574624964242926), (Int.negSucc 5765552326772547599), (Int.ofNat 154155013048081920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 263744839764940510250), (Int.ofNat 975222425702861112979), (Int.negSucc 12329864493069026000374), (Int.negSucc 21466188321385108736893), (Int.negSucc 38964286781683211162361), (Int.ofNat 6869735282377084580730), (Int.ofNat 8368282648583856329886), (Int.ofNat 13991482161060768031842), (Int.ofNat 32875533097216668832), (Int.negSucc 267716809191969506678), (Int.negSucc 291537984240208616328), (Int.ofNat 18671592933294846756), (Int.negSucc 257919128712920415)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 170339598072809231635), (Int.negSucc 441466043650451286887), (Int.ofNat 8414355813878673767696), (Int.ofNat 17646826951123742481999), (Int.ofNat 35879266909125380295188), (Int.ofNat 13399904517330912573370), (Int.negSucc 4140758102373340251887), (Int.negSucc 10467255454198188451411), (Int.negSucc 3372855515386423702407), (Int.negSucc 279379872199759375863), (Int.ofNat 301160672752146442052), (Int.ofNat 8210376971231298909), (Int.negSucc 1141056195159996567)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 81446533726212879648), (Int.ofNat 100455443442427393930), (Int.negSucc 4425454383825042275790), (Int.negSucc 13832152416635582748315), (Int.negSucc 23097556390063227743567), (Int.negSucc 27119552947877139681157), (Int.negSucc 239630805064621494529), (Int.ofNat 1696838937267695785962), (Int.ofNat 5610437721023710694786), (Int.ofNat 419909720720949160130), (Int.ofNat 28390100990787969931), (Int.negSucc 49140276795587540351), (Int.ofNat 774597082725510168)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 26566558763632817331), (Int.ofNat 30332918902141991536), (Int.ofNat 1809764763507782291734), (Int.ofNat 9219633403130318793255), (Int.ofNat 12272505507711050964672), (Int.ofNat 24632251929148492874494), (Int.ofNat 7053203236076524721324), (Int.ofNat 2956609327648500134244), (Int.negSucc 3322569676677348883219), (Int.negSucc 814772233103175415015), (Int.negSucc 213710668602117041053), (Int.ofNat 27640164034423989167), (Int.ofNat 2531788563340854936)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4321413461590048648), (Int.negSucc 45141862835769594143), (Int.negSucc 603446424812065953159), (Int.negSucc 4775313564539657390767), (Int.negSucc 6679850489243287863009), (Int.negSucc 13610905691014283851367), (Int.negSucc 11015128124581962329299), (Int.negSucc 3162395490824402908739), (Int.negSucc 491851625847660430559), (Int.ofNat 959634674537965408964), (Int.ofNat 144250216918200723876), (Int.ofNat 22784146623417655638), (Int.negSucc 2025701110726150211)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 722769208356276228), (Int.ofNat 27036655532435645797), (Int.ofNat 188124618371561142428), (Int.ofNat 1830087203707552815614), (Int.ofNat 3787745483491332241108), (Int.ofNat 5117995028151057041058), (Int.ofNat 8699189221886724659796), (Int.ofNat 2878717001867039742474), (Int.ofNat 1810841093813955776400), (Int.negSucc 321705968492591018351), (Int.negSucc 76734020298419515151), (Int.negSucc 29253072880004724485), (Int.negSucc 1589910531217838855)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 669219115350762439), (Int.negSucc 11238928380805700122), (Int.negSucc 64292140202509849535), (Int.negSucc 507355222483355611195), (Int.negSucc 1816029209447096020687), (Int.negSucc 1686752384668736257365), (Int.negSucc 3996562829700460746743), (Int.negSucc 2543144787613049600573), (Int.negSucc 1206916412287740225569), (Int.negSucc 295194191486915804921), (Int.ofNat 34048255725093155778), (Int.ofNat 9103042756588631616), (Int.ofNat 1908853659719040600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 198869951947648306), (Int.ofNat 3496399424034659871), (Int.ofNat 22580773043059962078), (Int.ofNat 104800853069406822974), (Int.ofNat 627567989411580004608), (Int.ofNat 700350904461620480634), (Int.ofNat 1088618589456044098716), (Int.ofNat 1531508339313029520432), (Int.ofNat 583355870005685368428), (Int.ofNat 338251667188879908630), (Int.ofNat 21908116878385223736), (Int.ofNat 1989462403095927660), (Int.negSucc 110544085504794527)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 32214831116185709), (Int.negSucc 803175160908276404), (Int.negSucc 6644795170540203494), (Int.negSucc 19680788324449696517), (Int.negSucc 143664234068112956981), (Int.negSucc 299642926822893492695), (Int.negSucc 194515665532405787303), (Int.negSucc 541514633447565193697), (Int.negSucc 291707095030460276597), (Int.negSucc 154147517915603039783), (Int.negSucc 38878376101757824535), (Int.negSucc 3958356082741185671), (Int.negSucc 468265537194114959)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2754276964143372), (Int.ofNat 128480786105525694), (Int.ofNat 1434533338457570808), (Int.ofNat 4479635868703152291), (Int.ofNat 20308420591400984688), (Int.ofNat 90579816978918903432), (Int.ofNat 48132167663201926968), (Int.ofNat 99691283318903395038), (Int.ofNat 118947851664787187712), (Int.ofNat 47068900739769296772), (Int.ofNat 20916485629581484368), (Int.ofNat 2847864267335991960), (Int.ofNat 197229336695682912)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 91746279373319), (Int.negSucc 12765219384533057), (Int.negSucc 210343355347088060), (Int.negSucc 1014226248802158197), (Int.negSucc 1808120413439314577), (Int.negSucc 16296490463470122005), (Int.negSucc 19306243667203359713), (Int.negSucc 6281536002739593407), (Int.negSucc 28799745960131560583), (Int.negSucc 13144777908388693343), (Int.negSucc 5913264600574427159), (Int.negSucc 1100901090423837887), (Int.negSucc 28895931713088287)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 594886323583800), (Int.ofNat 19042906822568802), (Int.ofNat 156586427661644145), (Int.ofNat 216254669084300772), (Int.ofNat 1420836063417764874), (Int.ofNat 5105040798368417400), (Int.negSucc 16014056459167259), (Int.ofNat 3024224355090402144), (Int.ofNat 3005004640545694512), (Int.ofNat 1103811778313512128), (Int.ofNat 203268318817684032), (Int.ofNat 1395865646931456)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 829111166994383), (Int.negSucc 13048513598275739), (Int.negSucc 43448340861496781), (Int.negSucc 14872715782868663), (Int.negSucc 668872854206322263), (Int.negSucc 274370777053609319), (Int.ofNat 105757847830760832), (Int.negSucc 385015999087325375), (Int.negSucc 156583418342943743), (Int.negSucc 13565626889665535)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 411704628020640), (Int.ofNat 4342875647301720), (Int.negSucc 1656297242264915), (Int.ofNat 26436913443732528), (Int.ofNat 81607589348872824), (Int.negSucc 53105847678276767), (Int.ofNat 17784120155848128), (Int.ofNat 12169761242734080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 66307741459775), (Int.negSucc 567049824454319), (Int.ofNat 1666108908123624), (Int.negSucc 7077569416796159), (Int.ofNat 3931194933776160)]]

theorem h2n45_arithmetic_row0 :
    (BiPoly.mul h2p4 h2p44).getD 0 []=h2p45.getD 0 [] := by
  decide +kernel

theorem h2n45_arithmetic_row1 :
    (BiPoly.mul h2p4 h2p44).getD 1 []=h2p45.getD 1 [] := by
  decide +kernel

theorem h2n45_arithmetic_row2 :
    (BiPoly.mul h2p4 h2p44).getD 2 []=h2p45.getD 2 [] := by
  decide +kernel

theorem h2n45_arithmetic_row3 :
    (BiPoly.mul h2p4 h2p44).getD 3 []=h2p45.getD 3 [] := by
  decide +kernel

theorem h2n45_arithmetic_row4 :
    (BiPoly.mul h2p4 h2p44).getD 4 []=h2p45.getD 4 [] := by
  decide +kernel

theorem h2n45_arithmetic_row5 :
    (BiPoly.mul h2p4 h2p44).getD 5 []=h2p45.getD 5 [] := by
  decide +kernel

theorem h2n45_arithmetic_row6 :
    (BiPoly.mul h2p4 h2p44).getD 6 []=h2p45.getD 6 [] := by
  decide +kernel

theorem h2n45_arithmetic_row7 :
    (BiPoly.mul h2p4 h2p44).getD 7 []=h2p45.getD 7 [] := by
  decide +kernel

theorem h2n45_arithmetic_row8 :
    (BiPoly.mul h2p4 h2p44).getD 8 []=h2p45.getD 8 [] := by
  decide +kernel

theorem h2n45_arithmetic_row9 :
    (BiPoly.mul h2p4 h2p44).getD 9 []=h2p45.getD 9 [] := by
  decide +kernel

theorem h2n45_arithmetic_row10 :
    (BiPoly.mul h2p4 h2p44).getD 10 []=h2p45.getD 10 [] := by
  decide +kernel

theorem h2n45_arithmetic_row11 :
    (BiPoly.mul h2p4 h2p44).getD 11 []=h2p45.getD 11 [] := by
  decide +kernel

theorem h2n45_arithmetic_row12 :
    (BiPoly.mul h2p4 h2p44).getD 12 []=h2p45.getD 12 [] := by
  decide +kernel

theorem h2n45_arithmetic_row13 :
    (BiPoly.mul h2p4 h2p44).getD 13 []=h2p45.getD 13 [] := by
  decide +kernel

theorem h2n45_arithmetic_row14 :
    (BiPoly.mul h2p4 h2p44).getD 14 []=h2p45.getD 14 [] := by
  decide +kernel

theorem h2n45_arithmetic_row15 :
    (BiPoly.mul h2p4 h2p44).getD 15 []=h2p45.getD 15 [] := by
  decide +kernel

theorem h2n45_arithmetic_row16 :
    (BiPoly.mul h2p4 h2p44).getD 16 []=h2p45.getD 16 [] := by
  decide +kernel

theorem h2n45_arithmetic_row17 :
    (BiPoly.mul h2p4 h2p44).getD 17 []=h2p45.getD 17 [] := by
  decide +kernel

theorem h2n45_arithmetic_row18 :
    (BiPoly.mul h2p4 h2p44).getD 18 []=h2p45.getD 18 [] := by
  decide +kernel

theorem h2n45_arithmetic_row19 :
    (BiPoly.mul h2p4 h2p44).getD 19 []=h2p45.getD 19 [] := by
  decide +kernel

theorem h2n45_arithmetic_row20 :
    (BiPoly.mul h2p4 h2p44).getD 20 []=h2p45.getD 20 [] := by
  decide +kernel

theorem h2n45_arithmetic_row21 :
    (BiPoly.mul h2p4 h2p44).getD 21 []=h2p45.getD 21 [] := by
  decide +kernel

theorem h2n45_arithmetic_row22 :
    (BiPoly.mul h2p4 h2p44).getD 22 []=h2p45.getD 22 [] := by
  decide +kernel

theorem h2n45_arithmetic : BiPoly.mul h2p4 h2p44=h2p45 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<23 at hk
    have hf : ∀ j : Fin 23, (BiPoly.mul h2p4 h2p44).getD j.val []=h2p45.getD j.val [] :=
      (fun j => Fin.cases h2n45_arithmetic_row0 (fun j => Fin.cases h2n45_arithmetic_row1 (fun j => Fin.cases h2n45_arithmetic_row2 (fun j => Fin.cases h2n45_arithmetic_row3 (fun j => Fin.cases h2n45_arithmetic_row4 (fun j => Fin.cases h2n45_arithmetic_row5 (fun j => Fin.cases h2n45_arithmetic_row6 (fun j => Fin.cases h2n45_arithmetic_row7 (fun j => Fin.cases h2n45_arithmetic_row8 (fun j => Fin.cases h2n45_arithmetic_row9 (fun j => Fin.cases h2n45_arithmetic_row10 (fun j => Fin.cases h2n45_arithmetic_row11 (fun j => Fin.cases h2n45_arithmetic_row12 (fun j => Fin.cases h2n45_arithmetic_row13 (fun j => Fin.cases h2n45_arithmetic_row14 (fun j => Fin.cases h2n45_arithmetic_row15 (fun j => Fin.cases h2n45_arithmetic_row16 (fun j => Fin.cases h2n45_arithmetic_row17 (fun j => Fin.cases h2n45_arithmetic_row18 (fun j => Fin.cases h2n45_arithmetic_row19 (fun j => Fin.cases h2n45_arithmetic_row20 (fun j => Fin.cases h2n45_arithmetic_row21 (fun j => Fin.cases h2n45_arithmetic_row22 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n45 : h2e45.toBi mapPolyEnv=h2p45 := by
  change BiPoly.mul (h2e4.toBi mapPolyEnv) (h2e44.toBi mapPolyEnv)=h2p45
  rw [h2n4, h2n44]
  exact h2n45_arithmetic

#print axioms h2n45_arithmetic
end StackSorting.RationalLift
