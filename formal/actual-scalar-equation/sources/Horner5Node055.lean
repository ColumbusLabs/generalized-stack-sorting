import BivariateRowEquality
import Horner5Base
import Horner5Node054
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p55 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 160043911885223423), (Int.negSucc 1597154192038466495), (Int.ofNat 4246869588248909376), (Int.ofNat 29398076775284485248), (Int.negSucc 21118803111745130879), (Int.negSucc 49350643552734512831), (Int.ofNat 14131605253079723328), (Int.ofNat 18649348787186772480)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1550619845409309696), (Int.ofNat 14739290461643497056), (Int.negSucc 43884996719662359359), (Int.negSucc 281438437709394125855), (Int.ofNat 218409477403069874304), (Int.ofNat 374798761862249636640), (Int.negSucc 141551845262536398911), (Int.negSucc 101707814361326709599), (Int.ofNat 10287403354437675264)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7026627869698670207), (Int.negSucc 62079262187067024479), (Int.ofNat 220092084854106433344), (Int.ofNat 1198988054477460003168), (Int.negSucc 980506263036916138751), (Int.negSucc 1223233634928521399327), (Int.ofNat 498078512055303802560), (Int.ofNat 211364432602613001504), (Int.negSucc 20996440403921322623), (Int.ofNat 1392700701117496320)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 19718526021821616960), (Int.ofNat 156592551961206102816), (Int.negSucc 695580082954451671967), (Int.negSucc 2958386771646207805247), (Int.ofNat 2361063953601731156832), (Int.ofNat 2222582902482017422368), (Int.negSucc 657116512905349387871), (Int.negSucc 215425361145117739391), (Int.negSucc 45622178498297681567), (Int.ofNat 3231813497038598016), (Int.negSucc 7199549946547199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 38109347032134413375), (Int.negSucc 260481171439831322159), (Int.ofNat 1510431210980327002320), (Int.ofNat 4640910657751694203632), (Int.negSucc 2939668339362996257711), (Int.negSucc 2588162501372948763983), (Int.negSucc 338501644121710917071), (Int.ofNat 200425066833989995920), (Int.ofNat 176548507160592770352), (Int.negSucc 11759647920940684223), (Int.ofNat 248516854477263360)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 53189286646401160704), (Int.ofNat 295337680246450360944), (Int.negSucc 2333323417209088170527), (Int.negSucc 4840727697641687598863), (Int.ofNat 752495301958153259808), (Int.ofNat 2383368089787634338000), (Int.ofNat 2125970372131766818272), (Int.negSucc 248965336665386391311), (Int.negSucc 160074408532886109215), (Int.negSucc 7911357514247337119), (Int.ofNat 915226768755959040)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 54521599363994526047), (Int.negSucc 225019431847515786047), (Int.ofNat 2599387200337876029072), (Int.ofNat 3555746594073074138976), (Int.ofNat 3293968902898129233408), (Int.negSucc 1937493344887806597263), (Int.negSucc 2657690599643804570543), (Int.negSucc 84818971488767073695), (Int.negSucc 12126604535260762175), (Int.ofNat 43471674822774904272), (Int.negSucc 602544321317930111)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 40801937032269474912), (Int.ofNat 103440263117753726784), (Int.negSucc 2090549903370645929615), (Int.negSucc 2222365514197126627439), (Int.negSucc 5489090437304544008687), (Int.ofNat 566581190101003483776), (Int.ofNat 1407746557348937869680), (Int.ofNat 777640005481236169680), (Int.ofNat 89861719591429476912), (Int.negSucc 27766325068335011519), (Int.negSucc 2792582829039148415)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 21557290527569399327), (Int.negSucc 12186342591854465375), (Int.ofNat 1202092818749685879552), (Int.ofNat 1638245965651251870672), (Int.ofNat 4291062909386983170912), (Int.ofNat 1590242856768119855232), (Int.negSucc 57178605298819419215), (Int.negSucc 873704325109590568799), (Int.negSucc 86761016536297978799), (Int.negSucc 19711947417426877103), (Int.ofNat 1833670890446268672)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7308150343558105824), (Int.negSucc 20328810159782940191), (Int.negSucc 484926461549955384191), (Int.negSucc 1324608030257386403663), (Int.negSucc 1950082145221236823439), (Int.negSucc 2649766805199748481903), (Int.negSucc 533729911013168144831), (Int.ofNat 251177451684842193984), (Int.ofNat 105758318892942143856), (Int.ofNat 29695756417966251072), (Int.ofNat 2177297906459617728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1046291103406117727), (Int.ofNat 17750516770963447200), (Int.ofNat 136071154447385573664), (Int.ofNat 839000179927540155600), (Int.ofNat 630547841869081322976), (Int.ofNat 1905953664122945232336), (Int.ofNat 720919680361001503920), (Int.ofNat 216938005299855420048), (Int.negSucc 63454996712720500415), (Int.negSucc 11325910375905145919), (Int.negSucc 1967385320149291775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 307352038871099807), (Int.negSucc 8351462763777032063), (Int.negSucc 30303459503002082015), (Int.negSucc 355183953442678048463), (Int.negSucc 279525196411848224783), (Int.negSucc 719040219629491746719), (Int.negSucc 625609992187873223567), (Int.negSucc 243523584623742380927), (Int.negSucc 18809476325626243391), (Int.negSucc 1666768882919379839), (Int.negSucc 177468390284488703)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 202418397652828896), (Int.ofNat 2760169033301190480), (Int.ofNat 8818525124604188208), (Int.ofNat 92947551347191318848), (Int.ofNat 167537204867395731312), (Int.ofNat 133492692191217570864), (Int.ofNat 322781045374509174144), (Int.ofNat 134535394056293090496), (Int.ofNat 42057521198727048000), (Int.ofNat 5003465388488529984), (Int.ofNat 558590006257814016)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 47396908515933791), (Int.negSucc 691858160137183535), (Int.negSucc 3400453092179503583), (Int.negSucc 13234489284398421887), (Int.negSucc 69556020650192469743), (Int.negSucc 14361562856327822783), (Int.negSucc 87428399681686747967), (Int.negSucc 56666501342423770751), (Int.negSucc 22126137330012322751), (Int.negSucc 3312544625870095871), (Int.negSucc 160443594260179199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5213722258729152), (Int.ofNat 130715275535410176), (Int.ofNat 982408787982175824), (Int.ofNat 741379638963524400), (Int.ofNat 16202000190383764416), (Int.ofNat 7109511580981688256), (Int.ofNat 8286487092701479296), (Int.ofNat 16590187336896342144), (Int.ofNat 6220825895713830912), (Int.ofNat 990933772283859456), (Int.ofNat 11166925175451648)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 203253295842431), (Int.negSucc 16776903825021023), (Int.negSucc 167925250443217967), (Int.negSucc 63754986324978431), (Int.negSucc 1751499130760368703), (Int.negSucc 3354481905044006015), (Int.ofNat 1234384168547650176), (Int.negSucc 2584112293390468607), (Int.negSucc 1090403863507095551), (Int.negSucc 108525015117324287)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1083378975505920), (Int.ofNat 14957241143806080), (Int.ofNat 34725921339943872), (Int.negSucc 2208887568363455), (Int.ofNat 689532953692905792), (Int.negSucc 372430848975865343), (Int.ofNat 142272961246785024), (Int.ofNat 97358089941872640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 530461931678207), (Int.negSucc 4536398595634559), (Int.ofNat 13328871264988992), (Int.negSucc 56620555334369279), (Int.ofNat 31449559470209280)]]

theorem h5n55_arithmetic_row0 :
    (BiPoly.mul h5p22 h5p54).getD 0 []=h5p55.getD 0 [] := by
  decide +kernel

theorem h5n55_arithmetic_row1 :
    (BiPoly.mul h5p22 h5p54).getD 1 []=h5p55.getD 1 [] := by
  decide +kernel

theorem h5n55_arithmetic_row2 :
    (BiPoly.mul h5p22 h5p54).getD 2 []=h5p55.getD 2 [] := by
  decide +kernel

theorem h5n55_arithmetic_row3 :
    (BiPoly.mul h5p22 h5p54).getD 3 []=h5p55.getD 3 [] := by
  decide +kernel

theorem h5n55_arithmetic_row4 :
    (BiPoly.mul h5p22 h5p54).getD 4 []=h5p55.getD 4 [] := by
  decide +kernel

theorem h5n55_arithmetic_row5 :
    (BiPoly.mul h5p22 h5p54).getD 5 []=h5p55.getD 5 [] := by
  decide +kernel

theorem h5n55_arithmetic_row6 :
    (BiPoly.mul h5p22 h5p54).getD 6 []=h5p55.getD 6 [] := by
  decide +kernel

theorem h5n55_arithmetic_row7 :
    (BiPoly.mul h5p22 h5p54).getD 7 []=h5p55.getD 7 [] := by
  decide +kernel

theorem h5n55_arithmetic_row8 :
    (BiPoly.mul h5p22 h5p54).getD 8 []=h5p55.getD 8 [] := by
  decide +kernel

theorem h5n55_arithmetic_row9 :
    (BiPoly.mul h5p22 h5p54).getD 9 []=h5p55.getD 9 [] := by
  decide +kernel

theorem h5n55_arithmetic_row10 :
    (BiPoly.mul h5p22 h5p54).getD 10 []=h5p55.getD 10 [] := by
  decide +kernel

theorem h5n55_arithmetic_row11 :
    (BiPoly.mul h5p22 h5p54).getD 11 []=h5p55.getD 11 [] := by
  decide +kernel

theorem h5n55_arithmetic_row12 :
    (BiPoly.mul h5p22 h5p54).getD 12 []=h5p55.getD 12 [] := by
  decide +kernel

theorem h5n55_arithmetic_row13 :
    (BiPoly.mul h5p22 h5p54).getD 13 []=h5p55.getD 13 [] := by
  decide +kernel

theorem h5n55_arithmetic_row14 :
    (BiPoly.mul h5p22 h5p54).getD 14 []=h5p55.getD 14 [] := by
  decide +kernel

theorem h5n55_arithmetic_row15 :
    (BiPoly.mul h5p22 h5p54).getD 15 []=h5p55.getD 15 [] := by
  decide +kernel

theorem h5n55_arithmetic_row16 :
    (BiPoly.mul h5p22 h5p54).getD 16 []=h5p55.getD 16 [] := by
  decide +kernel

theorem h5n55_arithmetic_row17 :
    (BiPoly.mul h5p22 h5p54).getD 17 []=h5p55.getD 17 [] := by
  decide +kernel

theorem h5n55_arithmetic : BiPoly.mul h5p22 h5p54=h5p55 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<18 at hk
    have hf : ∀ j : Fin 18, (BiPoly.mul h5p22 h5p54).getD j.val []=h5p55.getD j.val [] :=
      (fun j => Fin.cases h5n55_arithmetic_row0 (fun j => Fin.cases h5n55_arithmetic_row1 (fun j => Fin.cases h5n55_arithmetic_row2 (fun j => Fin.cases h5n55_arithmetic_row3 (fun j => Fin.cases h5n55_arithmetic_row4 (fun j => Fin.cases h5n55_arithmetic_row5 (fun j => Fin.cases h5n55_arithmetic_row6 (fun j => Fin.cases h5n55_arithmetic_row7 (fun j => Fin.cases h5n55_arithmetic_row8 (fun j => Fin.cases h5n55_arithmetic_row9 (fun j => Fin.cases h5n55_arithmetic_row10 (fun j => Fin.cases h5n55_arithmetic_row11 (fun j => Fin.cases h5n55_arithmetic_row12 (fun j => Fin.cases h5n55_arithmetic_row13 (fun j => Fin.cases h5n55_arithmetic_row14 (fun j => Fin.cases h5n55_arithmetic_row15 (fun j => Fin.cases h5n55_arithmetic_row16 (fun j => Fin.cases h5n55_arithmetic_row17 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n55 : h5e55.toBi mapPolyEnv=h5p55 := by
  change BiPoly.mul (h5e22.toBi mapPolyEnv) (h5e54.toBi mapPolyEnv)=h5p55
  rw [h5n22, h5n54]
  exact h5n55_arithmetic

#print axioms h5n55_arithmetic
end StackSorting.RationalLift
