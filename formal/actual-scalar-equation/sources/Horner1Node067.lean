import BivariateRowEquality
import Horner1Base
import Horner1Node066
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p67 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 33447873024000), (Int.ofNat 185541242077440), (Int.negSucc 27010858078079), (Int.negSucc 1008906704231039), (Int.negSucc 58785757983359), (Int.ofNat 771016719116160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 366004899077759), (Int.negSucc 1788855183461951), (Int.ofNat 1164580206281280), (Int.ofNat 10072167020642304), (Int.negSucc 1812231843197183), (Int.negSucc 6492298904650943), (Int.ofNat 439839684090432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1843326132937920), (Int.ofNat 7866569946934944), (Int.negSucc 9041701403896703), (Int.negSucc 44525492804436479), (Int.ofNat 14308195531462272), (Int.ofNat 21599184824474976), (Int.ofNat 323512891468992), (Int.negSucc 67005165347711)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5660311330942559), (Int.negSucc 20897798911783343), (Int.ofNat 34187853586385088), (Int.ofNat 117466609126846320), (Int.negSucc 36985256620685279), (Int.negSucc 40313920782700943), (Int.negSucc 17437316220133631), (Int.ofNat 2405767893282000), (Int.negSucc 97073147326463)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11832597720234000), (Int.ofNat 37461150657106632), (Int.negSucc 78817035941474543), (Int.negSucc 212587556795070839), (Int.ofNat 18701097579134640), (Int.ofNat 61042846274426520), (Int.ofNat 67559620004000496), (Int.negSucc 7474121977011623), (Int.ofNat 537618389167872), (Int.negSucc 24502554114047)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17802825988435199), (Int.negSucc 47986306778424959), (Int.ofNat 122165118819696912), (Int.ofNat 293069030669307600), (Int.ofNat 115861489600932288), (Int.negSucc 96362581754498015), (Int.negSucc 116581119792312047), (Int.negSucc 9331527011352431), (Int.ofNat 2039128304288352), (Int.negSucc 57101070959999), (Int.negSucc 2329243124735)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 19868588307964080), (Int.ofNat 45448994907622296), (Int.negSucc 134519707353043175), (Int.negSucc 337922713032108431), (Int.negSucc 340776195134701319), (Int.ofNat 101233534827122520), (Int.ofNat 109468545186627336), (Int.ofNat 75637000641948672), (Int.negSucc 10832948915482439), (Int.ofNat 763239158896896), (Int.negSucc 23865072976895), (Int.negSucc 64851511295)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 16698906262348159), (Int.negSucc 32568199434005311), (Int.ofNat 109832629115422320), (Int.ofNat 345297518864680800), (Int.ofNat 507300838559029104), (Int.ofNat 32184378261280128), (Int.negSucc 72268065082416463), (Int.negSucc 133432630972250959), (Int.ofNat 2900712503023632), (Int.ofNat 441178433652880), (Int.ofNat 13536581960320), (Int.negSucc 1513483276031)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10614666072195680), (Int.ofNat 17981690950052912), (Int.negSucc 70122032756617167), (Int.negSucc 311394116343483079), (Int.negSucc 513225350909080183), (Int.negSucc 283741247348869183), (Int.ofNat 42672132278194416), (Int.ofNat 95637562647588240), (Int.ofNat 44518108216229592), (Int.negSucc 6294062037249271), (Int.ofNat 354737799364768), (Int.negSucc 5923333990783)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5075260198324799), (Int.negSucc 7774291213282015), (Int.ofNat 37956358648351984), (Int.ofNat 237950957093432688), (Int.ofNat 405179361429880080), (Int.ofNat 451646576301148656), (Int.ofNat 35084065435526784), (Int.negSucc 9771719655723103), (Int.negSucc 78679306521228559), (Int.ofNat 3802870017732816), (Int.negSucc 47674458471487), (Int.ofNat 8389539762112)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1795886177432800), (Int.ofNat 2662702260326960), (Int.negSucc 18945341665483711), (Int.negSucc 148725406996880863), (Int.negSucc 278587557539628031), (Int.negSucc 411648094392678191), (Int.negSucc 167954316742591791), (Int.negSucc 29309060072222783), (Int.ofNat 41773719891094504), (Int.ofNat 15730026405247880), (Int.negSucc 1777146441989687), (Int.ofNat 59445781279072)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 455837919039519), (Int.negSucc 719825226262223), (Int.ofNat 8753818668291696), (Int.ofNat 74694757307126304), (Int.ofNat 174572962610408688), (Int.ofNat 258126482761357296), (Int.ofNat 235757336343662880), (Int.ofNat 41941654323118960), (Int.ofNat 14924646950557120), (Int.negSucc 25013771076112671), (Int.ofNat 996715733794656), (Int.negSucc 11932494162239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 78428763108240), (Int.ofNat 148247771850248), (Int.negSucc 3412780343465535), (Int.negSucc 29849767782811655), (Int.negSucc 95118088431957871), (Int.negSucc 129630680416257367), (Int.negSucc 181691604127087439), (Int.negSucc 65927724715717703), (Int.negSucc 27968959651373399), (Int.ofNat 7958321583267264), (Int.ofNat 3259723066563648), (Int.negSucc 204870656833535)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8185343289919), (Int.negSucc 21406353441887), (Int.ofNat 1003660200984320), (Int.ofNat 9335798846142176), (Int.ofNat 41440874922155616), (Int.ofNat 61201321169544688), (Int.ofNat 87775917545544528), (Int.ofNat 70122277648724640), (Int.ofNat 18142787984173200), (Int.ofNat 8294948980122624), (Int.negSucc 3864323788366031), (Int.ofNat 57532549614528)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 390894561200), (Int.ofNat 1853052138904), (Int.negSucc 201325560804439), (Int.negSucc 2202796080715791), (Int.negSucc 13432305476177063), (Int.negSucc 27372930210236759), (Int.negSucc 30508198617313127), (Int.negSucc 42507974782209983), (Int.negSucc 14305414871021039), (Int.negSucc 7823966744039567), (Int.ofNat 239692095927648), (Int.ofNat 291145034801664)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 67687448639), (Int.ofNat 24229497672480), (Int.ofNat 365706988002000), (Int.ofNat 3038053982585376), (Int.ofNat 9854061322703424), (Int.ofNat 10111679006223552), (Int.ofNat 14720078571559296), (Int.ofNat 10881797642042400), (Int.ofNat 3085992018080352), (Int.ofNat 1511733174484320), (Int.negSucc 198321686246015)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1312860222719), (Int.negSucc 37555782108599), (Int.negSucc 441623333413415), (Int.negSucc 2431825700146463), (Int.negSucc 3615101666526815), (Int.negSucc 3158298177469343), (Int.negSucc 4769218857688127), (Int.negSucc 1421762973086015), (Int.negSucc 806938828636031), (Int.negSucc 52741788125183)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1766405666592), (Int.ofNat 35633202819120), (Int.ofNat 359585339913216), (Int.ofNat 1017742574524464), (Int.ofNat 680916070956096), (Int.ofNat 1022343136025472), (Int.ofNat 746428196500992), (Int.ofNat 180036791066304), (Int.ofNat 79617145999104)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1112371583471), (Int.negSucc 25880501363471), (Int.negSucc 166456817328095), (Int.negSucc 201295100263679), (Int.negSucc 96756910361279), (Int.negSucc 205407255043007), (Int.negSucc 45685473064703), (Int.negSucc 22582572111359)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 472210313760), (Int.ofNat 11924987565024), (Int.ofNat 39052832268672), (Int.ofNat 12716439666624), (Int.ofNat 18840040573824), (Int.ofNat 14917624122240), (Int.ofNat 1889390707200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 134004103487), (Int.negSucc 2899647118655), (Int.negSucc 3611689420031), (Int.ofNat 453773456640), (Int.negSucc 1889390707199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 16956563328), (Int.ofNat 283408606080)]]

theorem h1n67_arithmetic_row0 :
    (BiPoly.mul h1p64 h1p66).getD 0 []=h1p67.getD 0 [] := by
  decide +kernel

theorem h1n67_arithmetic_row1 :
    (BiPoly.mul h1p64 h1p66).getD 1 []=h1p67.getD 1 [] := by
  decide +kernel

theorem h1n67_arithmetic_row2 :
    (BiPoly.mul h1p64 h1p66).getD 2 []=h1p67.getD 2 [] := by
  decide +kernel

theorem h1n67_arithmetic_row3 :
    (BiPoly.mul h1p64 h1p66).getD 3 []=h1p67.getD 3 [] := by
  decide +kernel

theorem h1n67_arithmetic_row4 :
    (BiPoly.mul h1p64 h1p66).getD 4 []=h1p67.getD 4 [] := by
  decide +kernel

theorem h1n67_arithmetic_row5 :
    (BiPoly.mul h1p64 h1p66).getD 5 []=h1p67.getD 5 [] := by
  decide +kernel

theorem h1n67_arithmetic_row6 :
    (BiPoly.mul h1p64 h1p66).getD 6 []=h1p67.getD 6 [] := by
  decide +kernel

theorem h1n67_arithmetic_row7 :
    (BiPoly.mul h1p64 h1p66).getD 7 []=h1p67.getD 7 [] := by
  decide +kernel

theorem h1n67_arithmetic_row8 :
    (BiPoly.mul h1p64 h1p66).getD 8 []=h1p67.getD 8 [] := by
  decide +kernel

theorem h1n67_arithmetic_row9 :
    (BiPoly.mul h1p64 h1p66).getD 9 []=h1p67.getD 9 [] := by
  decide +kernel

theorem h1n67_arithmetic_row10 :
    (BiPoly.mul h1p64 h1p66).getD 10 []=h1p67.getD 10 [] := by
  decide +kernel

theorem h1n67_arithmetic_row11 :
    (BiPoly.mul h1p64 h1p66).getD 11 []=h1p67.getD 11 [] := by
  decide +kernel

theorem h1n67_arithmetic_row12 :
    (BiPoly.mul h1p64 h1p66).getD 12 []=h1p67.getD 12 [] := by
  decide +kernel

theorem h1n67_arithmetic_row13 :
    (BiPoly.mul h1p64 h1p66).getD 13 []=h1p67.getD 13 [] := by
  decide +kernel

theorem h1n67_arithmetic_row14 :
    (BiPoly.mul h1p64 h1p66).getD 14 []=h1p67.getD 14 [] := by
  decide +kernel

theorem h1n67_arithmetic_row15 :
    (BiPoly.mul h1p64 h1p66).getD 15 []=h1p67.getD 15 [] := by
  decide +kernel

theorem h1n67_arithmetic_row16 :
    (BiPoly.mul h1p64 h1p66).getD 16 []=h1p67.getD 16 [] := by
  decide +kernel

theorem h1n67_arithmetic_row17 :
    (BiPoly.mul h1p64 h1p66).getD 17 []=h1p67.getD 17 [] := by
  decide +kernel

theorem h1n67_arithmetic_row18 :
    (BiPoly.mul h1p64 h1p66).getD 18 []=h1p67.getD 18 [] := by
  decide +kernel

theorem h1n67_arithmetic_row19 :
    (BiPoly.mul h1p64 h1p66).getD 19 []=h1p67.getD 19 [] := by
  decide +kernel

theorem h1n67_arithmetic_row20 :
    (BiPoly.mul h1p64 h1p66).getD 20 []=h1p67.getD 20 [] := by
  decide +kernel

theorem h1n67_arithmetic_row21 :
    (BiPoly.mul h1p64 h1p66).getD 21 []=h1p67.getD 21 [] := by
  decide +kernel

theorem h1n67_arithmetic : BiPoly.mul h1p64 h1p66=h1p67 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p64 h1p66).getD j.val []=h1p67.getD j.val [] :=
      (fun j => Fin.cases h1n67_arithmetic_row0 (fun j => Fin.cases h1n67_arithmetic_row1 (fun j => Fin.cases h1n67_arithmetic_row2 (fun j => Fin.cases h1n67_arithmetic_row3 (fun j => Fin.cases h1n67_arithmetic_row4 (fun j => Fin.cases h1n67_arithmetic_row5 (fun j => Fin.cases h1n67_arithmetic_row6 (fun j => Fin.cases h1n67_arithmetic_row7 (fun j => Fin.cases h1n67_arithmetic_row8 (fun j => Fin.cases h1n67_arithmetic_row9 (fun j => Fin.cases h1n67_arithmetic_row10 (fun j => Fin.cases h1n67_arithmetic_row11 (fun j => Fin.cases h1n67_arithmetic_row12 (fun j => Fin.cases h1n67_arithmetic_row13 (fun j => Fin.cases h1n67_arithmetic_row14 (fun j => Fin.cases h1n67_arithmetic_row15 (fun j => Fin.cases h1n67_arithmetic_row16 (fun j => Fin.cases h1n67_arithmetic_row17 (fun j => Fin.cases h1n67_arithmetic_row18 (fun j => Fin.cases h1n67_arithmetic_row19 (fun j => Fin.cases h1n67_arithmetic_row20 (fun j => Fin.cases h1n67_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n67 : h1e67.toBi mapPolyEnv=h1p67 := by
  change BiPoly.mul (h1e64.toBi mapPolyEnv) (h1e66.toBi mapPolyEnv)=h1p67
  rw [h1n64, h1n66]
  exact h1n67_arithmetic

#print axioms h1n67_arithmetic
end StackSorting.RationalLift
