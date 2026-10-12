import BivariateRowEquality
import Horner0Base
import Horner0Node079
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p80 : BiPoly.Poly := [[(Int.ofNat 1523547190158984000), (Int.ofNat 11520564604912427040), (Int.ofNat 15305446966497063840), (Int.negSucc 40933732885317364319), (Int.negSucc 46997681212757386079), (Int.ofNat 56607621254219851200)], [(Int.negSucc 14069341517855420159), (Int.negSucc 107152680102337674431), (Int.negSucc 149767906560836736095), (Int.ofNat 347892544887197990976), (Int.ofNat 402642630056084056992), (Int.negSucc 499701190208840479295), (Int.ofNat 41006057296895827200)], [(Int.ofNat 61245369733168400400), (Int.ofNat 457284224895877427400), (Int.ofNat 653025778583831115552), (Int.negSucc 1299819016107895468607), (Int.negSucc 1581845176201470165503), (Int.ofNat 1806680803089985939800), (Int.negSucc 188023730756735067983), (Int.ofNat 9614021433147873792)], [(Int.negSucc 166517434537287751439), (Int.negSucc 1185264530958662962919), (Int.negSucc 1711287305995949542367), (Int.ofNat 2651694157617223048416), (Int.ofNat 3712531615313565179376), (Int.negSucc 3203653854405591446327), (Int.ofNat 64000521297439163136), (Int.negSucc 2379444462713637791), (Int.ofNat 706251951755006976)], [(Int.ofNat 314804126306428428240), (Int.ofNat 2087881380705361543416), (Int.ofNat 3080260609257975248736), (Int.negSucc 2846496073869665204687), (Int.negSucc 5712176485171321627679), (Int.ofNat 1925862746008658431464), (Int.ofNat 1246760219631905922528), (Int.negSucc 122622238207725259967), (Int.ofNat 3845533296314544192), (Int.negSucc 3764143844398079)], [(Int.negSucc 435123164643461823959), (Int.negSucc 2659455099480424527251), (Int.negSucc 4148703885357583332443), (Int.ofNat 542969234391178614240), (Int.ofNat 5743141165859067790560), (Int.ofNat 3120550044140677532364), (Int.negSucc 3166867200071824287947), (Int.ofNat 189838988498825536536), (Int.negSucc 5308448177122612991), (Int.ofNat 122993045314349184)], [(Int.ofNat 450072092762200293000), (Int.ofNat 2554560375840880677588), (Int.ofNat 4453587626124832460520), (Int.ofNat 3025448374377290703216), (Int.negSucc 2989700582310694666871), (Int.negSucc 7700686569304056735779), (Int.ofNat 2620653540667850720808), (Int.ofNat 336235275397575166344), (Int.negSucc 30047732982302391407), (Int.ofNat 733695523625245056)], [(Int.negSucc 351129317540932662839), (Int.negSucc 1911837001939725256571), (Int.negSucc 3968377586559714092963), (Int.negSucc 5105455073372065077047), (Int.negSucc 1044619577700128415095), (Int.ofNat 6864814526082122272740), (Int.ofNat 1278877001897383737972), (Int.negSucc 1124500866706309983815), (Int.ofNat 43504089731545190784), (Int.ofNat 24289530237913728)], [(Int.ofNat 206047609985625655320), (Int.ofNat 1142951672410372172820), (Int.ofNat 2969684959276805361648), (Int.ofNat 4721428215461842117464), (Int.ofNat 3651206460377225795880), (Int.negSucc 1848626100770410574843), (Int.negSucc 4266932166956283358031), (Int.ofNat 817562214056655329784), (Int.ofNat 68055846741513361824), (Int.negSucc 3952980537816738911)], [(Int.negSucc 89841877410993057719), (Int.negSucc 552852637252765877435), (Int.negSucc 1838155841781460889063), (Int.negSucc 3139657882240100326559), (Int.negSucc 3683557283193356144867), (Int.negSucc 2131655780188831566359), (Int.ofNat 3112798846759043715108), (Int.ofNat 498283212046686576384), (Int.negSucc 163728581542291958339), (Int.negSucc 149198746025904743)], [(Int.ofNat 28434363379598384520), (Int.ofNat 215241319590757227756), (Int.ofNat 912280440771670543092), (Int.ofNat 1711061934895544342220), (Int.ofNat 2324392175843810126424), (Int.ofNat 2740868062216058017248), (Int.negSucc 204956811104107612979), (Int.negSucc 1075929823091452786835), (Int.ofNat 48731443623797042832), (Int.ofNat 8737142905054281168)], [(Int.negSucc 6275361283079199479), (Int.negSucc 65796914060443415387), (Int.negSucc 349797069506652416723), (Int.negSucc 808675702117531401599), (Int.negSucc 1098280736235591844631), (Int.negSucc 1578931155271762236863), (Int.negSucc 1129291939308471835991), (Int.ofNat 479377791458754468600), (Int.ofNat 108940707913242464232), (Int.negSucc 3805278459586304975)], [(Int.ofNat 900183540484277400), (Int.ofNat 15143151051405906132), (Int.ofNat 99483729646488216888), (Int.ofNat 318739509441675560472), (Int.ofNat 448759733104572901344), (Int.ofNat 572829915550181522328), (Int.ofNat 828977558641200454368), (Int.ofNat 140775980127735977784), (Int.negSucc 94326168723961729895), (Int.negSucc 6066884234541299759)], [(Int.negSucc 73188011075561519), (Int.negSucc 2466323971512827567), (Int.negSucc 19992379740350070995), (Int.negSucc 95739087500283670175), (Int.negSucc 166591650017413276499), (Int.negSucc 159453434872343817431), (Int.negSucc 283962297321931188383), (Int.negSucc 221403383933483118671), (Int.ofNat 4343339450898221040), (Int.ofNat 5107661750497803552)], [(Int.ofNat 2392047021054240), (Int.ofNat 255309932519798904), (Int.ofNat 2653100914321169532), (Int.ofNat 19977360646779882540), (Int.ofNat 50608357493907548304), (Int.ofNat 44944475384395388304), (Int.ofNat 51516290356689053808), (Int.ofNat 89963544712349998512), (Int.ofNat 25323959425170368448), (Int.ofNat 191117498076975168)], [(Int.ofNat 0), (Int.negSucc 12811266214639487), (Int.negSucc 206835882267041711), (Int.negSucc 2606561438977988711), (Int.negSucc 10850080597509474071), (Int.negSucc 12862396588922561951), (Int.negSucc 5301648401327243567), (Int.negSucc 15943192144443307871), (Int.negSucc 12509982936042144479), (Int.negSucc 1439994887113537727)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7119842392942560), (Int.ofNat 174885311880411768), (Int.ofNat 1429751002190312664), (Int.ofNat 2723879588326963488), (Int.ofNat 802420906723053984), (Int.ofNat 639365525197082784), (Int.ofNat 2392736446029492576), (Int.ofNat 536016567863969856)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2996129648131199), (Int.negSucc 92118093772922783), (Int.negSucc 332359919578562111), (Int.negSucc 200532201721794143), (Int.ofNat 174235643502500160), (Int.negSucc 161488848302516735), (Int.negSucc 62445874385525759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 962833231078272), (Int.ofNat 17414818697425248), (Int.ofNat 20892366869823648), (Int.negSucc 20171875201427519)]]

theorem h0n80_arithmetic_row0 :
    (BiPoly.mul h0p7 h0p79).getD 0 []=h0p80.getD 0 [] := by
  decide +kernel

theorem h0n80_arithmetic_row1 :
    (BiPoly.mul h0p7 h0p79).getD 1 []=h0p80.getD 1 [] := by
  decide +kernel

theorem h0n80_arithmetic_row2 :
    (BiPoly.mul h0p7 h0p79).getD 2 []=h0p80.getD 2 [] := by
  decide +kernel

theorem h0n80_arithmetic_row3 :
    (BiPoly.mul h0p7 h0p79).getD 3 []=h0p80.getD 3 [] := by
  decide +kernel

theorem h0n80_arithmetic_row4 :
    (BiPoly.mul h0p7 h0p79).getD 4 []=h0p80.getD 4 [] := by
  decide +kernel

theorem h0n80_arithmetic_row5 :
    (BiPoly.mul h0p7 h0p79).getD 5 []=h0p80.getD 5 [] := by
  decide +kernel

theorem h0n80_arithmetic_row6 :
    (BiPoly.mul h0p7 h0p79).getD 6 []=h0p80.getD 6 [] := by
  decide +kernel

theorem h0n80_arithmetic_row7 :
    (BiPoly.mul h0p7 h0p79).getD 7 []=h0p80.getD 7 [] := by
  decide +kernel

theorem h0n80_arithmetic_row8 :
    (BiPoly.mul h0p7 h0p79).getD 8 []=h0p80.getD 8 [] := by
  decide +kernel

theorem h0n80_arithmetic_row9 :
    (BiPoly.mul h0p7 h0p79).getD 9 []=h0p80.getD 9 [] := by
  decide +kernel

theorem h0n80_arithmetic_row10 :
    (BiPoly.mul h0p7 h0p79).getD 10 []=h0p80.getD 10 [] := by
  decide +kernel

theorem h0n80_arithmetic_row11 :
    (BiPoly.mul h0p7 h0p79).getD 11 []=h0p80.getD 11 [] := by
  decide +kernel

theorem h0n80_arithmetic_row12 :
    (BiPoly.mul h0p7 h0p79).getD 12 []=h0p80.getD 12 [] := by
  decide +kernel

theorem h0n80_arithmetic_row13 :
    (BiPoly.mul h0p7 h0p79).getD 13 []=h0p80.getD 13 [] := by
  decide +kernel

theorem h0n80_arithmetic_row14 :
    (BiPoly.mul h0p7 h0p79).getD 14 []=h0p80.getD 14 [] := by
  decide +kernel

theorem h0n80_arithmetic_row15 :
    (BiPoly.mul h0p7 h0p79).getD 15 []=h0p80.getD 15 [] := by
  decide +kernel

theorem h0n80_arithmetic_row16 :
    (BiPoly.mul h0p7 h0p79).getD 16 []=h0p80.getD 16 [] := by
  decide +kernel

theorem h0n80_arithmetic_row17 :
    (BiPoly.mul h0p7 h0p79).getD 17 []=h0p80.getD 17 [] := by
  decide +kernel

theorem h0n80_arithmetic_row18 :
    (BiPoly.mul h0p7 h0p79).getD 18 []=h0p80.getD 18 [] := by
  decide +kernel

theorem h0n80_arithmetic : BiPoly.mul h0p7 h0p79=h0p80 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p7 h0p79).getD j.val []=h0p80.getD j.val [] :=
      (fun j => Fin.cases h0n80_arithmetic_row0 (fun j => Fin.cases h0n80_arithmetic_row1 (fun j => Fin.cases h0n80_arithmetic_row2 (fun j => Fin.cases h0n80_arithmetic_row3 (fun j => Fin.cases h0n80_arithmetic_row4 (fun j => Fin.cases h0n80_arithmetic_row5 (fun j => Fin.cases h0n80_arithmetic_row6 (fun j => Fin.cases h0n80_arithmetic_row7 (fun j => Fin.cases h0n80_arithmetic_row8 (fun j => Fin.cases h0n80_arithmetic_row9 (fun j => Fin.cases h0n80_arithmetic_row10 (fun j => Fin.cases h0n80_arithmetic_row11 (fun j => Fin.cases h0n80_arithmetic_row12 (fun j => Fin.cases h0n80_arithmetic_row13 (fun j => Fin.cases h0n80_arithmetic_row14 (fun j => Fin.cases h0n80_arithmetic_row15 (fun j => Fin.cases h0n80_arithmetic_row16 (fun j => Fin.cases h0n80_arithmetic_row17 (fun j => Fin.cases h0n80_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n80 : h0e80.toBi mapPolyEnv=h0p80 := by
  change BiPoly.mul (h0e7.toBi mapPolyEnv) (h0e79.toBi mapPolyEnv)=h0p80
  rw [h0n7, h0n79]
  exact h0n80_arithmetic

#print axioms h0n80_arithmetic
end StackSorting.RationalLift
