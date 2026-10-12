import BivariateRowEquality
import Horner5Node059
import Horner5Node187
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p188 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4548518691471359), (Int.ofNat 5548798113177600), (Int.negSucc 90485514258217919), (Int.ofNat 55949394840217920), (Int.negSucc 285565736713138559), (Int.negSucc 31078365489048959), (Int.ofNat 1420650045652495680), (Int.ofNat 389074337049614400), (Int.negSucc 1291099539977763839), (Int.negSucc 670543428502056959)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 38250650314506240), (Int.negSucc 52090063513274879), (Int.ofNat 914030344573833600), (Int.negSucc 547047071145331199), (Int.ofNat 3989403725837440320), (Int.ofNat 990306828226494720), (Int.negSucc 12831619710583860479), (Int.negSucc 4044045188747508479), (Int.ofNat 7892310941787124800), (Int.ofNat 3117491999456578560), (Int.negSucc 372524126945587199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 145413164009610239), (Int.ofNat 174531164062809600), (Int.negSucc 4055632945677684719), (Int.ofNat 2052061163617855920), (Int.negSucc 22659377451457015919), (Int.negSucc 6580012685919329999), (Int.ofNat 49464961028483373360), (Int.ofNat 16632631410345730320), (Int.negSucc 20103327959626641359), (Int.negSucc 6687405151281888239), (Int.ofNat 773624537537537280), (Int.negSucc 51739462075775999)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 330930239260139520), (Int.negSucc 213820263140505599), (Int.ofNat 10446311289628662480), (Int.negSucc 2619273643548719519), (Int.ofNat 72081491468583487920), (Int.ofNat 23943642978767127360), (Int.negSucc 104209261877032841039), (Int.negSucc 42144724013747621279), (Int.ofNat 21469290918933339600), (Int.ofNat 9593765306370650880), (Int.ofNat 1136282154985313280), (Int.negSucc 53324261221171199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 503599511174964479), (Int.negSucc 204630795480674879), (Int.negSucc 17499738546277610639), (Int.negSucc 4931906433843024719), (Int.negSucc 145172089024294432319), (Int.negSucc 63036487237575070079), (Int.ofNat 121951197967886051760), (Int.ofNat 78506853158155382640), (Int.ofNat 8002050662639462880), (Int.negSucc 11297543373879155999), (Int.negSucc 5241865751963855999), (Int.ofNat 409218110937891840)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 542543620812003840), (Int.ofNat 1123604691524285760), (Int.ofNat 20438442594146495280), (Int.ofNat 24906723892057025280), (Int.ofNat 197698424714194369920), (Int.ofNat 130281532682201718720), (Int.negSucc 53440196070204706319), (Int.negSucc 107365707262302331199), (Int.negSucc 52129580161421963999), (Int.ofNat 7277535239581341120), (Int.ofNat 6032594279949578880), (Int.negSucc 56566827102919679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 427571327821655999), (Int.negSucc 1903033062207923519), (Int.negSucc 17723416384577410079), (Int.negSucc 45973773410551818719), (Int.negSucc 192011608853038243679), (Int.negSucc 204303406561614179039), (Int.negSucc 64491718599820478639), (Int.ofNat 91021232339707141680), (Int.ofNat 68095771030744053360), (Int.ofNat 7831475392533702480), (Int.negSucc 1466745324591323519), (Int.negSucc 1138309958268829439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 251119582358345280), (Int.ofNat 1911271791151347840), (Int.ofNat 12247080079144662240), (Int.ofNat 50182783951039234560), (Int.ofNat 142142803121904700320), (Int.ofNat 231226960227171801600), (Int.ofNat 146179371299687044560), (Int.negSucc 18768386329371001439), (Int.negSucc 45119742095905020719), (Int.negSucc 22543039376954182079), (Int.negSucc 2992535437241865599), (Int.ofNat 1199147078135278080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 110740582299860159), (Int.negSucc 1280414991120482879), (Int.negSucc 7149324230754480479), (Int.negSucc 35978461125437484959), (Int.negSucc 86985776586379621439), (Int.negSucc 184328165828100461759), (Int.negSucc 155764142293113946799), (Int.negSucc 55072536981273477359), (Int.ofNat 10018063823109503040), (Int.ofNat 19248865750823028480), (Int.ofNat 3824916625345478400), (Int.ofNat 252113424811188480)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 36503438350850880), (Int.ofNat 594436086285740160), (Int.ofNat 3518071154631788640), (Int.ofNat 17767567007206067520), (Int.ofNat 45868957925389652160), (Int.ofNat 103629728932872632640), (Int.ofNat 116144480436342313680), (Int.ofNat 74982577281918166080), (Int.ofNat 14198170427327920320), (Int.negSucc 3932170387939175039), (Int.negSucc 2518658534968784639), (Int.negSucc 945361535611991039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8810303650562879), (Int.negSucc 192110586050151359), (Int.negSucc 1361986619231130479), (Int.negSucc 6293285863696578959), (Int.negSucc 19770328029235754159), (Int.negSucc 42256991790632385359), (Int.negSucc 63645151302308914559), (Int.negSucc 51197553006286478399), (Int.negSucc 20865403653339908159), (Int.negSucc 5052692238337183679), (Int.ofNat 655280435313676800), (Int.ofNat 300759468944808960)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1486063287034560), (Int.ofNat 42104442705667200), (Int.ofNat 378514464975545040), (Int.ofNat 1675463912591893920), (Int.ofNat 6277288187888362800), (Int.ofNat 13206108408118165440), (Int.ofNat 24604976881511360640), (Int.ofNat 23145210838639975680), (Int.ofNat 14366650496195563200), (Int.ofNat 4653337876753674240), (Int.ofNat 667404231481382400), (Int.ofNat 186006126903091200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 158272126943039), (Int.negSucc 5808808147962239), (Int.negSucc 68727464873971919), (Int.negSucc 342429138209065679), (Int.negSucc 1341238484907017279), (Int.negSucc 3275112664600680959), (Int.negSucc 6319094657660864639), (Int.negSucc 7624095813534072959), (Int.negSucc 5640456114059166719), (Int.negSucc 2103872157575562239), (Int.negSucc 690727030286054399), (Int.negSucc 102040059460746239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8085392187840), (Int.ofNat 420416245788480), (Int.ofNat 7196549121437040), (Int.ofNat 49471676602027200), (Int.ofNat 182654915436129600), (Int.ofNat 591253335714153600), (Int.ofNat 1044679099202110080), (Int.ofNat 1752826364042895360), (Int.ofNat 1286070281065175040), (Int.ofNat 659177263955773440), (Int.ofNat 195773550772515840)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8820427841279), (Int.negSucc 337176143147519), (Int.negSucc 3928828296162239), (Int.negSucc 15865032417652799), (Int.negSucc 60205965197319359), (Int.negSucc 118086852263569919), (Int.negSucc 220812521313991679), (Int.negSucc 192120370923156479), (Int.negSucc 115259271088665599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2405571229440), (Int.ofNat 84516773863680), (Int.ofNat 825139208733120), (Int.ofNat 1909493698913280), (Int.ofNat 8707246676375040), (Int.ofNat 7831662424473600), (Int.ofNat 21525779776896000)]]

theorem h5n188_arithmetic_row0 :
    (BiPoly.mul h5p59 h5p187).getD 0 []=h5p188.getD 0 [] := by
  decide +kernel

theorem h5n188_arithmetic_row1 :
    (BiPoly.mul h5p59 h5p187).getD 1 []=h5p188.getD 1 [] := by
  decide +kernel

theorem h5n188_arithmetic_row2 :
    (BiPoly.mul h5p59 h5p187).getD 2 []=h5p188.getD 2 [] := by
  decide +kernel

theorem h5n188_arithmetic_row3 :
    (BiPoly.mul h5p59 h5p187).getD 3 []=h5p188.getD 3 [] := by
  decide +kernel

theorem h5n188_arithmetic_row4 :
    (BiPoly.mul h5p59 h5p187).getD 4 []=h5p188.getD 4 [] := by
  decide +kernel

theorem h5n188_arithmetic_row5 :
    (BiPoly.mul h5p59 h5p187).getD 5 []=h5p188.getD 5 [] := by
  decide +kernel

theorem h5n188_arithmetic_row6 :
    (BiPoly.mul h5p59 h5p187).getD 6 []=h5p188.getD 6 [] := by
  decide +kernel

theorem h5n188_arithmetic_row7 :
    (BiPoly.mul h5p59 h5p187).getD 7 []=h5p188.getD 7 [] := by
  decide +kernel

theorem h5n188_arithmetic_row8 :
    (BiPoly.mul h5p59 h5p187).getD 8 []=h5p188.getD 8 [] := by
  decide +kernel

theorem h5n188_arithmetic_row9 :
    (BiPoly.mul h5p59 h5p187).getD 9 []=h5p188.getD 9 [] := by
  decide +kernel

theorem h5n188_arithmetic_row10 :
    (BiPoly.mul h5p59 h5p187).getD 10 []=h5p188.getD 10 [] := by
  decide +kernel

theorem h5n188_arithmetic_row11 :
    (BiPoly.mul h5p59 h5p187).getD 11 []=h5p188.getD 11 [] := by
  decide +kernel

theorem h5n188_arithmetic_row12 :
    (BiPoly.mul h5p59 h5p187).getD 12 []=h5p188.getD 12 [] := by
  decide +kernel

theorem h5n188_arithmetic_row13 :
    (BiPoly.mul h5p59 h5p187).getD 13 []=h5p188.getD 13 [] := by
  decide +kernel

theorem h5n188_arithmetic_row14 :
    (BiPoly.mul h5p59 h5p187).getD 14 []=h5p188.getD 14 [] := by
  decide +kernel

theorem h5n188_arithmetic_row15 :
    (BiPoly.mul h5p59 h5p187).getD 15 []=h5p188.getD 15 [] := by
  decide +kernel

theorem h5n188_arithmetic : BiPoly.mul h5p59 h5p187=h5p188 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h5p59 h5p187).getD j.val []=h5p188.getD j.val [] :=
      (fun j => Fin.cases h5n188_arithmetic_row0 (fun j => Fin.cases h5n188_arithmetic_row1 (fun j => Fin.cases h5n188_arithmetic_row2 (fun j => Fin.cases h5n188_arithmetic_row3 (fun j => Fin.cases h5n188_arithmetic_row4 (fun j => Fin.cases h5n188_arithmetic_row5 (fun j => Fin.cases h5n188_arithmetic_row6 (fun j => Fin.cases h5n188_arithmetic_row7 (fun j => Fin.cases h5n188_arithmetic_row8 (fun j => Fin.cases h5n188_arithmetic_row9 (fun j => Fin.cases h5n188_arithmetic_row10 (fun j => Fin.cases h5n188_arithmetic_row11 (fun j => Fin.cases h5n188_arithmetic_row12 (fun j => Fin.cases h5n188_arithmetic_row13 (fun j => Fin.cases h5n188_arithmetic_row14 (fun j => Fin.cases h5n188_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n188 : h5e188.toBi mapPolyEnv=h5p188 := by
  change BiPoly.mul (h5e59.toBi mapPolyEnv) (h5e187.toBi mapPolyEnv)=h5p188
  rw [h5n59, h5n187]
  exact h5n188_arithmetic

#print axioms h5n188_arithmetic
end StackSorting.RationalLift
