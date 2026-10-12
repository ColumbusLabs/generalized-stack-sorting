import BivariateRowEquality
import Horner0Base
import Horner0Node014
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p15 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 10705477025738411712), (Int.ofNat 55175947345414510848), (Int.negSucc 39988735618205043071), (Int.negSucc 286260054819917955839), (Int.ofNat 288156172543265476800)], [(Int.ofNat 0), (Int.negSucc 104560052716534591871), (Int.negSucc 573372528034269648383), (Int.ofNat 246583339177653520128), (Int.ofNat 2802180228403503882240), (Int.negSucc 2606655667072208084351), (Int.ofNat 157820185311077076480)], [(Int.ofNat 0), (Int.ofNat 496504296136942277184), (Int.ofNat 2663085845942872069248), (Int.negSucc 781565077621420445951), (Int.negSucc 11571381113550599563775), (Int.ofNat 9849662867291690658240), (Int.negSucc 719566650883985922431), (Int.ofNat 20808180993764178432)], [(Int.ofNat 0), (Int.negSucc 1514247508419055337663), (Int.negSucc 7392045529924486272575), (Int.ofNat 2159627687211868230528), (Int.ofNat 25497509276425767502464), (Int.negSucc 18277742403391545196991), (Int.ofNat 211814795120752903104), (Int.ofNat 25014775067477703936), (Int.negSucc 219334388072785919)], [(Int.ofNat 0), (Int.ofNat 3296717912481055264704), (Int.ofNat 13687617097710002830656), (Int.negSucc 5208732023657538570047), (Int.negSucc 29879714262525990960767), (Int.ofNat 11579425296807992584704), (Int.ofNat 5185633694020705246272), (Int.negSucc 343469834224673604287), (Int.ofNat 7996989686075444736), (Int.ofNat 556565502028800)], [(Int.ofNat 0), (Int.negSucc 5391255920500311953855), (Int.negSucc 17682858997513576303487), (Int.ofNat 8045740612136849806848), (Int.ofNat 11850743564928438495360), (Int.ofNat 17460105117248533826112), (Int.negSucc 13384185867816684719615), (Int.ofNat 324273054958428801792), (Int.ofNat 13257116005691417088), (Int.negSucc 40390297603476479)], [(Int.ofNat 0), (Int.ofNat 6795865641682250669424), (Int.ofNat 16065987000749135075808), (Int.negSucc 4916079315610809930095), (Int.ofNat 13047740317303552577472), (Int.negSucc 40768051749792868257455), (Int.ofNat 11366877798149795570400), (Int.ofNat 1326864011534906401392), (Int.negSucc 76465192650729871871), (Int.ofNat 665135373026917632)], [(Int.ofNat 0), (Int.negSucc 6677851401212569042079), (Int.negSucc 10103805693400566818591), (Int.negSucc 5392320662582297397887), (Int.negSucc 18037849270466125467839), (Int.ofNat 27818708927343234057120), (Int.ofNat 5052011398313442317472), (Int.negSucc 3165753018422200243775), (Int.negSucc 10658561409098974463), (Int.ofNat 2578128975892578816)], [(Int.ofNat 0), (Int.ofNat 5120892162766984554768), (Int.ofNat 4400534349663845750880), (Int.ofNat 14098396668479869732704), (Int.ofNat 5832722965727839756320), (Int.ofNat 3679999384149224080848), (Int.negSucc 16964545793301407796959), (Int.ofNat 1672621340150694876096), (Int.ofNat 276149208226169110560), (Int.negSucc 2390768743769873087)], [(Int.ofNat 0), (Int.negSucc 3043373580907229140799), (Int.negSucc 1736126459876216187839), (Int.negSucc 13562159710788347977727), (Int.ofNat 1592149668202829174784), (Int.negSucc 16660811432867520924671), (Int.ofNat 10687085902829094583680), (Int.ofNat 1880442882339716916288), (Int.negSucc 234663530676185690303), (Int.negSucc 8658526107326673599)], [(Int.ofNat 0), (Int.ofNat 1381892325893300000016), (Int.ofNat 1213692225277634269056), (Int.ofNat 7121420504236633867968), (Int.ofNat 671672524621436499744), (Int.ofNat 9339983600790015080976), (Int.ofNat 1162802811838711408608), (Int.negSucc 2676641597650049831087), (Int.negSucc 167752349972584787999), (Int.ofNat 8013745304604314928)], [(Int.ofNat 0), (Int.negSucc 468823468362535249631), (Int.negSucc 1016741097276961267487), (Int.negSucc 1965711710758018852127), (Int.negSucc 3173939448413153443871), (Int.negSucc 1449880507440476788991), (Int.negSucc 4607557546319187360383), (Int.ofNat 700023247156741858464), (Int.ofNat 304256723774997868128), (Int.ofNat 7411074012887179968)], [(Int.ofNat 0), (Int.ofNat 114945221789565933936), (Int.ofNat 601601427596890947360), (Int.ofNat 167791975247912205456), (Int.ofNat 2320983462462622938528), (Int.negSucc 273587862629516676191), (Int.ofNat 2244970569915603871296), (Int.ofNat 608969917752176249040), (Int.negSucc 81434942458016964479), (Int.negSucc 10068159389060693375)], [(Int.ofNat 0), (Int.negSucc 19354809409258273343), (Int.negSucc 232808042118459255167), (Int.ofNat 10657638719426903424), (Int.negSucc 774697896616305211199), (Int.negSucc 95139559196255402111), (Int.negSucc 383814874434030622271), (Int.negSucc 489871685397981144959), (Int.negSucc 70777002567415467455), (Int.ofNat 404986190969923200)], [(Int.ofNat 0), (Int.ofNat 2060818256573744448), (Int.ofNat 58445141690200737504), (Int.ofNat 34883870939669534160), (Int.ofNat 99849717708671981664), (Int.ofNat 168626576035414580112), (Int.negSucc 25483935844211514623), (Int.ofNat 132561827308138405248), (Int.ofNat 52878202732059886080), (Int.ofNat 3617013097056500928)], [(Int.ofNat 0), (Int.negSucc 119953087917808895), (Int.negSucc 9148008821239546559), (Int.negSucc 24680690017745536223), (Int.ofNat 15007426039109472480), (Int.negSucc 62984667904843116095), (Int.ofNat 18249723237042711936), (Int.negSucc 12136097594739985919), (Int.negSucc 12639164839578427391), (Int.negSucc 1711473210486171647)], [(Int.ofNat 0), (Int.ofNat 2838583000541952), (Int.ofNat 794484735341035392), (Int.ofNat 7109161545067789104), (Int.negSucc 7878596652116083583), (Int.ofNat 10974883956597556992), (Int.negSucc 2324804370238236671), (Int.negSucc 679493452250247551), (Int.ofNat 991360245036220416), (Int.ofNat 244631676667871232)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 27163745561926655), (Int.negSucc 1038204854926216703), (Int.ofNat 1244286172798797888), (Int.negSucc 876302854399762559), (Int.ofNat 68067817229869056), (Int.ofNat 158046618791651328)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 64985687648750592), (Int.negSucc 81458746448804351), (Int.ofNat 25526879891137728)]]

theorem h0n15_arithmetic_row0 :
    (BiPoly.mul h0p11 h0p14).getD 0 []=h0p15.getD 0 [] := by
  decide +kernel

theorem h0n15_arithmetic_row1 :
    (BiPoly.mul h0p11 h0p14).getD 1 []=h0p15.getD 1 [] := by
  decide +kernel

theorem h0n15_arithmetic_row2 :
    (BiPoly.mul h0p11 h0p14).getD 2 []=h0p15.getD 2 [] := by
  decide +kernel

theorem h0n15_arithmetic_row3 :
    (BiPoly.mul h0p11 h0p14).getD 3 []=h0p15.getD 3 [] := by
  decide +kernel

theorem h0n15_arithmetic_row4 :
    (BiPoly.mul h0p11 h0p14).getD 4 []=h0p15.getD 4 [] := by
  decide +kernel

theorem h0n15_arithmetic_row5 :
    (BiPoly.mul h0p11 h0p14).getD 5 []=h0p15.getD 5 [] := by
  decide +kernel

theorem h0n15_arithmetic_row6 :
    (BiPoly.mul h0p11 h0p14).getD 6 []=h0p15.getD 6 [] := by
  decide +kernel

theorem h0n15_arithmetic_row7 :
    (BiPoly.mul h0p11 h0p14).getD 7 []=h0p15.getD 7 [] := by
  decide +kernel

theorem h0n15_arithmetic_row8 :
    (BiPoly.mul h0p11 h0p14).getD 8 []=h0p15.getD 8 [] := by
  decide +kernel

theorem h0n15_arithmetic_row9 :
    (BiPoly.mul h0p11 h0p14).getD 9 []=h0p15.getD 9 [] := by
  decide +kernel

theorem h0n15_arithmetic_row10 :
    (BiPoly.mul h0p11 h0p14).getD 10 []=h0p15.getD 10 [] := by
  decide +kernel

theorem h0n15_arithmetic_row11 :
    (BiPoly.mul h0p11 h0p14).getD 11 []=h0p15.getD 11 [] := by
  decide +kernel

theorem h0n15_arithmetic_row12 :
    (BiPoly.mul h0p11 h0p14).getD 12 []=h0p15.getD 12 [] := by
  decide +kernel

theorem h0n15_arithmetic_row13 :
    (BiPoly.mul h0p11 h0p14).getD 13 []=h0p15.getD 13 [] := by
  decide +kernel

theorem h0n15_arithmetic_row14 :
    (BiPoly.mul h0p11 h0p14).getD 14 []=h0p15.getD 14 [] := by
  decide +kernel

theorem h0n15_arithmetic_row15 :
    (BiPoly.mul h0p11 h0p14).getD 15 []=h0p15.getD 15 [] := by
  decide +kernel

theorem h0n15_arithmetic_row16 :
    (BiPoly.mul h0p11 h0p14).getD 16 []=h0p15.getD 16 [] := by
  decide +kernel

theorem h0n15_arithmetic_row17 :
    (BiPoly.mul h0p11 h0p14).getD 17 []=h0p15.getD 17 [] := by
  decide +kernel

theorem h0n15_arithmetic_row18 :
    (BiPoly.mul h0p11 h0p14).getD 18 []=h0p15.getD 18 [] := by
  decide +kernel

theorem h0n15_arithmetic : BiPoly.mul h0p11 h0p14=h0p15 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p11 h0p14).getD j.val []=h0p15.getD j.val [] :=
      (fun j => Fin.cases h0n15_arithmetic_row0 (fun j => Fin.cases h0n15_arithmetic_row1 (fun j => Fin.cases h0n15_arithmetic_row2 (fun j => Fin.cases h0n15_arithmetic_row3 (fun j => Fin.cases h0n15_arithmetic_row4 (fun j => Fin.cases h0n15_arithmetic_row5 (fun j => Fin.cases h0n15_arithmetic_row6 (fun j => Fin.cases h0n15_arithmetic_row7 (fun j => Fin.cases h0n15_arithmetic_row8 (fun j => Fin.cases h0n15_arithmetic_row9 (fun j => Fin.cases h0n15_arithmetic_row10 (fun j => Fin.cases h0n15_arithmetic_row11 (fun j => Fin.cases h0n15_arithmetic_row12 (fun j => Fin.cases h0n15_arithmetic_row13 (fun j => Fin.cases h0n15_arithmetic_row14 (fun j => Fin.cases h0n15_arithmetic_row15 (fun j => Fin.cases h0n15_arithmetic_row16 (fun j => Fin.cases h0n15_arithmetic_row17 (fun j => Fin.cases h0n15_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n15 : h0e15.toBi mapPolyEnv=h0p15 := by
  change BiPoly.mul (h0e11.toBi mapPolyEnv) (h0e14.toBi mapPolyEnv)=h0p15
  rw [h0n11, h0n14]
  exact h0n15_arithmetic

#print axioms h0n15_arithmetic
end StackSorting.RationalLift
