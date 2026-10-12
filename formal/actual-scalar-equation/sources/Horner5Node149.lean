import BivariateRowEquality
import Horner5Base
import Horner5Node148
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p149 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1967092907507711), (Int.negSucc 12377975439403007), (Int.ofNat 75141875704207104), (Int.negSucc 148370205024527615), (Int.ofNat 790719761597806080), (Int.ofNat 591711562426387968), (Int.negSucc 1949435772961713407), (Int.negSucc 1131779267278278911), (Int.ofNat 921160086053031936), (Int.ofNat 536434742801645568)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 16739897672540160), (Int.ofNat 92944293092683776), (Int.negSucc 627141146956411391), (Int.ofNat 1561385528633143296), (Int.negSucc 8333540449074240767), (Int.negSucc 4814885782849969151), (Int.ofNat 15336175314729682944), (Int.ofNat 6293411382777394176), (Int.negSucc 5869668141997814015), (Int.negSucc 1891572458290827263), (Int.ofNat 298019301556469760)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 63719181297881087), (Int.negSucc 315053723935111679), (Int.ofNat 2250088306088794560), (Int.negSucc 6393254023246510271), (Int.ofNat 38673168502519011264), (Int.ofNat 17002692476753941824), (Int.negSucc 51373572128898676415), (Int.negSucc 15813856942019144255), (Int.ofNat 13095547558083942720), (Int.ofNat 2438213355906887616), (Int.negSucc 256439308335148031), (Int.ofNat 41391569660620800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 142835431248936960), (Int.ofNat 643605514556411904), (Int.negSucc 4553690140219438655), (Int.ofNat 13150060910418095232), (Int.negSucc 102896718138224107967), (Int.negSucc 38950906279130390783), (Int.ofNat 90260344093221314112), (Int.ofNat 29225722485184703616), (Int.negSucc 7732838715544331327), (Int.negSucc 2945438836375348223), (Int.negSucc 1403832019814198783), (Int.ofNat 94465181324513280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 208713395982514175), (Int.negSucc 893743544176733951), (Int.ofNat 5725520332426205760), (Int.negSucc 12957487334307105983), (Int.ofNat 173374483217805130752), (Int.ofNat 77937343270637299200), (Int.negSucc 77504581445644596671), (Int.negSucc 53334141604539185087), (Int.negSucc 16242117118155521663), (Int.ofNat 6040004284039008384), (Int.ofNat 2495119058360656128), (Int.negSucc 223945424883087359)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 207378249457594368), (Int.ofNat 896132800426298112), (Int.negSucc 4674469304953457087), (Int.ofNat 32119032358821888), (Int.negSucc 194604739749879398399), (Int.negSucc 144028784417073413375), (Int.negSucc 1001664976502639807), (Int.ofNat 77396327083510415616), (Int.ofNat 35274544272306667392), (Int.negSucc 4544141166231597311), (Int.negSucc 774916948314656255), (Int.negSucc 269605063605712895)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 141061726263790847), (Int.negSucc 655574891047438079), (Int.ofNat 2627194822385351808), (Int.ofNat 16046522792393860992), (Int.ofNat 151406856963531516288), (Int.ofNat 209115845400531276672), (Int.ofNat 86476772784619128768), (Int.negSucc 59606610701028309695), (Int.negSucc 32903326310311501247), (Int.negSucc 6902939722037891903), (Int.negSucc 606381753995520767), (Int.ofNat 641245516393623552)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 63445568346342144), (Int.ofNat 326338731863032320), (Int.negSucc 1272270891904383359), (Int.negSucc 21138197868751749119), (Int.negSucc 87362418470498561663), (Int.negSucc 212618195602787719679), (Int.negSucc 127963600391306258495), (Int.negSucc 3345731155372374143), (Int.ofNat 20727154580859251136), (Int.ofNat 14057913418776006912), (Int.ofNat 401486919968964096), (Int.negSucc 61457523561427967)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 16287999233872127), (Int.negSucc 77985285279231743), (Int.ofNat 782887063019360640), (Int.ofNat 14740434136301036160), (Int.ofNat 42871682078366611200), (Int.ofNat 145827183176273182464), (Int.ofNat 124402393266699487680), (Int.ofNat 52738590250685656512), (Int.negSucc 6078836637783899135), (Int.negSucc 7872226281503889407), (Int.negSucc 1000241386978728959), (Int.negSucc 445796276976018431)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 438668956720896), (Int.negSucc 24248503633976831), (Int.negSucc 531228847165813631), (Int.negSucc 6426665260643296511), (Int.negSucc 20243102196811431167), (Int.negSucc 67250026988911703807), (Int.negSucc 90501851837515023935), (Int.negSucc 55371900606448769279), (Int.negSucc 8823698116204131071), (Int.negSucc 311522618967538175), (Int.ofNat 1406751911022486528), (Int.ofNat 188618435134009344)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1341909589895424), (Int.ofNat 29780557845970176), (Int.ofNat 275142395674427328), (Int.ofNat 1877566177047495744), (Int.ofNat 8416960681038812352), (Int.ofNat 21626314810584886080), (Int.ofNat 46684612531073182464), (Int.ofNat 34315670384328741120), (Int.ofNat 14235445472168524032), (Int.ofNat 2546373362906840832), (Int.negSucc 306083954187574271), (Int.ofNat 80601101293289472)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 513187689699071), (Int.negSucc 12098541258302975), (Int.negSucc 96292861749117503), (Int.negSucc 414563373018520703), (Int.negSucc 2502987476151185855), (Int.negSucc 5511617211718520063), (Int.negSucc 15695793988066054655), (Int.negSucc 15636758754465331199), (Int.negSucc 9292777730478468863), (Int.negSucc 1957907794623012863), (Int.negSucc 489705493725186047), (Int.negSucc 50664428012335103)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 89326416985344), (Int.ofNat 2522227909271040), (Int.ofNat 21950668098821952), (Int.ofNat 83688601119711552), (Int.ofNat 451296897280128000), (Int.ofNat 1286775297607265280), (Int.ofNat 3172765147945413120), (Int.ofNat 5303325279637283328), (Int.ofNat 3348863372289595392), (Int.ofNat 1145439111915270144), (Int.ofNat 292952891022188544), (Int.ofNat 4300474195980288)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6468313750271), (Int.negSucc 248717265742079), (Int.negSucc 3033795902415551), (Int.negSucc 14727719940247295), (Int.negSucc 44630878200986879), (Int.negSucc 233871968423259647), (Int.negSucc 377158416434698751), (Int.negSucc 1141939634377015295), (Int.negSucc 785778382525575167), (Int.negSucc 409101661446451199), (Int.negSucc 43769067828645887)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7056342273024), (Int.ofNat 203449910851584), (Int.ofNat 1540077061079808), (Int.ofNat 3275384077967616), (Int.ofNat 20436466450256640), (Int.ofNat 38740052516447232), (Int.ofNat 108955070501437440), (Int.ofNat 148471370370367488), (Int.ofNat 56689217454182400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1924456983551), (Int.negSucc 51470401287167), (Int.negSucc 306127377070847), (Int.negSucc 13067932041215), (Int.negSucc 4227258108671999), (Int.ofNat 394332451061760), (Int.negSucc 17220623821516799)]]

theorem h5n149_arithmetic_row0 :
    (BiPoly.mul h5p3 h5p148).getD 0 []=h5p149.getD 0 [] := by
  decide +kernel

theorem h5n149_arithmetic_row1 :
    (BiPoly.mul h5p3 h5p148).getD 1 []=h5p149.getD 1 [] := by
  decide +kernel

theorem h5n149_arithmetic_row2 :
    (BiPoly.mul h5p3 h5p148).getD 2 []=h5p149.getD 2 [] := by
  decide +kernel

theorem h5n149_arithmetic_row3 :
    (BiPoly.mul h5p3 h5p148).getD 3 []=h5p149.getD 3 [] := by
  decide +kernel

theorem h5n149_arithmetic_row4 :
    (BiPoly.mul h5p3 h5p148).getD 4 []=h5p149.getD 4 [] := by
  decide +kernel

theorem h5n149_arithmetic_row5 :
    (BiPoly.mul h5p3 h5p148).getD 5 []=h5p149.getD 5 [] := by
  decide +kernel

theorem h5n149_arithmetic_row6 :
    (BiPoly.mul h5p3 h5p148).getD 6 []=h5p149.getD 6 [] := by
  decide +kernel

theorem h5n149_arithmetic_row7 :
    (BiPoly.mul h5p3 h5p148).getD 7 []=h5p149.getD 7 [] := by
  decide +kernel

theorem h5n149_arithmetic_row8 :
    (BiPoly.mul h5p3 h5p148).getD 8 []=h5p149.getD 8 [] := by
  decide +kernel

theorem h5n149_arithmetic_row9 :
    (BiPoly.mul h5p3 h5p148).getD 9 []=h5p149.getD 9 [] := by
  decide +kernel

theorem h5n149_arithmetic_row10 :
    (BiPoly.mul h5p3 h5p148).getD 10 []=h5p149.getD 10 [] := by
  decide +kernel

theorem h5n149_arithmetic_row11 :
    (BiPoly.mul h5p3 h5p148).getD 11 []=h5p149.getD 11 [] := by
  decide +kernel

theorem h5n149_arithmetic_row12 :
    (BiPoly.mul h5p3 h5p148).getD 12 []=h5p149.getD 12 [] := by
  decide +kernel

theorem h5n149_arithmetic_row13 :
    (BiPoly.mul h5p3 h5p148).getD 13 []=h5p149.getD 13 [] := by
  decide +kernel

theorem h5n149_arithmetic_row14 :
    (BiPoly.mul h5p3 h5p148).getD 14 []=h5p149.getD 14 [] := by
  decide +kernel

theorem h5n149_arithmetic_row15 :
    (BiPoly.mul h5p3 h5p148).getD 15 []=h5p149.getD 15 [] := by
  decide +kernel

theorem h5n149_arithmetic : BiPoly.mul h5p3 h5p148=h5p149 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h5p3 h5p148).getD j.val []=h5p149.getD j.val [] :=
      (fun j => Fin.cases h5n149_arithmetic_row0 (fun j => Fin.cases h5n149_arithmetic_row1 (fun j => Fin.cases h5n149_arithmetic_row2 (fun j => Fin.cases h5n149_arithmetic_row3 (fun j => Fin.cases h5n149_arithmetic_row4 (fun j => Fin.cases h5n149_arithmetic_row5 (fun j => Fin.cases h5n149_arithmetic_row6 (fun j => Fin.cases h5n149_arithmetic_row7 (fun j => Fin.cases h5n149_arithmetic_row8 (fun j => Fin.cases h5n149_arithmetic_row9 (fun j => Fin.cases h5n149_arithmetic_row10 (fun j => Fin.cases h5n149_arithmetic_row11 (fun j => Fin.cases h5n149_arithmetic_row12 (fun j => Fin.cases h5n149_arithmetic_row13 (fun j => Fin.cases h5n149_arithmetic_row14 (fun j => Fin.cases h5n149_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n149 : h5e149.toBi mapPolyEnv=h5p149 := by
  change BiPoly.mul (h5e3.toBi mapPolyEnv) (h5e148.toBi mapPolyEnv)=h5p149
  rw [h5n3, h5n148]
  exact h5n149_arithmetic

#print axioms h5n149_arithmetic
end StackSorting.RationalLift
