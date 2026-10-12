import BivariateRowEquality
import Horner5Base
import Horner5Node342
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p343 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 1393661376000), (Int.ofNat 2765966434560), (Int.negSucc 17921391620399), (Int.negSucc 29892298112639), (Int.ofNat 6377900510880), (Int.ofNat 40791996783360), (Int.ofNat 23815494838800)], [(Int.ofNat 0), (Int.negSucc 12128983338239), (Int.negSucc 18889075594367), (Int.ofNat 162953259980616), (Int.ofNat 229510774793880), (Int.negSucc 59554041525359), (Int.negSucc 283275371687759), (Int.negSucc 134100725240663), (Int.ofNat 1670446835640)], [(Int.ofNat 0), (Int.ofNat 47492825316480), (Int.ofNat 57960791407296), (Int.negSucc 654033775389767), (Int.negSucc 822749790607055), (Int.ofNat 190083013757280), (Int.ofNat 872532591046848), (Int.ofNat 383802079739832), (Int.ofNat 49707231840144), (Int.negSucc 4595806060559)], [(Int.ofNat 0), (Int.negSucc 110362314237119), (Int.negSucc 109835695324511), (Int.ofNat 1542528385726896), (Int.ofNat 1882676610132192), (Int.negSucc 190808699108831), (Int.negSucc 1505136761326799), (Int.negSucc 790865425242143), (Int.negSucc 260668102557455), (Int.ofNat 25990031340432), (Int.negSucc 878927718239)], [(Int.ofNat 0), (Int.ofNat 168977236003200), (Int.ofNat 154040747102208), (Int.negSucc 2393990358483563), (Int.negSucc 3144400301294807), (Int.negSucc 412976360462915), (Int.ofNat 1451062723848144), (Int.ofNat 1304445113359596), (Int.ofNat 548371436284968), (Int.negSucc 5163814504715), (Int.negSucc 381221182847), (Int.ofNat 4494811200)], [(Int.ofNat 0), (Int.negSucc 178857122622719), (Int.negSucc 181219782620159), (Int.ofNat 2585509524159948), (Int.ofNat 4060234988008896), (Int.ofNat 1780348061703684), (Int.negSucc 451891755808727), (Int.negSucc 1520695743359699), (Int.negSucc 626994705196775), (Int.negSucc 147224371263347), (Int.ofNat 11562759132600), (Int.negSucc 162074045759)], [(Int.ofNat 0), (Int.ofNat 133447227360640), (Int.ofNat 182597767460672), (Int.negSucc 1992499027101315), (Int.negSucc 4098055678827135), (Int.negSucc 3225389855275239), (Int.negSucc 858149482613703), (Int.ofNat 854447833825956), (Int.ofNat 490841831164144), (Int.ofNat 294313456409776), (Int.negSucc 5447310149559), (Int.negSucc 333535539839)], [(Int.ofNat 0), (Int.negSucc 70138303902079), (Int.negSucc 146831898350655), (Int.ofNat 1094696732018876), (Int.ofNat 3199228313618324), (Int.ofNat 3721575790906496), (Int.ofNat 1771078769607836), (Int.ofNat 371661176949324), (Int.negSucc 307015050326659), (Int.negSucc 203349250188967), (Int.negSucc 35564028749403), (Int.ofNat 1284868047120)], [(Int.ofNat 0), (Int.ofNat 25436278587520), (Int.ofNat 86809491924032), (Int.negSucc 414100040817867), (Int.negSucc 1901713651159335), (Int.negSucc 2992708918817199), (Int.negSucc 2041380285120471), (Int.negSucc 1075490567499635), (Int.negSucc 3047027589967), (Int.ofNat 6580454225644), (Int.ofNat 51905523332504), (Int.ofNat 1515433838940)], [(Int.ofNat 0), (Int.negSucc 6060440895999), (Int.negSucc 35375483570047), (Int.ofNat 97101291162412), (Int.ofNat 847789394717972), (Int.ofNat 1728789584699268), (Int.ofNat 1688211062725248), (Int.ofNat 971644721016432), (Int.ofNat 317115023367180), (Int.ofNat 67409547184848), (Int.negSucc 12838011993311), (Int.negSucc 3107143288079)], [(Int.ofNat 0), (Int.ofNat 853852843520), (Int.ofNat 9291278287360), (Int.negSucc 9241326981859), (Int.negSucc 280512048549039), (Int.negSucc 724747159149395), (Int.negSucc 997052764366055), (Int.negSucc 598753033134119), (Int.negSucc 345719966277983), (Int.negSucc 67290039263267), (Int.negSucc 17946669083039), (Int.negSucc 195483961439)], [(Int.ofNat 0), (Int.negSucc 53916491199), (Int.negSucc 1407106877023), (Int.negSucc 1434863678491), (Int.ofNat 69350024802476), (Int.ofNat 222013574549304), (Int.ofNat 405152167094172), (Int.ofNat 301913707980432), (Int.ofNat 186739577041056), (Int.ofNat 54828197263488), (Int.ofNat 15765578966112), (Int.ofNat 1827809828640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 92999720640), (Int.ofNat 465221727000), (Int.negSucc 13208228220623), (Int.negSucc 51593766586403), (Int.negSucc 107451978413447), (Int.negSucc 119976733891259), (Int.negSucc 64741426143359), (Int.negSucc 28836506497535), (Int.negSucc 6680969983871), (Int.negSucc 758009437199)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 33630702479), (Int.ofNat 1891742840052), (Int.ofNat 10141949481936), (Int.ofNat 16777138111008), (Int.ofNat 33203809775664), (Int.ofNat 16764124159296), (Int.ofNat 9082622606688), (Int.ofNat 1706361730848), (Int.ofNat 77100906240)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 149852143151), (Int.negSucc 1716077712491), (Int.negSucc 1427496621407), (Int.negSucc 5276450748671), (Int.negSucc 3524479848575), (Int.negSucc 1765101162239), (Int.negSucc 175195042559)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 165003028992), (Int.ofNat 199076294592), (Int.ofNat 200066836032), (Int.ofNat 620667523296), (Int.ofNat 161073826560)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 38482506431), (Int.ofNat 42130991376), (Int.negSucc 62979690239)]]

theorem h5n343_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p342).getD 0 []=h5p343.getD 0 [] := by
  decide +kernel

theorem h5n343_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p342).getD 1 []=h5p343.getD 1 [] := by
  decide +kernel

theorem h5n343_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p342).getD 2 []=h5p343.getD 2 [] := by
  decide +kernel

theorem h5n343_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p342).getD 3 []=h5p343.getD 3 [] := by
  decide +kernel

theorem h5n343_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p342).getD 4 []=h5p343.getD 4 [] := by
  decide +kernel

theorem h5n343_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p342).getD 5 []=h5p343.getD 5 [] := by
  decide +kernel

theorem h5n343_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p342).getD 6 []=h5p343.getD 6 [] := by
  decide +kernel

theorem h5n343_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p342).getD 7 []=h5p343.getD 7 [] := by
  decide +kernel

theorem h5n343_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p342).getD 8 []=h5p343.getD 8 [] := by
  decide +kernel

theorem h5n343_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p342).getD 9 []=h5p343.getD 9 [] := by
  decide +kernel

theorem h5n343_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p342).getD 10 []=h5p343.getD 10 [] := by
  decide +kernel

theorem h5n343_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p342).getD 11 []=h5p343.getD 11 [] := by
  decide +kernel

theorem h5n343_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p342).getD 12 []=h5p343.getD 12 [] := by
  decide +kernel

theorem h5n343_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p342).getD 13 []=h5p343.getD 13 [] := by
  decide +kernel

theorem h5n343_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p342).getD 14 []=h5p343.getD 14 [] := by
  decide +kernel

theorem h5n343_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p342).getD 15 []=h5p343.getD 15 [] := by
  decide +kernel

theorem h5n343_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p342).getD 16 []=h5p343.getD 16 [] := by
  decide +kernel

theorem h5n343_arithmetic : BiPoly.mul h5p5 h5p342=h5p343 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p342).getD j.val []=h5p343.getD j.val [] :=
      (fun j => Fin.cases h5n343_arithmetic_row0 (fun j => Fin.cases h5n343_arithmetic_row1 (fun j => Fin.cases h5n343_arithmetic_row2 (fun j => Fin.cases h5n343_arithmetic_row3 (fun j => Fin.cases h5n343_arithmetic_row4 (fun j => Fin.cases h5n343_arithmetic_row5 (fun j => Fin.cases h5n343_arithmetic_row6 (fun j => Fin.cases h5n343_arithmetic_row7 (fun j => Fin.cases h5n343_arithmetic_row8 (fun j => Fin.cases h5n343_arithmetic_row9 (fun j => Fin.cases h5n343_arithmetic_row10 (fun j => Fin.cases h5n343_arithmetic_row11 (fun j => Fin.cases h5n343_arithmetic_row12 (fun j => Fin.cases h5n343_arithmetic_row13 (fun j => Fin.cases h5n343_arithmetic_row14 (fun j => Fin.cases h5n343_arithmetic_row15 (fun j => Fin.cases h5n343_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n343 : h5e343.toBi mapPolyEnv=h5p343 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e342.toBi mapPolyEnv)=h5p343
  rw [h5n5, h5n342]
  exact h5n343_arithmetic

#print axioms h5n343_arithmetic
end StackSorting.RationalLift
