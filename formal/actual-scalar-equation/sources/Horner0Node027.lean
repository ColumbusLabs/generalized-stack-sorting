import BivariateRowEquality
import Horner0Base
import Horner0Node014
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p27 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 4014553884651904391), (Int.negSucc 20690980254530441567), (Int.ofNat 14995775856826891152), (Int.ofNat 107347520557469233440), (Int.negSucc 108058564703724553799)], [(Int.ofNat 0), (Int.ofNat 39210019768700471952), (Int.ofNat 215014698012851118144), (Int.negSucc 92468752191620070047), (Int.negSucc 1050817585651313955839), (Int.ofNat 977495875152078031632), (Int.negSucc 59182569491653903679)], [(Int.ofNat 0), (Int.negSucc 186189111051353353943), (Int.negSucc 998657192228577025967), (Int.ofNat 293086904108032667232), (Int.ofNat 4339267917581474836416), (Int.negSucc 3693623575234383996839), (Int.ofNat 269837494081494720912), (Int.negSucc 7803067872661566911)], [(Int.ofNat 0), (Int.ofNat 567842815657145751624), (Int.ofNat 2772017073721682352216), (Int.negSucc 809860382704450586447), (Int.negSucc 9561565978659662813423), (Int.ofNat 6854153401271829448872), (Int.negSucc 79430548170282338663), (Int.negSucc 9380540650304138975), (Int.ofNat 82250395527294720)], [(Int.ofNat 0), (Int.negSucc 1236269217180395724263), (Int.negSucc 5132856411641251061495), (Int.ofNat 1953274508871576963768), (Int.ofNat 11204892848447246610288), (Int.negSucc 4342284486302997219263), (Int.negSucc 1944612635257764467351), (Int.ofNat 128801187834252601608), (Int.negSucc 2998871132278291775), (Int.negSucc 208712063260799)], [(Int.ofNat 0), (Int.ofNat 2021720970187616982696), (Int.ofNat 6631072124067591113808), (Int.negSucc 3017152729551318677567), (Int.negSucc 4444028836848164435759), (Int.negSucc 6547539418968200184791), (Int.ofNat 5019069700431256769856), (Int.negSucc 121602395609410800671), (Int.negSucc 4971418502134281407), (Int.ofNat 15146361601303680)], [(Int.ofNat 0), (Int.negSucc 2548449615630844001033), (Int.negSucc 6024745125280925653427), (Int.ofNat 1843529743354053723786), (Int.negSucc 4892902618988832216551), (Int.ofNat 15288019406172325596546), (Int.negSucc 4262579174306173338899), (Int.negSucc 497574004325589900521), (Int.ofNat 28674447244023701952), (Int.negSucc 249425764885094111)], [(Int.ofNat 0), (Int.ofNat 2504194275454713390780), (Int.ofNat 3788927135025212556972), (Int.ofNat 2022120248468361524208), (Int.ofNat 6764193476424797050440), (Int.negSucc 10432015847753712771419), (Int.negSucc 1894504274367540869051), (Int.ofNat 1187157381908325091416), (Int.ofNat 3996960528412115424), (Int.negSucc 966798365959717055)], [(Int.ofNat 0), (Int.negSucc 1920334561037619208037), (Int.negSucc 1650200381123942156579), (Int.negSucc 5286898750679951149763), (Int.negSucc 2187271112147939908619), (Int.negSucc 1379999769055959030317), (Int.ofNat 6361704672488027923860), (Int.negSucc 627233002556510578535), (Int.negSucc 103555953084813416459), (Int.ofNat 896538278913702408)], [(Int.ofNat 0), (Int.ofNat 1141265092840210927800), (Int.ofNat 651047422453581070440), (Int.ofNat 5085809891545630491648), (Int.negSucc 597056125576060940543), (Int.ofNat 6247804287325320346752), (Int.negSucc 4007657213560910468879), (Int.negSucc 705166080877393843607), (Int.ofNat 87998824003569633864), (Int.ofNat 3246947290247502600)], [(Int.ofNat 0), (Int.negSucc 518209622209987500005), (Int.negSucc 455134584479112850895), (Int.negSucc 2670532689088737700487), (Int.negSucc 251877196733038687403), (Int.negSucc 3502493850296255655365), (Int.negSucc 436051054439516778227), (Int.ofNat 1003740599118768686658), (Int.ofNat 62907131239719295500), (Int.negSucc 3005154489226618097)], [(Int.ofNat 0), (Int.ofNat 175808800635950718612), (Int.ofNat 381277911478860475308), (Int.ofNat 737141891534257069548), (Int.ofNat 1190227293154932541452), (Int.ofNat 543705190290178795872), (Int.ofNat 1727834079869695260144), (Int.negSucc 262508717683778196923), (Int.negSucc 114096271415624200547), (Int.negSucc 2779152754832692487)], [(Int.ofNat 0), (Int.negSucc 43104458171087225225), (Int.negSucc 225600535348834105259), (Int.negSucc 62921990717967077045), (Int.negSucc 870368798423483601947), (Int.ofNat 102595448486068753572), (Int.negSucc 841863963718351451735), (Int.negSucc 228363719157066093389), (Int.ofNat 30538103421756361680), (Int.ofNat 3775559770897760016)], [(Int.ofNat 0), (Int.ofNat 7258053528471852504), (Int.ofNat 87303015794422220688), (Int.negSucc 3996614519785088783), (Int.ofNat 290511711231114454200), (Int.ofNat 35677334698595775792), (Int.ofNat 143930577912761483352), (Int.ofNat 183701882024242929360), (Int.ofNat 26541375962780800296), (Int.negSucc 151869821613721199)], [(Int.ofNat 0), (Int.negSucc 772806846215154167), (Int.negSucc 21916928133825276563), (Int.negSucc 13081451602376075309), (Int.negSucc 37443644140751993123), (Int.negSucc 63234966013280467541), (Int.ofNat 9556475941579317984), (Int.negSucc 49710685240551901967), (Int.negSucc 19829326024522457279), (Int.negSucc 1356379911396187847)], [(Int.ofNat 0), (Int.ofNat 44982407969178336), (Int.ofNat 3430503307964829960), (Int.ofNat 9255258756654576084), (Int.negSucc 5627784764666052179), (Int.ofNat 23619250464316168536), (Int.negSucc 6843646213891016975), (Int.ofNat 4551036598027494720), (Int.ofNat 4739686814841910272), (Int.ofNat 641802453932314368)], [(Int.ofNat 0), (Int.negSucc 1064468625203231), (Int.negSucc 297931775752888271), (Int.negSucc 2665935579400420913), (Int.ofNat 2954473744543531344), (Int.negSucc 4115581483724083871), (Int.ofNat 871801638839338752), (Int.ofNat 254810044593842832), (Int.negSucc 371760091888582655), (Int.negSucc 91736878750451711)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10186404585722496), (Int.ofNat 389326820597331264), (Int.negSucc 466607314799549207), (Int.ofNat 328613570399910960), (Int.negSucc 25525431461200895), (Int.negSucc 59267482046869247)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 24369632868281471), (Int.ofNat 30547029918301632), (Int.negSucc 9572579959176647)]]

theorem h0n27_arithmetic_row0 :
    (BiPoly.mul h0p26 h0p14).getD 0 []=h0p27.getD 0 [] := by
  decide +kernel

theorem h0n27_arithmetic_row1 :
    (BiPoly.mul h0p26 h0p14).getD 1 []=h0p27.getD 1 [] := by
  decide +kernel

theorem h0n27_arithmetic_row2 :
    (BiPoly.mul h0p26 h0p14).getD 2 []=h0p27.getD 2 [] := by
  decide +kernel

theorem h0n27_arithmetic_row3 :
    (BiPoly.mul h0p26 h0p14).getD 3 []=h0p27.getD 3 [] := by
  decide +kernel

theorem h0n27_arithmetic_row4 :
    (BiPoly.mul h0p26 h0p14).getD 4 []=h0p27.getD 4 [] := by
  decide +kernel

theorem h0n27_arithmetic_row5 :
    (BiPoly.mul h0p26 h0p14).getD 5 []=h0p27.getD 5 [] := by
  decide +kernel

theorem h0n27_arithmetic_row6 :
    (BiPoly.mul h0p26 h0p14).getD 6 []=h0p27.getD 6 [] := by
  decide +kernel

theorem h0n27_arithmetic_row7 :
    (BiPoly.mul h0p26 h0p14).getD 7 []=h0p27.getD 7 [] := by
  decide +kernel

theorem h0n27_arithmetic_row8 :
    (BiPoly.mul h0p26 h0p14).getD 8 []=h0p27.getD 8 [] := by
  decide +kernel

theorem h0n27_arithmetic_row9 :
    (BiPoly.mul h0p26 h0p14).getD 9 []=h0p27.getD 9 [] := by
  decide +kernel

theorem h0n27_arithmetic_row10 :
    (BiPoly.mul h0p26 h0p14).getD 10 []=h0p27.getD 10 [] := by
  decide +kernel

theorem h0n27_arithmetic_row11 :
    (BiPoly.mul h0p26 h0p14).getD 11 []=h0p27.getD 11 [] := by
  decide +kernel

theorem h0n27_arithmetic_row12 :
    (BiPoly.mul h0p26 h0p14).getD 12 []=h0p27.getD 12 [] := by
  decide +kernel

theorem h0n27_arithmetic_row13 :
    (BiPoly.mul h0p26 h0p14).getD 13 []=h0p27.getD 13 [] := by
  decide +kernel

theorem h0n27_arithmetic_row14 :
    (BiPoly.mul h0p26 h0p14).getD 14 []=h0p27.getD 14 [] := by
  decide +kernel

theorem h0n27_arithmetic_row15 :
    (BiPoly.mul h0p26 h0p14).getD 15 []=h0p27.getD 15 [] := by
  decide +kernel

theorem h0n27_arithmetic_row16 :
    (BiPoly.mul h0p26 h0p14).getD 16 []=h0p27.getD 16 [] := by
  decide +kernel

theorem h0n27_arithmetic_row17 :
    (BiPoly.mul h0p26 h0p14).getD 17 []=h0p27.getD 17 [] := by
  decide +kernel

theorem h0n27_arithmetic_row18 :
    (BiPoly.mul h0p26 h0p14).getD 18 []=h0p27.getD 18 [] := by
  decide +kernel

theorem h0n27_arithmetic : BiPoly.mul h0p26 h0p14=h0p27 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p26 h0p14).getD j.val []=h0p27.getD j.val [] :=
      (fun j => Fin.cases h0n27_arithmetic_row0 (fun j => Fin.cases h0n27_arithmetic_row1 (fun j => Fin.cases h0n27_arithmetic_row2 (fun j => Fin.cases h0n27_arithmetic_row3 (fun j => Fin.cases h0n27_arithmetic_row4 (fun j => Fin.cases h0n27_arithmetic_row5 (fun j => Fin.cases h0n27_arithmetic_row6 (fun j => Fin.cases h0n27_arithmetic_row7 (fun j => Fin.cases h0n27_arithmetic_row8 (fun j => Fin.cases h0n27_arithmetic_row9 (fun j => Fin.cases h0n27_arithmetic_row10 (fun j => Fin.cases h0n27_arithmetic_row11 (fun j => Fin.cases h0n27_arithmetic_row12 (fun j => Fin.cases h0n27_arithmetic_row13 (fun j => Fin.cases h0n27_arithmetic_row14 (fun j => Fin.cases h0n27_arithmetic_row15 (fun j => Fin.cases h0n27_arithmetic_row16 (fun j => Fin.cases h0n27_arithmetic_row17 (fun j => Fin.cases h0n27_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n27 : h0e27.toBi mapPolyEnv=h0p27 := by
  change BiPoly.mul (h0e26.toBi mapPolyEnv) (h0e14.toBi mapPolyEnv)=h0p27
  rw [h0n26, h0n14]
  exact h0n27_arithmetic

#print axioms h0n27_arithmetic
end StackSorting.RationalLift
