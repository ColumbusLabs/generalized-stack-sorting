import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p24 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 472261338), (Int.ofNat 1217015676), (Int.negSucc 2450153789)], [(Int.ofNat 0), (Int.negSucc 2306280713), (Int.negSucc 6703599179), (Int.ofNat 10748750526), (Int.negSucc 670962071)], [(Int.ofNat 0), (Int.ofNat 5320050962), (Int.ofNat 12293004262), (Int.negSucc 16403256159), (Int.ofNat 117391062), (Int.ofNat 3405160)], [(Int.ofNat 0), (Int.negSucc 7419367906), (Int.negSucc 8377521066), (Int.ofNat 4036034801), (Int.ofNat 4035733571), (Int.negSucc 123557267)], [(Int.ofNat 0), (Int.ofNat 6517991433), (Int.ofNat 402433922), (Int.ofNat 12339545263), (Int.negSucc 5980552105), (Int.negSucc 206952321)], [(Int.ofNat 0), (Int.negSucc 3504802104), (Int.ofNat 987248176), (Int.negSucc 10739512338), (Int.ofNat 583467373), (Int.ofNat 377382165)], [(Int.ofNat 0), (Int.ofNat 1074940707), (Int.ofNat 858249577), (Int.ofNat 2281968902), (Int.ofNat 2850082835), (Int.ofNat 90990270)], [(Int.ofNat 0), (Int.negSucc 162483781), (Int.negSucc 936223362), (Int.ofNat 334049373), (Int.negSucc 1338212759), (Int.negSucc 249725645)], [(Int.ofNat 0), (Int.ofNat 7690068), (Int.ofNat 298735941), (Int.negSucc 165027065), (Int.ofNat 144652032), (Int.ofNat 71389728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 36794951), (Int.ofNat 23061006)]]

theorem h4n24_arithmetic : BiPoly.mul h4p7 h4p9=h4p24 := by
  decide +kernel

theorem h4n24 : h4e24.toBi mapPolyEnv=h4p24 := by
  change BiPoly.mul (h4e7.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p24
  rw [h4n7, h4n9]
  exact h4n24_arithmetic

#print axioms h4n24_arithmetic
end StackSorting.RationalLift
