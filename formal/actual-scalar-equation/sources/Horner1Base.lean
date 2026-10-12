import Horner1Expressions
import RationalMapPolynomials
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p0 : BiPoly.Poly := mapPolyEnv 0
theorem h1n0 : h1e0.toBi mapPolyEnv=h1p0 := rfl

noncomputable def h1p1 : BiPoly.Poly := mapPolyEnv 2
theorem h1n1 : h1e1.toBi mapPolyEnv=h1p1 := rfl

noncomputable def h1p2 : BiPoly.Poly := mapPolyEnv 4
theorem h1n2 : h1e2.toBi mapPolyEnv=h1p2 := rfl

noncomputable def h1p3 : BiPoly.Poly := mapPolyEnv 5
theorem h1n3 : h1e3.toBi mapPolyEnv=h1p3 := rfl

noncomputable def h1p4 : BiPoly.Poly := mapPolyEnv 6
theorem h1n4 : h1e4.toBi mapPolyEnv=h1p4 := rfl

noncomputable def h1p5 : BiPoly.Poly := mapPolyEnv 7
theorem h1n5 : h1e5.toBi mapPolyEnv=h1p5 := rfl

noncomputable def h1p6 : BiPoly.Poly := mapPolyEnv 8
theorem h1n6 : h1e6.toBi mapPolyEnv=h1p6 := rfl

noncomputable def h1p7 : BiPoly.Poly := [[(Int.ofNat 24)]]
theorem h1n7 : h1e7.toBi mapPolyEnv=h1p7 := rfl

noncomputable def h1p8 : BiPoly.Poly := [[(Int.ofNat 96)]]
theorem h1n8 : h1e8.toBi mapPolyEnv=h1p8 := rfl

noncomputable def h1p9 : BiPoly.Poly := mapPolyEnv 10
theorem h1n9 : h1e9.toBi mapPolyEnv=h1p9 := rfl

noncomputable def h1p14 : BiPoly.Poly := [[(Int.negSucc 35)]]
theorem h1n14 : h1e14.toBi mapPolyEnv=h1p14 := rfl

noncomputable def h1p21 : BiPoly.Poly := [[(Int.negSucc 95)]]
theorem h1n21 : h1e21.toBi mapPolyEnv=h1p21 := rfl

noncomputable def h1p23 : BiPoly.Poly := mapPolyEnv 9
theorem h1n23 : h1e23.toBi mapPolyEnv=h1p23 := rfl

noncomputable def h1p37 : BiPoly.Poly := [[(Int.negSucc 11)]]
theorem h1n37 : h1e37.toBi mapPolyEnv=h1p37 := rfl

noncomputable def h1p38 : BiPoly.Poly := [[(Int.negSucc 47)]]
theorem h1n38 : h1e38.toBi mapPolyEnv=h1p38 := rfl

noncomputable def h1p43 : BiPoly.Poly := [[(Int.ofNat 18)]]
theorem h1n43 : h1e43.toBi mapPolyEnv=h1p43 := rfl

noncomputable def h1p47 : BiPoly.Poly := [[(Int.ofNat 48)]]
theorem h1n47 : h1e47.toBi mapPolyEnv=h1p47 := rfl

noncomputable def h1p49 : BiPoly.Poly := [[(Int.negSucc 17)]]
theorem h1n49 : h1e49.toBi mapPolyEnv=h1p49 := rfl

noncomputable def h1p57 : BiPoly.Poly := mapPolyEnv 3
theorem h1n57 : h1e57.toBi mapPolyEnv=h1p57 := rfl

noncomputable def h1p58 : BiPoly.Poly := [[(Int.ofNat 4)]]
theorem h1n58 : h1e58.toBi mapPolyEnv=h1p58 := rfl

noncomputable def h1p59 : BiPoly.Poly := [[(Int.ofNat 8)]]
theorem h1n59 : h1e59.toBi mapPolyEnv=h1p59 := rfl

noncomputable def h1p64 : BiPoly.Poly := [[(Int.negSucc 3)]]
theorem h1n64 : h1e64.toBi mapPolyEnv=h1p64 := rfl

noncomputable def h1p70 : BiPoly.Poly := [[(Int.ofNat 16)]]
theorem h1n70 : h1e70.toBi mapPolyEnv=h1p70 := rfl

noncomputable def h1p74 : BiPoly.Poly := [[(Int.negSucc 15)]]
theorem h1n74 : h1e74.toBi mapPolyEnv=h1p74 := rfl

noncomputable def h1p83 : BiPoly.Poly := [[(Int.ofNat 12)]]
theorem h1n83 : h1e83.toBi mapPolyEnv=h1p83 := rfl

noncomputable def h1p93 : BiPoly.Poly := mapPolyEnv 1
theorem h1n93 : h1e93.toBi mapPolyEnv=h1p93 := rfl

noncomputable def h1p94 : BiPoly.Poly := [[(Int.negSucc 31)]]
theorem h1n94 : h1e94.toBi mapPolyEnv=h1p94 := rfl

noncomputable def h1p99 : BiPoly.Poly := [[(Int.ofNat 10)]]
theorem h1n99 : h1e99.toBi mapPolyEnv=h1p99 := rfl

noncomputable def h1p112 : BiPoly.Poly := [[(Int.ofNat 2)]]
theorem h1n112 : h1e112.toBi mapPolyEnv=h1p112 := rfl

noncomputable def h1p117 : BiPoly.Poly := [[(Int.negSucc 4)]]
theorem h1n117 : h1e117.toBi mapPolyEnv=h1p117 := rfl

noncomputable def h1p122 : BiPoly.Poly := [[(Int.ofNat 5)]]
theorem h1n122 : h1e122.toBi mapPolyEnv=h1p122 := rfl
end StackSorting.RationalLift
