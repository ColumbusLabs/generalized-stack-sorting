import Horner2Expressions
import RationalMapPolynomials
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p0 : BiPoly.Poly := mapPolyEnv 0
theorem h2n0 : h2e0.toBi mapPolyEnv=h2p0 := rfl

noncomputable def h2p1 : BiPoly.Poly := mapPolyEnv 2
theorem h2n1 : h2e1.toBi mapPolyEnv=h2p1 := rfl

noncomputable def h2p2 : BiPoly.Poly := mapPolyEnv 5
theorem h2n2 : h2e2.toBi mapPolyEnv=h2p2 := rfl

noncomputable def h2p4 : BiPoly.Poly := mapPolyEnv 7
theorem h2n4 : h2e4.toBi mapPolyEnv=h2p4 := rfl

noncomputable def h2p5 : BiPoly.Poly := mapPolyEnv 9
theorem h2n5 : h2e5.toBi mapPolyEnv=h2p5 := rfl

noncomputable def h2p6 : BiPoly.Poly := [[(Int.ofNat 12)]]
theorem h2n6 : h2e6.toBi mapPolyEnv=h2p6 := rfl

noncomputable def h2p7 : BiPoly.Poly := [[(Int.ofNat 48)]]
theorem h2n7 : h2e7.toBi mapPolyEnv=h2p7 := rfl

noncomputable def h2p8 : BiPoly.Poly := mapPolyEnv 10
theorem h2n8 : h2e8.toBi mapPolyEnv=h2p8 := rfl

noncomputable def h2p13 : BiPoly.Poly := [[(Int.negSucc 17)]]
theorem h2n13 : h2e13.toBi mapPolyEnv=h2p13 := rfl

noncomputable def h2p14 : BiPoly.Poly := mapPolyEnv 6
theorem h2n14 : h2e14.toBi mapPolyEnv=h2p14 := rfl

noncomputable def h2p20 : BiPoly.Poly := mapPolyEnv 4
theorem h2n20 : h2e20.toBi mapPolyEnv=h2p20 := rfl

noncomputable def h2p21 : BiPoly.Poly := [[(Int.negSucc 23)]]
theorem h2n21 : h2e21.toBi mapPolyEnv=h2p21 := rfl

noncomputable def h2p22 : BiPoly.Poly := [[(Int.negSucc 95)]]
theorem h2n22 : h2e22.toBi mapPolyEnv=h2p22 := rfl

noncomputable def h2p27 : BiPoly.Poly := [[(Int.ofNat 36)]]
theorem h2n27 : h2e27.toBi mapPolyEnv=h2p27 := rfl

noncomputable def h2p34 : BiPoly.Poly := mapPolyEnv 3
theorem h2n34 : h2e34.toBi mapPolyEnv=h2p34 := rfl

noncomputable def h2p35 : BiPoly.Poly := mapPolyEnv 8
theorem h2n35 : h2e35.toBi mapPolyEnv=h2p35 := rfl

noncomputable def h2p37 : BiPoly.Poly := [[(Int.ofNat 40)]]
theorem h2n37 : h2e37.toBi mapPolyEnv=h2p37 := rfl

noncomputable def h2p42 : BiPoly.Poly := [[(Int.negSucc 47)]]
theorem h2n42 : h2e42.toBi mapPolyEnv=h2p42 := rfl

noncomputable def h2p49 : BiPoly.Poly := [[(Int.negSucc 11)]]
theorem h2n49 : h2e49.toBi mapPolyEnv=h2p49 := rfl

noncomputable def h2p51 : BiPoly.Poly := [[(Int.ofNat 4)]]
theorem h2n51 : h2e51.toBi mapPolyEnv=h2p51 := rfl

noncomputable def h2p70 : BiPoly.Poly := mapPolyEnv 1
theorem h2n70 : h2e70.toBi mapPolyEnv=h2p70 := rfl

noncomputable def h2p71 : BiPoly.Poly := [[(Int.negSucc 1)]]
theorem h2n71 : h2e71.toBi mapPolyEnv=h2p71 := rfl

noncomputable def h2p72 : BiPoly.Poly := [[(Int.negSucc 15)]]
theorem h2n72 : h2e72.toBi mapPolyEnv=h2p72 := rfl

noncomputable def h2p77 : BiPoly.Poly := [[(Int.ofNat 5)]]
theorem h2n77 : h2e77.toBi mapPolyEnv=h2p77 := rfl

noncomputable def h2p81 : BiPoly.Poly := [[(Int.ofNat 32)]]
theorem h2n81 : h2e81.toBi mapPolyEnv=h2p81 := rfl

noncomputable def h2p86 : BiPoly.Poly := [[(Int.negSucc 9)]]
theorem h2n86 : h2e86.toBi mapPolyEnv=h2p86 := rfl

noncomputable def h2p94 : BiPoly.Poly := [[(Int.negSucc 7)]]
theorem h2n94 : h2e94.toBi mapPolyEnv=h2p94 := rfl

noncomputable def h2p99 : BiPoly.Poly := [[(Int.ofNat 16)]]
theorem h2n99 : h2e99.toBi mapPolyEnv=h2p99 := rfl
end StackSorting.RationalLift
