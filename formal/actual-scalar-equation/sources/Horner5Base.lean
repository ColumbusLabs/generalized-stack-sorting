import Horner5Expressions
import RationalMapPolynomials
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p0 : BiPoly.Poly := mapPolyEnv 0
theorem h5n0 : h5e0.toBi mapPolyEnv=h5p0 := rfl

noncomputable def h5p1 : BiPoly.Poly := mapPolyEnv 1
theorem h5n1 : h5e1.toBi mapPolyEnv=h5p1 := rfl

noncomputable def h5p2 : BiPoly.Poly := mapPolyEnv 2
theorem h5n2 : h5e2.toBi mapPolyEnv=h5p2 := rfl

noncomputable def h5p3 : BiPoly.Poly := mapPolyEnv 4
theorem h5n3 : h5e3.toBi mapPolyEnv=h5p3 := rfl

noncomputable def h5p4 : BiPoly.Poly := mapPolyEnv 5
theorem h5n4 : h5e4.toBi mapPolyEnv=h5p4 := rfl

noncomputable def h5p5 : BiPoly.Poly := mapPolyEnv 7
theorem h5n5 : h5e5.toBi mapPolyEnv=h5p5 := rfl

noncomputable def h5p6 : BiPoly.Poly := mapPolyEnv 8
theorem h5n6 : h5e6.toBi mapPolyEnv=h5p6 := rfl

noncomputable def h5p7 : BiPoly.Poly := [[(Int.ofNat 96)]]
theorem h5n7 : h5e7.toBi mapPolyEnv=h5p7 := rfl

noncomputable def h5p8 : BiPoly.Poly := [[(Int.negSucc 95)]]
theorem h5n8 : h5e8.toBi mapPolyEnv=h5p8 := rfl

noncomputable def h5p9 : BiPoly.Poly := mapPolyEnv 11
theorem h5n9 : h5e9.toBi mapPolyEnv=h5p9 := rfl

noncomputable def h5p11 : BiPoly.Poly := mapPolyEnv 10
theorem h5n11 : h5e11.toBi mapPolyEnv=h5p11 := rfl

noncomputable def h5p12 : BiPoly.Poly := [[(Int.negSucc 191)]]
theorem h5n12 : h5e12.toBi mapPolyEnv=h5p12 := rfl

noncomputable def h5p14 : BiPoly.Poly := [[(Int.ofNat 288)]]
theorem h5n14 : h5e14.toBi mapPolyEnv=h5p14 := rfl

noncomputable def h5p22 : BiPoly.Poly := mapPolyEnv 9
theorem h5n22 : h5e22.toBi mapPolyEnv=h5p22 := rfl

noncomputable def h5p24 : BiPoly.Poly := [[(Int.ofNat 72)]]
theorem h5n24 : h5e24.toBi mapPolyEnv=h5p24 := rfl

noncomputable def h5p25 : BiPoly.Poly := [[(Int.negSucc 71)]]
theorem h5n25 : h5e25.toBi mapPolyEnv=h5p25 := rfl

noncomputable def h5p34 : BiPoly.Poly := mapPolyEnv 6
theorem h5n34 : h5e34.toBi mapPolyEnv=h5p34 := rfl

noncomputable def h5p35 : BiPoly.Poly := [[(Int.negSucc 143)]]
theorem h5n35 : h5e35.toBi mapPolyEnv=h5p35 := rfl

noncomputable def h5p36 : BiPoly.Poly := [[(Int.ofNat 144)]]
theorem h5n36 : h5e36.toBi mapPolyEnv=h5p36 := rfl

noncomputable def h5p38 : BiPoly.Poly := [[(Int.negSucc 287)]]
theorem h5n38 : h5e38.toBi mapPolyEnv=h5p38 := rfl

noncomputable def h5p61 : BiPoly.Poly := [[(Int.ofNat 192)]]
theorem h5n61 : h5e61.toBi mapPolyEnv=h5p61 := rfl

noncomputable def h5p69 : BiPoly.Poly := [[(Int.negSucc 179)]]
theorem h5n69 : h5e69.toBi mapPolyEnv=h5p69 := rfl

noncomputable def h5p71 : BiPoly.Poly := [[(Int.ofNat 180)]]
theorem h5n71 : h5e71.toBi mapPolyEnv=h5p71 := rfl

noncomputable def h5p91 : BiPoly.Poly := [[(Int.ofNat 24)]]
theorem h5n91 : h5e91.toBi mapPolyEnv=h5p91 := rfl

noncomputable def h5p92 : BiPoly.Poly := [[(Int.negSucc 23)]]
theorem h5n92 : h5e92.toBi mapPolyEnv=h5p92 := rfl

noncomputable def h5p94 : BiPoly.Poly := [[(Int.negSucc 47)]]
theorem h5n94 : h5e94.toBi mapPolyEnv=h5p94 := rfl

noncomputable def h5p103 : BiPoly.Poly := [[(Int.ofNat 54)]]
theorem h5n103 : h5e103.toBi mapPolyEnv=h5p103 := rfl

noncomputable def h5p104 : BiPoly.Poly := [[(Int.negSucc 53)]]
theorem h5n104 : h5e104.toBi mapPolyEnv=h5p104 := rfl

noncomputable def h5p113 : BiPoly.Poly := [[(Int.negSucc 35)]]
theorem h5n113 : h5e113.toBi mapPolyEnv=h5p113 := rfl

noncomputable def h5p114 : BiPoly.Poly := [[(Int.ofNat 36)]]
theorem h5n114 : h5e114.toBi mapPolyEnv=h5p114 := rfl

noncomputable def h5p127 : BiPoly.Poly := mapPolyEnv 3
theorem h5n127 : h5e127.toBi mapPolyEnv=h5p127 := rfl

noncomputable def h5p154 : BiPoly.Poly := [[(Int.ofNat 18)]]
theorem h5n154 : h5e154.toBi mapPolyEnv=h5p154 := rfl

noncomputable def h5p155 : BiPoly.Poly := [[(Int.negSucc 17)]]
theorem h5n155 : h5e155.toBi mapPolyEnv=h5p155 := rfl

noncomputable def h5p163 : BiPoly.Poly := [[(Int.negSucc 11)]]
theorem h5n163 : h5e163.toBi mapPolyEnv=h5p163 := rfl

noncomputable def h5p164 : BiPoly.Poly := [[(Int.ofNat 12)]]
theorem h5n164 : h5e164.toBi mapPolyEnv=h5p164 := rfl

noncomputable def h5p181 : BiPoly.Poly := [[(Int.negSucc 59)]]
theorem h5n181 : h5e181.toBi mapPolyEnv=h5p181 := rfl

noncomputable def h5p183 : BiPoly.Poly := [[(Int.ofNat 60)]]
theorem h5n183 : h5e183.toBi mapPolyEnv=h5p183 := rfl

noncomputable def h5p191 : BiPoly.Poly := [[(Int.ofNat 48)]]
theorem h5n191 : h5e191.toBi mapPolyEnv=h5p191 := rfl

noncomputable def h5p206 : BiPoly.Poly := [[(Int.ofNat 216)]]
theorem h5n206 : h5e206.toBi mapPolyEnv=h5p206 := rfl

noncomputable def h5p207 : BiPoly.Poly := [[(Int.negSucc 215)]]
theorem h5n207 : h5e207.toBi mapPolyEnv=h5p207 := rfl

noncomputable def h5p273 : BiPoly.Poly := [[(Int.ofNat 9)]]
theorem h5n273 : h5e273.toBi mapPolyEnv=h5p273 := rfl

noncomputable def h5p274 : BiPoly.Poly := [[(Int.negSucc 8)]]
theorem h5n274 : h5e274.toBi mapPolyEnv=h5p274 := rfl

noncomputable def h5p291 : BiPoly.Poly := [[(Int.negSucc 31)]]
theorem h5n291 : h5e291.toBi mapPolyEnv=h5p291 := rfl

noncomputable def h5p292 : BiPoly.Poly := [[(Int.ofNat 32)]]
theorem h5n292 : h5e292.toBi mapPolyEnv=h5p292 := rfl

noncomputable def h5p294 : BiPoly.Poly := [[(Int.ofNat 64)]]
theorem h5n294 : h5e294.toBi mapPolyEnv=h5p294 := rfl

noncomputable def h5p328 : BiPoly.Poly := [[(Int.negSucc 63)]]
theorem h5n328 : h5e328.toBi mapPolyEnv=h5p328 := rfl

noncomputable def h5p355 : BiPoly.Poly := [[(Int.negSucc 7)]]
theorem h5n355 : h5e355.toBi mapPolyEnv=h5p355 := rfl

noncomputable def h5p356 : BiPoly.Poly := [[(Int.ofNat 8)]]
theorem h5n356 : h5e356.toBi mapPolyEnv=h5p356 := rfl

noncomputable def h5p358 : BiPoly.Poly := [[(Int.ofNat 16)]]
theorem h5n358 : h5e358.toBi mapPolyEnv=h5p358 := rfl

noncomputable def h5p409 : BiPoly.Poly := [[(Int.negSucc 15)]]
theorem h5n409 : h5e409.toBi mapPolyEnv=h5p409 := rfl
end StackSorting.RationalLift
