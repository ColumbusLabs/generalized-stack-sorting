import Horner4Expressions
import RationalMapPolynomials
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p0 : BiPoly.Poly := mapPolyEnv 0
theorem h4n0 : h4e0.toBi mapPolyEnv=h4p0 := rfl

noncomputable def h4p1 : BiPoly.Poly := mapPolyEnv 1
theorem h4n1 : h4e1.toBi mapPolyEnv=h4p1 := rfl

noncomputable def h4p2 : BiPoly.Poly := mapPolyEnv 2
theorem h4n2 : h4e2.toBi mapPolyEnv=h4p2 := rfl

noncomputable def h4p3 : BiPoly.Poly := mapPolyEnv 4
theorem h4n3 : h4e3.toBi mapPolyEnv=h4p3 := rfl

noncomputable def h4p4 : BiPoly.Poly := mapPolyEnv 5
theorem h4n4 : h4e4.toBi mapPolyEnv=h4p4 := rfl

noncomputable def h4p5 : BiPoly.Poly := mapPolyEnv 7
theorem h4n5 : h4e5.toBi mapPolyEnv=h4p5 := rfl

noncomputable def h4p6 : BiPoly.Poly := [[(Int.ofNat 72)]]
theorem h4n6 : h4e6.toBi mapPolyEnv=h4p6 := rfl

noncomputable def h4p7 : BiPoly.Poly := mapPolyEnv 9
theorem h4n7 : h4e7.toBi mapPolyEnv=h4p7 := rfl

noncomputable def h4p9 : BiPoly.Poly := mapPolyEnv 10
theorem h4n9 : h4e9.toBi mapPolyEnv=h4p9 := rfl

noncomputable def h4p13 : BiPoly.Poly := mapPolyEnv 8
theorem h4n13 : h4e13.toBi mapPolyEnv=h4p13 := rfl

noncomputable def h4p14 : BiPoly.Poly := [[(Int.ofNat 96)]]
theorem h4n14 : h4e14.toBi mapPolyEnv=h4p14 := rfl

noncomputable def h4p15 : BiPoly.Poly := [[(Int.negSucc 95)]]
theorem h4n15 : h4e15.toBi mapPolyEnv=h4p15 := rfl

noncomputable def h4p22 : BiPoly.Poly := [[(Int.negSucc 143)]]
theorem h4n22 : h4e22.toBi mapPolyEnv=h4p22 := rfl

noncomputable def h4p23 : BiPoly.Poly := mapPolyEnv 6
theorem h4n23 : h4e23.toBi mapPolyEnv=h4p23 := rfl

noncomputable def h4p30 : BiPoly.Poly := [[(Int.ofNat 144)]]
theorem h4n30 : h4e30.toBi mapPolyEnv=h4p30 := rfl

noncomputable def h4p37 : BiPoly.Poly := [[(Int.negSucc 179)]]
theorem h4n37 : h4e37.toBi mapPolyEnv=h4p37 := rfl

noncomputable def h4p51 : BiPoly.Poly := [[(Int.ofNat 54)]]
theorem h4n51 : h4e51.toBi mapPolyEnv=h4p51 := rfl

noncomputable def h4p53 : BiPoly.Poly := [[(Int.ofNat 24)]]
theorem h4n53 : h4e53.toBi mapPolyEnv=h4p53 := rfl

noncomputable def h4p54 : BiPoly.Poly := [[(Int.negSucc 23)]]
theorem h4n54 : h4e54.toBi mapPolyEnv=h4p54 := rfl

noncomputable def h4p61 : BiPoly.Poly := [[(Int.negSucc 35)]]
theorem h4n61 : h4e61.toBi mapPolyEnv=h4p61 := rfl

noncomputable def h4p67 : BiPoly.Poly := mapPolyEnv 3
theorem h4n67 : h4e67.toBi mapPolyEnv=h4p67 := rfl

noncomputable def h4p68 : BiPoly.Poly := [[(Int.negSucc 71)]]
theorem h4n68 : h4e68.toBi mapPolyEnv=h4p68 := rfl

noncomputable def h4p76 : BiPoly.Poly := [[(Int.ofNat 48)]]
theorem h4n76 : h4e76.toBi mapPolyEnv=h4p76 := rfl

noncomputable def h4p95 : BiPoly.Poly := [[(Int.ofNat 18)]]
theorem h4n95 : h4e95.toBi mapPolyEnv=h4p95 := rfl

noncomputable def h4p97 : BiPoly.Poly := [[(Int.ofNat 36)]]
theorem h4n97 : h4e97.toBi mapPolyEnv=h4p97 := rfl

noncomputable def h4p103 : BiPoly.Poly := [[(Int.negSucc 11)]]
theorem h4n103 : h4e103.toBi mapPolyEnv=h4p103 := rfl

noncomputable def h4p118 : BiPoly.Poly := [[(Int.negSucc 59)]]
theorem h4n118 : h4e118.toBi mapPolyEnv=h4p118 := rfl

noncomputable def h4p131 : BiPoly.Poly := [[(Int.ofNat 216)]]
theorem h4n131 : h4e131.toBi mapPolyEnv=h4p131 := rfl

noncomputable def h4p135 : BiPoly.Poly := [[(Int.negSucc 287)]]
theorem h4n135 : h4e135.toBi mapPolyEnv=h4p135 := rfl

noncomputable def h4p144 : BiPoly.Poly := [[(Int.negSucc 215)]]
theorem h4n144 : h4e144.toBi mapPolyEnv=h4p144 := rfl

noncomputable def h4p146 : BiPoly.Poly := [[(Int.ofNat 288)]]
theorem h4n146 : h4e146.toBi mapPolyEnv=h4p146 := rfl

noncomputable def h4p158 : BiPoly.Poly := [[(Int.negSucc 53)]]
theorem h4n158 : h4e158.toBi mapPolyEnv=h4p158 := rfl

noncomputable def h4p180 : BiPoly.Poly := [[(Int.ofNat 9)]]
theorem h4n180 : h4e180.toBi mapPolyEnv=h4p180 := rfl

noncomputable def h4p195 : BiPoly.Poly := [[(Int.negSucc 31)]]
theorem h4n195 : h4e195.toBi mapPolyEnv=h4p195 := rfl

noncomputable def h4p196 : BiPoly.Poly := [[(Int.ofNat 32)]]
theorem h4n196 : h4e196.toBi mapPolyEnv=h4p196 := rfl

noncomputable def h4p206 : BiPoly.Poly := [[(Int.negSucc 47)]]
theorem h4n206 : h4e206.toBi mapPolyEnv=h4p206 := rfl

noncomputable def h4p210 : BiPoly.Poly := [[(Int.ofNat 60)]]
theorem h4n210 : h4e210.toBi mapPolyEnv=h4p210 := rfl

noncomputable def h4p223 : BiPoly.Poly := [[(Int.negSucc 17)]]
theorem h4n223 : h4e223.toBi mapPolyEnv=h4p223 := rfl

noncomputable def h4p225 : BiPoly.Poly := [[(Int.negSucc 7)]]
theorem h4n225 : h4e225.toBi mapPolyEnv=h4p225 := rfl

noncomputable def h4p226 : BiPoly.Poly := [[(Int.ofNat 8)]]
theorem h4n226 : h4e226.toBi mapPolyEnv=h4p226 := rfl

noncomputable def h4p233 : BiPoly.Poly := [[(Int.ofNat 12)]]
theorem h4n233 : h4e233.toBi mapPolyEnv=h4p233 := rfl

noncomputable def h4p241 : BiPoly.Poly := [[(Int.ofNat 16)]]
theorem h4n241 : h4e241.toBi mapPolyEnv=h4p241 := rfl

noncomputable def h4p251 : BiPoly.Poly := [[(Int.negSucc 15)]]
theorem h4n251 : h4e251.toBi mapPolyEnv=h4p251 := rfl
end StackSorting.RationalLift
