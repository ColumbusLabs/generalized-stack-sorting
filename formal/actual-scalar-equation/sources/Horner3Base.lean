import Horner3Expressions
import RationalMapPolynomials
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

def h3p0 : BiPoly.Poly := mapPolyEnv 0
theorem h3n0 : h3e0.toBi mapPolyEnv=h3p0 := rfl

def h3p1 : BiPoly.Poly := mapPolyEnv 2
theorem h3n1 : h3e1.toBi mapPolyEnv=h3p1 := rfl

def h3p2 : BiPoly.Poly := mapPolyEnv 4
theorem h3n2 : h3e2.toBi mapPolyEnv=h3p2 := rfl

def h3p3 : BiPoly.Poly := mapPolyEnv 5
theorem h3n3 : h3e3.toBi mapPolyEnv=h3p3 := rfl

def h3p4 : BiPoly.Poly := [[-6]]
theorem h3n4 : h3e4.toBi mapPolyEnv=h3p4 := rfl

def h3p5 : BiPoly.Poly := mapPolyEnv 8
theorem h3n5 : h3e5.toBi mapPolyEnv=h3p5 := rfl

def h3p7 : BiPoly.Poly := [[6]]
theorem h3n7 : h3e7.toBi mapPolyEnv=h3p7 := rfl

def h3p8 : BiPoly.Poly := mapPolyEnv 9
theorem h3n8 : h3e8.toBi mapPolyEnv=h3p8 := rfl

def h3p9 : BiPoly.Poly := mapPolyEnv 10
theorem h3n9 : h3e9.toBi mapPolyEnv=h3p9 := rfl

def h3p14 : BiPoly.Poly := [[-12]]
theorem h3n14 : h3e14.toBi mapPolyEnv=h3p14 := rfl

def h3p20 : BiPoly.Poly := [[3]]
theorem h3n20 : h3e20.toBi mapPolyEnv=h3p20 := rfl

def h3p26 : BiPoly.Poly := mapPolyEnv 3
theorem h3n26 : h3e26.toBi mapPolyEnv=h3p26 := rfl

def h3p27 : BiPoly.Poly := [[-3]]
theorem h3n27 : h3e27.toBi mapPolyEnv=h3p27 := rfl

def h3p36 : BiPoly.Poly := mapPolyEnv 1
theorem h3n36 : h3e36.toBi mapPolyEnv=h3p36 := rfl

def h3p37 : BiPoly.Poly := [[-2]]
theorem h3n37 : h3e37.toBi mapPolyEnv=h3p37 := rfl

def h3p41 : BiPoly.Poly := [[4]]
theorem h3n41 : h3e41.toBi mapPolyEnv=h3p41 := rfl
end StackSorting.RationalLift
