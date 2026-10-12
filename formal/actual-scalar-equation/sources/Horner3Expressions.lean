import RationalDivisibilityLiterals3
import BivariatePolynomial
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

def h3e0 : IExpr := .var 0

def h3e1 : IExpr := .var 2

def h3e2 : IExpr := .var 4

def h3e3 : IExpr := .var 5

def h3e4 : IExpr := .integer (-6)

def h3e5 : IExpr := .var 8

def h3e6 : IExpr := .mul h3e4 h3e5

def h3e7 : IExpr := .integer (6)

def h3e8 : IExpr := .var 9

def h3e9 : IExpr := .var 10

def h3e10 : IExpr := .mul h3e8 h3e9

def h3e11 : IExpr := .mul h3e7 h3e10

def h3e12 : IExpr := .add h3e6 h3e11

def h3e13 : IExpr := .mul h3e3 h3e12

def h3e14 : IExpr := .integer (-12)

def h3e15 : IExpr := .mul h3e2 h3e9

def h3e16 : IExpr := .mul h3e8 h3e15

def h3e17 : IExpr := .mul h3e14 h3e16

def h3e18 : IExpr := .add h3e13 h3e17

def h3e19 : IExpr := .mul h3e2 h3e18

def h3e20 : IExpr := .integer (3)

def h3e21 : IExpr := .mul h3e3 h3e3

def h3e22 : IExpr := .mul h3e5 h3e21

def h3e23 : IExpr := .mul h3e20 h3e22

def h3e24 : IExpr := .add h3e19 h3e23

def h3e25 : IExpr := .mul h3e1 h3e24

def h3e26 : IExpr := .var 3

def h3e27 : IExpr := .integer (-3)

def h3e28 : IExpr := .mul h3e27 h3e9

def h3e29 : IExpr := .add h3e27 h3e28

def h3e30 : IExpr := .mul h3e3 h3e29

def h3e31 : IExpr := .mul h3e2 h3e30

def h3e32 : IExpr := .mul h3e26 h3e31

def h3e33 : IExpr := .mul h3e5 h3e32

def h3e34 : IExpr := .add h3e25 h3e33

def h3e35 : IExpr := .mul h3e0 h3e34

def h3e36 : IExpr := .var 1

def h3e37 : IExpr := .integer (-2)

def h3e38 : IExpr := .mul h3e3 h3e9

def h3e39 : IExpr := .mul h3e8 h3e38

def h3e40 : IExpr := .mul h3e37 h3e39

def h3e41 : IExpr := .integer (4)

def h3e42 : IExpr := .mul h3e41 h3e16

def h3e43 : IExpr := .add h3e40 h3e42

def h3e44 : IExpr := .mul h3e2 h3e43

def h3e45 : IExpr := .mul h3e26 h3e44

def h3e46 : IExpr := .mul h3e36 h3e45

def h3e47 : IExpr := .add h3e35 h3e46
end StackSorting.RationalLift
