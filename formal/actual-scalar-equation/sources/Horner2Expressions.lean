import RationalDivisibilityLiterals2
import BivariatePolynomial
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

def h2e0 : IExpr := .var 0

def h2e1 : IExpr := .var 2

def h2e2 : IExpr := .var 5

def h2e3 : IExpr := .mul h2e2 h2e2

def h2e4 : IExpr := .var 7

def h2e5 : IExpr := .var 9

def h2e6 : IExpr := .integer (12)

def h2e7 : IExpr := .integer (48)

def h2e8 : IExpr := .var 10

def h2e9 : IExpr := .mul h2e7 h2e8

def h2e10 : IExpr := .add h2e6 h2e9

def h2e11 : IExpr := .mul h2e5 h2e10

def h2e12 : IExpr := .mul h2e4 h2e11

def h2e13 : IExpr := .integer (-18)

def h2e14 : IExpr := .var 6

def h2e15 : IExpr := .mul h2e5 h2e8

def h2e16 : IExpr := .mul h2e14 h2e15

def h2e17 : IExpr := .mul h2e13 h2e16

def h2e18 : IExpr := .add h2e12 h2e17

def h2e19 : IExpr := .mul h2e3 h2e18

def h2e20 : IExpr := .var 4

def h2e21 : IExpr := .integer (-24)

def h2e22 : IExpr := .integer (-96)

def h2e23 : IExpr := .mul h2e22 h2e8

def h2e24 : IExpr := .add h2e21 h2e23

def h2e25 : IExpr := .mul h2e5 h2e24

def h2e26 : IExpr := .mul h2e4 h2e25

def h2e27 : IExpr := .integer (36)

def h2e28 : IExpr := .mul h2e27 h2e16

def h2e29 : IExpr := .add h2e26 h2e28

def h2e30 : IExpr := .mul h2e2 h2e29

def h2e31 : IExpr := .mul h2e20 h2e30

def h2e32 : IExpr := .add h2e19 h2e31

def h2e33 : IExpr := .mul h2e1 h2e32

def h2e34 : IExpr := .var 3

def h2e35 : IExpr := .var 8

def h2e36 : IExpr := .mul h2e21 h2e35

def h2e37 : IExpr := .integer (40)

def h2e38 : IExpr := .mul h2e37 h2e15

def h2e39 : IExpr := .add h2e36 h2e38

def h2e40 : IExpr := .mul h2e2 h2e39

def h2e41 : IExpr := .mul h2e4 h2e40

def h2e42 : IExpr := .integer (-48)

def h2e43 : IExpr := .mul h2e20 h2e8

def h2e44 : IExpr := .mul h2e5 h2e43

def h2e45 : IExpr := .mul h2e4 h2e44

def h2e46 : IExpr := .mul h2e42 h2e45

def h2e47 : IExpr := .add h2e41 h2e46

def h2e48 : IExpr := .mul h2e20 h2e47

def h2e49 : IExpr := .integer (-12)

def h2e50 : IExpr := .mul h2e49 h2e35

def h2e51 : IExpr := .integer (4)

def h2e52 : IExpr := .mul h2e51 h2e15

def h2e53 : IExpr := .add h2e50 h2e52

def h2e54 : IExpr := .mul h2e3 h2e53

def h2e55 : IExpr := .mul h2e4 h2e54

def h2e56 : IExpr := .add h2e48 h2e55

def h2e57 : IExpr := .mul h2e34 h2e56

def h2e58 : IExpr := .add h2e33 h2e57

def h2e59 : IExpr := .mul h2e1 h2e58

def h2e60 : IExpr := .mul h2e34 h2e34

def h2e61 : IExpr := .mul h2e49 h2e8

def h2e62 : IExpr := .add h2e49 h2e61

def h2e63 : IExpr := .mul h2e60 h2e62

def h2e64 : IExpr := .mul h2e2 h2e63

def h2e65 : IExpr := .mul h2e20 h2e64

def h2e66 : IExpr := .mul h2e35 h2e65

def h2e67 : IExpr := .mul h2e4 h2e66

def h2e68 : IExpr := .add h2e59 h2e67

def h2e69 : IExpr := .mul h2e0 h2e68

def h2e70 : IExpr := .var 1

def h2e71 : IExpr := .integer (-2)

def h2e72 : IExpr := .integer (-16)

def h2e73 : IExpr := .mul h2e72 h2e8

def h2e74 : IExpr := .add h2e71 h2e73

def h2e75 : IExpr := .mul h2e5 h2e74

def h2e76 : IExpr := .mul h2e4 h2e75

def h2e77 : IExpr := .integer (5)

def h2e78 : IExpr := .mul h2e77 h2e16

def h2e79 : IExpr := .add h2e76 h2e78

def h2e80 : IExpr := .mul h2e3 h2e79

def h2e81 : IExpr := .integer (32)

def h2e82 : IExpr := .mul h2e81 h2e8

def h2e83 : IExpr := .add h2e51 h2e82

def h2e84 : IExpr := .mul h2e5 h2e83

def h2e85 : IExpr := .mul h2e4 h2e84

def h2e86 : IExpr := .integer (-10)

def h2e87 : IExpr := .mul h2e86 h2e16

def h2e88 : IExpr := .add h2e85 h2e87

def h2e89 : IExpr := .mul h2e2 h2e88

def h2e90 : IExpr := .mul h2e20 h2e89

def h2e91 : IExpr := .add h2e80 h2e90

def h2e92 : IExpr := .mul h2e34 h2e91

def h2e93 : IExpr := .mul h2e1 h2e92

def h2e94 : IExpr := .integer (-8)

def h2e95 : IExpr := .mul h2e2 h2e8

def h2e96 : IExpr := .mul h2e5 h2e95

def h2e97 : IExpr := .mul h2e4 h2e96

def h2e98 : IExpr := .mul h2e94 h2e97

def h2e99 : IExpr := .integer (16)

def h2e100 : IExpr := .mul h2e99 h2e45

def h2e101 : IExpr := .add h2e98 h2e100

def h2e102 : IExpr := .mul h2e60 h2e101

def h2e103 : IExpr := .mul h2e20 h2e102

def h2e104 : IExpr := .add h2e93 h2e103

def h2e105 : IExpr := .mul h2e70 h2e104

def h2e106 : IExpr := .add h2e69 h2e105
end StackSorting.RationalLift
