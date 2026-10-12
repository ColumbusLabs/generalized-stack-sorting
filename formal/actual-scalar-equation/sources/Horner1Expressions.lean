import RationalDivisibilityLiterals1
import BivariatePolynomial
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

def h1e0 : IExpr := .var 0

def h1e1 : IExpr := .var 2

def h1e2 : IExpr := .var 4

def h1e3 : IExpr := .var 5

def h1e4 : IExpr := .var 6

def h1e5 : IExpr := .var 7

def h1e6 : IExpr := .var 8

def h1e7 : IExpr := .integer (24)

def h1e8 : IExpr := .integer (96)

def h1e9 : IExpr := .var 10

def h1e10 : IExpr := .mul h1e8 h1e9

def h1e11 : IExpr := .add h1e7 h1e10

def h1e12 : IExpr := .mul h1e6 h1e11

def h1e13 : IExpr := .mul h1e5 h1e12

def h1e14 : IExpr := .integer (-36)

def h1e15 : IExpr := .mul h1e6 h1e9

def h1e16 : IExpr := .mul h1e4 h1e15

def h1e17 : IExpr := .mul h1e14 h1e16

def h1e18 : IExpr := .add h1e13 h1e17

def h1e19 : IExpr := .mul h1e4 h1e18

def h1e20 : IExpr := .mul h1e5 h1e5

def h1e21 : IExpr := .integer (-96)

def h1e22 : IExpr := .mul h1e21 h1e6

def h1e23 : IExpr := .var 9

def h1e24 : IExpr := .mul h1e23 h1e9

def h1e25 : IExpr := .mul h1e7 h1e24

def h1e26 : IExpr := .add h1e22 h1e25

def h1e27 : IExpr := .mul h1e20 h1e26

def h1e28 : IExpr := .add h1e19 h1e27

def h1e29 : IExpr := .mul h1e3 h1e28

def h1e30 : IExpr := .mul h1e9 h1e20

def h1e31 : IExpr := .mul h1e2 h1e30

def h1e32 : IExpr := .mul h1e23 h1e31

def h1e33 : IExpr := .mul h1e7 h1e32

def h1e34 : IExpr := .add h1e29 h1e33

def h1e35 : IExpr := .mul h1e2 h1e34

def h1e36 : IExpr := .mul h1e3 h1e3

def h1e37 : IExpr := .integer (-12)

def h1e38 : IExpr := .integer (-48)

def h1e39 : IExpr := .mul h1e38 h1e9

def h1e40 : IExpr := .add h1e37 h1e39

def h1e41 : IExpr := .mul h1e6 h1e40

def h1e42 : IExpr := .mul h1e5 h1e41

def h1e43 : IExpr := .integer (18)

def h1e44 : IExpr := .mul h1e43 h1e16

def h1e45 : IExpr := .add h1e42 h1e44

def h1e46 : IExpr := .mul h1e4 h1e45

def h1e47 : IExpr := .integer (48)

def h1e48 : IExpr := .mul h1e47 h1e6

def h1e49 : IExpr := .integer (-18)

def h1e50 : IExpr := .mul h1e49 h1e24

def h1e51 : IExpr := .add h1e48 h1e50

def h1e52 : IExpr := .mul h1e20 h1e51

def h1e53 : IExpr := .add h1e46 h1e52

def h1e54 : IExpr := .mul h1e36 h1e53

def h1e55 : IExpr := .add h1e35 h1e54

def h1e56 : IExpr := .mul h1e1 h1e55

def h1e57 : IExpr := .var 3

def h1e58 : IExpr := .integer (4)

def h1e59 : IExpr := .integer (8)

def h1e60 : IExpr := .mul h1e59 h1e9

def h1e61 : IExpr := .add h1e58 h1e60

def h1e62 : IExpr := .mul h1e20 h1e61

def h1e63 : IExpr := .mul h1e6 h1e62

def h1e64 : IExpr := .integer (-4)

def h1e65 : IExpr := .mul h1e5 h1e15

def h1e66 : IExpr := .mul h1e4 h1e65

def h1e67 : IExpr := .mul h1e64 h1e66

def h1e68 : IExpr := .add h1e63 h1e67

def h1e69 : IExpr := .mul h1e36 h1e68

def h1e70 : IExpr := .integer (16)

def h1e71 : IExpr := .add h1e70 h1e60

def h1e72 : IExpr := .mul h1e20 h1e71

def h1e73 : IExpr := .mul h1e6 h1e72

def h1e74 : IExpr := .integer (-16)

def h1e75 : IExpr := .mul h1e74 h1e66

def h1e76 : IExpr := .add h1e73 h1e75

def h1e77 : IExpr := .mul h1e3 h1e76

def h1e78 : IExpr := .mul h1e2 h1e77

def h1e79 : IExpr := .add h1e69 h1e78

def h1e80 : IExpr := .mul h1e57 h1e79

def h1e81 : IExpr := .add h1e56 h1e80

def h1e82 : IExpr := .mul h1e1 h1e81

def h1e83 : IExpr := .integer (12)

def h1e84 : IExpr := .mul h1e57 h1e57

def h1e85 : IExpr := .mul h1e20 h1e84

def h1e86 : IExpr := .mul h1e9 h1e85

def h1e87 : IExpr := .mul h1e3 h1e86

def h1e88 : IExpr := .mul h1e2 h1e87

def h1e89 : IExpr := .mul h1e6 h1e88

def h1e90 : IExpr := .mul h1e83 h1e89

def h1e91 : IExpr := .add h1e82 h1e90

def h1e92 : IExpr := .mul h1e0 h1e91

def h1e93 : IExpr := .var 1

def h1e94 : IExpr := .integer (-32)

def h1e95 : IExpr := .mul h1e94 h1e9

def h1e96 : IExpr := .add h1e64 h1e95

def h1e97 : IExpr := .mul h1e6 h1e96

def h1e98 : IExpr := .mul h1e5 h1e97

def h1e99 : IExpr := .integer (10)

def h1e100 : IExpr := .mul h1e99 h1e16

def h1e101 : IExpr := .add h1e98 h1e100

def h1e102 : IExpr := .mul h1e4 h1e101

def h1e103 : IExpr := .mul h1e7 h1e6

def h1e104 : IExpr := .mul h1e64 h1e24

def h1e105 : IExpr := .add h1e103 h1e104

def h1e106 : IExpr := .mul h1e20 h1e105

def h1e107 : IExpr := .add h1e102 h1e106

def h1e108 : IExpr := .mul h1e3 h1e107

def h1e109 : IExpr := .mul h1e37 h1e32

def h1e110 : IExpr := .add h1e108 h1e109

def h1e111 : IExpr := .mul h1e2 h1e110

def h1e112 : IExpr := .integer (2)

def h1e113 : IExpr := .mul h1e70 h1e9

def h1e114 : IExpr := .add h1e112 h1e113

def h1e115 : IExpr := .mul h1e6 h1e114

def h1e116 : IExpr := .mul h1e5 h1e115

def h1e117 : IExpr := .integer (-5)

def h1e118 : IExpr := .mul h1e117 h1e16

def h1e119 : IExpr := .add h1e116 h1e118

def h1e120 : IExpr := .mul h1e4 h1e119

def h1e121 : IExpr := .mul h1e37 h1e6

def h1e122 : IExpr := .integer (5)

def h1e123 : IExpr := .mul h1e122 h1e24

def h1e124 : IExpr := .add h1e121 h1e123

def h1e125 : IExpr := .mul h1e20 h1e124

def h1e126 : IExpr := .add h1e120 h1e125

def h1e127 : IExpr := .mul h1e36 h1e126

def h1e128 : IExpr := .add h1e111 h1e127

def h1e129 : IExpr := .mul h1e57 h1e128

def h1e130 : IExpr := .mul h1e1 h1e129

def h1e131 : IExpr := .mul h1e93 h1e130

def h1e132 : IExpr := .add h1e92 h1e131
end StackSorting.RationalLift
