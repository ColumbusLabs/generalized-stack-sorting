import RationalDivisibilityLiterals0
import BivariatePolynomial
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

def h0e0 : IExpr := .var 0

def h0e1 : IExpr := .var 1

def h0e2 : IExpr := .var 2

def h0e3 : IExpr := .var 4

def h0e4 : IExpr := .var 7

def h0e5 : IExpr := .var 5

def h0e6 : IExpr := .integer (-72)

def h0e7 : IExpr := .var 8

def h0e8 : IExpr := .var 9

def h0e9 : IExpr := .mul h0e7 h0e8

def h0e10 : IExpr := .mul h0e6 h0e9

def h0e11 : IExpr := .integer (48)

def h0e12 : IExpr := .var 10

def h0e13 : IExpr := .mul h0e8 h0e8

def h0e14 : IExpr := .mul h0e12 h0e13

def h0e15 : IExpr := .mul h0e11 h0e14

def h0e16 : IExpr := .add h0e10 h0e15

def h0e17 : IExpr := .mul h0e5 h0e16

def h0e18 : IExpr := .mul h0e4 h0e17

def h0e19 : IExpr := .integer (-24)

def h0e20 : IExpr := .mul h0e3 h0e14

def h0e21 : IExpr := .mul h0e4 h0e20

def h0e22 : IExpr := .mul h0e19 h0e21

def h0e23 : IExpr := .add h0e18 h0e22

def h0e24 : IExpr := .mul h0e3 h0e23

def h0e25 : IExpr := .mul h0e5 h0e5

def h0e26 : IExpr := .integer (-18)

def h0e27 : IExpr := .mul h0e26 h0e14

def h0e28 : IExpr := .integer (36)

def h0e29 : IExpr := .mul h0e28 h0e9

def h0e30 : IExpr := .add h0e27 h0e29

def h0e31 : IExpr := .mul h0e25 h0e30

def h0e32 : IExpr := .mul h0e4 h0e31

def h0e33 : IExpr := .add h0e24 h0e32

def h0e34 : IExpr := .mul h0e2 h0e33

def h0e35 : IExpr := .var 3

def h0e36 : IExpr := .var 6

def h0e37 : IExpr := .integer (-12)

def h0e38 : IExpr := .mul h0e37 h0e7

def h0e39 : IExpr := .integer (-6)

def h0e40 : IExpr := .mul h0e8 h0e12

def h0e41 : IExpr := .mul h0e39 h0e40

def h0e42 : IExpr := .add h0e38 h0e41

def h0e43 : IExpr := .mul h0e7 h0e42

def h0e44 : IExpr := .mul h0e36 h0e43

def h0e45 : IExpr := .integer (6)

def h0e46 : IExpr := .integer (12)

def h0e47 : IExpr := .mul h0e46 h0e12

def h0e48 : IExpr := .add h0e45 h0e47

def h0e49 : IExpr := .mul h0e8 h0e48

def h0e50 : IExpr := .mul h0e7 h0e49

def h0e51 : IExpr := .mul h0e4 h0e50

def h0e52 : IExpr := .add h0e44 h0e51

def h0e53 : IExpr := .mul h0e25 h0e52

def h0e54 : IExpr := .mul h0e7 h0e40

def h0e55 : IExpr := .mul h0e4 h0e54

def h0e56 : IExpr := .mul h0e37 h0e55

def h0e57 : IExpr := .mul h0e36 h0e54

def h0e58 : IExpr := .mul h0e46 h0e57

def h0e59 : IExpr := .add h0e56 h0e58

def h0e60 : IExpr := .mul h0e5 h0e59

def h0e61 : IExpr := .mul h0e3 h0e60

def h0e62 : IExpr := .add h0e53 h0e61

def h0e63 : IExpr := .mul h0e35 h0e62

def h0e64 : IExpr := .add h0e34 h0e63

def h0e65 : IExpr := .mul h0e2 h0e64

def h0e66 : IExpr := .integer (18)

def h0e67 : IExpr := .mul h0e35 h0e35

def h0e68 : IExpr := .mul h0e12 h0e67

def h0e69 : IExpr := .mul h0e5 h0e68

def h0e70 : IExpr := .mul h0e3 h0e69

def h0e71 : IExpr := .mul h0e8 h0e70

def h0e72 : IExpr := .mul h0e7 h0e71

def h0e73 : IExpr := .mul h0e4 h0e72

def h0e74 : IExpr := .mul h0e66 h0e73

def h0e75 : IExpr := .add h0e65 h0e74

def h0e76 : IExpr := .mul h0e1 h0e75

def h0e77 : IExpr := .mul h0e19 h0e12

def h0e78 : IExpr := .add h0e37 h0e77

def h0e79 : IExpr := .mul h0e8 h0e78

def h0e80 : IExpr := .mul h0e7 h0e79

def h0e81 : IExpr := .mul h0e4 h0e80

def h0e82 : IExpr := .mul h0e66 h0e57

def h0e83 : IExpr := .add h0e81 h0e82

def h0e84 : IExpr := .mul h0e25 h0e83

def h0e85 : IExpr := .integer (24)

def h0e86 : IExpr := .mul h0e11 h0e12

def h0e87 : IExpr := .add h0e85 h0e86

def h0e88 : IExpr := .mul h0e8 h0e87

def h0e89 : IExpr := .mul h0e7 h0e88

def h0e90 : IExpr := .mul h0e4 h0e89

def h0e91 : IExpr := .integer (-36)

def h0e92 : IExpr := .mul h0e91 h0e57

def h0e93 : IExpr := .add h0e90 h0e92

def h0e94 : IExpr := .mul h0e5 h0e93

def h0e95 : IExpr := .mul h0e3 h0e94

def h0e96 : IExpr := .add h0e84 h0e95

def h0e97 : IExpr := .mul h0e2 h0e96

def h0e98 : IExpr := .mul h0e46 h0e7

def h0e99 : IExpr := .integer (-3)

def h0e100 : IExpr := .mul h0e99 h0e40

def h0e101 : IExpr := .add h0e98 h0e100

def h0e102 : IExpr := .mul h0e25 h0e101

def h0e103 : IExpr := .mul h0e7 h0e102

def h0e104 : IExpr := .mul h0e4 h0e103

def h0e105 : IExpr := .integer (-30)

def h0e106 : IExpr := .mul h0e5 h0e12

def h0e107 : IExpr := .mul h0e3 h0e106

def h0e108 : IExpr := .mul h0e8 h0e107

def h0e109 : IExpr := .mul h0e7 h0e108

def h0e110 : IExpr := .mul h0e4 h0e109

def h0e111 : IExpr := .mul h0e105 h0e110

def h0e112 : IExpr := .add h0e104 h0e111

def h0e113 : IExpr := .mul h0e35 h0e112

def h0e114 : IExpr := .add h0e97 h0e113

def h0e115 : IExpr := .mul h0e2 h0e114

def h0e116 : IExpr := .mul h0e0 h0e115

def h0e117 : IExpr := .add h0e76 h0e116

def h0e118 : IExpr := .mul h0e0 h0e117

def h0e119 : IExpr := .mul h0e1 h0e1

def h0e120 : IExpr := .integer (-16)

def h0e121 : IExpr := .mul h0e120 h0e14

def h0e122 : IExpr := .mul h0e85 h0e9

def h0e123 : IExpr := .add h0e121 h0e122

def h0e124 : IExpr := .mul h0e5 h0e123

def h0e125 : IExpr := .mul h0e4 h0e124

def h0e126 : IExpr := .integer (8)

def h0e127 : IExpr := .mul h0e126 h0e21

def h0e128 : IExpr := .add h0e125 h0e127

def h0e129 : IExpr := .mul h0e3 h0e128

def h0e130 : IExpr := .mul h0e37 h0e9

def h0e131 : IExpr := .mul h0e45 h0e14

def h0e132 : IExpr := .add h0e130 h0e131

def h0e133 : IExpr := .mul h0e25 h0e132

def h0e134 : IExpr := .mul h0e4 h0e133

def h0e135 : IExpr := .add h0e129 h0e134

def h0e136 : IExpr := .mul h0e119 h0e135

def h0e137 : IExpr := .mul h0e35 h0e136

def h0e138 : IExpr := .mul h0e2 h0e137

def h0e139 : IExpr := .add h0e118 h0e138
end StackSorting.RationalLift
