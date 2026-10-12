import RationalDivisibilityLiterals4
import BivariatePolynomial
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

def h4e0 : IExpr := .var 0

def h4e1 : IExpr := .var 1

def h4e2 : IExpr := .var 2

def h4e3 : IExpr := .var 4

def h4e4 : IExpr := .var 5

def h4e5 : IExpr := .var 7

def h4e6 : IExpr := .integer (72)

def h4e7 : IExpr := .var 9

def h4e8 : IExpr := .mul h4e7 h4e7

def h4e9 : IExpr := .var 10

def h4e10 : IExpr := .mul h4e9 h4e9

def h4e11 : IExpr := .mul h4e8 h4e10

def h4e12 : IExpr := .mul h4e6 h4e11

def h4e13 : IExpr := .var 8

def h4e14 : IExpr := .integer (96)

def h4e15 : IExpr := .integer (-96)

def h4e16 : IExpr := .mul h4e15 h4e9

def h4e17 : IExpr := .add h4e14 h4e16

def h4e18 : IExpr := .mul h4e7 h4e17

def h4e19 : IExpr := .mul h4e13 h4e18

def h4e20 : IExpr := .add h4e12 h4e19

def h4e21 : IExpr := .mul h4e5 h4e20

def h4e22 : IExpr := .integer (-144)

def h4e23 : IExpr := .var 6

def h4e24 : IExpr := .mul h4e7 h4e9

def h4e25 : IExpr := .mul h4e13 h4e24

def h4e26 : IExpr := .mul h4e23 h4e25

def h4e27 : IExpr := .mul h4e22 h4e26

def h4e28 : IExpr := .add h4e21 h4e27

def h4e29 : IExpr := .mul h4e4 h4e28

def h4e30 : IExpr := .integer (144)

def h4e31 : IExpr := .mul h4e3 h4e11

def h4e32 : IExpr := .mul h4e5 h4e31

def h4e33 : IExpr := .mul h4e30 h4e32

def h4e34 : IExpr := .add h4e29 h4e33

def h4e35 : IExpr := .mul h4e3 h4e34

def h4e36 : IExpr := .mul h4e4 h4e4

def h4e37 : IExpr := .integer (-180)

def h4e38 : IExpr := .mul h4e37 h4e11

def h4e39 : IExpr := .mul h4e14 h4e9

def h4e40 : IExpr := .add h4e15 h4e39

def h4e41 : IExpr := .mul h4e7 h4e40

def h4e42 : IExpr := .mul h4e13 h4e41

def h4e43 : IExpr := .add h4e38 h4e42

def h4e44 : IExpr := .mul h4e5 h4e43

def h4e45 : IExpr := .mul h4e30 h4e26

def h4e46 : IExpr := .add h4e44 h4e45

def h4e47 : IExpr := .mul h4e36 h4e46

def h4e48 : IExpr := .add h4e35 h4e47

def h4e49 : IExpr := .mul h4e3 h4e48

def h4e50 : IExpr := .mul h4e4 h4e36

def h4e51 : IExpr := .integer (54)

def h4e52 : IExpr := .mul h4e51 h4e11

def h4e53 : IExpr := .integer (24)

def h4e54 : IExpr := .integer (-24)

def h4e55 : IExpr := .mul h4e54 h4e9

def h4e56 : IExpr := .add h4e53 h4e55

def h4e57 : IExpr := .mul h4e7 h4e56

def h4e58 : IExpr := .mul h4e13 h4e57

def h4e59 : IExpr := .add h4e52 h4e58

def h4e60 : IExpr := .mul h4e5 h4e59

def h4e61 : IExpr := .integer (-36)

def h4e62 : IExpr := .mul h4e61 h4e26

def h4e63 : IExpr := .add h4e60 h4e62

def h4e64 : IExpr := .mul h4e50 h4e63

def h4e65 : IExpr := .add h4e49 h4e64

def h4e66 : IExpr := .mul h4e2 h4e65

def h4e67 : IExpr := .var 3

def h4e68 : IExpr := .integer (-72)

def h4e69 : IExpr := .mul h4e13 h4e9

def h4e70 : IExpr := .mul h4e68 h4e69

def h4e71 : IExpr := .mul h4e7 h4e10

def h4e72 : IExpr := .mul h4e61 h4e71

def h4e73 : IExpr := .add h4e70 h4e72

def h4e74 : IExpr := .mul h4e13 h4e73

def h4e75 : IExpr := .mul h4e23 h4e74

def h4e76 : IExpr := .integer (48)

def h4e77 : IExpr := .mul h4e76 h4e13

def h4e78 : IExpr := .mul h4e53 h4e9

def h4e79 : IExpr := .add h4e53 h4e78

def h4e80 : IExpr := .mul h4e9 h4e79

def h4e81 : IExpr := .mul h4e7 h4e80

def h4e82 : IExpr := .add h4e77 h4e81

def h4e83 : IExpr := .mul h4e13 h4e82

def h4e84 : IExpr := .mul h4e5 h4e83

def h4e85 : IExpr := .add h4e75 h4e84

def h4e86 : IExpr := .mul h4e36 h4e85

def h4e87 : IExpr := .mul h4e4 h4e10

def h4e88 : IExpr := .mul h4e3 h4e87

def h4e89 : IExpr := .mul h4e7 h4e88

def h4e90 : IExpr := .mul h4e13 h4e89

def h4e91 : IExpr := .mul h4e5 h4e90

def h4e92 : IExpr := .mul h4e14 h4e91

def h4e93 : IExpr := .add h4e86 h4e92

def h4e94 : IExpr := .mul h4e3 h4e93

def h4e95 : IExpr := .integer (18)

def h4e96 : IExpr := .mul h4e95 h4e71

def h4e97 : IExpr := .integer (36)

def h4e98 : IExpr := .mul h4e97 h4e69

def h4e99 : IExpr := .add h4e96 h4e98

def h4e100 : IExpr := .mul h4e13 h4e99

def h4e101 : IExpr := .mul h4e23 h4e100

def h4e102 : IExpr := .mul h4e54 h4e13

def h4e103 : IExpr := .integer (-12)

def h4e104 : IExpr := .mul h4e61 h4e9

def h4e105 : IExpr := .add h4e103 h4e104

def h4e106 : IExpr := .mul h4e9 h4e105

def h4e107 : IExpr := .mul h4e7 h4e106

def h4e108 : IExpr := .add h4e102 h4e107

def h4e109 : IExpr := .mul h4e13 h4e108

def h4e110 : IExpr := .mul h4e5 h4e109

def h4e111 : IExpr := .add h4e101 h4e110

def h4e112 : IExpr := .mul h4e50 h4e111

def h4e113 : IExpr := .add h4e94 h4e112

def h4e114 : IExpr := .mul h4e67 h4e113

def h4e115 : IExpr := .add h4e66 h4e114

def h4e116 : IExpr := .mul h4e2 h4e115

def h4e117 : IExpr := .mul h4e67 h4e67

def h4e118 : IExpr := .integer (-60)

def h4e119 : IExpr := .mul h4e118 h4e71

def h4e120 : IExpr := .mul h4e53 h4e69

def h4e121 : IExpr := .add h4e119 h4e120

def h4e122 : IExpr := .mul h4e36 h4e121

def h4e123 : IExpr := .mul h4e13 h4e122

def h4e124 : IExpr := .mul h4e5 h4e123

def h4e125 : IExpr := .mul h4e76 h4e91

def h4e126 : IExpr := .add h4e124 h4e125

def h4e127 : IExpr := .mul h4e117 h4e126

def h4e128 : IExpr := .mul h4e3 h4e127

def h4e129 : IExpr := .add h4e116 h4e128

def h4e130 : IExpr := .mul h4e1 h4e129

def h4e131 : IExpr := .integer (216)

def h4e132 : IExpr := .mul h4e13 h4e71

def h4e133 : IExpr := .mul h4e23 h4e132

def h4e134 : IExpr := .mul h4e131 h4e133

def h4e135 : IExpr := .integer (-288)

def h4e136 : IExpr := .mul h4e135 h4e9

def h4e137 : IExpr := .add h4e22 h4e136

def h4e138 : IExpr := .mul h4e9 h4e137

def h4e139 : IExpr := .mul h4e7 h4e138

def h4e140 : IExpr := .mul h4e13 h4e139

def h4e141 : IExpr := .mul h4e5 h4e140

def h4e142 : IExpr := .add h4e134 h4e141

def h4e143 : IExpr := .mul h4e36 h4e142

def h4e144 : IExpr := .integer (-216)

def h4e145 : IExpr := .mul h4e144 h4e133

def h4e146 : IExpr := .integer (288)

def h4e147 : IExpr := .mul h4e146 h4e9

def h4e148 : IExpr := .add h4e30 h4e147

def h4e149 : IExpr := .mul h4e9 h4e148

def h4e150 : IExpr := .mul h4e7 h4e149

def h4e151 : IExpr := .mul h4e13 h4e150

def h4e152 : IExpr := .mul h4e5 h4e151

def h4e153 : IExpr := .add h4e145 h4e152

def h4e154 : IExpr := .mul h4e4 h4e153

def h4e155 : IExpr := .mul h4e3 h4e154

def h4e156 : IExpr := .add h4e143 h4e155

def h4e157 : IExpr := .mul h4e3 h4e156

def h4e158 : IExpr := .integer (-54)

def h4e159 : IExpr := .mul h4e158 h4e133

def h4e160 : IExpr := .mul h4e6 h4e9

def h4e161 : IExpr := .add h4e97 h4e160

def h4e162 : IExpr := .mul h4e9 h4e161

def h4e163 : IExpr := .mul h4e7 h4e162

def h4e164 : IExpr := .mul h4e13 h4e163

def h4e165 : IExpr := .mul h4e5 h4e164

def h4e166 : IExpr := .add h4e159 h4e165

def h4e167 : IExpr := .mul h4e50 h4e166

def h4e168 : IExpr := .add h4e157 h4e167

def h4e169 : IExpr := .mul h4e2 h4e168

def h4e170 : IExpr := .mul h4e6 h4e69

def h4e171 : IExpr := .mul h4e6 h4e71

def h4e172 : IExpr := .add h4e170 h4e171

def h4e173 : IExpr := .mul h4e36 h4e172

def h4e174 : IExpr := .mul h4e13 h4e173

def h4e175 : IExpr := .mul h4e5 h4e174

def h4e176 : IExpr := .mul h4e37 h4e91

def h4e177 : IExpr := .add h4e175 h4e176

def h4e178 : IExpr := .mul h4e3 h4e177

def h4e179 : IExpr := .mul h4e61 h4e69

def h4e180 : IExpr := .integer (9)

def h4e181 : IExpr := .mul h4e180 h4e71

def h4e182 : IExpr := .add h4e179 h4e181

def h4e183 : IExpr := .mul h4e50 h4e182

def h4e184 : IExpr := .mul h4e13 h4e183

def h4e185 : IExpr := .mul h4e5 h4e184

def h4e186 : IExpr := .add h4e178 h4e185

def h4e187 : IExpr := .mul h4e67 h4e186

def h4e188 : IExpr := .add h4e169 h4e187

def h4e189 : IExpr := .mul h4e2 h4e188

def h4e190 : IExpr := .mul h4e0 h4e189

def h4e191 : IExpr := .add h4e130 h4e190

def h4e192 : IExpr := .mul h4e0 h4e191

def h4e193 : IExpr := .mul h4e1 h4e1

def h4e194 : IExpr := .mul h4e54 h4e11

def h4e195 : IExpr := .integer (-32)

def h4e196 : IExpr := .integer (32)

def h4e197 : IExpr := .mul h4e196 h4e9

def h4e198 : IExpr := .add h4e195 h4e197

def h4e199 : IExpr := .mul h4e7 h4e198

def h4e200 : IExpr := .mul h4e13 h4e199

def h4e201 : IExpr := .add h4e194 h4e200

def h4e202 : IExpr := .mul h4e5 h4e201

def h4e203 : IExpr := .mul h4e76 h4e26

def h4e204 : IExpr := .add h4e202 h4e203

def h4e205 : IExpr := .mul h4e4 h4e204

def h4e206 : IExpr := .integer (-48)

def h4e207 : IExpr := .mul h4e206 h4e32

def h4e208 : IExpr := .add h4e205 h4e207

def h4e209 : IExpr := .mul h4e3 h4e208

def h4e210 : IExpr := .integer (60)

def h4e211 : IExpr := .mul h4e210 h4e11

def h4e212 : IExpr := .mul h4e195 h4e9

def h4e213 : IExpr := .add h4e196 h4e212

def h4e214 : IExpr := .mul h4e7 h4e213

def h4e215 : IExpr := .mul h4e13 h4e214

def h4e216 : IExpr := .add h4e211 h4e215

def h4e217 : IExpr := .mul h4e5 h4e216

def h4e218 : IExpr := .mul h4e206 h4e26

def h4e219 : IExpr := .add h4e217 h4e218

def h4e220 : IExpr := .mul h4e36 h4e219

def h4e221 : IExpr := .add h4e209 h4e220

def h4e222 : IExpr := .mul h4e3 h4e221

def h4e223 : IExpr := .integer (-18)

def h4e224 : IExpr := .mul h4e223 h4e11

def h4e225 : IExpr := .integer (-8)

def h4e226 : IExpr := .integer (8)

def h4e227 : IExpr := .mul h4e226 h4e9

def h4e228 : IExpr := .add h4e225 h4e227

def h4e229 : IExpr := .mul h4e7 h4e228

def h4e230 : IExpr := .mul h4e13 h4e229

def h4e231 : IExpr := .add h4e224 h4e230

def h4e232 : IExpr := .mul h4e5 h4e231

def h4e233 : IExpr := .integer (12)

def h4e234 : IExpr := .mul h4e233 h4e26

def h4e235 : IExpr := .add h4e232 h4e234

def h4e236 : IExpr := .mul h4e50 h4e235

def h4e237 : IExpr := .add h4e222 h4e236

def h4e238 : IExpr := .mul h4e67 h4e237

def h4e239 : IExpr := .mul h4e2 h4e238

def h4e240 : IExpr := .mul h4e103 h4e133

def h4e241 : IExpr := .integer (16)

def h4e242 : IExpr := .mul h4e241 h4e9

def h4e243 : IExpr := .add h4e226 h4e242

def h4e244 : IExpr := .mul h4e9 h4e243

def h4e245 : IExpr := .mul h4e7 h4e244

def h4e246 : IExpr := .mul h4e13 h4e245

def h4e247 : IExpr := .mul h4e5 h4e246

def h4e248 : IExpr := .add h4e240 h4e247

def h4e249 : IExpr := .mul h4e36 h4e248

def h4e250 : IExpr := .mul h4e53 h4e133

def h4e251 : IExpr := .integer (-16)

def h4e252 : IExpr := .add h4e251 h4e212

def h4e253 : IExpr := .mul h4e9 h4e252

def h4e254 : IExpr := .mul h4e7 h4e253

def h4e255 : IExpr := .mul h4e13 h4e254

def h4e256 : IExpr := .mul h4e5 h4e255

def h4e257 : IExpr := .add h4e250 h4e256

def h4e258 : IExpr := .mul h4e4 h4e257

def h4e259 : IExpr := .mul h4e3 h4e258

def h4e260 : IExpr := .add h4e249 h4e259

def h4e261 : IExpr := .mul h4e117 h4e260

def h4e262 : IExpr := .mul h4e3 h4e261

def h4e263 : IExpr := .add h4e239 h4e262

def h4e264 : IExpr := .mul h4e193 h4e263

def h4e265 : IExpr := .add h4e192 h4e264
end StackSorting.RationalLift
