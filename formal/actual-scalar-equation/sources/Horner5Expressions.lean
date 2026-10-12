import RationalDivisibilityLiterals5
import BivariatePolynomial
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

def h5e0 : IExpr := .var 0

def h5e1 : IExpr := .var 1

def h5e2 : IExpr := .var 2

def h5e3 : IExpr := .var 4

def h5e4 : IExpr := .var 5

def h5e5 : IExpr := .var 7

def h5e6 : IExpr := .var 8

def h5e7 : IExpr := .integer (96)

def h5e8 : IExpr := .integer (-96)

def h5e9 : IExpr := .var 11

def h5e10 : IExpr := .mul h5e8 h5e9

def h5e11 : IExpr := .var 10

def h5e12 : IExpr := .integer (-192)

def h5e13 : IExpr := .mul h5e8 h5e11

def h5e14 : IExpr := .integer (288)

def h5e15 : IExpr := .mul h5e14 h5e9

def h5e16 : IExpr := .add h5e13 h5e15

def h5e17 : IExpr := .add h5e12 h5e16

def h5e18 : IExpr := .mul h5e11 h5e17

def h5e19 : IExpr := .add h5e10 h5e18

def h5e20 : IExpr := .add h5e7 h5e19

def h5e21 : IExpr := .mul h5e6 h5e20

def h5e22 : IExpr := .var 9

def h5e23 : IExpr := .mul h5e11 h5e11

def h5e24 : IExpr := .integer (72)

def h5e25 : IExpr := .integer (-72)

def h5e26 : IExpr := .mul h5e25 h5e9

def h5e27 : IExpr := .mul h5e24 h5e11

def h5e28 : IExpr := .add h5e26 h5e27

def h5e29 : IExpr := .add h5e24 h5e28

def h5e30 : IExpr := .mul h5e23 h5e29

def h5e31 : IExpr := .mul h5e22 h5e30

def h5e32 : IExpr := .add h5e21 h5e31

def h5e33 : IExpr := .mul h5e5 h5e32

def h5e34 : IExpr := .var 6

def h5e35 : IExpr := .integer (-144)

def h5e36 : IExpr := .integer (144)

def h5e37 : IExpr := .mul h5e36 h5e9

def h5e38 : IExpr := .integer (-288)

def h5e39 : IExpr := .mul h5e38 h5e9

def h5e40 : IExpr := .add h5e36 h5e39

def h5e41 : IExpr := .mul h5e11 h5e40

def h5e42 : IExpr := .add h5e37 h5e41

def h5e43 : IExpr := .add h5e35 h5e42

def h5e44 : IExpr := .mul h5e11 h5e43

def h5e45 : IExpr := .mul h5e6 h5e44

def h5e46 : IExpr := .mul h5e34 h5e45

def h5e47 : IExpr := .add h5e33 h5e46

def h5e48 : IExpr := .mul h5e4 h5e47

def h5e49 : IExpr := .mul h5e35 h5e9

def h5e50 : IExpr := .mul h5e36 h5e11

def h5e51 : IExpr := .add h5e49 h5e50

def h5e52 : IExpr := .add h5e36 h5e51

def h5e53 : IExpr := .mul h5e23 h5e52

def h5e54 : IExpr := .mul h5e3 h5e53

def h5e55 : IExpr := .mul h5e22 h5e54

def h5e56 : IExpr := .mul h5e5 h5e55

def h5e57 : IExpr := .add h5e48 h5e56

def h5e58 : IExpr := .mul h5e3 h5e57

def h5e59 : IExpr := .mul h5e4 h5e4

def h5e60 : IExpr := .mul h5e7 h5e9

def h5e61 : IExpr := .integer (192)

def h5e62 : IExpr := .mul h5e7 h5e11

def h5e63 : IExpr := .add h5e39 h5e62

def h5e64 : IExpr := .add h5e61 h5e63

def h5e65 : IExpr := .mul h5e11 h5e64

def h5e66 : IExpr := .add h5e60 h5e65

def h5e67 : IExpr := .add h5e8 h5e66

def h5e68 : IExpr := .mul h5e6 h5e67

def h5e69 : IExpr := .integer (-180)

def h5e70 : IExpr := .mul h5e69 h5e11

def h5e71 : IExpr := .integer (180)

def h5e72 : IExpr := .mul h5e71 h5e9

def h5e73 : IExpr := .add h5e70 h5e72

def h5e74 : IExpr := .add h5e69 h5e73

def h5e75 : IExpr := .mul h5e23 h5e74

def h5e76 : IExpr := .mul h5e22 h5e75

def h5e77 : IExpr := .add h5e68 h5e76

def h5e78 : IExpr := .mul h5e5 h5e77

def h5e79 : IExpr := .add h5e35 h5e15

def h5e80 : IExpr := .mul h5e11 h5e79

def h5e81 : IExpr := .add h5e49 h5e80

def h5e82 : IExpr := .add h5e36 h5e81

def h5e83 : IExpr := .mul h5e11 h5e82

def h5e84 : IExpr := .mul h5e6 h5e83

def h5e85 : IExpr := .mul h5e34 h5e84

def h5e86 : IExpr := .add h5e78 h5e85

def h5e87 : IExpr := .mul h5e59 h5e86

def h5e88 : IExpr := .add h5e58 h5e87

def h5e89 : IExpr := .mul h5e3 h5e88

def h5e90 : IExpr := .mul h5e4 h5e59

def h5e91 : IExpr := .integer (24)

def h5e92 : IExpr := .integer (-24)

def h5e93 : IExpr := .mul h5e92 h5e9

def h5e94 : IExpr := .integer (-48)

def h5e95 : IExpr := .mul h5e92 h5e11

def h5e96 : IExpr := .mul h5e24 h5e9

def h5e97 : IExpr := .add h5e95 h5e96

def h5e98 : IExpr := .add h5e94 h5e97

def h5e99 : IExpr := .mul h5e11 h5e98

def h5e100 : IExpr := .add h5e93 h5e99

def h5e101 : IExpr := .add h5e91 h5e100

def h5e102 : IExpr := .mul h5e6 h5e101

def h5e103 : IExpr := .integer (54)

def h5e104 : IExpr := .integer (-54)

def h5e105 : IExpr := .mul h5e104 h5e9

def h5e106 : IExpr := .mul h5e103 h5e11

def h5e107 : IExpr := .add h5e105 h5e106

def h5e108 : IExpr := .add h5e103 h5e107

def h5e109 : IExpr := .mul h5e23 h5e108

def h5e110 : IExpr := .mul h5e22 h5e109

def h5e111 : IExpr := .add h5e102 h5e110

def h5e112 : IExpr := .mul h5e5 h5e111

def h5e113 : IExpr := .integer (-36)

def h5e114 : IExpr := .integer (36)

def h5e115 : IExpr := .mul h5e114 h5e9

def h5e116 : IExpr := .add h5e114 h5e26

def h5e117 : IExpr := .mul h5e11 h5e116

def h5e118 : IExpr := .add h5e115 h5e117

def h5e119 : IExpr := .add h5e113 h5e118

def h5e120 : IExpr := .mul h5e11 h5e119

def h5e121 : IExpr := .mul h5e6 h5e120

def h5e122 : IExpr := .mul h5e34 h5e121

def h5e123 : IExpr := .add h5e112 h5e122

def h5e124 : IExpr := .mul h5e90 h5e123

def h5e125 : IExpr := .add h5e89 h5e124

def h5e126 : IExpr := .mul h5e2 h5e125

def h5e127 : IExpr := .var 3

def h5e128 : IExpr := .mul h5e113 h5e11

def h5e129 : IExpr := .add h5e128 h5e115

def h5e130 : IExpr := .add h5e113 h5e129

def h5e131 : IExpr := .mul h5e23 h5e130

def h5e132 : IExpr := .mul h5e6 h5e131

def h5e133 : IExpr := .mul h5e34 h5e132

def h5e134 : IExpr := .mul h5e91 h5e11

def h5e135 : IExpr := .mul h5e91 h5e9

def h5e136 : IExpr := .add h5e134 h5e135

def h5e137 : IExpr := .mul h5e11 h5e136

def h5e138 : IExpr := .add h5e93 h5e137

def h5e139 : IExpr := .add h5e91 h5e138

def h5e140 : IExpr := .mul h5e11 h5e139

def h5e141 : IExpr := .mul h5e6 h5e140

def h5e142 : IExpr := .mul h5e5 h5e141

def h5e143 : IExpr := .add h5e133 h5e142

def h5e144 : IExpr := .mul h5e59 h5e143

def h5e145 : IExpr := .add h5e10 h5e62

def h5e146 : IExpr := .add h5e7 h5e145

def h5e147 : IExpr := .mul h5e23 h5e146

def h5e148 : IExpr := .mul h5e4 h5e147

def h5e149 : IExpr := .mul h5e3 h5e148

def h5e150 : IExpr := .mul h5e6 h5e149

def h5e151 : IExpr := .mul h5e5 h5e150

def h5e152 : IExpr := .add h5e144 h5e151

def h5e153 : IExpr := .mul h5e3 h5e152

def h5e154 : IExpr := .integer (18)

def h5e155 : IExpr := .integer (-18)

def h5e156 : IExpr := .mul h5e155 h5e9

def h5e157 : IExpr := .mul h5e154 h5e11

def h5e158 : IExpr := .add h5e156 h5e157

def h5e159 : IExpr := .add h5e154 h5e158

def h5e160 : IExpr := .mul h5e23 h5e159

def h5e161 : IExpr := .mul h5e6 h5e160

def h5e162 : IExpr := .mul h5e34 h5e161

def h5e163 : IExpr := .integer (-12)

def h5e164 : IExpr := .integer (12)

def h5e165 : IExpr := .mul h5e164 h5e9

def h5e166 : IExpr := .add h5e128 h5e165

def h5e167 : IExpr := .add h5e92 h5e166

def h5e168 : IExpr := .mul h5e11 h5e167

def h5e169 : IExpr := .add h5e165 h5e168

def h5e170 : IExpr := .add h5e163 h5e169

def h5e171 : IExpr := .mul h5e11 h5e170

def h5e172 : IExpr := .mul h5e6 h5e171

def h5e173 : IExpr := .mul h5e5 h5e172

def h5e174 : IExpr := .add h5e162 h5e173

def h5e175 : IExpr := .mul h5e90 h5e174

def h5e176 : IExpr := .add h5e153 h5e175

def h5e177 : IExpr := .mul h5e127 h5e176

def h5e178 : IExpr := .add h5e126 h5e177

def h5e179 : IExpr := .mul h5e2 h5e178

def h5e180 : IExpr := .mul h5e127 h5e127

def h5e181 : IExpr := .integer (-60)

def h5e182 : IExpr := .mul h5e181 h5e11

def h5e183 : IExpr := .integer (60)

def h5e184 : IExpr := .mul h5e183 h5e9

def h5e185 : IExpr := .add h5e182 h5e184

def h5e186 : IExpr := .add h5e181 h5e185

def h5e187 : IExpr := .mul h5e23 h5e186

def h5e188 : IExpr := .mul h5e59 h5e187

def h5e189 : IExpr := .mul h5e6 h5e188

def h5e190 : IExpr := .mul h5e5 h5e189

def h5e191 : IExpr := .integer (48)

def h5e192 : IExpr := .mul h5e94 h5e9

def h5e193 : IExpr := .mul h5e191 h5e11

def h5e194 : IExpr := .add h5e192 h5e193

def h5e195 : IExpr := .add h5e191 h5e194

def h5e196 : IExpr := .mul h5e23 h5e195

def h5e197 : IExpr := .mul h5e4 h5e196

def h5e198 : IExpr := .mul h5e3 h5e197

def h5e199 : IExpr := .mul h5e6 h5e198

def h5e200 : IExpr := .mul h5e5 h5e199

def h5e201 : IExpr := .add h5e190 h5e200

def h5e202 : IExpr := .mul h5e180 h5e201

def h5e203 : IExpr := .mul h5e3 h5e202

def h5e204 : IExpr := .add h5e179 h5e203

def h5e205 : IExpr := .mul h5e1 h5e204

def h5e206 : IExpr := .integer (216)

def h5e207 : IExpr := .integer (-216)

def h5e208 : IExpr := .mul h5e207 h5e9

def h5e209 : IExpr := .mul h5e206 h5e11

def h5e210 : IExpr := .add h5e208 h5e209

def h5e211 : IExpr := .add h5e206 h5e210

def h5e212 : IExpr := .mul h5e23 h5e211

def h5e213 : IExpr := .mul h5e6 h5e212

def h5e214 : IExpr := .mul h5e34 h5e213

def h5e215 : IExpr := .mul h5e38 h5e11

def h5e216 : IExpr := .add h5e35 h5e215

def h5e217 : IExpr := .mul h5e11 h5e216

def h5e218 : IExpr := .add h5e37 h5e217

def h5e219 : IExpr := .add h5e35 h5e218

def h5e220 : IExpr := .mul h5e11 h5e219

def h5e221 : IExpr := .mul h5e6 h5e220

def h5e222 : IExpr := .mul h5e5 h5e221

def h5e223 : IExpr := .add h5e214 h5e222

def h5e224 : IExpr := .mul h5e59 h5e223

def h5e225 : IExpr := .mul h5e207 h5e11

def h5e226 : IExpr := .mul h5e206 h5e9

def h5e227 : IExpr := .add h5e225 h5e226

def h5e228 : IExpr := .add h5e207 h5e227

def h5e229 : IExpr := .mul h5e23 h5e228

def h5e230 : IExpr := .mul h5e6 h5e229

def h5e231 : IExpr := .mul h5e34 h5e230

def h5e232 : IExpr := .mul h5e14 h5e11

def h5e233 : IExpr := .add h5e36 h5e232

def h5e234 : IExpr := .mul h5e11 h5e233

def h5e235 : IExpr := .add h5e49 h5e234

def h5e236 : IExpr := .add h5e36 h5e235

def h5e237 : IExpr := .mul h5e11 h5e236

def h5e238 : IExpr := .mul h5e6 h5e237

def h5e239 : IExpr := .mul h5e5 h5e238

def h5e240 : IExpr := .add h5e231 h5e239

def h5e241 : IExpr := .mul h5e4 h5e240

def h5e242 : IExpr := .mul h5e3 h5e241

def h5e243 : IExpr := .add h5e224 h5e242

def h5e244 : IExpr := .mul h5e3 h5e243

def h5e245 : IExpr := .mul h5e104 h5e11

def h5e246 : IExpr := .mul h5e103 h5e9

def h5e247 : IExpr := .add h5e245 h5e246

def h5e248 : IExpr := .add h5e104 h5e247

def h5e249 : IExpr := .mul h5e23 h5e248

def h5e250 : IExpr := .mul h5e6 h5e249

def h5e251 : IExpr := .mul h5e34 h5e250

def h5e252 : IExpr := .mul h5e113 h5e9

def h5e253 : IExpr := .add h5e114 h5e27

def h5e254 : IExpr := .mul h5e11 h5e253

def h5e255 : IExpr := .add h5e252 h5e254

def h5e256 : IExpr := .add h5e114 h5e255

def h5e257 : IExpr := .mul h5e11 h5e256

def h5e258 : IExpr := .mul h5e6 h5e257

def h5e259 : IExpr := .mul h5e5 h5e258

def h5e260 : IExpr := .add h5e251 h5e259

def h5e261 : IExpr := .mul h5e90 h5e260

def h5e262 : IExpr := .add h5e244 h5e261

def h5e263 : IExpr := .mul h5e2 h5e262

def h5e264 : IExpr := .mul h5e59 h5e30

def h5e265 : IExpr := .mul h5e6 h5e264

def h5e266 : IExpr := .mul h5e5 h5e265

def h5e267 : IExpr := .mul h5e4 h5e75

def h5e268 : IExpr := .mul h5e3 h5e267

def h5e269 : IExpr := .mul h5e6 h5e268

def h5e270 : IExpr := .mul h5e5 h5e269

def h5e271 : IExpr := .add h5e266 h5e270

def h5e272 : IExpr := .mul h5e3 h5e271

def h5e273 : IExpr := .integer (9)

def h5e274 : IExpr := .integer (-9)

def h5e275 : IExpr := .mul h5e274 h5e9

def h5e276 : IExpr := .mul h5e273 h5e11

def h5e277 : IExpr := .add h5e275 h5e276

def h5e278 : IExpr := .add h5e273 h5e277

def h5e279 : IExpr := .mul h5e23 h5e278

def h5e280 : IExpr := .mul h5e90 h5e279

def h5e281 : IExpr := .mul h5e6 h5e280

def h5e282 : IExpr := .mul h5e5 h5e281

def h5e283 : IExpr := .add h5e272 h5e282

def h5e284 : IExpr := .mul h5e127 h5e283

def h5e285 : IExpr := .add h5e263 h5e284

def h5e286 : IExpr := .mul h5e2 h5e285

def h5e287 : IExpr := .mul h5e0 h5e286

def h5e288 : IExpr := .add h5e205 h5e287

def h5e289 : IExpr := .mul h5e0 h5e288

def h5e290 : IExpr := .mul h5e1 h5e1

def h5e291 : IExpr := .integer (-32)

def h5e292 : IExpr := .integer (32)

def h5e293 : IExpr := .mul h5e292 h5e9

def h5e294 : IExpr := .integer (64)

def h5e295 : IExpr := .mul h5e292 h5e11

def h5e296 : IExpr := .add h5e10 h5e295

def h5e297 : IExpr := .add h5e294 h5e296

def h5e298 : IExpr := .mul h5e11 h5e297

def h5e299 : IExpr := .add h5e293 h5e298

def h5e300 : IExpr := .add h5e291 h5e299

def h5e301 : IExpr := .mul h5e6 h5e300

def h5e302 : IExpr := .add h5e95 h5e135

def h5e303 : IExpr := .add h5e92 h5e302

def h5e304 : IExpr := .mul h5e23 h5e303

def h5e305 : IExpr := .mul h5e22 h5e304

def h5e306 : IExpr := .add h5e301 h5e305

def h5e307 : IExpr := .mul h5e5 h5e306

def h5e308 : IExpr := .add h5e94 h5e60

def h5e309 : IExpr := .mul h5e11 h5e308

def h5e310 : IExpr := .add h5e192 h5e309

def h5e311 : IExpr := .add h5e191 h5e310

def h5e312 : IExpr := .mul h5e11 h5e311

def h5e313 : IExpr := .mul h5e6 h5e312

def h5e314 : IExpr := .mul h5e34 h5e313

def h5e315 : IExpr := .add h5e307 h5e314

def h5e316 : IExpr := .mul h5e4 h5e315

def h5e317 : IExpr := .mul h5e94 h5e11

def h5e318 : IExpr := .mul h5e191 h5e9

def h5e319 : IExpr := .add h5e317 h5e318

def h5e320 : IExpr := .add h5e94 h5e319

def h5e321 : IExpr := .mul h5e23 h5e320

def h5e322 : IExpr := .mul h5e3 h5e321

def h5e323 : IExpr := .mul h5e22 h5e322

def h5e324 : IExpr := .mul h5e5 h5e323

def h5e325 : IExpr := .add h5e316 h5e324

def h5e326 : IExpr := .mul h5e3 h5e325

def h5e327 : IExpr := .mul h5e291 h5e9

def h5e328 : IExpr := .integer (-64)

def h5e329 : IExpr := .mul h5e291 h5e11

def h5e330 : IExpr := .add h5e329 h5e60

def h5e331 : IExpr := .add h5e328 h5e330

def h5e332 : IExpr := .mul h5e11 h5e331

def h5e333 : IExpr := .add h5e327 h5e332

def h5e334 : IExpr := .add h5e292 h5e333

def h5e335 : IExpr := .mul h5e6 h5e334

def h5e336 : IExpr := .mul h5e181 h5e9

def h5e337 : IExpr := .mul h5e183 h5e11

def h5e338 : IExpr := .add h5e336 h5e337

def h5e339 : IExpr := .add h5e183 h5e338

def h5e340 : IExpr := .mul h5e23 h5e339

def h5e341 : IExpr := .mul h5e22 h5e340

def h5e342 : IExpr := .add h5e335 h5e341

def h5e343 : IExpr := .mul h5e5 h5e342

def h5e344 : IExpr := .add h5e191 h5e10

def h5e345 : IExpr := .mul h5e11 h5e344

def h5e346 : IExpr := .add h5e318 h5e345

def h5e347 : IExpr := .add h5e94 h5e346

def h5e348 : IExpr := .mul h5e11 h5e347

def h5e349 : IExpr := .mul h5e6 h5e348

def h5e350 : IExpr := .mul h5e34 h5e349

def h5e351 : IExpr := .add h5e343 h5e350

def h5e352 : IExpr := .mul h5e59 h5e351

def h5e353 : IExpr := .add h5e326 h5e352

def h5e354 : IExpr := .mul h5e3 h5e353

def h5e355 : IExpr := .integer (-8)

def h5e356 : IExpr := .integer (8)

def h5e357 : IExpr := .mul h5e356 h5e9

def h5e358 : IExpr := .integer (16)

def h5e359 : IExpr := .mul h5e356 h5e11

def h5e360 : IExpr := .add h5e93 h5e359

def h5e361 : IExpr := .add h5e358 h5e360

def h5e362 : IExpr := .mul h5e11 h5e361

def h5e363 : IExpr := .add h5e357 h5e362

def h5e364 : IExpr := .add h5e355 h5e363

def h5e365 : IExpr := .mul h5e6 h5e364

def h5e366 : IExpr := .mul h5e155 h5e11

def h5e367 : IExpr := .mul h5e154 h5e9

def h5e368 : IExpr := .add h5e366 h5e367

def h5e369 : IExpr := .add h5e155 h5e368

def h5e370 : IExpr := .mul h5e23 h5e369

def h5e371 : IExpr := .mul h5e22 h5e370

def h5e372 : IExpr := .add h5e365 h5e371

def h5e373 : IExpr := .mul h5e5 h5e372

def h5e374 : IExpr := .mul h5e163 h5e9

def h5e375 : IExpr := .add h5e163 h5e135

def h5e376 : IExpr := .mul h5e11 h5e375

def h5e377 : IExpr := .add h5e374 h5e376

def h5e378 : IExpr := .add h5e164 h5e377

def h5e379 : IExpr := .mul h5e11 h5e378

def h5e380 : IExpr := .mul h5e6 h5e379

def h5e381 : IExpr := .mul h5e34 h5e380

def h5e382 : IExpr := .add h5e373 h5e381

def h5e383 : IExpr := .mul h5e90 h5e382

def h5e384 : IExpr := .add h5e354 h5e383

def h5e385 : IExpr := .mul h5e127 h5e384

def h5e386 : IExpr := .mul h5e2 h5e385

def h5e387 : IExpr := .mul h5e163 h5e11

def h5e388 : IExpr := .add h5e387 h5e165

def h5e389 : IExpr := .add h5e163 h5e388

def h5e390 : IExpr := .mul h5e23 h5e389

def h5e391 : IExpr := .mul h5e6 h5e390

def h5e392 : IExpr := .mul h5e34 h5e391

def h5e393 : IExpr := .mul h5e355 h5e9

def h5e394 : IExpr := .mul h5e358 h5e11

def h5e395 : IExpr := .add h5e356 h5e394

def h5e396 : IExpr := .mul h5e11 h5e395

def h5e397 : IExpr := .add h5e393 h5e396

def h5e398 : IExpr := .add h5e356 h5e397

def h5e399 : IExpr := .mul h5e11 h5e398

def h5e400 : IExpr := .mul h5e6 h5e399

def h5e401 : IExpr := .mul h5e5 h5e400

def h5e402 : IExpr := .add h5e392 h5e401

def h5e403 : IExpr := .mul h5e59 h5e402

def h5e404 : IExpr := .add h5e93 h5e134

def h5e405 : IExpr := .add h5e91 h5e404

def h5e406 : IExpr := .mul h5e23 h5e405

def h5e407 : IExpr := .mul h5e6 h5e406

def h5e408 : IExpr := .mul h5e34 h5e407

def h5e409 : IExpr := .integer (-16)

def h5e410 : IExpr := .mul h5e358 h5e9

def h5e411 : IExpr := .add h5e409 h5e329

def h5e412 : IExpr := .mul h5e11 h5e411

def h5e413 : IExpr := .add h5e410 h5e412

def h5e414 : IExpr := .add h5e409 h5e413

def h5e415 : IExpr := .mul h5e11 h5e414

def h5e416 : IExpr := .mul h5e6 h5e415

def h5e417 : IExpr := .mul h5e5 h5e416

def h5e418 : IExpr := .add h5e408 h5e417

def h5e419 : IExpr := .mul h5e4 h5e418

def h5e420 : IExpr := .mul h5e3 h5e419

def h5e421 : IExpr := .add h5e403 h5e420

def h5e422 : IExpr := .mul h5e180 h5e421

def h5e423 : IExpr := .mul h5e3 h5e422

def h5e424 : IExpr := .add h5e386 h5e423

def h5e425 : IExpr := .mul h5e290 h5e424

def h5e426 : IExpr := .add h5e289 h5e425
end StackSorting.RationalLift
