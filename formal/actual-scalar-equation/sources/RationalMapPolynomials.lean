import BivariatePolynomial
import RationalMapLiterals
import ScalarPolynomialReification
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def aNPoly : BiPoly.Poly := [[0],[-4823712,1739232],[19903008,-6163728,440880],[-32166392,239448,2054656,-12320],[24635292,20543536,-6790820,450976],[-7510080,-28676000,1720144,605752],[-991528,14248240,8415540,-1604640],[1148136,-887376,-8145624,108144],[-194724,-1349856,2219256,1008288],[0,302616,157248,-547776],[0,0,-106272,82944]]
theorem aNPoly_eval (x y : FPS) : BiPoly.eval aNPoly x y=aN x y := by
  dsimp [aNPoly, aN, BiPoly.eval, IntPoly.eval]
  grind

def aDPoly : BiPoly.Poly := [[9647424,-3478464],[-46677636,19929132,-1911888],[92361738,-25826328,2014626,-262680],[-93931284,-22305702,13586376,-751746],[48459621,80868789,-21660051,1443339],[-7523526,-73657059,-4560792,3042231],[-4166142,26529657,26221053,-3803550],[2114430,-295215,-17394768,-1085328],[-284625,-2155878,3599604,2616696],[0,391068,269460,-1010556],[0,0,-128628,114048]]
theorem aDPoly_eval (x y : FPS) : BiPoly.eval aDPoly x y=aD x y := by
  dsimp [aDPoly, aD, BiPoly.eval, IntPoly.eval]
  grind

def tNPoly : BiPoly.Poly := [[126,-36,414],[-545,669,-1451,-137],[934,-2195,1824,681,-70],[-792,3090,-340,-1115,-45],[332,-2204,-1654,485,254],[-55,789,2063,356,-214],[0,-113,-1066,-444,-96],[0,0,210,264,72],[0,0,0,-72]]
theorem tNPoly_eval (x y : FPS) : BiPoly.eval tNPoly x y=tN x y := by
  dsimp [tNPoly, tN, BiPoly.eval, IntPoly.eval]
  grind

def tDPoly : BiPoly.Poly := [[1296,1296],[-5640,-3552,-264],[9664,4368,2704,-176],[-8112,-5192,-4424,136],[3312,5608,2128,952],[-520,-3128,-528,-1056],[0,600,528,144],[0,0,-144]]
theorem tDPoly_eval (x y : FPS) : BiPoly.eval tDPoly x y=tD x y := by
  dsimp [tDPoly, tD, BiPoly.eval, IntPoly.eval]
  grind

def uNPoly : BiPoly.Poly := [[-2353392,-15067542,110200308,-13450326,-52857648],[8955200,45090875,-428781429,124214965,81932205,-14682680],[-12632580,-43955705,613384190,-118328303,14400648,-25943080],[7533714,7834996,-385089686,-201090179,-9267693,32794536],[-1039982,12842468,88631730,351530481,-22108722,11649564],[-646506,-8477943,2455167,-165359808,-40716774,-11807352],[183546,1832967,140238,18827064,44370288,1086264],[0,-100116,-918918,1939680,-9470520]]
theorem uNPoly_eval (x y : FPS) : BiPoly.eval uNPoly x y=uN x y := by
  dsimp [uNPoly, uN, BiPoly.eval, IntPoly.eval]
  grind

def uDPoly : BiPoly.Poly := [[8706816,-9664188,90904872,-48917244,-105715296],[-32256464,36644638,-473549634,135326642,288699378,-29365360],[47168280,-13402306,893344012,-80551390,-257964480,-15132416],[-35069628,-74148088,-763715548,-276429286,-25390242,120027336],[14493284,98211592,316578468,522692754,172213548,-77904504],[-3409380,-44925366,-81601050,-315486648,-135404604,-37586880],[367092,7483950,22107276,70552224,64107504,41239152],[0,-200232,-3517452,-3445632,-18941040]]
theorem uDPoly_eval (x y : FPS) : BiPoly.eval uDPoly x y=uD x y := by
  dsimp [uDPoly, uD, BiPoly.eval, IntPoly.eval]
  grind

def iNPoly : BiPoly.Poly := [[-192,-300,1236],[622,108,-3638,400],[-726,1060,2766,1104,16],[354,-1366,-384,-3318,312],[-58,588,444,1356,384],[0,-90,-552,324,-720],[0,0,108]]
theorem iNPoly_eval (x y : FPS) : BiPoly.eval iNPoly x y=iN x y := by
  dsimp [iNPoly, iN, BiPoly.eval, IntPoly.eval]
  grind

def iDPoly : BiPoly.Poly := [[0,-162,-162],[0,543,282,33],[0,-665,-264,-305,22],[0,349,385,248,5],[0,-65,-316,-18,-114],[0,0,75,48,18],[0,0,0,-18]]
theorem iDPoly_eval (x y : FPS) : BiPoly.eval iDPoly x y=iD x y := by
  dsimp [iDPoly, iD, BiPoly.eval, IntPoly.eval]
  grind

def qNPoly : BiPoly.Poly := [[-268839000,-802397340,962654220],[1169748360,3193476012,-4188154752,433720224],[-2066177070,-5515330239,5374037010,-161720925,46059312],[1892029140,5444283330,-156751152,-2586728298,166292490],[-946246900,-3301090402,-5301533755,3365954191,-144462961],[245406860,1187147458,4875114360,-44259028,-537084452],[-25921390,-220890927,-1837805783,-1917712992,441424332],[0,14802108,275782650,1046220384,145620858],[0,0,-6329898,-173703666,-185354088],[0,0,0,2180628,36446580]]
theorem qNPoly_eval (x y : FPS) : BiPoly.eval qNPoly x y=qN x y := by
  dsimp [qNPoly, qN, BiPoly.eval, IntPoly.eval]
  grind

def qDPoly : BiPoly.Poly := [[472261338,1217015676,-2450153790],[-2306280714,-6703599180,10748750526,-670962072],[5320050962,12293004262,-16403256160,117391062,3405160],[-7419367907,-8377521067,4036034801,4035733571,-123557268],[6517991433,402433922,12339545263,-5980552106,-206952322],[-3504802105,987248176,-10739512339,583467373,377382165],[1074940707,858249577,2281968902,2850082835,90990270],[-162483782,-936223363,334049373,-1338212760,-249725646],[7690068,298735941,-165027066,144652032,71389728],[0,-36794952,23061006]]
theorem qDPoly_eval (x y : FPS) : BiPoly.eval qDPoly x y=qD x y := by
  dsimp [qDPoly, qD, BiPoly.eval, IntPoly.eval]
  grind

def scalarQPoly : BiPoly.Poly := [[-8100,-11016,80028],[51444,18252,-467820,121212],[-140841,94788,1068822,-349236,47583],[216756,-381312,-1228464,-13248,67968,5220],[-204775,609666,816316,1059340,-434593,48094,-100],[121420,-545072,-514200,-1441424,235008,9376,3380],[-44079,295164,515321,797680,524094,-195284,15095],[8956,-97068,-430040,-240468,-671588,77436,4044],[-781,18086,205778,136788,251778,155040,-30168],[0,-1488,-50844,-100632,-23076,-123804,648],[0,0,5103,33984,8604,20520,16092],[0,0,0,-3996,-6912,1944,-5184],[0,0,0,0,972]]
theorem scalarQPoly_eval (x y : FPS) : BiPoly.eval scalarQPoly x y=scalarPolynomialRing x y := by
  rw [scalarPolynomial_reification]
  dsimp [scalarQPoly, BiPoly.eval, IntPoly.eval, scalarLiteralFPS]
  grind

def mapPolyEnv : Nat → BiPoly.Poly
  | 0 => aNPoly
  | 1 => aDPoly
  | 2 => tNPoly
  | 3 => tDPoly
  | 4 => uNPoly
  | 5 => uDPoly
  | 6 => iNPoly
  | 7 => iDPoly
  | 8 => qNPoly
  | 9 => qDPoly
  | 10 => [[0,1]]
  | 11 => [[0],[1]]
  | _ => []

theorem mapPolyEnv_eval (x y : FPS) (n : Nat) :
    BiPoly.eval (mapPolyEnv n) x y=mapEnv x y n := by
  cases n with
  | zero =>
    exact aNPoly_eval x y
  | succ n =>
    cases n with
    | zero =>
      exact aDPoly_eval x y
    | succ n =>
      cases n with
      | zero =>
        exact tNPoly_eval x y
      | succ n =>
        cases n with
        | zero =>
          exact tDPoly_eval x y
        | succ n =>
          cases n with
          | zero =>
            exact uNPoly_eval x y
          | succ n =>
            cases n with
            | zero =>
              exact uDPoly_eval x y
            | succ n =>
              cases n with
              | zero =>
                exact iNPoly_eval x y
              | succ n =>
                cases n with
                | zero =>
                  exact iDPoly_eval x y
                | succ n =>
                  cases n with
                  | zero =>
                    exact qNPoly_eval x y
                  | succ n =>
                    cases n with
                    | zero =>
                      exact qDPoly_eval x y
                    | succ n =>
                      cases n with
                      | zero =>
                        change BiPoly.eval [[0,1]] x y=x
                        dsimp [BiPoly.eval, IntPoly.eval]
                        grind
                      | succ n =>
                        cases n with
                        | zero =>
                          change BiPoly.eval [[0],[1]] x y=y
                          dsimp [BiPoly.eval, IntPoly.eval]
                          grind
                        | succ n =>
                          rfl

theorem homogeneous_poly_eval (e : IExpr) (x y : FPS) :
    BiPoly.eval (e.toBi mapPolyEnv) x y=e.eval (mapEnv x y) := by
  rw [IExpr.eval_toBi]
  have he : (fun n => BiPoly.eval (mapPolyEnv n) x y)=mapEnv x y :=
    funext (mapPolyEnv_eval x y)
  rw [he]

#print axioms homogeneous_poly_eval
#print axioms scalarQPoly_eval
end StackSorting.RationalLift
