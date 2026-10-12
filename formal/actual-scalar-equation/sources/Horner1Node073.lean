import BivariateRowEquality
import Horner1Base
import Horner1Node072
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p73 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 112886571455999), (Int.negSucc 619146281295359), (Int.negSucc 663875416955519), (Int.ofNat 280252902948480), (Int.ofNat 639979788862080), (Int.ofNat 202111178797440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1247940142525440), (Int.ofNat 6355735989654528), (Int.ofNat 5441258105678592), (Int.negSucc 3467290066806527), (Int.negSucc 5206578156473471), (Int.negSucc 1397106994010111), (Int.ofNat 8718837107328)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6355390091961599), (Int.negSucc 30384490509400319), (Int.negSucc 21850219269116927), (Int.ofNat 14312784721285152), (Int.ofNat 19022294426536512), (Int.ofNat 6657584906829312), (Int.ofNat 729870884861760), (Int.negSucc 73936199083679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 19754340304746240), (Int.ofNat 90146691979013376), (Int.ofNat 61531422134335488), (Int.negSucc 24604534560429791), (Int.negSucc 45449140770889919), (Int.negSucc 25016607759492287), (Int.negSucc 4528994716119743), (Int.ofNat 487518199928352), (Int.negSucc 13711429353599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 41849350131863519), (Int.negSucc 186644890111895135), (Int.negSucc 143159479991743319), (Int.negSucc 1177629469347455), (Int.ofNat 81591878811985704), (Int.ofNat 62759302333098336), (Int.ofNat 15396520111579512), (Int.ofNat 95172026262336), (Int.negSucc 137666327407271), (Int.ofNat 6540273780480)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 63892555835506560), (Int.ofNat 287300565152322048), (Int.ofNat 283592866300519392), (Int.ofNat 98597889693836640), (Int.negSucc 99536415116915231), (Int.negSucc 104553890845886159), (Int.negSucc 40652696053999583), (Int.negSucc 5526489427773695), (Int.ofNat 1050127359865056), (Int.negSucc 68867428062095), (Int.ofNat 2214389675520)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 72463050001000799), (Int.negSucc 341277722010760607), (Int.negSucc 459595939741455911), (Int.negSucc 259756456556076119), (Int.ofNat 39499585643258448), (Int.ofNat 122169303699927384), (Int.ofNat 77557860540251544), (Int.ofNat 17501811540475320), (Int.negSucc 1138917264132287), (Int.ofNat 2780655150408), (Int.negSucc 2397830104031), (Int.ofNat 178341656064)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 61992371010800640), (Int.ofNat 319350652729871232), (Int.ofNat 587250270888178752), (Int.ofNat 435412958670175104), (Int.ofNat 121336611591513792), (Int.negSucc 91724396653248911), (Int.negSucc 96573469163377247), (Int.negSucc 34342128084357983), (Int.negSucc 3638817505332479), (Int.ofNat 783992732901072), (Int.negSucc 45135811009055), (Int.ofNat 724948910400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 40184048229384639), (Int.negSucc 237153989262813503), (Int.negSucc 582032754605881327), (Int.negSucc 561170795819250191), (Int.negSucc 306338142708346055), (Int.negSucc 3453157260072215), (Int.ofNat 72908009442136352), (Int.ofNat 47618010103710912), (Int.ofNat 11817043003200880), (Int.negSucc 1071158302085079), (Int.ofNat 45541057065384), (Int.negSucc 2105742012127)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 19633180826814720), (Int.ofNat 139202212492177536), (Int.ofNat 444939166535207232), (Int.ofNat 576806562001568352), (Int.ofNat 410940738891550848), (Int.ofNat 136714875112947984), (Int.negSucc 17978238898643039), (Int.negSucc 41005901153229743), (Int.negSucc 16739031221513951), (Int.negSucc 1533324136258847), (Int.ofNat 270149162891712), (Int.negSucc 9101801474831)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7115122507258559), (Int.negSucc 63654214312463807), (Int.negSucc 261040516363599311), (Int.negSucc 466750633743027983), (Int.negSucc 403431629682662495), (Int.negSucc 227416864017664319), (Int.negSucc 43831995554824463), (Int.ofNat 13767979526228064), (Int.ofNat 14588239138852416), (Int.ofNat 4711322928511944), (Int.negSucc 356386818536279), (Int.ofNat 10924105151928)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1854287863804160), (Int.ofNat 22110978514335360), (Int.ofNat 116306803892999680), (Int.ofNat 290020405729895936), (Int.ofNat 316936947480181824), (Int.ofNat 226145176418753536), (Int.ofNat 88348755677421184), (Int.ofNat 13719745392791520), (Int.negSucc 6084916400300799), (Int.negSucc 4388512623588079), (Int.negSucc 433715698526495), (Int.ofNat 39203983123712)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 328482524473439), (Int.negSucc 5609542301938271), (Int.negSucc 38555795105202743), (Int.negSucc 134744705796085919), (Int.negSucc 199962488034827783), (Int.negSucc 164321826980821487), (Int.negSucc 94139855570480759), (Int.negSucc 27788081000220479), (Int.negSucc 3138839924843303), (Int.ofNat 1550326895647512), (Int.ofNat 972422812519296), (Int.negSucc 37159227020447)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 35406359164800), (Int.ofNat 975699927381888), (Int.ofNat 9172449875370720), (Int.ofNat 45357936880056960), (Int.ofNat 97215361308799776), (Int.ofNat 95635195532546064), (Int.ofNat 67208851491146304), (Int.ofNat 28358562879232704), (Int.ofNat 7349189952884352), (Int.ofNat 718583252850000), (Int.negSucc 461063466883583), (Int.negSucc 58667336842415)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1752285963999), (Int.negSucc 103586353529759), (Int.negSucc 1470695478121351), (Int.negSucc 10570747719875959), (Int.negSucc 34403914273212431), (Int.negSucc 45291528182245479), (Int.negSucc 35293591938091607), (Int.negSucc 19926878948365655), (Int.negSucc 6699618251279999), (Int.negSucc 1437580677883055), (Int.negSucc 142038271426031), (Int.ofNat 70848320258400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5044359340800), (Int.ofNat 141078691680960), (Int.ofNat 1580827666537440), (Int.ofNat 8283902482897728), (Int.ofNat 16444247671563600), (Int.ofNat 14802995298112512), (Int.ofNat 9878313025559136), (Int.ofNat 4195310443128768), (Int.ofNat 1167616143250464), (Int.ofNat 237888973250784), (Int.negSucc 1474576432991)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6040451894399), (Int.negSucc 130965594636431), (Int.negSucc 1229744411165399), (Int.negSucc 4140432602717975), (Int.negSucc 5055445233869855), (Int.negSucc 3599702050272959), (Int.negSucc 1900746216751967), (Int.negSucc 631945902244031), (Int.negSucc 132509407960511), (Int.negSucc 23276123127935)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4141059232320), (Int.ofNat 92673416626560), (Int.ofNat 633828527706096), (Int.ofNat 1279498386927744), (Int.ofNat 1040704206699600), (Int.ofNat 611799754096512), (Int.ofNat 237508483416192), (Int.ofNat 54924662791296), (Int.ofNat 10304755785792)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1920687720479), (Int.negSucc 46442170964591), (Int.negSucc 201388981907951), (Int.negSucc 238807779435359), (Int.negSucc 143560625615999), (Int.negSucc 61123389006527), (Int.negSucc 16711110077759), (Int.negSucc 1677051910655)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 628084953792), (Int.ofNat 14715576812448), (Int.ofNat 36529562852640), (Int.ofNat 25844341686912), (Int.ofNat 10923930755136), (Int.ofNat 2855918487168), (Int.ofNat 94469535360)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 127017320831), (Int.negSucc 2598770723903), (Int.negSucc 3258790418879), (Int.negSucc 1373457835007), (Int.negSucc 188939070719)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11304375552), (Int.ofNat 194591258496), (Int.ofNat 94469535360)]]

theorem h1n73_arithmetic_row0 :
    (BiPoly.mul h1p6 h1p72).getD 0 []=h1p73.getD 0 [] := by
  decide +kernel

theorem h1n73_arithmetic_row1 :
    (BiPoly.mul h1p6 h1p72).getD 1 []=h1p73.getD 1 [] := by
  decide +kernel

theorem h1n73_arithmetic_row2 :
    (BiPoly.mul h1p6 h1p72).getD 2 []=h1p73.getD 2 [] := by
  decide +kernel

theorem h1n73_arithmetic_row3 :
    (BiPoly.mul h1p6 h1p72).getD 3 []=h1p73.getD 3 [] := by
  decide +kernel

theorem h1n73_arithmetic_row4 :
    (BiPoly.mul h1p6 h1p72).getD 4 []=h1p73.getD 4 [] := by
  decide +kernel

theorem h1n73_arithmetic_row5 :
    (BiPoly.mul h1p6 h1p72).getD 5 []=h1p73.getD 5 [] := by
  decide +kernel

theorem h1n73_arithmetic_row6 :
    (BiPoly.mul h1p6 h1p72).getD 6 []=h1p73.getD 6 [] := by
  decide +kernel

theorem h1n73_arithmetic_row7 :
    (BiPoly.mul h1p6 h1p72).getD 7 []=h1p73.getD 7 [] := by
  decide +kernel

theorem h1n73_arithmetic_row8 :
    (BiPoly.mul h1p6 h1p72).getD 8 []=h1p73.getD 8 [] := by
  decide +kernel

theorem h1n73_arithmetic_row9 :
    (BiPoly.mul h1p6 h1p72).getD 9 []=h1p73.getD 9 [] := by
  decide +kernel

theorem h1n73_arithmetic_row10 :
    (BiPoly.mul h1p6 h1p72).getD 10 []=h1p73.getD 10 [] := by
  decide +kernel

theorem h1n73_arithmetic_row11 :
    (BiPoly.mul h1p6 h1p72).getD 11 []=h1p73.getD 11 [] := by
  decide +kernel

theorem h1n73_arithmetic_row12 :
    (BiPoly.mul h1p6 h1p72).getD 12 []=h1p73.getD 12 [] := by
  decide +kernel

theorem h1n73_arithmetic_row13 :
    (BiPoly.mul h1p6 h1p72).getD 13 []=h1p73.getD 13 [] := by
  decide +kernel

theorem h1n73_arithmetic_row14 :
    (BiPoly.mul h1p6 h1p72).getD 14 []=h1p73.getD 14 [] := by
  decide +kernel

theorem h1n73_arithmetic_row15 :
    (BiPoly.mul h1p6 h1p72).getD 15 []=h1p73.getD 15 [] := by
  decide +kernel

theorem h1n73_arithmetic_row16 :
    (BiPoly.mul h1p6 h1p72).getD 16 []=h1p73.getD 16 [] := by
  decide +kernel

theorem h1n73_arithmetic_row17 :
    (BiPoly.mul h1p6 h1p72).getD 17 []=h1p73.getD 17 [] := by
  decide +kernel

theorem h1n73_arithmetic_row18 :
    (BiPoly.mul h1p6 h1p72).getD 18 []=h1p73.getD 18 [] := by
  decide +kernel

theorem h1n73_arithmetic_row19 :
    (BiPoly.mul h1p6 h1p72).getD 19 []=h1p73.getD 19 [] := by
  decide +kernel

theorem h1n73_arithmetic_row20 :
    (BiPoly.mul h1p6 h1p72).getD 20 []=h1p73.getD 20 [] := by
  decide +kernel

theorem h1n73_arithmetic_row21 :
    (BiPoly.mul h1p6 h1p72).getD 21 []=h1p73.getD 21 [] := by
  decide +kernel

theorem h1n73_arithmetic : BiPoly.mul h1p6 h1p72=h1p73 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p6 h1p72).getD j.val []=h1p73.getD j.val [] :=
      (fun j => Fin.cases h1n73_arithmetic_row0 (fun j => Fin.cases h1n73_arithmetic_row1 (fun j => Fin.cases h1n73_arithmetic_row2 (fun j => Fin.cases h1n73_arithmetic_row3 (fun j => Fin.cases h1n73_arithmetic_row4 (fun j => Fin.cases h1n73_arithmetic_row5 (fun j => Fin.cases h1n73_arithmetic_row6 (fun j => Fin.cases h1n73_arithmetic_row7 (fun j => Fin.cases h1n73_arithmetic_row8 (fun j => Fin.cases h1n73_arithmetic_row9 (fun j => Fin.cases h1n73_arithmetic_row10 (fun j => Fin.cases h1n73_arithmetic_row11 (fun j => Fin.cases h1n73_arithmetic_row12 (fun j => Fin.cases h1n73_arithmetic_row13 (fun j => Fin.cases h1n73_arithmetic_row14 (fun j => Fin.cases h1n73_arithmetic_row15 (fun j => Fin.cases h1n73_arithmetic_row16 (fun j => Fin.cases h1n73_arithmetic_row17 (fun j => Fin.cases h1n73_arithmetic_row18 (fun j => Fin.cases h1n73_arithmetic_row19 (fun j => Fin.cases h1n73_arithmetic_row20 (fun j => Fin.cases h1n73_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n73 : h1e73.toBi mapPolyEnv=h1p73 := by
  change BiPoly.mul (h1e6.toBi mapPolyEnv) (h1e72.toBi mapPolyEnv)=h1p73
  rw [h1n6, h1n72]
  exact h1n73_arithmetic

#print axioms h1n73_arithmetic
end StackSorting.RationalLift
