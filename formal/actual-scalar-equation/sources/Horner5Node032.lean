import Horner5Node021
import Horner5Node031
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p32 : BiPoly.Poly := [[(Int.negSucc 25808543999), (Int.negSucc 25413056639), (Int.ofNat 306286454736), (Int.ofNat 13828479408), (Int.negSucc 181200749327), (Int.negSucc 176411072879)], [(Int.ofNat 138104386560), (Int.ofNat 81586524672), (Int.negSucc 1651066359839), (Int.ofNat 80097091056), (Int.ofNat 786450542976), (Int.ofNat 683963627184), (Int.negSucc 48309269183)], [(Int.negSucc 310648841279), (Int.negSucc 102451874975), (Int.ofNat 3644083785888), (Int.negSucc 14895204767), (Int.negSucc 1425372191423), (Int.negSucc 1117591196975), (Int.ofNat 4275634032), (Int.ofNat 245171520)], [(Int.ofNat 379987796160), (Int.ofNat 93794311584), (Int.negSucc 4263546127751), (Int.negSucc 1200105340415), (Int.ofNat 1345114134864), (Int.ofNat 802378006704), (Int.ofNat 265467443256), (Int.negSucc 8896123295)], [(Int.negSucc 272474499839), (Int.negSucc 112972081151), (Int.ofNat 2802193401216), (Int.ofNat 2962564489104), (Int.negSucc 285298241663), (Int.negSucc 80227786511), (Int.negSucc 422735751263), (Int.negSucc 14900567183)], [(Int.ofNat 114398760960), (Int.ofNat 111233610240), (Int.negSucc 946888321967), (Int.negSucc 3114449428823), (Int.negSucc 1118420379983), (Int.negSucc 234871737215), (Int.ofNat 135641841312), (Int.ofNat 27171515880)], [(Int.negSucc 26047511999), (Int.negSucc 59517602399), (Int.ofNat 72099128064), (Int.ofNat 1666353426240), (Int.ofNat 1625161111728), (Int.ofNat 272164727520), (Int.ofNat 142209011808), (Int.ofNat 6551299440)], [(Int.ofNat 2488453440), (Int.ofNat 15161171040), (Int.ofNat 47351334648), (Int.negSucc 440022616559), (Int.negSucc 1015706211551), (Int.negSucc 278771881967), (Int.negSucc 134862467039), (Int.negSucc 17980246511)], [(Int.ofNat 0), (Int.negSucc 1421002367), (Int.negSucc 10567280303), (Int.ofNat 52998789600), (Int.ofNat 289072134000), (Int.ofNat 189086660208), (Int.ofNat 51329245680), (Int.ofNat 5140060416)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 53985312), (Int.negSucc 9096342695), (Int.negSucc 18259367615), (Int.negSucc 69343614863), (Int.negSucc 8638932095)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2439896256), (Int.negSucc 4531243247), (Int.ofNat 10496615040)]]

theorem h5n32_arithmetic : BiPoly.add h5p21 h5p31=h5p32 := by
  decide +kernel

theorem h5n32 : h5e32.toBi mapPolyEnv=h5p32 := by
  change BiPoly.add (h5e21.toBi mapPolyEnv) (h5e31.toBi mapPolyEnv)=h5p32
  rw [h5n21, h5n31]
  exact h5n32_arithmetic

#print axioms h5n32_arithmetic
end StackSorting.RationalLift
