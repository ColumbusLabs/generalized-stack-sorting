import Horner4Node170
import Horner4Node171
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p172 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 19356407999), (Int.negSucc 23769792143), (Int.ofNat 156936232512), (Int.negSucc 176411072879)], [(Int.ofNat 0), (Int.ofNat 84221881920), (Int.ofNat 63878061456), (Int.negSucc 784206283103), (Int.ofNat 805137894000), (Int.negSucc 48309269183)], [(Int.ofNat 0), (Int.negSucc 148764749039), (Int.negSucc 14060107943), (Int.ofNat 1272026971584), (Int.negSucc 1192678350119), (Int.ofNat 11768426928), (Int.ofNat 245171520)], [(Int.ofNat 0), (Int.ofNat 136226098080), (Int.negSucc 142206089543), (Int.negSucc 614467599767), (Int.ofNat 104350068216), (Int.ofNat 302545876392), (Int.negSucc 8896123295)], [(Int.ofNat 0), (Int.negSucc 68129776799), (Int.ofNat 231616874232), (Int.negSucc 352735187975), (Int.ofNat 1130795960688), (Int.negSucc 441001084823), (Int.negSucc 14900567183)], [(Int.ofNat 0), (Int.ofNat 17669293920), (Int.negSucc 166871134583), (Int.ofNat 422090102592), (Int.negSucc 776431538423), (Int.ofNat 3339570312), (Int.ofNat 27171515880)], [(Int.ofNat 0), (Int.negSucc 1866340079), (Int.ofNat 61491584160), (Int.negSucc 70528046831), (Int.ofNat 26226425520), (Int.ofNat 236988516024), (Int.ofNat 6551299440)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10633080527), (Int.negSucc 47551731335), (Int.ofNat 99379422504), (Int.negSucc 85866616943), (Int.negSucc 17980246511)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 553684896), (Int.ofNat 21053235096), (Int.negSucc 24388612703), (Int.negSucc 2930548031), (Int.ofNat 5140060416)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2649236543), (Int.ofNat 1817397648), (Int.ofNat 2624153760)]]

theorem h4n172_arithmetic : BiPoly.add h4p170 h4p171=h4p172 := by
  decide +kernel

theorem h4n172 : h4e172.toBi mapPolyEnv=h4p172 := by
  change BiPoly.add (h4e170.toBi mapPolyEnv) (h4e171.toBi mapPolyEnv)=h4p172
  rw [h4n170, h4n171]
  exact h4n172_arithmetic

#print axioms h4n172_arithmetic
end StackSorting.RationalLift
