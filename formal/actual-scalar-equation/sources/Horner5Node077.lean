import Horner5Node068
import Horner5Node076
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p77 : BiPoly.Poly := [[(Int.ofNat 25808544000), (Int.ofNat 25413056640), (Int.negSucc 357290679239), (Int.negSucc 196270396919), (Int.ofNat 314379665640), (Int.ofNat 441027682200)], [(Int.negSucc 138104386559), (Int.negSucc 81586524671), (Int.ofNat 1951148901456), (Int.ofNat 1024407630504), (Int.negSucc 1487943497663), (Int.negSucc 1772364780215), (Int.ofNat 120773172960)], [(Int.ofNat 310648841280), (Int.ofNat 102451874976), (Int.negSucc 4467727606895), (Int.negSucc 2611303470863), (Int.ofNat 3030144453216), (Int.ofNat 2804000723784), (Int.negSucc 17321626007), (Int.negSucc 612928799)], [(Int.negSucc 379987796159), (Int.negSucc 93794311583), (Int.ofNat 5639403365604), (Int.ofNat 4233813809904), (Int.negSucc 2647785283415), (Int.negSucc 1661450756183), (Int.negSucc 687614726699), (Int.ofNat 22240308240)], [(Int.ofNat 272474499840), (Int.ofNat 112972081152), (Int.negSucc 4307428209935), (Int.negSucc 4614742702679), (Int.negSucc 654943751807), (Int.negSucc 170684248775), (Int.ofNat 1077642044544), (Int.ofNat 37251417960)], [(Int.negSucc 114398760959), (Int.negSucc 111233610239), (Int.ofNat 2029350024072), (Int.ofNat 3429808116732), (Int.ofNat 3504335797992), (Int.ofNat 685824966096), (Int.negSucc 261764442191), (Int.negSucc 67928789699)], [(Int.ofNat 26047512000), (Int.ofNat 59517602400), (Int.negSucc 566711351759), (Int.negSucc 1768515173903), (Int.negSucc 3124172040071), (Int.negSucc 763411838831), (Int.negSucc 419087633327), (Int.negSucc 16378248599)], [(Int.negSucc 2488453439), (Int.negSucc 15161171039), (Int.ofNat 86290510164), (Int.ofNat 651373942536), (Int.ofNat 1327193643888), (Int.ofNat 695030473944), (Int.ofNat 316186764048), (Int.ofNat 44950616280)], [(Int.ofNat 0), (Int.ofNat 1421002368), (Int.negSucc 7811495495), (Int.negSucc 187204921775), (Int.negSucc 267435360215), (Int.negSucc 331413134615), (Int.negSucc 101632125527), (Int.negSucc 12850151039)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 776542032), (Int.ofNat 45333679140), (Int.ofNat 1919710656), (Int.ofNat 82475445672), (Int.ofNat 16349022720)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6413751071), (Int.ofNat 7021831896), (Int.negSucc 10496615039)]]

theorem h5n77_arithmetic : BiPoly.add h5p68 h5p76=h5p77 := by
  decide +kernel

theorem h5n77 : h5e77.toBi mapPolyEnv=h5p77 := by
  change BiPoly.add (h5e68.toBi mapPolyEnv) (h5e76.toBi mapPolyEnv)=h5p77
  rw [h5n68, h5n76]
  exact h5n77_arithmetic

#print axioms h5n77_arithmetic
end StackSorting.RationalLift
