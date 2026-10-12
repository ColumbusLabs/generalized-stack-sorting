import BivariateRowEquality
import Horner2Base
import Horner2Node015
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p16 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 90674176895), (Int.negSucc 375345411191), (Int.ofNat 689039838648), (Int.ofNat 2239277512536), (Int.negSucc 3028390084439)], [(Int.ofNat 0), (Int.ofNat 736552449324), (Int.ofNat 2786963231736), (Int.negSucc 6013888021511), (Int.negSucc 15884664129863), (Int.ofNat 22887210030156), (Int.negSucc 1809370636991)], [(Int.ofNat 0), (Int.negSucc 2798818120199), (Int.negSucc 8757945476471), (Int.ofNat 24764213375424), (Int.ofNat 45591778070760), (Int.negSucc 67594137607871), (Int.ofNat 4199036499624), (Int.negSucc 303378511679)], [(Int.ofNat 0), (Int.ofNat 6575130648524), (Int.ofNat 14262978581260), (Int.negSucc 59661254042191), (Int.negSucc 64527633150047), (Int.ofNat 87040882549588), (Int.ofNat 16450031552684), (Int.negSucc 1451358432079), (Int.negSucc 9373329151)], [(Int.ofNat 0), (Int.negSucc 10572472722061), (Int.negSucc 10345833551905), (Int.ofNat 88733409943156), (Int.ofNat 45848870489908), (Int.negSucc 13126614831005), (Int.negSucc 78348301561049), (Int.ofNat 6323571269488), (Int.negSucc 253125520031), (Int.ofNat 54482560)], [(Int.ofNat 0), (Int.ofNat 12130636097928), (Int.negSucc 3891557663977), (Int.negSucc 81493469755611), (Int.negSucc 26895813060275), (Int.negSucc 90042327210483), (Int.ofNat 110877084281862), (Int.ofNat 2478562390964), (Int.negSucc 386938160719), (Int.negSucc 914506367)], [(Int.ofNat 0), (Int.negSucc 10053456500285), (Int.ofNat 16157162584820), (Int.ofNat 44497624866428), (Int.ofNat 48656521733316), (Int.ofNat 93426024331078), (Int.negSucc 32189489047879), (Int.negSucc 34183115740947), (Int.ofNat 2028688814800), (Int.negSucc 40553523327)], [(Int.ofNat 0), (Int.ofNat 5981988640016), (Int.negSucc 16670018936629), (Int.negSucc 14664395716629), (Int.negSucc 71324703306699), (Int.negSucc 30682211509647), (Int.negSucc 69417732009077), (Int.ofNat 44603316335290), (Int.ofNat 581856786508), (Int.negSucc 108428715935)], [(Int.ofNat 0), (Int.negSucc 2501691807025), (Int.ofNat 9470830891696), (Int.ofNat 6910107882090), (Int.ofNat 52777119225062), (Int.ofNat 10460105111788), (Int.ofNat 70092881529070), (Int.negSucc 6528376921905), (Int.negSucc 6546867961341), (Int.ofNat 128690621112)], [(Int.ofNat 0), (Int.ofNat 706553980396), (Int.negSucc 3168077650373), (Int.negSucc 7341605510733), (Int.negSucc 19300267442795), (Int.negSucc 22644731737839), (Int.negSucc 18958168306335), (Int.negSucc 25030690338389), (Int.ofNat 5293494153480), (Int.ofNat 318313777104)], [(Int.ofNat 0), (Int.negSucc 125448809201), (Int.ofNat 556631344180), (Int.ofNat 5326950660320), (Int.ofNat 3004467625960), (Int.ofNat 18855390599148), (Int.negSucc 687385618379), (Int.ofNat 17467041957624), (Int.ofNat 1412185932192), (Int.negSucc 313547061023)], [(Int.ofNat 0), (Int.ofNat 12146343428), (Int.negSucc 16023147013), (Int.negSucc 2216336162177), (Int.negSucc 527127812123), (Int.negSucc 6202479568163), (Int.negSucc 1531974809783), (Int.negSucc 3084768422495), (Int.negSucc 3066820153055), (Int.negSucc 139134047327)], [(Int.ofNat 0), (Int.negSucc 446023943), (Int.negSucc 11206797221), (Int.ofNat 537112940574), (Int.ofNat 547045746474), (Int.ofNat 525060409176), (Int.ofNat 1760434635240), (Int.negSucc 354751141895), (Int.ofNat 1034952929352), (Int.ofNat 207216120672)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1442001096), (Int.negSucc 71652370805), (Int.negSucc 251447431823), (Int.ofNat 165752317512), (Int.negSucc 482217159599), (Int.ofNat 108164672568), (Int.negSucc 81019191167), (Int.negSucc 51400604159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4142073024), (Int.ofNat 50498804592), (Int.negSucc 42474162887), (Int.ofNat 49586550840), (Int.negSucc 8893833695)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3973854815), (Int.ofNat 2490588648)]]

theorem h2n16_arithmetic_row0 :
    (BiPoly.mul h2p14 h2p15).getD 0 []=h2p16.getD 0 [] := by
  decide +kernel

theorem h2n16_arithmetic_row1 :
    (BiPoly.mul h2p14 h2p15).getD 1 []=h2p16.getD 1 [] := by
  decide +kernel

theorem h2n16_arithmetic_row2 :
    (BiPoly.mul h2p14 h2p15).getD 2 []=h2p16.getD 2 [] := by
  decide +kernel

theorem h2n16_arithmetic_row3 :
    (BiPoly.mul h2p14 h2p15).getD 3 []=h2p16.getD 3 [] := by
  decide +kernel

theorem h2n16_arithmetic_row4 :
    (BiPoly.mul h2p14 h2p15).getD 4 []=h2p16.getD 4 [] := by
  decide +kernel

theorem h2n16_arithmetic_row5 :
    (BiPoly.mul h2p14 h2p15).getD 5 []=h2p16.getD 5 [] := by
  decide +kernel

theorem h2n16_arithmetic_row6 :
    (BiPoly.mul h2p14 h2p15).getD 6 []=h2p16.getD 6 [] := by
  decide +kernel

theorem h2n16_arithmetic_row7 :
    (BiPoly.mul h2p14 h2p15).getD 7 []=h2p16.getD 7 [] := by
  decide +kernel

theorem h2n16_arithmetic_row8 :
    (BiPoly.mul h2p14 h2p15).getD 8 []=h2p16.getD 8 [] := by
  decide +kernel

theorem h2n16_arithmetic_row9 :
    (BiPoly.mul h2p14 h2p15).getD 9 []=h2p16.getD 9 [] := by
  decide +kernel

theorem h2n16_arithmetic_row10 :
    (BiPoly.mul h2p14 h2p15).getD 10 []=h2p16.getD 10 [] := by
  decide +kernel

theorem h2n16_arithmetic_row11 :
    (BiPoly.mul h2p14 h2p15).getD 11 []=h2p16.getD 11 [] := by
  decide +kernel

theorem h2n16_arithmetic_row12 :
    (BiPoly.mul h2p14 h2p15).getD 12 []=h2p16.getD 12 [] := by
  decide +kernel

theorem h2n16_arithmetic_row13 :
    (BiPoly.mul h2p14 h2p15).getD 13 []=h2p16.getD 13 [] := by
  decide +kernel

theorem h2n16_arithmetic_row14 :
    (BiPoly.mul h2p14 h2p15).getD 14 []=h2p16.getD 14 [] := by
  decide +kernel

theorem h2n16_arithmetic_row15 :
    (BiPoly.mul h2p14 h2p15).getD 15 []=h2p16.getD 15 [] := by
  decide +kernel

theorem h2n16_arithmetic : BiPoly.mul h2p14 h2p15=h2p16 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h2p14 h2p15).getD j.val []=h2p16.getD j.val [] :=
      (fun j => Fin.cases h2n16_arithmetic_row0 (fun j => Fin.cases h2n16_arithmetic_row1 (fun j => Fin.cases h2n16_arithmetic_row2 (fun j => Fin.cases h2n16_arithmetic_row3 (fun j => Fin.cases h2n16_arithmetic_row4 (fun j => Fin.cases h2n16_arithmetic_row5 (fun j => Fin.cases h2n16_arithmetic_row6 (fun j => Fin.cases h2n16_arithmetic_row7 (fun j => Fin.cases h2n16_arithmetic_row8 (fun j => Fin.cases h2n16_arithmetic_row9 (fun j => Fin.cases h2n16_arithmetic_row10 (fun j => Fin.cases h2n16_arithmetic_row11 (fun j => Fin.cases h2n16_arithmetic_row12 (fun j => Fin.cases h2n16_arithmetic_row13 (fun j => Fin.cases h2n16_arithmetic_row14 (fun j => Fin.cases h2n16_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n16 : h2e16.toBi mapPolyEnv=h2p16 := by
  change BiPoly.mul (h2e14.toBi mapPolyEnv) (h2e15.toBi mapPolyEnv)=h2p16
  rw [h2n14, h2n15]
  exact h2n16_arithmetic

#print axioms h2n16_arithmetic
end StackSorting.RationalLift
