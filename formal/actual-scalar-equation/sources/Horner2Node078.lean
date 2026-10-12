import BivariateRowEquality
import Horner2Base
import Horner2Node016
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p78 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 453370884479), (Int.negSucc 1876727055959), (Int.ofNat 3445199193240), (Int.ofNat 11196387562680), (Int.negSucc 15141950422199)], [(Int.ofNat 0), (Int.ofNat 3682762246620), (Int.ofNat 13934816158680), (Int.negSucc 30069440107559), (Int.negSucc 79423320649319), (Int.ofNat 114436050150780), (Int.negSucc 9046853184959)], [(Int.ofNat 0), (Int.negSucc 13994090600999), (Int.negSucc 43789727382359), (Int.ofNat 123821066877120), (Int.ofNat 227958890353800), (Int.negSucc 337970688039359), (Int.ofNat 20995182498120), (Int.negSucc 1516892558399)], [(Int.ofNat 0), (Int.ofNat 32875653242620), (Int.ofNat 71314892906300), (Int.negSucc 298306270210959), (Int.negSucc 322638165750239), (Int.ofNat 435204412747940), (Int.ofNat 82250157763420), (Int.negSucc 7256792160399), (Int.negSucc 46866645759)], [(Int.ofNat 0), (Int.negSucc 52862363610309), (Int.negSucc 51729167759529), (Int.ofNat 443667049715780), (Int.ofNat 229244352449540), (Int.negSucc 65633074155029), (Int.negSucc 391741507805249), (Int.ofNat 31617856347440), (Int.negSucc 1265627600159), (Int.ofNat 272412800)], [(Int.ofNat 0), (Int.ofNat 60653180489640), (Int.negSucc 19457788319889), (Int.negSucc 407467348778059), (Int.negSucc 134479065301379), (Int.negSucc 450211636052419), (Int.ofNat 554385421409310), (Int.ofNat 12392811954820), (Int.negSucc 1934690803599), (Int.negSucc 4572531839)], [(Int.ofNat 0), (Int.negSucc 50267282501429), (Int.ofNat 80785812924100), (Int.ofNat 222488124332140), (Int.ofNat 243282608666580), (Int.ofNat 467130121655390), (Int.negSucc 160947445239399), (Int.negSucc 170915578704739), (Int.ofNat 10143444074000), (Int.negSucc 202767616639)], [(Int.ofNat 0), (Int.ofNat 29909943200080), (Int.negSucc 83350094683149), (Int.negSucc 73321978583149), (Int.negSucc 356623516533499), (Int.negSucc 153411057548239), (Int.negSucc 347088660045389), (Int.ofNat 223016581676450), (Int.ofNat 2909283932540), (Int.negSucc 542143579679)], [(Int.ofNat 0), (Int.negSucc 12508459035129), (Int.ofNat 47354154458480), (Int.ofNat 34550539410450), (Int.ofNat 263885596125310), (Int.ofNat 52300525558940), (Int.ofNat 350464407645350), (Int.negSucc 32641884609529), (Int.negSucc 32734339806709), (Int.ofNat 643453105560)], [(Int.ofNat 0), (Int.ofNat 3532769901980), (Int.negSucc 15840388251869), (Int.negSucc 36708027553669), (Int.negSucc 96501337213979), (Int.negSucc 113223658689199), (Int.negSucc 94790841531679), (Int.negSucc 125153451691949), (Int.ofNat 26467470767400), (Int.ofNat 1591568885520)], [(Int.ofNat 0), (Int.negSucc 627244046009), (Int.ofNat 2783156720900), (Int.ofNat 26634753301600), (Int.ofNat 15022338129800), (Int.ofNat 94276952995740), (Int.negSucc 3436928091899), (Int.ofNat 87335209788120), (Int.ofNat 7060929660960), (Int.negSucc 1567735305119)], [(Int.ofNat 0), (Int.ofNat 60731717140), (Int.negSucc 80115735069), (Int.negSucc 11081680810889), (Int.negSucc 2635639060619), (Int.negSucc 31012397840819), (Int.negSucc 7659874048919), (Int.negSucc 15423842112479), (Int.negSucc 15334100765279), (Int.negSucc 695670236639)], [(Int.ofNat 0), (Int.negSucc 2230119719), (Int.negSucc 56033986109), (Int.ofNat 2685564702870), (Int.ofNat 2735228732370), (Int.ofNat 2625302045880), (Int.ofNat 8802173176200), (Int.negSucc 1773755709479), (Int.ofNat 5174764646760), (Int.ofNat 1036080603360)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7210005480), (Int.negSucc 358261854029), (Int.negSucc 1257237159119), (Int.ofNat 828761587560), (Int.negSucc 2411085797999), (Int.ofNat 540823362840), (Int.negSucc 405095955839), (Int.negSucc 257003020799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 20710365120), (Int.ofNat 252494022960), (Int.negSucc 212370814439), (Int.ofNat 247932754200), (Int.negSucc 44469168479)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 19869274079), (Int.ofNat 12452943240)]]

theorem h2n78_arithmetic_row0 :
    (BiPoly.mul h2p77 h2p16).getD 0 []=h2p78.getD 0 [] := by
  decide +kernel

theorem h2n78_arithmetic_row1 :
    (BiPoly.mul h2p77 h2p16).getD 1 []=h2p78.getD 1 [] := by
  decide +kernel

theorem h2n78_arithmetic_row2 :
    (BiPoly.mul h2p77 h2p16).getD 2 []=h2p78.getD 2 [] := by
  decide +kernel

theorem h2n78_arithmetic_row3 :
    (BiPoly.mul h2p77 h2p16).getD 3 []=h2p78.getD 3 [] := by
  decide +kernel

theorem h2n78_arithmetic_row4 :
    (BiPoly.mul h2p77 h2p16).getD 4 []=h2p78.getD 4 [] := by
  decide +kernel

theorem h2n78_arithmetic_row5 :
    (BiPoly.mul h2p77 h2p16).getD 5 []=h2p78.getD 5 [] := by
  decide +kernel

theorem h2n78_arithmetic_row6 :
    (BiPoly.mul h2p77 h2p16).getD 6 []=h2p78.getD 6 [] := by
  decide +kernel

theorem h2n78_arithmetic_row7 :
    (BiPoly.mul h2p77 h2p16).getD 7 []=h2p78.getD 7 [] := by
  decide +kernel

theorem h2n78_arithmetic_row8 :
    (BiPoly.mul h2p77 h2p16).getD 8 []=h2p78.getD 8 [] := by
  decide +kernel

theorem h2n78_arithmetic_row9 :
    (BiPoly.mul h2p77 h2p16).getD 9 []=h2p78.getD 9 [] := by
  decide +kernel

theorem h2n78_arithmetic_row10 :
    (BiPoly.mul h2p77 h2p16).getD 10 []=h2p78.getD 10 [] := by
  decide +kernel

theorem h2n78_arithmetic_row11 :
    (BiPoly.mul h2p77 h2p16).getD 11 []=h2p78.getD 11 [] := by
  decide +kernel

theorem h2n78_arithmetic_row12 :
    (BiPoly.mul h2p77 h2p16).getD 12 []=h2p78.getD 12 [] := by
  decide +kernel

theorem h2n78_arithmetic_row13 :
    (BiPoly.mul h2p77 h2p16).getD 13 []=h2p78.getD 13 [] := by
  decide +kernel

theorem h2n78_arithmetic_row14 :
    (BiPoly.mul h2p77 h2p16).getD 14 []=h2p78.getD 14 [] := by
  decide +kernel

theorem h2n78_arithmetic_row15 :
    (BiPoly.mul h2p77 h2p16).getD 15 []=h2p78.getD 15 [] := by
  decide +kernel

theorem h2n78_arithmetic : BiPoly.mul h2p77 h2p16=h2p78 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h2p77 h2p16).getD j.val []=h2p78.getD j.val [] :=
      (fun j => Fin.cases h2n78_arithmetic_row0 (fun j => Fin.cases h2n78_arithmetic_row1 (fun j => Fin.cases h2n78_arithmetic_row2 (fun j => Fin.cases h2n78_arithmetic_row3 (fun j => Fin.cases h2n78_arithmetic_row4 (fun j => Fin.cases h2n78_arithmetic_row5 (fun j => Fin.cases h2n78_arithmetic_row6 (fun j => Fin.cases h2n78_arithmetic_row7 (fun j => Fin.cases h2n78_arithmetic_row8 (fun j => Fin.cases h2n78_arithmetic_row9 (fun j => Fin.cases h2n78_arithmetic_row10 (fun j => Fin.cases h2n78_arithmetic_row11 (fun j => Fin.cases h2n78_arithmetic_row12 (fun j => Fin.cases h2n78_arithmetic_row13 (fun j => Fin.cases h2n78_arithmetic_row14 (fun j => Fin.cases h2n78_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h2n78 : h2e78.toBi mapPolyEnv=h2p78 := by
  change BiPoly.mul (h2e77.toBi mapPolyEnv) (h2e16.toBi mapPolyEnv)=h2p78
  rw [h2n77, h2n16]
  exact h2n78_arithmetic

#print axioms h2n78_arithmetic
end StackSorting.RationalLift
