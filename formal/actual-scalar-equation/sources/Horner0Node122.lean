import BivariateRowEquality
import Horner0Base
import Horner0Node009
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p122 : BiPoly.Poly := [[(Int.negSucc 3047094380317967999), (Int.negSucc 16946940449188918079), (Int.ofNat 3282986965383708480), (Int.ofNat 75301491839867311680), (Int.negSucc 56607621254219851199)], [(Int.ofNat 28138683035710840320), (Int.ofNat 158027994133253668224), (Int.negSucc 16520175144833864255), (Int.negSucc 662744739484728253439), (Int.ofNat 520204218857288392896), (Int.negSucc 41006057296895827199)], [(Int.negSucc 122490739466336800799), (Int.negSucc 669586970859081253199), (Int.ofNat 33122384550500275296), (Int.ofNat 2533393263114790386624), (Int.negSucc 1903096173826640442239), (Int.ofNat 192830741473309004880), (Int.negSucc 9614021433147873791)], [(Int.ofNat 333034869074575502880), (Int.ofNat 1704459323768174920080), (Int.ofNat 13655964455549244576), (Int.negSucc 5330700244145544585983), (Int.ofNat 3236337257663958813216), (Int.negSucc 65366806516734733775), (Int.ofNat 2732570438591141280), (Int.negSucc 706251951755006975)], [(Int.negSucc 629608252612856856479), (Int.negSucc 2916546256185009373871), (Int.negSucc 327428706145931749727), (Int.ofNat 6347849560031193908832), (Int.negSucc 1271346149719744562303), (Int.negSucc 1309033192577827738319), (Int.ofNat 124545945891843631584), (Int.negSucc 3847415368236743231), (Int.ofNat 3764143844398080)], [(Int.ofNat 870246329286923647920), (Int.ofNat 3578417540387001758664), (Int.ofNat 1140572689941163147560), (Int.negSucc 3367083848664683523599), (Int.negSucc 4752114634388768533919), (Int.ofNat 3263129180496182003112), (Int.negSucc 192523960848715430327), (Int.ofNat 5369944699779787584), (Int.negSucc 122993045314349183)], [(Int.negSucc 900144185524400585999), (Int.negSucc 3308832380632960183175), (Int.negSucc 2289510490983744554687), (Int.negSucc 1471875766787092297055), (Int.ofNat 8923152698195573927856), (Int.negSucc 2444932257783034384151), (Int.negSucc 351442565769632673311), (Int.ofNat 30414580744115013936), (Int.negSucc 733695523625245055)], [(Int.ofNat 702258635081865325680), (Int.ofNat 2419156733715719861784), (Int.ofNat 3098441705687988462360), (Int.ofNat 4014026735368153229376), (Int.negSucc 5938814315336049628559), (Int.negSucc 1852000421492145288359), (Int.ofNat 1146246839189523100776), (Int.negSucc 43491944966426233919), (Int.negSucc 24289530237913727)], [(Int.negSucc 412095219971251310639), (Int.negSucc 1461712904878241724359), (Int.negSucc 3015944108797127274575), (Int.negSucc 3410968213329429685775), (Int.negSucc 480476494095592220207), (Int.ofNat 4658205189732005590104), (Int.negSucc 782546045551444464143), (Int.negSucc 70032337010421731279), (Int.ofNat 3952980537816738912)], [(Int.ofNat 179683754821986115440), (Int.ofNat 746337764861559523992), (Int.ofNat 2183636153839802730144), (Int.ofNat 1912043456800595192832), (Int.ofNat 3543027652785521904072), (Int.negSucc 2822743745193380675423), (Int.negSucc 580110203131326079367), (Int.ofNat 163653982169279005968), (Int.ofNat 149198746025904744)], [(Int.negSucc 56868726759196769039), (Int.negSucc 316745185663120917431), (Int.negSucc 1191070510217099251319), (Int.negSucc 1039982849356890181799), (Int.negSucc 2568818652973839889247), (Int.negSucc 344098818484436255999), (Int.ofNat 1098111259177087737960), (Int.negSucc 44362872171269902247), (Int.negSucc 8737142905054281167)], [(Int.ofNat 12550722566158398960), (Int.ofNat 106492382988570032856), (Int.ofNat 486609373036164767736), (Int.ofNat 644132658162733267728), (Int.ofNat 908296156145717153808), (Int.ofNat 1341269998252090166112), (Int.negSucc 423956117887236660239), (Int.negSucc 110843347143035616719), (Int.ofNat 3805278459586304976)], [(Int.negSucc 1800367080968554799), (Int.negSucc 26685567940874702663), (Int.negSucc 145596323411227028447), (Int.negSucc 346286372060897064047), (Int.negSucc 204946722087351674591), (Int.negSucc 735766386925659695471), (Int.negSucc 186422343431081517791), (Int.ofNat 91292726606691080016), (Int.ofNat 6066884234541299760)], [(Int.ofNat 146376022151123040), (Int.ofNat 4639895898723409056), (Int.ofNat 30704967683253323880), (Int.ofNat 130068239634060692592), (Int.ofNat 73046820766705167816), (Int.ofNat 172813228211277299232), (Int.ofNat 222298138221307778304), (Int.negSucc 1789508575649319263), (Int.negSucc 5107661750497803551)], [(Int.negSucc 4784094042108479), (Int.negSucc 501051676955380847), (Int.negSucc 4304098474731577367), (Int.negSucc 31346524344096610343), (Int.negSucc 38523666299621875919), (Int.negSucc 12841618169547024767), (Int.negSucc 77349344374284058079), (Int.negSucc 25228400676131880863), (Int.negSucc 191117498076975167)], [(Int.ofNat 0), (Int.ofNat 25622532429278976), (Int.ofNat 362426699675525472), (Int.ofNat 4488269478604926480), (Int.ofNat 12723622237809095184), (Int.ofNat 277548702226933536), (Int.ofNat 10048199398200620064), (Int.ofNat 11789985492485375616), (Int.ofNat 1439994887113537728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14239684785885119), (Int.negSucc 321291254189053295), (Int.negSucc 2216919496002518735), (Int.negSucc 1013920184648889503), (Int.ofNat 422998555851671040), (Int.negSucc 2124728162097507647), (Int.negSucc 536016567863969855)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5992259296262400), (Int.ofNat 172251668953320768), (Int.ofNat 320216501250482688), (Int.negSucc 239368599057377087), (Int.ofNat 130265911109753856), (Int.ofNat 62445874385525760)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1925666462156543), (Int.negSucc 30978304470537407), (Int.ofNat 20171875201427520)]]

theorem h0n122_arithmetic_row0 :
    (BiPoly.mul h0p85 h0p9).getD 0 []=h0p122.getD 0 [] := by
  decide +kernel

theorem h0n122_arithmetic_row1 :
    (BiPoly.mul h0p85 h0p9).getD 1 []=h0p122.getD 1 [] := by
  decide +kernel

theorem h0n122_arithmetic_row2 :
    (BiPoly.mul h0p85 h0p9).getD 2 []=h0p122.getD 2 [] := by
  decide +kernel

theorem h0n122_arithmetic_row3 :
    (BiPoly.mul h0p85 h0p9).getD 3 []=h0p122.getD 3 [] := by
  decide +kernel

theorem h0n122_arithmetic_row4 :
    (BiPoly.mul h0p85 h0p9).getD 4 []=h0p122.getD 4 [] := by
  decide +kernel

theorem h0n122_arithmetic_row5 :
    (BiPoly.mul h0p85 h0p9).getD 5 []=h0p122.getD 5 [] := by
  decide +kernel

theorem h0n122_arithmetic_row6 :
    (BiPoly.mul h0p85 h0p9).getD 6 []=h0p122.getD 6 [] := by
  decide +kernel

theorem h0n122_arithmetic_row7 :
    (BiPoly.mul h0p85 h0p9).getD 7 []=h0p122.getD 7 [] := by
  decide +kernel

theorem h0n122_arithmetic_row8 :
    (BiPoly.mul h0p85 h0p9).getD 8 []=h0p122.getD 8 [] := by
  decide +kernel

theorem h0n122_arithmetic_row9 :
    (BiPoly.mul h0p85 h0p9).getD 9 []=h0p122.getD 9 [] := by
  decide +kernel

theorem h0n122_arithmetic_row10 :
    (BiPoly.mul h0p85 h0p9).getD 10 []=h0p122.getD 10 [] := by
  decide +kernel

theorem h0n122_arithmetic_row11 :
    (BiPoly.mul h0p85 h0p9).getD 11 []=h0p122.getD 11 [] := by
  decide +kernel

theorem h0n122_arithmetic_row12 :
    (BiPoly.mul h0p85 h0p9).getD 12 []=h0p122.getD 12 [] := by
  decide +kernel

theorem h0n122_arithmetic_row13 :
    (BiPoly.mul h0p85 h0p9).getD 13 []=h0p122.getD 13 [] := by
  decide +kernel

theorem h0n122_arithmetic_row14 :
    (BiPoly.mul h0p85 h0p9).getD 14 []=h0p122.getD 14 [] := by
  decide +kernel

theorem h0n122_arithmetic_row15 :
    (BiPoly.mul h0p85 h0p9).getD 15 []=h0p122.getD 15 [] := by
  decide +kernel

theorem h0n122_arithmetic_row16 :
    (BiPoly.mul h0p85 h0p9).getD 16 []=h0p122.getD 16 [] := by
  decide +kernel

theorem h0n122_arithmetic_row17 :
    (BiPoly.mul h0p85 h0p9).getD 17 []=h0p122.getD 17 [] := by
  decide +kernel

theorem h0n122_arithmetic_row18 :
    (BiPoly.mul h0p85 h0p9).getD 18 []=h0p122.getD 18 [] := by
  decide +kernel

theorem h0n122_arithmetic : BiPoly.mul h0p85 h0p9=h0p122 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p85 h0p9).getD j.val []=h0p122.getD j.val [] :=
      (fun j => Fin.cases h0n122_arithmetic_row0 (fun j => Fin.cases h0n122_arithmetic_row1 (fun j => Fin.cases h0n122_arithmetic_row2 (fun j => Fin.cases h0n122_arithmetic_row3 (fun j => Fin.cases h0n122_arithmetic_row4 (fun j => Fin.cases h0n122_arithmetic_row5 (fun j => Fin.cases h0n122_arithmetic_row6 (fun j => Fin.cases h0n122_arithmetic_row7 (fun j => Fin.cases h0n122_arithmetic_row8 (fun j => Fin.cases h0n122_arithmetic_row9 (fun j => Fin.cases h0n122_arithmetic_row10 (fun j => Fin.cases h0n122_arithmetic_row11 (fun j => Fin.cases h0n122_arithmetic_row12 (fun j => Fin.cases h0n122_arithmetic_row13 (fun j => Fin.cases h0n122_arithmetic_row14 (fun j => Fin.cases h0n122_arithmetic_row15 (fun j => Fin.cases h0n122_arithmetic_row16 (fun j => Fin.cases h0n122_arithmetic_row17 (fun j => Fin.cases h0n122_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n122 : h0e122.toBi mapPolyEnv=h0p122 := by
  change BiPoly.mul (h0e85.toBi mapPolyEnv) (h0e9.toBi mapPolyEnv)=h0p122
  rw [h0n85, h0n9]
  exact h0n122_arithmetic

#print axioms h0n122_arithmetic
end StackSorting.RationalLift
