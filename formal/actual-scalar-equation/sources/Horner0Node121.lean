import BivariateRowEquality
import Horner0Base
import Horner0Node014
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p121 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 3568492341912803903), (Int.negSucc 18391982448471503615), (Int.ofNat 13329578539401681024), (Int.ofNat 95420018273305985280), (Int.negSucc 96052057514421825599)], [(Int.ofNat 0), (Int.ofNat 34853350905511530624), (Int.ofNat 191124176011423216128), (Int.negSucc 82194446392551173375), (Int.negSucc 934060076134501294079), (Int.ofNat 868885222357402694784), (Int.negSucc 52606728437025692159)], [(Int.ofNat 0), (Int.negSucc 165501432045647425727), (Int.negSucc 887695281980957356415), (Int.ofNat 260521692540473481984), (Int.ofNat 3857127037850199854592), (Int.negSucc 3283220955763896886079), (Int.ofNat 239855550294661974144), (Int.negSucc 6936060331254726143)], [(Int.ofNat 0), (Int.ofNat 504749169473018445888), (Int.ofNat 2464015176641495424192), (Int.negSucc 719875895737289410175), (Int.negSucc 8499169758808589167487), (Int.ofNat 6092580801130515065664), (Int.negSucc 70604931706917634367), (Int.negSucc 8338258355825901311), (Int.ofNat 73111462690928640)], [(Int.ofNat 0), (Int.negSucc 1098905970827018421567), (Int.negSucc 4562539032570000943551), (Int.ofNat 1736244007885846190016), (Int.ofNat 9959904754175330320256), (Int.negSucc 3859808432269330861567), (Int.negSucc 1728544564673568415423), (Int.ofNat 114489944741557868096), (Int.negSucc 2665663228691814911), (Int.negSucc 185521834009599)], [(Int.ofNat 0), (Int.ofNat 1797085306833437317952), (Int.ofNat 5894286332504525434496), (Int.negSucc 2681913537378949935615), (Int.negSucc 3950247854976146165119), (Int.negSucc 5820035039082844608703), (Int.ofNat 4461395289272228239872), (Int.negSucc 108091018319476267263), (Int.negSucc 4419038668563805695), (Int.ofNat 13463432534492160)], [(Int.ofNat 0), (Int.negSucc 2265288547227416889807), (Int.negSucc 5355329000249711691935), (Int.ofNat 1638693105203603310032), (Int.negSucc 4349246772434517525823), (Int.ofNat 13589350583264289419152), (Int.negSucc 3788959266049931856799), (Int.negSucc 442288003844968800463), (Int.ofNat 25488397550243290624), (Int.negSucc 221711791008972543)], [(Int.ofNat 0), (Int.ofNat 2225950467070856347360), (Int.ofNat 3367935231133522272864), (Int.ofNat 1797440220860765799296), (Int.ofNat 6012616423488708489280), (Int.negSucc 9272902975781078019039), (Int.negSucc 1684003799437814105823), (Int.ofNat 1055251006140733414592), (Int.ofNat 3552853803032991488), (Int.negSucc 859376325297526271)], [(Int.ofNat 0), (Int.negSucc 1706964054255661518255), (Int.negSucc 1466844783221281916959), (Int.negSucc 4699465556159956577567), (Int.negSucc 1944240988575946585439), (Int.negSucc 1226666461383074693615), (Int.ofNat 5654848597767135932320), (Int.negSucc 557540446716898292031), (Int.negSucc 92049736075389703519), (Int.ofNat 796922914589957696)], [(Int.ofNat 0), (Int.ofNat 1014457860302409713600), (Int.ofNat 578708819958738729280), (Int.ofNat 4520719903596115992576), (Int.negSucc 530716556067609724927), (Int.ofNat 5553603810955840308224), (Int.negSucc 3562361967609698194559), (Int.negSucc 626814294113238972095), (Int.ofNat 78221176892061896768), (Int.ofNat 2886175369108891200)], [(Int.ofNat 0), (Int.negSucc 460630775297766666671), (Int.negSucc 404564075092544756351), (Int.negSucc 2373806834745544622655), (Int.negSucc 223890841540478833247), (Int.negSucc 3113327866930005026991), (Int.negSucc 387600937279570469535), (Int.ofNat 892213865883349943696), (Int.ofNat 55917449990861596000), (Int.negSucc 2671248434868104975)], [(Int.ofNat 0), (Int.ofNat 156274489454178416544), (Int.ofNat 338913699092320422496), (Int.ofNat 655237236919339617376), (Int.ofNat 1057979816137717814624), (Int.ofNat 483293502480158929664), (Int.ofNat 1535852515439729120128), (Int.negSucc 233341082385580619487), (Int.negSucc 101418907924999289375), (Int.negSucc 2470358004295726655)], [(Int.ofNat 0), (Int.negSucc 38315073929855311311), (Int.negSucc 200533809198963649119), (Int.negSucc 55930658415970735151), (Int.negSucc 773661154154207646175), (Int.ofNat 91195954209838892064), (Int.negSucc 748323523305201290431), (Int.negSucc 202989972584058749679), (Int.ofNat 27144980819338988160), (Int.ofNat 3356053129686897792)], [(Int.ofNat 0), (Int.ofNat 6451603136419424448), (Int.ofNat 77602680706153085056), (Int.negSucc 3552546239808967807), (Int.ofNat 258232632205435070400), (Int.ofNat 31713186398751800704), (Int.ofNat 127938291478010207424), (Int.ofNat 163290561799327048320), (Int.ofNat 23592334189138489152), (Int.negSucc 134995396989974399)], [(Int.ofNat 0), (Int.negSucc 686939418857914815), (Int.negSucc 19481713896733579167), (Int.negSucc 11627956979889844719), (Int.negSucc 33283239236223993887), (Int.negSucc 56208858678471526703), (Int.ofNat 8494645281403838208), (Int.negSucc 44187275769379468415), (Int.negSucc 17626067577353295359), (Int.negSucc 1205671032352166975)], [(Int.ofNat 0), (Int.ofNat 39984362639269632), (Int.ofNat 3049336273746515520), (Int.ofNat 8226896672581845408), (Int.negSucc 5002475346369824159), (Int.ofNat 20994889301614372032), (Int.negSucc 6083241079014237311), (Int.ofNat 4045365864913328640), (Int.ofNat 4213054946526142464), (Int.ofNat 570491070162057216)], [(Int.ofNat 0), (Int.negSucc 946194333513983), (Int.negSucc 264828245113678463), (Int.negSucc 2369720515022596367), (Int.ofNat 2626198884038694528), (Int.negSucc 3658294652199185663), (Int.ofNat 774934790079412224), (Int.ofNat 226497817416749184), (Int.negSucc 330453415012073471), (Int.negSucc 81543892222623743)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9054581853975552), (Int.ofNat 346068284975405568), (Int.negSucc 414762057599599295), (Int.ofNat 292100951466587520), (Int.negSucc 22689272409956351), (Int.negSucc 52682206263883775)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 21661895882916863), (Int.ofNat 27152915482934784), (Int.negSucc 8508959963712575)]]

theorem h0n121_arithmetic_row0 :
    (BiPoly.mul h0p120 h0p14).getD 0 []=h0p121.getD 0 [] := by
  decide +kernel

theorem h0n121_arithmetic_row1 :
    (BiPoly.mul h0p120 h0p14).getD 1 []=h0p121.getD 1 [] := by
  decide +kernel

theorem h0n121_arithmetic_row2 :
    (BiPoly.mul h0p120 h0p14).getD 2 []=h0p121.getD 2 [] := by
  decide +kernel

theorem h0n121_arithmetic_row3 :
    (BiPoly.mul h0p120 h0p14).getD 3 []=h0p121.getD 3 [] := by
  decide +kernel

theorem h0n121_arithmetic_row4 :
    (BiPoly.mul h0p120 h0p14).getD 4 []=h0p121.getD 4 [] := by
  decide +kernel

theorem h0n121_arithmetic_row5 :
    (BiPoly.mul h0p120 h0p14).getD 5 []=h0p121.getD 5 [] := by
  decide +kernel

theorem h0n121_arithmetic_row6 :
    (BiPoly.mul h0p120 h0p14).getD 6 []=h0p121.getD 6 [] := by
  decide +kernel

theorem h0n121_arithmetic_row7 :
    (BiPoly.mul h0p120 h0p14).getD 7 []=h0p121.getD 7 [] := by
  decide +kernel

theorem h0n121_arithmetic_row8 :
    (BiPoly.mul h0p120 h0p14).getD 8 []=h0p121.getD 8 [] := by
  decide +kernel

theorem h0n121_arithmetic_row9 :
    (BiPoly.mul h0p120 h0p14).getD 9 []=h0p121.getD 9 [] := by
  decide +kernel

theorem h0n121_arithmetic_row10 :
    (BiPoly.mul h0p120 h0p14).getD 10 []=h0p121.getD 10 [] := by
  decide +kernel

theorem h0n121_arithmetic_row11 :
    (BiPoly.mul h0p120 h0p14).getD 11 []=h0p121.getD 11 [] := by
  decide +kernel

theorem h0n121_arithmetic_row12 :
    (BiPoly.mul h0p120 h0p14).getD 12 []=h0p121.getD 12 [] := by
  decide +kernel

theorem h0n121_arithmetic_row13 :
    (BiPoly.mul h0p120 h0p14).getD 13 []=h0p121.getD 13 [] := by
  decide +kernel

theorem h0n121_arithmetic_row14 :
    (BiPoly.mul h0p120 h0p14).getD 14 []=h0p121.getD 14 [] := by
  decide +kernel

theorem h0n121_arithmetic_row15 :
    (BiPoly.mul h0p120 h0p14).getD 15 []=h0p121.getD 15 [] := by
  decide +kernel

theorem h0n121_arithmetic_row16 :
    (BiPoly.mul h0p120 h0p14).getD 16 []=h0p121.getD 16 [] := by
  decide +kernel

theorem h0n121_arithmetic_row17 :
    (BiPoly.mul h0p120 h0p14).getD 17 []=h0p121.getD 17 [] := by
  decide +kernel

theorem h0n121_arithmetic_row18 :
    (BiPoly.mul h0p120 h0p14).getD 18 []=h0p121.getD 18 [] := by
  decide +kernel

theorem h0n121_arithmetic : BiPoly.mul h0p120 h0p14=h0p121 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p120 h0p14).getD j.val []=h0p121.getD j.val [] :=
      (fun j => Fin.cases h0n121_arithmetic_row0 (fun j => Fin.cases h0n121_arithmetic_row1 (fun j => Fin.cases h0n121_arithmetic_row2 (fun j => Fin.cases h0n121_arithmetic_row3 (fun j => Fin.cases h0n121_arithmetic_row4 (fun j => Fin.cases h0n121_arithmetic_row5 (fun j => Fin.cases h0n121_arithmetic_row6 (fun j => Fin.cases h0n121_arithmetic_row7 (fun j => Fin.cases h0n121_arithmetic_row8 (fun j => Fin.cases h0n121_arithmetic_row9 (fun j => Fin.cases h0n121_arithmetic_row10 (fun j => Fin.cases h0n121_arithmetic_row11 (fun j => Fin.cases h0n121_arithmetic_row12 (fun j => Fin.cases h0n121_arithmetic_row13 (fun j => Fin.cases h0n121_arithmetic_row14 (fun j => Fin.cases h0n121_arithmetic_row15 (fun j => Fin.cases h0n121_arithmetic_row16 (fun j => Fin.cases h0n121_arithmetic_row17 (fun j => Fin.cases h0n121_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n121 : h0e121.toBi mapPolyEnv=h0p121 := by
  change BiPoly.mul (h0e120.toBi mapPolyEnv) (h0e14.toBi mapPolyEnv)=h0p121
  rw [h0n120, h0n14]
  exact h0n121_arithmetic

#print axioms h0n121_arithmetic
end StackSorting.RationalLift
