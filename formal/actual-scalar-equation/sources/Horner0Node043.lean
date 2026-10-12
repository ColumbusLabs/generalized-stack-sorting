import BivariateRowEquality
import Horner0Base
import Horner0Node042
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p43 : BiPoly.Poly := [[(Int.negSucc 867292895051999999), (Int.negSucc 4415403168638747999), (Int.ofNat 2721813165842242320), (Int.ofNat 17717601709880668080), (Int.negSucc 29945810727372528719), (Int.ofNat 14151905313554962800)], [(Int.ofNat 7547375504496960000), (Int.ofNat 36096542124034619520), (Int.negSucc 32056579487290995935), (Int.negSucc 147506191749002597615), (Int.ofNat 270800444072805845760), (Int.negSucc 140071597208712784943), (Int.ofNat 10251514324223956800)], [(Int.negSucc 29750990164393795199), (Int.negSucc 134405975424516322679), (Int.ofNat 138794049868549252212), (Int.ofNat 530409489951880851912), (Int.negSucc 1004055113012048264015), (Int.ofNat 523993082277348623232), (Int.negSucc 51529184746416892691), (Int.ofNat 2403505358286968448)], [(Int.ofNat 70213403065693564800), (Int.ofNat 301500408654807175800), (Int.negSucc 301835575104943809347), (Int.negSucc 1089120032843761633895), (Int.ofNat 1896243112793909953440), (Int.negSucc 821844455390346633479), (Int.ofNat 18812813508951604020), (Int.negSucc 1162587132478006631), (Int.ofNat 176562987938751744)], [(Int.negSucc 110451117509596868399), (Int.negSucc 453469165982716318919), (Int.ofNat 331994730952861347456), (Int.ofNat 1393253382148510216248), (Int.negSucc 1645115223255193164239), (Int.negSucc 6876826470699392303), (Int.ofNat 367982498031422335848), (Int.negSucc 32688702348260447735), (Int.ofNat 936396319396225680), (Int.negSucc 941035961099519)], [(Int.ofNat 121970710058530651200), (Int.ofNat 480438724453005699540), (Int.negSucc 70381071160891907489), (Int.negSucc 1072966555593887740937), (Int.negSucc 322524966580787125403), (Int.ofNat 1932310206770769292536), (Int.negSucc 884246117524489704185), (Int.ofNat 53139608024453757342), (Int.negSucc 1526309799268952015), (Int.ofNat 30748261328587296)], [(Int.negSucc 96936809597450697599), (Int.negSucc 365190966550623715259), (Int.negSucc 317861255700123246701), (Int.ofNat 299277556791563672616), (Int.ofNat 2313017950583053439808), (Int.negSucc 2693652251779898122475), (Int.ofNat 505398552208057522062), (Int.ofNat 99493481294746658352), (Int.negSucc 7775790742558126715), (Int.ofNat 183423880906311264)], [(Int.ofNat 55864853731890878400), (Int.ofNat 197608886293758243300), (Int.ofNat 498936554743055220138), (Int.ofNat 369527584810879351242), (Int.negSucc 2347914533388634264271), (Int.ofNat 923685532005301859268), (Int.ofNat 817256928316140119082), (Int.negSucc 315594347726198591993), (Int.ofNat 12043246541826076416), (Int.ofNat 6072382559478432)], [(Int.negSucc 23173601035109584799), (Int.negSucc 72716390762964517139), (Int.negSucc 387247793233663470053), (Int.negSucc 565115305511668784435), (Int.ofNat 843239025702653940336), (Int.ofNat 1295329904715976543116), (Int.negSucc 1397429008638482868905), (Int.ofNat 176457666997904147724), (Int.ofNat 18913203523348044072), (Int.negSucc 988245134454184727)], [(Int.ofNat 6750228137832926400), (Int.ofNat 15633078983062902180), (Int.ofNat 177436663984972765194), (Int.ofNat 387171773166962050632), (Int.ofNat 369887471545259759616), (Int.negSucc 1618898772015422213345), (Int.ofNat 515077067417368515912), (Int.ofNat 224657331185646727698), (Int.negSucc 44698332936484041443), (Int.negSucc 37299686506476185)], [(Int.negSucc 1311367161569299199), (Int.negSucc 517050862398345659), (Int.negSucc 43744643316021805505), (Int.negSucc 149035201298211425417), (Int.negSucc 552687606809096526965), (Int.ofNat 598592208178992626424), (Int.ofNat 444831552570447404136), (Int.negSucc 313448686648132607705), (Int.ofNat 8783387765977666026), (Int.ofNat 2184285726263570292)], [(Int.ofNat 152670886241649600), (Int.negSucc 761990005083174779), (Int.ofNat 1250694221330103354), (Int.ofNat 24136796999856300402), (Int.ofNat 258739573224751349772), (Int.ofNat 130070417538451355244), (Int.negSucc 493872093062359217687), (Int.ofNat 62927481264232718772), (Int.ofNat 34605154886735850468), (Int.negSucc 951319614896576243)], [(Int.negSucc 8063021514385199), (Int.ofNat 225491641156792860), (Int.ofNat 2752773584781202902), (Int.ofNat 5166473429612048544), (Int.negSucc 47484955591766855711), (Int.negSucc 198113311161960540359), (Int.ofNat 137607256567794124380), (Int.ofNat 97187825463176023560), (Int.negSucc 24072492403230579539), (Int.negSucc 1516721058635324939)], [(Int.ofNat 0), (Int.negSucc 27385416394817879), (Int.negSucc 872652661660262759), (Int.negSucc 3657519259845600137), (Int.negSucc 6252891514218650315), (Int.ofNat 69955478873106648894), (Int.ofNat 34332382151409507912), (Int.negSucc 65328800593602171455), (Int.negSucc 3358211845261268231), (Int.ofNat 1276915437624450888)], [(Int.ofNat 0), (Int.ofNat 1196023510527120), (Int.ofNat 118695776310683964), (Int.ofNat 823588703131243158), (Int.ofNat 4960120867506297018), (Int.negSucc 7574653837520439515), (Int.negSucc 31253533201548157823), (Int.ofNat 9057028341795985080), (Int.ofNat 8486107659827737272), (Int.ofNat 47779374519243792)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6405633107319743), (Int.negSucc 87001377095091671), (Int.negSucc 984228567487088003), (Int.negSucc 1517013244402562915), (Int.ofNat 7249054673412975672), (Int.ofNat 4403492543867175000), (Int.negSucc 2685824034764953247), (Int.negSucc 359998721778384431)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3559921196471280), (Int.ofNat 79067332855046700), (Int.ofNat 500460464323007892), (Int.negSucc 432740101226600519), (Int.negSucc 1801238865453609407), (Int.negSucc 8468788753739375), (Int.ofNat 134004141965992464)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1498064824065599), (Int.negSucc 42731641570747535), (Int.negSucc 65426456233474559), (Int.ofNat 221484378725213328), (Int.ofNat 129566064541418496), (Int.negSucc 15611468596381439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 481416615539136), (Int.ofNat 7687514455941744), (Int.negSucc 6950403188810639), (Int.negSucc 15940238324356799)]]

theorem h0n43_arithmetic_row0 :
    (BiPoly.mul h0p7 h0p42).getD 0 []=h0p43.getD 0 [] := by
  decide +kernel

theorem h0n43_arithmetic_row1 :
    (BiPoly.mul h0p7 h0p42).getD 1 []=h0p43.getD 1 [] := by
  decide +kernel

theorem h0n43_arithmetic_row2 :
    (BiPoly.mul h0p7 h0p42).getD 2 []=h0p43.getD 2 [] := by
  decide +kernel

theorem h0n43_arithmetic_row3 :
    (BiPoly.mul h0p7 h0p42).getD 3 []=h0p43.getD 3 [] := by
  decide +kernel

theorem h0n43_arithmetic_row4 :
    (BiPoly.mul h0p7 h0p42).getD 4 []=h0p43.getD 4 [] := by
  decide +kernel

theorem h0n43_arithmetic_row5 :
    (BiPoly.mul h0p7 h0p42).getD 5 []=h0p43.getD 5 [] := by
  decide +kernel

theorem h0n43_arithmetic_row6 :
    (BiPoly.mul h0p7 h0p42).getD 6 []=h0p43.getD 6 [] := by
  decide +kernel

theorem h0n43_arithmetic_row7 :
    (BiPoly.mul h0p7 h0p42).getD 7 []=h0p43.getD 7 [] := by
  decide +kernel

theorem h0n43_arithmetic_row8 :
    (BiPoly.mul h0p7 h0p42).getD 8 []=h0p43.getD 8 [] := by
  decide +kernel

theorem h0n43_arithmetic_row9 :
    (BiPoly.mul h0p7 h0p42).getD 9 []=h0p43.getD 9 [] := by
  decide +kernel

theorem h0n43_arithmetic_row10 :
    (BiPoly.mul h0p7 h0p42).getD 10 []=h0p43.getD 10 [] := by
  decide +kernel

theorem h0n43_arithmetic_row11 :
    (BiPoly.mul h0p7 h0p42).getD 11 []=h0p43.getD 11 [] := by
  decide +kernel

theorem h0n43_arithmetic_row12 :
    (BiPoly.mul h0p7 h0p42).getD 12 []=h0p43.getD 12 [] := by
  decide +kernel

theorem h0n43_arithmetic_row13 :
    (BiPoly.mul h0p7 h0p42).getD 13 []=h0p43.getD 13 [] := by
  decide +kernel

theorem h0n43_arithmetic_row14 :
    (BiPoly.mul h0p7 h0p42).getD 14 []=h0p43.getD 14 [] := by
  decide +kernel

theorem h0n43_arithmetic_row15 :
    (BiPoly.mul h0p7 h0p42).getD 15 []=h0p43.getD 15 [] := by
  decide +kernel

theorem h0n43_arithmetic_row16 :
    (BiPoly.mul h0p7 h0p42).getD 16 []=h0p43.getD 16 [] := by
  decide +kernel

theorem h0n43_arithmetic_row17 :
    (BiPoly.mul h0p7 h0p42).getD 17 []=h0p43.getD 17 [] := by
  decide +kernel

theorem h0n43_arithmetic_row18 :
    (BiPoly.mul h0p7 h0p42).getD 18 []=h0p43.getD 18 [] := by
  decide +kernel

theorem h0n43_arithmetic : BiPoly.mul h0p7 h0p42=h0p43 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p7 h0p42).getD j.val []=h0p43.getD j.val [] :=
      (fun j => Fin.cases h0n43_arithmetic_row0 (fun j => Fin.cases h0n43_arithmetic_row1 (fun j => Fin.cases h0n43_arithmetic_row2 (fun j => Fin.cases h0n43_arithmetic_row3 (fun j => Fin.cases h0n43_arithmetic_row4 (fun j => Fin.cases h0n43_arithmetic_row5 (fun j => Fin.cases h0n43_arithmetic_row6 (fun j => Fin.cases h0n43_arithmetic_row7 (fun j => Fin.cases h0n43_arithmetic_row8 (fun j => Fin.cases h0n43_arithmetic_row9 (fun j => Fin.cases h0n43_arithmetic_row10 (fun j => Fin.cases h0n43_arithmetic_row11 (fun j => Fin.cases h0n43_arithmetic_row12 (fun j => Fin.cases h0n43_arithmetic_row13 (fun j => Fin.cases h0n43_arithmetic_row14 (fun j => Fin.cases h0n43_arithmetic_row15 (fun j => Fin.cases h0n43_arithmetic_row16 (fun j => Fin.cases h0n43_arithmetic_row17 (fun j => Fin.cases h0n43_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n43 : h0e43.toBi mapPolyEnv=h0p43 := by
  change BiPoly.mul (h0e7.toBi mapPolyEnv) (h0e42.toBi mapPolyEnv)=h0p43
  rw [h0n7, h0n42]
  exact h0n43_arithmetic

#print axioms h0n43_arithmetic
end StackSorting.RationalLift
