import BivariateRowEquality
import Horner5Base
import Horner5Node032
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p33 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 4180984128000), (Int.ofNat 8297899303680), (Int.negSucc 45501490491551), (Int.negSucc 51858619331327), (Int.ofNat 27114307727040), (Int.ofNat 57933115197696), (Int.ofNat 28578593806560)], [(Int.ofNat 0), (Int.negSucc 36386950014719), (Int.negSucc 56667226783103), (Int.ofNat 412551114294384), (Int.ofNat 347540035227984), (Int.negSucc 224765639398943), (Int.negSucc 384640579629791), (Int.negSucc 158703553275983), (Int.ofNat 2004536202768)], [(Int.ofNat 0), (Int.ofNat 142478475949440), (Int.ofNat 173882374221888), (Int.negSucc 1631808397773359), (Int.negSucc 1090216556408159), (Int.ofNat 651339476620992), (Int.ofNat 1175445552678336), (Int.ofNat 475098777146448), (Int.ofNat 58034176030944), (Int.negSucc 5514967272671)], [(Int.ofNat 0), (Int.negSucc 331086942711359), (Int.negSucc 329507085973535), (Int.ofNat 3740102325314784), (Int.ofNat 2378360460945312), (Int.negSucc 702262428729983), (Int.negSucc 2206772932502015), (Int.negSucc 1032200213147135), (Int.negSucc 300315503503295), (Int.ofNat 30550877800416), (Int.negSucc 1054713261887)], [(Int.ofNat 0), (Int.ofNat 506931708009600), (Int.ofNat 462122241306624), (Int.negSucc 5535265333697351), (Int.negSucc 4393560480296687), (Int.negSucc 443297263233527), (Int.ofNat 2625490569042720), (Int.ofNat 1722237229897992), (Int.ofNat 654410550635280), (Int.negSucc 5740207566119), (Int.negSucc 515831779583), (Int.ofNat 5393773440)], [(Int.ofNat 0), (Int.negSucc 536571367868159), (Int.negSucc 543659347860479), (Int.ofNat 5541925153695624), (Int.ofNat 6847916216037984), (Int.ofNat 2542796272218744), (Int.negSucc 1461367769407631), (Int.negSucc 2110841449436087), (Int.negSucc 816614151719759), (Int.negSucc 168231596480855), (Int.ofNat 13651320033936), (Int.negSucc 194488854911)], [(Int.ofNat 0), (Int.ofNat 400341682081920), (Int.ofNat 547793302382016), (Int.negSucc 3774901024648055), (Int.negSucc 8182965339663455), (Int.negSucc 4582930353159503), (Int.negSucc 946618260517487), (Int.ofNat 1561012427396088), (Int.ofNat 693455361529728), (Int.ofNat 345846650003904), (Int.negSucc 6099157086095), (Int.negSucc 400242647807)], [(Int.ofNat 0), (Int.negSucc 210414911706239), (Int.negSucc 440495695051967), (Int.ofNat 1659271079127336), (Int.ofNat 7001497332160440), (Int.ofNat 5742717205509600), (Int.ofNat 2849161246769544), (Int.negSucc 40218254044343), (Int.negSucc 461109193780343), (Int.negSucc 267696168040463), (Int.negSucc 40910447037287), (Int.ofNat 1541841656544)], [(Int.ofNat 0), (Int.ofNat 76308835762560), (Int.ofNat 260428475772096), (Int.negSucc 362218713682151), (Int.negSucc 4116413225224847), (Int.negSucc 5410830671989823), (Int.negSucc 3246752799489935), (Int.negSucc 1336740181004087), (Int.ofNat 113840227795872), (Int.ofNat 41361464361288), (Int.ofNat 60760921766928), (Int.ofNat 1818520606728)], [(Int.ofNat 0), (Int.negSucc 18181322687999), (Int.negSucc 106126450710143), (Int.negSucc 50661850708535), (Int.ofNat 1581947387578104), (Int.ofNat 3672441670457592), (Int.ofNat 2648740039657344), (Int.ofNat 1582526331837216), (Int.ofNat 299769597116712), (Int.ofNat 70157380263840), (Int.negSucc 19094207498495), (Int.negSucc 3728571945695)], [(Int.ofNat 0), (Int.ofNat 2561558530560), (Int.ofNat 27873834862080), (Int.ofNat 63739679688840), (Int.negSucc 357545897096447), (Int.negSucc 1681431110450423), (Int.negSucc 1732951740523247), (Int.negSucc 1042781243726447), (Int.negSucc 460735923219839), (Int.negSucc 78626247705719), (Int.negSucc 17887643112959), (Int.negSucc 234580753727)], [(Int.ofNat 0), (Int.negSucc 161749473599), (Int.negSucc 4221320631071), (Int.negSucc 19957804386215), (Int.ofNat 34596838549608), (Int.ofNat 478315243440432), (Int.ofNat 849422408493096), (Int.ofNat 508747541862240), (Int.ofNat 315073487577024), (Int.ofNat 66427393077504), (Int.ofNat 19424427685056), (Int.ofNat 2193371794368)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 278999161920), (Int.ofNat 2880139651056), (Int.ofNat 538742342304), (Int.negSucc 74430895043735), (Int.negSucc 269842394949551), (Int.negSucc 216789525801287), (Int.negSucc 123504998107391), (Int.negSucc 41761885474943), (Int.negSucc 9395749384703), (Int.negSucc 909611324639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 154876384799), (Int.ofNat 292071494808), (Int.ofNat 6008065315488), (Int.ofNat 44913307249152), (Int.ofNat 74063064482208), (Int.ofNat 31787205235200), (Int.ofNat 16793548561728), (Int.ofNat 2479132018368), (Int.ofNat 92521087488)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 128966315615), (Int.negSucc 965899767527), (Int.negSucc 2053408741631), (Int.negSucc 14957769488255), (Int.negSucc 7381019261951), (Int.negSucc 3783394344959), (Int.negSucc 248021865215)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 182020483584), (Int.negSucc 58994054783), (Int.ofNat 942333201792), (Int.ofNat 1670460211008), (Int.ofNat 344439848448)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 43918132607), (Int.ofNat 81562378464), (Int.negSucc 188939070719)]]

theorem h5n33_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p32).getD 0 []=h5p33.getD 0 [] := by
  decide +kernel

theorem h5n33_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p32).getD 1 []=h5p33.getD 1 [] := by
  decide +kernel

theorem h5n33_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p32).getD 2 []=h5p33.getD 2 [] := by
  decide +kernel

theorem h5n33_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p32).getD 3 []=h5p33.getD 3 [] := by
  decide +kernel

theorem h5n33_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p32).getD 4 []=h5p33.getD 4 [] := by
  decide +kernel

theorem h5n33_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p32).getD 5 []=h5p33.getD 5 [] := by
  decide +kernel

theorem h5n33_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p32).getD 6 []=h5p33.getD 6 [] := by
  decide +kernel

theorem h5n33_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p32).getD 7 []=h5p33.getD 7 [] := by
  decide +kernel

theorem h5n33_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p32).getD 8 []=h5p33.getD 8 [] := by
  decide +kernel

theorem h5n33_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p32).getD 9 []=h5p33.getD 9 [] := by
  decide +kernel

theorem h5n33_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p32).getD 10 []=h5p33.getD 10 [] := by
  decide +kernel

theorem h5n33_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p32).getD 11 []=h5p33.getD 11 [] := by
  decide +kernel

theorem h5n33_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p32).getD 12 []=h5p33.getD 12 [] := by
  decide +kernel

theorem h5n33_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p32).getD 13 []=h5p33.getD 13 [] := by
  decide +kernel

theorem h5n33_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p32).getD 14 []=h5p33.getD 14 [] := by
  decide +kernel

theorem h5n33_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p32).getD 15 []=h5p33.getD 15 [] := by
  decide +kernel

theorem h5n33_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p32).getD 16 []=h5p33.getD 16 [] := by
  decide +kernel

theorem h5n33_arithmetic : BiPoly.mul h5p5 h5p32=h5p33 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p32).getD j.val []=h5p33.getD j.val [] :=
      (fun j => Fin.cases h5n33_arithmetic_row0 (fun j => Fin.cases h5n33_arithmetic_row1 (fun j => Fin.cases h5n33_arithmetic_row2 (fun j => Fin.cases h5n33_arithmetic_row3 (fun j => Fin.cases h5n33_arithmetic_row4 (fun j => Fin.cases h5n33_arithmetic_row5 (fun j => Fin.cases h5n33_arithmetic_row6 (fun j => Fin.cases h5n33_arithmetic_row7 (fun j => Fin.cases h5n33_arithmetic_row8 (fun j => Fin.cases h5n33_arithmetic_row9 (fun j => Fin.cases h5n33_arithmetic_row10 (fun j => Fin.cases h5n33_arithmetic_row11 (fun j => Fin.cases h5n33_arithmetic_row12 (fun j => Fin.cases h5n33_arithmetic_row13 (fun j => Fin.cases h5n33_arithmetic_row14 (fun j => Fin.cases h5n33_arithmetic_row15 (fun j => Fin.cases h5n33_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n33 : h5e33.toBi mapPolyEnv=h5p33 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e32.toBi mapPolyEnv)=h5p33
  rw [h5n5, h5n32]
  exact h5n33_arithmetic

#print axioms h5n33_arithmetic
end StackSorting.RationalLift
