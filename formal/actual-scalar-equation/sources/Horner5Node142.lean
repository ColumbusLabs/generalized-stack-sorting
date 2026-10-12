import BivariateRowEquality
import Horner5Base
import Horner5Node141
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p142 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1045246032000), (Int.ofNat 4164966889920), (Int.ofNat 422167282560), (Int.ofNat 422167282560), (Int.negSucc 623078749439), (Int.negSucc 3742799607359)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 9096737503679), (Int.negSucc 32360281703135), (Int.ofNat 7505629218720), (Int.negSucc 5643853474751), (Int.ofNat 6102393355008), (Int.ofNat 20476986512544), (Int.negSucc 923882088671)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 35619618987360), (Int.ofNat 114709831530192), (Int.negSucc 52244377008911), (Int.ofNat 43015633754688), (Int.negSucc 25804202449247), (Int.negSucc 41048389788623), (Int.negSucc 7402202422127), (Int.ofNat 672709240512)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 82771735677839), (Int.negSucc 247920242849063), (Int.ofNat 125727818963904), (Int.negSucc 139468666149575), (Int.ofNat 62614218306096), (Int.ofNat 27696124091304), (Int.ofNat 49339628977248), (Int.negSucc 5733557992439), (Int.ofNat 265483253376)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 126732927002400), (Int.ofNat 368996414331456), (Int.negSucc 117906693797735), (Int.ofNat 211077970235064), (Int.negSucc 55464709743215), (Int.ofNat 19690357751856), (Int.negSucc 94945092896519), (Int.ofNat 3102812491320), (Int.negSucc 238792733279), (Int.ofNat 24319316736)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 134142841967039), (Int.negSucc 404200520899199), (Int.negSucc 60306007105943), (Int.negSucc 123663718092455), (Int.negSucc 90857965900463), (Int.negSucc 25713647542223), (Int.ofNat 56900342583144), (Int.ofNat 33200169993432), (Int.negSucc 3605068935359), (Int.ofNat 93329552160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 100085420520480), (Int.ofNat 337119166636464), (Int.ofNat 297783260927856), (Int.negSucc 40452945517991), (Int.ofNat 277381772142648), (Int.negSucc 12437961840383), (Int.ofNat 49097714897952), (Int.negSucc 65984960287607), (Int.ofNat 3791954823048), (Int.negSucc 182339622239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 52603727926559), (Int.negSucc 215331379616111), (Int.negSucc 391855631458391), (Int.ofNat 58622242387080), (Int.negSucc 263526680118935), (Int.negSucc 25236715448111), (Int.negSucc 86713226490935), (Int.ofNat 30727665140208), (Int.ofNat 10608075985080), (Int.negSucc 735994775831)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 19077208940640), (Int.ofNat 103261536824304), (Int.ofNat 300803047904592), (Int.ofNat 66186722110680), (Int.ofNat 77415778715256), (Int.ofNat 120322534450992), (Int.ofNat 33868984224792), (Int.ofNat 31794376914960), (Int.negSucc 18159117334439), (Int.ofNat 635710930032)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 4545330671999), (Int.negSucc 35622274021535), (Int.negSucc 149994959430167), (Int.negSucc 142675271725223), (Int.ofNat 33482565457008), (Int.negSucc 118883539906079), (Int.negSucc 4924017610367), (Int.negSucc 40848245655071), (Int.ofNat 3941547947184), (Int.ofNat 1536913794384)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 640389632640), (Int.ofNat 8249237980800), (Int.ofNat 48958118588160), (Int.ofNat 106812310080600), (Int.negSucc 13491923245463), (Int.ofNat 34492036608336), (Int.ofNat 19852908051120), (Int.ofNat 12688622624592), (Int.ofNat 8303871912192), (Int.negSucc 1520149911119)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 40437368399), (Int.negSucc 1136204894567), (Int.negSucc 9951604514279), (Int.negSucc 42516156560063), (Int.negSucc 18718576687175), (Int.ofNat 11418879985128), (Int.negSucc 18612673928927), (Int.ofNat 581831777088), (Int.negSucc 5923137356927), (Int.negSucc 210722052383)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 69749790480), (Int.ofNat 1106946905400), (Int.ofNat 9181983478032), (Int.ofNat 15501370706136), (Int.negSucc 7179106165199), (Int.ofNat 3045884250816), (Int.ofNat 644928220800), (Int.ofNat 990822986208), (Int.ofNat 574410585024)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 47716475759), (Int.negSucc 919607915375), (Int.negSucc 4502262975119), (Int.negSucc 613865767535), (Int.ofNat 2175559472448), (Int.negSucc 818454952799), (Int.ofNat 201223360512), (Int.negSucc 179790808895)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 21190106736), (Int.ofNat 497960833248), (Int.ofNat 896463214992), (Int.negSucc 762950269151), (Int.negSucc 34495581887), (Int.negSucc 56789351423), (Int.ofNat 15744922560)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6659646335), (Int.negSucc 137438296127), (Int.ofNat 4409531136), (Int.ofNat 106314503616), (Int.ofNat 0)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 942031296), (Int.ofNat 14802891264), (Int.negSucc 15744922559)]]

theorem h5n142_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p141).getD 0 []=h5p142.getD 0 [] := by
  decide +kernel

theorem h5n142_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p141).getD 1 []=h5p142.getD 1 [] := by
  decide +kernel

theorem h5n142_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p141).getD 2 []=h5p142.getD 2 [] := by
  decide +kernel

theorem h5n142_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p141).getD 3 []=h5p142.getD 3 [] := by
  decide +kernel

theorem h5n142_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p141).getD 4 []=h5p142.getD 4 [] := by
  decide +kernel

theorem h5n142_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p141).getD 5 []=h5p142.getD 5 [] := by
  decide +kernel

theorem h5n142_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p141).getD 6 []=h5p142.getD 6 [] := by
  decide +kernel

theorem h5n142_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p141).getD 7 []=h5p142.getD 7 [] := by
  decide +kernel

theorem h5n142_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p141).getD 8 []=h5p142.getD 8 [] := by
  decide +kernel

theorem h5n142_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p141).getD 9 []=h5p142.getD 9 [] := by
  decide +kernel

theorem h5n142_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p141).getD 10 []=h5p142.getD 10 [] := by
  decide +kernel

theorem h5n142_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p141).getD 11 []=h5p142.getD 11 [] := by
  decide +kernel

theorem h5n142_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p141).getD 12 []=h5p142.getD 12 [] := by
  decide +kernel

theorem h5n142_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p141).getD 13 []=h5p142.getD 13 [] := by
  decide +kernel

theorem h5n142_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p141).getD 14 []=h5p142.getD 14 [] := by
  decide +kernel

theorem h5n142_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p141).getD 15 []=h5p142.getD 15 [] := by
  decide +kernel

theorem h5n142_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p141).getD 16 []=h5p142.getD 16 [] := by
  decide +kernel

theorem h5n142_arithmetic : BiPoly.mul h5p5 h5p141=h5p142 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p141).getD j.val []=h5p142.getD j.val [] :=
      (fun j => Fin.cases h5n142_arithmetic_row0 (fun j => Fin.cases h5n142_arithmetic_row1 (fun j => Fin.cases h5n142_arithmetic_row2 (fun j => Fin.cases h5n142_arithmetic_row3 (fun j => Fin.cases h5n142_arithmetic_row4 (fun j => Fin.cases h5n142_arithmetic_row5 (fun j => Fin.cases h5n142_arithmetic_row6 (fun j => Fin.cases h5n142_arithmetic_row7 (fun j => Fin.cases h5n142_arithmetic_row8 (fun j => Fin.cases h5n142_arithmetic_row9 (fun j => Fin.cases h5n142_arithmetic_row10 (fun j => Fin.cases h5n142_arithmetic_row11 (fun j => Fin.cases h5n142_arithmetic_row12 (fun j => Fin.cases h5n142_arithmetic_row13 (fun j => Fin.cases h5n142_arithmetic_row14 (fun j => Fin.cases h5n142_arithmetic_row15 (fun j => Fin.cases h5n142_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n142 : h5e142.toBi mapPolyEnv=h5p142 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e141.toBi mapPolyEnv)=h5p142
  rw [h5n5, h5n141]
  exact h5n142_arithmetic

#print axioms h5n142_arithmetic
end StackSorting.RationalLift
