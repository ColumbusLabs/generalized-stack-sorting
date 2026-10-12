import BivariateRowEquality
import Horner5Base
import Horner5Node111
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p112 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 1045246032000), (Int.ofNat 2074474825920), (Int.negSucc 14129600746103), (Int.negSucc 25570746501695), (Int.ofNat 4118374866960), (Int.ofNat 35964237183552), (Int.ofNat 21433945354920)], [(Int.ofNat 0), (Int.negSucc 9096737503679), (Int.negSucc 14166806695775), (Int.ofNat 128574000456084), (Int.ofNat 200549105191548), (Int.negSucc 40823571575447), (Int.negSucc 251221990051943), (Int.negSucc 120875429134331), (Int.ofNat 1503402152076)], [(Int.ofNat 0), (Int.ofNat 35619618987360), (Int.ofNat 43470593555472), (Int.negSucc 518049742241987), (Int.negSucc 731898410906375), (Int.ofNat 135804724038864), (Int.ofNat 774578794990320), (Int.ofNat 344210514977628), (Int.ofNat 44871050504232), (Int.negSucc 4136225454503)], [(Int.ofNat 0), (Int.negSucc 82771735677839), (Int.negSucc 82376771493383), (Int.ofNat 1230853191950664), (Int.ofNat 1684479905053416), (Int.negSucc 132286830047999), (Int.negSucc 1321239016951631), (Int.negSucc 704848740813215), (Int.negSucc 235641810598847), (Int.ofNat 23444124857064), (Int.negSucc 791034946415)], [(Int.ofNat 0), (Int.ofNat 126732927002400), (Int.ofNat 115530560326656), (Int.negSucc 1932718247342117), (Int.negSucc 2778270261270083), (Int.negSucc 376034921860121), (Int.ofNat 1232271843094584), (Int.ofNat 1160925344201430), (Int.ofNat 493837223732028), (Int.negSucc 4685463874205), (Int.negSucc 338235201215), (Int.ofNat 4045330080)], [(Int.ofNat 0), (Int.negSucc 134142841967039), (Int.negSucc 135914836965119), (Int.ofNat 2123682428018646), (Int.ofNat 3489575303339064), (Int.ofNat 1568448372352122), (Int.negSucc 330111108358091), (Int.negSucc 1344792289240025), (Int.negSucc 558943525886795), (Int.negSucc 133205071556609), (Int.ofNat 10425149129772), (Int.negSucc 145866641183)], [(Int.ofNat 0), (Int.ofNat 100085420520480), (Int.ofNat 136948325595504), (Int.negSucc 1677923941713977), (Int.negSucc 3416141900521847), (Int.negSucc 2843478992511947), (Int.negSucc 779264627570579), (Int.ofNat 724363464876282), (Int.ofNat 433053884370000), (Int.ofNat 265492902242784), (Int.negSucc 4939047059051), (Int.negSucc 300181985855)], [(Int.ofNat 0), (Int.negSucc 52603727926559), (Int.negSucc 110123923762991), (Int.ofNat 956424142091598), (Int.ofNat 2615770202604954), (Int.ofNat 3243016023780696), (Int.ofNat 1533648665710374), (Int.ofNat 375012698119686), (Int.negSucc 268589284178297), (Int.negSucc 181041236185595), (Int.negSucc 32154824829629), (Int.ofNat 1156381242408)], [(Int.ofNat 0), (Int.ofNat 19077208940640), (Int.ofNat 65107118943024), (Int.negSucc 383915148011021), (Int.negSucc 1558679215723931), (Int.negSucc 2541806362818047), (Int.negSucc 1770817551829643), (Int.negSucc 964095552415961), (Int.negSucc 12533713239623), (Int.ofNat 3133665528870), (Int.ofNat 46842113185260), (Int.ofNat 1363890455046)], [(Int.ofNat 0), (Int.negSucc 4545330671999), (Int.negSucc 26531612677535), (Int.ofNat 101323112054790), (Int.ofNat 715960445753130), (Int.ofNat 1422752778827802), (Int.ofNat 1467482726087136), (Int.ofNat 839767526696664), (Int.ofNat 292134223607454), (Int.ofNat 61563098829528), (Int.negSucc 11246828035103), (Int.negSucc 2796428959271)], [(Int.ofNat 0), (Int.ofNat 640389632640), (Int.ofNat 6968458715520), (Int.negSucc 14552966955929), (Int.negSucc 250716557124335), (Int.negSucc 584627899945193), (Int.negSucc 852640119322451), (Int.negSucc 511854596156915), (Int.negSucc 307325306009663), (Int.negSucc 60737851954457), (Int.negSucc 16456032156959), (Int.negSucc 175935565295)], [(Int.ofNat 0), (Int.negSucc 40437368399), (Int.negSucc 1055330157767), (Int.ofNat 228286687026), (Int.ofNat 66466954923342), (Int.ofNat 182153970929268), (Int.ofNat 334366966386414), (Int.ofNat 259518079491912), (Int.ofNat 160483453076304), (Int.ofNat 49292581173696), (Int.ofNat 14146876659024), (Int.ofNat 1645028845776)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 69749790480), (Int.ofNat 225210089412), (Int.negSucc 13253123415815), (Int.negSucc 45391191999425), (Int.negSucc 84965112167651), (Int.negSucc 101910940074485), (Int.negSucc 54449342967743), (Int.negSucc 25356349374623), (Int.negSucc 5897990868479), (Int.negSucc 682208493479)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 20724337079), (Int.ofNat 1867403548818), (Int.ofNat 9641277372312), (Int.ofNat 13034362506912), (Int.ofNat 27031887735480), (Int.ofNat 14115190389696), (Int.ofNat 7683160226544), (Int.ofNat 1499767395984), (Int.ofNat 69390815616)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 139104950183), (Int.negSucc 1635586065197), (Int.negSucc 1256379226271), (Int.negSucc 4029969957983), (Int.negSucc 2909394910079), (Int.negSucc 1449818300159), (Int.negSucc 154526553791)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 149834655360), (Int.ofNat 203992465824), (Int.ofNat 121539069216), (Int.ofNat 481462505712), (Int.ofNat 132370505856)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 34822662047), (Int.ofNat 35334126504), (Int.negSucc 47234767679)]]

theorem h5n112_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p111).getD 0 []=h5p112.getD 0 [] := by
  decide +kernel

theorem h5n112_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p111).getD 1 []=h5p112.getD 1 [] := by
  decide +kernel

theorem h5n112_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p111).getD 2 []=h5p112.getD 2 [] := by
  decide +kernel

theorem h5n112_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p111).getD 3 []=h5p112.getD 3 [] := by
  decide +kernel

theorem h5n112_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p111).getD 4 []=h5p112.getD 4 [] := by
  decide +kernel

theorem h5n112_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p111).getD 5 []=h5p112.getD 5 [] := by
  decide +kernel

theorem h5n112_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p111).getD 6 []=h5p112.getD 6 [] := by
  decide +kernel

theorem h5n112_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p111).getD 7 []=h5p112.getD 7 [] := by
  decide +kernel

theorem h5n112_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p111).getD 8 []=h5p112.getD 8 [] := by
  decide +kernel

theorem h5n112_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p111).getD 9 []=h5p112.getD 9 [] := by
  decide +kernel

theorem h5n112_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p111).getD 10 []=h5p112.getD 10 [] := by
  decide +kernel

theorem h5n112_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p111).getD 11 []=h5p112.getD 11 [] := by
  decide +kernel

theorem h5n112_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p111).getD 12 []=h5p112.getD 12 [] := by
  decide +kernel

theorem h5n112_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p111).getD 13 []=h5p112.getD 13 [] := by
  decide +kernel

theorem h5n112_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p111).getD 14 []=h5p112.getD 14 [] := by
  decide +kernel

theorem h5n112_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p111).getD 15 []=h5p112.getD 15 [] := by
  decide +kernel

theorem h5n112_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p111).getD 16 []=h5p112.getD 16 [] := by
  decide +kernel

theorem h5n112_arithmetic : BiPoly.mul h5p5 h5p111=h5p112 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p111).getD j.val []=h5p112.getD j.val [] :=
      (fun j => Fin.cases h5n112_arithmetic_row0 (fun j => Fin.cases h5n112_arithmetic_row1 (fun j => Fin.cases h5n112_arithmetic_row2 (fun j => Fin.cases h5n112_arithmetic_row3 (fun j => Fin.cases h5n112_arithmetic_row4 (fun j => Fin.cases h5n112_arithmetic_row5 (fun j => Fin.cases h5n112_arithmetic_row6 (fun j => Fin.cases h5n112_arithmetic_row7 (fun j => Fin.cases h5n112_arithmetic_row8 (fun j => Fin.cases h5n112_arithmetic_row9 (fun j => Fin.cases h5n112_arithmetic_row10 (fun j => Fin.cases h5n112_arithmetic_row11 (fun j => Fin.cases h5n112_arithmetic_row12 (fun j => Fin.cases h5n112_arithmetic_row13 (fun j => Fin.cases h5n112_arithmetic_row14 (fun j => Fin.cases h5n112_arithmetic_row15 (fun j => Fin.cases h5n112_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n112 : h5e112.toBi mapPolyEnv=h5p112 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e111.toBi mapPolyEnv)=h5p112
  rw [h5n5, h5n111]
  exact h5n112_arithmetic

#print axioms h5n112_arithmetic
end StackSorting.RationalLift
