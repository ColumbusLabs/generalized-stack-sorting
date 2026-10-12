import BivariateRowEquality
import Horner5Base
import Horner5Node306
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p307 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 1393661375999), (Int.negSucc 2765966434559), (Int.ofNat 15167163497184), (Int.ofNat 17286206443776), (Int.negSucc 9038102575679), (Int.negSucc 19311038399231), (Int.negSucc 9526197935519)], [(Int.ofNat 0), (Int.ofNat 12128983338240), (Int.ofNat 18889075594368), (Int.negSucc 137517038098127), (Int.negSucc 115846678409327), (Int.ofNat 74921879799648), (Int.ofNat 128213526543264), (Int.ofNat 52901184425328), (Int.negSucc 668178734255)], [(Int.ofNat 0), (Int.negSucc 47492825316479), (Int.negSucc 57960791407295), (Int.ofNat 543936132591120), (Int.ofNat 363405518802720), (Int.negSucc 217113158873663), (Int.negSucc 391815184226111), (Int.negSucc 158366259048815), (Int.negSucc 19344725343647), (Int.ofNat 1838322424224)], [(Int.ofNat 0), (Int.ofNat 110362314237120), (Int.ofNat 109835695324512), (Int.negSucc 1246700775104927), (Int.negSucc 792786820315103), (Int.ofNat 234087476243328), (Int.ofNat 735590977500672), (Int.ofNat 344066737715712), (Int.ofNat 100105167834432), (Int.negSucc 10183625933471), (Int.ofNat 351571087296)], [(Int.ofNat 0), (Int.negSucc 168977236003199), (Int.negSucc 154040747102207), (Int.ofNat 1845088444565784), (Int.ofNat 1464520160098896), (Int.ofNat 147765754411176), (Int.negSucc 875163523014239), (Int.negSucc 574079076632663), (Int.negSucc 218136850211759), (Int.ofNat 1913402522040), (Int.ofNat 171943926528), (Int.negSucc 1797924479)], [(Int.ofNat 0), (Int.ofNat 178857122622720), (Int.ofNat 181219782620160), (Int.negSucc 1847308384565207), (Int.negSucc 2282638738679327), (Int.negSucc 847598757406247), (Int.ofNat 487122589802544), (Int.ofNat 703613816478696), (Int.ofNat 272204717239920), (Int.ofNat 56077198826952), (Int.negSucc 4550440011311), (Int.ofNat 64829618304)], [(Int.ofNat 0), (Int.negSucc 133447227360639), (Int.negSucc 182597767460671), (Int.ofNat 1258300341549352), (Int.ofNat 2727655113221152), (Int.ofNat 1527643451053168), (Int.ofNat 315539420172496), (Int.negSucc 520337475798695), (Int.negSucc 231151787176575), (Int.negSucc 115282216667967), (Int.ofNat 2033052362032), (Int.ofNat 133414215936)], [(Int.ofNat 0), (Int.ofNat 70138303902080), (Int.ofNat 146831898350656), (Int.negSucc 553090359709111), (Int.negSucc 2333832444053479), (Int.negSucc 1914239068503199), (Int.negSucc 949720415589847), (Int.ofNat 13406084681448), (Int.ofNat 153703064593448), (Int.ofNat 89232056013488), (Int.ofNat 13636815679096), (Int.negSucc 513947218847)], [(Int.ofNat 0), (Int.negSucc 25436278587519), (Int.negSucc 86809491924031), (Int.ofNat 120739571227384), (Int.ofNat 1372137741741616), (Int.ofNat 1803610223996608), (Int.ofNat 1082250933163312), (Int.ofNat 445580060334696), (Int.negSucc 37946742598623), (Int.negSucc 13787154787095), (Int.negSucc 20253640588975), (Int.negSucc 606173535575)], [(Int.ofNat 0), (Int.ofNat 6060440896000), (Int.ofNat 35375483570048), (Int.ofNat 16887283569512), (Int.negSucc 527315795859367), (Int.negSucc 1224147223485863), (Int.negSucc 882913346552447), (Int.negSucc 527508777279071), (Int.negSucc 99923199038903), (Int.negSucc 23385793421279), (Int.ofNat 6364735832832), (Int.ofNat 1242857315232)], [(Int.ofNat 0), (Int.negSucc 853852843519), (Int.negSucc 9291278287359), (Int.negSucc 21246559896279), (Int.ofNat 119181965698816), (Int.ofNat 560477036816808), (Int.ofNat 577650580174416), (Int.ofNat 347593747908816), (Int.ofNat 153578641073280), (Int.ofNat 26208749235240), (Int.ofNat 5962547704320), (Int.ofNat 78193584576)], [(Int.ofNat 0), (Int.ofNat 53916491200), (Int.ofNat 1407106877024), (Int.ofNat 6652601462072), (Int.negSucc 11532279516535), (Int.negSucc 159438414480143), (Int.negSucc 283140802831031), (Int.negSucc 169582513954079), (Int.negSucc 105024495859007), (Int.negSucc 22142464359167), (Int.negSucc 6474809228351), (Int.negSucc 731123931455)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 92999720639), (Int.negSucc 960046550351), (Int.negSucc 179580780767), (Int.ofNat 24810298347912), (Int.ofNat 89947464983184), (Int.ofNat 72263175267096), (Int.ofNat 41168332702464), (Int.ofNat 13920628491648), (Int.ofNat 3131916461568), (Int.ofNat 303203774880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 51625461600), (Int.negSucc 97357164935), (Int.negSucc 2002688438495), (Int.negSucc 14971102416383), (Int.negSucc 24687688160735), (Int.negSucc 10595735078399), (Int.negSucc 5597849520575), (Int.negSucc 826377339455), (Int.negSucc 30840362495)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 42988771872), (Int.ofNat 321966589176), (Int.ofNat 684469580544), (Int.ofNat 4985923162752), (Int.ofNat 2460339753984), (Int.ofNat 1261131448320), (Int.ofNat 82673955072)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 60673494527), (Int.ofNat 19664684928), (Int.negSucc 314111067263), (Int.negSucc 556820070335), (Int.negSucc 114813282815)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 14639377536), (Int.negSucc 27187459487), (Int.ofNat 62979690240)]]

theorem h5n307_arithmetic_row0 :
    (BiPoly.mul h5p5 h5p306).getD 0 []=h5p307.getD 0 [] := by
  decide +kernel

theorem h5n307_arithmetic_row1 :
    (BiPoly.mul h5p5 h5p306).getD 1 []=h5p307.getD 1 [] := by
  decide +kernel

theorem h5n307_arithmetic_row2 :
    (BiPoly.mul h5p5 h5p306).getD 2 []=h5p307.getD 2 [] := by
  decide +kernel

theorem h5n307_arithmetic_row3 :
    (BiPoly.mul h5p5 h5p306).getD 3 []=h5p307.getD 3 [] := by
  decide +kernel

theorem h5n307_arithmetic_row4 :
    (BiPoly.mul h5p5 h5p306).getD 4 []=h5p307.getD 4 [] := by
  decide +kernel

theorem h5n307_arithmetic_row5 :
    (BiPoly.mul h5p5 h5p306).getD 5 []=h5p307.getD 5 [] := by
  decide +kernel

theorem h5n307_arithmetic_row6 :
    (BiPoly.mul h5p5 h5p306).getD 6 []=h5p307.getD 6 [] := by
  decide +kernel

theorem h5n307_arithmetic_row7 :
    (BiPoly.mul h5p5 h5p306).getD 7 []=h5p307.getD 7 [] := by
  decide +kernel

theorem h5n307_arithmetic_row8 :
    (BiPoly.mul h5p5 h5p306).getD 8 []=h5p307.getD 8 [] := by
  decide +kernel

theorem h5n307_arithmetic_row9 :
    (BiPoly.mul h5p5 h5p306).getD 9 []=h5p307.getD 9 [] := by
  decide +kernel

theorem h5n307_arithmetic_row10 :
    (BiPoly.mul h5p5 h5p306).getD 10 []=h5p307.getD 10 [] := by
  decide +kernel

theorem h5n307_arithmetic_row11 :
    (BiPoly.mul h5p5 h5p306).getD 11 []=h5p307.getD 11 [] := by
  decide +kernel

theorem h5n307_arithmetic_row12 :
    (BiPoly.mul h5p5 h5p306).getD 12 []=h5p307.getD 12 [] := by
  decide +kernel

theorem h5n307_arithmetic_row13 :
    (BiPoly.mul h5p5 h5p306).getD 13 []=h5p307.getD 13 [] := by
  decide +kernel

theorem h5n307_arithmetic_row14 :
    (BiPoly.mul h5p5 h5p306).getD 14 []=h5p307.getD 14 [] := by
  decide +kernel

theorem h5n307_arithmetic_row15 :
    (BiPoly.mul h5p5 h5p306).getD 15 []=h5p307.getD 15 [] := by
  decide +kernel

theorem h5n307_arithmetic_row16 :
    (BiPoly.mul h5p5 h5p306).getD 16 []=h5p307.getD 16 [] := by
  decide +kernel

theorem h5n307_arithmetic : BiPoly.mul h5p5 h5p306=h5p307 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p5 h5p306).getD j.val []=h5p307.getD j.val [] :=
      (fun j => Fin.cases h5n307_arithmetic_row0 (fun j => Fin.cases h5n307_arithmetic_row1 (fun j => Fin.cases h5n307_arithmetic_row2 (fun j => Fin.cases h5n307_arithmetic_row3 (fun j => Fin.cases h5n307_arithmetic_row4 (fun j => Fin.cases h5n307_arithmetic_row5 (fun j => Fin.cases h5n307_arithmetic_row6 (fun j => Fin.cases h5n307_arithmetic_row7 (fun j => Fin.cases h5n307_arithmetic_row8 (fun j => Fin.cases h5n307_arithmetic_row9 (fun j => Fin.cases h5n307_arithmetic_row10 (fun j => Fin.cases h5n307_arithmetic_row11 (fun j => Fin.cases h5n307_arithmetic_row12 (fun j => Fin.cases h5n307_arithmetic_row13 (fun j => Fin.cases h5n307_arithmetic_row14 (fun j => Fin.cases h5n307_arithmetic_row15 (fun j => Fin.cases h5n307_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n307 : h5e307.toBi mapPolyEnv=h5p307 := by
  change BiPoly.mul (h5e5.toBi mapPolyEnv) (h5e306.toBi mapPolyEnv)=h5p307
  rw [h5n5, h5n306]
  exact h5n307_arithmetic

#print axioms h5n307_arithmetic
end StackSorting.RationalLift
