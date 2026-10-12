import BivariateRowEquality
import Horner1Base
import Horner1Node085
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p86 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 44079842304), (Int.ofNat 176319369216), (Int.ofNat 264479053824), (Int.ofNat 176319369216), (Int.ofNat 44079842304)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 679156088831), (Int.negSucc 2432554260479), (Int.negSucc 3258643156991), (Int.negSucc 1972164796415), (Int.negSucc 502836719615), (Int.negSucc 35916908543)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4921251365376), (Int.ofNat 15823937793024), (Int.ofNat 19395765508608), (Int.ofNat 11572137695232), (Int.ofNat 3633503215104), (Int.ofNat 541474606080), (Int.negSucc 12969994751)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 22279005531647), (Int.negSucc 64823806462463), (Int.negSucc 75564986614271), (Int.negSucc 48054862960127), (Int.negSucc 18462897824255), (Int.negSucc 3509117572607), (Int.negSucc 67754589695), (Int.ofNat 13142435328)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 70596139788864), (Int.ofNat 188844492745728), (Int.ofNat 219762711684864), (Int.ofNat 154480232678400), (Int.ofNat 67633341565824), (Int.ofNat 15857966730240), (Int.ofNat 1508229206784), (Int.negSucc 158452816895), (Int.ofNat 1972745280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 166232531380607), (Int.negSucc 419735179224575), (Int.negSucc 510702504187391), (Int.negSucc 394110795649535), (Int.negSucc 190320617067263), (Int.negSucc 56507870979071), (Int.negSucc 8466963706367), (Int.ofNat 361450833408), (Int.ofNat 36107330688), (Int.negSucc 1784775167)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 301364196421824), (Int.ofNat 746468154074880), (Int.ofNat 978421051464192), (Int.ofNat 811387638217728), (Int.ofNat 436188006253440), (Int.ofNat 157298184672768), (Int.ofNat 30052005460992), (Int.ofNat 1553587540992), (Int.negSucc 411214100543), (Int.ofNat 18484215552), (Int.negSucc 239196671)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 429972338118911), (Int.negSucc 1098031841011967), (Int.negSucc 1562108415937535), (Int.negSucc 1379545740025343), (Int.negSucc 835884176408063), (Int.negSucc 343501490598911), (Int.negSucc 84325686171647), (Int.negSucc 10707293930495), (Int.ofNat 1114635330816), (Int.ofNat 3940780800), (Int.negSucc 2703275519), (Int.ofNat 89954304)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 489281355605056), (Int.ofNat 1363110779155968), (Int.ofNat 2087347853146240), (Int.ofNat 1983604164711424), (Int.ofNat 1341162429027072), (Int.ofNat 611354395278336), (Int.ofNat 191255202386176), (Int.ofNat 32362622856192), (Int.ofNat 533061539776), (Int.negSucc 437300575743), (Int.ofNat 29268615552), (Int.negSucc 949971967), (Int.ofNat 14992384)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 447240439800447), (Int.negSucc 1438327700504575), (Int.negSucc 2349076002551807), (Int.negSucc 2446886316945407), (Int.negSucc 1801151695047167), (Int.negSucc 921343322744831), (Int.negSucc 342103883072511), (Int.negSucc 72831641099263), (Int.negSucc 8662688909183), (Int.ofNat 1253963561984), (Int.negSucc 39372300799), (Int.ofNat 354799104), (Int.negSucc 16355327)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 329055921411264), (Int.ofNat 1284777265691904), (Int.ofNat 2249051892615936), (Int.ofNat 2592528023234304), (Int.ofNat 2046964263643392), (Int.ofNat 1188107230012416), (Int.ofNat 489481963309056), (Int.ofNat 135973794832896), (Int.ofNat 22614075319872), (Int.negSucc 207798051071), (Int.negSucc 225645202175), (Int.ofNat 14574177024), (Int.negSucc 318371327)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 194338413806591), (Int.negSucc 960247840561919), (Int.negSucc 1850940401656319), (Int.negSucc 2345168630885119), (Int.negSucc 2003358073861631), (Int.negSucc 1296495082115071), (Int.negSucc 586604164857855), (Int.negSucc 202737348988415), (Int.negSucc 39480008327167), (Int.negSucc 4705087228671), (Int.ofNat 692411432448), (Int.negSucc 26070967039), (Int.ofNat 463733248)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 91413458463936), (Int.ofNat 591088208953344), (Int.ofNat 1314368547404160), (Int.ofNat 1804941890978048), (Int.ofNat 1704911432896960), (Int.ofNat 1189976320035840), (Int.ofNat 608574518675456), (Int.ofNat 235963807088128), (Int.ofNat 58719027470208), (Int.ofNat 10443694306304), (Int.negSucc 206823193471), (Int.negSucc 58965977855), (Int.ofNat 2418831936)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 33769746695807), (Int.negSucc 294177196629503), (Int.negSucc 798440718018047), (Int.negSucc 1187201656031999), (Int.negSucc 1253323582550399), (Int.negSucc 930834095219711), (Int.negSucc 541697983712255), (Int.negSucc 223297164664319), (Int.negSucc 72401168181503), (Int.negSucc 13524328645631), (Int.negSucc 1647305412095), (Int.ofNat 186957418752), (Int.negSucc 4624451711)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9578177361984), (Int.ofNat 115818665787648), (Int.ofNat 406002793473024), (Int.ofNat 673257974645248), (Int.ofNat 783868365822144), (Int.ofNat 633669813921280), (Int.ofNat 402987022355456), (Int.ofNat 183068006742528), (Int.ofNat 68292744495232), (Int.ofNat 15085071125504), (Int.ofNat 2983576347648), (Int.negSucc 45565970431), (Int.negSucc 6782690239)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2011847036159), (Int.negSucc 35078426674943), (Int.negSucc 167453794572287), (Int.negSucc 329433078682623), (Int.negSucc 413937075872767), (Int.negSucc 376353189348863), (Int.negSucc 250252442045439), (Int.negSucc 131340517604863), (Int.negSucc 49936903297535), (Int.negSucc 14968520270847), (Int.negSucc 2743226376703), (Int.negSucc 328231755263), (Int.ofNat 19393562112)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 294576734400), (Int.ofNat 7856644369920), (Int.ofNat 53893952534400), (Int.ofNat 136285192877568), (Int.ofNat 186124678466688), (Int.ofNat 190332942744576), (Int.ofNat 133896225230592), (Int.ofNat 78438855224832), (Int.ofNat 31214659294848), (Int.ofNat 11240271230976), (Int.ofNat 2109390464256), (Int.ofNat 455072510976), (Int.negSucc 1506627071)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 26820975999), (Int.negSucc 1222344115199), (Int.negSucc 12897476426751), (Int.negSucc 45611428978175), (Int.negSucc 72179511832319), (Int.negSucc 79848927899647), (Int.negSucc 63119351303167), (Int.negSucc 37845423438335), (Int.negSucc 17592362682623), (Int.negSucc 6097489044479), (Int.negSucc 1602291525119), (Int.negSucc 282058532351), (Int.negSucc 27065235455)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1142440000), (Int.ofNat 117694304000), (Int.ofNat 2142947093760), (Int.ofNat 11601815147264), (Int.ofNat 23809751131264), (Int.ofNat 27872670372864), (Int.ofNat 25384594195968), (Int.ofNat 15385702523904), (Int.ofNat 8237305819008), (Int.ofNat 2732250120192), (Int.ofNat 920676519936), (Int.ofNat 130472322048), (Int.ofNat 26582929920)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5272799999), (Int.negSucc 219442329599), (Int.negSucc 2065717198079), (Int.negSucc 6280637975039), (Int.negSucc 8347817768447), (Int.negSucc 8231498648063), (Int.negSucc 5589334872575), (Int.negSucc 2953559877119), (Int.negSucc 1155377530367), (Int.negSucc 343894201343), (Int.negSucc 66898897919), (Int.negSucc 10354894847)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 10391472000), (Int.ofNat 226403078400), (Int.ofNat 1194642997056), (Int.ofNat 2139854192640), (Int.ofNat 2139599183616), (Int.ofNat 1733024553984), (Int.ofNat 859547026944), (Int.ofNat 402511693824), (Int.ofNat 98382574080), (Int.ofNat 26447855616), (Int.ofNat 1971495936)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 11400479999), (Int.negSucc 140994760319), (Int.negSucc 425028446207), (Int.negSucc 476919304703), (Int.negSucc 409949213183), (Int.negSucc 229759690751), (Int.negSucc 97644828671), (Int.negSucc 27772637183), (Int.negSucc 5836105727), (Int.negSucc 183638015)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7605057600), (Int.ofNat 54164090880), (Int.ofNat 91981495296), (Int.ofNat 73264186368), (Int.ofNat 51607466496), (Int.ofNat 17888034816), (Int.ofNat 6333272064), (Int.ofNat 636014592), (Int.ofNat 6718464)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3157055999), (Int.negSucc 12520977407), (Int.negSucc 11611745279), (Int.negSucc 7799887871), (Int.negSucc 3156185087), (Int.negSucc 806215679), (Int.negSucc 26873855)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 796884480), (Int.ofNat 1591529472), (Int.ofNat 799497216), (Int.ofNat 438939648), (Int.ofNat 40310784)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 111974399), (Int.negSucc 85100543), (Int.negSucc 26873855)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 6718464)]]

theorem h1n86_arithmetic_row0 :
    (BiPoly.mul h1p9 h1p85).getD 0 []=h1p86.getD 0 [] := by
  decide +kernel

theorem h1n86_arithmetic_row1 :
    (BiPoly.mul h1p9 h1p85).getD 1 []=h1p86.getD 1 [] := by
  decide +kernel

theorem h1n86_arithmetic_row2 :
    (BiPoly.mul h1p9 h1p85).getD 2 []=h1p86.getD 2 [] := by
  decide +kernel

theorem h1n86_arithmetic_row3 :
    (BiPoly.mul h1p9 h1p85).getD 3 []=h1p86.getD 3 [] := by
  decide +kernel

theorem h1n86_arithmetic_row4 :
    (BiPoly.mul h1p9 h1p85).getD 4 []=h1p86.getD 4 [] := by
  decide +kernel

theorem h1n86_arithmetic_row5 :
    (BiPoly.mul h1p9 h1p85).getD 5 []=h1p86.getD 5 [] := by
  decide +kernel

theorem h1n86_arithmetic_row6 :
    (BiPoly.mul h1p9 h1p85).getD 6 []=h1p86.getD 6 [] := by
  decide +kernel

theorem h1n86_arithmetic_row7 :
    (BiPoly.mul h1p9 h1p85).getD 7 []=h1p86.getD 7 [] := by
  decide +kernel

theorem h1n86_arithmetic_row8 :
    (BiPoly.mul h1p9 h1p85).getD 8 []=h1p86.getD 8 [] := by
  decide +kernel

theorem h1n86_arithmetic_row9 :
    (BiPoly.mul h1p9 h1p85).getD 9 []=h1p86.getD 9 [] := by
  decide +kernel

theorem h1n86_arithmetic_row10 :
    (BiPoly.mul h1p9 h1p85).getD 10 []=h1p86.getD 10 [] := by
  decide +kernel

theorem h1n86_arithmetic_row11 :
    (BiPoly.mul h1p9 h1p85).getD 11 []=h1p86.getD 11 [] := by
  decide +kernel

theorem h1n86_arithmetic_row12 :
    (BiPoly.mul h1p9 h1p85).getD 12 []=h1p86.getD 12 [] := by
  decide +kernel

theorem h1n86_arithmetic_row13 :
    (BiPoly.mul h1p9 h1p85).getD 13 []=h1p86.getD 13 [] := by
  decide +kernel

theorem h1n86_arithmetic_row14 :
    (BiPoly.mul h1p9 h1p85).getD 14 []=h1p86.getD 14 [] := by
  decide +kernel

theorem h1n86_arithmetic_row15 :
    (BiPoly.mul h1p9 h1p85).getD 15 []=h1p86.getD 15 [] := by
  decide +kernel

theorem h1n86_arithmetic_row16 :
    (BiPoly.mul h1p9 h1p85).getD 16 []=h1p86.getD 16 [] := by
  decide +kernel

theorem h1n86_arithmetic_row17 :
    (BiPoly.mul h1p9 h1p85).getD 17 []=h1p86.getD 17 [] := by
  decide +kernel

theorem h1n86_arithmetic_row18 :
    (BiPoly.mul h1p9 h1p85).getD 18 []=h1p86.getD 18 [] := by
  decide +kernel

theorem h1n86_arithmetic_row19 :
    (BiPoly.mul h1p9 h1p85).getD 19 []=h1p86.getD 19 [] := by
  decide +kernel

theorem h1n86_arithmetic_row20 :
    (BiPoly.mul h1p9 h1p85).getD 20 []=h1p86.getD 20 [] := by
  decide +kernel

theorem h1n86_arithmetic_row21 :
    (BiPoly.mul h1p9 h1p85).getD 21 []=h1p86.getD 21 [] := by
  decide +kernel

theorem h1n86_arithmetic_row22 :
    (BiPoly.mul h1p9 h1p85).getD 22 []=h1p86.getD 22 [] := by
  decide +kernel

theorem h1n86_arithmetic_row23 :
    (BiPoly.mul h1p9 h1p85).getD 23 []=h1p86.getD 23 [] := by
  decide +kernel

theorem h1n86_arithmetic_row24 :
    (BiPoly.mul h1p9 h1p85).getD 24 []=h1p86.getD 24 [] := by
  decide +kernel

theorem h1n86_arithmetic_row25 :
    (BiPoly.mul h1p9 h1p85).getD 25 []=h1p86.getD 25 [] := by
  decide +kernel

theorem h1n86_arithmetic_row26 :
    (BiPoly.mul h1p9 h1p85).getD 26 []=h1p86.getD 26 [] := by
  decide +kernel

theorem h1n86_arithmetic : BiPoly.mul h1p9 h1p85=h1p86 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<27 at hk
    have hf : ∀ j : Fin 27, (BiPoly.mul h1p9 h1p85).getD j.val []=h1p86.getD j.val [] :=
      (fun j => Fin.cases h1n86_arithmetic_row0 (fun j => Fin.cases h1n86_arithmetic_row1 (fun j => Fin.cases h1n86_arithmetic_row2 (fun j => Fin.cases h1n86_arithmetic_row3 (fun j => Fin.cases h1n86_arithmetic_row4 (fun j => Fin.cases h1n86_arithmetic_row5 (fun j => Fin.cases h1n86_arithmetic_row6 (fun j => Fin.cases h1n86_arithmetic_row7 (fun j => Fin.cases h1n86_arithmetic_row8 (fun j => Fin.cases h1n86_arithmetic_row9 (fun j => Fin.cases h1n86_arithmetic_row10 (fun j => Fin.cases h1n86_arithmetic_row11 (fun j => Fin.cases h1n86_arithmetic_row12 (fun j => Fin.cases h1n86_arithmetic_row13 (fun j => Fin.cases h1n86_arithmetic_row14 (fun j => Fin.cases h1n86_arithmetic_row15 (fun j => Fin.cases h1n86_arithmetic_row16 (fun j => Fin.cases h1n86_arithmetic_row17 (fun j => Fin.cases h1n86_arithmetic_row18 (fun j => Fin.cases h1n86_arithmetic_row19 (fun j => Fin.cases h1n86_arithmetic_row20 (fun j => Fin.cases h1n86_arithmetic_row21 (fun j => Fin.cases h1n86_arithmetic_row22 (fun j => Fin.cases h1n86_arithmetic_row23 (fun j => Fin.cases h1n86_arithmetic_row24 (fun j => Fin.cases h1n86_arithmetic_row25 (fun j => Fin.cases h1n86_arithmetic_row26 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n86 : h1e86.toBi mapPolyEnv=h1p86 := by
  change BiPoly.mul (h1e9.toBi mapPolyEnv) (h1e85.toBi mapPolyEnv)=h1p86
  rw [h1n9, h1n85]
  exact h1n86_arithmetic

#print axioms h1n86_arithmetic
end StackSorting.RationalLift
