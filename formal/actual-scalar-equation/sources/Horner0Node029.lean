import BivariateRowEquality
import Horner0Base
import Horner0Node009
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p29 : BiPoly.Poly := [[(Int.negSucc 4570641570476951999), (Int.negSucc 25420410673783377119), (Int.ofNat 4924480448075562720), (Int.ofNat 112952237759800967520), (Int.negSucc 84911431881329776799)], [(Int.ofNat 42208024553566260480), (Int.ofNat 237041991199880502336), (Int.negSucc 24780262717250796383), (Int.negSucc 994117109227092380159), (Int.ofNat 780306328285932589344), (Int.negSucc 61509085945343740799)], [(Int.negSucc 183736109199505201199), (Int.negSucc 1004380456288621879799), (Int.ofNat 49683576825750412944), (Int.ofNat 3800089894672185579936), (Int.negSucc 2854644260739960663359), (Int.ofNat 289246112209963507320), (Int.negSucc 14421032149721810687)], [(Int.ofNat 499552303611863254320), (Int.ofNat 2556688985652262380120), (Int.ofNat 20483946683323866864), (Int.negSucc 7996050366218316878975), (Int.ofNat 4854505886495938219824), (Int.negSucc 98050209775102100663), (Int.ofNat 4098855657886711920), (Int.negSucc 1059377927632510463)], [(Int.negSucc 944412378919285284719), (Int.negSucc 4374819384277514060807), (Int.negSucc 491143059218897624591), (Int.ofNat 9521774340046790863248), (Int.negSucc 1907019224579616843455), (Int.negSucc 1963549788866741607479), (Int.ofNat 186818918837765447376), (Int.negSucc 5771123052355114847), (Int.ofNat 5646215766597120)], [(Int.ofNat 1305369493930385471880), (Int.ofNat 5367626310580502637996), (Int.ofNat 1710859034911744721340), (Int.negSucc 5050625772997025285399), (Int.negSucc 7128171951583152800879), (Int.ofNat 4894693770744273004668), (Int.negSucc 288785941273073145491), (Int.ofNat 8054917049669681376), (Int.negSucc 184489567971523775)], [(Int.negSucc 1350216278286600878999), (Int.negSucc 4963248570949440274763), (Int.negSucc 3434265736475616832031), (Int.negSucc 2207813650180638445583), (Int.ofNat 13384729047293360891784), (Int.negSucc 3667398386674551576227), (Int.negSucc 527163848654449009967), (Int.ofNat 45621871116172520904), (Int.negSucc 1100543285437867583)], [(Int.ofNat 1053387952622797988520), (Int.ofNat 3628735100573579792676), (Int.ofNat 4647662558531982693540), (Int.ofNat 6021040103052229844064), (Int.negSucc 8908221473004074442839), (Int.negSucc 2778000632238217932539), (Int.ofNat 1719370258784284651164), (Int.negSucc 65237917449639350879), (Int.negSucc 36434295356870591)], [(Int.negSucc 618142829956876965959), (Int.negSucc 2192569357317362586539), (Int.negSucc 4523916163195690911863), (Int.negSucc 5116452319994144528663), (Int.negSucc 720714741143388330311), (Int.ofNat 6987307784598008385156), (Int.negSucc 1173819068327166696215), (Int.negSucc 105048505515632596919), (Int.ofNat 5929470806725108368)], [(Int.ofNat 269525632232979173160), (Int.ofNat 1119506647292339285988), (Int.ofNat 3275454230759704095216), (Int.ofNat 2868065185200892789248), (Int.ofNat 5314541479178282856108), (Int.negSucc 4234115617790071013135), (Int.negSucc 870165304696989119051), (Int.ofNat 245480973253918508952), (Int.ofNat 223798119038857116)], [(Int.negSucc 85303090138795153559), (Int.negSucc 475117778494681376147), (Int.negSucc 1786605765325648876979), (Int.negSucc 1559974274035335272699), (Int.negSucc 3853227979460759833871), (Int.negSucc 516148227726654383999), (Int.ofNat 1647166888765631606940), (Int.negSucc 66544308256904853371), (Int.negSucc 13105714357581421751)], [(Int.ofNat 18826083849237598440), (Int.ofNat 159738574482855049284), (Int.ofNat 729914059554247151604), (Int.ofNat 966198987244099901592), (Int.ofNat 1362444234218575730712), (Int.ofNat 2011904997378135249168), (Int.negSucc 635934176830854990359), (Int.negSucc 166265020714553425079), (Int.ofNat 5707917689379457464)], [(Int.negSucc 2700550621452832199), (Int.negSucc 40028351911312053995), (Int.negSucc 218394485116840542671), (Int.negSucc 519429558091345596071), (Int.negSucc 307420083131027511887), (Int.negSucc 1103649580388489543207), (Int.negSucc 279633515146622276687), (Int.ofNat 136939089910036620024), (Int.ofNat 9100326351811949640)], [(Int.ofNat 219564033226684560), (Int.ofNat 6959843848085113584), (Int.ofNat 46057451524879985820), (Int.ofNat 195102359451091038888), (Int.ofNat 109570231150057751724), (Int.ofNat 259219842316915948848), (Int.ofNat 333447207331961667456), (Int.negSucc 2684262863473978895), (Int.negSucc 7661492625746705327)], [(Int.negSucc 7176141063162719), (Int.negSucc 751577515433071271), (Int.negSucc 6456147712097366051), (Int.negSucc 47019786516144915515), (Int.negSucc 57785499449432813879), (Int.negSucc 19262427254320537151), (Int.negSucc 116024016561426087119), (Int.negSucc 37842601014197821295), (Int.negSucc 286676247115462751)], [(Int.ofNat 0), (Int.ofNat 38433798643918464), (Int.ofNat 543640049513288208), (Int.ofNat 6732404217907389720), (Int.ofNat 19085433356713642776), (Int.ofNat 416323053340400304), (Int.ofNat 15072299097300930096), (Int.ofNat 17684978238728063424), (Int.ofNat 2159992330670306592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 21359527178827679), (Int.negSucc 481936881283579943), (Int.negSucc 3325379244003778103), (Int.negSucc 1520880276973334255), (Int.ofNat 634497833777506560), (Int.negSucc 3187092243146261471), (Int.negSucc 804024851795954783)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8988388944393600), (Int.ofNat 258377503429981152), (Int.ofNat 480324751875724032), (Int.negSucc 359052898586065631), (Int.ofNat 195398866664630784), (Int.ofNat 93668811578288640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2888499693234815), (Int.negSucc 46467456705806111), (Int.ofNat 30257812802141280)]]

theorem h0n29_arithmetic_row0 :
    (BiPoly.mul h0p28 h0p9).getD 0 []=h0p29.getD 0 [] := by
  decide +kernel

theorem h0n29_arithmetic_row1 :
    (BiPoly.mul h0p28 h0p9).getD 1 []=h0p29.getD 1 [] := by
  decide +kernel

theorem h0n29_arithmetic_row2 :
    (BiPoly.mul h0p28 h0p9).getD 2 []=h0p29.getD 2 [] := by
  decide +kernel

theorem h0n29_arithmetic_row3 :
    (BiPoly.mul h0p28 h0p9).getD 3 []=h0p29.getD 3 [] := by
  decide +kernel

theorem h0n29_arithmetic_row4 :
    (BiPoly.mul h0p28 h0p9).getD 4 []=h0p29.getD 4 [] := by
  decide +kernel

theorem h0n29_arithmetic_row5 :
    (BiPoly.mul h0p28 h0p9).getD 5 []=h0p29.getD 5 [] := by
  decide +kernel

theorem h0n29_arithmetic_row6 :
    (BiPoly.mul h0p28 h0p9).getD 6 []=h0p29.getD 6 [] := by
  decide +kernel

theorem h0n29_arithmetic_row7 :
    (BiPoly.mul h0p28 h0p9).getD 7 []=h0p29.getD 7 [] := by
  decide +kernel

theorem h0n29_arithmetic_row8 :
    (BiPoly.mul h0p28 h0p9).getD 8 []=h0p29.getD 8 [] := by
  decide +kernel

theorem h0n29_arithmetic_row9 :
    (BiPoly.mul h0p28 h0p9).getD 9 []=h0p29.getD 9 [] := by
  decide +kernel

theorem h0n29_arithmetic_row10 :
    (BiPoly.mul h0p28 h0p9).getD 10 []=h0p29.getD 10 [] := by
  decide +kernel

theorem h0n29_arithmetic_row11 :
    (BiPoly.mul h0p28 h0p9).getD 11 []=h0p29.getD 11 [] := by
  decide +kernel

theorem h0n29_arithmetic_row12 :
    (BiPoly.mul h0p28 h0p9).getD 12 []=h0p29.getD 12 [] := by
  decide +kernel

theorem h0n29_arithmetic_row13 :
    (BiPoly.mul h0p28 h0p9).getD 13 []=h0p29.getD 13 [] := by
  decide +kernel

theorem h0n29_arithmetic_row14 :
    (BiPoly.mul h0p28 h0p9).getD 14 []=h0p29.getD 14 [] := by
  decide +kernel

theorem h0n29_arithmetic_row15 :
    (BiPoly.mul h0p28 h0p9).getD 15 []=h0p29.getD 15 [] := by
  decide +kernel

theorem h0n29_arithmetic_row16 :
    (BiPoly.mul h0p28 h0p9).getD 16 []=h0p29.getD 16 [] := by
  decide +kernel

theorem h0n29_arithmetic_row17 :
    (BiPoly.mul h0p28 h0p9).getD 17 []=h0p29.getD 17 [] := by
  decide +kernel

theorem h0n29_arithmetic_row18 :
    (BiPoly.mul h0p28 h0p9).getD 18 []=h0p29.getD 18 [] := by
  decide +kernel

theorem h0n29_arithmetic : BiPoly.mul h0p28 h0p9=h0p29 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p28 h0p9).getD j.val []=h0p29.getD j.val [] :=
      (fun j => Fin.cases h0n29_arithmetic_row0 (fun j => Fin.cases h0n29_arithmetic_row1 (fun j => Fin.cases h0n29_arithmetic_row2 (fun j => Fin.cases h0n29_arithmetic_row3 (fun j => Fin.cases h0n29_arithmetic_row4 (fun j => Fin.cases h0n29_arithmetic_row5 (fun j => Fin.cases h0n29_arithmetic_row6 (fun j => Fin.cases h0n29_arithmetic_row7 (fun j => Fin.cases h0n29_arithmetic_row8 (fun j => Fin.cases h0n29_arithmetic_row9 (fun j => Fin.cases h0n29_arithmetic_row10 (fun j => Fin.cases h0n29_arithmetic_row11 (fun j => Fin.cases h0n29_arithmetic_row12 (fun j => Fin.cases h0n29_arithmetic_row13 (fun j => Fin.cases h0n29_arithmetic_row14 (fun j => Fin.cases h0n29_arithmetic_row15 (fun j => Fin.cases h0n29_arithmetic_row16 (fun j => Fin.cases h0n29_arithmetic_row17 (fun j => Fin.cases h0n29_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n29 : h0e29.toBi mapPolyEnv=h0p29 := by
  change BiPoly.mul (h0e28.toBi mapPolyEnv) (h0e9.toBi mapPolyEnv)=h0p29
  rw [h0n28, h0n9]
  exact h0n29_arithmetic

#print axioms h0n29_arithmetic
end StackSorting.RationalLift
