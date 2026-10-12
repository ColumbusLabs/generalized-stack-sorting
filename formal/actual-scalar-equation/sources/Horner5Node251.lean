import BivariateRowEquality
import Horner5Base
import Horner5Node250
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p251 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2787322751999), (Int.negSucc 15461770173119), (Int.ofNat 2250904839840), (Int.ofNat 84075558685920), (Int.ofNat 4898813165280), (Int.negSucc 64251393259679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 23945038080480), (Int.ofNat 114410836377936), (Int.negSucc 84576848129279), (Int.negSucc 653316873815231), (Int.ofNat 123322493133792), (Int.ofNat 443266043985072), (Int.negSucc 49741553782655)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 92408911261919), (Int.negSucc 372638167697663), (Int.ofNat 509367242274120), (Int.ofNat 2160109510416720), (Int.negSucc 697604822135711), (Int.negSucc 1170570224511791), (Int.ofNat 117238814878680), (Int.negSucc 13274272804607)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 211264450513560), (Int.ofNat 698966236092708), (Int.negSucc 1440622514177027), (Int.negSucc 4086349245583271), (Int.ofNat 1044138311173440), (Int.ofNat 1699463605397076), (Int.ofNat 371623435877772), (Int.negSucc 38383922891087), (Int.negSucc 1369615412735)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 317578736443679), (Int.negSucc 825855105902903), (Int.ofNat 2398408420217148), (Int.ofNat 5136798967705440), (Int.ofNat 796972210139016), (Int.negSucc 1925450682738551), (Int.negSucc 1614277484951507), (Int.ofNat 212477430521952), (Int.negSucc 13545176428511), (Int.negSucc 39795245567)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 329228204203440), (Int.ofNat 624200197878072), (Int.negSucc 2589773572410515), (Int.negSucc 4985016561195911), (Int.negSucc 4661403693435503), (Int.ofNat 1807335408447216), (Int.ofNat 2203811332677972), (Int.ofNat 49153136296176), (Int.negSucc 3454658001935), (Int.negSucc 919683999935)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 239910160016159), (Int.negSucc 280401058997423), (Int.ofNat 1929031590591072), (Int.ofNat 4385339419543308), (Int.ofNat 7039374596562096), (Int.negSucc 602696965463), (Int.negSucc 1454086044828287), (Int.negSucc 926926890366563), (Int.ofNat 104812858589256), (Int.negSucc 3631965766847)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 122753306869920), (Int.ofNat 44723575543680), (Int.negSucc 1064076607100339), (Int.negSucc 3652807934485439), (Int.negSucc 6044321961252035), (Int.negSucc 3241367873681507), (Int.ofNat 468540136734336), (Int.ofNat 1155069905883336), (Int.negSucc 20830315847795), (Int.ofNat 1240497911376)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 43176934193759), (Int.ofNat 27509233217472), (Int.ofNat 485133896747304), (Int.ofNat 2598531698183580), (Int.ofNat 3689991924302304), (Int.ofNat 4748398649809416), (Int.ofNat 500426162172684), (Int.negSucc 382348587551723), (Int.negSucc 269101052410247), (Int.ofNat 18128444194944)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 9935192576880), (Int.negSucc 21154775868935), (Int.negSucc 201219194585555), (Int.negSucc 1420801698799655), (Int.negSucc 2046727480500863), (Int.negSucc 3387380711137919), (Int.negSucc 1486775171595023), (Int.negSucc 212751592225055), (Int.ofNat 259288825261608), (Int.negSucc 2042670293855)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1345313370239), (Int.ofNat 6741745365168), (Int.ofNat 72210492220248), (Int.ofNat 563705693072316), (Int.ofNat 1146652689835944), (Int.ofNat 1430786677716792), (Int.ofNat 1579449411968400), (Int.ofNat 328621690010808), (Int.ofNat 3710419937064), (Int.negSucc 32328492725663)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 81185793480), (Int.negSucc 1120563588131), (Int.negSucc 18896460936119), (Int.negSucc 155353490249831), (Int.negSucc 536100639464339), (Int.negSucc 467619233017391), (Int.negSucc 824171633738495), (Int.negSucc 328959140093855), (Int.negSucc 97536763024847), (Int.ofNat 17234339746176)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 79617753144), (Int.ofNat 2965936999932), (Int.ofNat 27769979477124), (Int.ofNat 169232898344328), (Int.ofNat 182613239553168), (Int.ofNat 212563602072576), (Int.ofNat 221521700669616), (Int.ofNat 53453869969248), (Int.ofNat 8891189347968)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 203286550823), (Int.negSucc 2795282426303), (Int.negSucc 31021674310583), (Int.negSucc 67950473154623), (Int.negSucc 30518808578063), (Int.negSucc 72636445753631), (Int.negSucc 23078137858847), (Int.negSucc 7962323224319)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 110259471240), (Int.ofNat 2643848260056), (Int.ofNat 14581607808528), (Int.ofNat 7999202848320), (Int.ofNat 7800971169888), (Int.ofNat 8826479707680), (Int.ofNat 1417043030400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 47513817215), (Int.negSucc 1267887740831), (Int.negSucc 2354506307423), (Int.ofNat 340330092480), (Int.negSucc 1417043030399)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 12717422496), (Int.ofNat 212556454560)]]

theorem h5n251_arithmetic_row0 :
    (BiPoly.mul h5p34 h5p250).getD 0 []=h5p251.getD 0 [] := by
  decide +kernel

theorem h5n251_arithmetic_row1 :
    (BiPoly.mul h5p34 h5p250).getD 1 []=h5p251.getD 1 [] := by
  decide +kernel

theorem h5n251_arithmetic_row2 :
    (BiPoly.mul h5p34 h5p250).getD 2 []=h5p251.getD 2 [] := by
  decide +kernel

theorem h5n251_arithmetic_row3 :
    (BiPoly.mul h5p34 h5p250).getD 3 []=h5p251.getD 3 [] := by
  decide +kernel

theorem h5n251_arithmetic_row4 :
    (BiPoly.mul h5p34 h5p250).getD 4 []=h5p251.getD 4 [] := by
  decide +kernel

theorem h5n251_arithmetic_row5 :
    (BiPoly.mul h5p34 h5p250).getD 5 []=h5p251.getD 5 [] := by
  decide +kernel

theorem h5n251_arithmetic_row6 :
    (BiPoly.mul h5p34 h5p250).getD 6 []=h5p251.getD 6 [] := by
  decide +kernel

theorem h5n251_arithmetic_row7 :
    (BiPoly.mul h5p34 h5p250).getD 7 []=h5p251.getD 7 [] := by
  decide +kernel

theorem h5n251_arithmetic_row8 :
    (BiPoly.mul h5p34 h5p250).getD 8 []=h5p251.getD 8 [] := by
  decide +kernel

theorem h5n251_arithmetic_row9 :
    (BiPoly.mul h5p34 h5p250).getD 9 []=h5p251.getD 9 [] := by
  decide +kernel

theorem h5n251_arithmetic_row10 :
    (BiPoly.mul h5p34 h5p250).getD 10 []=h5p251.getD 10 [] := by
  decide +kernel

theorem h5n251_arithmetic_row11 :
    (BiPoly.mul h5p34 h5p250).getD 11 []=h5p251.getD 11 [] := by
  decide +kernel

theorem h5n251_arithmetic_row12 :
    (BiPoly.mul h5p34 h5p250).getD 12 []=h5p251.getD 12 [] := by
  decide +kernel

theorem h5n251_arithmetic_row13 :
    (BiPoly.mul h5p34 h5p250).getD 13 []=h5p251.getD 13 [] := by
  decide +kernel

theorem h5n251_arithmetic_row14 :
    (BiPoly.mul h5p34 h5p250).getD 14 []=h5p251.getD 14 [] := by
  decide +kernel

theorem h5n251_arithmetic_row15 :
    (BiPoly.mul h5p34 h5p250).getD 15 []=h5p251.getD 15 [] := by
  decide +kernel

theorem h5n251_arithmetic_row16 :
    (BiPoly.mul h5p34 h5p250).getD 16 []=h5p251.getD 16 [] := by
  decide +kernel

theorem h5n251_arithmetic : BiPoly.mul h5p34 h5p250=h5p251 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<17 at hk
    have hf : ∀ j : Fin 17, (BiPoly.mul h5p34 h5p250).getD j.val []=h5p251.getD j.val [] :=
      (fun j => Fin.cases h5n251_arithmetic_row0 (fun j => Fin.cases h5n251_arithmetic_row1 (fun j => Fin.cases h5n251_arithmetic_row2 (fun j => Fin.cases h5n251_arithmetic_row3 (fun j => Fin.cases h5n251_arithmetic_row4 (fun j => Fin.cases h5n251_arithmetic_row5 (fun j => Fin.cases h5n251_arithmetic_row6 (fun j => Fin.cases h5n251_arithmetic_row7 (fun j => Fin.cases h5n251_arithmetic_row8 (fun j => Fin.cases h5n251_arithmetic_row9 (fun j => Fin.cases h5n251_arithmetic_row10 (fun j => Fin.cases h5n251_arithmetic_row11 (fun j => Fin.cases h5n251_arithmetic_row12 (fun j => Fin.cases h5n251_arithmetic_row13 (fun j => Fin.cases h5n251_arithmetic_row14 (fun j => Fin.cases h5n251_arithmetic_row15 (fun j => Fin.cases h5n251_arithmetic_row16 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n251 : h5e251.toBi mapPolyEnv=h5p251 := by
  change BiPoly.mul (h5e34.toBi mapPolyEnv) (h5e250.toBi mapPolyEnv)=h5p251
  rw [h5n34, h5n250]
  exact h5n251_arithmetic

#print axioms h5n251_arithmetic
end StackSorting.RationalLift
