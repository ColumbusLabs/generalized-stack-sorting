import BivariateRowEquality
import Horner0Base
import Horner0Node049
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p50 : BiPoly.Poly := [[(Int.negSucc 761773595079491999), (Int.negSucc 5760282302456213519), (Int.negSucc 7652723483248531919), (Int.ofNat 20466866442658682160), (Int.ofNat 23498840606378693040), (Int.negSucc 28303810627109925599)], [(Int.ofNat 7034670758927710080), (Int.ofNat 53576340051168837216), (Int.ofNat 74883953280418368048), (Int.negSucc 173946272443598995487), (Int.negSucc 201321315028042028495), (Int.ofNat 249850595104420239648), (Int.negSucc 20503028648447913599)], [(Int.negSucc 30622684866584200199), (Int.negSucc 228642112447938713699), (Int.negSucc 326512889291915557775), (Int.ofNat 649909508053947734304), (Int.ofNat 790922588100735082752), (Int.negSucc 903340401544992969899), (Int.ofNat 94011865378367533992), (Int.negSucc 4807010716573936895)], [(Int.ofNat 83258717268643875720), (Int.ofNat 592632265479331481460), (Int.ofNat 855643652997974771184), (Int.negSucc 1325847078808611524207), (Int.negSucc 1856265807656782589687), (Int.ofNat 1601826927202795723164), (Int.negSucc 32000260648719581567), (Int.ofNat 1189722231356818896), (Int.negSucc 353125975877503487)], [(Int.negSucc 157402063153214214119), (Int.negSucc 1043940690352680771707), (Int.negSucc 1540130304628987624367), (Int.ofNat 1423248036934832602344), (Int.ofNat 2856088242585660813840), (Int.negSucc 962931373004329215731), (Int.negSucc 623380109815952961263), (Int.ofNat 61311119103862629984), (Int.negSucc 1922766648157272095), (Int.ofNat 1882071922199040)], [(Int.ofNat 217561582321730911980), (Int.ofNat 1329727549740212263626), (Int.ofNat 2074351942678791666222), (Int.negSucc 271484617195589307119), (Int.negSucc 2871570582929533895279), (Int.negSucc 1560275022070338766181), (Int.ofNat 1583433600035912143974), (Int.negSucc 94919494249412768267), (Int.ofNat 2654224088561306496), (Int.negSucc 61496522657174591)], [(Int.negSucc 225036046381100146499), (Int.negSucc 1277280187920440338793), (Int.negSucc 2226793813062416230259), (Int.negSucc 1512724187188645351607), (Int.ofNat 1494850291155347333436), (Int.ofNat 3850343284652028367890), (Int.negSucc 1310326770333925360403), (Int.negSucc 168117637698787583171), (Int.ofNat 15023866491151195704), (Int.negSucc 366847761812622527)], [(Int.ofNat 175564658770466331420), (Int.ofNat 955918500969862628286), (Int.ofNat 1984188793279857046482), (Int.ofNat 2552727536686032538524), (Int.ofNat 522309788850064207548), (Int.negSucc 3432407263041061136369), (Int.negSucc 639438500948691868985), (Int.ofNat 562250433353154991908), (Int.negSucc 21752044865772595391), (Int.negSucc 12144765118956863)], [(Int.negSucc 103023804992812827659), (Int.negSucc 571475836205186086409), (Int.negSucc 1484842479638402680823), (Int.negSucc 2360714107730921058731), (Int.negSucc 1825603230188612897939), (Int.ofNat 924313050385205287422), (Int.ofNat 2133466083478141679016), (Int.negSucc 408781107028327664891), (Int.negSucc 34027923370756680911), (Int.ofNat 1976490268908369456)], [(Int.ofNat 44920938705496528860), (Int.ofNat 276426318626382938718), (Int.ofNat 919077920890730444532), (Int.ofNat 1569828941120050163280), (Int.ofNat 1841778641596678072434), (Int.ofNat 1065827890094415783180), (Int.negSucc 1556399423379521857553), (Int.negSucc 249141606023343288191), (Int.ofNat 81864290771145979170), (Int.ofNat 74599373012952372)], [(Int.negSucc 14217181689799192259), (Int.negSucc 107620659795378613877), (Int.negSucc 456140220385835271545), (Int.negSucc 855530967447772171109), (Int.negSucc 1162196087921905063211), (Int.negSucc 1370434031108029008623), (Int.ofNat 102478405552053806490), (Int.ofNat 537964911545726393418), (Int.negSucc 24365721811898521415), (Int.negSucc 4368571452527140583)], [(Int.ofNat 3137680641539599740), (Int.ofNat 32898457030221707694), (Int.ofNat 174898534753326208362), (Int.ofNat 404337851058765700800), (Int.ofNat 549140368117795922316), (Int.ofNat 789465577635881118432), (Int.ofNat 564645969654235917996), (Int.negSucc 239688895729377234299), (Int.negSucc 54470353956621232115), (Int.ofNat 1902639229793152488)], [(Int.negSucc 450091770242138699), (Int.negSucc 7571575525702953065), (Int.negSucc 49741864823244108443), (Int.negSucc 159369754720837780235), (Int.negSucc 224379866552286450671), (Int.negSucc 286414957775090761163), (Int.negSucc 414488779320600227183), (Int.negSucc 70387990063867988891), (Int.ofNat 47163084361980864948), (Int.ofNat 3033442117270649880)], [(Int.ofNat 36594005537780760), (Int.ofNat 1233161985756413784), (Int.ofNat 9996189870175035498), (Int.ofNat 47869543750141835088), (Int.ofNat 83295825008706638250), (Int.ofNat 79726717436171908716), (Int.ofNat 141981148660965594192), (Int.ofNat 110701691966741559336), (Int.negSucc 2171669725449110519), (Int.negSucc 2553830875248901775)], [(Int.negSucc 1196023510527119), (Int.negSucc 127654966259899451), (Int.negSucc 1326550457160584765), (Int.negSucc 9988680323389941269), (Int.negSucc 25304178746953774151), (Int.negSucc 22472237692197694151), (Int.negSucc 25758145178344526903), (Int.negSucc 44981772356174999255), (Int.negSucc 12661979712585184223), (Int.negSucc 95558749038487583)], [(Int.ofNat 0), (Int.ofNat 6405633107319744), (Int.ofNat 103417941133520856), (Int.ofNat 1303280719488994356), (Int.ofNat 5425040298754737036), (Int.ofNat 6431198294461280976), (Int.ofNat 2650824200663621784), (Int.ofNat 7971596072221653936), (Int.ofNat 6254991468021072240), (Int.ofNat 719997443556768864)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3559921196471279), (Int.negSucc 87442655940205883), (Int.negSucc 714875501095156331), (Int.negSucc 1361939794163481743), (Int.negSucc 401210453361526991), (Int.negSucc 319682762598541391), (Int.negSucc 1196368223014746287), (Int.negSucc 268008283931984927)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1498064824065600), (Int.ofNat 46059046886461392), (Int.ofNat 166179959789281056), (Int.ofNat 100266100860897072), (Int.negSucc 87117821751250079), (Int.ofNat 80744424151258368), (Int.ofNat 31222937192762880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 481416615539135), (Int.negSucc 8707409348712623), (Int.negSucc 10446183434911823), (Int.ofNat 10085937600713760)]]

theorem h0n50_arithmetic_row0 :
    (BiPoly.mul h0p7 h0p49).getD 0 []=h0p50.getD 0 [] := by
  decide +kernel

theorem h0n50_arithmetic_row1 :
    (BiPoly.mul h0p7 h0p49).getD 1 []=h0p50.getD 1 [] := by
  decide +kernel

theorem h0n50_arithmetic_row2 :
    (BiPoly.mul h0p7 h0p49).getD 2 []=h0p50.getD 2 [] := by
  decide +kernel

theorem h0n50_arithmetic_row3 :
    (BiPoly.mul h0p7 h0p49).getD 3 []=h0p50.getD 3 [] := by
  decide +kernel

theorem h0n50_arithmetic_row4 :
    (BiPoly.mul h0p7 h0p49).getD 4 []=h0p50.getD 4 [] := by
  decide +kernel

theorem h0n50_arithmetic_row5 :
    (BiPoly.mul h0p7 h0p49).getD 5 []=h0p50.getD 5 [] := by
  decide +kernel

theorem h0n50_arithmetic_row6 :
    (BiPoly.mul h0p7 h0p49).getD 6 []=h0p50.getD 6 [] := by
  decide +kernel

theorem h0n50_arithmetic_row7 :
    (BiPoly.mul h0p7 h0p49).getD 7 []=h0p50.getD 7 [] := by
  decide +kernel

theorem h0n50_arithmetic_row8 :
    (BiPoly.mul h0p7 h0p49).getD 8 []=h0p50.getD 8 [] := by
  decide +kernel

theorem h0n50_arithmetic_row9 :
    (BiPoly.mul h0p7 h0p49).getD 9 []=h0p50.getD 9 [] := by
  decide +kernel

theorem h0n50_arithmetic_row10 :
    (BiPoly.mul h0p7 h0p49).getD 10 []=h0p50.getD 10 [] := by
  decide +kernel

theorem h0n50_arithmetic_row11 :
    (BiPoly.mul h0p7 h0p49).getD 11 []=h0p50.getD 11 [] := by
  decide +kernel

theorem h0n50_arithmetic_row12 :
    (BiPoly.mul h0p7 h0p49).getD 12 []=h0p50.getD 12 [] := by
  decide +kernel

theorem h0n50_arithmetic_row13 :
    (BiPoly.mul h0p7 h0p49).getD 13 []=h0p50.getD 13 [] := by
  decide +kernel

theorem h0n50_arithmetic_row14 :
    (BiPoly.mul h0p7 h0p49).getD 14 []=h0p50.getD 14 [] := by
  decide +kernel

theorem h0n50_arithmetic_row15 :
    (BiPoly.mul h0p7 h0p49).getD 15 []=h0p50.getD 15 [] := by
  decide +kernel

theorem h0n50_arithmetic_row16 :
    (BiPoly.mul h0p7 h0p49).getD 16 []=h0p50.getD 16 [] := by
  decide +kernel

theorem h0n50_arithmetic_row17 :
    (BiPoly.mul h0p7 h0p49).getD 17 []=h0p50.getD 17 [] := by
  decide +kernel

theorem h0n50_arithmetic_row18 :
    (BiPoly.mul h0p7 h0p49).getD 18 []=h0p50.getD 18 [] := by
  decide +kernel

theorem h0n50_arithmetic : BiPoly.mul h0p7 h0p49=h0p50 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p7 h0p49).getD j.val []=h0p50.getD j.val [] :=
      (fun j => Fin.cases h0n50_arithmetic_row0 (fun j => Fin.cases h0n50_arithmetic_row1 (fun j => Fin.cases h0n50_arithmetic_row2 (fun j => Fin.cases h0n50_arithmetic_row3 (fun j => Fin.cases h0n50_arithmetic_row4 (fun j => Fin.cases h0n50_arithmetic_row5 (fun j => Fin.cases h0n50_arithmetic_row6 (fun j => Fin.cases h0n50_arithmetic_row7 (fun j => Fin.cases h0n50_arithmetic_row8 (fun j => Fin.cases h0n50_arithmetic_row9 (fun j => Fin.cases h0n50_arithmetic_row10 (fun j => Fin.cases h0n50_arithmetic_row11 (fun j => Fin.cases h0n50_arithmetic_row12 (fun j => Fin.cases h0n50_arithmetic_row13 (fun j => Fin.cases h0n50_arithmetic_row14 (fun j => Fin.cases h0n50_arithmetic_row15 (fun j => Fin.cases h0n50_arithmetic_row16 (fun j => Fin.cases h0n50_arithmetic_row17 (fun j => Fin.cases h0n50_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n50 : h0e50.toBi mapPolyEnv=h0p50 := by
  change BiPoly.mul (h0e7.toBi mapPolyEnv) (h0e49.toBi mapPolyEnv)=h0p50
  rw [h0n7, h0n49]
  exact h0n50_arithmetic

#print axioms h0n50_arithmetic
end StackSorting.RationalLift
