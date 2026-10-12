import BivariateRowEquality
import Horner4Base
import Horner4Node082
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p83 : BiPoly.Poly := [[(Int.ofNat 3469171580208000000), (Int.ofNat 17661612674554992000), (Int.negSucc 13934347043686937279), (Int.negSucc 87817347288711590399), (Int.ofNat 123066229874873823360), (Int.ofNat 18693870585647460480), (Int.negSucc 56607621254219851199)], [(Int.negSucc 30189502017987839999), (Int.negSucc 144386168496138478079), (Int.ofNat 156365000984874824064), (Int.ofNat 748052761129264058688), (Int.negSucc 1099721951436057247295), (Int.negSucc 102458350649877113663), (Int.ofNat 479198161560392565696), (Int.negSucc 41006057296895827199)], [(Int.ofNat 119003960657575180800), (Int.ofNat 537623901698065290720), (Int.negSucc 677666938940533809647), (Int.negSucc 2791224930666604660847), (Int.ofNat 4049342836598693331360), (Int.ofNat 437420934005395893696), (Int.negSucc 1696979434840972871471), (Int.ofNat 183216720040161131088), (Int.negSucc 9614021433147873791)], [(Int.negSucc 280853612262774259199), (Int.negSucc 1206001634619228703199), (Int.ofNat 1540377169494350740272), (Int.ofNat 6060939455143221455664), (Int.negSucc 7571316486720090569183), (Int.negSucc 2043322422584158052063), (Int.ofNat 3161086003628152397136), (Int.negSucc 60716457986822707247), (Int.ofNat 2026318486836134304), (Int.negSucc 706251951755006975)], [(Int.ofNat 441804470038387473600), (Int.ofNat 1813876663930865275680), (Int.negSucc 1957587176424302246303), (Int.negSucc 8489559784779050238863), (Int.ofNat 6253032186874840907232), (Int.ofNat 6375356865913991478048), (Int.negSucc 2743276141845433905695), (Int.negSucc 1178278383184785947375), (Int.ofNat 120800360614258728864), (Int.negSucc 3843651224392345151), (Int.ofNat 3764143844398080)], [(Int.negSucc 487882840234122604799), (Int.negSucc 1921754897812022798159), (Int.ofNat 1151770613930491277880), (Int.ofNat 7870283762762552722416), (Int.ofNat 2430672556264311649176), (Int.negSucc 11096324675747760693743), (Int.negSucc 1215130164290809717175), (Int.ofNat 3050570748398366973744), (Int.negSucc 186418721651639622263), (Int.ofNat 5246951654465438400), (Int.negSucc 122993045314349183)], [(Int.ofNat 387747238389802790400), (Int.ofNat 1460763866202494861040), (Int.ofNat 371300837276092400808), (Int.negSucc 4505942607799214873639), (Int.negSucc 11541582293315958313919), (Int.ofNat 9302733240332500192848), (Int.ofNat 6901558489363343839608), (Int.negSucc 2842906182962021017559), (Int.negSucc 320339402799400166447), (Int.ofNat 29680885220489768880), (Int.negSucc 733695523625245055)], [(Int.negSucc 223459414927563513599), (Int.negSucc 790435545175032973199), (Int.negSucc 1293487583890355554871), (Int.ofNat 941046394472202456816), (Int.ofNat 12490099839242525519448), (Int.ofNat 319284607346945792304), (Int.negSucc 9207842028600610104887), (Int.negSucc 589623030587350920383), (Int.ofNat 1098073853022218795112), (Int.negSucc 43516234496664147647), (Int.negSucc 24289530237913727)], [(Int.ofNat 92694404140438339200), (Int.ofNat 290865563051858068560), (Int.ofNat 1136895952963402569576), (Int.ofNat 798748317168433413384), (Int.negSucc 6388900211607743035919), (Int.negSucc 8592287832193335858239), (Int.ofNat 5109239540458339255416), (Int.ofNat 3952374521740388999208), (Int.negSucc 858198859644836640431), (Int.negSucc 66079356472604992367), (Int.ofNat 3952980537816738912)], [(Int.negSucc 27000912551331705599), (Int.negSucc 62532315932251608719), (Int.negSucc 530062901117904945335), (Int.negSucc 802349327806288678535), (Int.ofNat 704086267658763691680), (Int.ofNat 8387638544862284046216), (Int.ofNat 1482719383116047840424), (Int.negSucc 3721373069935967586215), (Int.negSucc 401316871385389913591), (Int.ofNat 163803180915304910712), (Int.ofNat 149198746025904744)], [(Int.ofNat 5245468646277196800), (Int.ofNat 2068203449593382640), (Int.ofNat 118109846504890452984), (Int.ofNat 279395619529724784240), (Int.ofNat 1019679917019286856544), (Int.negSucc 3434351682072860687495), (Int.negSucc 4348144863255629505791), (Int.ofNat 909695928108094174824), (Int.ofNat 1062977708113177073856), (Int.negSucc 53100015076324183415), (Int.negSucc 8737142905054281167)], [(Int.negSucc 610683544966598399), (Int.ofNat 3047960020332699120), (Int.ofNat 7547945680837985544), (Int.ofNat 9945194989144831248), (Int.negSucc 548348919862840631351), (Int.ofNat 123850988008927846752), (Int.ofNat 2883784528395154024560), (Int.ofNat 1089560073195159291024), (Int.negSucc 562376737434180062111), (Int.negSucc 107038068683449311743), (Int.ofNat 3805278459586304976)], [(Int.ofNat 32252086057540800), (Int.negSucc 901966564627171439), (Int.negSucc 12811461420093366407), (Int.negSucc 47351461659322896839), (Int.ofNat 44343498955840394400), (Int.ofNat 446166872586945097392), (Int.negSucc 755375748358528172111), (Int.negSucc 1124517688778363789711), (Int.negSucc 90132373818159199631), (Int.ofNat 97359610841232379776), (Int.ofNat 6066884234541299760)], [(Int.ofNat 0), (Int.ofNat 109541665579271520), (Int.ofNat 3636986668792174080), (Int.ofNat 19269972938105809608), (Int.ofNat 55716533740127925144), (Int.negSucc 149753675858365902983), (Int.negSucc 64282707838932863831), (Int.ofNat 434128430585685985056), (Int.ofNat 235730985602352851232), (Int.negSucc 6897170326147122815), (Int.negSucc 5107661750497803551)], [(Int.ofNat 0), (Int.negSucc 4784094042108479), (Int.negSucc 479567199284844335), (Int.negSucc 3795406489480353479), (Int.negSucc 24144581944756765439), (Int.negSucc 1047908994014852279), (Int.ofNat 86490466506570755376), (Int.negSucc 49069731536730965087), (Int.negSucc 111293775013595007167), (Int.negSucc 25419518174208856031), (Int.negSucc 191117498076975167)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 25622532429278976), (Int.ofNat 373628040809645664), (Int.ofNat 4299340969623877488), (Int.ofNat 10556322456215178144), (Int.negSucc 16272596455842807503), (Int.negSucc 17336421473241766463), (Int.ofNat 20791495537260433056), (Int.ofNat 13229980379598913344), (Int.ofNat 1439994887113537728)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14239684785885119), (Int.negSucc 330509016206071919), (Int.negSucc 2323133111481084863), (Int.negSucc 485959091096116655), (Int.ofNat 6191035277165548128), (Int.ofNat 456873710866628544), (Int.negSucc 2660744729961477503), (Int.negSucc 536016567863969855)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5992259296262400), (Int.ofNat 176918825579252544), (Int.ofNat 433957493887219008), (Int.negSucc 565721013650370623), (Int.negSucc 757632857223051071), (Int.ofNat 192711785495279616), (Int.ofNat 62445874385525760)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1925666462156543), (Int.negSucc 32675724285923519), (Int.negSucc 3176691715294847), (Int.ofNat 83932828498854720)]]

theorem h4n83_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p82).getD 0 []=h4p83.getD 0 [] := by
  decide +kernel

theorem h4n83_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p82).getD 1 []=h4p83.getD 1 [] := by
  decide +kernel

theorem h4n83_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p82).getD 2 []=h4p83.getD 2 [] := by
  decide +kernel

theorem h4n83_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p82).getD 3 []=h4p83.getD 3 [] := by
  decide +kernel

theorem h4n83_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p82).getD 4 []=h4p83.getD 4 [] := by
  decide +kernel

theorem h4n83_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p82).getD 5 []=h4p83.getD 5 [] := by
  decide +kernel

theorem h4n83_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p82).getD 6 []=h4p83.getD 6 [] := by
  decide +kernel

theorem h4n83_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p82).getD 7 []=h4p83.getD 7 [] := by
  decide +kernel

theorem h4n83_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p82).getD 8 []=h4p83.getD 8 [] := by
  decide +kernel

theorem h4n83_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p82).getD 9 []=h4p83.getD 9 [] := by
  decide +kernel

theorem h4n83_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p82).getD 10 []=h4p83.getD 10 [] := by
  decide +kernel

theorem h4n83_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p82).getD 11 []=h4p83.getD 11 [] := by
  decide +kernel

theorem h4n83_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p82).getD 12 []=h4p83.getD 12 [] := by
  decide +kernel

theorem h4n83_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p82).getD 13 []=h4p83.getD 13 [] := by
  decide +kernel

theorem h4n83_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p82).getD 14 []=h4p83.getD 14 [] := by
  decide +kernel

theorem h4n83_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p82).getD 15 []=h4p83.getD 15 [] := by
  decide +kernel

theorem h4n83_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p82).getD 16 []=h4p83.getD 16 [] := by
  decide +kernel

theorem h4n83_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p82).getD 17 []=h4p83.getD 17 [] := by
  decide +kernel

theorem h4n83_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p82).getD 18 []=h4p83.getD 18 [] := by
  decide +kernel

theorem h4n83_arithmetic : BiPoly.mul h4p13 h4p82=h4p83 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p82).getD j.val []=h4p83.getD j.val [] :=
      (fun j => Fin.cases h4n83_arithmetic_row0 (fun j => Fin.cases h4n83_arithmetic_row1 (fun j => Fin.cases h4n83_arithmetic_row2 (fun j => Fin.cases h4n83_arithmetic_row3 (fun j => Fin.cases h4n83_arithmetic_row4 (fun j => Fin.cases h4n83_arithmetic_row5 (fun j => Fin.cases h4n83_arithmetic_row6 (fun j => Fin.cases h4n83_arithmetic_row7 (fun j => Fin.cases h4n83_arithmetic_row8 (fun j => Fin.cases h4n83_arithmetic_row9 (fun j => Fin.cases h4n83_arithmetic_row10 (fun j => Fin.cases h4n83_arithmetic_row11 (fun j => Fin.cases h4n83_arithmetic_row12 (fun j => Fin.cases h4n83_arithmetic_row13 (fun j => Fin.cases h4n83_arithmetic_row14 (fun j => Fin.cases h4n83_arithmetic_row15 (fun j => Fin.cases h4n83_arithmetic_row16 (fun j => Fin.cases h4n83_arithmetic_row17 (fun j => Fin.cases h4n83_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n83 : h4e83.toBi mapPolyEnv=h4p83 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e82.toBi mapPolyEnv)=h4p83
  rw [h4n13, h4n82]
  exact h4n83_arithmetic

#print axioms h4n83_arithmetic
end StackSorting.RationalLift
