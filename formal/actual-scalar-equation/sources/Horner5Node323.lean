import BivariateRowEquality
import Horner5Base
import Horner5Node322
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p323 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 53347970628407808), (Int.ofNat 532384730679488832), (Int.negSucc 1415623196082969791), (Int.negSucc 9799358925094828415), (Int.ofNat 7039601037248376960), (Int.ofNat 16450214517578170944), (Int.negSucc 4710535084359907775), (Int.negSucc 6216449595728924159)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 516873281803103231), (Int.negSucc 4913096820547832351), (Int.ofNat 14628332239887453120), (Int.ofNat 93812812569798041952), (Int.negSucc 72803159134356624767), (Int.negSucc 124932920620749878879), (Int.ofNat 47183948420845466304), (Int.ofNat 33902604787108903200), (Int.negSucc 3429134451479225087)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 2342209289899556736), (Int.ofNat 20693087395689008160), (Int.negSucc 73364028284702144447), (Int.negSucc 399662684825820001055), (Int.ofNat 326835421012305379584), (Int.ofNat 407744544976173799776), (Int.negSucc 166026170685101267519), (Int.negSucc 70454810867537667167), (Int.ofNat 6998813467973774208), (Int.negSucc 464233567039165439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6572842007273872319), (Int.negSucc 52197517320402034271), (Int.ofNat 231860027651483890656), (Int.ofNat 986128923882069268416), (Int.negSucc 787021317867243718943), (Int.negSucc 740860967494005807455), (Int.ofNat 219038837635116462624), (Int.ofNat 71808453715039246464), (Int.ofNat 15207392832765893856), (Int.negSucc 1077271165679532671), (Int.ofNat 2399849982182400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 12703115677378137792), (Int.ofNat 86827057146610440720), (Int.negSucc 503477070326775667439), (Int.negSucc 1546970219250564734543), (Int.ofNat 979889446454332085904), (Int.ofNat 862720833790982921328), (Int.ofNat 112833881373903639024), (Int.negSucc 66808355611329998639), (Int.negSucc 58849502386864256783), (Int.ofNat 3919882640313561408), (Int.negSucc 82838951492421119)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17729762215467053567), (Int.negSucc 98445893415483453647), (Int.ofNat 777774472403029390176), (Int.ofNat 1613575899213895866288), (Int.negSucc 250831767319384419935), (Int.negSucc 794456029929211445999), (Int.negSucc 708656790710588939423), (Int.ofNat 82988445555128797104), (Int.ofNat 53358136177628703072), (Int.ofNat 2637119171415779040), (Int.negSucc 305075589585319679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 18173866454664842016), (Int.ofNat 75006477282505262016), (Int.negSucc 866462400112625343023), (Int.negSucc 1185248864691024712991), (Int.negSucc 1097989634299376411135), (Int.ofNat 645831114962602199088), (Int.ofNat 885896866547934856848), (Int.ofNat 28272990496255691232), (Int.ofNat 4042201511753587392), (Int.negSucc 14490558274258301423), (Int.ofNat 200848107105976704)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 13600645677423158303), (Int.negSucc 34480087705917908927), (Int.ofNat 696849967790215309872), (Int.ofNat 740788504732375542480), (Int.ofNat 1829696812434848002896), (Int.negSucc 188860396700334494591), (Int.negSucc 469248852449645956559), (Int.negSucc 259213335160412056559), (Int.negSucc 29953906530476492303), (Int.ofNat 9255441689445003840), (Int.ofNat 930860943013049472)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7185763509189799776), (Int.ofNat 4062114197284821792), (Int.negSucc 400697606249895293183), (Int.negSucc 546081988550417290223), (Int.negSucc 1430354303128994390303), (Int.negSucc 530080952256039951743), (Int.ofNat 19059535099606473072), (Int.ofNat 291234775036530189600), (Int.ofNat 28920338845432659600), (Int.ofNat 6570649139142292368), (Int.negSucc 611223630148756223)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2436050114519368607), (Int.ofNat 6776270053260980064), (Int.ofNat 161642153849985128064), (Int.ofNat 441536010085795467888), (Int.ofNat 650027381740412274480), (Int.ofNat 883255601733249493968), (Int.ofNat 177909970337722714944), (Int.negSucc 83725817228280731327), (Int.negSucc 35252772964314047951), (Int.negSucc 9898585472655417023), (Int.negSucc 725765968819872575)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 348763701135372576), (Int.negSucc 5916838923654482399), (Int.negSucc 45357051482461857887), (Int.negSucc 279666726642513385199), (Int.negSucc 210182613956360440991), (Int.negSucc 635317888040981744111), (Int.negSucc 240306560120333834639), (Int.negSucc 72312668433285140015), (Int.ofNat 21151665570906833472), (Int.ofNat 3775303458635048640), (Int.ofNat 655795106716430592)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 102450679623699936), (Int.ofNat 2783820921259010688), (Int.ofNat 10101153167667360672), (Int.ofNat 118394651147559349488), (Int.ofNat 93175065470616074928), (Int.ofNat 239680073209830582240), (Int.ofNat 208536664062624407856), (Int.ofNat 81174528207914126976), (Int.ofNat 6269825441875414464), (Int.ofNat 555589627639793280), (Int.ofNat 59156130094829568)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 67472799217609631), (Int.negSucc 920056344433730159), (Int.negSucc 2939508374868062735), (Int.negSucc 30982517115730439615), (Int.negSucc 55845734955798577103), (Int.negSucc 44497564063739190287), (Int.negSucc 107593681791503058047), (Int.negSucc 44845131352097696831), (Int.negSucc 14019173732909015999), (Int.negSucc 1667821796162843327), (Int.negSucc 186196668752604671)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 15798969505311264), (Int.ofNat 230619386712394512), (Int.ofNat 1133484364059834528), (Int.ofNat 4411496428132807296), (Int.ofNat 23185340216730823248), (Int.ofNat 4787187618775940928), (Int.ofNat 29142799893895582656), (Int.ofNat 18888833780807923584), (Int.ofNat 7375379110004107584), (Int.ofNat 1104181541956698624), (Int.ofNat 53481198086726400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1737907419576383), (Int.negSucc 43571758511803391), (Int.negSucc 327469595994058607), (Int.negSucc 247126546321174799), (Int.negSucc 5400666730127921471), (Int.negSucc 2369837193660562751), (Int.negSucc 2762162364233826431), (Int.negSucc 5530062445632114047), (Int.negSucc 2073608631904610303), (Int.negSucc 330311257427953151), (Int.negSucc 3722308391817215)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 67751098614144), (Int.ofNat 5592301275007008), (Int.ofNat 55975083481072656), (Int.ofNat 21251662108326144), (Int.ofNat 583833043586789568), (Int.ofNat 1118160635014668672), (Int.negSucc 411461389515883391), (Int.ofNat 861370764463489536), (Int.ofNat 363467954502365184), (Int.ofNat 36175005039108096)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 361126325168639), (Int.negSucc 4985747047935359), (Int.negSucc 11575307113314623), (Int.ofNat 736295856121152), (Int.negSucc 229844317897635263), (Int.ofNat 124143616325288448), (Int.negSucc 47424320415595007), (Int.negSucc 32452696647290879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 176820643892736), (Int.ofNat 1512132865211520), (Int.negSucc 4442957088329663), (Int.ofNat 18873518444789760), (Int.negSucc 10483186490069759)]]

theorem h5n323_arithmetic_row0 :
    (BiPoly.mul h5p22 h5p322).getD 0 []=h5p323.getD 0 [] := by
  decide +kernel

theorem h5n323_arithmetic_row1 :
    (BiPoly.mul h5p22 h5p322).getD 1 []=h5p323.getD 1 [] := by
  decide +kernel

theorem h5n323_arithmetic_row2 :
    (BiPoly.mul h5p22 h5p322).getD 2 []=h5p323.getD 2 [] := by
  decide +kernel

theorem h5n323_arithmetic_row3 :
    (BiPoly.mul h5p22 h5p322).getD 3 []=h5p323.getD 3 [] := by
  decide +kernel

theorem h5n323_arithmetic_row4 :
    (BiPoly.mul h5p22 h5p322).getD 4 []=h5p323.getD 4 [] := by
  decide +kernel

theorem h5n323_arithmetic_row5 :
    (BiPoly.mul h5p22 h5p322).getD 5 []=h5p323.getD 5 [] := by
  decide +kernel

theorem h5n323_arithmetic_row6 :
    (BiPoly.mul h5p22 h5p322).getD 6 []=h5p323.getD 6 [] := by
  decide +kernel

theorem h5n323_arithmetic_row7 :
    (BiPoly.mul h5p22 h5p322).getD 7 []=h5p323.getD 7 [] := by
  decide +kernel

theorem h5n323_arithmetic_row8 :
    (BiPoly.mul h5p22 h5p322).getD 8 []=h5p323.getD 8 [] := by
  decide +kernel

theorem h5n323_arithmetic_row9 :
    (BiPoly.mul h5p22 h5p322).getD 9 []=h5p323.getD 9 [] := by
  decide +kernel

theorem h5n323_arithmetic_row10 :
    (BiPoly.mul h5p22 h5p322).getD 10 []=h5p323.getD 10 [] := by
  decide +kernel

theorem h5n323_arithmetic_row11 :
    (BiPoly.mul h5p22 h5p322).getD 11 []=h5p323.getD 11 [] := by
  decide +kernel

theorem h5n323_arithmetic_row12 :
    (BiPoly.mul h5p22 h5p322).getD 12 []=h5p323.getD 12 [] := by
  decide +kernel

theorem h5n323_arithmetic_row13 :
    (BiPoly.mul h5p22 h5p322).getD 13 []=h5p323.getD 13 [] := by
  decide +kernel

theorem h5n323_arithmetic_row14 :
    (BiPoly.mul h5p22 h5p322).getD 14 []=h5p323.getD 14 [] := by
  decide +kernel

theorem h5n323_arithmetic_row15 :
    (BiPoly.mul h5p22 h5p322).getD 15 []=h5p323.getD 15 [] := by
  decide +kernel

theorem h5n323_arithmetic_row16 :
    (BiPoly.mul h5p22 h5p322).getD 16 []=h5p323.getD 16 [] := by
  decide +kernel

theorem h5n323_arithmetic_row17 :
    (BiPoly.mul h5p22 h5p322).getD 17 []=h5p323.getD 17 [] := by
  decide +kernel

theorem h5n323_arithmetic : BiPoly.mul h5p22 h5p322=h5p323 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<18 at hk
    have hf : ∀ j : Fin 18, (BiPoly.mul h5p22 h5p322).getD j.val []=h5p323.getD j.val [] :=
      (fun j => Fin.cases h5n323_arithmetic_row0 (fun j => Fin.cases h5n323_arithmetic_row1 (fun j => Fin.cases h5n323_arithmetic_row2 (fun j => Fin.cases h5n323_arithmetic_row3 (fun j => Fin.cases h5n323_arithmetic_row4 (fun j => Fin.cases h5n323_arithmetic_row5 (fun j => Fin.cases h5n323_arithmetic_row6 (fun j => Fin.cases h5n323_arithmetic_row7 (fun j => Fin.cases h5n323_arithmetic_row8 (fun j => Fin.cases h5n323_arithmetic_row9 (fun j => Fin.cases h5n323_arithmetic_row10 (fun j => Fin.cases h5n323_arithmetic_row11 (fun j => Fin.cases h5n323_arithmetic_row12 (fun j => Fin.cases h5n323_arithmetic_row13 (fun j => Fin.cases h5n323_arithmetic_row14 (fun j => Fin.cases h5n323_arithmetic_row15 (fun j => Fin.cases h5n323_arithmetic_row16 (fun j => Fin.cases h5n323_arithmetic_row17 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n323 : h5e323.toBi mapPolyEnv=h5p323 := by
  change BiPoly.mul (h5e22.toBi mapPolyEnv) (h5e322.toBi mapPolyEnv)=h5p323
  rw [h5n22, h5n322]
  exact h5n323_arithmetic

#print axioms h5n323_arithmetic
end StackSorting.RationalLift
