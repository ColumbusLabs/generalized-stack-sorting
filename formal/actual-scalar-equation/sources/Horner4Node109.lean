import BivariateRowEquality
import Horner4Base
import Horner4Node108
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p109 : BiPoly.Poly := [[(Int.negSucc 1734585790103999999), (Int.negSucc 8830806337277495999), (Int.ofNat 10014267902161436640), (Int.ofNat 60855614093544713280), (Int.negSucc 64816101902820620159), (Int.negSucc 84648427132691041919), (Int.ofNat 84911431881329776800)], [(Int.ofNat 15094751008993920000), (Int.ofNat 72193084248069239040), (Int.negSucc 106321183528148252351), (Int.negSucc 532054374697885697567), (Int.ofNat 566381150862862487904), (Int.ofNat 713973914809666810272), (Int.negSucc 759803299637484675743), (Int.ofNat 61509085945343740800)], [(Int.negSucc 59501980328787590399), (Int.negSucc 268811950849032645359), (Int.ofNat 461324208936603705624), (Int.ofNat 2065199436192383583624), (Int.negSucc 2057793802849846940975), (Int.negSucc 2752103730117488333471), (Int.ofNat 2751585891247126877976), (Int.negSucc 284439101493389570423), (Int.ofNat 14421032149721810688)], [(Int.ofNat 140426806131387129600), (Int.ofNat 603000817309614351600), (Int.negSucc 1103223453821750873015), (Int.negSucc 4734929051339785647911), (Int.ofNat 3772002278904496040016), (Int.ofNat 6352361455437623612016), (Int.negSucc 4816880259478035011783), (Int.ofNat 95725035510146087400), (Int.negSucc 3745729682009208431), (Int.ofNat 1059377927632510464)], [(Int.negSucc 220902235019193736799), (Int.negSucc 906938331965432637839), (Int.ofNat 1608401840825007979632), (Int.ofNat 7161326148574534493304), (Int.negSucc 2799087387291488703887), (Int.negSucc 9535527992988189647855), (Int.ofNat 2642984220642461515152), (Int.ofNat 1898172384170220712008), (Int.negSucc 184946126198972996015), (Int.ofNat 5769240980432915808), (Int.negSucc 5646215766597119)], [(Int.ofNat 243941420117061302400), (Int.ofNat 960877448906011399080), (Int.negSucc 1446131636252169286859), (Int.negSucc 7513559421768278119871), (Int.negSucc 2355908968073318972147), (Int.ofNat 8915246186538563870472), (Int.ofNat 5359679716534173392508), (Int.negSucc 4788414554695365489983), (Int.ofNat 285733321674535241460), (Int.negSucc 7993420527012506783), (Int.ofNat 184489567971523776)], [(Int.negSucc 193873619194901395199), (Int.negSucc 730381933101247430519), (Int.ofNat 714493766886354385596), (Int.ofNat 5561803684532567619996), (Int.ofNat 8060301637641723711648), (Int.negSucc 3179490853379157799367), (Int.negSucc 12373931942877245847659), (Int.ofNat 3866385349264044892932), (Int.ofNat 511612267169332756536), (Int.negSucc 45255023354359898375), (Int.ofNat 1100543285437867584)], [(Int.ofNat 111729707463781756800), (Int.ofNat 395217772587516486600), (Int.negSucc 55514843136687548243), (Int.negSucc 2889679930951821090191), (Int.negSucc 9343491625309251222083), (Int.negSucc 4173669039041626125527), (Int.ofNat 10542735329636354681004), (Int.ofNat 2146811936785820748552), (Int.negSucc 1695283765700632498331), (Int.ofNat 65250062214758307744), (Int.ofNat 36434295356870592)], [(Int.negSucc 46347202070219169599), (Int.negSucc 145432781525929034279), (Int.negSucc 156352756510449974147), (Int.ofNat 1062338746294025017668), (Int.ofNat 6210394214600998792536), (Int.ofNat 7707112129426097614896), (Int.negSucc 2074143276133577407499), (Int.negSucc 6634392450602200089707), (Int.ofNat 1211645475373862784360), (Int.ofNat 103072015246724227464), (Int.negSucc 5929470806725108367)], [(Int.ofNat 13500456275665852800), (Int.ofNat 31266157966125804360), (Int.ofNat 85347695736966357228), (Int.negSucc 345163100958415184723), (Int.negSucc 2535679287669184575983), (Int.negSucc 6105862729231737215939), (Int.negSucc 4284387344343545824283), (Int.ofNat 4683430280161364468532), (Int.ofNat 780768638824021036164), (Int.negSucc 245555572626931461323), (Int.negSucc 223798119038857115)], [(Int.negSucc 2622734323138598399), (Int.negSucc 1034101724796691319), (Int.negSucc 2186196493248457451), (Int.ofNat 177047375898258525312), (Int.ofNat 681230551707455823048), (Int.ofNat 2757158690393320525548), (Int.ofNat 4742891084601654642144), (Int.negSucc 110749145569610831411), (Int.negSucc 1629600113233676274887), (Int.ofNat 70912879709431993956), (Int.ofNat 13105714357581421752)], [(Int.ofNat 305341772483299200), (Int.negSucc 1523980010166349559), (Int.negSucc 16324695406577391731), (Int.negSucc 111464980483142448479), (Int.negSucc 212434913104744452059), (Int.negSucc 706058152167197191103), (Int.negSucc 2350188420343294166087), (Int.negSucc 1886050034849669811623), (Int.ofNat 705144486604326691296), (Int.ofNat 164362381484760272592), (Int.negSucc 5707917689379457463)], [(Int.negSucc 16126043028770399), (Int.ofNat 450983282313585720), (Int.ofNat 8206097791015238004), (Int.ofNat 50361298770536151084), (Int.ofNat 123424573933306831248), (Int.ofNat 123202935767424515352), (Int.ofNat 582634596266615760648), (Int.ofNat 1298025231314841590328), (Int.ofNat 231488530340161117608), (Int.negSucc 139972532027307269903), (Int.negSucc 9100326351811949639)], [(Int.ofNat 0), (Int.negSucc 54770832789635759), (Int.negSucc 1964869356547210079), (Int.negSucc 14274882367776313859), (Int.negSucc 58563234553317286451), (Int.negSucc 55191401704877741099), (Int.negSucc 40905466847238735899), (Int.negSucc 389877443504120291759), (Int.negSucc 340163631022484203919), (Int.ofNat 5238093738722880672), (Int.ofNat 7661492625746705328)], [(Int.ofNat 0), (Int.ofNat 2392047021054240), (Int.ofNat 244567693684530648), (Int.ofNat 2398754921695557588), (Int.ofNat 16376389447109960088), (Int.ofNat 31870478841104036484), (Int.negSucc 4721566953663501767), (Int.ofNat 37376483937912507312), (Int.ofNat 132996231881081561664), (Int.ofNat 37938159763236308880), (Int.ofNat 286676247115462752)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 12811266214639487), (Int.negSucc 212436552834101807), (Int.negSucc 2512097184487464215), (Int.negSucc 9766430706712515551), (Int.negSucc 4587324009887691431), (Int.ofNat 8390662034393949696), (Int.negSucc 20443947166830836591), (Int.negSucc 18404975682284832287), (Int.negSucc 2159992330670306591)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 7119842392942560), (Int.ofNat 179494192888921080), (Int.ofNat 1482857809929595728), (Int.ofNat 2459899041550577064), (Int.negSucc 2081597453933884559), (Int.negSucc 651435411284985311), (Int.ofNat 3455100527078246400), (Int.ofNat 804024851795954784)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2996129648131199), (Int.negSucc 94451672085888671), (Int.negSucc 389230415896930271), (Int.negSucc 37355994425297375), (Int.ofNat 618185027668902624), (Int.negSucc 226621803857393663), (Int.negSucc 93668811578288639)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 962833231078272), (Int.ofNat 18263528605118304), (Int.ofNat 32566650328184832), (Int.negSucc 62138289450854879)]]

theorem h4n109_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p108).getD 0 []=h4p109.getD 0 [] := by
  decide +kernel

theorem h4n109_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p108).getD 1 []=h4p109.getD 1 [] := by
  decide +kernel

theorem h4n109_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p108).getD 2 []=h4p109.getD 2 [] := by
  decide +kernel

theorem h4n109_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p108).getD 3 []=h4p109.getD 3 [] := by
  decide +kernel

theorem h4n109_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p108).getD 4 []=h4p109.getD 4 [] := by
  decide +kernel

theorem h4n109_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p108).getD 5 []=h4p109.getD 5 [] := by
  decide +kernel

theorem h4n109_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p108).getD 6 []=h4p109.getD 6 [] := by
  decide +kernel

theorem h4n109_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p108).getD 7 []=h4p109.getD 7 [] := by
  decide +kernel

theorem h4n109_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p108).getD 8 []=h4p109.getD 8 [] := by
  decide +kernel

theorem h4n109_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p108).getD 9 []=h4p109.getD 9 [] := by
  decide +kernel

theorem h4n109_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p108).getD 10 []=h4p109.getD 10 [] := by
  decide +kernel

theorem h4n109_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p108).getD 11 []=h4p109.getD 11 [] := by
  decide +kernel

theorem h4n109_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p108).getD 12 []=h4p109.getD 12 [] := by
  decide +kernel

theorem h4n109_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p108).getD 13 []=h4p109.getD 13 [] := by
  decide +kernel

theorem h4n109_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p108).getD 14 []=h4p109.getD 14 [] := by
  decide +kernel

theorem h4n109_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p108).getD 15 []=h4p109.getD 15 [] := by
  decide +kernel

theorem h4n109_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p108).getD 16 []=h4p109.getD 16 [] := by
  decide +kernel

theorem h4n109_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p108).getD 17 []=h4p109.getD 17 [] := by
  decide +kernel

theorem h4n109_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p108).getD 18 []=h4p109.getD 18 [] := by
  decide +kernel

theorem h4n109_arithmetic : BiPoly.mul h4p13 h4p108=h4p109 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p108).getD j.val []=h4p109.getD j.val [] :=
      (fun j => Fin.cases h4n109_arithmetic_row0 (fun j => Fin.cases h4n109_arithmetic_row1 (fun j => Fin.cases h4n109_arithmetic_row2 (fun j => Fin.cases h4n109_arithmetic_row3 (fun j => Fin.cases h4n109_arithmetic_row4 (fun j => Fin.cases h4n109_arithmetic_row5 (fun j => Fin.cases h4n109_arithmetic_row6 (fun j => Fin.cases h4n109_arithmetic_row7 (fun j => Fin.cases h4n109_arithmetic_row8 (fun j => Fin.cases h4n109_arithmetic_row9 (fun j => Fin.cases h4n109_arithmetic_row10 (fun j => Fin.cases h4n109_arithmetic_row11 (fun j => Fin.cases h4n109_arithmetic_row12 (fun j => Fin.cases h4n109_arithmetic_row13 (fun j => Fin.cases h4n109_arithmetic_row14 (fun j => Fin.cases h4n109_arithmetic_row15 (fun j => Fin.cases h4n109_arithmetic_row16 (fun j => Fin.cases h4n109_arithmetic_row17 (fun j => Fin.cases h4n109_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n109 : h4e109.toBi mapPolyEnv=h4p109 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e108.toBi mapPolyEnv)=h4p109
  rw [h4n13, h4n108]
  exact h4n109_arithmetic

#print axioms h4n109_arithmetic
end StackSorting.RationalLift
