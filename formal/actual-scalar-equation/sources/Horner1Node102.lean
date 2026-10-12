import BivariateRowEquality
import Horner1Base
import Horner1Node101
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p102 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 65656935935999), (Int.negSucc 152374057148159), (Int.ofNat 1921849509882240), (Int.ofNat 4963906861585920), (Int.negSucc 9989102534964479), (Int.negSucc 19096505107557119), (Int.ofNat 20874563765700480)], [(Int.ofNat 0), (Int.ofNat 707327711072640), (Int.ofNat 839208788422848), (Int.negSucc 22197471549834815), (Int.negSucc 39425668385947775), (Int.ofNat 123584614267984128), (Int.ofNat 150720008005738944), (Int.negSucc 215514571594674239), (Int.ofNat 19663368913322496)], [(Int.ofNat 0), (Int.negSucc 3501845139559679), (Int.negSucc 57674134938815), (Int.ofNat 114421671454596768), (Int.ofNat 125791037785857888), (Int.negSucc 641534457627499967), (Int.negSucc 507868323050815487), (Int.ofNat 873093259662619680), (Int.negSucc 85188556687379615), (Int.ofNat 6377226268276224)], [(Int.ofNat 0), (Int.ofNat 10552281693625440), (Int.negSucc 12714019837560143), (Int.negSucc 350503293854517983), (Int.negSucc 179873127116945135), (Int.ofNat 1898168256262959840), (Int.ofNat 1045219588658770896), (Int.negSucc 1760256578000411423), (Int.negSucc 158940832350247055), (Int.ofNat 21355504886287296), (Int.ofNat 667566420000768)], [(Int.ofNat 0), (Int.negSucc 21604565439064799), (Int.ofNat 54017295756674832), (Int.ofNat 714931789579558752), (Int.negSucc 1258509590012111), (Int.negSucc 3642485771011812479), (Int.negSucc 1850728114778439119), (Int.ofNat 1652206674939434016), (Int.ofNat 1679566975666345104), (Int.negSucc 235974173970118559), (Int.ofNat 14385653307710208), (Int.negSucc 46127571154943)], [(Int.ofNat 0), (Int.ofNat 31764704767684800), (Int.negSucc 123989772072443999), (Int.negSucc 1029749826618943727), (Int.ofNat 465323023932135216), (Int.ofNat 4930370596687407888), (Int.ofNat 3596480742232288128), (Int.ofNat 140929882316367984), (Int.negSucc 4229055068192971535), (Int.ofNat 269325886208284656), (Int.negSucc 14004088617266303), (Int.ofNat 1881596308468224), (Int.negSucc 11628029288447)], [(Int.ofNat 0), (Int.negSucc 34555026997165119), (Int.ofNat 188846960146556096), (Int.ofNat 1083711044014323072), (Int.negSucc 902903332309683119), (Int.negSucc 5142278208035687135), (Int.negSucc 6514672495514946719), (Int.negSucc 2483817116586603423), (Int.ofNat 4771772905317826160), (Int.ofNat 1246572263322418656), (Int.negSucc 206961762719500863), (Int.ofNat 10841457657527552), (Int.ofNat 4424501485056), (Int.negSucc 400900251647)], [(Int.ofNat 0), (Int.ofNat 28227226864304640), (Int.negSucc 205069653878160831), (Int.negSucc 851985642786913135), (Int.ofNat 965663425553032000), (Int.ofNat 4639702160143432864), (Int.ofNat 9034900083647000800), (Int.ofNat 4398758625941758960), (Int.negSucc 1380921094322712911), (Int.negSucc 4081178615468011167), (Int.ofNat 410449607290550096), (Int.negSucc 26341074735441919), (Int.ofNat 1424720723036928), (Int.negSucc 7083595723775)], [(Int.ofNat 0), (Int.negSucc 17382099951480319), (Int.ofNat 163947846113387712), (Int.ofNat 509695595140199888), (Int.negSucc 684675494876968543), (Int.negSucc 3985355716041074383), (Int.negSucc 9211462161979631295), (Int.negSucc 6312516635605290895), (Int.negSucc 2915738877145459471), (Int.ofNat 4613322479574068752), (Int.ofNat 480195223608440144), (Int.negSucc 89744191955904927), (Int.ofNat 3535462564608000), (Int.ofNat 19341890027008)], [(Int.ofNat 0), (Int.ofNat 8021666985473600), (Int.negSucc 97757426244414815), (Int.negSucc 237488383496363663), (Int.ofNat 356405257824439920), (Int.ofNat 3214032358118138784), (Int.ofNat 7193048210348901136), (Int.ofNat 7841580413017178672), (Int.ofNat 4621046420088259008), (Int.negSucc 1138396966515116431), (Int.negSucc 2171451803418187823), (Int.ofNat 219528464172424720), (Int.negSucc 11721807424754751), (Int.ofNat 333381398067456)], [(Int.ofNat 0), (Int.negSucc 2728279988299199), (Int.ofNat 43468953834374880), (Int.ofNat 89336128059566448), (Int.negSucc 161742847820318719), (Int.negSucc 2229383316155821183), (Int.negSucc 4696847286802369247), (Int.negSucc 7465063969026459407), (Int.negSucc 4413766146618236079), (Int.negSucc 2517988760461860607), (Int.ofNat 2241174864660064352), (Int.ofNat 120990445955744672), (Int.negSucc 21640361971620511), (Int.ofNat 485827716722816)], [(Int.ofNat 0), (Int.ofNat 662523489765280), (Int.negSucc 14235244088994223), (Int.negSucc 28345658324560175), (Int.ofNat 79173033814790752), (Int.ofNat 1245812815841603600), (Int.ofNat 2818991107896314000), (Int.ofNat 5178839380018859968), (Int.ofNat 4003027111220908720), (Int.ofNat 3075543961095986800), (Int.negSucc 239099113921794751), (Int.negSucc 678855599235257119), (Int.ofNat 53679664047498048), (Int.negSucc 1709304104079359)], [(Int.ofNat 0), (Int.negSucc 108490462492959), (Int.ofNat 3337526512410928), (Int.ofNat 7711301696871888), (Int.negSucc 39977347601426063), (Int.negSucc 547882982641566319), (Int.negSucc 1577119440247405263), (Int.negSucc 2695659108214539263), (Int.negSucc 3232258285983503423), (Int.negSucc 1935721156654292831), (Int.negSucc 1271172018632837375), (Int.ofNat 564355490967492960), (Int.ofNat 25986540087468288), (Int.negSucc 2548890265663487)], [(Int.ofNat 0), (Int.ofNat 10714503070080), (Int.negSucc 530640048313087), (Int.negSucc 1707230647249023), (Int.ofNat 16598327457090016), (Int.ofNat 189420104137415504), (Int.ofNat 759680566843984336), (Int.ofNat 1167357873404186672), (Int.ofNat 1917179583036484224), (Int.ofNat 1140918166972843680), (Int.ofNat 1096698996836430624), (Int.ofNat 60878570216796480), (Int.negSucc 115010911590324287), (Int.ofNat 4839446602040064)], [(Int.ofNat 0), (Int.negSucc 481100998399), (Int.ofNat 51289147798304), (Int.ofNat 273834916906672), (Int.negSucc 4912853522664751), (Int.negSucc 51453305581677439), (Int.negSucc 287831862492856031), (Int.negSucc 479094847191239327), (Int.negSucc 776773213134881567), (Int.negSucc 731290118232396671), (Int.negSucc 442332275976123647), (Int.negSucc 333222649415138495), (Int.ofNat 62970677701913088), (Int.ofNat 3333613160765952)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2275937651519), (Int.negSucc 26874434756159), (Int.ofNat 954734242225680), (Int.ofNat 10738640168806416), (Int.ofNat 80402879262051072), (Int.ofNat 184696990330940064), (Int.ofNat 227415846419551872), (Int.ofNat 356202761107145088), (Int.ofNat 154516270038509952), (Int.ofNat 187710809995679616), (Int.ofNat 27934744386962304), (Int.negSucc 7612713328854527)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1167341232960), (Int.negSucc 109128848706239), (Int.negSucc 1611733494977375), (Int.negSucc 15640100436278591), (Int.negSucc 57059344963392287), (Int.negSucc 61295482573108991), (Int.negSucc 104723852948334719), (Int.negSucc 77629008363321599), (Int.negSucc 42552005454835199), (Int.negSucc 38603552065735679), (Int.ofNat 1699562003355648)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5562601515072), (Int.ofNat 151552924193376), (Int.ofNat 1953652525204896), (Int.ofNat 12080186716502592), (Int.ofNat 17988902230074048), (Int.ofNat 17687727922533120), (Int.ofNat 29598565779537408), (Int.ofNat 6875749080184320), (Int.ofNat 12570749455193856), (Int.ofNat 2306765135250432)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 6505426861631), (Int.negSucc 133881712109567), (Int.negSucc 1526899378686911), (Int.negSucc 4275285122942207), (Int.negSucc 2525682967303679), (Int.negSucc 5340679018219007), (Int.negSucc 3039330353303807), (Int.negSucc 1056795874555391), (Int.negSucc 1343071177850879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3332702154240), (Int.ofNat 92507604453504), (Int.ofNat 585164574497664), (Int.ofNat 577570501347840), (Int.ofNat 306045890148096), (Int.ofNat 801923676613632), (Int.negSucc 37510404410879), (Int.ofNat 204054196377600)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1296237489407), (Int.negSucc 33917697077759), (Int.negSucc 90358462759679), (Int.negSucc 6324280022015), (Int.negSucc 54940924270079), (Int.negSucc 15115125657599)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 271305013248), (Int.ofNat 4670190203904), (Int.ofNat 2267268848640)]]

theorem h1n102_arithmetic_row0 :
    (BiPoly.mul h1p4 h1p101).getD 0 []=h1p102.getD 0 [] := by
  decide +kernel

theorem h1n102_arithmetic_row1 :
    (BiPoly.mul h1p4 h1p101).getD 1 []=h1p102.getD 1 [] := by
  decide +kernel

theorem h1n102_arithmetic_row2 :
    (BiPoly.mul h1p4 h1p101).getD 2 []=h1p102.getD 2 [] := by
  decide +kernel

theorem h1n102_arithmetic_row3 :
    (BiPoly.mul h1p4 h1p101).getD 3 []=h1p102.getD 3 [] := by
  decide +kernel

theorem h1n102_arithmetic_row4 :
    (BiPoly.mul h1p4 h1p101).getD 4 []=h1p102.getD 4 [] := by
  decide +kernel

theorem h1n102_arithmetic_row5 :
    (BiPoly.mul h1p4 h1p101).getD 5 []=h1p102.getD 5 [] := by
  decide +kernel

theorem h1n102_arithmetic_row6 :
    (BiPoly.mul h1p4 h1p101).getD 6 []=h1p102.getD 6 [] := by
  decide +kernel

theorem h1n102_arithmetic_row7 :
    (BiPoly.mul h1p4 h1p101).getD 7 []=h1p102.getD 7 [] := by
  decide +kernel

theorem h1n102_arithmetic_row8 :
    (BiPoly.mul h1p4 h1p101).getD 8 []=h1p102.getD 8 [] := by
  decide +kernel

theorem h1n102_arithmetic_row9 :
    (BiPoly.mul h1p4 h1p101).getD 9 []=h1p102.getD 9 [] := by
  decide +kernel

theorem h1n102_arithmetic_row10 :
    (BiPoly.mul h1p4 h1p101).getD 10 []=h1p102.getD 10 [] := by
  decide +kernel

theorem h1n102_arithmetic_row11 :
    (BiPoly.mul h1p4 h1p101).getD 11 []=h1p102.getD 11 [] := by
  decide +kernel

theorem h1n102_arithmetic_row12 :
    (BiPoly.mul h1p4 h1p101).getD 12 []=h1p102.getD 12 [] := by
  decide +kernel

theorem h1n102_arithmetic_row13 :
    (BiPoly.mul h1p4 h1p101).getD 13 []=h1p102.getD 13 [] := by
  decide +kernel

theorem h1n102_arithmetic_row14 :
    (BiPoly.mul h1p4 h1p101).getD 14 []=h1p102.getD 14 [] := by
  decide +kernel

theorem h1n102_arithmetic_row15 :
    (BiPoly.mul h1p4 h1p101).getD 15 []=h1p102.getD 15 [] := by
  decide +kernel

theorem h1n102_arithmetic_row16 :
    (BiPoly.mul h1p4 h1p101).getD 16 []=h1p102.getD 16 [] := by
  decide +kernel

theorem h1n102_arithmetic_row17 :
    (BiPoly.mul h1p4 h1p101).getD 17 []=h1p102.getD 17 [] := by
  decide +kernel

theorem h1n102_arithmetic_row18 :
    (BiPoly.mul h1p4 h1p101).getD 18 []=h1p102.getD 18 [] := by
  decide +kernel

theorem h1n102_arithmetic_row19 :
    (BiPoly.mul h1p4 h1p101).getD 19 []=h1p102.getD 19 [] := by
  decide +kernel

theorem h1n102_arithmetic_row20 :
    (BiPoly.mul h1p4 h1p101).getD 20 []=h1p102.getD 20 [] := by
  decide +kernel

theorem h1n102_arithmetic_row21 :
    (BiPoly.mul h1p4 h1p101).getD 21 []=h1p102.getD 21 [] := by
  decide +kernel

theorem h1n102_arithmetic : BiPoly.mul h1p4 h1p101=h1p102 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p4 h1p101).getD j.val []=h1p102.getD j.val [] :=
      (fun j => Fin.cases h1n102_arithmetic_row0 (fun j => Fin.cases h1n102_arithmetic_row1 (fun j => Fin.cases h1n102_arithmetic_row2 (fun j => Fin.cases h1n102_arithmetic_row3 (fun j => Fin.cases h1n102_arithmetic_row4 (fun j => Fin.cases h1n102_arithmetic_row5 (fun j => Fin.cases h1n102_arithmetic_row6 (fun j => Fin.cases h1n102_arithmetic_row7 (fun j => Fin.cases h1n102_arithmetic_row8 (fun j => Fin.cases h1n102_arithmetic_row9 (fun j => Fin.cases h1n102_arithmetic_row10 (fun j => Fin.cases h1n102_arithmetic_row11 (fun j => Fin.cases h1n102_arithmetic_row12 (fun j => Fin.cases h1n102_arithmetic_row13 (fun j => Fin.cases h1n102_arithmetic_row14 (fun j => Fin.cases h1n102_arithmetic_row15 (fun j => Fin.cases h1n102_arithmetic_row16 (fun j => Fin.cases h1n102_arithmetic_row17 (fun j => Fin.cases h1n102_arithmetic_row18 (fun j => Fin.cases h1n102_arithmetic_row19 (fun j => Fin.cases h1n102_arithmetic_row20 (fun j => Fin.cases h1n102_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n102 : h1e102.toBi mapPolyEnv=h1p102 := by
  change BiPoly.mul (h1e4.toBi mapPolyEnv) (h1e101.toBi mapPolyEnv)=h1p102
  rw [h1n4, h1n101]
  exact h1n102_arithmetic

#print axioms h1n102_arithmetic
end StackSorting.RationalLift
