import BivariateRowEquality
import Horner4Base
import Horner4Node057
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p58 : BiPoly.Poly := [[(Int.negSucc 3047094380317967999), (Int.negSucc 13899846068870950079), (Int.ofNat 20229927414572626560), (Int.ofNat 72018504874483603200), (Int.negSucc 131909113094087162879), (Int.ofNat 56607621254219851200)], [(Int.ofNat 28138683035710840320), (Int.ofNat 129889311097542827904), (Int.negSucc 174548169278087532479), (Int.negSucc 646224564339894389183), (Int.ofNat 1182948958342016646336), (Int.negSucc 561210276154184220095), (Int.ofNat 41006057296895827200)], [(Int.negSucc 122490739466336800799), (Int.negSucc 547096231392744452399), (Int.ofNat 702709355409581528496), (Int.ofNat 2500270878564290111328), (Int.negSucc 4436489436941430828863), (Int.ofNat 2095926915299949447120), (Int.negSucc 202444762906456878671), (Int.ofNat 9614021433147873792)], [(Int.ofNat 333034869074575502880), (Int.ofNat 1371424454693599417200), (Int.negSucc 1690803359312625675503), (Int.negSucc 5344356208601093830559), (Int.ofNat 8567037501809503399200), (Int.negSucc 3301704064180693546991), (Int.ofNat 68099376955325875056), (Int.negSucc 3438822390346148255), (Int.ofNat 706251951755006976)], [(Int.negSucc 629608252612856856479), (Int.negSucc 2286938003572152517391), (Int.ofNat 2589117550039077624144), (Int.ofNat 6675278266177125658560), (Int.negSucc 7619195709750938471135), (Int.negSucc 37687042858083176015), (Int.ofNat 1433579138469671369904), (Int.negSucc 128393361260080374815), (Int.ofNat 3851179512081141312), (Int.negSucc 3764143844398079)], [(Int.ofNat 870246329286923647920), (Int.ofNat 2708171211100078110744), (Int.negSucc 2437844850445838611103), (Int.negSucc 4507656538605846671159), (Int.negSucc 1385030785724085010319), (Int.ofNat 8015243814884950537032), (Int.negSucc 3455653141344897433439), (Int.ofNat 197893905548495217912), (Int.negSucc 5492937745094136767), (Int.ofNat 122993045314349184)], [(Int.negSucc 900144185524400585999), (Int.negSucc 2408688195108559597175), (Int.ofNat 1019321889649215628488), (Int.ofNat 817634724196652257632), (Int.ofNat 10395028464982666224912), (Int.negSucc 11368084955978608312007), (Int.ofNat 2093489692013401710840), (Int.ofNat 381857146513747687248), (Int.negSucc 31148276267740258991), (Int.ofNat 733695523625245056)], [(Int.ofNat 702258635081865325680), (Int.ofNat 1716898098633854536104), (Int.ofNat 679284971972268600576), (Int.ofNat 915585029680164767016), (Int.negSucc 9952841050704202857935), (Int.ofNat 4086813893843904340200), (Int.ofNat 2998247260681668389136), (Int.negSucc 1189738784155949334695), (Int.ofNat 43467655436188320192), (Int.ofNat 24289530237913728)], [(Int.negSucc 412095219971251310639), (Int.negSucc 1049617684906990413719), (Int.negSucc 1554231203918885550215), (Int.negSucc 395024104532302411199), (Int.ofNat 2930491719233837465568), (Int.ofNat 5138681683827597810312), (Int.negSucc 5440751235283450054247), (Int.ofNat 712513708541022732864), (Int.ofNat 73985317548238470192), (Int.negSucc 3952980537816738911)], [(Int.ofNat 179683754821986115440), (Int.ofNat 566654010039573408552), (Int.ofNat 1437298388978243206152), (Int.negSucc 271592697039207537311), (Int.ofNat 1630984195984926711240), (Int.negSucc 6365771397978902579495), (Int.ofNat 2242633542062054596056), (Int.ofNat 743764185300605085336), (Int.negSucc 163504783423253101223), (Int.negSucc 149198746025904743)], [(Int.negSucc 56868726759196769039), (Int.negSucc 259876458903924148391), (Int.negSucc 874325324553978333887), (Int.ofNat 151087660860209069520), (Int.negSucc 1528835803616949707447), (Int.ofNat 2224719834489403633248), (Int.ofNat 1442210077661523993960), (Int.negSucc 1142474131348357640207), (Int.ofNat 35625729266215621080), (Int.ofNat 8737142905054281168)], [(Int.ofNat 12550722566158398960), (Int.ofNat 93941660422411633896), (Int.ofNat 380116990047594734880), (Int.ofNat 157523285126568499992), (Int.ofNat 264163497982983886080), (Int.ofNat 432973842106373012304), (Int.negSucc 1765226116139326826351), (Int.ofNat 313112770744201043520), (Int.ofNat 114648625602621921696), (Int.negSucc 3805278459586304975)], [(Int.negSucc 1800367080968554799), (Int.negSucc 24885200859906147863), (Int.negSucc 118910755470352325783), (Int.negSucc 200690048649670035599), (Int.ofNat 141339649973545389456), (Int.negSucc 530819664838308020879), (Int.ofNat 549344043494578177680), (Int.ofNat 277715070037772597808), (Int.negSucc 85225842372149780255), (Int.negSucc 6066884234541299759)], [(Int.ofNat 146376022151123040), (Int.ofNat 4493519876572286016), (Int.ofNat 26065071784529914824), (Int.ofNat 99363271950807368712), (Int.negSucc 57021418867355524775), (Int.ofNat 99766407444572131416), (Int.ofNat 49484910010030479072), (Int.negSucc 224087646796957097567), (Int.negSucc 3318153174848484287), (Int.ofNat 5107661750497803552)], [(Int.negSucc 4784094042108479), (Int.negSucc 496267582913272367), (Int.negSucc 3803046797776196519), (Int.negSucc 27042425869365032975), (Int.negSucc 7177141955525265575), (Int.ofNat 25682048130074851152), (Int.negSucc 64507726204737033311), (Int.ofNat 52120943698152177216), (Int.ofNat 25037283178054905696), (Int.ofNat 191117498076975168)], [(Int.ofNat 0), (Int.ofNat 25622532429278976), (Int.ofNat 336804167246246496), (Int.ofNat 4125842778929401008), (Int.ofNat 8235352759204168704), (Int.negSucc 12446073535582161647), (Int.ofNat 9770650695973686528), (Int.ofNat 1741786094284755552), (Int.negSucc 10349990605371837887), (Int.negSucc 1439994887113537727)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14239684785885119), (Int.negSucc 307051569403168175), (Int.negSucc 1895628241813465439), (Int.ofNat 1202999311353629232), (Int.ofNat 1436918740500560544), (Int.negSucc 2547726717949178687), (Int.ofNat 1588711594233537792), (Int.ofNat 536016567863969856)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5992259296262400), (Int.ofNat 166259409657058368), (Int.ofNat 147964832297161920), (Int.negSucc 559585100307859775), (Int.ofNat 369634510167130944), (Int.negSucc 67820036724228095), (Int.negSucc 62445874385525759)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1925666462156543), (Int.negSucc 29052638008380863), (Int.ofNat 51150179671964928), (Int.negSucc 20171875201427519)]]

theorem h4n58_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p57).getD 0 []=h4p58.getD 0 [] := by
  decide +kernel

theorem h4n58_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p57).getD 1 []=h4p58.getD 1 [] := by
  decide +kernel

theorem h4n58_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p57).getD 2 []=h4p58.getD 2 [] := by
  decide +kernel

theorem h4n58_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p57).getD 3 []=h4p58.getD 3 [] := by
  decide +kernel

theorem h4n58_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p57).getD 4 []=h4p58.getD 4 [] := by
  decide +kernel

theorem h4n58_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p57).getD 5 []=h4p58.getD 5 [] := by
  decide +kernel

theorem h4n58_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p57).getD 6 []=h4p58.getD 6 [] := by
  decide +kernel

theorem h4n58_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p57).getD 7 []=h4p58.getD 7 [] := by
  decide +kernel

theorem h4n58_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p57).getD 8 []=h4p58.getD 8 [] := by
  decide +kernel

theorem h4n58_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p57).getD 9 []=h4p58.getD 9 [] := by
  decide +kernel

theorem h4n58_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p57).getD 10 []=h4p58.getD 10 [] := by
  decide +kernel

theorem h4n58_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p57).getD 11 []=h4p58.getD 11 [] := by
  decide +kernel

theorem h4n58_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p57).getD 12 []=h4p58.getD 12 [] := by
  decide +kernel

theorem h4n58_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p57).getD 13 []=h4p58.getD 13 [] := by
  decide +kernel

theorem h4n58_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p57).getD 14 []=h4p58.getD 14 [] := by
  decide +kernel

theorem h4n58_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p57).getD 15 []=h4p58.getD 15 [] := by
  decide +kernel

theorem h4n58_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p57).getD 16 []=h4p58.getD 16 [] := by
  decide +kernel

theorem h4n58_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p57).getD 17 []=h4p58.getD 17 [] := by
  decide +kernel

theorem h4n58_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p57).getD 18 []=h4p58.getD 18 [] := by
  decide +kernel

theorem h4n58_arithmetic : BiPoly.mul h4p13 h4p57=h4p58 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p57).getD j.val []=h4p58.getD j.val [] :=
      (fun j => Fin.cases h4n58_arithmetic_row0 (fun j => Fin.cases h4n58_arithmetic_row1 (fun j => Fin.cases h4n58_arithmetic_row2 (fun j => Fin.cases h4n58_arithmetic_row3 (fun j => Fin.cases h4n58_arithmetic_row4 (fun j => Fin.cases h4n58_arithmetic_row5 (fun j => Fin.cases h4n58_arithmetic_row6 (fun j => Fin.cases h4n58_arithmetic_row7 (fun j => Fin.cases h4n58_arithmetic_row8 (fun j => Fin.cases h4n58_arithmetic_row9 (fun j => Fin.cases h4n58_arithmetic_row10 (fun j => Fin.cases h4n58_arithmetic_row11 (fun j => Fin.cases h4n58_arithmetic_row12 (fun j => Fin.cases h4n58_arithmetic_row13 (fun j => Fin.cases h4n58_arithmetic_row14 (fun j => Fin.cases h4n58_arithmetic_row15 (fun j => Fin.cases h4n58_arithmetic_row16 (fun j => Fin.cases h4n58_arithmetic_row17 (fun j => Fin.cases h4n58_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n58 : h4e58.toBi mapPolyEnv=h4p58 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e57.toBi mapPolyEnv)=h4p58
  rw [h4n13, h4n57]
  exact h4n58_arithmetic

#print axioms h4n58_arithmetic
end StackSorting.RationalLift
