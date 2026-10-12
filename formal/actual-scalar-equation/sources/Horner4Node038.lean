import BivariateRowEquality
import Horner4Base
import Horner4Node011
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p38 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 40145538846519043919), (Int.negSucc 206909802545304415679), (Int.ofNat 149957758568268911520), (Int.ofNat 1073475205574692334400), (Int.negSucc 1080585647037245537999)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 392100197687004719520), (Int.ofNat 2150146980128511181440), (Int.negSucc 924687521916200700479), (Int.negSucc 10508175856513139558399), (Int.ofNat 9774958751520780316320), (Int.negSucc 591825694916539036799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1861891110513533539439), (Int.negSucc 9986571922285770259679), (Int.ofNat 2930869041080326672320), (Int.ofNat 43392679175814748364160), (Int.negSucc 36936235752343839968399), (Int.ofNat 2698374940814947209120), (Int.negSucc 78030678726615669119)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5678428156571457516240), (Int.ofNat 27720170737216823522160), (Int.negSucc 8098603827044505864479), (Int.negSucc 95615659786596628134239), (Int.ofNat 68541534012718294488720), (Int.negSucc 794305481702823386639), (Int.negSucc 93805406503041389759), (Int.ofNat 822503955272947200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 12362692171803957242639), (Int.negSucc 51328564116412510614959), (Int.ofNat 19532745088715769637680), (Int.ofNat 112048928484472466102880), (Int.negSucc 43422844863029972192639), (Int.negSucc 19446126352577644673519), (Int.ofNat 1288011878342526016080), (Int.negSucc 29988711322782917759), (Int.negSucc 2087120632607999)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 20217209701876169826960), (Int.ofNat 66310721240675911138080), (Int.negSucc 30171527295513186775679), (Int.negSucc 44440288368481644357599), (Int.negSucc 65475394189682001847919), (Int.ofNat 50190697004312567698560), (Int.negSucc 1216023956094108006719), (Int.negSucc 49714185021342814079), (Int.ofNat 151463616013036800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 25484496156308440010339), (Int.negSucc 60247451252809256534279), (Int.ofNat 18435297433540537237860), (Int.negSucc 48929026189888322165519), (Int.ofNat 152880194061723255965460), (Int.negSucc 42625791743061733388999), (Int.negSucc 4975740043255899005219), (Int.ofNat 286744472440237019520), (Int.negSucc 2494257648850941119)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 25041942754547133907800), (Int.ofNat 37889271350252125569720), (Int.ofNat 20221202484683615242080), (Int.ofNat 67641934764247970504400), (Int.negSucc 104320158477537127714199), (Int.negSucc 18945042743675408690519), (Int.ofNat 11871573819083250914160), (Int.ofNat 39969605284121154240), (Int.negSucc 9667983659597170559)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 19203345610376192080379), (Int.negSucc 16502003811239421565799), (Int.negSucc 52868987506799511497639), (Int.negSucc 21872711121479399086199), (Int.negSucc 13799997690559590303179), (Int.ofNat 63617046724880279238600), (Int.negSucc 6272330025565105785359), (Int.negSucc 1035559530848134164599), (Int.ofNat 8965382789137024080)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 11412650928402109278000), (Int.ofNat 6510474224535810704400), (Int.ofNat 50858098915456304916480), (Int.negSucc 5970561255760609405439), (Int.ofNat 62478042873253203467520), (Int.negSucc 40076572135609104688799), (Int.negSucc 7051660808773938436079), (Int.ofNat 879988240035696338640), (Int.ofNat 32469472902475026000)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 5182096222099875000059), (Int.negSucc 4551345844791128508959), (Int.negSucc 26705326890887377004879), (Int.negSucc 2518771967330386874039), (Int.negSucc 35024938502962556553659), (Int.negSucc 4360510544395167782279), (Int.ofNat 10037405991187686866580), (Int.ofNat 629071312397192955000), (Int.negSucc 30051544892266180979)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1758088006359507186120), (Int.ofNat 3812779114788604753080), (Int.ofNat 7371418915342570695480), (Int.ofNat 11902272931549325414520), (Int.ofNat 5437051902901787958720), (Int.ofNat 17278340798696952601440), (Int.negSucc 2625087176837781969239), (Int.negSucc 1140962714156242005479), (Int.negSucc 27791527548326924879)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 431044581710872252259), (Int.negSucc 2256005353488341052599), (Int.negSucc 629219907179670770459), (Int.negSucc 8703687984234836019479), (Int.ofNat 1025954484860687535720), (Int.negSucc 8418639637183514517359), (Int.negSucc 2283637191570660933899), (Int.ofNat 305381034217563616800), (Int.ofNat 37755597708977600160)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 72580535284718525040), (Int.ofNat 873030157944222206880), (Int.negSucc 39966145197850887839), (Int.ofNat 2905117112311144542000), (Int.ofNat 356773346985957757920), (Int.ofNat 1439305779127614833520), (Int.ofNat 1837018820242429293600), (Int.ofNat 265413759627808002960), (Int.negSucc 1518698216137211999)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 7728068462151541679), (Int.negSucc 219169281338252765639), (Int.negSucc 130814516023760753099), (Int.negSucc 374436441407519931239), (Int.negSucc 632349660132804675419), (Int.ofNat 95564759415793179840), (Int.negSucc 497106852405519019679), (Int.negSucc 198293260245224572799), (Int.negSucc 13563799113961878479)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 449824079691783360), (Int.ofNat 34305033079648299600), (Int.ofNat 92552587566545760840), (Int.negSucc 56277847646660521799), (Int.ofNat 236192504643161685360), (Int.negSucc 68436462138910169759), (Int.ofNat 45510365980274947200), (Int.ofNat 47396868148419102720), (Int.ofNat 6418024539323143680)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 10644686252032319), (Int.negSucc 2979317757528882719), (Int.negSucc 26659355794004209139), (Int.ofNat 29544737445435313440), (Int.negSucc 41155814837240838719), (Int.ofNat 8718016388393387520), (Int.ofNat 2548100445938428320), (Int.negSucc 3717600918885826559), (Int.negSucc 917368787504517119)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 101864045857224960), (Int.ofNat 3893268205973312640), (Int.negSucc 4666073147995492079), (Int.ofNat 3286135703999109600), (Int.negSucc 255254314612008959), (Int.negSucc 592674820468692479)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 243696328682814719), (Int.ofNat 305470299183016320), (Int.negSucc 95725799591766479)]]

theorem h4n38_arithmetic_row0 :
    (BiPoly.mul h4p37 h4p11).getD 0 []=h4p38.getD 0 [] := by
  decide +kernel

theorem h4n38_arithmetic_row1 :
    (BiPoly.mul h4p37 h4p11).getD 1 []=h4p38.getD 1 [] := by
  decide +kernel

theorem h4n38_arithmetic_row2 :
    (BiPoly.mul h4p37 h4p11).getD 2 []=h4p38.getD 2 [] := by
  decide +kernel

theorem h4n38_arithmetic_row3 :
    (BiPoly.mul h4p37 h4p11).getD 3 []=h4p38.getD 3 [] := by
  decide +kernel

theorem h4n38_arithmetic_row4 :
    (BiPoly.mul h4p37 h4p11).getD 4 []=h4p38.getD 4 [] := by
  decide +kernel

theorem h4n38_arithmetic_row5 :
    (BiPoly.mul h4p37 h4p11).getD 5 []=h4p38.getD 5 [] := by
  decide +kernel

theorem h4n38_arithmetic_row6 :
    (BiPoly.mul h4p37 h4p11).getD 6 []=h4p38.getD 6 [] := by
  decide +kernel

theorem h4n38_arithmetic_row7 :
    (BiPoly.mul h4p37 h4p11).getD 7 []=h4p38.getD 7 [] := by
  decide +kernel

theorem h4n38_arithmetic_row8 :
    (BiPoly.mul h4p37 h4p11).getD 8 []=h4p38.getD 8 [] := by
  decide +kernel

theorem h4n38_arithmetic_row9 :
    (BiPoly.mul h4p37 h4p11).getD 9 []=h4p38.getD 9 [] := by
  decide +kernel

theorem h4n38_arithmetic_row10 :
    (BiPoly.mul h4p37 h4p11).getD 10 []=h4p38.getD 10 [] := by
  decide +kernel

theorem h4n38_arithmetic_row11 :
    (BiPoly.mul h4p37 h4p11).getD 11 []=h4p38.getD 11 [] := by
  decide +kernel

theorem h4n38_arithmetic_row12 :
    (BiPoly.mul h4p37 h4p11).getD 12 []=h4p38.getD 12 [] := by
  decide +kernel

theorem h4n38_arithmetic_row13 :
    (BiPoly.mul h4p37 h4p11).getD 13 []=h4p38.getD 13 [] := by
  decide +kernel

theorem h4n38_arithmetic_row14 :
    (BiPoly.mul h4p37 h4p11).getD 14 []=h4p38.getD 14 [] := by
  decide +kernel

theorem h4n38_arithmetic_row15 :
    (BiPoly.mul h4p37 h4p11).getD 15 []=h4p38.getD 15 [] := by
  decide +kernel

theorem h4n38_arithmetic_row16 :
    (BiPoly.mul h4p37 h4p11).getD 16 []=h4p38.getD 16 [] := by
  decide +kernel

theorem h4n38_arithmetic_row17 :
    (BiPoly.mul h4p37 h4p11).getD 17 []=h4p38.getD 17 [] := by
  decide +kernel

theorem h4n38_arithmetic_row18 :
    (BiPoly.mul h4p37 h4p11).getD 18 []=h4p38.getD 18 [] := by
  decide +kernel

theorem h4n38_arithmetic : BiPoly.mul h4p37 h4p11=h4p38 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p37 h4p11).getD j.val []=h4p38.getD j.val [] :=
      (fun j => Fin.cases h4n38_arithmetic_row0 (fun j => Fin.cases h4n38_arithmetic_row1 (fun j => Fin.cases h4n38_arithmetic_row2 (fun j => Fin.cases h4n38_arithmetic_row3 (fun j => Fin.cases h4n38_arithmetic_row4 (fun j => Fin.cases h4n38_arithmetic_row5 (fun j => Fin.cases h4n38_arithmetic_row6 (fun j => Fin.cases h4n38_arithmetic_row7 (fun j => Fin.cases h4n38_arithmetic_row8 (fun j => Fin.cases h4n38_arithmetic_row9 (fun j => Fin.cases h4n38_arithmetic_row10 (fun j => Fin.cases h4n38_arithmetic_row11 (fun j => Fin.cases h4n38_arithmetic_row12 (fun j => Fin.cases h4n38_arithmetic_row13 (fun j => Fin.cases h4n38_arithmetic_row14 (fun j => Fin.cases h4n38_arithmetic_row15 (fun j => Fin.cases h4n38_arithmetic_row16 (fun j => Fin.cases h4n38_arithmetic_row17 (fun j => Fin.cases h4n38_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n38 : h4e38.toBi mapPolyEnv=h4p38 := by
  change BiPoly.mul (h4e37.toBi mapPolyEnv) (h4e11.toBi mapPolyEnv)=h4p38
  rw [h4n37, h4n11]
  exact h4n38_arithmetic

#print axioms h4n38_arithmetic
end StackSorting.RationalLift
