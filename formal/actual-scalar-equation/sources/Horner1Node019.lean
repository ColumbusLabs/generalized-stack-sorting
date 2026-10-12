import BivariateRowEquality
import Horner1Base
import Horner1Node018
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p19 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 156090074112000), (Int.ofNat 263797415262720), (Int.negSucc 5963234214216959), (Int.negSucc 15578340730329599), (Int.ofNat 31259102764723200), (Int.ofNat 66614806623006720), (Int.negSucc 71447549304764159)], [(Int.ofNat 0), (Int.negSucc 1667968002074879), (Int.negSucc 484722713586815), (Int.ofNat 68529400203712896), (Int.ofNat 123349190330020608), (Int.negSucc 392208853241986559), (Int.negSucc 535709224296844415), (Int.ofNat 743633807756685696), (Int.negSucc 68676897604326911)], [(Int.ofNat 0), (Int.ofNat 8182659783363840), (Int.negSucc 9824175548762111), (Int.negSucc 352458398121908543), (Int.negSucc 389386720037145023), (Int.ofNat 2061462012722195328), (Int.ofNat 1845167257955214720), (Int.negSucc 3040236078567476543), (Int.ofNat 308392478350452288), (Int.negSucc 23279639359463423)], [(Int.ofNat 0), (Int.negSucc 24403466902789439), (Int.ofNat 68755694414972256), (Int.ofNat 1079451574492380480), (Int.ofNat 529725092931219744), (Int.negSucc 6180801382848148415), (Int.negSucc 3843566341072382303), (Int.ofNat 6185266419972837312), (Int.ofNat 482714035660371168), (Int.negSucc 65099156149297151), (Int.negSucc 2869190219169791)], [(Int.ofNat 0), (Int.ofNat 49378201052071680), (Int.negSucc 227572557243962111), (Int.negSucc 2204780033072760767), (Int.ofNat 136418998313135808), (Int.ofNat 12047645868836261760), (Int.ofNat 6605883650523603456), (Int.negSucc 5817081455674316351), (Int.negSucc 5704217043634812095), (Int.ofNat 812340956668768128), (Int.negSucc 49148977509877247), (Int.ofNat 48446996410368)], [(Int.ofNat 0), (Int.negSucc 71626154791420799), (Int.ofNat 476076750984529344), (Int.ofNat 3183568818124485024), (Int.negSucc 1792135989427479839), (Int.negSucc 16620670375904229407), (Int.negSucc 12159925325740967039), (Int.negSucc 690093281258966303), (Int.ofNat 14687404535318845536), (Int.negSucc 1019258427934608479), (Int.ofNat 60339577453046784), (Int.negSucc 7042241667594239), (Int.ofNat 30680538439680)], [(Int.ofNat 0), (Int.ofNat 76713485250680640), (Int.negSucc 693557420427667871), (Int.negSucc 3360357285247672415), (Int.ofNat 3415771912297312224), (Int.ofNat 17708035394697636384), (Int.ofNat 21574134763622147808), (Int.ofNat 9164938078434054816), (Int.negSucc 16834462243789039775), (Int.negSucc 4098603467482195679), (Int.ofNat 691232417014534848), (Int.negSucc 35308423429249535), (Int.negSucc 130324912008191), (Int.ofNat 1131953651712)], [(Int.ofNat 0), (Int.negSucc 61540641681861119), (Int.ofNat 736259682543720576), (Int.ofNat 2647222646872648224), (Int.negSucc 3777905757512121983), (Int.negSucc 16263021698507560319), (Int.negSucc 30167838783872935487), (Int.negSucc 15507602681538388127), (Int.ofNat 4944667541499569760), (Int.ofNat 14044804677010778880), (Int.negSucc 1464753994472233823), (Int.ofNat 96913037732419968), (Int.negSucc 5060386649660927), (Int.ofNat 18236224880640)], [(Int.ofNat 0), (Int.ofNat 37100361252059520), (Int.negSucc 582417907141783487), (Int.negSucc 1580299147328584415), (Int.ofNat 2875591903549683744), (Int.ofNat 14084329661480941440), (Int.ofNat 31378761092400373824), (Int.ofNat 21260688783436808544), (Int.ofNat 10471956042304775520), (Int.negSucc 16255744085477174975), (Int.negSucc 1499910136663084223), (Int.ofNat 292016222543985792), (Int.negSucc 11010707794060031), (Int.negSucc 98062807252991)], [(Int.ofNat 0), (Int.negSucc 16697376671725439), (Int.ofNat 346223784439811136), (Int.ofNat 726546322007110752), (Int.negSucc 1671950703680132639), (Int.negSucc 11400782362608534911), (Int.negSucc 25034064405515376479), (Int.negSucc 26145987677661593951), (Int.negSucc 16443911471053468415), (Int.ofNat 4240155160757896800), (Int.ofNat 7430438932961020320), (Int.negSucc 771934276235279903), (Int.ofNat 41949534433024896), (Int.negSucc 1159903242184703)], [(Int.ofNat 0), (Int.ofNat 5511681132038400), (Int.negSucc 154258465576856831), (Int.negSucc 263360270167708895), (Int.ofNat 848277588951339648), (Int.ofNat 7980508122671035392), (Int.ofNat 16559385382840742400), (Int.ofNat 25301409795592618848), (Int.ofNat 15153719151634543968), (Int.ofNat 8823819121577402016), (Int.negSucc 7905467720671572959), (Int.negSucc 355796327234715743), (Int.ofNat 69232330301213568), (Int.negSucc 1463640030062591)], [(Int.ofNat 0), (Int.negSucc 1291073557460159), (Int.ofNat 50786437252018848), (Int.ofNat 77580044078457888), (Int.negSucc 422272009662549695), (Int.negSucc 4545366412220547551), (Int.negSucc 9929921326524026207), (Int.negSucc 17970632258038171775), (Int.negSucc 13379922356321175071), (Int.negSucc 10906457471875918559), (Int.ofNat 992428166063805696), (Int.ofNat 2321421938320477632), (Int.negSucc 188433917062789247), (Int.ofNat 6096218802706944)], [(Int.ofNat 0), (Int.ofNat 202336633514880), (Int.negSucc 11994432034200383), (Int.negSucc 18858423979540319), (Int.ofNat 199176548395247232), (Int.ofNat 2057383264388841696), (Int.ofNat 5532176793416278848), (Int.ofNat 9518205373479315840), (Int.ofNat 10922236669048315104), (Int.ofNat 6719268588483305376), (Int.ofNat 4422868288951780800), (Int.negSucc 2001303159243044543), (Int.negSucc 77413184018979839), (Int.ofNat 8192625803587584)], [(Int.ofNat 0), (Int.negSucc 18927387156479), (Int.ofNat 1922389774396032), (Int.ofNat 3634495351213056), (Int.negSucc 77342327111540543), (Int.negSucc 736558640246386847), (Int.negSucc 2682817011818903903), (Int.negSucc 4119384204750564383), (Int.negSucc 6648815561069668607), (Int.negSucc 3814261159550374655), (Int.negSucc 3880938883839413183), (Int.negSucc 170072720583800255), (Int.ofNat 395352449421935616), (Int.negSucc 17145851529194495)], [(Int.ofNat 0), (Int.ofNat 793816647360), (Int.negSucc 187211963313503), (Int.negSucc 493729704666623), (Int.ofNat 22006620583449696), (Int.ofNat 206896012049427936), (Int.ofNat 1037414671193200032), (Int.ofNat 1666571061560876640), (Int.ofNat 2751963353399774592), (Int.ofNat 2462939142372470592), (Int.ofNat 1542507722318839104), (Int.ofNat 1161471236492882304), (Int.negSucc 226242665749958399), (Int.negSucc 10603511211709439)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8355825422208), (Int.ofNat 38272270954752), (Int.negSucc 4198438454389343), (Int.negSucc 44195040623498399), (Int.negSucc 298517453401462271), (Int.negSucc 641877700457344319), (Int.negSucc 805489176452255999), (Int.negSucc 1237789877183139455), (Int.negSucc 511432324300225151), (Int.negSucc 664574313916423295), (Int.negSucc 92832788508549119), (Int.ofNat 26453823889895424)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1051563904127), (Int.ofNat 476696003334048), (Int.ofNat 6681868827989472), (Int.ofNat 60020951250570048), (Int.ofNat 202417122507173568), (Int.ofNat 210891164889790080), (Int.ofNat 373292164620603648), (Int.ofNat 259984410726461184), (Int.ofNat 148299410555320320), (Int.ofNat 135226061350695936), (Int.negSucc 6371583795081215)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 24264739054079), (Int.negSucc 622631466662399), (Int.negSucc 7725114532997567), (Int.negSucc 44205244726684607), (Int.negSucc 61509082240843775), (Int.negSucc 62861046906991103), (Int.negSucc 103439017425014783), (Int.negSucc 21601929644017919), (Int.negSucc 44581602591977471), (Int.negSucc 7922192186105855)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 26089228502208), (Int.ofNat 538747983266112), (Int.ofNat 5772107718315648), (Int.ofNat 15075141960049920), (Int.ofNat 8358458785894656), (Int.ofNat 19254988707957504), (Int.ofNat 10065279583042560), (Int.ofNat 3639373050756096), (Int.ofNat 4726659894128640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 13131032508287), (Int.negSucc 359380736682623), (Int.negSucc 2143079325324287), (Int.negSucc 1922319665162495), (Int.negSucc 1085942391510527), (Int.negSucc 2832295338948095), (Int.ofNat 202107513968640), (Int.negSucc 725526031564799)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 4988064810240), (Int.ofNat 128419642867968), (Int.ofNat 320040214373376), (Int.ofNat 4342242567168), (Int.ofNat 204499977661440), (Int.ofNat 45345376972800)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1017393799679), (Int.negSucc 17411473884671), (Int.negSucc 6801806545919)]]

theorem h1n19_arithmetic_row0 :
    (BiPoly.mul h1p4 h1p18).getD 0 []=h1p19.getD 0 [] := by
  decide +kernel

theorem h1n19_arithmetic_row1 :
    (BiPoly.mul h1p4 h1p18).getD 1 []=h1p19.getD 1 [] := by
  decide +kernel

theorem h1n19_arithmetic_row2 :
    (BiPoly.mul h1p4 h1p18).getD 2 []=h1p19.getD 2 [] := by
  decide +kernel

theorem h1n19_arithmetic_row3 :
    (BiPoly.mul h1p4 h1p18).getD 3 []=h1p19.getD 3 [] := by
  decide +kernel

theorem h1n19_arithmetic_row4 :
    (BiPoly.mul h1p4 h1p18).getD 4 []=h1p19.getD 4 [] := by
  decide +kernel

theorem h1n19_arithmetic_row5 :
    (BiPoly.mul h1p4 h1p18).getD 5 []=h1p19.getD 5 [] := by
  decide +kernel

theorem h1n19_arithmetic_row6 :
    (BiPoly.mul h1p4 h1p18).getD 6 []=h1p19.getD 6 [] := by
  decide +kernel

theorem h1n19_arithmetic_row7 :
    (BiPoly.mul h1p4 h1p18).getD 7 []=h1p19.getD 7 [] := by
  decide +kernel

theorem h1n19_arithmetic_row8 :
    (BiPoly.mul h1p4 h1p18).getD 8 []=h1p19.getD 8 [] := by
  decide +kernel

theorem h1n19_arithmetic_row9 :
    (BiPoly.mul h1p4 h1p18).getD 9 []=h1p19.getD 9 [] := by
  decide +kernel

theorem h1n19_arithmetic_row10 :
    (BiPoly.mul h1p4 h1p18).getD 10 []=h1p19.getD 10 [] := by
  decide +kernel

theorem h1n19_arithmetic_row11 :
    (BiPoly.mul h1p4 h1p18).getD 11 []=h1p19.getD 11 [] := by
  decide +kernel

theorem h1n19_arithmetic_row12 :
    (BiPoly.mul h1p4 h1p18).getD 12 []=h1p19.getD 12 [] := by
  decide +kernel

theorem h1n19_arithmetic_row13 :
    (BiPoly.mul h1p4 h1p18).getD 13 []=h1p19.getD 13 [] := by
  decide +kernel

theorem h1n19_arithmetic_row14 :
    (BiPoly.mul h1p4 h1p18).getD 14 []=h1p19.getD 14 [] := by
  decide +kernel

theorem h1n19_arithmetic_row15 :
    (BiPoly.mul h1p4 h1p18).getD 15 []=h1p19.getD 15 [] := by
  decide +kernel

theorem h1n19_arithmetic_row16 :
    (BiPoly.mul h1p4 h1p18).getD 16 []=h1p19.getD 16 [] := by
  decide +kernel

theorem h1n19_arithmetic_row17 :
    (BiPoly.mul h1p4 h1p18).getD 17 []=h1p19.getD 17 [] := by
  decide +kernel

theorem h1n19_arithmetic_row18 :
    (BiPoly.mul h1p4 h1p18).getD 18 []=h1p19.getD 18 [] := by
  decide +kernel

theorem h1n19_arithmetic_row19 :
    (BiPoly.mul h1p4 h1p18).getD 19 []=h1p19.getD 19 [] := by
  decide +kernel

theorem h1n19_arithmetic_row20 :
    (BiPoly.mul h1p4 h1p18).getD 20 []=h1p19.getD 20 [] := by
  decide +kernel

theorem h1n19_arithmetic_row21 :
    (BiPoly.mul h1p4 h1p18).getD 21 []=h1p19.getD 21 [] := by
  decide +kernel

theorem h1n19_arithmetic : BiPoly.mul h1p4 h1p18=h1p19 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<22 at hk
    have hf : ∀ j : Fin 22, (BiPoly.mul h1p4 h1p18).getD j.val []=h1p19.getD j.val [] :=
      (fun j => Fin.cases h1n19_arithmetic_row0 (fun j => Fin.cases h1n19_arithmetic_row1 (fun j => Fin.cases h1n19_arithmetic_row2 (fun j => Fin.cases h1n19_arithmetic_row3 (fun j => Fin.cases h1n19_arithmetic_row4 (fun j => Fin.cases h1n19_arithmetic_row5 (fun j => Fin.cases h1n19_arithmetic_row6 (fun j => Fin.cases h1n19_arithmetic_row7 (fun j => Fin.cases h1n19_arithmetic_row8 (fun j => Fin.cases h1n19_arithmetic_row9 (fun j => Fin.cases h1n19_arithmetic_row10 (fun j => Fin.cases h1n19_arithmetic_row11 (fun j => Fin.cases h1n19_arithmetic_row12 (fun j => Fin.cases h1n19_arithmetic_row13 (fun j => Fin.cases h1n19_arithmetic_row14 (fun j => Fin.cases h1n19_arithmetic_row15 (fun j => Fin.cases h1n19_arithmetic_row16 (fun j => Fin.cases h1n19_arithmetic_row17 (fun j => Fin.cases h1n19_arithmetic_row18 (fun j => Fin.cases h1n19_arithmetic_row19 (fun j => Fin.cases h1n19_arithmetic_row20 (fun j => Fin.cases h1n19_arithmetic_row21 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h1n19 : h1e19.toBi mapPolyEnv=h1p19 := by
  change BiPoly.mul (h1e4.toBi mapPolyEnv) (h1e18.toBi mapPolyEnv)=h1p19
  rw [h1n4, h1n18]
  exact h1n19_arithmetic

#print axioms h1n19_arithmetic
end StackSorting.RationalLift
