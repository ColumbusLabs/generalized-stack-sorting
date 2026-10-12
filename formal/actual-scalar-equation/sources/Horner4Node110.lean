import BivariateRowEquality
import Horner4Base
import Horner4Node109
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p110 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 281002897996848000000), (Int.ofNat 1711593524635802352000), (Int.negSucc 191720773511198383679), (Int.negSucc 11480920883304396287039), (Int.ofNat 641599025102696914560), (Int.ofNat 24213253703752889256960), (Int.negSucc 42606769279475050559), (Int.negSucc 13755651964775423841599)], [(Int.ofNat 0), (Int.negSucc 3387229747483487039999), (Int.negSucc 19424910345595240092479), (Int.ofNat 8418970836060774380064), (Int.ofNat 138994045824691646962560), (Int.negSucc 23264327056806900227231), (Int.negSucc 269651522043509421413951), (Int.ofNat 27521480039456608722144), (Int.ofNat 134275288313283024135168), (Int.negSucc 7162394671061803375199)], [(Int.ofNat 0), (Int.ofNat 18989270161566448204800), (Int.ofNat 102974838244921751271840), (Int.negSucc 71861918540633064442223), (Int.negSucc 766260072999489902236703), (Int.ofNat 176585515790911300794384), (Int.ofNat 1364114932801554986662176), (Int.negSucc 205469262698990714205263), (Int.negSucc 555006539563897813322975), (Int.ofNat 8254728461499332837040), (Int.ofNat 1561644129330665204544)], [(Int.ofNat 0), (Int.negSucc 65702097773543629382399), (Int.negSucc 338922904993425391823279), (Int.ofNat 300472232606306608683384), (Int.ofNat 2571500167243183164856824), (Int.negSucc 562694883215828902691543), (Int.negSucc 4150419517024701193546199), (Int.ofNat 514965701386274860443528), (Int.ofNat 1261261393498267580531016), (Int.ofNat 255364307499741174717912), (Int.negSucc 39935956944799135065527), (Int.ofNat 1657474727461915355136)], [(Int.ofNat 0), (Int.ofNat 156987550899591982430400), (Int.ofNat 776337442163722594052640), (Int.negSucc 759070676127657061308959), (Int.negSucc 5912845711010576405706527), (Int.ofNat 599089199728413235506768), (Int.ofNat 8467161351781655499354288), (Int.ofNat 149650049295777122264448), (Int.negSucc 1684646947521594785165759), (Int.negSucc 1398876051763683370074671), (Int.ofNat 176961524678796452339664), (Int.negSucc 11107096464582883660031), (Int.ofNat 353136865859941413888)], [(Int.ofNat 0), (Int.negSucc 274599599702090045104799), (Int.negSucc 1314327040646080074585119), (Int.ofNat 1246381842615839445266712), (Int.ofNat 9919721625660983553104232), (Int.ofNat 1562789756480388284177640), (Int.negSucc 12037375505219752275006383), (Int.negSucc 4120610462621981396865503), (Int.ofNat 1149424762068586488309480), (Int.ofNat 3317186944377179016421608), (Int.negSucc 130451452219914306740351), (Int.negSucc 5103408058644735120167), (Int.negSucc 174505750686790241471), (Int.ofNat 23119989287617525248)], [(Int.ofNat 0), (Int.ofNat 363644287782127449804000), (Int.ofNat 1703628630019429435541880), (Int.negSucc 1322282443286072508701435), (Int.negSucc 12587324416567782822402479), (Int.negSucc 7509795204343210494449687), (Int.ofNat 11311971424874456033278656), (Int.ofNat 11878473887693764784046576), (Int.ofNat 665742478111341906248352), (Int.negSucc 3916221234743555428775255), (Int.negSucc 958397809414569212258711), (Int.ofNat 144308481947416728259164), (Int.negSucc 7616988093336911027279), (Int.ofNat 140030442759559106304), (Int.negSucc 124216746865136639)], [(Int.ofNat 0), (Int.negSucc 371817254630048645858399), (Int.negSucc 1726380691214279542233119), (Int.ofNat 766898581928140223692704), (Int.ofNat 12306524926414786689346524), (Int.ofNat 15513853199670536244337116), (Int.negSucc 4179678126648556984968563), (Int.negSucc 18653728438408467658836275), (Int.negSucc 4255129148648230443388931), (Int.ofNat 1203644096816135497243596), (Int.ofNat 3018755630708488034862732), (Int.negSucc 246128013808625254247459), (Int.ofNat 8657846470414911995136), (Int.negSucc 289129781764197970271), (Int.ofNat 4030539416540537472)], [(Int.ofNat 0), (Int.ofNat 296597635549920414655200), (Int.ofNat 1382617791059106383009880), (Int.ofNat 75491684850486116525004), (Int.negSucc 9305343929315040009646847), (Int.negSucc 20611717923270745212871751), (Int.negSucc 7420898078294659530661907), (Int.ofNat 17424657275244090950966688), (Int.ofNat 9439239082634394491537412), (Int.ofNat 3176826422930894665408104), (Int.negSucc 3549403943602010857106771), (Int.negSucc 282642447353724605538443), (Int.ofNat 48374359429326801504732), (Int.negSucc 1962810611073983750927), (Int.ofNat 25778068716882777408)], [(Int.ofNat 0), (Int.negSucc 185171945510831317099199), (Int.negSucc 877263393005382400447439), (Int.negSucc 622930580107052598738095), (Int.ofNat 5384825166683900284893180), (Int.ofNat 19324911978512840931363060), (Int.ofNat 17583127762912793658164544), (Int.negSucc 6758569245585522429814799), (Int.negSucc 13002521377929483701450003), (Int.negSucc 5764848762427790577180155), (Int.ofNat 660017243950047823031736), (Int.ofNat 1350900798511155359096088), (Int.negSucc 99242699513391118716311), (Int.ofNat 2286880437182634500808), (Int.negSucc 14829171707511967679)], [(Int.ofNat 0), (Int.ofNat 90171973247259182606400), (Int.ofNat 438306956778939019500720), (Int.ofNat 648725480598064272127152), (Int.negSucc 2337461596571618917736627), (Int.negSucc 13217146485477639369846755), (Int.negSucc 20676185577843774253374767), (Int.negSucc 6631621503615191025176807), (Int.ofNat 10611157145729367562282572), (Int.ofNat 5802935032042036459748856), (Int.ofNat 3074751557674977353052744), (Int.negSucc 1486047220916910212601503), (Int.negSucc 58972804517095789170479), (Int.ofNat 9408312054792457782804), (Int.negSucc 252407308587597507743)], [(Int.ofNat 0), (Int.negSucc 33889018035576649895999), (Int.negSucc 169595802191379303693359), (Int.negSucc 381621758086814183708423), (Int.ofNat 771475827418783381309800), (Int.ofNat 6701891858517218712774180), (Int.ofNat 16326084146602151243788632), (Int.ofNat 14308366200662396942383440), (Int.negSucc 2720629181003262399230195), (Int.negSucc 4498583384196404511175787), (Int.negSucc 3905959920059428629587723), (Int.ofNat 33213150214834759521684), (Int.ofNat 327767839387771725082920), (Int.negSucc 14060872346219478257051), (Int.negSucc 18914643185282029367)], [(Int.ofNat 0), (Int.ofNat 9636758701087888857600), (Int.ofNat 49156357379321747818320), (Int.ofNat 132460266273883147355448), (Int.negSucc 253128783205473672384719), (Int.negSucc 2616228055257761607140543), (Int.negSucc 9152010478097090440088543), (Int.negSucc 13651126374849295867137155), (Int.negSucc 4841801972889946598175167), (Int.ofNat 2226340775080720488263724), (Int.ofNat 2149546274063322418312104), (Int.ofNat 1335535896817605298385988), (Int.negSucc 277406011312431372931667), (Int.negSucc 14395839682561258004003), (Int.ofNat 963822214554683017572)], [(Int.ofNat 0), (Int.negSucc 2004672656759667568799), (Int.negSucc 9963093090638313887999), (Int.negSucc 16550661388815831752615), (Int.ofNat 138598254762303874900128), (Int.ofNat 913640881534662985970712), (Int.ofNat 3710073971362248308598552), (Int.ofNat 8425340985165051205880940), (Int.ofNat 7352583668911196006016684), (Int.ofNat 532453083914074769164008), (Int.negSucc 422147329929278626545431), (Int.negSucc 1201210988147136127243259), (Int.negSucc 86431951596439087229279), (Int.ofNat 38228747581557711990756), (Int.negSucc 141263106329063194847)], [(Int.ofNat 0), (Int.ofNat 287765828214812632800), (Int.ofNat 1168447756555413063000), (Int.negSucc 8558577808243217856923), (Int.negSucc 89829649167078099931655), (Int.negSucc 376390496749501192696967), (Int.negSucc 1162142614028763550425335), (Int.negSucc 3555557772545133370590851), (Int.negSucc 5439057408530779834218071), (Int.negSucc 2247358693237589438392583), (Int.negSucc 338087818190025459666575), (Int.ofNat 316159781003113417843812), (Int.ofNat 275315519501571735849300), (Int.negSucc 13288701877980070507271), (Int.negSucc 1726826571093741687215)], [(Int.ofNat 0), (Int.negSucc 25475204228455317599), (Int.negSucc 5228249380399660799), (Int.ofNat 5580934939004688700176), (Int.ofNat 43856341106306454523980), (Int.ofNat 178948642002815346010092), (Int.ofNat 366167345507506424823276), (Int.ofNat 1030966010943971176505328), (Int.ofNat 2525916187175949020509056), (Int.ofNat 2169642819892607230558392), (Int.ofNat 576956469699069426459000), (Int.ofNat 175903269779367352842948), (Int.negSucc 148547850008904394358975), (Int.negSucc 21893834948609388617423), (Int.ofNat 1009656681033091511448)], [(Int.ofNat 0), (Int.ofNat 1048192796870076000), (Int.negSucc 22023182729628135239), (Int.negSucc 1605101393046655302563), (Int.negSucc 14678862388539503905295), (Int.negSucc 72742129543693305521423), (Int.negSucc 151505998931105191829531), (Int.negSucc 228488384615247217821203), (Int.negSucc 744266107313637558771203), (Int.negSucc 1185951788283708848125043), (Int.negSucc 545600448150615451546883), (Int.negSucc 205055843403307231050551), (Int.negSucc 9636748809834919815503), (Int.ofNat 21171478637032309082592), (Int.ofNat 979309026263005731792)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3185475314516474160), (Int.ofNat 267372190772274457632), (Int.ofNat 3294433662586489306044), (Int.ofNat 21362076054985144848396), (Int.ofNat 62520664154874338469552), (Int.ofNat 65599985584131357843972), (Int.ofNat 127928374276561236386424), (Int.ofNat 393584163664043385995148), (Int.ofNat 333161876639923789899096), (Int.ofNat 121733912165068951238016), (Int.ofNat 46344332774857544636184), (Int.negSucc 3047420752393263284159), (Int.negSucc 1083302483706908932175)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 155483056368525599), (Int.negSucc 24941462541761628071), (Int.negSucc 475164808380534256019), (Int.negSucc 4225329682400932085771), (Int.negSucc 18853223129115447468887), (Int.negSucc 28069594765825891267619), (Int.negSucc 13494208147168047448355), (Int.negSucc 71197944178403796601895), (Int.negSucc 126567310233046252942511), (Int.negSucc 60037726936783752771983), (Int.negSucc 25524990017216020367135), (Int.negSucc 4504276593193337250191), (Int.ofNat 112114360178437414464)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 1012135830530634720), (Int.ofNat 39784831326743494968), (Int.ofNat 525080483022901494636), (Int.ofNat 3691157113864575294408), (Int.ofNat 9496303181323048292076), (Int.ofNat 4598697908541363320880), (Int.ofNat 3040075352583502292016), (Int.ofNat 27155103783068290799880), (Int.ofNat 22762284069982631775552), (Int.ofNat 8757241598165429924928), (Int.ofNat 2936044531796194868544), (Int.ofNat 253358708548750704864)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1466691568018204319), (Int.negSucc 35912542708329390647), (Int.negSucc 430003942087548709439), (Int.negSucc 1969528682550406530599), (Int.negSucc 2334004389972535202639), (Int.ofNat 936642964851341770464), (Int.negSucc 1993007218678212618863), (Int.negSucc 5446776390437917068767), (Int.negSucc 2428857025103444433407), (Int.negSucc 872846248311329853887), (Int.negSucc 131007039114695807231)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 959339398462730784), (Int.ofNat 25049839304582696232), (Int.ofNat 227121261510494285856), (Int.ofNat 580798893243061447272), (Int.ofNat 56000789868176417664), (Int.negSucc 406854838201282000847), (Int.ofNat 613970687727132048576), (Int.ofNat 508605166389112804224), (Int.ofNat 167185788573831856704), (Int.ofNat 25150691852252091072)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 415451046702893759), (Int.negSucc 11949969761905951151), (Int.negSucc 68376770673500318399), (Int.negSucc 74153651583042231695), (Int.ofNat 92000853526997928384), (Int.ofNat 21135566614979500992), (Int.negSucc 61883721445497275519), (Int.negSucc 23047742757518126783), (Int.negSucc 1686038608409195519)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 126142825997232000), (Int.ofNat 3116110738021625952), (Int.ofNat 10342626631963694784), (Int.negSucc 2096021078513761823), (Int.negSucc 13523768685773954495), (Int.ofNat 2960703259317698112), (Int.ofNat 1686038608409195520)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 17330998159408895), (Int.negSucc 328743514892129471), (Int.negSucc 586199705907326975), (Int.ofNat 1118489210115387840)]]

theorem h4n110_arithmetic_row0 :
    (BiPoly.mul h4p5 h4p109).getD 0 []=h4p110.getD 0 [] := by
  decide +kernel

theorem h4n110_arithmetic_row1 :
    (BiPoly.mul h4p5 h4p109).getD 1 []=h4p110.getD 1 [] := by
  decide +kernel

theorem h4n110_arithmetic_row2 :
    (BiPoly.mul h4p5 h4p109).getD 2 []=h4p110.getD 2 [] := by
  decide +kernel

theorem h4n110_arithmetic_row3 :
    (BiPoly.mul h4p5 h4p109).getD 3 []=h4p110.getD 3 [] := by
  decide +kernel

theorem h4n110_arithmetic_row4 :
    (BiPoly.mul h4p5 h4p109).getD 4 []=h4p110.getD 4 [] := by
  decide +kernel

theorem h4n110_arithmetic_row5 :
    (BiPoly.mul h4p5 h4p109).getD 5 []=h4p110.getD 5 [] := by
  decide +kernel

theorem h4n110_arithmetic_row6 :
    (BiPoly.mul h4p5 h4p109).getD 6 []=h4p110.getD 6 [] := by
  decide +kernel

theorem h4n110_arithmetic_row7 :
    (BiPoly.mul h4p5 h4p109).getD 7 []=h4p110.getD 7 [] := by
  decide +kernel

theorem h4n110_arithmetic_row8 :
    (BiPoly.mul h4p5 h4p109).getD 8 []=h4p110.getD 8 [] := by
  decide +kernel

theorem h4n110_arithmetic_row9 :
    (BiPoly.mul h4p5 h4p109).getD 9 []=h4p110.getD 9 [] := by
  decide +kernel

theorem h4n110_arithmetic_row10 :
    (BiPoly.mul h4p5 h4p109).getD 10 []=h4p110.getD 10 [] := by
  decide +kernel

theorem h4n110_arithmetic_row11 :
    (BiPoly.mul h4p5 h4p109).getD 11 []=h4p110.getD 11 [] := by
  decide +kernel

theorem h4n110_arithmetic_row12 :
    (BiPoly.mul h4p5 h4p109).getD 12 []=h4p110.getD 12 [] := by
  decide +kernel

theorem h4n110_arithmetic_row13 :
    (BiPoly.mul h4p5 h4p109).getD 13 []=h4p110.getD 13 [] := by
  decide +kernel

theorem h4n110_arithmetic_row14 :
    (BiPoly.mul h4p5 h4p109).getD 14 []=h4p110.getD 14 [] := by
  decide +kernel

theorem h4n110_arithmetic_row15 :
    (BiPoly.mul h4p5 h4p109).getD 15 []=h4p110.getD 15 [] := by
  decide +kernel

theorem h4n110_arithmetic_row16 :
    (BiPoly.mul h4p5 h4p109).getD 16 []=h4p110.getD 16 [] := by
  decide +kernel

theorem h4n110_arithmetic_row17 :
    (BiPoly.mul h4p5 h4p109).getD 17 []=h4p110.getD 17 [] := by
  decide +kernel

theorem h4n110_arithmetic_row18 :
    (BiPoly.mul h4p5 h4p109).getD 18 []=h4p110.getD 18 [] := by
  decide +kernel

theorem h4n110_arithmetic_row19 :
    (BiPoly.mul h4p5 h4p109).getD 19 []=h4p110.getD 19 [] := by
  decide +kernel

theorem h4n110_arithmetic_row20 :
    (BiPoly.mul h4p5 h4p109).getD 20 []=h4p110.getD 20 [] := by
  decide +kernel

theorem h4n110_arithmetic_row21 :
    (BiPoly.mul h4p5 h4p109).getD 21 []=h4p110.getD 21 [] := by
  decide +kernel

theorem h4n110_arithmetic_row22 :
    (BiPoly.mul h4p5 h4p109).getD 22 []=h4p110.getD 22 [] := by
  decide +kernel

theorem h4n110_arithmetic_row23 :
    (BiPoly.mul h4p5 h4p109).getD 23 []=h4p110.getD 23 [] := by
  decide +kernel

theorem h4n110_arithmetic_row24 :
    (BiPoly.mul h4p5 h4p109).getD 24 []=h4p110.getD 24 [] := by
  decide +kernel

theorem h4n110_arithmetic : BiPoly.mul h4p5 h4p109=h4p110 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<25 at hk
    have hf : ∀ j : Fin 25, (BiPoly.mul h4p5 h4p109).getD j.val []=h4p110.getD j.val [] :=
      (fun j => Fin.cases h4n110_arithmetic_row0 (fun j => Fin.cases h4n110_arithmetic_row1 (fun j => Fin.cases h4n110_arithmetic_row2 (fun j => Fin.cases h4n110_arithmetic_row3 (fun j => Fin.cases h4n110_arithmetic_row4 (fun j => Fin.cases h4n110_arithmetic_row5 (fun j => Fin.cases h4n110_arithmetic_row6 (fun j => Fin.cases h4n110_arithmetic_row7 (fun j => Fin.cases h4n110_arithmetic_row8 (fun j => Fin.cases h4n110_arithmetic_row9 (fun j => Fin.cases h4n110_arithmetic_row10 (fun j => Fin.cases h4n110_arithmetic_row11 (fun j => Fin.cases h4n110_arithmetic_row12 (fun j => Fin.cases h4n110_arithmetic_row13 (fun j => Fin.cases h4n110_arithmetic_row14 (fun j => Fin.cases h4n110_arithmetic_row15 (fun j => Fin.cases h4n110_arithmetic_row16 (fun j => Fin.cases h4n110_arithmetic_row17 (fun j => Fin.cases h4n110_arithmetic_row18 (fun j => Fin.cases h4n110_arithmetic_row19 (fun j => Fin.cases h4n110_arithmetic_row20 (fun j => Fin.cases h4n110_arithmetic_row21 (fun j => Fin.cases h4n110_arithmetic_row22 (fun j => Fin.cases h4n110_arithmetic_row23 (fun j => Fin.cases h4n110_arithmetic_row24 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n110 : h4e110.toBi mapPolyEnv=h4p110 := by
  change BiPoly.mul (h4e5.toBi mapPolyEnv) (h4e109.toBi mapPolyEnv)=h4p110
  rw [h4n5, h4n109]
  exact h4n110_arithmetic

#print axioms h4n110_arithmetic
end StackSorting.RationalLift
