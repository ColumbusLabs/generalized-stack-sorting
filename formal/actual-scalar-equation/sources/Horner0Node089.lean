import BivariateRowEquality
import Horner0Base
import Horner0Node088
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p89 : BiPoly.Poly := [[(Int.negSucc 3047094380317967999), (Int.negSucc 23041129209824854079), (Int.negSucc 30610893932994127679), (Int.ofNat 81867465770634728640), (Int.ofNat 93995362425514772160), (Int.negSucc 113215242508439702399)], [(Int.ofNat 28138683035710840320), (Int.ofNat 214305360204675348864), (Int.ofNat 299535813121673472192), (Int.negSucc 695785089774395981951), (Int.negSucc 805285260112168113983), (Int.ofNat 999402380417680958592), (Int.negSucc 82012114593791654399)], [(Int.negSucc 122490739466336800799), (Int.negSucc 914568449791754854799), (Int.negSucc 1306051557167662231103), (Int.ofNat 2599638032215790937216), (Int.ofNat 3163690352402940331008), (Int.negSucc 3613361606179971879599), (Int.ofNat 376047461513470135968), (Int.negSucc 19228042866295747583)], [(Int.ofNat 333034869074575502880), (Int.ofNat 2370529061917325925840), (Int.ofNat 3422574611991899084736), (Int.negSucc 5303388315234446096831), (Int.negSucc 7425063230627130358751), (Int.ofNat 6407307708811182892656), (Int.negSucc 128001042594878326271), (Int.ofNat 4758888925427275584), (Int.negSucc 1412503903510013951)], [(Int.negSucc 629608252612856856479), (Int.negSucc 4175762761410723086831), (Int.negSucc 6160521218515950497471), (Int.ofNat 5692992147739330409376), (Int.ofNat 11424352970342643255360), (Int.negSucc 3851725492017316862927), (Int.negSucc 2493520439263811845055), (Int.ofNat 245244476415450519936), (Int.negSucc 7691066592629088383), (Int.ofNat 7528287688796160)], [(Int.ofNat 870246329286923647920), (Int.ofNat 5318910198960849054504), (Int.ofNat 8297407770715166664888), (Int.negSucc 1085938468782357228479), (Int.negSucc 11486282331718135581119), (Int.negSucc 6241100088281355064727), (Int.ofNat 6333734400143648575896), (Int.negSucc 379677976997651073071), (Int.ofNat 10616896354245225984), (Int.negSucc 245986090628698367)], [(Int.negSucc 900144185524400585999), (Int.negSucc 5109120751681761355175), (Int.negSucc 8907175252249664921039), (Int.negSucc 6050896748754581406431), (Int.ofNat 5979401164621389333744), (Int.ofNat 15401373138608113471560), (Int.negSucc 5241307081335701441615), (Int.negSucc 672470550795150332687), (Int.ofNat 60095465964604782816), (Int.negSucc 1467391047250490111)], [(Int.ofNat 702258635081865325680), (Int.ofNat 3823674003879450513144), (Int.ofNat 7936755173119428185928), (Int.ofNat 10210910146744130154096), (Int.ofNat 2089239155400256830192), (Int.negSucc 13729629052164244545479), (Int.negSucc 2557754003794767475943), (Int.ofNat 2249001733412619967632), (Int.negSucc 87008179463090381567), (Int.negSucc 48579060475827455)], [(Int.negSucc 412095219971251310639), (Int.negSucc 2285903344820744345639), (Int.negSucc 5939369918553610723295), (Int.negSucc 9442856430923684234927), (Int.negSucc 7302412920754451591759), (Int.ofNat 3697252201540821149688), (Int.ofNat 8533864333912566716064), (Int.negSucc 1635124428113310659567), (Int.negSucc 136111693483026723647), (Int.ofNat 7905961075633477824)], [(Int.ofNat 179683754821986115440), (Int.ofNat 1105705274505531754872), (Int.ofNat 3676311683562921778128), (Int.ofNat 6279315764480200653120), (Int.ofNat 7367114566386712289736), (Int.ofNat 4263311560377663132720), (Int.negSucc 6225597693518087430215), (Int.negSucc 996566424093373152767), (Int.ofNat 327457163084583916680), (Int.ofNat 298397492051809488)], [(Int.negSucc 56868726759196769039), (Int.negSucc 430482639181514455511), (Int.negSucc 1824560881543341086183), (Int.negSucc 3422123869791088684439), (Int.negSucc 4648784351687620252847), (Int.negSucc 5481736124432116034495), (Int.ofNat 409913622208215225960), (Int.ofNat 2151859646182905573672), (Int.negSucc 97462887247594085663), (Int.negSucc 17474285810108562335)], [(Int.ofNat 12550722566158398960), (Int.ofNat 131593828120886830776), (Int.ofNat 699594139013304833448), (Int.ofNat 1617351404235062803200), (Int.ofNat 2196561472471183689264), (Int.ofNat 3157862310543524473728), (Int.ofNat 2258583878616943671984), (Int.negSucc 958755582917508937199), (Int.negSucc 217881415826484928463), (Int.ofNat 7610556919172609952)], [(Int.negSucc 1800367080968554799), (Int.negSucc 30286302102811812263), (Int.negSucc 198967459292976433775), (Int.negSucc 637479018883351120943), (Int.negSucc 897519466209145802687), (Int.negSucc 1145659831100363044655), (Int.negSucc 1657955117282400908735), (Int.negSucc 281551960255471955567), (Int.ofNat 188652337447923459792), (Int.ofNat 12133768469082599520)], [(Int.ofNat 146376022151123040), (Int.ofNat 4932647943025655136), (Int.ofNat 39984759480700141992), (Int.ofNat 191478175000567340352), (Int.ofNat 333183300034826553000), (Int.ofNat 318906869744687634864), (Int.ofNat 567924594643862376768), (Int.ofNat 442806767866966237344), (Int.negSucc 8686678901796442079), (Int.negSucc 10215323500995607103)], [(Int.negSucc 4784094042108479), (Int.negSucc 510619865039597807), (Int.negSucc 5306201828642339063), (Int.negSucc 39954721293559765079), (Int.negSucc 101216714987815096607), (Int.negSucc 89888950768790776607), (Int.negSucc 103032580713378107615), (Int.negSucc 179927089424699997023), (Int.negSucc 50647918850340736895), (Int.negSucc 382234996153950335)], [(Int.ofNat 0), (Int.ofNat 25622532429278976), (Int.ofNat 413671764534083424), (Int.ofNat 5213122877955977424), (Int.ofNat 21700161195018948144), (Int.ofNat 25724793177845123904), (Int.ofNat 10603296802654487136), (Int.ofNat 31886384288886615744), (Int.ofNat 25019965872084288960), (Int.ofNat 2879989774227075456)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 14239684785885119), (Int.negSucc 349770623760823535), (Int.negSucc 2859502004380625327), (Int.negSucc 5447759176653926975), (Int.negSucc 1604841813446107967), (Int.negSucc 1278731050394165567), (Int.negSucc 4785472892058985151), (Int.negSucc 1072033135727939711)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 5992259296262400), (Int.ofNat 184236187545845568), (Int.ofNat 664719839157124224), (Int.ofNat 401064403443588288), (Int.negSucc 348471287005000319), (Int.ofNat 322977696605033472), (Int.ofNat 124891748771051520)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 1925666462156543), (Int.negSucc 34829637394850495), (Int.negSucc 41784733739647295), (Int.ofNat 40343750402855040)]]

theorem h0n89_arithmetic_row0 :
    (BiPoly.mul h0p7 h0p88).getD 0 []=h0p89.getD 0 [] := by
  decide +kernel

theorem h0n89_arithmetic_row1 :
    (BiPoly.mul h0p7 h0p88).getD 1 []=h0p89.getD 1 [] := by
  decide +kernel

theorem h0n89_arithmetic_row2 :
    (BiPoly.mul h0p7 h0p88).getD 2 []=h0p89.getD 2 [] := by
  decide +kernel

theorem h0n89_arithmetic_row3 :
    (BiPoly.mul h0p7 h0p88).getD 3 []=h0p89.getD 3 [] := by
  decide +kernel

theorem h0n89_arithmetic_row4 :
    (BiPoly.mul h0p7 h0p88).getD 4 []=h0p89.getD 4 [] := by
  decide +kernel

theorem h0n89_arithmetic_row5 :
    (BiPoly.mul h0p7 h0p88).getD 5 []=h0p89.getD 5 [] := by
  decide +kernel

theorem h0n89_arithmetic_row6 :
    (BiPoly.mul h0p7 h0p88).getD 6 []=h0p89.getD 6 [] := by
  decide +kernel

theorem h0n89_arithmetic_row7 :
    (BiPoly.mul h0p7 h0p88).getD 7 []=h0p89.getD 7 [] := by
  decide +kernel

theorem h0n89_arithmetic_row8 :
    (BiPoly.mul h0p7 h0p88).getD 8 []=h0p89.getD 8 [] := by
  decide +kernel

theorem h0n89_arithmetic_row9 :
    (BiPoly.mul h0p7 h0p88).getD 9 []=h0p89.getD 9 [] := by
  decide +kernel

theorem h0n89_arithmetic_row10 :
    (BiPoly.mul h0p7 h0p88).getD 10 []=h0p89.getD 10 [] := by
  decide +kernel

theorem h0n89_arithmetic_row11 :
    (BiPoly.mul h0p7 h0p88).getD 11 []=h0p89.getD 11 [] := by
  decide +kernel

theorem h0n89_arithmetic_row12 :
    (BiPoly.mul h0p7 h0p88).getD 12 []=h0p89.getD 12 [] := by
  decide +kernel

theorem h0n89_arithmetic_row13 :
    (BiPoly.mul h0p7 h0p88).getD 13 []=h0p89.getD 13 [] := by
  decide +kernel

theorem h0n89_arithmetic_row14 :
    (BiPoly.mul h0p7 h0p88).getD 14 []=h0p89.getD 14 [] := by
  decide +kernel

theorem h0n89_arithmetic_row15 :
    (BiPoly.mul h0p7 h0p88).getD 15 []=h0p89.getD 15 [] := by
  decide +kernel

theorem h0n89_arithmetic_row16 :
    (BiPoly.mul h0p7 h0p88).getD 16 []=h0p89.getD 16 [] := by
  decide +kernel

theorem h0n89_arithmetic_row17 :
    (BiPoly.mul h0p7 h0p88).getD 17 []=h0p89.getD 17 [] := by
  decide +kernel

theorem h0n89_arithmetic_row18 :
    (BiPoly.mul h0p7 h0p88).getD 18 []=h0p89.getD 18 [] := by
  decide +kernel

theorem h0n89_arithmetic : BiPoly.mul h0p7 h0p88=h0p89 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h0p7 h0p88).getD j.val []=h0p89.getD j.val [] :=
      (fun j => Fin.cases h0n89_arithmetic_row0 (fun j => Fin.cases h0n89_arithmetic_row1 (fun j => Fin.cases h0n89_arithmetic_row2 (fun j => Fin.cases h0n89_arithmetic_row3 (fun j => Fin.cases h0n89_arithmetic_row4 (fun j => Fin.cases h0n89_arithmetic_row5 (fun j => Fin.cases h0n89_arithmetic_row6 (fun j => Fin.cases h0n89_arithmetic_row7 (fun j => Fin.cases h0n89_arithmetic_row8 (fun j => Fin.cases h0n89_arithmetic_row9 (fun j => Fin.cases h0n89_arithmetic_row10 (fun j => Fin.cases h0n89_arithmetic_row11 (fun j => Fin.cases h0n89_arithmetic_row12 (fun j => Fin.cases h0n89_arithmetic_row13 (fun j => Fin.cases h0n89_arithmetic_row14 (fun j => Fin.cases h0n89_arithmetic_row15 (fun j => Fin.cases h0n89_arithmetic_row16 (fun j => Fin.cases h0n89_arithmetic_row17 (fun j => Fin.cases h0n89_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h0n89 : h0e89.toBi mapPolyEnv=h0p89 := by
  change BiPoly.mul (h0e7.toBi mapPolyEnv) (h0e88.toBi mapPolyEnv)=h0p89
  rw [h0n7, h0n88]
  exact h0n89_arithmetic

#print axioms h0n89_arithmetic
end StackSorting.RationalLift
