import BivariateRowEquality
import Horner4Base
import Horner4Node163
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p164 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 4570641570476951999), (Int.negSucc 34561693814737281119), (Int.negSucc 45916340899491191519), (Int.ofNat 122801198655952092960), (Int.ofNat 140993043638272158240), (Int.negSucc 169822863762659553599)], [(Int.ofNat 0), (Int.ofNat 42208024553566260480), (Int.ofNat 321458040307013023296), (Int.ofNat 449303719682510208288), (Int.negSucc 1043677634661593972927), (Int.negSucc 1207927890168252170975), (Int.ofNat 1499103570626521437888), (Int.negSucc 123018171890687481599)], [(Int.ofNat 0), (Int.negSucc 183736109199505201199), (Int.negSucc 1371852674687632282199), (Int.negSucc 1959077335751493346655), (Int.ofNat 3899457048323686405824), (Int.ofNat 4745535528604410496512), (Int.negSucc 5420042409269957819399), (Int.ofNat 564071192270205203952), (Int.negSucc 28842064299443621375)], [(Int.ofNat 0), (Int.ofNat 499552303611863254320), (Int.ofNat 3555793592875988888760), (Int.ofNat 5133861917987848627104), (Int.negSucc 7955082472851669145247), (Int.negSucc 11137594845940695538127), (Int.ofNat 9610961563216774338984), (Int.negSucc 192001563892317489407), (Int.ofNat 7138333388140913376), (Int.negSucc 2118755855265020927)], [(Int.ofNat 0), (Int.negSucc 944412378919285284719), (Int.negSucc 6263644142116084630247), (Int.negSucc 9240781827773925746207), (Int.ofNat 8539488221608995614064), (Int.ofNat 17136529455513964883040), (Int.negSucc 5777588238025975294391), (Int.negSucc 3740280658895717767583), (Int.ofNat 367866714623175779904), (Int.negSucc 11536599888943632575), (Int.ofNat 11292431533194240)], [(Int.ofNat 0), (Int.ofNat 1305369493930385471880), (Int.ofNat 7978365298441273581756), (Int.ofNat 12446111656072749997332), (Int.negSucc 1628907703173535842719), (Int.negSucc 17229423497577203371679), (Int.negSucc 9361650132422032597091), (Int.ofNat 9500601600215472863844), (Int.negSucc 569516965496476609607), (Int.ofNat 15925344531367838976), (Int.negSucc 368979135943047551)], [(Int.ofNat 0), (Int.negSucc 1350216278286600878999), (Int.negSucc 7663681127522642032763), (Int.negSucc 13360762878374497381559), (Int.negSucc 9076345123131872109647), (Int.ofNat 8969101746932084000616), (Int.ofNat 23102059707912170207340), (Int.negSucc 7861960622003552162423), (Int.negSucc 1008705826192725499031), (Int.ofNat 90143198946907174224), (Int.negSucc 2201086570875735167)], [(Int.ofNat 0), (Int.ofNat 1053387952622797988520), (Int.ofNat 5735511005819175769716), (Int.ofNat 11905132759679142278892), (Int.ofNat 15316365220116195231144), (Int.ofNat 3133858733100385245288), (Int.negSucc 20594443578246366818219), (Int.negSucc 3836631005692151213915), (Int.ofNat 3373502600118929951448), (Int.negSucc 130512269194635572351), (Int.negSucc 72868590713741183)], [(Int.ofNat 0), (Int.negSucc 618142829956876965959), (Int.negSucc 3428855017231116518459), (Int.negSucc 8909054877830416084943), (Int.negSucc 14164284646385526352391), (Int.negSucc 10953619381131677387639), (Int.ofNat 5545878302311231724532), (Int.ofNat 12800796500868850074096), (Int.negSucc 2452686642169965989351), (Int.negSucc 204167540224540085471), (Int.ofNat 11858941613450216736)], [(Int.ofNat 0), (Int.ofNat 269525632232979173160), (Int.ofNat 1658557911758297632308), (Int.ofNat 5514467525344382667192), (Int.ofNat 9418973646720300979680), (Int.ofNat 11050671849580068434604), (Int.ofNat 6394967340566494699080), (Int.negSucc 9338396540277131145323), (Int.negSucc 1494849636140059729151), (Int.ofNat 491185744626875875020), (Int.ofNat 447596238077714232)], [(Int.ofNat 0), (Int.negSucc 85303090138795153559), (Int.negSucc 645723958772271683267), (Int.negSucc 2736841322315011629275), (Int.negSucc 5133185804686633026659), (Int.negSucc 6973176527531430379271), (Int.negSucc 8222604186648174051743), (Int.ofNat 614870433312322838940), (Int.ofNat 3227789469274358360508), (Int.negSucc 146194330871391128495), (Int.negSucc 26211428715162843503)], [(Int.ofNat 0), (Int.ofNat 18826083849237598440), (Int.ofNat 197390742181330246164), (Int.ofNat 1049391208519957250172), (Int.ofNat 2426027106352594204800), (Int.ofNat 3294842208706775533896), (Int.ofNat 4736793465815286710592), (Int.ofNat 3387875817925415507976), (Int.negSucc 1438133374376263405799), (Int.negSucc 326822123739727392695), (Int.ofNat 11415835378758914928)], [(Int.ofNat 0), (Int.negSucc 2700550621452832199), (Int.negSucc 45429453154217718395), (Int.negSucc 298451188939464650663), (Int.negSucc 956218528325026681415), (Int.negSucc 1346279199313718704031), (Int.negSucc 1718489746650544566983), (Int.negSucc 2486932675923601363103), (Int.negSucc 422327940383207933351), (Int.ofNat 282978506171885189688), (Int.ofNat 18200652703623899280)], [(Int.ofNat 0), (Int.ofNat 219564033226684560), (Int.ofNat 7398971914538482704), (Int.ofNat 59977139221050212988), (Int.ofNat 287217262500851010528), (Int.ofNat 499774950052239829500), (Int.ofNat 478360304617031452296), (Int.ofNat 851886891965793565152), (Int.ofNat 664210151800449356016), (Int.negSucc 13030018352694663119), (Int.negSucc 15322985251493410655)], [(Int.ofNat 0), (Int.negSucc 7176141063162719), (Int.negSucc 765929797559396711), (Int.negSucc 7959302742963508595), (Int.negSucc 59932081940339647619), (Int.negSucc 151825072481722644911), (Int.negSucc 134833426153186164911), (Int.negSucc 154548871070067161423), (Int.negSucc 269890634137049995535), (Int.negSucc 75971878275511105343), (Int.negSucc 573352494230925503)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 38433798643918464), (Int.ofNat 620507646801125136), (Int.ofNat 7819684316933966136), (Int.ofNat 32550241792528422216), (Int.ofNat 38587189766767685856), (Int.ofNat 15904945203981730704), (Int.ofNat 47829576433329923616), (Int.ofNat 37529948808126433440), (Int.ofNat 4319984661340613184)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 21359527178827679), (Int.negSucc 524655935641235303), (Int.negSucc 4289253006570937991), (Int.negSucc 8171638764980890463), (Int.negSucc 2407262720169161951), (Int.negSucc 1918096575591248351), (Int.negSucc 7178209338088477727), (Int.negSucc 1608049703591909567)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8988388944393600), (Int.ofNat 276354281318768352), (Int.ofNat 997079758735686336), (Int.ofNat 601596605165382432), (Int.negSucc 522706930507500479), (Int.ofNat 484466544907550208), (Int.ofNat 187337623156577280)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 2888499693234815), (Int.negSucc 52244456092275743), (Int.negSucc 62677100609470943), (Int.ofNat 60515625604282560)]]

theorem h4n164_arithmetic_row0 :
    (BiPoly.mul h4p13 h4p163).getD 0 []=h4p164.getD 0 [] := by
  decide +kernel

theorem h4n164_arithmetic_row1 :
    (BiPoly.mul h4p13 h4p163).getD 1 []=h4p164.getD 1 [] := by
  decide +kernel

theorem h4n164_arithmetic_row2 :
    (BiPoly.mul h4p13 h4p163).getD 2 []=h4p164.getD 2 [] := by
  decide +kernel

theorem h4n164_arithmetic_row3 :
    (BiPoly.mul h4p13 h4p163).getD 3 []=h4p164.getD 3 [] := by
  decide +kernel

theorem h4n164_arithmetic_row4 :
    (BiPoly.mul h4p13 h4p163).getD 4 []=h4p164.getD 4 [] := by
  decide +kernel

theorem h4n164_arithmetic_row5 :
    (BiPoly.mul h4p13 h4p163).getD 5 []=h4p164.getD 5 [] := by
  decide +kernel

theorem h4n164_arithmetic_row6 :
    (BiPoly.mul h4p13 h4p163).getD 6 []=h4p164.getD 6 [] := by
  decide +kernel

theorem h4n164_arithmetic_row7 :
    (BiPoly.mul h4p13 h4p163).getD 7 []=h4p164.getD 7 [] := by
  decide +kernel

theorem h4n164_arithmetic_row8 :
    (BiPoly.mul h4p13 h4p163).getD 8 []=h4p164.getD 8 [] := by
  decide +kernel

theorem h4n164_arithmetic_row9 :
    (BiPoly.mul h4p13 h4p163).getD 9 []=h4p164.getD 9 [] := by
  decide +kernel

theorem h4n164_arithmetic_row10 :
    (BiPoly.mul h4p13 h4p163).getD 10 []=h4p164.getD 10 [] := by
  decide +kernel

theorem h4n164_arithmetic_row11 :
    (BiPoly.mul h4p13 h4p163).getD 11 []=h4p164.getD 11 [] := by
  decide +kernel

theorem h4n164_arithmetic_row12 :
    (BiPoly.mul h4p13 h4p163).getD 12 []=h4p164.getD 12 [] := by
  decide +kernel

theorem h4n164_arithmetic_row13 :
    (BiPoly.mul h4p13 h4p163).getD 13 []=h4p164.getD 13 [] := by
  decide +kernel

theorem h4n164_arithmetic_row14 :
    (BiPoly.mul h4p13 h4p163).getD 14 []=h4p164.getD 14 [] := by
  decide +kernel

theorem h4n164_arithmetic_row15 :
    (BiPoly.mul h4p13 h4p163).getD 15 []=h4p164.getD 15 [] := by
  decide +kernel

theorem h4n164_arithmetic_row16 :
    (BiPoly.mul h4p13 h4p163).getD 16 []=h4p164.getD 16 [] := by
  decide +kernel

theorem h4n164_arithmetic_row17 :
    (BiPoly.mul h4p13 h4p163).getD 17 []=h4p164.getD 17 [] := by
  decide +kernel

theorem h4n164_arithmetic_row18 :
    (BiPoly.mul h4p13 h4p163).getD 18 []=h4p164.getD 18 [] := by
  decide +kernel

theorem h4n164_arithmetic : BiPoly.mul h4p13 h4p163=h4p164 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<19 at hk
    have hf : ∀ j : Fin 19, (BiPoly.mul h4p13 h4p163).getD j.val []=h4p164.getD j.val [] :=
      (fun j => Fin.cases h4n164_arithmetic_row0 (fun j => Fin.cases h4n164_arithmetic_row1 (fun j => Fin.cases h4n164_arithmetic_row2 (fun j => Fin.cases h4n164_arithmetic_row3 (fun j => Fin.cases h4n164_arithmetic_row4 (fun j => Fin.cases h4n164_arithmetic_row5 (fun j => Fin.cases h4n164_arithmetic_row6 (fun j => Fin.cases h4n164_arithmetic_row7 (fun j => Fin.cases h4n164_arithmetic_row8 (fun j => Fin.cases h4n164_arithmetic_row9 (fun j => Fin.cases h4n164_arithmetic_row10 (fun j => Fin.cases h4n164_arithmetic_row11 (fun j => Fin.cases h4n164_arithmetic_row12 (fun j => Fin.cases h4n164_arithmetic_row13 (fun j => Fin.cases h4n164_arithmetic_row14 (fun j => Fin.cases h4n164_arithmetic_row15 (fun j => Fin.cases h4n164_arithmetic_row16 (fun j => Fin.cases h4n164_arithmetic_row17 (fun j => Fin.cases h4n164_arithmetic_row18 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h4n164 : h4e164.toBi mapPolyEnv=h4p164 := by
  change BiPoly.mul (h4e13.toBi mapPolyEnv) (h4e163.toBi mapPolyEnv)=h4p164
  rw [h4n13, h4n163]
  exact h4n164_arithmetic

#print axioms h4n164_arithmetic
end StackSorting.RationalLift
