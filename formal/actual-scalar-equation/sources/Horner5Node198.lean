import BivariateRowEquality
import Horner5Base
import Horner5Node197
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p198 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 983546453753855), (Int.negSucc 6188987719701503), (Int.ofNat 37570937852103552), (Int.negSucc 74185102512263807), (Int.ofNat 395359880798903040), (Int.ofNat 295855781213193984), (Int.negSucc 974717886480856703), (Int.negSucc 565889633639139455), (Int.ofNat 460580043026515968), (Int.ofNat 268217371400822784)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 8369948836270080), (Int.ofNat 46472146546341888), (Int.negSucc 313570573478205695), (Int.ofNat 780692764316571648), (Int.negSucc 4166770224537120383), (Int.negSucc 2407442891424984575), (Int.ofNat 7668087657364841472), (Int.ofNat 3146705691388697088), (Int.negSucc 2934834070998907007), (Int.negSucc 945786229145413631), (Int.ofNat 149009650778234880)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 31859590648940543), (Int.negSucc 157526861967555839), (Int.ofNat 1125044153044397280), (Int.negSucc 3196627011623255135), (Int.ofNat 19336584251259505632), (Int.ofNat 8501346238376970912), (Int.negSucc 25686786064449338207), (Int.negSucc 7906928471009572127), (Int.ofNat 6547773779041971360), (Int.ofNat 1219106677953443808), (Int.negSucc 128219654167574015), (Int.ofNat 20695784830310400)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 71417715624468480), (Int.ofNat 321802757278205952), (Int.negSucc 2276845070109719327), (Int.ofNat 6575030455209047616), (Int.negSucc 51448359069112053983), (Int.negSucc 19475453139565195391), (Int.ofNat 45130172046610657056), (Int.ofNat 14612861242592351808), (Int.negSucc 3866419357772165663), (Int.negSucc 1472719418187674111), (Int.negSucc 701916009907099391), (Int.ofNat 47232590662256640)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 104356697991257087), (Int.negSucc 446871772088366975), (Int.ofNat 2862760166213102880), (Int.negSucc 6478743667153552991), (Int.ofNat 86687241608902565376), (Int.ofNat 38968671635318649600), (Int.negSucc 38752290722822298335), (Int.negSucc 26667070802269592543), (Int.negSucc 8121058559077760831), (Int.ofNat 3020002142019504192), (Int.ofNat 1247559529180328064), (Int.negSucc 111972712441543679)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 103689124728797184), (Int.ofNat 448066400213149056), (Int.negSucc 2337234652476728543), (Int.ofNat 16059516179410944), (Int.negSucc 97302369874939699199), (Int.negSucc 72014392208536706687), (Int.negSucc 500832488251319903), (Int.ofNat 38698163541755207808), (Int.ofNat 17637272136153333696), (Int.negSucc 2272070583115798655), (Int.negSucc 387458474157328127), (Int.negSucc 134802531802856447)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 70530863131895423), (Int.negSucc 327787445523719039), (Int.ofNat 1313597411192675904), (Int.ofNat 8023261396196930496), (Int.ofNat 75703428481765758144), (Int.ofNat 104557922700265638336), (Int.ofNat 43238386392309564384), (Int.negSucc 29803305350514154847), (Int.negSucc 16451663155155750623), (Int.negSucc 3451469861018945951), (Int.negSucc 303190876997760383), (Int.ofNat 320622758196811776)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 31722784173171072), (Int.ofNat 163169365931516160), (Int.negSucc 636135445952191679), (Int.negSucc 10569098934375874559), (Int.negSucc 43681209235249280831), (Int.negSucc 106309097801393859839), (Int.negSucc 63981800195653129247), (Int.negSucc 1672865577686187071), (Int.ofNat 10363577290429625568), (Int.ofNat 7028956709388003456), (Int.ofNat 200743459984482048), (Int.negSucc 30728761780713983)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 8143999616936063), (Int.negSucc 38992642639615871), (Int.ofNat 391443531509680320), (Int.ofNat 7370217068150518080), (Int.ofNat 21435841039183305600), (Int.ofNat 72913591588136591232), (Int.ofNat 62201196633349743840), (Int.ofNat 26369295125342828256), (Int.negSucc 3039418318891949567), (Int.negSucc 3936113140751944703), (Int.negSucc 500120693489364479), (Int.negSucc 222898138488009215)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 219334478360448), (Int.negSucc 12124251816988415), (Int.negSucc 265614423582906815), (Int.negSucc 3213332630321648255), (Int.negSucc 10121551098405715583), (Int.negSucc 33625013494455851903), (Int.negSucc 45250925918757511967), (Int.negSucc 27685950303224384639), (Int.negSucc 4411849058102065535), (Int.negSucc 155761309483769087), (Int.ofNat 703375955511243264), (Int.ofNat 94309217567004672)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 670954794947712), (Int.ofNat 14890278922985088), (Int.ofNat 137571197837213664), (Int.ofNat 938783088523747872), (Int.ofNat 4208480340519406176), (Int.ofNat 10813157405292443040), (Int.ofNat 23342306265536591232), (Int.ofNat 17157835192164370560), (Int.ofNat 7117722736084262016), (Int.ofNat 1273186681453420416), (Int.negSucc 153041977093787135), (Int.ofNat 40300550646644736)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 256593844849535), (Int.negSucc 6049270629151487), (Int.negSucc 48146430874558751), (Int.negSucc 207281686509260351), (Int.negSucc 1251493738075592927), (Int.negSucc 2755808605859260031), (Int.negSucc 7847896994033027327), (Int.negSucc 7818379377232665599), (Int.negSucc 4646388865239234431), (Int.negSucc 978953897311506431), (Int.negSucc 244852746862593023), (Int.negSucc 25332214006167551)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 44663208492672), (Int.ofNat 1261113954635520), (Int.ofNat 10975334049410976), (Int.ofNat 41844300559855776), (Int.ofNat 225648448640064000), (Int.ofNat 643387648803632640), (Int.ofNat 1586382573972706560), (Int.ofNat 2651662639818641664), (Int.ofNat 1674431686144797696), (Int.ofNat 572719555957635072), (Int.ofNat 146476445511094272), (Int.ofNat 2150237097990144)], [(Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 3234156875135), (Int.negSucc 124358632871039), (Int.negSucc 1516897951207775), (Int.negSucc 7363859970123647), (Int.negSucc 22315439100493439), (Int.negSucc 116935984211629823), (Int.negSucc 188579208217349375), (Int.negSucc 570969817188507647), (Int.negSucc 392889191262787583), (Int.negSucc 204550830723225599), (Int.negSucc 21884533914322943)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 3528171136512), (Int.ofNat 101724955425792), (Int.ofNat 770038530539904), (Int.ofNat 1637692038983808), (Int.ofNat 10218233225128320), (Int.ofNat 19370026258223616), (Int.ofNat 54477535250718720), (Int.ofNat 74235685185183744), (Int.ofNat 28344608727091200)], [(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0), (Int.negSucc 962228491775), (Int.negSucc 25735200643583), (Int.negSucc 153063688535423), (Int.negSucc 6533966020607), (Int.negSucc 2113629054335999), (Int.ofNat 197166225530880), (Int.negSucc 8610311910758399)]]

theorem h5n198_arithmetic_row0 :
    (BiPoly.mul h5p3 h5p197).getD 0 []=h5p198.getD 0 [] := by
  decide +kernel

theorem h5n198_arithmetic_row1 :
    (BiPoly.mul h5p3 h5p197).getD 1 []=h5p198.getD 1 [] := by
  decide +kernel

theorem h5n198_arithmetic_row2 :
    (BiPoly.mul h5p3 h5p197).getD 2 []=h5p198.getD 2 [] := by
  decide +kernel

theorem h5n198_arithmetic_row3 :
    (BiPoly.mul h5p3 h5p197).getD 3 []=h5p198.getD 3 [] := by
  decide +kernel

theorem h5n198_arithmetic_row4 :
    (BiPoly.mul h5p3 h5p197).getD 4 []=h5p198.getD 4 [] := by
  decide +kernel

theorem h5n198_arithmetic_row5 :
    (BiPoly.mul h5p3 h5p197).getD 5 []=h5p198.getD 5 [] := by
  decide +kernel

theorem h5n198_arithmetic_row6 :
    (BiPoly.mul h5p3 h5p197).getD 6 []=h5p198.getD 6 [] := by
  decide +kernel

theorem h5n198_arithmetic_row7 :
    (BiPoly.mul h5p3 h5p197).getD 7 []=h5p198.getD 7 [] := by
  decide +kernel

theorem h5n198_arithmetic_row8 :
    (BiPoly.mul h5p3 h5p197).getD 8 []=h5p198.getD 8 [] := by
  decide +kernel

theorem h5n198_arithmetic_row9 :
    (BiPoly.mul h5p3 h5p197).getD 9 []=h5p198.getD 9 [] := by
  decide +kernel

theorem h5n198_arithmetic_row10 :
    (BiPoly.mul h5p3 h5p197).getD 10 []=h5p198.getD 10 [] := by
  decide +kernel

theorem h5n198_arithmetic_row11 :
    (BiPoly.mul h5p3 h5p197).getD 11 []=h5p198.getD 11 [] := by
  decide +kernel

theorem h5n198_arithmetic_row12 :
    (BiPoly.mul h5p3 h5p197).getD 12 []=h5p198.getD 12 [] := by
  decide +kernel

theorem h5n198_arithmetic_row13 :
    (BiPoly.mul h5p3 h5p197).getD 13 []=h5p198.getD 13 [] := by
  decide +kernel

theorem h5n198_arithmetic_row14 :
    (BiPoly.mul h5p3 h5p197).getD 14 []=h5p198.getD 14 [] := by
  decide +kernel

theorem h5n198_arithmetic_row15 :
    (BiPoly.mul h5p3 h5p197).getD 15 []=h5p198.getD 15 [] := by
  decide +kernel

theorem h5n198_arithmetic : BiPoly.mul h5p3 h5p197=h5p198 := by
  apply BiPoly.eq_of_rows
  · decide +kernel
  · intro k hk
    change k<16 at hk
    have hf : ∀ j : Fin 16, (BiPoly.mul h5p3 h5p197).getD j.val []=h5p198.getD j.val [] :=
      (fun j => Fin.cases h5n198_arithmetic_row0 (fun j => Fin.cases h5n198_arithmetic_row1 (fun j => Fin.cases h5n198_arithmetic_row2 (fun j => Fin.cases h5n198_arithmetic_row3 (fun j => Fin.cases h5n198_arithmetic_row4 (fun j => Fin.cases h5n198_arithmetic_row5 (fun j => Fin.cases h5n198_arithmetic_row6 (fun j => Fin.cases h5n198_arithmetic_row7 (fun j => Fin.cases h5n198_arithmetic_row8 (fun j => Fin.cases h5n198_arithmetic_row9 (fun j => Fin.cases h5n198_arithmetic_row10 (fun j => Fin.cases h5n198_arithmetic_row11 (fun j => Fin.cases h5n198_arithmetic_row12 (fun j => Fin.cases h5n198_arithmetic_row13 (fun j => Fin.cases h5n198_arithmetic_row14 (fun j => Fin.cases h5n198_arithmetic_row15 (fun j => Fin.elim0 j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j) j)
    exact hf ⟨k,hk⟩

theorem h5n198 : h5e198.toBi mapPolyEnv=h5p198 := by
  change BiPoly.mul (h5e3.toBi mapPolyEnv) (h5e197.toBi mapPolyEnv)=h5p198
  rw [h5n3, h5n197]
  exact h5n198_arithmetic

#print axioms h5n198_arithmetic
end StackSorting.RationalLift
