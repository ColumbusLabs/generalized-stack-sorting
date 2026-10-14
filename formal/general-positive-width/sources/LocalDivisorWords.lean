import LocalDivisor
import FactorizationTree

namespace StackSorting.Simon
open FactorizationTree

namespace FactorizationTree

theorem Valid.leaves_ne_nil {A M : Type*} [Monoid M] {φ : A → M}
    {t : FactorizationTree A} (hv : Valid φ t) : t.leaves ≠ [] := by
  induction hv with
  | leaf a => simp [leaves]
  | node ts hc ha hb ih =>
    intro hempty
    rw [leaves] at hempty
    have hall := List.flatMap_eq_nil_iff.mp hempty
    have hts : ts ≠ [] := by intro h; simp [h] at ha
    obtain ⟨r, rest, rfl⟩ := List.exists_cons_of_ne_nil hts
    exact ih r (by simp) (hall r (by simp))

end FactorizationTree

variable {B M : Type*} [Monoid M]

/-- Block values with a common left boundary. -/
def ambientBlockValue (c : M) (interior : B → M) (b : B) : M := c * interior b

noncomputable def localBlockValue (c : M) (interior : B → M) (b : B) : LocalDivisor c :=
  LocalDivisor.sandwich c (interior b)

/-- The local multiplication removes exactly the duplicated boundary c. -/
theorem localBlockWord_value (c : M) (interior : B → M) (w : List B) :
    ((w.map (localBlockValue c interior)).prod).val =
      (w.map (ambientBlockValue c interior)).prod * c := by
  induction w with
  | nil => simp [LocalDivisor.val_one]
  | cons b w ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [LocalDivisor.val_mul_left _ _ (c * interior b) rfl, ih]
    simp only [ambientBlockValue, mul_assoc]

/-- Every nonempty sequence of blocks still has the common left boundary. -/
theorem exists_blockWord_interior (c : M) (interior : B → M)
    (w : List B) (hne : w ≠ []) :
    ∃ x : M,
      (w.map (ambientBlockValue c interior)).prod = c * x ∧
      (w.map (localBlockValue c interior)).prod = LocalDivisor.sandwich c x := by
  obtain ⟨b, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  let x := interior b * (tail.map (ambientBlockValue c interior)).prod
  have ha : ((b :: tail).map (ambientBlockValue c interior)).prod = c * x := by
    simp [x, ambientBlockValue, mul_assoc]
  refine ⟨x, ha, ?_⟩
  apply Subtype.ext
  rw [localBlockWord_value, ha]
  rfl

/-- The pair alphabet needed at a local-idempotent node really is right-zero
under the ambient evaluation. No ambient idempotence is assumed. -/
theorem paired_blockWords_rightZero (c : M) (interior : B → M)
    (e : LocalDivisor c) (he : e * e = e)
    (u v r s : List B) (hu : u ≠ []) (hv : v ≠ []) (hr : r ≠ []) (hs : s ≠ [])
    (ue : (u.map (localBlockValue c interior)).prod = e)
    (ve : (v.map (localBlockValue c interior)).prod = e)
    (re : (r.map (localBlockValue c interior)).prod = e) :
    ((u ++ v).map (ambientBlockValue c interior)).prod *
      ((r ++ s).map (ambientBlockValue c interior)).prod =
      ((r ++ s).map (ambientBlockValue c interior)).prod := by
  obtain ⟨x, hxa, hxl⟩ := exists_blockWord_interior c interior u hu
  obtain ⟨y, hya, hyl⟩ := exists_blockWord_interior c interior v hv
  obtain ⟨z, hza, hzl⟩ := exists_blockWord_interior c interior r hr
  obtain ⟨t, hta, _⟩ := exists_blockWord_interior c interior s hs
  simp only [List.map_append, List.prod_append, hxa, hya, hza, hta]
  exact LocalDivisor.fiber_pairs_mul e he x y z t
    (hxl.symm.trans ue) (hyl.symm.trans ve) (hzl.symm.trans re)

#print axioms paired_blockWords_rightZero
end StackSorting.Simon
