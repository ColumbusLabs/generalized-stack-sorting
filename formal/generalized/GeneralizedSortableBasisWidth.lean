import GeneralizedInverseOrientation

/-! Exact inverse/deletion commutation, literal minimality transfer, and the
sortable-input basis width bound with zero-based indices and original widths. -/
namespace StackSorting.Generalized
open List

theorem deleteRank_succ_succ (v a : Nat) : deleteRank (v+1) (a+1) = deleteRank v a + 1 := by
  unfold deleteRank
  split <;> split <;> omega

theorem idxOf_deleteWord_of_not_mem {v a : Nat} {p : List Nat}
    (hv : v ∉ p) (ha : a ≠ v) : (deleteWord v p).idxOf (deleteRank v a) = p.idxOf a := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    have hbn : b ≠ v := by intro he; exact hv (by simp [he])
    have hvt : v ∉ p := fun h => hv (by simp [h])
    by_cases hba : b = a
    · subst b; simp [deleteWord_cons, ha]
    · have hne : deleteRank v b ≠ deleteRank v a :=
        fun h => hba (deleteRank_injective_surviving hbn ha h)
      simp [deleteWord_cons, hbn, List.idxOf_cons, hba, hne, ih hvt]

/-- Exact position compression under standardized one-value deletion. The
index of the deleted label is the position removed from the surviving word. -/
theorem idxOf_deleteWord {v a : Nat} {p : List Nat}
    (hn : p.Nodup) (ha : a ∈ p) (hav : a ≠ v) :
    (deleteWord v p).idxOf (deleteRank v a) = deleteRank (p.idxOf v) (p.idxOf a) := by
  induction p with
  | nil => simp at ha
  | cons b p ih =>
    have hnd := List.nodup_cons.mp hn
    by_cases hb : b = v
    · subst b
      have h := idxOf_deleteWord_of_not_mem hnd.1 hav
      simpa [deleteWord_cons, List.idxOf_cons, Ne.symm hav, deleteRank] using h
    · by_cases hba : b = a
      · subst b; simp [deleteWord_cons, hb, deleteRank]
      · have hat : a ∈ p := (List.mem_cons.mp ha).resolve_left (Ne.symm hba)
        have hne : deleteRank v b ≠ deleteRank v a :=
          fun h => hba (deleteRank_injective_surviving hb hav h)
        simpa [deleteWord_cons, hb, hba, hne, List.idxOf_cons, deleteRank_succ_succ] using
          ih hnd.2 hat

theorem idxOf_injective_on_members {p : List Nat} {a b : Nat}
    (ha : a ∈ p) (hb : b ∈ p) (he : p.idxOf a = p.idxOf b) : a = b := by
  have hia := List.idxOf_lt_length_of_mem ha
  have hib := List.idxOf_lt_length_of_mem hb
  calc
    a = p[p.idxOf a] := (List.getElem_idxOf hia).symm
    _ = p[p.idxOf b] := by congr 1
    _ = b := List.getElem_idxOf hib

/-- Inversion commutes with ordinary standardized deletion, at the matching
inverse value: deleting original value v deletes original position idxOf(v)
from the inverse permutation. -/
theorem inversePermutation_deleteWord {n v : Nat} {p : List Nat}
    (hp : p.Perm (List.range n)) (hv : v ∈ List.range n) :
    inversePermutation (deleteWord v p) = deleteWord (p.idxOf v) (inversePermutation p) := by
  have hn := hp.nodup_iff.mpr List.nodup_range
  have hlen : p.length = n := by simpa using hp.length_eq
  have hvlt := List.mem_range.mp hv
  have hpd := deleteWord_permutation hp hvlt
  have hld : (deleteWord v p).length = n-1 := by simpa using hpd.length_eq
  have hvp := hp.mem_iff.mpr hv
  let base := (List.range n).filter (fun a => a != v)
  let f := fun a => deleteRank (p.idxOf v) (p.idxOf a)
  have hleft : inversePermutation (deleteWord v p) = base.map f := by
    rw [inversePermutation, hld, ← deleteWord_range hvlt]
    change (((List.range n).filter (fun a => a != v)).map (deleteRank v)).map (deleteWord v p).idxOf = base.map f
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    obtain ⟨har, han⟩ := List.mem_filter.mp ha
    have hav : a ≠ v := by simpa using han
    exact idxOf_deleteWord hn (hp.mem_iff.mpr har) hav
  have hright : deleteWord (p.idxOf v) (inversePermutation p) = base.map f := by
    unfold inversePermutation deleteWord
    rw [hlen, List.filter_map, List.map_map]
    have hfilter : (List.range n).filter (fun a => p.idxOf a != p.idxOf v) = base := by
      apply List.filter_congr
      intro a ha
      have heq : p.idxOf a = p.idxOf v ↔ a = v :=
        ⟨idxOf_injective_on_members (hp.mem_iff.mpr ha) hvp, fun h => h ▸ rfl⟩
      apply Bool.eq_iff_iff.mpr
      simpa only [bne_iff_ne] using not_congr heq
    change ((List.range n).filter (fun a => p.idxOf a != p.idxOf v)).map f = base.map f
    rw [hfilter]
  exact hleft.trans hright.symm

/-- Literal sortable-input one-deletion minimal rejection transfers to literal
generated-output minimal rejection of the genuine inverse. -/
theorem sortable_minimal_inverse_generated {r s n : Nat} {p : List Nat}
    (hp : p.Perm (List.range n))
    (hreject : ¬ Run r s [] p (List.range n) [])
    (hdelete : ∀ v ∈ List.range n,
      Run r s [] (deleteWord v p) (List.range (n-1)) []) :
    (¬ Run r s [] (List.range n) (inversePermutation p) []) ∧
      ∀ j ∈ List.range n,
        Run r s [] (List.range (n-1)) (deleteWord j (inversePermutation p)) [] := by
  refine ⟨fun h => hreject ((sortable_iff_inverse_generated hp).mpr h), ?_⟩
  intro j hj
  have hlen : p.length = n := by simpa using hp.length_eq
  have hji : j < p.length := by simpa [hlen] using List.mem_range.mp hj
  have hv : p[j] ∈ List.range n := hp.mem_iff.mp (List.getElem_mem hji)
  have hpd := deleteWord_permutation hp (List.mem_range.mp hv)
  have hg := (sortable_iff_inverse_generated hpd).mp (hdelete p[j] hv)
  rw [inversePermutation_deleteWord hp hv] at hg
  have hn := hp.nodup_iff.mpr List.nodup_range
  rw [hn.idxOf_getElem j hji] at hg
  exact hg

/-- The published sortable-input orientation: every zero-based position i of
an ordinary one-deletion-minimal rejected input satisfies i ≤ p[i]+2*max r s. -/
theorem oneDeletionMinimal_sortable_getElem_le {r s n i : Nat} {p : List Nat}
    (hp : p.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ Run r s [] p (List.range n) [])
    (hdelete : ∀ v ∈ List.range n,
      Run r s [] (deleteWord v p) (List.range (n-1)) []) (hi : i < p.length) :
    i ≤ p[i] + 2 * max r s := by
  obtain ⟨hno, hdel⟩ := sortable_minimal_inverse_generated hp hreject hdelete
  have hbound : ∀ j (hj : j < (inversePermutation p).length),
      (inversePermutation p)[j] ≤ j + 2 * max r s := fun _ hj =>
    oneDeletionMinimal_output_getElem_le (inversePermutation_perm hp) hr hs hno hdel hj
  exact (inverse_displacement_iff hp).mp hbound i hi

/-- The exact finite sortable-input displacement-width formula, with empty
maximum zero: 1 + max over positions i of the natural delay i-p[i]. -/
def sortableDisplacementWidth (p : List Nat) : Nat :=
  1 + ((List.range p.length).map (fun i => i - p[i]!)).foldr Nat.max 0

theorem foldr_max_le {xs : List Nat} {D : Nat} (h : ∀ x ∈ xs, x ≤ D) : xs.foldr Nat.max 0 ≤ D := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨hx, ht⟩

/-- Global sortable-input basis-width bound, with the actual ordinary
one-deletion minimality hypotheses stated in the literal machine. -/
theorem oneDeletionMinimal_sortable_width_le {r s n : Nat} {p : List Nat}
    (hp : p.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ Run r s [] p (List.range n) [])
    (hdelete : ∀ v ∈ List.range n,
      Run r s [] (deleteWord v p) (List.range (n-1)) []) :
    sortableDisplacementWidth p ≤ 2 * max r s + 1 := by
  have hb : ∀ d ∈ (List.range p.length).map (fun i => i - p[i]!), d ≤ 2 * max r s := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    have hlt := List.mem_range.mp hi
    rw [getElem!_pos p i hlt]
    have h := oneDeletionMinimal_sortable_getElem_le hp hr hs hreject hdelete hlt
    omega
  have h := foldr_max_le hb
  unfold sortableDisplacementWidth
  omega

theorem oneDeletionMinimal_sortable_three_three_width_le_seven {n : Nat} {p : List Nat}
    (hp : p.Perm (List.range n))
    (hreject : ¬ Run 3 3 [] p (List.range n) [])
    (hdelete : ∀ v ∈ List.range n,
      Run 3 3 [] (deleteWord v p) (List.range (n-1)) []) : sortableDisplacementWidth p ≤ 7 := by
  simpa using oneDeletionMinimal_sortable_width_le hp (by decide : 0 < 3) (by decide : 0 < 3) hreject hdelete

#print axioms idxOf_deleteWord
#print axioms inversePermutation_deleteWord
#print axioms sortable_minimal_inverse_generated
#print axioms oneDeletionMinimal_sortable_getElem_le
#print axioms oneDeletionMinimal_sortable_width_le
#print axioms oneDeletionMinimal_sortable_three_three_width_le_seven
end StackSorting.Generalized
