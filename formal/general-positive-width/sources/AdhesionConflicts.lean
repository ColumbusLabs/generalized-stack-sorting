import AdhesionGeometry

namespace StackSorting.AdhesionGuidance
open GraphWidth FinitePort
variable {n t : Nat} {G : Graph n} {T : RootedTree t}
variable {D : Decomposition G T}
namespace Paths
variable (P : Paths D)

def rank (i : Index D) : Nat := i.val.1.val * n + i.val.2.val

theorem rank_injective : Function.Injective (rank (D := D)) := by
  intro i j he
  have hi := i.val.2.isLt
  have hj := j.val.2.isLt
  have hb : i.val.1.val = j.val.1.val := by
    dsimp [rank] at he
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h <;> nlinarith
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext hb
  · apply Fin.ext
    dsimp [rank] at he
    rw [hb] at he
    omega

theorem rank_lt_base_le {i j : Index D} (h : rank i < rank j) :
    i.val.1.val ≤ j.val.1.val := by
  have hi := i.val.2.isLt
  have hj := j.val.2.isLt
  dsimp [rank] at h
  by_contra hn
  have hh : j.val.1.val < i.val.1.val := by omega
  nlinarith

noncomputable def earlier (i : Index D) : Finset (Index D) := by
  classical
  exact Finset.univ.filter (fun j => rank j < rank i ∧ P.Conflict j i)

theorem earlier_ancestor {i j : Index D} (h : j ∈ P.earlier i) :
    Ancestor T j.val.1 i.val.1 := by
  classical
  have hh := (Finset.mem_filter.mp h).2
  rcases P.conflict_comparable hh.2 with hc | hc
  · exact hc
  · have he : i.val.1 = j.val.1 :=
      Fin.ext (Nat.le_antisymm hc.val_le (rank_lt_base_le hh.1))
    rw [he]
    exact .refl _

/-- Every earlier conflict belongs to one of the four actual indexed families.
This is the combinatorial content of B–P Lemma 5.10. -/
theorem earlier_four_cases {i j : Index D} (h : j ∈ P.earlier i) :
    j ∈ based (D := D) i.val.1 ∨ j ∈ P.load i.val.1 ∨
    j ∈ based (D := D) (introductionNode D i.val.2) ∨
    j ∈ P.load (introductionNode D i.val.2) := by
  classical
  have ha := P.earlier_ancestor h
  have hc := (Finset.mem_filter.mp h).2.2
  by_cases he : j.val.1 = i.val.1
  · exact Or.inl (by simp [based,he])
  · by_cases hm : ∃ v, v ∈ (P.walk j).support ∧ v ∈ component D i.val.1
    · exact Or.inr (Or.inl (by simp only [load,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨ha,he,hm⟩))
    · obtain ⟨hne,v,hj,hi⟩ := hc
      have hv : v = i.val.2 := by
        by_contra hv
        exact hm ⟨v,hj,P.contained i v hi hv⟩
      subst v
      have hy := (component_iff D _ _).mp (P.contained j _ hj hne.symm)
      by_cases hey : j.val.1 = introductionNode D i.val.2
      · exact Or.inr (Or.inr (Or.inl (by simp [based,hey])))
      · apply Or.inr ∘ Or.inr ∘ Or.inr
        simp only [load,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨hy,hey,i.val.2,hj,introduction_component D i.val.2⟩

/-- Counting indices, not distinct targets or distinct support sets, yields
exactly the palette `2*L + 2*k`, including zero-adhesion cases. -/
theorem earlier_card_lt {k L : Nat} (hb : P.Bounded k L) (i : Index D) :
    (P.earlier i).card < 2 * L + 2 * k := by
  classical
  let y := introductionNode D i.val.2
  let S := ((based (D := D) i.val.1 ∪ P.load i.val.1) ∪ based (D := D) y) ∪ P.load y
  have hs : insert i (P.earlier i) ⊆ S := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp [S,based]
    · rcases P.earlier_four_cases hj with h | h | h | h <;> simp [S,y,h]
  have hcard : S.card ≤ 2 * L + 2 * k := by
    have h1 := Finset.card_union_le (based (D := D) i.val.1) (P.load i.val.1)
    have h2 := Finset.card_union_le (based (D := D) i.val.1 ∪ P.load i.val.1) (based (D := D) y)
    have h3 := Finset.card_union_le ((based (D := D) i.val.1 ∪ P.load i.val.1) ∪ based (D := D) y) (P.load y)
    have h4 := hb.1 i.val.1
    have h5 := hb.2 i.val.1
    have h6 := hb.1 y
    have h7 := hb.2 y
    dsimp [S]
    omega
  have hn : i ∉ P.earlier i := by simp [earlier]
  have hh := (Finset.card_le_card hs).trans hcard
  rw [Finset.card_insert_of_notMem hn] at hh
  omega

#print axioms earlier_card_lt
end Paths
end StackSorting.AdhesionGuidance
