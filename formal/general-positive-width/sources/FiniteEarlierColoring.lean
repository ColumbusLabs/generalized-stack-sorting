import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

namespace StackSorting.FiniteEarlierColoring

noncomputable def predecessors {α : Type} [Fintype α]
    (rank : α → Nat) (adj : α → α → Prop) (i : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun j => rank j < rank i ∧ adj j i)

/-- Generic finite greedy coloring extracted from the checked adhesion-color
construction. All earlier-neighbor counts are concrete finite set counts. -/
theorem exists_coloring {α : Type} [Fintype α] (rank : α → Nat)
    (hrank : Function.Injective rank) (adj : α → α → Prop)
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (palette : Nat)
    (hbound : ∀ i, (predecessors rank adj i).card < palette) :
    ∃ f : α → Fin palette, ∀ i j, adj i j → f i ≠ f j := by
  classical
  let earlier (i : α) := Finset.univ.filter (fun j => rank j < rank i ∧ adj j i)
  by_cases hI : Nonempty α
  · have hc : 0 < palette := lt_of_le_of_lt (Nat.zero_le _) (hbound (Classical.choice hI))
    have aux : ∀ S : Finset α, ∃ f : α → Fin palette,
        ∀ i ∈ S, ∀ j ∈ S, adj i j → f i ≠ f j := by
      intro S
      refine Finset.strongInductionOn S ?_
      intro S ih
      by_cases hs : S.Nonempty
      · obtain ⟨a,ha,hm⟩ := S.exists_max_image rank hs
        obtain ⟨f,hf⟩ := ih (S.erase a) (Finset.erase_ssubset ha)
        have hsmall : ((earlier a).image f).card < (Finset.univ : Finset (Fin palette)).card := by
          simpa [earlier,predecessors] using lt_of_le_of_lt (Finset.card_image_le) (hbound a)
        obtain ⟨c,_,hcnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
        have havoid : ∀ j ∈ S, j ≠ a → adj j a → f j ≠ c := by
          intro j hj hja hconf he
          apply hcnot
          apply Finset.mem_image.mpr
          refine ⟨j,?_,he⟩
          simp only [earlier,Finset.mem_filter,Finset.mem_univ,true_and]
          refine ⟨lt_of_le_of_ne (hm j hj) ?_,hconf⟩
          exact fun hsame => hja (hrank hsame)
        refine ⟨fun i => if i=a then c else f i,?_⟩
        intro i hi j hj hij
        by_cases hei : i=a
        · subst i
          have hja : j≠a := by intro he; subst j; exact hirr _ hij
          simpa [hja] using (havoid j hj hja (hsymm _ _ hij)).symm
        · by_cases hej : j=a
          · subst j
            simpa [hei] using havoid i hi hei hij
          · simpa [hei,hej] using hf i (Finset.mem_erase.mpr ⟨hei,hi⟩)
              j (Finset.mem_erase.mpr ⟨hej,hj⟩) hij
      · refine ⟨fun _ => ⟨0,hc⟩,?_⟩
        intro i hi
        exact False.elim (hs ⟨i,hi⟩)
    obtain ⟨f,hf⟩ := aux Finset.univ
    exact ⟨f,fun i j h => hf i (Finset.mem_univ _) j (Finset.mem_univ _) h⟩
  · have : IsEmpty α := not_nonempty_iff.mp hI
    exact ⟨isEmptyElim,fun i => isEmptyElim i⟩

#print axioms exists_coloring
end StackSorting.FiniteEarlierColoring
