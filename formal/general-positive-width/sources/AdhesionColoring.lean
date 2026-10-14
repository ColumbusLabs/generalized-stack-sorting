import AdhesionConflicts

namespace StackSorting.AdhesionGuidance
open GraphWidth FinitePort
variable {n t : Nat} {G : Graph n} {T : RootedTree t}
variable {D : Decomposition G T}
namespace Paths
variable (P : Paths D)

/-- Finite greedy coloring, proved by deleting an actual maximum-rank index.
The only quantitative premise is the proved earlier-neighbor count. -/
theorem exists_coloring {k L : Nat} (hb : P.Bounded k L) :
    ∃ f : Index D → Fin (2 * L + 2 * k),
      ∀ i j, P.Conflict i j → f i ≠ f j := by
  classical
  by_cases hI : Nonempty (Index D)
  · have hc : 0 < 2 * L + 2 * k :=
      lt_of_le_of_lt (Nat.zero_le _) (P.earlier_card_lt hb (Classical.choice hI))
    have aux : ∀ S : Finset (Index D),
        ∃ f : Index D → Fin (2 * L + 2 * k),
          ∀ i ∈ S, ∀ j ∈ S, P.Conflict i j → f i ≠ f j := by
      intro S
      refine Finset.strongInductionOn S ?_
      intro S ih
      by_cases hs : S.Nonempty
      · obtain ⟨a,ha,hm⟩ := S.exists_max_image rank hs
        obtain ⟨f,hf⟩ := ih (S.erase a) (Finset.erase_ssubset ha)
        have hsmall : ((P.earlier a).image f).card <
            (Finset.univ : Finset (Fin (2 * L + 2 * k))).card := by
          simpa using lt_of_le_of_lt (Finset.card_image_le) (P.earlier_card_lt hb a)
        obtain ⟨c,_,hcnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
        have havoid : ∀ j ∈ S, j ≠ a → P.Conflict j a → f j ≠ c := by
          intro j hj hja hconf he
          apply hcnot
          apply Finset.mem_image.mpr
          refine ⟨j,?_,he⟩
          simp only [earlier,Finset.mem_filter,Finset.mem_univ,true_and]
          refine ⟨lt_of_le_of_ne (hm j hj) ?_,hconf⟩
          intro hsame
          exact hja (rank_injective hsame)
        refine ⟨fun i => if i = a then c else f i,?_⟩
        intro i hi j hj hij
        by_cases hei : i = a
        · subst i
          have hja : j ≠ a := by intro he; subst j; exact hij.1 rfl
          simpa [hja] using (havoid j hj hja (P.conflict_symm hij)).symm
        · by_cases hej : j = a
          · subst j
            simpa [hei] using havoid i hi hei hij
          · simpa [hei,hej] using hf i (Finset.mem_erase.mpr ⟨hei,hi⟩)
              j (Finset.mem_erase.mpr ⟨hej,hj⟩) hij
      · refine ⟨fun _ => ⟨0,hc⟩,?_⟩
        intro i hi
        exact False.elim (hs ⟨i,hi⟩)
    obtain ⟨f,hf⟩ := aux Finset.univ
    exact ⟨f,fun i j h => hf i (Finset.mem_univ _) j (Finset.mem_univ _) h⟩
  · have : IsEmpty (Index D) := not_nonempty_iff.mp hI
    exact ⟨isEmptyElim,fun i => isEmptyElim i⟩

/-- The constructed map is a proper coloring of the actual finite conflict graph. -/
theorem exists_conflict_graph_coloring {k L : Nat} (hb : P.Bounded k L) :
    ∃ f : Index D → Fin (2 * L + 2 * k),
      ∀ i j, P.conflictGraph.Adj i j → f i ≠ f j :=
  P.exists_coloring hb

#print axioms exists_coloring
end Paths
end StackSorting.AdhesionGuidance
