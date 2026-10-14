import PersistentRestrictionWord
import GuidanceInducedRestriction
import DecompositionFiniteSurgery
import GuidanceBiInterfaceIso

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord GuidedPathwidth
variable {k c : Nat} {V : Type}

noncomputable def persistentFinset (G : Graph k V) : Finset V := by
  classical
  exact Finset.univ.image (Subtype.val : Persistent G → V)

@[simp] theorem mem_persistentFinset (G : Graph k V) (x : V) :
    x ∈ persistentFinset G ↔ x ∈ Persistent G := by
  classical
  simp [persistentFinset]

theorem persistentFinset_card_le (G : Graph k V) : (persistentFinset G).card ≤ k := by
  classical
  exact (Finset.card_image_le).trans (by simpa using persistent_card_le G)

/-- Persistent deletion is performed on the existing captured decomposition,
then re-expressed on the genuine induced graph of surviving vertices. -/
theorem exists_guided_removePersistent [Finite V] (G : Graph k V)
    (D : GuidedDecomposition G.simple Set.univ c) :
    Nonempty (GuidedDecomposition (removePersistent G).simple Set.univ (2^k*c)) := by
  obtain ⟨E⟩ := D.exists_deleteFinset (persistentFinset G)
  have hc : 2^(persistentFinset G).card*c ≤ 2^k*c :=
    Nat.mul_le_mul_right c (Nat.pow_le_pow_right (by omega) (persistentFinset_card_le G))
  have he : Set.univ \ (persistentFinset G : Set V) = (Persistent G)ᶜ := by
    ext x; simp
  let E' : GuidedDecomposition G.simple (Persistent G)ᶜ (2^k*c) := he ▸ E.pad hc
  exact ⟨E'.induced⟩

/-- Restore the exact deleted persistent vertices with at most k new colors. -/
theorem exists_guided_restorePersistent [Finite V] (G : Graph k V)
    (D : GuidedDecomposition (removePersistent G).simple Set.univ c) :
    Nonempty (GuidedDecomposition G.simple Set.univ (c+k)) := by
  let E : GuidedDecomposition G.simple (Persistent G)ᶜ c :=
    GuidedDecomposition.ofInduced (G := G.simple) (P := (Persistent G)ᶜ) D
  have he : (Persistent G)ᶜ = Set.univ \ (persistentFinset G : Set V) := by
    ext x; simp
  obtain ⟨F⟩ := GuidedDecomposition.exists_restoreFinset (persistentFinset G) (he ▸ E)
  exact ⟨F.pad (Nat.add_le_add_left (persistentFinset_card_le G) _)⟩
end StackSorting.BiInterface.RepeatedColumn
