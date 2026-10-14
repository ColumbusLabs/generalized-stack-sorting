import InterfaceFiniteSets
import DecompositionFiniteSurgery
import DecompositionDisjointUnion
import DecompositionEmbedding

namespace StackSorting.BiInterface
open GuidedPathwidth
universe u
variable {k c : Nat} {V W : Type u} [Finite V] [Finite W]

/-- Actual quotient gluing of two captured finite graphs admits a captured
forest decomposition. The coarse palette bound depends only on the interface
size and the common input palette. -/
theorem exists_guided_glue (G : Graph k V) (H : Graph k W)
    (D : GuidedDecomposition G.simple Set.univ c)
    (E : GuidedDecomposition H.simple Set.univ c) :
    Nonempty (GuidedDecomposition (glue G H).simple Set.univ (2^k*c+2*k)) := by
  classical
  obtain ⟨D₀⟩ := D.exists_deleteFinset (namedFinset G.right)
  obtain ⟨E₀⟩ := E.exists_deleteFinset (namedFinset H.left)
  have hcG : 2^(namedFinset G.right).card*c ≤ 2^k*c :=
    Nat.mul_le_mul_right c (Nat.pow_le_pow_right (by omega) (namedFinset_card_le _))
  have hcH : 2^(namedFinset H.left).card*c ≤ 2^k*c :=
    Nat.mul_le_mul_right c (Nat.pow_le_pow_right (by omega) (namedFinset_card_le _))
  have hPG : Set.univ \ (namedFinset G.right : Set V) = (namedVertices G.right)ᶜ := by
    ext x; simp
  have hPH : Set.univ \ (namedFinset H.left : Set W) = (namedVertices H.left)ᶜ := by
    ext x; simp
  let D₁ : GuidedDecomposition G.simple (namedVertices G.right)ᶜ (2^k*c) :=
    hPG ▸ D₀.pad hcG
  let E₁ : GuidedDecomposition H.simple (namedVertices H.left)ᶜ (2^k*c) :=
    hPH ▸ E₀.pad hcH
  let f : V ↪ Glued G H := ⟨inLeft G H,inLeft_injective G H⟩
  let g : W ↪ Glued G H := ⟨inRight G H,inRight_injective G H⟩
  let D₂ : GuidedDecomposition (glue G H).simple (leftInteriorImage G H) (2^k*c) :=
    D₁.mapRegion f (fun {a b} h => Or.inl ⟨a,b,h,rfl,rfl⟩)
      (fun ha _ h => leftInterior_reflects_adj G H ha h)
  let E₂ : GuidedDecomposition (glue G H).simple (rightInteriorImage G H) (2^k*c) :=
    E₁.mapRegion g (fun {a b} h => Or.inr ⟨a,b,h,rfl,rfl⟩)
      (fun ha _ h => rightInterior_reflects_adj G H ha h)
  let F := D₂.disjointUnion E₂ (interiorImages_disjoint G H)
    (fun _ ha _ hb => interiorImages_no_edge G H ha hb)
  have hP : leftInteriorImage G H ∪ rightInteriorImage G H =
      Set.univ \ (joinBoundaryFinset G H : Set (Glued G H)) := by
    rw [interiorImages_cover]
    ext x; simp
  obtain ⟨F'⟩ := GuidedDecomposition.exists_restoreFinset (joinBoundaryFinset G H) (hP ▸ F)
  exact ⟨F'.pad (Nat.add_le_add_left (joinBoundaryFinset_card_le G H) _)⟩

#print axioms exists_guided_glue
end StackSorting.BiInterface
