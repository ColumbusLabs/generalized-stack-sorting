import BiInterfaceSeparatorRegions
import TorsoAbstraction
import Mathlib.Data.Finset.Option

namespace StackSorting.BiInterface
open scoped BigOperators
universe u
variable {k : Nat} {V W : Type u}

noncomputable def namedFinset (p : Fin k → Option V) : Finset V := by
  classical
  exact Finset.univ.biUnion (fun i => (p i).toFinset)

@[simp] theorem mem_namedFinset (p : Fin k → Option V) (x : V) :
    x ∈ namedFinset p ↔ x ∈ namedVertices p := by
  classical
  simp [namedFinset,namedVertices,Option.mem_def]

theorem namedFinset_card_le (p : Fin k → Option V) : (namedFinset p).card ≤ k := by
  classical
  calc
    (namedFinset p).card ≤ ∑ i : Fin k, (p i).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin k, 1 := Finset.sum_le_sum (by
      intro i _
      cases p i <;> simp)
    _ = k := by simp

noncomputable def boundaryFinset (G : Graph k V) : Finset V := by
  classical
  exact namedFinset G.left ∪ namedFinset G.right

@[simp] theorem mem_boundaryFinset (G : Graph k V) (x : V) :
    x ∈ boundaryFinset G ↔ x ∈ G.boundary := by
  classical
  simp only [boundaryFinset,Finset.mem_union,mem_namedFinset]
  constructor
  · rintro (⟨i,hi⟩ | ⟨i,hi⟩)
    · exact ⟨(false,i),hi⟩
    · exact ⟨(true,i),hi⟩
  · rintro ⟨⟨b,i⟩,hi⟩
    cases b
    · exact Or.inl ⟨i,hi⟩
    · exact Or.inr ⟨i,hi⟩

theorem boundaryFinset_card_le (G : Graph k V) : (boundaryFinset G).card ≤ 2*k := by
  classical
  exact (Finset.card_union_le _ _).trans
    (by have h := Nat.add_le_add (namedFinset_card_le G.left) (namedFinset_card_le G.right); omega)

noncomputable def joinBoundaryFinset (G : Graph k V) (H : Graph k W) : Finset (Glued G H) := by
  classical
  exact (namedFinset G.right).image (inLeft G H) ∪
    (namedFinset H.left).image (inRight G H)

@[simp] theorem mem_joinBoundaryFinset (G : Graph k V) (H : Graph k W) (x : Glued G H) :
    x ∈ joinBoundaryFinset G H ↔ x ∈ joinBoundary G H := by
  classical
  simp [joinBoundaryFinset,joinBoundary]

theorem joinBoundaryFinset_card_le (G : Graph k V) (H : Graph k W) :
    (joinBoundaryFinset G H).card ≤ 2*k := by
  classical
  calc
    (joinBoundaryFinset G H).card ≤
        ((namedFinset G.right).image (inLeft G H)).card +
        ((namedFinset H.left).image (inRight G H)).card := Finset.card_union_le _ _
    _ ≤ (namedFinset G.right).card + (namedFinset H.left).card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ ≤ k+k := Nat.add_le_add (namedFinset_card_le _) (namedFinset_card_le _)
    _ = 2*k := by omega
end StackSorting.BiInterface
