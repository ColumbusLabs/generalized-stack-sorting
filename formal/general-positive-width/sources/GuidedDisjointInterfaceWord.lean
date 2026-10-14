import WordColumnGeometry
import InterfaceFiniteSets
import DecompositionFiniteSurgery
import DecompositionFiniteUnion
import DecompositionEmbedding

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord GuidedPathwidth
variable {k c : Nat}

/-- A child decomposition is deleted on its actual named boundary and then
embedded into the exact interior image of its quotient column. -/
theorem exists_guided_columnInterior (ps : List (Packed.{0} k)) (i : Fin ps.length)
    (D : GuidedDecomposition (ps.get i).graph.simple Set.univ c) :
    Nonempty (GuidedDecomposition (Packed.eval ps).graph.simple
      (columnInterior (occurrenceAt ps i)) (2^(2*k)*c)) := by
  classical
  let P := ps.get i
  let h := occurrenceAt ps i
  obtain ⟨E⟩ := D.exists_deleteFinset (boundaryFinset P.graph)
  have hc : 2^(boundaryFinset P.graph).card*c ≤ 2^(2*k)*c :=
    Nat.mul_le_mul_right c (Nat.pow_le_pow_right (by omega) (boundaryFinset_card_le _))
  have heq : Set.univ \ (boundaryFinset P.graph : Set P.Vertex) = P.graph.boundaryᶜ := by
    ext x; simp
  let E' : GuidedDecomposition P.graph.simple P.graph.boundaryᶜ (2^(2*k)*c) := heq ▸ E.pad hc
  let f : P.Vertex ↪ (Packed.eval ps).Vertex := ⟨h.column,h.column_injective⟩
  refine ⟨E'.mapRegion f (fun hab => h.column_adj hab) ?_⟩
  intro a b ha hb hab
  obtain ⟨y,hay,hyb⟩ := edge_at_column_interior h a ha hab
  have hy : y = b := h.column_injective hyb
  exact hy ▸ hay

/-- Combine arbitrarily many actual column interiors while reusing the same
palette. Distinct interiors are proven disjoint and have no crossing edges. -/
theorem exists_guided_interiors (ps : List (Packed.{0} k))
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph)
    (D : ∀ P ∈ ps, Nonempty (GuidedDecomposition P.graph.simple Set.univ c)) :
    Nonempty (GuidedDecomposition (Packed.eval ps).graph.simple
      (wordColumnGeometry ps hd).inside (2^(2*k)*c)) := by
  classical
  let R : Fin ps.length → Set (Packed.eval ps).Vertex :=
    fun i => columnInterior (occurrenceAt ps i)
  have hc : ∀ i ∈ (Finset.univ : Finset (Fin ps.length)),
      Nonempty (GuidedDecomposition (Packed.eval ps).graph.simple (R i) (2^(2*k)*c)) := by
    intro i hi
    obtain ⟨E⟩ := D (ps.get i) (List.get_mem ps i)
    exact exists_guided_columnInterior ps i E
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin ps.length)), ∀ j ∈ Finset.univ,
      i ≠ j → Disjoint (R i) (R j) := by
    intro i hi j hj hij
    apply column_interiors_disjoint (occurrenceAt ps i) (occurrenceAt ps j)
    simpa only [occurrenceAt_index] using (fun h => hij (Fin.ext h))
  have hsep : ∀ i ∈ (Finset.univ : Finset (Fin ps.length)), ∀ j ∈ Finset.univ,
      i ≠ j → ∀ x ∈ R i, ∀ y ∈ R j, ¬ (Packed.eval ps).graph.simple.Adj x y := by
    intro i hi j hj hij x hx y hy
    apply no_edge_between_column_interiors (occurrenceAt ps i) (occurrenceAt ps j) _ hx hy
    simpa only [occurrenceAt_index] using (fun h => hij (Fin.ext h))
  obtain ⟨E⟩ := GuidedDecomposition.exists_finsetUnion R Finset.univ hc hdisj hsep
  have he : {x | ∃ j ∈ (Finset.univ : Finset (Fin ps.length)), x ∈ R j} =
      (wordColumnGeometry ps hd).inside := by
    ext x
    constructor
    · rintro ⟨i,_,hi⟩
      exact ⟨i,by rw [wordColumnGeometry_interior]; exact hi⟩
    · rintro ⟨i,hi⟩
      refine ⟨i,Finset.mem_univ _,?_⟩
      simpa only [wordColumnGeometry_interior] using hi
  exact ⟨he ▸ E⟩

/-- Genuine unbounded-arity composition after persistent interfaces have been
removed. Its palette does not depend on the number or size of the factors. -/
theorem exists_guided_disjointInterface_word (e : Abstract k) (he : e*e=e)
    (ps : List (Packed.{0} k)) (hp : ∀ P ∈ ps, abstractGraph P.graph = e)
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph)
    (D : ∀ P ∈ ps, Nonempty (GuidedDecomposition P.graph.simple Set.univ c)) :
    Nonempty (GuidedDecomposition (Packed.eval ps).graph.simple Set.univ (2^(2*k)*c+8*k)) := by
  obtain ⟨E⟩ := exists_guided_interiors ps hd D
  exact (wordColumnGeometry ps hd).exists_guided_graft (columnGuides ps hd)
    (columnGuides_routes e he ps hp hd) E

#print axioms exists_guided_disjointInterface_word
end StackSorting.BiInterface.RepeatedColumn
