import GuidedDisjointInterfaceWord
import GuidedPersistentDeletion

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord GuidedPathwidth
variable {k c : Nat}

/-- Actual unbounded-arity idempotent composition, including deletion and
restoration of persistent interfaces. No guidance witness for the output is
assumed. The explicit coarse bound is independent of the number of factors. -/
theorem exists_guided_idempotent_word (e : Abstract k) (he : e*e=e)
    (ps : List (Packed.{0} k)) (hne : ps ≠ [])
    (hp : ∀ P ∈ ps, abstractGraph P.graph = e)
    (D : ∀ P ∈ ps, Nonempty (GuidedDecomposition P.graph.simple Set.univ c)) :
    Nonempty (GuidedDecomposition (Packed.eval ps).graph.simple Set.univ (2^(3*k)*c+9*k)) := by
  obtain ⟨e',he',hp'⟩ := exists_removed_common_idempotent e he ps hp
  let qs := ps.map removePackedPersistent
  have hq : ∀ Q ∈ qs, abstractGraph Q.graph = e' := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hQ
    exact hp' P hP
  have hd : ∀ Q ∈ qs, DisjointInterfaces Q.graph := by
    intro Q hQ
    obtain ⟨P,_,rfl⟩ := List.mem_map.mp hQ
    exact removePersistent_disjoint P.graph
  have hD : ∀ Q ∈ qs, Nonempty (GuidedDecomposition Q.graph.simple Set.univ (2^k*c)) := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hQ
    obtain ⟨E⟩ := D P hP
    exact exists_guided_removePersistent P.graph E
  obtain ⟨E⟩ := exists_guided_disjointInterface_word e' he' qs hq hd hD
  let E' := (restrictionEvalIso e he ps hne hp).mapGuided E
  obtain ⟨F⟩ := exists_guided_restorePersistent (Packed.eval ps).graph E'
  have hc : 2^(2*k)*(2^k*c)+8*k+k = 2^(3*k)*c+9*k := by
    rw [← Nat.mul_assoc,← pow_add]
    have he : 2*k+k = 3*k := by omega
    rw [he]
    omega
  exact ⟨hc ▸ F⟩

#print axioms exists_guided_idempotent_word
end StackSorting.BiInterface.RepeatedColumn
