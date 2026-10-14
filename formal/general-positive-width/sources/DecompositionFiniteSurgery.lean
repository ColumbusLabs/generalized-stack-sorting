import DecompositionAddition
import GuidedDecompositionBase

namespace StackSorting.GuidedPathwidth
universe u
variable {V : Type u} [Finite V] {G : SimpleGraph V} {P : Set V} {c : Nat}
namespace GuidedDecomposition

/-- Restore a specified finite set of actual vertices, with one additional
color per vertex. Every intermediate index forest and guide is constructed. -/
theorem exists_restoreFinset (S : Finset V)
    (D : GuidedDecomposition G (P \ (S : Set V)) c) :
    Nonempty (GuidedDecomposition G P (c + S.card)) := by
  classical
  induction S using Finset.induction_on generalizing P with
  | empty =>
    simpa using (show Nonempty (GuidedDecomposition G P c) from
      ⟨by simpa using D⟩)
  | @insert u S hu ih =>
    have heq : P \ ((insert u S : Finset V) : Set V) =
        (P \ {u}) \ (S : Set V) := by
      ext x
      simp only [Finset.coe_insert,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    have D' : GuidedDecomposition G ((P \ {u}) \ (S : Set V)) c := heq ▸ D
    obtain ⟨E⟩ := ih D'
    obtain ⟨F⟩ := exists_restoreVertex u E
    exact ⟨by simpa [Finset.card_insert_of_notMem hu,Nat.add_assoc] using F⟩

/-- Delete a specified finite set, splitting bags into actual remaining graph
components at each step. The palette cost is at most doubling per vertex. -/
theorem exists_deleteFinset (S : Finset V) (D : GuidedDecomposition G P c) :
    Nonempty (GuidedDecomposition G (P \ (S : Set V)) (2 ^ S.card * c)) := by
  classical
  induction S using Finset.induction_on generalizing P c with
  | empty => simpa using (show Nonempty (GuidedDecomposition G P c) from ⟨D⟩)
  | @insert u S hu ih =>
    obtain ⟨E⟩ := ih (D.deleteVertex u)
    have heq : (P \ {u}) \ (S : Set V) =
        P \ ((insert u S : Finset V) : Set V) := by
      ext x
      simp only [Finset.coe_insert,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    have hn : 2 ^ S.card * (c+c) = 2 ^ (insert u S).card * c := by
      rw [Finset.card_insert_of_notMem hu,pow_succ]
      ring
    exact ⟨by simpa only [heq,hn] using E⟩
end GuidedDecomposition

#print axioms GuidedDecomposition.exists_restoreFinset
#print axioms GuidedDecomposition.exists_deleteFinset
end StackSorting.GuidedPathwidth
