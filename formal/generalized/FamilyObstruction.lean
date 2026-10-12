import FamilyCycles
import BlockTerminal

namespace StackSorting.Generalized
namespace BasisFamily

theorem relayMap_range (e k n : Nat) (hk : 0 < k) :
    (List.range' k n).map (relayMap e) = List.range' (e+k+1) n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have hn : k ≠ 0 := by omega
    simp only [List.range'_succ, List.map_cons, relayMap, hn, ite_false]
    have ht := ih (k+1) (by omega)
    change (e+k+1) :: (List.range' (k+1) n).map (relayMap e) = _
    rw [ht]
    simp [Nat.add_assoc]

theorem terminal_no_run {s limit e : Nat} (hs : 3 ≤ s) (he : 2 ≤ e) (out : List Nat) :
    ¬ RangeLazyRun 2 s limit (e+2) [e,1] ((e+s+1) :: 1 :: out) := by
  intro h
  rcases h.cons_cases with ⟨after, pop, tail⟩ |
    ⟨before, after, lower, upper, fresh, read, pop, tail⟩
  · have hm := pop.pop_mem
    simp at hm
    omega
  · have hread : Run 2 s [e,1] (List.range' (e+2) s) [] before := by
      have hc : e+s+1+1-(e+2) = s := by omega
      simpa [hc] using read
    rcases tail.cons_cases with ⟨final, hp, hr⟩ |
      ⟨before', after', lower', upper', fresh', read', pop', tail'⟩
    · have habs : ∀ k, relayMap e k ≠ 1 := by
        intro k
        by_cases hk : k = 0 <;> simp [relayMap, hk] <;> omega
      apply singleton_terminal_obstruction (relayMap e) (relayMap_injective e) s 1
        (by omega) habs final
      refine ⟨after, ⟨before, ?_, ?_⟩, hp⟩
      · simpa [relayMap_range e 1 s (by decide), relayMap, Nat.add_assoc] using hread
      · have hn : s ≠ 0 := by omega
        simpa [relayMap, hn] using pop
    · omega

/-- Every member of the literal uniform family is rejected by the original
(2,s) machine, not merely by a symbolic-state recognizer. -/
theorem rho_not_generated (s m : Nat) (hs : 3 ≤ s) :
    ¬ Run 2 s [] (List.range (2*s+2+2*m)) (rho s m) [] := by
  intro h
  have hl := generated_rangeLazy h
  have ht := intact_before_terminal s m hs hl
  have he : 2*s+1+2*m = (s+2*m)+s+1 := by omega
  have ht' : RangeLazyRun 2 s (2*s+2+2*m) ((s+2*m)+2) [s+2*m,1]
      (((s+2*m)+s+1) :: 1 :: ((s+2*m) :: List.range' (s+2+2*m) (s-1))) := by
    simpa [he] using ht
  exact terminal_no_run hs (by omega) _ ht'

/-- The executable no-bypass semantics rejects the same family. -/
theorem rho_no_executable_trace (s m : Nat) (hs : 3 ≤ s) :
    ¬ ∃ ops, run 2 s ops [] = some ([], rho s m) ∧
      inputs ops = List.range (2*s+2+2*m) := by
  rw [← run_relational_iff]
  exact rho_not_generated s m hs

#print axioms rho_not_generated
#print axioms rho_no_executable_trace
end BasisFamily
end StackSorting.Generalized
