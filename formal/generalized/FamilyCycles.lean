import FamilyInitial
import BlockCycles

namespace StackSorting.Generalized
namespace BasisFamily

/-- Increasing embedding of an old relay followed by the next two inputs;
the intervening already-output record is skipped. -/
def relayMap (e k : Nat) : Nat := if k = 0 then e else e+k+1

theorem relayMap_injective (e : Nat) : Function.Injective (relayMap e) := by
  intro a b he
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [relayMap, ha, hb] at he ⊢ <;> omega

theorem relay_cycle {s limit e : Nat} (hs : 2 ≤ s) (he : 2 ≤ e) (out : List Nat)
    (h : RangeLazyRun 2 s limit (e+2) [e,1] ((e+3) :: e :: out)) :
    RangeLazyRun 2 s limit (e+4) [e+2,1] out := by
  rcases h.cons_cases with ⟨after, pop, tail⟩ |
    ⟨before, after, lower, upper, fresh, read, pop, tail⟩
  · have hm := pop.pop_mem
    simp at hm
  · have hread : Run 2 s [e,1] [e+2,e+3] [] before := by
      have hc : e+3+1-(e+2) = 2 := by omega
      simpa [hc, List.range'_succ, Nat.add_assoc] using read
    rcases tail.cons_cases with ⟨final, hp, hr⟩ |
      ⟨before', after', lower', upper', fresh', read', pop', tail'⟩
    · have hcycle := singleton_record_cycle (relayMap e) (relayMap_injective e) s [1] final hs
        (by simp [relayMap] <;> omega) (by simp [relayMap] <;> omega)
      have hrecord : RecordStep s [relayMap e 1, relayMap e 2] (relayMap e 2)
          (relayMap e 0 :: [1]) after := by
        refine ⟨before, ?_, ?_⟩
        · simpa [relayMap, Nat.add_assoc] using hread
        · simpa [relayMap, Nat.add_assoc] using pop
      have hfinal := hcycle.mp ⟨after, hrecord, by simpa [relayMap] using hp⟩
      simpa [hfinal, relayMap, Nat.add_assoc] using hr
    · omega

theorem pair_prefix {s limit : Nat} (hs : 3 ≤ s) (m : Nat) (out : List Nat)
    (h : RangeLazyRun 2 s limit (s+2) [s,1] (pairs s m ++ out)) :
    RangeLazyRun 2 s limit (s+2*m+2) [s+2*m,1] out := by
  induction m generalizing out with
  | zero => simpa [pairs] using h
  | succ m ih =>
    have hp : RangeLazyRun 2 s limit (s+2) [s,1]
        (pairs s m ++ [s+3+2*m,s+2*m] ++ out) := by
      simpa [pairs_succ] using h
    have hm := ih ([s+3+2*m,s+2*m] ++ out) (by simpa [List.append_assoc] using hp)
    have hm' : RangeLazyRun 2 s limit ((s+2*m)+2) [s+2*m,1]
        (((s+2*m)+3) :: (s+2*m) :: out) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
    have ht := relay_cycle (by omega) (by omega) out hm'
    have hn : s+2*(m+1)+2 = s+2*m+4 := by omega
    have hr : s+2*(m+1) = s+2*m+2 := by omega
    rw [hn, hr]
    exact ht

theorem intact_before_terminal (s m : Nat) (hs : 3 ≤ s)
    (h : RangeLazyRun 2 s (2*s+2+2*m) 0 [] (rho s m)) :
    RangeLazyRun 2 s (2*s+2+2*m) (s+2*m+2) [s+2*m,1]
      ([2*s+1+2*m,1,s+2*m] ++ List.range' (s+2+2*m) (s-1)) := by
  apply pair_prefix hs m
  apply initial_prefix hs
  simpa [rho, List.append_assoc] using h

#print axioms relay_cycle
#print axioms pair_prefix
#print axioms intact_before_terminal
end BasisFamily
end StackSorting.Generalized
