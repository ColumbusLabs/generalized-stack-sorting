import GeneralizedActualCounting
import GeneralizedDecoratedTransitions
import GeneralizedDecoratedRecords

/-! Finite, complete lazy codes for an actual initially-held state. The
remaining-input budget is explicit, so the first-letter partition reduces
held height plus future inputs by one and counts no physical histories. -/
namespace StackSorting.Generalized
namespace LazyCode

inductive Budget : Nat → Nat → List Letter → Prop where
  | nil : Budget 0 0 []
  | held {h n k : Nat} {code : List Letter}
      (positive : 0 < k) (valid : k ≤ h) (tail : Budget (h-1) n code) :
      Budget h n (.H k :: code)
  | record {h n b : Nat} {code : List Letter}
      (positive : 0 < b) (valid : b ≤ n) (tail : Budget (h+b-1) (n-b) code) :
      Budget h n (.N b :: code)

theorem Budget.length {h n : Nat} {code : List Letter} (hb : Budget h n code) :
    code.length = h+n := by
  induction hb with
  | nil => rfl
  | held positive valid tail ih => simp only [List.length_cons]; omega
  | record positive valid tail ih => simp only [List.length_cons]; omega

/-- Per-size boundedness follows from the exact remaining supply; this is
not a fixed capacity bound or a truncated-class theorem. -/
theorem Budget.bounded {h n H : Nat} {code : List Letter}
    (hb : Budget h n code) (bound : h+n ≤ H) : Bounded H h code := by
  induction hb with
  | nil => exact .nil
  | held positive valid tail ih =>
    exact .held positive valid (ih (by omega))
  | record positive valid tail ih =>
    exact .record positive (by omega) (ih (by omega))

/-- A literal decoding determines exactly its finite remaining-input budget. -/
theorem Decodes.budget {limit next : Nat} {held output : List Nat} {code : List Letter}
    (hd : Decodes limit next held code output) : Budget held.length (limit-next) code := by
  induction hd with
  | nil => simpa using Budget.nil
  | @held next a pre post code output old tail ih =>
    have hs : (pre ++ a :: post).length-1 = (pre ++ post).length := by simp
    exact .held (by omega) (by simp) (by simpa [hs] using ih)
  | @record next a held code output new tail ih =>
    have hlimit := tail.supply.1
    have hb : 0 < a+1-next := by omega
    have hv : a+1-next ≤ limit-next := by omega
    have hh : held.length+(a+1-next)-1 = (held ++ List.range' next (a-next)).length := by
      simp only [List.length_append, List.length_range']; omega
    have hn : (limit-next)-(a+1-next) = limit-(a+1) := by omega
    exact .record hb hv (by simpa [hh, hn] using ih)

/-- Every budget-valid code decodes completely from the specified old labels,
with its final input bound derived from the code length and supply invariant. -/
theorem Budget.decodes {h n next : Nat} {code : List Letter} {held : List Nat}
    (hb : Budget h n code) (hlen : held.length = h) (inv : HeldInvariant next held) :
    ∃ output, Decodes (next+n) next held code output := by
  obtain ⟨limit, output, hd⟩ := (hb.bounded (Nat.le_refl _)).decodes hlen inv
  have supply := hd.supply
  have hl : output.length = held.length + (limit-next) := by
    simpa using supply.2.length_eq
  have hc := hd.length
  have he : limit = next+n := by have h := hb.length; omega
  subst limit
  exact ⟨output, hd⟩

def budgetCheck (h n : Nat) : List Letter → Bool
  | [] => decide (h = 0 ∧ n = 0)
  | .H k :: code => decide (0 < k ∧ k ≤ h) && budgetCheck (h-1) n code
  | .N b :: code => decide (0 < b ∧ b ≤ n) && budgetCheck (h+b-1) (n-b) code

theorem budgetCheck_iff (h n : Nat) (code : List Letter) :
    budgetCheck h n code = true ↔ Budget h n code := by
  induction code generalizing h n with
  | nil =>
    simp only [budgetCheck, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact .nil
    · intro hb; cases hb; exact ⟨rfl, rfl⟩
  | cons letter code ih =>
    cases letter with
    | H k =>
      simp only [budgetCheck, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨⟨hp, hv⟩, ht⟩; exact .held hp hv ht
      · intro hb; cases hb with | held hp hv ht => exact ⟨⟨hp, hv⟩, ht⟩
    | N b =>
      simp only [budgetCheck, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨⟨hp, hv⟩, ht⟩; exact .record hp hv ht
      · intro hb; cases hb with | record hp hv ht => exact ⟨⟨hp, hv⟩, ht⟩

end LazyCode

namespace Decorated
open LazyCode

/-- Complete distinct lazy-code language of the actual physical subset
represented by a factor state. Realizing physical orders are existential. -/
def CodeCompletion (state : State) (n : Nat) (code : List Letter) : Prop :=
  Budget (height state) n code ∧
    ∃ physical, Represents state physical ∧
      [] ∈ rankCodeOrders 3 3 (height state) code physical

/-- The empty code contributes exactly one code, and only when all supplied
tokens are exhausted and the state represents the empty physical stack. -/
theorem codeCompletion_nil (state : State) (n : Nat) :
    CodeCompletion state n [] ↔
      height state = 0 ∧ n = 0 ∧ Represents state [] := by
  constructor
  · rintro ⟨hb, physical, hp, ha⟩
    have hz : height state = 0 ∧ n = 0 := by
      have hc := (budgetCheck_iff _ _ _).mpr hb
      simpa [budgetCheck] using hc
    have he : physical = [] := by
      have he' : [] = physical := by simpa [rankCodeOrders] using ha
      exact he'.symm
    exact ⟨hz.1, hz.2, he ▸ hp⟩
  · rintro ⟨hh, hn, hp⟩
    refine ⟨?_, [], hp, by simp [rankCodeOrders]⟩
    simpa [hh, hn] using Budget.nil

/-- Exact H_k first-letter partition, retaining each value rank as a separate
letter even if two ranks have the same represented successor state. -/
theorem codeCompletion_held (state : State) (n k : Nat) (code : List Letter) :
    CodeCompletion state n (.H k :: code) ↔
      0 < k ∧ k ≤ height state ∧ Budget (height state-1) n code ∧
      ∃ after, PhysicalPopImage state (k-1) after ∧
        [] ∈ rankCodeOrders 3 3 (height state-1) code after := by
  constructor
  · rintro ⟨hb, physical, hp, ha⟩
    have hc := (budgetCheck_iff _ _ _).mpr hb
    simp only [budgetCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨positive, valid⟩, tailCheck⟩ := hc
    have tail := (budgetCheck_iff _ _ _).mp tailCheck
    have hs : ∃ after, after ∈ rankPopOrders 3 k physical ∧
        [] ∈ rankCodeOrders 3 3 (height state-1) code after := by
      simpa [rankCodeOrders, positive, List.mem_flatMap] using ha
    obtain ⟨after, hpop, htail⟩ := hs
    have hk : k-1+1 = k := by omega
    exact ⟨positive, valid, tail, after,
      ⟨physical, hp, by simpa [hk] using hpop⟩, htail⟩
  · rintro ⟨positive, valid, tail, after, ⟨physical, hp, hpop⟩, htail⟩
    have hk : k-1+1 = k := by omega
    refine ⟨.held positive valid tail, physical, hp, ?_⟩
    simp only [rankCodeOrders, positive, ite_true, List.mem_flatMap]
    exact ⟨after, by simpa [hk] using hpop, htail⟩

/-- Exact N_b first-letter partition at all heights and all batch sizes.
The final record consumes one input but does not remain held. -/
theorem codeCompletion_record (state : State) (n b : Nat) (code : List Letter) :
    CodeCompletion state n (.N b :: code) ↔
      0 < b ∧ b ≤ n ∧ Budget (height state+b-1) (n-b) code ∧
      ∃ physical after, Represents state physical ∧
        after ∈ rankReadOrders 3 (height state) (b-1) physical ∧
        [] ∈ rankCodeOrders 3 3 (height state+b-1) code after := by
  constructor
  · rintro ⟨hb, physical, hp, ha⟩
    have hc := (budgetCheck_iff _ _ _).mpr hb
    simp only [budgetCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨positive, valid⟩, tailCheck⟩ := hc
    have tail := (budgetCheck_iff _ _ _).mp tailCheck
    have hs : ∃ after, after ∈ rankReadOrders 3 (height state) (b-1) physical ∧
        [] ∈ rankCodeOrders 3 3 (height state+b-1) code after := by
      simpa [rankCodeOrders, positive, List.mem_flatMap] using ha
    obtain ⟨after, hread, htail⟩ := hs
    exact ⟨positive, valid, tail, physical, after, hp, hread, htail⟩
  · rintro ⟨positive, valid, tail, physical, after, hp, hread, htail⟩
    refine ⟨.record positive valid tail, physical, hp, ?_⟩
    simp only [rankCodeOrders, positive, ite_true, List.mem_flatMap]
    exact ⟨after, hread, htail⟩

end Decorated

#print axioms LazyCode.Budget.decodes
#print axioms LazyCode.Decodes.budget
#print axioms Decorated.codeCompletion_nil
#print axioms Decorated.codeCompletion_held
#print axioms Decorated.codeCompletion_record
end StackSorting.Generalized
