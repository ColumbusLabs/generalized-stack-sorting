import GeneralizedClauseFaces
import GeneralizedCoordinateRanks
import ZeroRestrictionIntersection

/-! Ordinary Z/B/T factors as literal hereditary upper bounds on old-label
insertion ranks. These are semantic constraints on a total physical order. -/
namespace StackSorting.Generalized.Decorated
open Coordinates StackSorting.MonotoneElimination

/-- The clause-free, O-free factors required by the terminal-clause counting
application. No reachability or counting assertion is included. -/
def Unary (state : State) : Prop :=
  ∀ factor ∈ state, factor = .Z ∨ factor = .B ∨ factor = .T

def threshold : Factor → Nat
  | .Z => 0
  | .B => 1
  | .T => 2
  | _ => 0

def boundsAt : State → Nat → List (Nat × Nat)
  | [], _ => []
  | factor :: rest, next => (next, threshold factor) :: boundsAt rest (next+1)

def RankBounds (bounds : List (Nat × Nat)) (physical : List Nat) : Prop :=
  ∀ label bound, (label, bound) ∈ bounds → rankSlot physical label ≤ bound

def BoundEligible (bounds : List (Nat × Nat)) : Eligibility :=
  fun U v => ∀ label bound, (label, bound) ∈ bounds →
    v = label → smallerCount U v ≤ bound

theorem unary_height {state : State} (h : Unary state) : height state = state.length := by
  induction state with
  | nil => rfl
  | cons factor rest ih =>
    have hf := h factor (by simp)
    have ht : Unary rest := fun f hm => h f (by simp [hm])
    rcases hf with rfl | rfl | rfl <;> simpa [height, Factor.height, Nat.add_comm] using ih ht

theorem unary_tail {factor : Factor} {rest : State} (h : Unary (factor :: rest)) : Unary rest :=
  fun f hm => h f (by simp [hm])

theorem factor_unary_singleton {factor : Factor}
    (h : factor = .Z ∨ factor = .B ∨ factor = .T) (d : Nat) :
    factor.denotes [d] ↔ d ≤ threshold factor := by
  rcases h with rfl | rfl | rfl <;> simp [Factor.denotes, threshold] <;> omega

theorem rankWord_append (physical : List Nat) (next a b : Nat) :
    rankWord physical next (a+b) =
      rankWord physical next a ++ rankWord physical (next+a) b := by
  unfold rankWord
  rw [← List.map_append, List.range'_append_1]

theorem denotes_unary_rankWord {state : State} (h : Unary state)
    (physical : List Nat) (next : Nat) :
    denotes state (rankWord physical next state.length) ↔
      RankBounds (boundsAt state next) physical := by
  induction state generalizing next with
  | nil => simp [rankWord, denotes, RankBounds, boundsAt]
  | cons factor rest ih =>
    have hf := h factor (by simp)
    have ht := unary_tail h
    have hlen : factor.height = 1 := by rcases hf with rfl | rfl | rfl <;> rfl
    have hword : rankWord physical next (factor :: rest).length =
        rankSlot physical next :: rankWord physical (next+1) rest.length := by
      simp [rankWord, List.range'_succ]
    rw [hword]
    constructor
    · rintro ⟨left, right, hleft, hright, he⟩
      have hl : left.length = 1 := (Factor.denotes_length hleft).trans hlen
      obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp hl
      have he' := List.cons.inj he
      rcases he' with ⟨hd, hr⟩
      subst d
      change rankWord physical (next+1) rest.length = right at hr
      subst right
      have hbound := (factor_unary_singleton hf _).mp hleft
      have hrest := (ih ht (next+1)).mp hright
      intro label bound hm
      simp only [boundsAt, List.mem_cons, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | hm
      · exact hbound
      · exact hrest label bound hm
    · intro hb
      refine ⟨[rankSlot physical next], rankWord physical (next+1) rest.length,
        (factor_unary_singleton hf _).mpr (hb next (threshold factor) (by simp [boundsAt])),
        (ih ht (next+1)).mpr ?_, rfl⟩
      intro label bound hm
      exact hb label bound (by simp [boundsAt, hm])

theorem rankSlot_split {physical above below : List Nat} {v : Nat}
    (hn : physical.Nodup) (he : physical = above ++ v :: below) :
    rankSlot physical v = smallerCount above v := by
  subst physical
  have hv : v ∉ above := by
    intro hm
    exact (List.nodup_append.mp hn).2.2 v hm v (by simp) rfl
  clear hn
  induction above with
  | nil => simp [rankSlot, smallerCount]
  | cons head above ih =>
    have hh : head ≠ v := by intro he; subst head; exact hv (by simp)
    have ht : v ∉ above := fun hm => hv (by simp [hm])
    simp only [List.cons_append, rankSlot, hh, ite_false, smallerCount,
      List.filter_cons, decide_eq_true_eq]
    rw [ih ht]
    by_cases hc : head < v <;> simp [hc, smallerCount] <;> omega

theorem rankBounds_iff_feasible {bounds : List (Nat × Nat)} {physical : List Nat}
    (hn : physical.Nodup) (hmem : ∀ label bound, (label,bound) ∈ bounds → label ∈ physical) :
    RankBounds bounds physical ↔ FeasibleOrder (BoundEligible bounds) physical := by
  rw [feasibleOrder_iff_prefixes]
  constructor
  · intro hb above v below he label bound hm hv
    subst label
    simpa [rankSlot_split hn he] using hb v bound hm
  · intro hf label bound hm
    obtain ⟨above, below, he⟩ := List.append_of_mem (hmem label bound hm)
    simpa [rankSlot_split hn he] using hf above label below he label bound hm rfl

theorem boundEligible_monotone (bounds : List (Nat × Nat)) : Monotone (BoundEligible bounds) := by
  intro U V v hn hsub hb label bound hm hv
  exact Nat.le_trans (smallerCount_mono hn hsub) (hb label bound hm hv)

theorem smallerCount_erase_self {U : List Nat} {v : Nat} (hn : U.Nodup) :
    smallerCount (U.erase v) v = smallerCount U v := by
  rw [smallerCount, smallerCount, hn.erase_eq_filter, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro w _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, by omega⟩

theorem boundEligible_self (bounds : List (Nat × Nat)) : SelfIndependent (BoundEligible bounds) := by
  intro U v hn _
  simp only [BoundEligible, smallerCount_erase_self hn]

#print axioms denotes_unary_rankWord
#print axioms rankBounds_iff_feasible
end StackSorting.Generalized.Decorated
