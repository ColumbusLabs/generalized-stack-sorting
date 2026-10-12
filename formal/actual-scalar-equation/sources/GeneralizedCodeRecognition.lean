import GeneralizedLazyCode

/-! Exact local physical-stack semantics for the N_b/H_k code recognizer.
All stacks remain top first. Ordered held labels give value rank only.
This module does not identify deletion shadows or a serialized DFA with basis.
-/
namespace StackSorting.Generalized
open List

/-- Erasing a fresh input token that is the sole output removes its entire
physical history, without changing the final physical order of survivors. -/
theorem Run.cancel_fresh_singleton {r s a : Nat} {held input after : List Nat}
    (h : Run r s held (input ++ [a]) [a] after)
    (freshHeld : a ∉ held) (freshInput : a ∉ input) :
    Run r s held input [] after := by
  have hc := h.supply.count_eq a
  have hz : after.count a = 0 := by
    simpa [List.count_append, List.count_eq_zero.mpr freshHeld,
      List.count_eq_zero.mpr freshInput] using hc.symm
  have freshAfter : a ∉ after := List.count_eq_zero.mp hz
  have filter_eq (xs : List Nat) (ha : a ∉ xs) :
      xs.filter (fun v => v != a) = xs := by
    apply List.filter_eq_self.mpr
    intro v hv
    simp only [bne_iff_ne]
    intro he
    exact ha (he ▸ hv)
  simpa [List.filter_append, filter_eq held freshHeld,
    filter_eq input freshInput, filter_eq after freshAfter] using
    h.filter (fun v => v != a)

/-- This is the literal recognizer's record shortcut, in both directions.
The excluded last token can be inserted/popped at slot zero at positive widths.
Freshness is required only for cancellation, not reconstructed history. -/
theorem record_segment_iff {r s a : Nat} {held input after : List Nat}
    (hr : 0 < r) (hs : 0 < s) (freshHeld : a ∉ held) (freshInput : a ∉ input) :
    (∃ before, Run r s held (input ++ [a]) [] before ∧
      Step r s before [] [a] after) ↔ Run r s held input [] after := by
  constructor
  · rintro ⟨before, read, pop⟩
    exact (by simpa using read.append (Run.single pop) :
      Run r s held (input ++ [a]) [a] after).cancel_fresh_singleton freshHeld freshInput
  · intro read
    have push : Step r s after [a] [] (a :: after) := Step.push [] after a hr
    have pop : Step r s (a :: after) [] [a] after := Step.pop [] after a hs
    exact ⟨a :: after, by simpa using read.append (Run.single push), pop⟩

/-- A concrete N_b record reads b labels, INCLUDING the output record. Its
recognizer successor physical orders are precisely the orders after b−1
ordinary restricted pushes. -/
theorem record_batch_iff {r s next b : Nat} {held after : List Nat}
    (hr : 0 < r) (hs : 0 < s) (hb : 0 < b)
    (heldOld : ∀ a ∈ held, a < next) :
    (∃ before, Run r s held (List.range' next b) [] before ∧
      Step r s before [] [next+b-1] after) ↔
    Run r s held (List.range' next (b-1)) [] after := by
  have hrange : List.range' next b = List.range' next (b-1) ++ [next+b-1] := by
    have he : b = (b-1)+1 := by omega
    have hs : next + (b-1) = next+b-1 := by omega
    calc
      List.range' next b = List.range' next ((b-1)+1) := congrArg (List.range' next) he
      _ = List.range' next (b-1) ++ [next+b-1] := by simp only [List.range'_concat, Nat.one_mul, hs]
  rw [hrange]
  apply record_segment_iff hr hs
  · intro hm
    have := heldOld _ hm
    omega
  · intro hm
    have := List.mem_range'.mp hm
    omega

/-- Literal transient height at the record pop: all b labels have been
inserted, and none has yet been emitted. This is h+b, not h+b−1. -/
theorem record_batch_height {r s next b : Nat} {held before after : List Nat}
    (read : Run r s held (List.range' next b) [] before)
    (pop : Step r s before [] [next+b-1] after) :
    before.length = held.length+b ∧ after.length+1 = held.length+b := by
  have hi := read.supply.length_eq
  have ho := pop.supply.length_eq
  simp only [List.length_append, List.length_range', List.length_nil,
    List.length_cons] at hi ho
  constructor <;> omega

namespace LazyCode

/-- Every legal zero-based push slot, applied to a top-first labelled stack.
Out-of-range physical positions produce none and are omitted. -/
def pushOrders (r a : Nat) (held : List Nat) : List (List Nat) :=
  (List.range r).filterMap (fun k => insertAt? k a held)

/-- The held token is addressed by its label here. Value-rank selection is
proved separately below; it is never confused with a physical pop slot. -/
def popOrders (s a : Nat) (held : List Nat) : List (List Nat) :=
  (List.range s).filterMap (fun k => do
    let (after, token) ← removeAt? k held
    if token = a then some after else none)

theorem mem_pushOrders_iff {r s a : Nat} {held after : List Nat} :
    after ∈ pushOrders r a held ↔ Step r s held [a] [] after := by
  constructor
  · intro h
    obtain ⟨k, hk, he⟩ := List.mem_filterMap.mp h
    have hk' : k < r := List.mem_range.mp hk
    exact step_relational r s (.push k a) held after [] (by simp [step, hk', he])
  · intro h
    cases h with
    | push pre post a allowed =>
      exact List.mem_filterMap.mpr ⟨pre.length, List.mem_range.mpr allowed,
        insertAt_prefix pre post a⟩

theorem mem_popOrders_iff {r s a : Nat} {held after : List Nat} :
    after ∈ popOrders s a held ↔ Step r s held [] [a] after := by
  constructor
  · intro h
    obtain ⟨k, hk, he⟩ := List.mem_filterMap.mp h
    have hk' : k < s := List.mem_range.mp hk
    cases hx : removeAt? k held with
    | none => simp [hx] at he
    | some p =>
      rcases p with ⟨xs, x⟩
      by_cases ha : x = a
      · subst x
        simp [hx] at he
        subst after
        exact step_relational r s (.pop k) held xs [a] (by simp [step, hk', hx])
      · simp [hx, ha] at he
  · intro h
    cases h with
    | pop pre post a allowed =>
      apply List.mem_filterMap.mpr
      exact ⟨pre.length, List.mem_range.mpr allowed, by simp [removeAt_prefix]⟩

/-- Successive top-r pushes in the exact input order. Duplicates in this
finite list are semantically ignored by membership. -/
def readOrders (r : Nat) : List Nat → List Nat → List (List Nat)
  | [], held => [held]
  | a :: input, held => (pushOrders r a held).flatMap (readOrders r input)

theorem run_mem_readOrders {r s : Nat} {held input output after : List Nat}
    (h : Run r s held input output after) (empty : output = []) :
    after ∈ readOrders r input held := by
  induction h with
  | nil => simp [readOrders]
  | cons head tail ih =>
    cases head with
    | push pre post a allowed =>
      simp only [List.nil_append] at empty
      apply List.mem_flatMap.mpr
      exact ⟨_, (mem_pushOrders_iff (s := s)).mpr (Step.push pre post a allowed), ih empty⟩
    | pop pre post a allowed => simp at empty

theorem mem_readOrders_iff {r s : Nat} {held input after : List Nat} :
    after ∈ readOrders r input held ↔ Run r s held input [] after := by
  constructor
  · intro h
    induction input generalizing held with
    | nil =>
      have he : after = held := by simpa [readOrders] using h
      subst after
      exact .nil held
    | cons a input ih =>
      obtain ⟨middle, hm, ht⟩ := List.mem_flatMap.mp h
      exact by simpa using Run.cons (mem_pushOrders_iff.mp hm) (ih ht)
  · intro h
    exact run_mem_readOrders h rfl

/-- Exact N_b transition of the executable physical-order enumerator. -/
theorem record_transition_iff {r s next b : Nat} {held after : List Nat}
    (hr : 0 < r) (hs : 0 < s) (hb : 0 < b)
    (heldOld : ∀ a ∈ held, a < next) :
    after ∈ readOrders r (List.range' next (b-1)) held ↔
    ∃ before, Run r s held (List.range' next b) [] before ∧
      Step r s before [] [next+b-1] after :=
  mem_readOrders_iff.trans (record_batch_iff hr hs hb heldOld).symm

/-- Executable labelled form of the literal subset recognizer. A finite list
represents the set of possible top-first physical stacks; duplicate list entries
are harmless. This deliberately retains original labels rather than quotienting
states by rank or identifying them with the external automaton's state IDs. -/
def codeOrders (r s : Nat) : Nat → List Nat → List Letter → List Nat → List (List Nat)
  | _, _, [], physical => [physical]
  | next, held, .N b :: code, physical =>
    if 0 < b then
      (readOrders r (List.range' next (b-1)) physical).flatMap
        (codeOrders r s (next+b) (held ++ List.range' next (b-1)) code)
    else []
  | next, held, .H k :: code, physical =>
    if 0 < k then
      match removeAt? (k-1) held with
      | none => []
      | some (after, a) => (popOrders s a physical).flatMap (codeOrders r s next after code)
    else []

/-- The H_k rank is taken in increasing held-value order, while legality is
checked independently against the first s physical stack positions. -/
theorem held_code_step {r s next a : Nat} {pre post physical final : List Nat} {code : List Letter} :
    final ∈ codeOrders r s next (pre ++ a :: post) (.H (pre.length+1) :: code) physical ↔
    ∃ after, Step r s physical [] [a] after ∧
      final ∈ codeOrders r s next (pre ++ post) (code) after := by
  simp only [codeOrders, Nat.zero_lt_succ, ite_true, Nat.add_sub_cancel,
    removeAt_prefix, List.mem_flatMap, mem_popOrders_iff (r := r)]

/-- A pop preserves the exact set of surviving labels even when its physical
position differs from the token's value rank. -/
theorem pop_remaining_perm {r s a : Nat} {physical after pre post : List Nat}
    (hp : physical.Perm (pre ++ a :: post)) (pop : Step r s physical [] [a] after) :
    after.Perm (pre ++ post) := by
  have hh : physical.Perm (a :: after) := by simpa using pop.supply
  exact ((hh.symm.trans hp).trans List.perm_middle).cons_inv

/-- Complete literal decoding gives an all-length semantic bridge from the
executable labelled subset recognizer to actual normalized machine histories.
No deletion, basis, width, finite-state closure, or DFA equivalence is assumed. -/
theorem Decodes.codeOrders_iff_rangeLazy {r s limit next : Nat}
    {held output physical : List Nat} {code : List Letter}
    (hd : Decodes limit next held code output) (hr : 0 < r) (hs : 0 < s)
    (inv : HeldInvariant next held) (hp : physical.Perm held) :
    [] ∈ codeOrders r s next held code physical ↔
      RangeLazyRun r s limit next physical output := by
  induction hd generalizing physical with
  | nil =>
    have he : physical = [] := List.perm_nil.mp hp
    subst physical
    constructor
    · intro _; exact .nil
    · intro _; simp [codeOrders]
  | @held next a pre post code output old tail ih =>
    have hstep : [] ∈ codeOrders r s next (pre ++ a :: post) (.H (pre.length+1) :: code) physical ↔
        ∃ after, Step r s physical [] [a] after ∧
          [] ∈ codeOrders r s next (pre ++ post) code after := by
      simp only [codeOrders, Nat.zero_lt_succ, ite_true, Nat.add_sub_cancel,
        removeAt_prefix, List.mem_flatMap, mem_popOrders_iff (r := r)]
    rw [hstep]
    constructor
    · rintro ⟨after, pop, htail⟩
      exact .held pop ((ih inv.remove (pop_remaining_perm hp pop)).mp htail)
    · intro h
      cases h with
      | held pop rest =>
        exact ⟨_, pop, (ih inv.remove (pop_remaining_perm hp pop)).mpr rest⟩
      | record lower _ _ _ _ _ => omega
  | @record next a held code output new tail ih =>
    have positive : 0 < a+1-next := by omega
    have hnext : next+(a+1-next) = a+1 := by omega
    have hcount : a+1-next-1 = a-next := by omega
    have hrecord : next+(a+1-next)-1 = a := by omega
    have old : ∀ v ∈ physical, v < next := fun v hv => inv.2 v (hp.mem_iff.mp hv)
    have hstep : [] ∈ codeOrders r s next held (.N (a+1-next) :: code) physical ↔
        ∃ after, Run r s physical (List.range' next (a-next)) [] after ∧
          [] ∈ codeOrders r s (a+1) (held ++ List.range' next (a-next)) code after := by
      simp only [codeOrders, positive, ite_true, hnext, hcount, List.mem_flatMap, mem_readOrders_iff (s := s)]
    rw [hstep]
    have afterPerm {after : List Nat}
        (read : Run r s physical (List.range' next (a-next)) [] after) :
        after.Perm (held ++ List.range' next (a-next)) := by
      have hh : (physical ++ List.range' next (a-next)).Perm after := by simpa using read.supply
      exact hh.symm.trans (hp.append_right _)
    constructor
    · rintro ⟨after, read, htail⟩
      have rest := (ih (inv.record new) (afterPerm read)).mp htail
      have hx := (record_batch_iff hr hs positive old).mpr (by simpa only [hcount] using read)
      obtain ⟨before, fullread, pop⟩ := hx
      have upper : a < limit := by have := rest.bound; omega
      have fresh : a ∉ physical := by intro ha; have := old a ha; omega
      exact .record new upper fresh fullread (by simpa only [hrecord] using pop) rest
    · intro h
      cases h with
      | held pop rest =>
        have ha : a ∈ physical := by
          have hm := pop.supply.mem_iff.mpr (by simp : a ∈ [a] ++ _)
          simpa using hm
        have := old a ha
        omega
      | record lower upper fresh fullread pop rest =>
        have read := (record_batch_iff hr hs positive old).mp
          ⟨_, fullread, by simpa only [hrecord] using pop⟩
        have read' := read
        rw [hcount] at read'
        exact ⟨_, read', (ih (inv.record new) (afterPerm read')).mpr rest⟩

/-- On every complete valid lazy code, the executable labelled recognizer
accepts exactly the permutations generated by the actual top-position machine.
This applies at every length and specializes to (3,3) without extra hypotheses. -/
theorem Decodes.codeOrders_iff_generated {r s n : Nat}
    {output : List Nat} {code : List Letter}
    (hd : Decodes n 0 [] code output) (hr : 0 < r) (hs : 0 < s) :
    [] ∈ codeOrders r s 0 [] code [] ↔ Run r s [] (List.range n) output [] :=
  (hd.codeOrders_iff_rangeLazy hr hs (by simp [HeldInvariant]) (List.Perm.refl [])).trans
    (generated_rangeLazy_iff r s n output)

/-- Executable acceptance test. This is a labelled order-list calculation,
not the minimized DFA, and no polynomial resource bound is asserted. -/
def recognizes (r s : Nat) (code : List Letter) : Bool :=
  (codeOrders r s 0 [] code []).contains []

theorem Decodes.recognizes_iff {r s n : Nat} {output : List Nat} {code : List Letter}
    (hd : Decodes n 0 [] code output) (hr : 0 < r) (hs : 0 < s) :
    recognizes r s code = true ↔ Run r s [] (List.range n) output [] := by
  simpa only [recognizes, List.contains_iff_mem] using hd.codeOrders_iff_generated hr hs

/-- Every actual permutation is recognized through its canonical executable
encoder. No bounded-width assumption is required for this semantic theorem. -/
theorem permutation_recognizes_iff {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s) :
    recognizes r s (encode 0 [] output) = true ↔ Run r s [] (List.range n) output [] := by
  have bound : ∀ pre a post, output = pre ++ a :: post → a+1 ≤ pre.length+n := by
    intro pre a post he
    have ha : a ∈ output := by simp [he]
    have hlt := List.mem_range.mp (hp.mem_iff.mp ha)
    omega
  obtain ⟨code, hd, _, _⟩ := permutation_unique_bounded_code hp bound
  rw [hd.encode_eq (by simp [HeldInvariant])]
  exact hd.recognizes_iff hr hs

/-- A direct all-one-deletion oracle. It recomputes each shortened canonical
code from its actual standardized permutation. It does NOT implement or assume
the annotation shadow transducer, merging, pruning, or serialized finite DFA. -/
def oneDeletionCheck (r s : Nat) (output : List Nat) : Bool :=
  !recognizes r s (encode 0 [] output) &&
    (List.range output.length).all (fun v => recognizes r s (encode 0 [] (deleteWord v output)))

/-- Exact executable rejection plus ordinary one-value minimality, with all
input/output words in generated orientation. The permutation premise is explicit. -/
theorem oneDeletionCheck_iff {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s) :
    oneDeletionCheck r s output = true ↔
      (¬ Run r s [] (List.range n) output []) ∧
      ∀ v ∈ List.range n, Run r s [] (List.range (n-1)) (deleteWord v output) [] := by
  have hlen : output.length = n := by simpa using hp.length_eq
  simp only [oneDeletionCheck, Bool.and_eq_true, Bool.not_eq_true',
    hlen, List.all_eq_true]
  have original := permutation_recognizes_iff hp hr hs
  have deleted (v : Nat) (hv : v ∈ List.range n) :=
    permutation_recognizes_iff (deleteWord_permutation hp (List.mem_range.mp hv)) hr hs
  constructor
  · rintro ⟨reject, accept⟩
    exact ⟨fun run => by have := original.mpr run; simp_all,
      fun v hv => (deleted v hv).mp (accept v hv)⟩
  · rintro ⟨reject, accept⟩
    refine ⟨?_, fun v hv => (deleted v hv).mpr (accept v hv)⟩
    cases he : recognizes r s (encode 0 [] output) with
    | false => rfl
    | true => exact (reject (original.mp he)).elim

end LazyCode

#print axioms Run.cancel_fresh_singleton
#print axioms record_segment_iff
#print axioms record_batch_iff
#print axioms record_batch_height
#print axioms LazyCode.mem_pushOrders_iff
#print axioms LazyCode.mem_popOrders_iff
#print axioms LazyCode.mem_readOrders_iff
#print axioms LazyCode.record_transition_iff
#print axioms LazyCode.Decodes.codeOrders_iff_rangeLazy
#print axioms LazyCode.Decodes.codeOrders_iff_generated
#print axioms LazyCode.Decodes.recognizes_iff
#print axioms LazyCode.permutation_recognizes_iff
#print axioms LazyCode.oneDeletionCheck_iff
end StackSorting.Generalized
