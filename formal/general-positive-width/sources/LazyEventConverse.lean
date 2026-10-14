import GeneralizedCanonicalTrace

namespace StackSorting.Generalized
open List

/-- Input events carry consecutive ranks; every removal names an already read
rank. This imposes neither a canonical event word nor a physical history. -/
inductive RankedForward : Nat → List EndpointEvent → Prop where
  | nil (next : Nat) : RankedForward next []
  | push {next : Nat} {events : List EndpointEvent} :
      RankedForward (next + 1) events → RankedForward next (.push next :: events)
  | pop {next a : Nat} {events : List EndpointEvent} : a < next →
      RankedForward next events → RankedForward next (.pop a :: events)

/-- Only the literal adjacent push/pop pairs are constrained. -/
def EventLazyBoundary (events : List EndpointEvent) : Prop :=
  ∀ pre a b post, events = pre ++ .push a :: .pop b :: post → a = b

/-- Forward perfect matching will imply this elementary terminal condition. -/
def NoTrailingPush (events : List EndpointEvent) : Prop :=
  ∀ pre a, events ≠ pre ++ [.push a]

theorem EventLazyBoundary.tail {e : EndpointEvent} {events : List EndpointEvent}
    (h : EventLazyBoundary (e :: events)) : EventLazyBoundary events := by
  intro pre a b post he
  apply h (e :: pre) a b post
  simp [he]

theorem NoTrailingPush.tail {e : EndpointEvent} {events : List EndpointEvent}
    (h : NoTrailingPush (e :: events)) : NoTrailingPush events := by
  intro pre a he
  apply h (e :: pre) a
  simp [he]

/-- A nonempty initial insertion run must stop at an output at least as large
as its first label. The local lazy-boundary equation supplies this fact. -/
theorem RankedForward.first_output_after_push {next : Nat}
    {events : List EndpointEvent} (h : RankedForward next (.push next :: events))
    (hl : EventLazyBoundary (.push next :: events))
    (ht : NoTrailingPush (.push next :: events)) :
    ∃ a output, traceOutputs events = a :: output ∧ next ≤ a := by
  induction events generalizing next with
  | nil => exact False.elim (ht [] next rfl)
  | cons e events ih =>
    cases h with
    | push htail =>
      cases e with
      | pop a =>
        have he := hl [] next a events rfl
        exact ⟨a, traceOutputs events, by simp [traceOutputs, EndpointEvent.output], by omega⟩
      | push a =>
        have ha : a = next + 1 := by cases htail; rfl
        subst a
        obtain ⟨v, output, ho, hv⟩ := ih htail hl.tail ht.tail
        exact ⟨v, output, by simpa [traceOutputs, EndpointEvent.output] using ho, by omega⟩

/-- Reading one more input peels exactly one event from the deterministic
canonical record block, including its final single-insertion case. -/
theorem canonicalEvents_read_one {next a : Nat} (ha : next ≤ a)
    (output : List Nat) :
    canonicalEvents next (a :: output) =
      .push next :: canonicalEvents (next + 1) (a :: output) := by
  by_cases he : a = next
  · subst a
    simp [canonicalEvents]
  · have hbig : next + 1 ≤ a := by omega
    have hlen : a + 1 - next = (a + 1 - (next + 1)) + 1 := by omega
    simp [canonicalEvents, Nat.not_lt.mpr ha, Nat.not_lt.mpr hbig,
      hlen, List.range'_succ]

/-- The local axioms determine the complete canonical word, for all lengths.
No existence of a permutation, code, physical order, or canonical schedule is
assumed. Duplicate-freeness and complete matching belong to the separate
model-to-permutation bridge. -/
theorem RankedForward.eq_canonicalEvents {next : Nat} {events : List EndpointEvent}
    (h : RankedForward next events) (hl : EventLazyBoundary events)
    (ht : NoTrailingPush events) : events = canonicalEvents next (traceOutputs events) := by
  induction h with
  | nil => rfl
  | @pop next a events ha h ih =>
    simpa [traceOutputs, EndpointEvent.output, canonicalEvents, ha] using
      congrArg (EndpointEvent.pop a :: ·) (ih hl.tail ht.tail)
  | @push next events h ih =>
    obtain ⟨a, output, ho, ha⟩ := RankedForward.first_output_after_push
      (RankedForward.push h) hl ht
    have he := ih hl.tail ht.tail
    change .push next :: events = canonicalEvents next (traceOutputs events)
    rw [ho, canonicalEvents_read_one ha]
    rw [ho] at he
    exact congrArg (EndpointEvent.push next :: ·) he

/-- Two event schedules with the same outputs and the local lazy axioms are
literally equal, stronger than equality after taking a quotient. -/
theorem lazy_event_word_unique {next : Nat} {a b : List EndpointEvent}
    (ha : RankedForward next a) (hb : RankedForward next b)
    (hla : EventLazyBoundary a) (hlb : EventLazyBoundary b)
    (hta : NoTrailingPush a) (htb : NoTrailingPush b)
    (ho : traceOutputs a = traceOutputs b) : a = b := by
  rw [ha.eq_canonicalEvents hla hta, hb.eq_canonicalEvents hlb htb, ho]

#print axioms RankedForward.first_output_after_push
#print axioms canonicalEvents_read_one
#print axioms RankedForward.eq_canonicalEvents
#print axioms lazy_event_word_unique
end StackSorting.Generalized
