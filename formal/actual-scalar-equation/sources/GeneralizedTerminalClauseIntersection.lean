import GeneralizedTerminalFaceBounds
import GeneralizedRankCompletion

/-! Actual simultaneous-feasibility theorem for terminal clauses after an
arbitrary ordinary Z/B/T prefix. Every semantic bridge is proved from literal
Completion; no intersection-of-existentials claim is an assumption. -/
namespace StackSorting.Generalized.Decorated
open Coordinates InitialSchedule StackSorting.MonotoneElimination

def terminalEligibility (P : State) (m : Nat) (output : List Nat) : Eligibility :=
  fun U v => BoundEligible (terminalBaseBounds P m) U v ∧
    ScheduleEligible 3 3 U v (List.range' 1 (P.length+m))
      (canonicalEvents (P.length+m+1) output)

def terminalSchedule (P : State) (m n : Nat) (output : List Nat) : Prop :=
  traceInputs (canonicalEvents (P.length+m+1) output) = List.range' (P.length+m+1) n ∧
  traceOutputs (canonicalEvents (P.length+m+1) output) = output ∧
  InitialSchedule.Valid (List.range' 1 (P.length+m))
    (canonicalEvents (P.length+m+1) output)

theorem terminalEligible_eq (P : State) (m : Nat) (J : List Nat) (output : List Nat) :
    (fun U v => BoundEligible (terminalFaceBounds P m J) U v ∧
      ScheduleEligible 3 3 U v (List.range' 1 (P.length+m))
        (canonicalEvents (P.length+m+1) output)) =
      WithZeros (terminalEligibility P m output) (selectedLabels P J) := by
  funext U v
  apply propext
  rw [boundEligible_terminalFace]
  simp only [WithZeros, terminalEligibility]
  exact ⟨fun ⟨⟨hb,hz⟩,hf⟩ => ⟨⟨hb,hf⟩,hz⟩,
    fun ⟨⟨hb,hf⟩,hz⟩ => ⟨⟨hb,hz⟩,hf⟩⟩

theorem completion_terminal_face_iff {P : State} (hu : Unary P)
    (m n : Nat) (J : List Nat) (hsub : J ⊆ List.range m) (output : List Nat) :
    Completion (P ++ zeroFace m J) n output ↔
      terminalSchedule P m n output ∧
      ∃ order, order.Perm (List.range' 1 (P.length+m+n)) ∧
        FeasibleOrder (WithZeros (terminalEligibility P m output) (selectedLabels P J)) order := by
  have hh : height (P ++ zeroFace m J) = P.length+m := by
    rw [height_append, unary_height hu, height_zeroFace]
  have hlabels : ∀ label bound, (label,bound) ∈ terminalFaceBounds P m J →
      label ∈ List.range' 1 (height (P ++ zeroFace m J)) := by
    rw [hh]
    exact terminalFaceBounds_labels P m J hsub
  have hrep : ∀ physical, physical.Perm (List.range' 1 (height (P ++ zeroFace m J))) →
      (Represents (P ++ zeroFace m J) physical ↔ RankBounds (terminalFaceBounds P m J) physical) := by
    intro physical hp
    rw [hh] at hp
    rw [represents_terminal_face_iff hu m J hsub physical]
    exact ⟨And.right, fun h => ⟨hp,h⟩⟩
  have ht := completion_iff_rank_order (P ++ zeroFace m J) n output
    (terminalFaceBounds P m J) hlabels hrep
  rw [hh, terminalEligible_eq] at ht
  simpa only [terminalSchedule, and_assoc] using ht

theorem withZeros_monotone {base : Eligibility} (hm : Monotone base) (selected : List Nat) :
    Monotone (WithZeros base selected) := by
  intro U V v hn hsub h
  refine ⟨hm hn hsub h.1, ?_⟩
  intro i hi he
  have hz := h.2 i hi he
  have hl := smallerCount_mono hn hsub (v := v)
  omega

theorem withZeros_self {base : Eligibility} (hs : SelfIndependent base) (selected : List Nat) :
    SelfIndependent (WithZeros base selected) := by
  intro U v hn hv
  simp only [WithZeros, ZeroRestriction, smallerCount_erase_self hn, hs hn hv]

theorem terminalEligibility_monotone (P : State) (m : Nat) (output : List Nat) :
    Monotone (terminalEligibility P m output) := by
  intro U V v hn hsub h
  exact ⟨boundEligible_monotone _ hn hsub h.1, h.2.subset hn hsub⟩

theorem terminalEligibility_self (P : State) (m : Nat) (output : List Nat) :
    SelfIndependent (terminalEligibility P m output) := by
  intro U v hn hv
  simp only [terminalEligibility, boundEligible_self _ hn hv,
    ScheduleEligible.erase_self 3 3 _ U v _ hv]

/-- The central actual-language intersection. It holds even without m≥2,
provided the selected coordinates form a nonempty sublist of the block range.
The prefix is genuinely unary Z/B/T; arbitrary additional clauses are not
silently included in the statement. -/
theorem completion_terminal_faces_intersection {P : State} (hu : Unary P)
    (m n : Nat) (J : List Nat) (hne : J ≠ []) (hsub : J ⊆ List.range m)
    (output : List Nat) :
    (∀ j ∈ J, Completion (P ++ zeroFace m [j]) n output) ↔
      Completion (P ++ zeroFace m J) n output := by
  let E := terminalEligibility P m output
  let U := List.range' 1 (P.length+m+n)
  let selected := selectedLabels P J
  have hm : Monotone E := terminalEligibility_monotone P m output
  have hs : SelfIndependent E := terminalEligibility_self P m output
  have huN : U.Nodup := List.nodup_range'
  have hselected : selected ≠ [] := by simpa [selected, selectedLabels] using hne
  have hsingleSub (j : Nat) (hj : j ∈ J) : [j] ⊆ List.range m := by
    intro k hk
    have he : k = j := by simpa using hk
    subst k
    exact hsub hj
  constructor
  · intro hall
    obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil J hne
    have hcommon := ((completion_terminal_face_iff hu m n [j] (hsingleSub j hj) output).mp
      (hall j hj)).1
    have hsingle : ∀ i ∈ selected, EverySubset (WithZeros E [i]) U := by
      intro i hi
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
      obtain ⟨_, order, hp, hf⟩ :=
        (completion_terminal_face_iff hu m n [k] (hsingleSub k hk) output).mp (hall k hk)
      have hf' : FeasibleOrder (WithZeros E [P.length+1+k]) order := by
        simpa [selectedLabels, E] using hf
      exact (feasibleOrder_iff_everySubset (E := WithZeros E [P.length+1+k])
        (withZeros_monotone (base := E) hm _) (withZeros_self (base := E) hs _) huN).mp ⟨order,hp,hf'⟩
    have hbound : ∀ V, V.Nodup → V ⊆ U →
        ∀ v ∈ selected, E V v → smallerCount V v ≤ 1 := by
      intro V _ _ v hv hb
      exact terminal_base_selected_bound P m J hsub V v hv hb.1
    have hjoint := everySubset_withZeros E U selected hselected hbound hsingle
    obtain ⟨order,hp,hf⟩ :=
      (feasibleOrder_iff_everySubset (E := WithZeros E selected)
        (withZeros_monotone (base := E) hm _) (withZeros_self (base := E) hs _) huN).mpr hjoint
    exact (completion_terminal_face_iff hu m n J hsub output).mpr ⟨hcommon,order,hp,hf⟩
  · intro h j hj
    obtain ⟨hcommon,order,hp,hf⟩ :=
      (completion_terminal_face_iff hu m n J hsub output).mp h
    apply (completion_terminal_face_iff hu m n [j] (hsingleSub j hj) output).mpr
    refine ⟨hcommon,order,hp,?_⟩
    apply (feasibleOrder_iff_prefixes _ order).mpr
    intro above v below he
    obtain ⟨hb,hz⟩ := (feasibleOrder_iff_prefixes _ order).mp hf above v below he
    refine ⟨hb,?_⟩
    intro i hi
    have hie : i = P.length+1+j := by simpa [selectedLabels] using hi
    subst i
    exact hz _ (List.mem_map.mpr ⟨j,hj,rfl⟩)

#print axioms completion_terminal_face_iff
#print axioms completion_terminal_faces_intersection
end StackSorting.Generalized.Decorated
