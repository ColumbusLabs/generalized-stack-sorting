import GeneralizedNonrecordDeletion

/-! Endpoint order and peeling transport for the actual event filter-map used
by nonrecord deletion. Deleted labels are excluded from every finite domain. -/
namespace StackSorting.Generalized
open List IntervalCritical

/-- A collision-free partial event relabelling preserves and reflects the order
of the first positions of any two surviving events. -/
theorem idxOf_filterMap_lt_iff (f : EndpointEvent → Option EndpointEvent)
    (hinj : ∀ a b c, f a = some c → f b = some c → a = b)
    {events : List EndpointEvent} {a b a' b' : EndpointEvent}
    (ha : a ∈ events) (hb : b ∈ events) (hfa : f a = some a') (hfb : f b = some b') :
    (events.filterMap f).idxOf a' < (events.filterMap f).idxOf b' ↔
      events.idxOf a < events.idxOf b := by
  induction events with
  | nil => simp at ha
  | cons x events ih =>
    by_cases hxa : x = a
    · subst x
      by_cases hab : a = b
      · subst b
        have he : a' = b' := Option.some.inj (hfa.symm.trans hfb)
        simp [he]
      · have hab' : a' ≠ b' := fun h => hab (hinj a b b' (h ▸ hfa) hfb)
        simp [hfa, List.idxOf_cons, hab, hab']
    · by_cases hxb : x = b
      · subst x
        have hba' : b' ≠ a' := fun h => hxa (hinj b a a' (h ▸ hfb) hfa)
        simp [hfb, List.idxOf_cons, hxa, hba']
      · have hat : a ∈ events := (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
        have hbt : b ∈ events := (List.mem_cons.mp hb).resolve_left (Ne.symm hxb)
        have ht := ih hat hbt
        cases hx : f x with
        | none => simpa [List.filterMap_cons, hx, List.idxOf_cons, hxa, hxb] using ht
        | some c =>
          have hca : c ≠ a' := fun h => hxa (hinj x a a' (h ▸ hx) hfa)
          have hcb : c ≠ b' := fun h => hxb (hinj x b b' (h ▸ hx) hfb)
          simpa [List.filterMap_cons, hx, List.idxOf_cons, hxa, hxb, hca, hcb] using ht

theorem deleteEvent_injective (v : Nat) (a b c : EndpointEvent)
    (ha : deleteEvent v a = some c) (hb : deleteEvent v b = some c) : a = b := by
  cases a <;> cases b <;> rename_i a b
  all_goals
    by_cases ha0 : a = v
    · simp [deleteEvent, ha0] at ha
    · by_cases hb0 : b = v
      · simp [deleteEvent, hb0] at hb
      · simp only [deleteEvent, ite_eq_right ha0, ite_eq_right hb0] at ha hb
        have he := (Option.some.inj ha).trans (Option.some.inj hb).symm
        simp only [EndpointEvent.push.injEq, EndpointEvent.pop.injEq, reduceCtorEq] at he
        all_goals
          have hab := deleteRank_injective_surviving ha0 hb0 he
          exact congrArg _ hab

/-- Exact left/right incidence after event deletion. All three endpoint owners
are survivors; the erased owner's endpoints are intentionally outside scope. -/
theorem deleteEvents_covers_endpoints {v u w : Nat} {events : List EndpointEvent}
    (hu : u ≠ v) (hw : w ≠ v)
    (hup : EndpointEvent.push u ∈ events) (huq : EndpointEvent.pop u ∈ events)
    (hwp : EndpointEvent.push w ∈ events) (hwq : EndpointEvent.pop w ∈ events) :
    (Covers (extractedEndpoints (deleteEvents v events)) (deleteRank v u)
        ((extractedEndpoints (deleteEvents v events)).left (deleteRank v w)) ↔
      Covers (extractedEndpoints events) u ((extractedEndpoints events).left w)) ∧
    (Covers (extractedEndpoints (deleteEvents v events)) (deleteRank v u)
        ((extractedEndpoints (deleteEvents v events)).right (deleteRank v w)) ↔
      Covers (extractedEndpoints events) u ((extractedEndpoints events).right w)) := by
  have hpu : deleteEvent v (.push u) = some (.push (deleteRank v u)) := by simp [deleteEvent, hu]
  have hqu : deleteEvent v (.pop u) = some (.pop (deleteRank v u)) := by simp [deleteEvent, hu]
  have hpw : deleteEvent v (.push w) = some (.push (deleteRank v w)) := by simp [deleteEvent, hw]
  have hqw : deleteEvent v (.pop w) = some (.pop (deleteRank v w)) := by simp [deleteEvent, hw]
  have hll := idxOf_filterMap_lt_iff (deleteEvent v) (deleteEvent_injective v) hup hwp hpu hpw
  have hlr := idxOf_filterMap_lt_iff (deleteEvent v) (deleteEvent_injective v) hwp huq hpw hqu
  have hrl := idxOf_filterMap_lt_iff (deleteEvent v) (deleteEvent_injective v) hup hwq hpu hqw
  have hrr := idxOf_filterMap_lt_iff (deleteEvent v) (deleteEvent_injective v) hwq huq hqw hqu
  exact ⟨and_congr hll hlr, and_congr hrl hrr⟩

/-- Count transport retains exactly the supplied finite surviving-token domain. -/
theorem deleteEvents_endpoint_counts {v w : Nat} {events : List EndpointEvent} {U : Tokens}
    (hU : ∀ u ∈ U, u ≠ v ∧ EndpointEvent.push u ∈ events ∧ EndpointEvent.pop u ∈ events)
    (hw : w ≠ v) (hwp : EndpointEvent.push w ∈ events) (hwq : EndpointEvent.pop w ∈ events) :
    endpointCount (extractedEndpoints (deleteEvents v events)) (U.map (deleteRank v))
        ((extractedEndpoints (deleteEvents v events)).left (deleteRank v w)) =
      endpointCount (extractedEndpoints events) U ((extractedEndpoints events).left w) ∧
    endpointCount (extractedEndpoints (deleteEvents v events)) (U.map (deleteRank v))
        ((extractedEndpoints (deleteEvents v events)).right (deleteRank v w)) =
      endpointCount (extractedEndpoints events) U ((extractedEndpoints events).right w) := by
  constructor <;> unfold endpointCount <;> rw [List.countP_map] <;> apply List.countP_congr
  · intro u hu
    obtain ⟨hneq, hp, hq⟩ := hU u hu
    simpa only [Function.comp_apply, decide_eq_true_eq] using (deleteEvents_covers_endpoints hneq hw hp hq hwp hwq).1
  · intro u hu
    obtain ⟨hneq, hp, hq⟩ := hU u hu
    simpa only [Function.comp_apply, decide_eq_true_eq] using (deleteEvents_covers_endpoints hneq hw hp hq hwp hwq).2

theorem deleteRank_map_erase {v w : Nat} {U : Tokens}
    (hU : ∀ u ∈ U, u ≠ v) (hw : w ≠ v) :
    (U.map (deleteRank v)).erase (deleteRank v w) = (U.erase w).map (deleteRank v) := by
  induction U with
  | nil => rfl
  | cons a U ih =>
    have ha := hU a (by simp)
    have ht : ∀ u ∈ U, u ≠ v := fun u hu => hU u (by simp [hu])
    by_cases he : a = w
    · subst a; simp
    · have he' : deleteRank v a ≠ deleteRank v w :=
        fun h => he (deleteRank_injective_surviving ha hw h)
      simp [he, he', ih ht]

/-- Full peeling transport through the actual deletion filter-map. The domain
contains only surviving tokens whose push and pop events actually occur. -/
theorem peelable_deleteEvents_map_iff {v r s : Nat} {events : List EndpointEvent} {U : Tokens}
    (hU : ∀ u ∈ U, u ≠ v ∧ EndpointEvent.push u ∈ events ∧ EndpointEvent.pop u ∈ events) :
    Peelable (extractedEndpoints (deleteEvents v events)) r s (U.map (deleteRank v)) ↔
      Peelable (extractedEndpoints events) r s U := by
  constructor
  · intro h
    generalize heq : U.map (deleteRank v) = W at h
    induction h generalizing U with
    | nil =>
      have hn : U = [] := List.map_eq_nil_iff.mp heq
      subst U
      exact .nil
    | @step W x hx hel rest ih =>
      have hxm : x ∈ U.map (deleteRank v) := heq ▸ hx
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hxm
      subst x
      obtain ⟨hwv, hwp, hwq⟩ := hU w hw
      obtain ⟨hl, hr⟩ := deleteEvents_endpoint_counts hU hwv hwp hwq
      have he : Eligible (extractedEndpoints events) r s U w := by
        rw [← heq] at hel
        exact ⟨by simpa only [hl] using hel.1, by simpa only [hr] using hel.2⟩
      have ht : ∀ u ∈ U.erase w, u ≠ v ∧ EndpointEvent.push u ∈ events ∧ EndpointEvent.pop u ∈ events :=
        fun u hu => hU u (List.mem_of_mem_erase hu)
      have hmap : (U.erase w).map (deleteRank v) = W.erase (deleteRank v w) := by
        rw [← heq, deleteRank_map_erase (fun u hu => (hU u hu).1) hwv]
      exact .step w hw he (ih ht hmap)
  · intro h
    induction h with
    | nil => exact .nil
    | @step U w hw hel rest ih =>
      obtain ⟨hwv, hwp, hwq⟩ := hU w hw
      obtain ⟨hl, hr⟩ := deleteEvents_endpoint_counts hU hwv hwp hwq
      have he : Eligible (extractedEndpoints (deleteEvents v events)) r s (U.map (deleteRank v)) (deleteRank v w) :=
        ⟨by simpa only [hl] using hel.1, by simpa only [hr] using hel.2⟩
      have ht : ∀ u ∈ U.erase w, u ≠ v ∧ EndpointEvent.push u ∈ events ∧ EndpointEvent.pop u ∈ events :=
        fun u hu => hU u (List.mem_of_mem_erase hu)
      have hrest := ih ht
      rw [← deleteRank_map_erase (fun u hu => (hU u hu).1) hwv] at hrest
      exact .step (deleteRank v w) (List.mem_map.mpr ⟨w, hw, rfl⟩) he hrest

#print axioms idxOf_filterMap_lt_iff
#print axioms deleteEvent_injective
#print axioms deleteEvents_covers_endpoints
#print axioms deleteEvents_endpoint_counts
#print axioms peelable_deleteEvents_map_iff
end StackSorting.Generalized
