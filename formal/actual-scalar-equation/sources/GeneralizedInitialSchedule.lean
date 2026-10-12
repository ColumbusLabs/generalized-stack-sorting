import GeneralizedCanonicalTrace

/-! Static total-order constraints for a fixed event schedule with an arbitrary
initial physical stack. Active pools are updated from event labels alone;
feasibility contains only finite prefix counts, never a physical Run premise. -/
namespace StackSorting.Generalized
namespace InitialSchedule
open List

def owner : EndpointEvent → Nat
  | .push v => v
  | .pop v => v

def width (r s : Nat) : EndpointEvent → Nat
  | .push _ => r
  | .pop _ => s

def advance (pool : List Nat) : EndpointEvent → List Nat
  | .push v => v :: pool
  | .pop v => pool.erase v

def EventValid (pool : List Nat) : EndpointEvent → Prop
  | .push v => v ∉ pool
  | .pop v => v ∈ pool

def Valid : List Nat → List EndpointEvent → Prop
  | pool, [] => pool = []
  | pool, event :: events => EventValid pool event ∧ Valid (advance pool event) events

def project (order pool : List Nat) : List Nat :=
  order.filter (fun v => decide (v ∈ pool))

/-- An owner's own occurrence is deliberately excluded. This makes the
eligibility predicate self-insensitive, including at a pop event. -/
def count (pool above : List Nat) (v : Nat) : Nat :=
  (above.filter (fun u => decide (u ∈ pool ∧ u ≠ v))).length

def ScheduleEligible (r s : Nat) (above : List Nat) (v : Nat) :
    List Nat → List EndpointEvent → Prop
  | _, [] => True
  | pool, event :: events =>
      (owner event = v → count pool above v < width r s event) ∧
      ScheduleEligible r s above v (advance pool event) events

def Feasible (r s : Nat) (order pool : List Nat) (events : List EndpointEvent) : Prop :=
  ∀ above v below, order = above ++ v :: below →
    ScheduleEligible r s above v pool events

theorem count_perm {pool U V : List Nat} {v : Nat} (hp : U.Perm V) :
    count pool U v = count pool V v := (hp.filter _).length_eq

theorem count_subset {pool U V : List Nat} {v : Nat}
    (hn : U.Nodup) (hs : U ⊆ V) : count pool U v ≤ count pool V v := by
  apply List.Nodup.length_le_of_subset (hn.filter _)
  intro u hu
  obtain ⟨hu, hp⟩ := List.mem_filter.mp hu
  exact List.mem_filter.mpr ⟨hs hu, hp⟩

theorem count_snoc_self (pool U : List Nat) (v : Nat) :
    count pool (U ++ [v]) v = count pool U v := by simp [count]

theorem ScheduleEligible.perm {r s v : Nat} {pool U V : List Nat}
    {events : List EndpointEvent} (h : ScheduleEligible r s U v pool events)
    (hp : U.Perm V) : ScheduleEligible r s V v pool events := by
  induction events generalizing pool with
  | nil => trivial
  | cons event events ih =>
    exact ⟨fun he => by simpa only [count_perm hp] using h.1 he, ih h.2⟩

theorem ScheduleEligible.subset {r s v : Nat} {pool U V : List Nat}
    {events : List EndpointEvent} (h : ScheduleEligible r s V v pool events)
    (hn : U.Nodup) (hs : U ⊆ V) : ScheduleEligible r s U v pool events := by
  induction events generalizing pool with
  | nil => trivial
  | cons event events ih =>
    exact ⟨fun he => Nat.lt_of_le_of_lt (count_subset hn hs) (h.1 he), ih h.2⟩

theorem ScheduleEligible.snoc_self (r s : Nat) (pool U : List Nat) (v : Nat)
    (events : List EndpointEvent) :
    ScheduleEligible r s (U ++ [v]) v pool events ↔
      ScheduleEligible r s U v pool events := by
  induction events generalizing pool with
  | nil => rfl
  | cons event events ih => simp [ScheduleEligible, count_snoc_self, ih]

theorem ScheduleEligible.erase_self (r s : Nat) (pool U : List Nat) (v : Nat)
    (events : List EndpointEvent) (hv : v ∈ U) :
    ScheduleEligible r s U v pool events ↔
      ScheduleEligible r s (U.erase v) v pool events := by
  have hp : U.Perm (U.erase v ++ [v]) :=
    (List.perm_cons_erase hv).trans (by simpa using
      (List.perm_middle (a := v) (l₁ := U.erase v) (l₂ := [])).symm)
  constructor
  · intro h
    exact (ScheduleEligible.snoc_self r s pool (U.erase v) v events).mp (h.perm hp)
  · intro h
    exact ((ScheduleEligible.snoc_self r s pool (U.erase v) v events).mpr h).perm hp.symm

theorem advance_perm {pool pool' : List Nat} (hp : pool.Perm pool')
    (event : EndpointEvent) : (advance pool event).Perm (advance pool' event) := by
  cases event with
  | push v => exact List.Perm.cons v hp
  | pop v => exact hp.erase v

theorem count_pool_perm {pool pool' : List Nat} (hp : pool.Perm pool')
    (above : List Nat) (v : Nat) : count pool above v = count pool' above v := by
  unfold count
  congr 1
  apply List.filter_congr
  intro u _
  simp only [hp.mem_iff]

theorem ScheduleEligible.pool_perm {r s v : Nat} {pool pool' above : List Nat}
    {events : List EndpointEvent} (h : ScheduleEligible r s above v pool events)
    (hp : pool.Perm pool') : ScheduleEligible r s above v pool' events := by
  induction events generalizing pool pool' with
  | nil => trivial
  | cons event events ih =>
    exact ⟨fun he => by simpa only [count_pool_perm hp] using h.1 he,
      ih h.2 (advance_perm hp event)⟩

theorem Valid.perm {pool pool' : List Nat} {events : List EndpointEvent}
    (h : Valid pool events) (hp : pool.Perm pool') : Valid pool' events := by
  induction events generalizing pool pool' with
  | nil =>
    change pool = [] at h
    rw [h] at hp
    exact List.perm_nil.mp hp.symm
  | cons event events ih =>
    refine ⟨?_, ih h.2 (advance_perm hp event)⟩
    cases event <;> simpa only [EventValid, hp.mem_iff] using h.1

theorem Feasible.pool_perm {r s : Nat} {order pool pool' : List Nat}
    {events : List EndpointEvent} (h : Feasible r s order pool events)
    (hp : pool.Perm pool') : Feasible r s order pool' events :=
  fun above v below he => (h above v below he).pool_perm hp

theorem project_pool_perm {order pool pool' : List Nat} (hp : pool.Perm pool') :
    project order pool = project order pool' := by
  apply List.filter_congr
  intro v _
  simp only [hp.mem_iff]

theorem feasible_cons_iff (r s : Nat) (order pool : List Nat)
    (event : EndpointEvent) (events : List EndpointEvent) :
    Feasible r s order pool (event :: events) ↔
      (∀ above below, order = above ++ owner event :: below →
        count pool above (owner event) < width r s event) ∧
      Feasible r s order (advance pool event) events := by
  constructor
  · intro h
    exact ⟨fun above below he => (h above (owner event) below he).1 rfl,
      fun above v below he => (h above v below he).2⟩
  · rintro ⟨hh, ht⟩ above v below he
    exact ⟨fun hv => by subst v; exact hh above below he, ht above v below he⟩

theorem split_not_mem {order above below : List Nat} {v : Nat}
    (hn : order.Nodup) (he : order = above ++ v :: below) :
    v ∉ above ∧ v ∉ below := by
  rw [he] at hn
  have hp := List.nodup_append.mp hn
  exact ⟨fun hv => hp.2.2 v hv v (by simp) rfl, (List.nodup_cons.mp hp.2.1).1⟩

theorem project_cons_of_not_mem {W pool : List Nat} {v : Nat} (hn : v ∉ W) :
    project W (v :: pool) = project W pool := by
  apply List.filter_congr
  intro u hu
  have hne : u ≠ v := fun he => hn (he ▸ hu)
  simp [hne]

theorem project_erase_of_not_mem {W pool : List Nat} {v : Nat} (hn : v ∉ W) :
    project W (pool.erase v) = project W pool := by
  apply List.filter_congr
  intro u hu
  have hne : u ≠ v := fun he => hn (he ▸ hu)
  simp [List.mem_erase_of_ne hne]

theorem count_eq_project {pool W : List Nat} {v : Nat} (hn : v ∉ W) :
    count pool W v = (project W pool).length := by
  unfold count project
  congr 1
  apply List.filter_congr
  intro u hu
  have hne : u ≠ v := fun he => hn (he ▸ hu)
  simp [hne]

theorem project_push_split {order above below pool : List Nat} {v : Nat}
    (hn : order.Nodup) (he : order = above ++ v :: below) (hv : v ∉ pool) :
    project order pool = project above pool ++ project below pool ∧
      project order (v :: pool) = project above pool ++ v :: project below pool := by
  obtain ⟨ha, hb⟩ := split_not_mem hn he
  constructor
  · simp [project, he, hv]
  · calc
      project order (v :: pool) =
          project above (v :: pool) ++ v :: project below (v :: pool) := by
        simp [project, he]
      _ = _ := by rw [project_cons_of_not_mem ha, project_cons_of_not_mem hb]

theorem project_pop_split {order above below pool : List Nat} {v : Nat}
    (hn : order.Nodup) (hp : pool.Nodup)
    (he : order = above ++ v :: below) (hv : v ∈ pool) :
    project order pool = project above pool ++ v :: project below pool ∧
      project order (pool.erase v) = project above pool ++ project below pool := by
  obtain ⟨ha, hb⟩ := split_not_mem hn he
  constructor
  · simp [project, he, hv]
  · have hnot : v ∉ pool.erase v := List.Nodup.not_mem_erase hp
    calc
      project order (pool.erase v) =
          project above (pool.erase v) ++ project below (pool.erase v) := by
        simp [project, he, hnot]
      _ = _ := by rw [project_erase_of_not_mem ha, project_erase_of_not_mem hb]

/-- One static rank inequality is exactly one step of the established literal
machine on the global order's active membership filters. -/
theorem step_iff_bounds {r s : Nat} {order pool : List Nat} {event : EndpointEvent}
    (hn : order.Nodup) (hp : pool.Nodup) (hm : owner event ∈ order)
    (hv : EventValid pool event) :
    Step r s (project order pool) event.input event.output
      (project order (advance pool event)) ↔
      ∀ above below, order = above ++ owner event :: below →
        count pool above (owner event) < width r s event := by
  cases event with
  | push v =>
    simp only [owner, width, advance, EventValid, EndpointEvent.input, EndpointEvent.output] at *
    constructor
    · intro hs above below he
      obtain ⟨_, ha⟩ := project_push_split hn he hv
      have hb := hs.push_rank_bound (hn.filter _)
      rw [ha] at hb
      have hnd : (project above pool ++ v :: project below pool).Nodup := by
        rw [← ha]; exact hn.filter _
      rw [idxOf_split_of_nodup hnd] at hb
      simpa only [owner, width, count_eq_project (split_not_mem hn he).1] using hb
    · intro hb
      obtain ⟨above, below, he⟩ := List.mem_iff_append.mp hm
      obtain ⟨hbefore, hafter⟩ := project_push_split hn he hv
      have hbound := hb above below he
      rw [count_eq_project (split_not_mem hn he).1] at hbound
      simpa only [advance, EndpointEvent.input, EndpointEvent.output, hbefore, hafter] using
        (Step.push (s := s) (project above pool) (project below pool) v hbound)
  | pop v =>
    simp only [owner, width, advance, EventValid, EndpointEvent.input, EndpointEvent.output] at *
    constructor
    · intro hs above below he
      obtain ⟨hbefore, _⟩ := project_pop_split hn hp he hv
      have hb := hs.pop_rank_bound (hn.filter _)
      rw [hbefore] at hb
      have hnd : (project above pool ++ v :: project below pool).Nodup := by
        rw [← hbefore]; exact hn.filter _
      rw [idxOf_split_of_nodup hnd] at hb
      simpa only [owner, width, count_eq_project (split_not_mem hn he).1] using hb
    · intro hb
      obtain ⟨above, below, he⟩ := List.mem_iff_append.mp hm
      obtain ⟨hbefore, hafter⟩ := project_pop_split hn hp he hv
      have hbound := hb above below he
      rw [count_eq_project (split_not_mem hn he).1] at hbound
      simpa only [advance, EndpointEvent.input, EndpointEvent.output, hbefore, hafter] using
        (Step.pop (r := r) (project above pool) (project below pool) v hbound)

theorem advance_nodup {pool : List Nat} {event : EndpointEvent}
    (hn : pool.Nodup) (hv : EventValid pool event) : (advance pool event).Nodup := by
  cases event with
  | push v => exact List.nodup_cons.mpr ⟨hv, hn⟩
  | pop v => exact hn.erase v

theorem advance_subset {pool order : List Nat} {event : EndpointEvent}
    (hp : pool ⊆ order) (hv : owner event ∈ order) : advance pool event ⊆ order := by
  cases event with
  | push v =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hv
    · exact hp hu
  | pop v => exact fun _ hu => hp (List.mem_of_mem_erase hu)

/-- Replay of the fixed labeled schedule from arbitrary initially active labels.
The only semantic assumptions are the explicit static bounds and label validity. -/
theorem feasible_history {r s : Nat} {order pool : List Nat} {events : List EndpointEvent}
    (hn : order.Nodup) (hp : pool.Nodup) (hsub : pool ⊆ order)
    (hin : traceInputs events ⊆ order) (hv : Valid pool events)
    (hf : Feasible r s order pool events) :
    Run r s (project order pool) (traceInputs events) (traceOutputs events) [] := by
  induction events generalizing pool with
  | nil =>
    have he : pool = [] := hv
    have hz : project order pool = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro v _
      simp [he]
    simpa [hz, traceInputs, traceOutputs] using Run.nil ([] : List Nat)
  | cons event events ih =>
    have hm : owner event ∈ order := by
      cases event with
      | push v => exact hin (by simp [traceInputs, EndpointEvent.input, owner])
      | pop v => exact hsub hv.1
    have hit : traceInputs events ⊆ order := by
      intro u hu
      exact hin (by simp only [traceInputs, List.flatMap_cons]; exact List.mem_append_right _ hu)
    obtain ⟨hbound, htail⟩ := (feasible_cons_iff r s order pool event events).mp hf
    have hs := (step_iff_bounds hn hp hm hv.1).mpr hbound
    have ht := ih (advance_nodup hp hv.1) (advance_subset hsub hm) hit hv.2 htail
    simpa only [traceInputs, traceOutputs, List.flatMap_cons] using Run.cons hs ht

/-- A physical step induces the same unordered active-pool update. -/
theorem step_pool_advance {r s : Nat} {pool held after : List Nat} {event : EndpointEvent}
    (hs : Step r s held event.input event.output after) (hp : pool.Perm held) :
    (advance pool event).Perm after := by
  cases event with
  | push v =>
    have hh : (held ++ [v]).Perm after := by simpa [EndpointEvent.input, EndpointEvent.output] using hs.supply
    have hm : (v :: held).Perm (held ++ [v]) := by
      simpa using (List.perm_middle (a := v) (l₁ := held) (l₂ := [])).symm
    exact (List.Perm.cons v hp).trans (hm.trans hh)
  | pop v =>
    have hh : held.Perm (v :: after) := by simpa [EndpointEvent.input, EndpointEvent.output] using hs.supply
    simpa [advance] using (hp.trans hh).erase v

/-- Extract label validity and all static prefix inequalities from the exact
physical history and its independently constructed common global order. -/
theorem exactTrace_feasible {r s : Nat} {ops : List RawOp}
    {held output order pool : List Nat} {events : List EndpointEvent}
    (ht : ExactTrace r s ops held events [] output) (hn : order.Nodup)
    (hfit : OrderFits order r s ops held) (hp : pool.Perm held) :
    Valid pool events ∧ Feasible r s order pool events := by
  induction ops generalizing held output events pool with
  | nil =>
    cases ht
    have he : pool = [] := List.perm_nil.mp hp
    exact ⟨he, by intro above v below hs; trivial⟩
  | cons op ops ih =>
    cases ht with
    | @cons _ _ _ middle _ _ event events hs hi ht =>
      obtain ⟨middle', emitted, hs', hf⟩ := hfit.2
      have heq : middle' = middle ∧ emitted = event.output := by
        simpa only [Option.some.injEq, Prod.mk.injEq] using hs'.symm.trans hs
      rcases heq with ⟨heq₁, heq₂⟩
      subst middle'
      subst emitted
      have hrel : Step r s held event.input event.output middle := by
        simpa only [hi] using step_relational r s op held middle event.output hs
      have hpool := step_pool_advance hrel hp
      have hmidN := hf.initial.nodup hn
      have hheldN := hfit.initial.nodup hn
      have hvalid : EventValid pool event := by
        cases event with
        | push v =>
          have hv : v ∉ held := by
            cases hrel with
            | push pre post v allowed =>
              have hn' := List.nodup_append.mp hmidN
              have ha : v ∉ pre := fun hv => hn'.2.2 v hv v (by simp) rfl
              have hb := (List.nodup_cons.mp hn'.2.1).1
              simp [ha, hb]
          exact fun h => hv (hp.mem_iff.mp h)
        | pop v =>
          have hv : v ∈ held := by
            cases hrel with
            | pop pre post v allowed => simp
          exact hp.mem_iff.mpr hv
      have hm : owner event ∈ order := by
        cases event with
        | push v =>
          have hv : v ∈ middle := by cases hrel with | push pre post v allowed => simp
          exact hf.initial.subset hv
        | pop v => exact hfit.initial.subset (hp.mem_iff.mp hvalid)
      have hb : held = project order pool := by
        apply sublist_eq_filter hn hfit.initial
        intro v _
        simpa using hp.mem_iff
      have ha : middle = project order (advance pool event) := by
        apply sublist_eq_filter hn hf.initial
        intro v _
        simpa using hpool.mem_iff
      have hbound := (step_iff_bounds hn (hp.nodup_iff.mpr hheldN) hm hvalid).mp
        (by simpa only [← hb, ← ha] using hrel)
      obtain ⟨hv, hfeas⟩ := ih ht hf hpool
      exact ⟨⟨hvalid, hv⟩, (feasible_cons_iff r s order pool event events).mpr ⟨hbound, hfeas⟩⟩
/-- Arbitrary-initial increasing-input lazy normalization, retaining the exact
initial stack and the deterministic future token-event schedule. -/
theorem run_iff_canonical_trace {r s next n : Nat} {held output : List Nat}
    (hn : (held ++ List.range' next n).Nodup)
    (hb : ∀ v ∈ held, v < next) :
    Run r s held (List.range' next n) output [] ↔
      ∃ ops, ExactTrace r s ops held (canonicalEvents next output) [] output ∧
        Generalized.inputs ops = List.range' next n := by
  constructor
  · intro h
    obtain ⟨ops, ht, hi⟩ := (h.rangeLazy hn).exactTrace hb
    exact ⟨ops, ht, by simpa using hi⟩
  · rintro ⟨ops, ht, hi⟩
    simpa [hi] using run_relational r s ops held [] output ht.run

/-- Literal complete histories are equivalent to one static total order that
preserves the arbitrary initial physical stack and satisfies all future
canonical insertion/removal top-width inequalities. -/
theorem run_iff_canonical_order {r s next n : Nat} {held output : List Nat}
    (hn : (held ++ List.range' next n).Nodup)
    (hb : ∀ v ∈ held, v < next) :
    Run r s held (List.range' next n) output [] ↔
      traceInputs (canonicalEvents next output) = List.range' next n ∧
      traceOutputs (canonicalEvents next output) = output ∧
      Valid held (canonicalEvents next output) ∧
      ∃ order, order.Perm (held ++ List.range' next n) ∧
        project order held = held ∧ Feasible r s order held (canonicalEvents next output) := by
  constructor
  · intro h
    obtain ⟨ops, ht, hi⟩ := (run_iff_canonical_trace hn hb).mp h
    obtain ⟨order, ho, hp, hf⟩ := run_has_distinct_global_order ht.run (by simpa [hi] using hn)
    obtain ⟨hv, hfeas⟩ := exactTrace_feasible ht ho hf (List.Perm.refl held)
    refine ⟨ht.inputs.trans hi, ht.outputs, hv, order, by simpa [hi] using hp, ?_, hfeas⟩
    symm
    apply sublist_eq_filter ho hf.initial
    intro v _
    simp
  · rintro ⟨hi, ho, hv, order, hp, hinit, hf⟩
    have hnd := hp.nodup_iff.mpr hn
    have hheld := (List.nodup_append.mp hn).1
    have hsub : held ⊆ order := fun v hv => hp.mem_iff.mpr (List.mem_append_left _ hv)
    have hinput : traceInputs (canonicalEvents next output) ⊆ order := by
      intro v hv
      rw [hi] at hv
      exact hp.mem_iff.mpr (List.mem_append_right _ hv)
    simpa [hi, ho, hinit] using feasible_history hnd hheld hsub hinput hv hf

#print axioms ScheduleEligible.perm
#print axioms ScheduleEligible.subset
#print axioms ScheduleEligible.snoc_self
#print axioms feasible_history
#print axioms exactTrace_feasible
#print axioms run_iff_canonical_order
end InitialSchedule
end StackSorting.Generalized
