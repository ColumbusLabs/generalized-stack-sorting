import SparseCanonicalUniqueness

namespace StackSorting.Generalized
open List

theorem EventLazyBoundary.nil : EventLazyBoundary [] := by
  intro pre a b post he
  have hh := congrArg List.length he
  simp at hh

theorem EventLazyBoundary.pop {events : List EndpointEvent}
    (h : EventLazyBoundary events) (a : Nat) : EventLazyBoundary (.pop a :: events) := by
  intro pre b c post he
  cases pre with
  | nil => cases he
  | cons e pre => exact h pre b c post (List.cons.inj he).2

theorem EventLazyBoundary.push_push {events : List EndpointEvent} {b : Nat}
    (h : EventLazyBoundary (.push b :: events)) (a : Nat) :
    EventLazyBoundary (.push a :: .push b :: events) := by
  intro pre c d post he
  cases pre with
  | nil => have hh := (List.cons.inj (List.cons.inj he).2).1; cases hh
  | cons e pre => exact h pre c d post (List.cons.inj he).2

theorem EventLazyBoundary.push_pop {events : List EndpointEvent}
    (h : EventLazyBoundary events) (a : Nat) : EventLazyBoundary (.push a :: .pop a :: events) := by
  intro pre b c post he
  cases pre with
  | nil =>
    have hab := EndpointEvent.push.inj (List.cons.inj he).1
    have hac := EndpointEvent.pop.inj (List.cons.inj (List.cons.inj he).2).1
    exact hab.symm.trans hac
  | cons e pre => exact h.pop a pre b c post (List.cons.inj he).2

theorem EventLazyBoundary.push_block {events : List EndpointEvent}
    (h : EventLazyBoundary events) (start count : Nat) :
    EventLazyBoundary ((List.range' start (count + 1)).map EndpointEvent.push ++
      .pop (start + count) :: events) := by
  induction count generalizing start with
  | zero => simpa using h.push_pop start
  | succ count ih =>
    have ht := ih (start + 1)
    rw [List.range'_succ, List.map_cons, List.cons_append] at ht
    simpa [List.range'_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht.push_push start

theorem canonicalEvents_lazy (next : Nat) (output : List Nat) :
    EventLazyBoundary (canonicalEvents next output) := by
  induction output generalizing next with
  | nil => exact .nil
  | cons a output ih =>
    by_cases ha : a < next
    · simpa [canonicalEvents, ha] using (ih next).pop a
    · have hlen : a + 1 - next = (a - next) + 1 := by omega
      have he : next + (a - next) = a := by omega
      simpa [canonicalEvents, ha, hlen, he] using (ih (a + 1)).push_block next (a - next)

end StackSorting.Generalized

namespace StackSorting.SparseEndpointMSO
open Generalized

theorem eventDiagram_lazy {events : List EndpointEvent} (h : EventLazyBoundary events) :
    LazyBoundary (eventDiagram events) := by
  intro x _ y _ hi hr hs
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hr
  have hy : y = x + 1 := hs.2.2.symm
  subst y
  obtain ⟨hx, hxa⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hy, hyb⟩ := List.getElem?_eq_some_iff.mp hb
  have hd : events.drop (x + 1) = .pop b :: events.drop (x + 2) := by
    simpa only [hyb, Nat.add_assoc] using (List.getElem_cons_drop hy).symm
  have he : events = events.take x ++ .push a :: .pop b :: events.drop (x + 2) := by
    calc
      events = events.take x ++ events[x] :: events.drop (x + 1) := by
        rw [List.getElem_cons_drop hx, List.take_append_drop]
      _ = _ := by rw [hxa, hd]
  have hab := h _ a b _ he
  subst b
  exact ⟨a, Or.inl ⟨ha, hb⟩⟩

theorem TimePath.rooted {D : Model} {n : Nat} (hp : TimePath D n) (hn : 0 < n) :
    RootedPathAxioms D 0 where
  root_mem := by simpa [hp.1] using hn
  no_incoming x hx hs := by
    have hh := (hp.2 x hx 0 (by simpa [hp.1] using hn)).mp hs
    omega
  reachable x hx := by
    have hz : 0 ∈ D.domain := by simpa [hp.1] using hn
    exact (closedReach_iff_walk D hz).mpr ((walk_iff_le D n hp hz hx).mpr (Nat.zero_le x))
  outgoing_unique x hx y hy z hz hxy hxz := by
    have hy' := (hp.2 x hx y hy).mp hxy
    have hz' := (hp.2 x hx z hz).mp hxz
    omega
  incoming_unique x hx y hy z hz hyx hzx := by
    have hy' := (hp.2 y hy x hx).mp hyx
    have hz' := (hp.2 z hz x hx).mp hzx
    omega

theorem MatchingAxioms.to_path {D : Model} {n : Nat}
    (h : MatchingAxioms D) (hp : TimePath D n) : PathMatchingAxioms D where
  partition := h.partition
  symmetric := h.symmetric
  perfect := h.perfect
  opposite := h.opposite
  forward x hx y hy hi hm := by
    have hlt := h.forward x hx y hy hi hm
    exact ⟨Nat.ne_of_lt hlt, (closedReach_iff_walk D hx).mpr
      ((walk_iff_le D n hp hx hy).mpr (Nat.le_of_lt hlt))⟩

/-- Every nonempty genuine permutation satisfies the complete syntactic
structural sentence, including the previously unformalized lazy boundary. -/
theorem canonicalDiagram_structural {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hn : 0 < n) :
    Satisfies (canonicalDiagram output) structuralSentence := by
  have hsize := canonical_domain_size hp
  have hlen : 0 < (canonicalEvents 0 output).length := by
    simp only [canonicalDiagram, eventDiagram, List.length_range] at hsize
    omega
  have hpath : TimePath (canonicalDiagram output) (canonicalEvents 0 output).length := eventDiagram_path _
  exact (satisfies_structuralSentence _).mpr ⟨⟨0, hpath.rooted hlen⟩,
    (canonicalMatchingAxioms hp).to_path hpath, eventDiagram_lazy (canonicalEvents_lazy 0 output)⟩

theorem nonempty_size_of_isomorphism {D : Model} {n : Nat} {output : List Nat}
    (hs : Satisfies D structuralSentence) (hp : output.Perm (List.range n))
    (iso : Isomorphism D (canonicalDiagram output)) : 0 < n := by
  obtain ⟨⟨root, hr⟩, _, _⟩ := (satisfies_structuralSentence D).mp hs
  have hm := iso.to_mem root hr.root_mem
  have hpos := List.length_pos_of_mem hm
  rw [canonical_domain_size hp] at hpos
  omega

/-- Exact structural characterization up to isomorphism, with the empty
permutation excluded exactly as in the nonempty path sentence. -/
theorem structuralSentence_iff_canonical (D : Model) :
    Satisfies D structuralSentence ↔ ∃ n output, 0 < n ∧ output.Perm (List.range n) ∧
      Nonempty (Isomorphism D (canonicalDiagram output)) := by
  constructor
  · intro hs
    obtain ⟨n, output, hp, ⟨iso⟩⟩ := structuralSentence_canonical_converse hs
    exact ⟨n, output, nonempty_size_of_isomorphism hs hp iso, hp, ⟨iso⟩⟩
  · rintro ⟨n, output, hn, hp, ⟨iso⟩⟩
    exact (iso.satisfies structuralSentence).mpr (canonicalDiagram_structural hp hn)

def acceptedSentence (r s : Nat) : Formula 0 0 := .conj structuralSentence (eligibilitySentence r s)

/-- The accepted arbitrary sparse structures are exactly the nonempty
generated permutations up to isomorphism, at all natural slot widths. -/
theorem acceptedSentence_iff_generated (D : Model) (r s : Nat) :
    Satisfies D (acceptedSentence r s) ↔
      ∃ n output, 0 < n ∧ output.Perm (List.range n) ∧
        Generalized.Run r s [] (List.range n) output [] ∧
        Nonempty (Isomorphism D (canonicalDiagram output)) := by
  constructor
  · rintro ⟨hs, hf⟩
    obtain ⟨n, output, hp, hg, ⟨iso⟩⟩ := acceptedModel_generated_permutation hs hf
    exact ⟨n, output, nonempty_size_of_isomorphism hs hp iso, hp, hg, ⟨iso⟩⟩
  · rintro ⟨n, output, hn, hp, hg, ⟨iso⟩⟩
    exact ⟨(iso.satisfies structuralSentence).mpr (canonicalDiagram_structural hp hn),
      (iso.satisfies _).mpr ((generated_iff_sparseEndpointMSO hp).mp hg)⟩

#print axioms canonicalDiagram_structural
#print axioms structuralSentence_iff_canonical
#print axioms acceptedSentence_iff_generated
end StackSorting.SparseEndpointMSO
