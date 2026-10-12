import GeneralizedDecoratedSemantics

/-! Exact factor-language transitions attached to the original rank-normalized
physical subset recognizer. Language rewrite correctness is a separate theorem;
this module proves that the literal coordinate image is the actual held-pop
image, including standardization and rejection. -/
namespace StackSorting.Generalized
namespace Decorated
open Coordinates LazyCode

/-- The zero-based selected held rank deletes one coordinate and runs the
proved physical deletion scan on every later coordinate. This is a set image. -/
def PopImage (state : State) (rank : Nat) (output : List Nat) : Prop :=
  ∃ earlier selected later,
    denotes state (earlier ++ selected :: later) ∧ earlier.length = rank ∧
    scan 3 selected later = some (eraseSuffix selected later) ∧
    output = eraseWord earlier selected later

/-- The exact physical recognizer transition, taking a union over all current
physical orders represented by the state. Equal witnesses give no multiplicity. -/
def PhysicalPopImage (state : State) (rank : Nat) (after : List Nat) : Prop :=
  ∃ physical, Represents state physical ∧ after ∈ rankPopOrders 3 (rank+1) physical

/-- Every accepted coordinate-image word really decodes; ambient validity of
successors is derived from the actual physical pop. -/
theorem PopImage.decodes {state : State} {rank : Nat} {output : List Nat}
    (valid : Valid state) (h : PopImage state rank output) :
    ∃ physical, Coordinates.Decodes output physical := by
  obtain ⟨earlier, selected, later, hd, _, _, rfl⟩ := h
  obtain ⟨physical, hp⟩ := valid _ hd
  obtain ⟨survivor, _, hs⟩ := decoded_pop_successor hp
  exact ⟨_, hs⟩

/-- A list coordinate decomposition at any valid zero-based index. -/
theorem split_coordinate {digits : List Nat} {rank : Nat} (h : rank < digits.length) :
    ∃ earlier selected later, earlier.length = rank ∧ digits = earlier ++ selected :: later := by
  have he : digits[rank] :: digits.drop (rank+1) = digits.drop rank :=
    List.getElem_cons_drop h
  exact ⟨digits.take rank, digits[rank], digits.drop (rank+1),
    by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt h)],
    by rw [he, List.take_append_drop]⟩

/-- No formal-language hypothesis is needed in the machine-to-language
orientation: an actual represented pop produces a literal PopImage word. -/
theorem physicalPop_to_coordinate {state : State} {rank : Nat} {after : List Nat}
    (h : PhysicalPopImage state rank after) :
    ∃ output, PopImage state rank output ∧ Coordinates.Decodes output after := by
  obtain ⟨physical, ⟨digits, hd, hp⟩, hm⟩ := h
  obtain ⟨survivor, hpop, rfl⟩ := List.mem_map.mp hm
  have pop : Step 3 3 physical [] [rank+1] survivor := mem_popOrders_iff.mp hpop
  have tokenMem : rank+1 ∈ physical := by
    have hs := pop.supply.mem_iff.mpr (by simp : rank+1 ∈ [rank+1] ++ survivor)
    simpa using hs
  have tokenRange := List.mem_range'.mp (hp.permutation.mem_iff.mp tokenMem)
  have bound : rank < digits.length := by omega
  obtain ⟨earlier, selected, later, hlen, he⟩ := split_coordinate bound
  have hp' : Coordinates.Decodes (earlier ++ selected :: later) physical := by
    simpa [he] using hp
  obtain ⟨actualSurvivor, hremove, hdecode⟩ := decoded_pop_successor hp'
  have pop' : Step 3 3 physical [] [earlier.length+1] survivor := by simpa [hlen] using pop
  obtain ⟨allowed, hs⟩ := (physical_pop_iff hp'.nodup hremove).mp pop'
  refine ⟨eraseWord earlier selected later, ?_, ?_⟩
  · exact ⟨earlier, selected, later, by simpa [← he] using hd, hlen,
      by simp [scan_eq, allowed], rfl⟩
  · simpa [hs, hlen] using hdecode

/-- Conversely the physical subset recognizer realizes every decoded image
of a valid factor state, preserving the exact post-pop standardized order. -/
theorem coordinate_to_physicalPop {state : State} {rank : Nat} {output after : List Nat}
    (valid : Valid state) (h : PopImage state rank output)
    (hafter : Coordinates.Decodes output after) : PhysicalPopImage state rank after := by
  obtain ⟨earlier, selected, later, hd, hlen, hscan, rfl⟩ := h
  obtain ⟨physical, hp⟩ := valid _ hd
  obtain ⟨survivor, hremove, hdecode⟩ := decoded_pop_successor hp
  have he : after = survivor.map (closeRank (earlier.length+1)) :=
    Option.some.inj (hafter.symm.trans hdecode)
  have allowed : position selected later < 3 := by
    rw [scan_eq] at hscan
    by_cases hlt : position selected later < 3
    · exact hlt
    · simp [hlt] at hscan
  have pop : Step 3 3 physical [] [earlier.length+1] survivor :=
    (physical_pop_iff hp.nodup hremove).mpr ⟨allowed, rfl⟩
  refine ⟨physical, ⟨_, hd, hp⟩, ?_⟩
  exact List.mem_map.mpr ⟨survivor, mem_popOrders_iff.mpr (by simpa [hlen] using pop),
    by simpa [hlen] using he.symm⟩

/-- Exact held-transition semantics for arbitrary valid decorated states.
Later closure theorems only have to identify this explicit PopImage language. -/
theorem physicalPop_iff_coordinate {state : State} {rank : Nat} {after : List Nat}
    (valid : Valid state) :
    PhysicalPopImage state rank after ↔
      ∃ output, PopImage state rank output ∧ Coordinates.Decodes output after := by
  constructor
  · exact physicalPop_to_coordinate
  · rintro ⟨output, hp, hd⟩
    exact coordinate_to_physicalPop valid hp hd

/-- Any exact language rewrite of PopImage yields the exact represented
physical successor set, and its ambient validity follows automatically. -/
theorem exact_pop_rewrite {state next : State} {rank : Nat}
    (valid : Valid state)
    (rewrite : ∀ output, denotes next output ↔ PopImage state rank output) :
    Valid next ∧ (∀ after, Represents next after ↔ PhysicalPopImage state rank after) := by
  constructor
  · intro output hd
    exact ((rewrite output).mp hd).decodes valid
  · intro after
    rw [physicalPop_iff_coordinate valid]
    constructor
    · rintro ⟨output, hd, hp⟩
      exact ⟨output, (rewrite output).mp hd, hp⟩
    · rintro ⟨output, hd, hp⟩
      exact ⟨output, (rewrite output).mpr hd, hp⟩

#print axioms PopImage.decodes
#print axioms physicalPop_to_coordinate
#print axioms coordinate_to_physicalPop
#print axioms physicalPop_iff_coordinate
#print axioms exact_pop_rewrite
end Decorated
end StackSorting.Generalized
