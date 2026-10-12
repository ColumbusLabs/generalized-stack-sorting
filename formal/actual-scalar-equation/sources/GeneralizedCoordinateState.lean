import GeneralizedCoordinateRecords
import GeneralizedRankNormalization

/-! Coordinate decoding, current physical stacks, and exact standardized
successors. No finite-state or counting equivalence is a premise. -/
namespace StackSorting.Generalized
namespace Coordinates
open LazyCode

/-- Concatenating coordinate words composes their actual physical insertions. -/
theorem build_append (next : Nat) (left right held : List Nat) :
    build next (left ++ right) held = (do
      let middle ← build next left held
      build (next + left.length) right middle) := by
  induction left generalizing next held with
  | nil => simp [build]
  | cons slot left ih =>
    simp [build, ih, Option.bind_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Physical insertion is symbol-oblivious, including its failure cases. -/
theorem insertAt_map (f : Nat → Nat) (slot token : Nat) (held : List Nat) :
    (insertAt? slot token held).map (List.map f) =
      insertAt? slot (f token) (held.map f) := by
  induction slot generalizing held with
  | zero => rfl
  | succ slot ih =>
    cases held with
    | nil => rfl
    | cons head held =>
      simp [insertAt?, ← ih, Option.map_map, Function.comp_def]

/-- Relabelling commutes with an arbitrary coordinate word whenever the
newly introduced labels have the specified correspondence. This equation
includes both successful and failed physical decodings. -/
theorem build_map (f : Nat → Nat) (next next' : Nat) (digits held : List Nat)
    (fresh : ∀ offset, f (next + offset) = next' + offset) :
    (build next digits held).map (List.map f) =
      build next' digits (held.map f) := by
  induction digits generalizing next next' held with
  | nil => rfl
  | cons slot digits ih =>
    have hhead : f next = next' := by simpa using fresh 0
    have htail : ∀ offset, f ((next+1)+offset) = (next'+1)+offset := by
      intro offset
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fresh (offset+1)
    have hi' := insertAt_map f slot next held
    rw [hhead] at hi'
    simp only [build]
    rw [← hi']
    cases hi : insertAt? slot next held with
    | none => rfl
    | some after =>
      change (build (next+1) digits after).map (List.map f) =
        build (next'+1) digits (after.map f)
      exact ih (next+1) (next'+1) after htail

/-- Decoding consumes exactly the increasing labels specified by the word
length. In particular, an initially empty decoding is a real permutation. -/
theorem build_supply {next : Nat} {digits held final : List Nat}
    (hb : build next digits held = some final) :
    final.Perm (held ++ List.range' next digits.length) := by
  induction digits generalizing next held with
  | nil =>
    have he : held = final := by simpa [build] using hb
    simp [← he]
  | cons slot digits ih =>
    cases hi : insertAt? slot next held with
    | none => simp [build, hi] at hb
    | some middle =>
      have ht : build (next+1) digits middle = some final := by simpa [build, hi] using hb
      have hs : Step (slot+1) 0 held [next] [] middle :=
        step_relational (slot+1) 0 (.push slot next) held middle []
          (by simp [step, hi])
      have hp : middle.Perm (held ++ [next]) := by simpa using hs.supply.symm
      simpa [List.range'_succ, List.append_assoc] using
        (ih ht).trans (hp.append_right (List.range' (next+1) digits.length))

/-- The physical order represented by a full coordinate word, with one-based
held ranks exactly as in the established rank-normalized code recognizer. -/
def Decodes (digits physical : List Nat) : Prop := build 1 digits [] = some physical

theorem Decodes.permutation {digits physical : List Nat} (h : Decodes digits physical) :
    physical.Perm (List.range' 1 digits.length) := by
  simpa using build_supply h

theorem Decodes.nodup {digits physical : List Nat} (h : Decodes digits physical) :
    physical.Nodup := h.permutation.nodup_iff.mpr List.nodup_range'

/-- Closing the deleted rank fixes every earlier represented token. -/
theorem closeRank_prefix {k : Nat} {digits physical : List Nat}
    (h : Decodes digits physical) (hlen : digits.length + 1 = k) :
    physical.map (closeRank k) = physical := by
  calc
    physical.map (closeRank k) = physical.map (fun token => token) := by
      apply List.map_congr_left
      intro token hm
      have ht := List.mem_range'.mp (h.permutation.mem_iff.mp hm)
      simp only [closeRank]
      have hn : ¬ k < token := by omega
      simp [hn]
    _ = physical := by simp

/-- The coordinate word after selecting one held rank. The earlier digits
are unchanged, the selected digit disappears, and the entire later suffix
is the exact deterministic transducer image. -/
def eraseWord (earlier : List Nat) (selected : Nat) (later : List Nat) : List Nat :=
  earlier ++ eraseSuffix selected later

/-- Exact standardized deletion from a completely decoded current stack.
This theorem removes the temporary physical-order and distinctness premises
of the local scan theorem by deriving both from the full coordinate decoder. -/
theorem decoded_pop_successor {earlier later physical : List Nat} {selected : Nat}
    (decoded : Decodes (earlier ++ selected :: later) physical) :
    ∃ survivor,
      removeAt? (position selected later) physical = some (survivor, earlier.length+1) ∧
      Decodes (eraseWord earlier selected later)
        (survivor.map (closeRank (earlier.length+1))) := by
  unfold Decodes at decoded
  rw [build_append] at decoded
  cases hp : build 1 earlier [] with
  | none => simp [hp] at decoded
  | some base =>
    have hbase : Decodes earlier base := hp
    have hs : build (earlier.length+1) (selected :: later) base = some physical := by
      simpa [hp, Nat.add_comm] using decoded
    cases hi : insertAt? selected (earlier.length+1) base with
    | none => simp [build, hi] at hs
    | some inserted =>
      have ht : build ((earlier.length+1)+1) later inserted = some physical := by
        simpa [build, hi] using hs
      obtain ⟨survivor, hb, hd⟩ := selected_coordinate_removal hi ht
      refine ⟨survivor, hd, ?_⟩
      have hmap := build_map (closeRank (earlier.length+1))
        ((earlier.length+1)+1) (earlier.length+1) (eraseSuffix selected later) base
        (by intro offset; simp only [closeRank]; split <;> omega)
      rw [hb, Option.map_some, closeRank_prefix hbase rfl] at hmap
      unfold Decodes eraseWord
      rw [build_append, hp]
      simpa [Nat.add_comm] using hmap.symm

/-- All-length held transition from decoded coordinates to the existing
rank-normalized physical subset recognizer, with exact acceptance and the
standardized successor word. -/
theorem decoded_scan_iff_rankPop {r width : Nat} {earlier later physical : List Nat}
    {selected : Nat} (decoded : Decodes (earlier ++ selected :: later) physical) :
    (∃ result, result ∈ rankPopOrders width (earlier.length+1) physical) ↔
      scan width selected later = some (eraseSuffix selected later) := by
  obtain ⟨survivor, hd, _⟩ := decoded_pop_successor decoded
  have hn := decoded.nodup
  rw [scan_eq]
  constructor
  · rintro ⟨result, hm⟩
    obtain ⟨after, ha, _⟩ := List.mem_map.mp hm
    have hp : Step r width physical [] [earlier.length+1] after := mem_popOrders_iff.mp ha
    have hlt := ((physical_pop_iff hn hd).mp hp).1
    simp [hlt]
  · intro hs
    have hlt : position selected later < width := by
      by_cases h : position selected later < width
      · exact h
      · simp [h] at hs
    have hp : Step r width physical [] [earlier.length+1] survivor :=
      (physical_pop_iff hn hd).mpr ⟨hlt, rfl⟩
    exact ⟨survivor.map (closeRank (earlier.length+1)),
      List.mem_map.mpr ⟨survivor, mem_popOrders_iff.mpr hp, rfl⟩⟩

#print axioms build_append
#print axioms insertAt_map
#print axioms build_map
#print axioms build_supply
#print axioms Decodes.permutation
#print axioms decoded_pop_successor
#print axioms decoded_scan_iff_rankPop
end Coordinates
end StackSorting.Generalized
