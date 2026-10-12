import GeneralizedRelational

/-!
# Exact maximum-insertion coordinate deletion

This module supplies the physical semantics of the deletion transducer used
in the reviewed (3,3) decorated normal form. It does not assume that normal
form, its language closure, O-run quotient, clause valuation, or matrix
counting theorem. Coordinates describe current physical orders, not histories.
-/
namespace StackSorting.Generalized
namespace Coordinates

/-- Slot of the marked old token after a new token is inserted. -/
def advance (slot marked : Nat) : Nat :=
  if slot ≤ marked then marked + 1 else marked

/-- Insertion slot of the new token after the marked old token is removed. -/
def retained (slot marked : Nat) : Nat :=
  if slot ≤ marked then slot else slot - 1

/-- The exact two cases of the maximum-insertion deletion transducer. This
tracks a distinguished physical occurrence, so it needs no label distinctness. -/
theorem insert_remove_marked {slot marked new target : Nat}
    {held survivor inserted : List Nat}
    (hd : removeAt? marked held = some (survivor, target))
    (hi : insertAt? slot new held = some inserted) :
    ∃ after, insertAt? (retained slot marked) new survivor = some after ∧
      removeAt? (advance slot marked) inserted = some (after, target) := by
  induction slot generalizing marked held survivor inserted with
  | zero =>
    simp only [insertAt?, Option.some.injEq] at hi
    subst inserted
    exact ⟨new :: survivor, rfl, by simp [advance, removeAt?, hd]⟩
  | succ slot ih =>
    cases held with
    | nil => simp [insertAt?] at hi
    | cons head held =>
      cases hh : insertAt? slot new held with
      | none => simp [insertAt?, hh] at hi
      | some tail =>
        simp only [insertAt?, hh, Option.map_some, Option.some.injEq] at hi
        subst inserted
        cases marked with
        | zero =>
          simp only [removeAt?, Option.some.injEq, Prod.mk.injEq] at hd
          rcases hd with ⟨rfl, rfl⟩
          exact ⟨tail, by simpa [retained] using hh, by simp [advance, removeAt?]⟩
        | succ marked =>
          cases hr : removeAt? marked held with
          | none => simp [removeAt?, hr] at hd
          | some pair =>
            rcases pair with ⟨rest, token⟩
            simp only [removeAt?, hr, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at hd
            rcases hd with ⟨rfl, rfl⟩
            obtain ⟨after, ha, hb⟩ := ih hr hh
            refine ⟨head :: after, ?_, ?_⟩
            · have he : retained (slot+1) (marked+1) = retained slot marked + 1 := by
                by_cases h : slot ≤ marked
                · simp [retained, h]
                · simp only [retained, Nat.add_le_add_iff_right, h, ite_false]
                  omega
              simp only [he, insertAt?, ha, Option.map_some]
            · by_cases h : slot ≤ marked <;>
                simpa [advance, h, removeAt?] using
                  congrArg (Option.map (fun pair => (head :: pair.1, pair.2))) hb

/-- Read coordinates from left to right, inserting successive new maxima.
The labels may start above zero; arbitrary earlier held labels are retained. -/
def build (next : Nat) : List Nat → List Nat → Option (List Nat)
  | [], held => some held
  | slot :: digits, held => do
      let after ← insertAt? slot next held
      build (next+1) digits after

/-- Final physical position of the marked token. -/
def position (marked : Nat) : List Nat → Nat
  | [] => marked
  | slot :: digits => position (advance slot marked) digits

/-- Surviving maximum-insertion coordinates. Original token labels are kept,
so this definition does not need to assume a relabelling theorem. -/
def eraseSuffix (marked : Nat) : List Nat → List Nat
  | [] => []
  | slot :: digits => retained slot marked :: eraseSuffix (advance slot marked) digits

/-- The central all-length physical invariant. Scanning any number of later
coordinates yields exactly the original final stack with the marked token
removed. The output is a single physical order, never a sum over histories. -/
theorem build_eraseSuffix {next marked target : Nat}
    {digits held survivor final : List Nat}
    (hd : removeAt? marked held = some (survivor, target))
    (hb : build next digits held = some final) :
    ∃ after, build next (eraseSuffix marked digits) survivor = some after ∧
      removeAt? (position marked digits) final = some (after, target) := by
  induction digits generalizing next marked held survivor final with
  | nil =>
    simp only [build, Option.some.injEq] at hb
    subst final
    exact ⟨survivor, rfl, hd⟩
  | cons slot digits ih =>
    cases hi : insertAt? slot next held with
    | none => simp [build, hi] at hb
    | some inserted =>
      have ht : build (next+1) digits inserted = some final := by
        simpa [build, hi] using hb
      obtain ⟨middle, hm, hd'⟩ := insert_remove_marked hd hi
      obtain ⟨after, ha, hr⟩ := ih hd' ht
      exact ⟨after, by simpa [eraseSuffix, build, hm] using ha, hr⟩

theorem marked_le_advance (slot marked : Nat) : marked ≤ advance slot marked := by
  unfold advance
  split <;> omega

theorem marked_le_position (marked : Nat) (digits : List Nat) :
    marked ≤ position marked digits := by
  induction digits generalizing marked with
  | nil => exact Nat.le_refl marked
  | cons slot digits ih =>
    exact Nat.le_trans (marked_le_advance slot marked) (ih (advance slot marked))

/-- Reject as soon as the tracked physical position is outside the pop width.
For width three this is precisely the reviewed three-live-state transducer. -/
def scan (width marked : Nat) : List Nat → Option (List Nat)
  | [] => if marked < width then some [] else none
  | slot :: digits =>
      if marked < width then
        (scan width (advance slot marked) digits).map (retained slot marked :: ·)
      else none

/-- Early rejection loses no accepted physical pop. No suffix-length bound,
finite-state saturation, or finite checking premise occurs in this theorem. -/
theorem scan_eq (width marked : Nat) (digits : List Nat) :
    scan width marked digits =
      if position marked digits < width then some (eraseSuffix marked digits) else none := by
  induction digits generalizing marked with
  | nil => rfl
  | cons slot digits ih =>
    by_cases hm : marked < width
    · simp only [scan, hm, ite_true, ih, position, eraseSuffix]
      by_cases hp : position (advance slot marked) digits < width <;> simp [hp]
    · have hn : ¬ position (advance slot marked) digits < width := by
        have h := marked_le_advance slot marked
        have h' := marked_le_position (advance slot marked) digits
        omega
      simp [scan, hm, position, hn]

/-- A marked coordinate can be recovered after insertion at that coordinate. -/
theorem remove_insert {slot token : Nat} {held after : List Nat}
    (hi : insertAt? slot token held = some after) :
    removeAt? slot after = some (held, token) := by
  obtain ⟨pre, post, rfl, hl, rfl⟩ := insertAt_split slot token held after hi
  simpa [← hl] using removeAt_prefix pre post token

/-- The transducer is now attached to an actual selected coordinate: decode
its prefix, insert that selected token, and scan every later coordinate. -/
theorem selected_coordinate_removal {next slot : Nat} {base inserted final suffix : List Nat}
    (hi : insertAt? slot next base = some inserted)
    (hb : build (next+1) suffix inserted = some final) :
    ∃ after, build (next+1) (eraseSuffix slot suffix) base = some after ∧
      removeAt? (position slot suffix) final = some (after, next) :=
  build_eraseSuffix (remove_insert hi) hb

/-- Duplicate-free physical stacks identify a token's removal position
uniquely. Without this invariant, equal labels at different positions could
make a different physical occurrence appear to rescue a rejected code. -/
theorem removeAt_idxOf {marked token : Nat} {held after : List Nat}
    (hn : held.Nodup) (hd : removeAt? marked held = some (after, token)) :
    held.idxOf token = marked := by
  obtain ⟨pre, post, rfl, hl, rfl⟩ := removeAt_split marked token held after hd
  have hnot : token ∉ pre := by
    have hd := (List.nodup_append.mp hn).2.2
    intro hm
    exact hd token hm token (by simp) rfl
  simp [List.idxOf_append, hnot, hl]

/-- Exact relation to the original machine's physical pop, for any positive
or zero width. Both accepted and rejected scan outcomes are accounted for. -/
theorem physical_pop_iff {r width marked token : Nat} {held after result : List Nat}
    (hn : held.Nodup) (hd : removeAt? marked held = some (after, token)) :
    Step r width held [] [token] result ↔ marked < width ∧ result = after := by
  constructor
  · intro hp
    cases hp with
    | pop pre post token allowed =>
      have hi := removeAt_idxOf hn hd
      have hi' := removeAt_idxOf hn (removeAt_prefix pre post token)
      have hs : marked = pre.length := hi.symm.trans hi'
      have he : some (after, token) = some (pre ++ post, token) := by
        rw [← hd, hs, removeAt_prefix]
      have ha : after = pre ++ post := (Prod.mk.inj (Option.some.inj he)).1
      exact ⟨by omega, ha.symm⟩
  · rintro ⟨allowed, rfl⟩
    exact step_relational r width (.pop marked) held result [token]
      (by simp [step, allowed, hd])

/-- An actual selected maximum-insertion coordinate is poppable exactly when
its deterministic suffix scan accepts. This is an unrestricted all-length
machine/transducer equivalence, specialized below to top-three removal. -/
theorem selected_scan_iff_pop {r width next slot : Nat}
    {base inserted final suffix : List Nat}
    (hi : insertAt? slot next base = some inserted)
    (hb : build (next+1) suffix inserted = some final)
    (hn : final.Nodup) :
    (∃ after, Step r width final [] [next] after) ↔
      scan width slot suffix = some (eraseSuffix slot suffix) := by
  obtain ⟨after, _, hd⟩ := selected_coordinate_removal hi hb
  rw [scan_eq]
  constructor
  · rintro ⟨result, hp⟩
    have allowed := ((physical_pop_iff hn hd).mp hp).1
    simp [allowed]
  · intro hs
    have allowed : position slot suffix < width := by
      by_cases h : position slot suffix < width
      · exact h
      · simp [h] at hs
    exact ⟨after, (physical_pop_iff hn hd).mpr ⟨allowed, rfl⟩⟩

/-- The concrete machine width in the accepted unrestricted (3,3) result. -/
theorem three_three_selected_scan_iff_pop {next slot : Nat}
    {base inserted final suffix : List Nat}
    (hi : insertAt? slot next base = some inserted)
    (hb : build (next+1) suffix inserted = some final)
    (hn : final.Nodup) :
    (∃ after, Step 3 3 final [] [next] after) ↔
      scan 3 slot suffix = some (eraseSuffix slot suffix) :=
  selected_scan_iff_pop hi hb hn

theorem eraseSuffix_length (marked : Nat) (digits : List Nat) :
    (eraseSuffix marked digits).length = digits.length := by
  induction digits generalizing marked with
  | nil => rfl
  | cons slot digits ih => simp [eraseSuffix, ih]

/-- Every accepted suffix image for top-three coordinates is binary. This
is derived from the physical-position invariant, not tested at finite height. -/
theorem eraseSuffix_binary {marked : Nat} {digits : List Nat}
    (bounded : ∀ slot ∈ digits, slot < 3)
    (accepted : position marked digits < 3) :
    ∀ digit ∈ eraseSuffix marked digits, digit ≤ 1 := by
  induction digits generalizing marked with
  | nil => simp [eraseSuffix]
  | cons slot digits ih =>
    have hs : slot < 3 := bounded slot (by simp)
    have ht : ∀ a ∈ digits, a < 3 := fun a ha => bounded a (by simp [ha])
    have hp : advance slot marked < 3 :=
      Nat.lt_of_le_of_lt (marked_le_position (advance slot marked) digits) accepted
    have hd : retained slot marked ≤ 1 := by
      by_cases h : slot ≤ marked
      · simp only [advance, h, ite_true] at hp
        simp only [retained, h, ite_true]
        omega
      · simp only [retained, h, ite_false]
        omega
    intro digit hmem
    simp only [eraseSuffix, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact hd
    · exact ih ht accepted digit hmem

/-- The three live states accept an empty suffix. -/
theorem scan_three_nil (marked : Nat) (h : marked < 3) : scan 3 marked [] = some [] := by
  simp [scan, h]

/-- At state two every bounded next insertion goes above the marked token,
so a nonempty suffix rejects. This includes input coordinate two. -/
theorem scan_three_two_cons {slot : Nat} (h : slot < 3) (digits : List Nat) :
    scan 3 2 (slot :: digits) = none := by
  have hs : slot ≤ 2 := by omega
  have hp : ¬ position 3 digits < 3 := by
    have hm := marked_le_position 3 digits
    omega
  simp [scan, advance, hs, scan_eq, hp]

theorem scan_three_zero_zero (digits : List Nat) :
    scan 3 0 (0 :: digits) = (scan 3 1 digits).map (0 :: ·) := by
  simp [scan, advance, retained]

theorem scan_three_zero_one (digits : List Nat) :
    scan 3 0 (1 :: digits) = (scan 3 0 digits).map (0 :: ·) := by
  simp [scan, advance, retained]

theorem scan_three_zero_two (digits : List Nat) :
    scan 3 0 (2 :: digits) = (scan 3 0 digits).map (1 :: ·) := by
  simp [scan, advance, retained]

theorem scan_three_one_zero (digits : List Nat) :
    scan 3 1 (0 :: digits) = (scan 3 2 digits).map (0 :: ·) := by
  simp [scan, advance, retained]

theorem scan_three_one_one (digits : List Nat) :
    scan 3 1 (1 :: digits) = (scan 3 2 digits).map (1 :: ·) := by
  simp [scan, advance, retained]

theorem scan_three_one_two (digits : List Nat) :
    scan 3 1 (2 :: digits) = (scan 3 1 digits).map (1 :: ·) := by
  simp [scan, advance, retained]

#print axioms insert_remove_marked
#print axioms build_eraseSuffix
#print axioms scan_eq
#print axioms selected_coordinate_removal
#print axioms physical_pop_iff
#print axioms three_three_selected_scan_iff_pop

end Coordinates
end StackSorting.Generalized
