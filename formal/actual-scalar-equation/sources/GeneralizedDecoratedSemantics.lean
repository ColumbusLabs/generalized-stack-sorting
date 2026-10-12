import GeneralizedCoordinateState

/-! Literal decorated-factor semantics shared by the closure and counting
reductions. A state denotes a SET of current physical stacks via actual
maximum-insertion decoding. No closure, quotient, or cardinality identity is
part of the definition. -/
namespace StackSorting.Generalized
namespace Decorated

inductive Factor where
  | Z | O | B | T
  | C (size : Nat)
  deriving DecidableEq, Repr

abbrev State := List Factor

def Factor.height : Factor → Nat
  | .C size => size
  | _ => 1

def height (state : State) : Nat := (state.map Factor.height).sum

/-- C_0 is rejection, C_1 is Z, and C_m excludes precisely the all-one
binary word at length m. These are ordinary languages with no multiplicity. -/
def Factor.denotes : Factor → List Nat → Prop
  | .Z, digits => digits = [0]
  | .O, digits => digits = [1]
  | .B, digits => digits = [0] ∨ digits = [1]
  | .T, digits => digits = [0] ∨ digits = [1] ∨ digits = [2]
  | .C size, digits => digits.length = size ∧ (∀ digit ∈ digits, digit ≤ 1) ∧ 0 ∈ digits

def denotes : State → List Nat → Prop
  | [], digits => digits = []
  | factor :: rest, digits =>
      ∃ left right, factor.denotes left ∧ denotes rest right ∧ digits = left ++ right

/-- Exact suffix-transducer image of the factor language. -/
def ScanImage (marked : Nat) (state : State) (output : List Nat) : Prop :=
  ∃ digits, denotes state digits ∧ Coordinates.scan 3 marked digits = some output

/-- Literal represented physical orders, retaining one-based token ranks. -/
def Represents (state : State) (physical : List Nat) : Prop :=
  ∃ digits, denotes state digits ∧ Coordinates.Decodes digits physical

/-- Distinct admitted output language with n new, increasing input tokens.
An existential initial order or realizing physical history is never counted. -/
def Completion (state : State) (n : Nat) (output : List Nat) : Prop :=
  ∃ physical, Represents state physical ∧
    Run 3 3 physical (List.range' (height state + 1) n) output []

/-- No arbitrary O erasure is permitted. This is the syntactic O-free domain
used by the separately proved clause valuation. -/
def OFree (state : State) : Prop := ∀ factor ∈ state, factor ≠ .O

/-- Every coordinate word in a valid state is a genuine insertion encoding.
This says only that ambient slot bounds are respected, not that the state is
reachable, finite-state, or has any asserted completion count. -/
def Valid (state : State) : Prop :=
  ∀ digits, denotes state digits → ∃ physical, Coordinates.Decodes digits physical

/-- A binary block with precisely the selected zero-based coordinates forced
to zero. The unselected coordinates independently allow zero or one. -/
def zeroFace (size : Nat) (selected : List Nat) : State :=
  (List.range size).map (fun index => if index ∈ selected then Factor.Z else Factor.B)

theorem Factor.denotes_length {factor : Factor} {digits : List Nat}
    (h : factor.denotes digits) : digits.length = factor.height := by
  cases factor with
  | Z => simp only [Factor.denotes] at h; simp [h, Factor.height]
  | O => simp only [Factor.denotes] at h; simp [h, Factor.height]
  | B => rcases h with rfl | rfl <;> rfl
  | T => rcases h with rfl | rfl | rfl <;> rfl
  | C size => exact h.1

theorem denotes_length {state : State} {digits : List Nat}
    (h : denotes state digits) : digits.length = height state := by
  induction state generalizing digits with
  | nil => simp only [denotes] at h; simp [h, height]
  | cons factor state ih =>
    obtain ⟨left, right, hf, hr, rfl⟩ := h
    simp [List.length_append, Factor.denotes_length hf, ih hr, height]

theorem denotes_append (left right : State) (digits : List Nat) :
    denotes (left ++ right) digits ↔
      ∃ a b, denotes left a ∧ denotes right b ∧ digits = a ++ b := by
  induction left generalizing digits with
  | nil => simp [denotes]
  | cons factor left ih =>
    constructor
    · rintro ⟨a, tail, ha, ht, rfl⟩
      obtain ⟨b, c, hb, hc, rfl⟩ := (ih tail).mp ht
      exact ⟨a ++ b, c, ⟨a, b, ha, hb, rfl⟩, hc, by simp [List.append_assoc]⟩
    · rintro ⟨front, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
      exact ⟨a, b ++ c, ha, (ih (b ++ c)).mpr ⟨b, c, hb, hc, rfl⟩,
        by simp [List.append_assoc]⟩

theorem Represents.permutation {state : State} {physical : List Nat}
    (h : Represents state physical) : physical.Perm (List.range' 1 (height state)) := by
  obtain ⟨digits, hd, hp⟩ := h
  simpa [denotes_length hd] using hp.permutation

theorem Completion.permutation {state : State} {n : Nat} {output : List Nat}
    (h : Completion state n output) :
    output.Perm (List.range' 1 (height state+n)) := by
  obtain ⟨physical, hp, hr⟩ := h
  have hs : output.Perm (physical ++ List.range' (height state+1) n) := by
    simpa using hr.supply.symm
  have hl := hp.permutation.append_right (List.range' (height state+1) n)
  have he : List.range' 1 (height state) ++ List.range' (height state+1) n =
      List.range' 1 (height state+n) := by
    simp [Nat.add_comm]
  exact (hs.trans hl).trans (by rw [he])

end Decorated
end StackSorting.Generalized
