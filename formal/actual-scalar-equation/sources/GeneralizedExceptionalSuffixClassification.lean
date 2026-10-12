import GeneralizedExceptionalSuffixImages

/-! The converse exceptional-tail classification. Nonempty state-one images
force exactly a T-prefix followed by one unary factor; this is proved from
literal scan rejection, not assumed decorated closure. -/
namespace StackSorting.Generalized.Decorated
namespace ExceptionalSuffix
open Coordinates
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Canonical correlated factors have at least two coordinates. C_0 and C_1
must be normalized to rejection and Z before this classification is used. -/
def CanonicalFactors (state : State) : Prop :=
  ∀ size, Factor.C size ∈ state → 2 ≤ size

theorem canonical_tail {factor : Factor} {state : State}
    (hc : CanonicalFactors (factor :: state)) : CanonicalFactors state := by
  intro size hm
  exact hc size (by simp [hm])

theorem canonical_denotes_nonempty {state : State} (hc : CanonicalFactors state)
    (hn : state ≠ []) {digits : List Nat} (hd : denotes state digits) : digits ≠ [] := by
  cases state with
  | nil => exact (hn rfl).elim
  | cons factor rest =>
    obtain ⟨left, right, hl, hr, rfl⟩ := hd
    have hp : 0 < factor.height := by
      cases factor with
      | Z => decide
      | O => decide
      | B => decide
      | T => decide
      | C size => have := hc size (by simp); change 0 < size; omega
    have hlen := Factor.denotes_length hl
    intro he
    have hz := congrArg List.length he
    simp only [List.length_append, List.length_nil] at hz
    omega

/-- From state one, a binary unary head consumes the last remaining token. -/
theorem scanImage_one_binary_terminal {factor : Factor} {state : State}
    (hf : factor = .Z ∨ factor = .O ∨ factor = .B)
    (hc : CanonicalFactors state) {output : List Nat}
    (hs : ScanImage 1 (factor :: state) output) : state = [] := by
  by_cases hn : state = []
  · exact hn
  exfalso
  obtain ⟨digits, hd, hs⟩ := hs
  obtain ⟨left, right, hl, hr, rfl⟩ := hd
  have hnr := canonical_denotes_nonempty hc hn hr
  have hbr := denotes_bounded hr
  have binaryReject : ∀ digit, digit ≤ 1 → scan 3 1 (digit :: right) = none := by
    intro digit hb
    rw [scan_one_binary_head hb right hbr]
    simp [hnr]
  rcases hf with rfl | rfl | rfl
  · have he : left = [0] := hl
    subst left
    simpa [binaryReject 0 (by omega)] using hs
  · have he : left = [1] := hl
    subst left
    simpa [binaryReject 1 (by omega)] using hs
  · rcases hl with rfl | rfl
    · simpa [binaryReject 0 (by omega)] using hs
    · simpa [binaryReject 1 (by omega)] using hs

/-- Every accepted nonempty canonical factor suffix from state one is an
exceptional suffix, with no bound on its length or clause parameters. -/
theorem scanImage_one_classification {state : State} (hc : CanonicalFactors state)
    (hn : state ≠ []) {output : List Nat} (hs : ScanImage 1 state output) :
    ∃ q factor, Unary factor ∧ state = List.replicate q .T ++ [factor] := by
  induction state generalizing output with
  | nil => exact (hn rfl).elim
  | cons factor state ih =>
    have hct := canonical_tail hc
    cases factor with
    | Z =>
      have he := scanImage_one_binary_terminal (Or.inl rfl) hct hs
      subst state
      exact ⟨0, .Z, Or.inl rfl, rfl⟩
    | O =>
      have he := scanImage_one_binary_terminal (Or.inr (Or.inl rfl)) hct hs
      subst state
      exact ⟨0, .O, Or.inr (Or.inl rfl), rfl⟩
    | B =>
      have he := scanImage_one_binary_terminal (Or.inr (Or.inr rfl)) hct hs
      subst state
      exact ⟨0, .B, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    | T =>
      by_cases he : state = []
      · subst state
        exact ⟨0, .T, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
      · obtain ⟨tail, ht, _⟩ :=
          (scanImage_one_T (fun digits hd => canonical_denotes_nonempty hct he hd) output).mp hs
        obtain ⟨q, terminalFactor, hf, hstate⟩ := ih hct he ht
        exact ⟨q+1, terminalFactor, hf, by simp [List.replicate_succ, hstate]⟩
    | C size =>
      have hm := hc size (by simp)
      exact (ScanImage_one_C hm hs).elim

/-- The image itself, including its terminal output constraint, is now
classified. This is useful for closure proofs without arbitrary case guesses. -/
theorem scanImage_one_iff_exceptional {state : State} (hc : CanonicalFactors state)
    (hn : state ≠ []) (output : List Nat) :
    ScanImage 1 state output ↔
      ∃ q factor, Unary factor ∧ state = List.replicate q .T ++ [factor] ∧
        denotes (List.replicate q .O ++ [terminal factor]) output := by
  constructor
  · intro hs
    obtain ⟨q, factor, hf, he⟩ := scanImage_one_classification hc hn hs
    exact ⟨q, factor, hf, he, (scanImage_one_exceptional q hf output).mp (he ▸ hs)⟩
  · rintro ⟨q, factor, hf, rfl, ho⟩
    exact (scanImage_one_exceptional q hf output).mpr ho

#print axioms canonical_denotes_nonempty
#print axioms scanImage_one_classification
#print axioms scanImage_one_iff_exceptional

end ExceptionalSuffix
end StackSorting.Generalized.Decorated
