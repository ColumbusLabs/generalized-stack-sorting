import GeneralizedCodeRecognition

/-!
# Actual distinct-permutation counts for the unrestricted machine

The output list is defined by a duplicate-free finite universe of labelled
words, filtered by the already proved executable physical subset recognizer.
Membership is proved equivalent to the literal machine Run, for every n.
An independently enumerated list of complete accepted lazy codes has the
same cardinality by a proved bijection. No operation history is counted.
There is no fixed height or input-length cutoff in these definitions.
-/
namespace StackSorting.Generalized
namespace ActualCounting
open LazyCode

/-- Remove repeated elements without assigning any multiplicity to witnesses. -/
def unique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: rest => if a ∈ rest then unique rest else a :: unique rest

theorem mem_unique {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    a ∈ unique xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [unique]
  | cons head rest ih =>
    by_cases hh : head ∈ rest
    · simp only [unique, hh, ite_true, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hm)
        · exact hh
        · exact hm
    · simp [unique, hh, ih]

theorem unique_nodup {α : Type} [DecidableEq α] (xs : List α) : (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons head rest ih =>
    by_cases hh : head ∈ rest
    · simpa [unique, hh] using ih
    · simp [unique, hh, List.nodup_cons, mem_unique, ih]

/-- Every word of a specified length over an explicit finite alphabet. -/
def words {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n+1 => alphabet.flatMap (fun a => (words alphabet n).map (a :: ·))

theorem mem_words {α : Type} (alphabet : List α) (n : Nat) (word : List α) :
    word ∈ words alphabet n ↔ word.length = n ∧ ∀ a ∈ word, a ∈ alphabet := by
  induction n generalizing word with
  | zero => cases word <;> simp [words]
  | succ n ih =>
    cases word with
    | nil => simp [words]
    | cons head rest =>
      simp only [words, List.mem_flatMap, List.mem_map, List.cons.injEq,
        List.length_cons, Nat.add_right_cancel_iff, List.mem_cons]
      constructor
      · rintro ⟨a, ha, tail, ht, rfl, rfl⟩
        have hw := (ih tail).mp ht
        exact ⟨hw.1, fun b hb => hb.elim (fun he => he ▸ ha) (hw.2 b)⟩
      · rintro ⟨hl, hm⟩
        exact ⟨head, hm head (Or.inl rfl), rest,
          (ih rest).mpr ⟨hl, fun a ha => hm a (Or.inr ha)⟩, rfl, rfl⟩

/-- Concrete finite enumeration of distinct generated outputs. Its semantics
are proved below against actual increasing-input physical histories. -/
def generatedOutputs (r s n : Nat) : List (List Nat) :=
  (unique (words (List.range n) n)).filter (fun output =>
    decide (output.Perm (List.range n)) && recognizes r s (encode 0 [] output))

theorem generatedOutputs_nodup (r s n : Nat) : (generatedOutputs r s n).Nodup :=
  (unique_nodup _).filter _

/-- Exact all-length output membership. The right side is the original
unrestricted physical machine, not an abstract recurrence or fitted sequence. -/
theorem mem_generatedOutputs_iff {r s n : Nat} (hr : 0 < r) (hs : 0 < s)
    (output : List Nat) :
    output ∈ generatedOutputs r s n ↔ Run r s [] (List.range n) output [] := by
  simp only [generatedOutputs, List.mem_filter, mem_unique, mem_words,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hp, accepted⟩
    exact (permutation_recognizes_iff hp hr hs).mp accepted
  · intro run
    have hp : output.Perm (List.range n) := by simpa using run.supply.symm
    refine ⟨⟨by simpa using hp.length_eq, fun a ha => hp.mem_iff.mp ha⟩,
      hp, (permutation_recognizes_iff hp hr hs).mpr run⟩

/-- Each element of the finite output list is one actual permutation. -/
def generatedCount (r s n : Nat) : Nat := (generatedOutputs r s n).length

/-- The actual unrestricted (3,3) ordinary counting series as coefficients.
The empty output appears exactly once, proved below. -/
def threeThreeCounts : Nat → Nat := generatedCount 3 3

def codeAlphabet (n : Nat) : List Letter :=
  ((List.range n).map (fun k => Letter.H (k+1))) ++
    ((List.range n).map (fun b => Letter.N (b+1)))

theorem held_mem_alphabet {n k : Nat} :
    Letter.H k ∈ codeAlphabet n ↔ 0 < k ∧ k ≤ n := by
  simp only [codeAlphabet, List.mem_append, List.mem_map, List.mem_range,
    Letter.H.injEq, reduceCtorEq, and_false, exists_false, or_false]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨hk, hn⟩
    exact ⟨k-1, by omega, by omega⟩

theorem record_mem_alphabet {n b : Nat} :
    Letter.N b ∈ codeAlphabet n ↔ 0 < b ∧ b ≤ n := by
  simp only [codeAlphabet, List.mem_append, List.mem_map, List.mem_range,
    Letter.N.injEq, reduceCtorEq, and_false, exists_false, false_or]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨hb, hn⟩
    exact ⟨b-1, by omega, by omega⟩

/-- The finite alphabet is only a per-size universe: every valid complete
code of a size-n permutation lies in it. It is not a fixed machine cutoff. -/
theorem bounded_alphabet {H h : Nat} {code : List Letter}
    (hb : Bounded H h code) (height : h ≤ H) :
    ∀ letter ∈ code, letter ∈ codeAlphabet H := by
  induction hb with
  | nil => simp
  | @held h k code positive valid tail ih =>
    intro letter hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact held_mem_alphabet.mpr ⟨positive, Nat.le_trans valid height⟩
    · exact ih (by omega) letter hm
  | @record h b code positive physical tail ih =>
    intro letter hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact record_mem_alphabet.mpr ⟨positive, by omega⟩
    · exact ih (by omega) letter hm

/-- Every actual permutation has its literal canonical code, even without a
machine membership hypothesis. The height bound n is automatic at size n. -/
theorem permutation_encoded {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    Decodes n 0 [] (encode 0 [] output) output ∧ Bounded n 0 (encode 0 [] output) := by
  have bound : ∀ pre a post, output = pre ++ a :: post → a+1 ≤ pre.length+n := by
    intro pre a post he
    have ha : a ∈ output := by simp [he]
    have hlt := List.mem_range.mp (hp.mem_iff.mp ha)
    omega
  obtain ⟨code, hd, hb, _⟩ := permutation_unique_bounded_code hp bound
  rw [hd.encode_eq (by simp [HeldInvariant])]
  exact ⟨hd, hb⟩

theorem encode_injective_permutations {n : Nat} {a b : List Nat}
    (ha : a.Perm (List.range n)) (hb : b.Perm (List.range n))
    (he : encode 0 [] a = encode 0 [] b) : a = b := by
  have hda := (permutation_encoded ha).1.decode_eq
  have hdb := (permutation_encoded hb).1.decode_eq
  rw [he, hdb] at hda
  exact (Prod.mk.inj (Option.some.inj hda)).2.symm

/-- Independent enumeration of accepted complete lazy codes. The candidates
are all length-n code words over the per-size alphabet, not encoded outputs. -/
def acceptedCodes (r s n : Nat) : List (List Letter) :=
  (unique (words (codeAlphabet n) n)).filter (fun code =>
    boundedCheck n 0 code && recognizes r s code)

theorem acceptedCodes_nodup (r s n : Nat) : (acceptedCodes r s n).Nodup :=
  (unique_nodup _).filter _

theorem mem_acceptedCodes_iff (r s n : Nat) (code : List Letter) :
    code ∈ acceptedCodes r s n ↔ code.length = n ∧
      Bounded n 0 code ∧ recognizes r s code = true := by
  simp only [acceptedCodes, List.mem_filter, mem_unique, mem_words,
    Bool.and_eq_true, boundedCheck_iff]
  constructor
  · rintro ⟨⟨hlen, _⟩, hb, ha⟩
    exact ⟨hlen, hb, ha⟩
  · rintro ⟨hlen, hb, ha⟩
    exact ⟨⟨hlen, bounded_alphabet hb (by omega)⟩, hb, ha⟩

/-- The canonical output encoder and literal decoder give an all-length
bijection between actual distinct outputs and independent accepted codes. -/
theorem encoded_outputs_perm_accepted {r s : Nat} (hr : 0 < r) (hs : 0 < s) (n : Nat) :
    ((generatedOutputs r s n).map (encode 0 [])).Perm (acceptedCodes r s n) := by
  have mappedNodup : ((generatedOutputs r s n).map (encode 0 [])).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := generatedOutputs_nodup r s n)
    intro a b ha hb hne he
    have hpa : a.Perm (List.range n) := by
      have run := (mem_generatedOutputs_iff hr hs a).mp ha
      simpa using run.supply.symm
    have hpb : b.Perm (List.range n) := by
      have run := (mem_generatedOutputs_iff hr hs b).mp hb
      simpa using run.supply.symm
    exact hne (encode_injective_permutations hpa hpb he)
  apply (List.perm_ext_iff_of_nodup mappedNodup (acceptedCodes_nodup r s n)).mpr
  intro code
  constructor
  · rintro hm
    obtain ⟨output, ho, rfl⟩ := List.mem_map.mp hm
    have run := (mem_generatedOutputs_iff hr hs output).mp ho
    have hp : output.Perm (List.range n) := by simpa using run.supply.symm
    obtain ⟨hd, hb⟩ := permutation_encoded hp
    apply (mem_acceptedCodes_iff r s n _).mpr
    exact ⟨by simpa using hd.length.trans hp.length_eq, hb, (hd.recognizes_iff hr hs).mpr run⟩
  · intro hm
    obtain ⟨hlen, hb, accepted⟩ := (mem_acceptedCodes_iff r s n code).mp hm
    obtain ⟨output, hd, hp, _⟩ := bounded_word_permutation hb
    rw [hlen] at hd hp
    have run := (hd.recognizes_iff hr hs).mp accepted
    exact List.mem_map.mpr ⟨output, (mem_generatedOutputs_iff hr hs output).mpr run,
      hd.encode_eq (by simp [HeldInvariant])⟩

/-- Equality of actual distinct-permutation counts and accepted-code counts
for every input size. This does not yet identify either with the scalar Q root. -/
theorem generatedCount_eq_acceptedCodes {r s : Nat} (hr : 0 < r) (hs : 0 < s) (n : Nat) :
    generatedCount r s n = (acceptedCodes r s n).length := by
  have h := (encoded_outputs_perm_accepted hr hs n).length_eq
  simpa [generatedCount] using h

theorem threeThreeCounts_eq_acceptedCodes (n : Nat) :
    threeThreeCounts n = (acceptedCodes 3 3 n).length :=
  generatedCount_eq_acceptedCodes (by decide) (by decide) n

theorem threeThreeCounts_zero : threeThreeCounts 0 = 1 := by decide +kernel

#print axioms mem_generatedOutputs_iff
#print axioms encode_injective_permutations
#print axioms encoded_outputs_perm_accepted
#print axioms generatedCount_eq_acceptedCodes
#print axioms threeThreeCounts_eq_acceptedCodes
#print axioms threeThreeCounts_zero
end ActualCounting
end StackSorting.Generalized
