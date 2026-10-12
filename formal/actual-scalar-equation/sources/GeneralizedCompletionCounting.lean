import GeneralizedCompletionCodes

/-! Actual completion-output cardinalities and their exact canonical-code
cardinalities. All initial physical orders and realizing histories remain
existential. The finite candidate universes depend on the complete supply,
not on an imposed machine capacity or enumeration cutoff. -/
namespace StackSorting.Generalized
namespace Decorated
open LazyCode ActualCounting

theorem initial_held_invariant (h : Nat) : HeldInvariant (h+1) (List.range' 1 h) := by
  refine ⟨List.pairwise_lt_range', ?_⟩
  intro token ht
  have hm := List.mem_range'.mp ht
  omega

theorem normalize_initial_ranks {h : Nat} {physical : List Nat}
    (hp : physical.Perm (List.range' 1 h)) : normalize (List.range' 1 h) physical = physical := by
  have hs : (List.range' 1 h).map (valueRank (List.range' 1 h)) = List.range' 1 h := by
    simpa [normalize] using normalize_self (List.nodup_range' (s := 1) (n := h))
  have hf : ∀ token ∈ List.range' 1 h, valueRank (List.range' 1 h) token = token := by
    apply List.map_eq_map_iff.mp
    simpa using hs
  calc
    normalize (List.range' 1 h) physical = physical.map (fun token => token) := by
      apply List.map_congr_left
      exact fun token ht => hf token (hp.mem_iff.mp ht)
    _ = physical := by simp

theorem initial_range_append (h n : Nat) :
    List.range' 1 h ++ List.range' (h+1) n = List.range' 1 (h+n) := by
  simpa only [Nat.add_comm 1 h] using (List.range'_append_1 (s := 1) (m := h) (n := n))

theorem initial_supply_nodup {h n : Nat} {physical : List Nat}
    (hp : physical.Perm (List.range' 1 h)) :
    (physical ++ List.range' (h+1) n).Nodup := by
  have hfull : (physical ++ List.range' (h+1) n).Perm (List.range' 1 (h+n)) := by
    rw [← initial_range_append h n]
    exact hp.append_right (List.range' (h+1) n)
  exact hfull.nodup_iff.mpr List.nodup_range'

/-- Exact complete rank-code semantics with an arbitrary represented initial
physical order, derived from the existing literal decoding and lazy-run proofs. -/
theorem complete_rankCode_iff {h n : Nat} {physical output : List Nat} {code : List Letter}
    (hd : Decodes (h+n+1) (h+1) (List.range' 1 h) code output)
    (hp : physical.Perm (List.range' 1 h)) :
    [] ∈ rankCodeOrders 3 3 h code physical ↔
      Run 3 3 physical (List.range' (h+1) n) output [] := by
  have rank := hd.rankCodeOrders_iff (r := 3) (s := 3) (initial_held_invariant h) hp
  have hnorm := normalize_initial_ranks hp
  simp only [List.length_range', hnorm] at rank
  rw [rank, hd.codeOrders_iff_rangeLazy (by decide) (by decide) (initial_held_invariant h) hp]
  constructor
  · intro hr
    have hn : h+n+1-(h+1) = n := by omega
    simpa [hn] using hr.history
  · intro hr
    have hl := hr.rangeLazy (initial_supply_nodup hp)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hl

/-- Every actual completion has its literal unique code from the existing
old-label dictionary. No physical recognition or counting theorem is assumed. -/
theorem Completion.decodes {state : State} {n : Nat} {output : List Nat}
    (hc : Completion state n output) :
    ∃ code, Decodes (height state+n+1) (height state+1)
      (List.range' 1 (height state)) code output := by
  have hp := hc.permutation
  have supplied : output.Perm (List.range' 1 (height state) ++
      List.range' (height state+1) ((height state+n+1)-(height state+1))) := by
    have hn : (height state+n+1)-(height state+1) = n := by omega
    rw [hn, initial_range_append]
    exact hp
  have bound : ∀ pre a post, output = pre ++ a :: post →
      a+1 ≤ 1+pre.length+(height state+n+1) := by
    intro pre a post he
    have ha : a ∈ output := by simp [he]
    have hr := List.mem_range'.mp (hp.mem_iff.mp ha)
    omega
  obtain ⟨code, hd, _⟩ := exists_bounded_code (consumed := 1)
    supplied (by omega) (initial_held_invariant (height state)) (by simp only [List.length_range']; omega) bound
  exact ⟨code, hd⟩

/-- The exact state code language is in bijection with its actual admitted
outputs. These witnesses describe outputs, never histories. -/
theorem CodeCompletion.decodes {state : State} {n : Nat} {code : List Letter}
    (hc : CodeCompletion state n code) :
    ∃ output, Decodes (height state+n+1) (height state+1)
      (List.range' 1 (height state)) code output ∧ Completion state n output := by
  obtain ⟨output, hd⟩ := hc.1.decodes (held := List.range' 1 (height state))
    (next := height state+1) (by simp) (initial_held_invariant _)
  have hd' : Decodes (height state+n+1) (height state+1)
      (List.range' 1 (height state)) code output := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd
  obtain ⟨physical, hp, ha⟩ := hc.2
  exact ⟨output, hd', physical, hp, (complete_rankCode_iff hd' hp.permutation).mp ha⟩

def stateEncode (state : State) (output : List Nat) : List Letter :=
  encode (height state+1) (List.range' 1 (height state)) output

theorem Completion.encoded {state : State} {n : Nat} {output : List Nat}
    (hc : Completion state n output) :
    Decodes (height state+n+1) (height state+1) (List.range' 1 (height state))
      (stateEncode state output) output ∧ CodeCompletion state n (stateEncode state output) := by
  obtain ⟨code, hd⟩ := hc.decodes
  have he : stateEncode state output = code := hd.encode_eq (initial_held_invariant _)
  rw [he]
  have hb : Budget (height state) n code := by
    have hn : height state+n+1-(height state+1) = n := by omega
    simpa [hn] using hd.budget
  obtain ⟨physical, hp, hr⟩ := hc
  exact ⟨hd, hb, physical, hp, (complete_rankCode_iff hd hp.permutation).mpr hr⟩

theorem stateEncode_injective {state : State} {n : Nat} {a b : List Nat}
    (ha : Completion state n a) (hb : Completion state n b)
    (he : stateEncode state a = stateEncode state b) : a = b := by
  have hda := ha.encoded.1.decode_eq
  have hdb := hb.encoded.1.decode_eq
  rw [he, hdb] at hda
  exact (Prod.mk.inj (Option.some.inj hda)).2.symm

noncomputable def completionOutputs (state : State) (n : Nat) : List (List Nat) := by
  classical
  exact (unique (words (List.range' 1 (height state+n)) (height state+n))).filter
    (fun output => decide (Completion state n output))

noncomputable def completionCodes (state : State) (n : Nat) : List (List Letter) := by
  classical
  exact (unique (words (codeAlphabet (height state+n)) (height state+n))).filter
    (fun code => decide (CodeCompletion state n code))

noncomputable def completionCount (state : State) (n : Nat) : Nat :=
  (completionOutputs state n).length

theorem mem_completionOutputs (state : State) (n : Nat) (output : List Nat) :
    output ∈ completionOutputs state n ↔ Completion state n output := by
  classical
  simp only [completionOutputs, List.mem_filter, mem_unique, mem_words, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro hc
    have hp := hc.permutation
    exact ⟨⟨by simpa using hp.length_eq, fun a ha => hp.mem_iff.mp ha⟩, hc⟩

theorem mem_completionCodes (state : State) (n : Nat) (code : List Letter) :
    code ∈ completionCodes state n ↔ CodeCompletion state n code := by
  classical
  simp only [completionCodes, List.mem_filter, mem_unique, mem_words, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro hc
    exact ⟨⟨hc.1.length, bounded_alphabet (hc.1.bounded (Nat.le_refl _)) (by omega)⟩, hc⟩

theorem completionOutputs_nodup (state : State) (n : Nat) : (completionOutputs state n).Nodup := by
  classical
  exact (unique_nodup _).filter _

theorem completionCodes_nodup (state : State) (n : Nat) : (completionCodes state n).Nodup := by
  classical
  exact (unique_nodup _).filter _

/-- Distinct outputs and independently bounded canonical codes have equal
finite cardinality for every initial factor state and every future supply. -/
theorem completion_encoded_perm (state : State) (n : Nat) :
    ((completionOutputs state n).map (stateEncode state)).Perm (completionCodes state n) := by
  have hn : ((completionOutputs state n).map (stateEncode state)).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := completionOutputs_nodup state n)
    intro a b ha hb hne he
    exact hne (stateEncode_injective ((mem_completionOutputs state n a).mp ha)
      ((mem_completionOutputs state n b).mp hb) he)
  apply (List.perm_ext_iff_of_nodup hn (completionCodes_nodup state n)).mpr
  intro code
  constructor
  · rintro hm
    obtain ⟨output, ho, rfl⟩ := List.mem_map.mp hm
    exact (mem_completionCodes state n _).mpr ((mem_completionOutputs state n output).mp ho).encoded.2
  · intro hm
    have hc := (mem_completionCodes state n code).mp hm
    obtain ⟨output, hd, ho⟩ := hc.decodes
    exact List.mem_map.mpr ⟨output, (mem_completionOutputs state n output).mpr ho,
      hd.encode_eq (initial_held_invariant _)⟩

theorem completionCount_eq_codes (state : State) (n : Nat) :
    completionCount state n = (completionCodes state n).length := by
  have hl := (completion_encoded_perm state n).length_eq
  simpa [completionCount] using hl

end Decorated
#print axioms Decorated.complete_rankCode_iff
#print axioms Decorated.Completion.encoded
#print axioms Decorated.CodeCompletion.decodes
#print axioms Decorated.completion_encoded_perm
#print axioms Decorated.completionCount_eq_codes
end StackSorting.Generalized
