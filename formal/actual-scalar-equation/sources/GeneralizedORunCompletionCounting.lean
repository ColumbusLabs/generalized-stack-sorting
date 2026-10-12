import GeneralizedCoordinateRelabel
import GeneralizedCompletionCounting

/-! A single literal Z O^q block may be replaced by Z^(q+1) when counting
actual distinct decorated completions. This is the exact one-block transport
needed for the O-run introduced by deletion from a unary Z/B/T state. There
is no theorem erasing an arbitrary isolated O, nor any assumed count equality.
-/
namespace StackSorting.Generalized.Decorated
namespace ORunCount
open Coordinates Coordinates.ORun

/-- The only block changed by the reduction, with its leading Z retained. -/
def source (pre suffix : State) (q : Nat) : State :=
  pre ++ (.Z :: List.replicate q .O) ++ suffix

def target (pre suffix : State) (q : Nat) : State :=
  pre ++ List.replicate (q+1) .Z ++ suffix

theorem denotes_ones (q : Nat) (digits : List Nat) :
    denotes (List.replicate q .O) digits ↔ digits = List.replicate q 1 := by
  induction q generalizing digits with
  | zero => simp [denotes]
  | succ q ih => simp [List.replicate_succ, denotes, Factor.denotes, ih]

theorem denotes_source_block (q : Nat) (digits : List Nat) :
    denotes (.Z :: List.replicate q .O) digits ↔ digits = 0 :: List.replicate q 1 := by
  simp [denotes, Factor.denotes, denotes_ones]

theorem denotes_zeros (q : Nat) (digits : List Nat) :
    denotes (List.replicate q .Z) digits ↔ digits = List.replicate q 0 := by
  induction q generalizing digits with
  | zero => simp [denotes]
  | succ q ih => simp [List.replicate_succ, denotes, Factor.denotes, ih]

theorem denotes_target_block (q : Nat) (digits : List Nat) :
    denotes (List.replicate (q+1) .Z) digits ↔ digits = List.replicate (q+1) 0 :=
  denotes_zeros (q+1) digits

/-- Both states hold exactly the same number of labels. Prefix and suffix
lengths are their actual denoted coordinate lengths, including clause factors. -/
theorem source_height (pre suffix : State) (q : Nat) :
    height (source pre suffix q) = height pre+1+q+height suffix := by
  simp [source, height, Factor.height, List.sum_append, List.sum_replicate_nat]
  omega

theorem target_height (pre suffix : State) (q : Nat) :
    height (target pre suffix q) = height pre+1+q+height suffix := by
  simp [target, height, Factor.height, List.sum_append, List.sum_replicate_nat]
  omega

/-- Match the decorated physical language with the exact independently
reviewed coordinate-family language, without a recognition or closure premise. -/
theorem represents_fixed_block (pre block suffix : State) (word physical : List Nat)
    (fixed : ∀ digits, denotes block digits ↔ digits = word) :
    Represents (pre ++ block ++ suffix) physical ↔
      Initial (height pre+1) word (PrefixOrders (height pre+1) (denotes pre))
        (fun digits => denotes suffix digits ∧ digits.length = height suffix) physical := by
  constructor
  · rintro ⟨digits, hd, hp⟩
    rw [List.append_assoc] at hd
    obtain ⟨earlier, tail, he, ht, rfl⟩ := (denotes_append pre (block ++ suffix) digits).mp hd
    obtain ⟨middle, later, hm, hl, rfl⟩ := (denotes_append block suffix tail).mp ht
    have hmiddle := (fixed middle).mp hm
    subst middle
    have hlen := denotes_length he
    unfold Coordinates.Decodes at hp
    rw [build_append] at hp
    cases hb : build 1 earlier [] with
    | none => simp [hb] at hp
    | some old =>
      refine ⟨old, later, ⟨earlier, he, by omega, hb⟩, ⟨hl, denotes_length hl⟩, ?_⟩
      simpa [hb, hlen, Nat.add_comm] using hp
  · rintro ⟨old, later, ⟨earlier, he, hlen, hb⟩, ⟨hl, _⟩, hp⟩
    refine ⟨earlier ++ word ++ later, ?_, ?_⟩
    · rw [List.append_assoc, List.append_assoc]
      exact (denotes_append pre (block ++ suffix) _).mpr
        ⟨earlier, word ++ later, he,
          (denotes_append block suffix _).mpr ⟨word, later, (fixed word).mpr rfl, hl, rfl⟩, rfl⟩
    · unfold Coordinates.Decodes
      rw [List.append_assoc, build_append, hb]
      have hnext : 1+earlier.length = height pre+1 := by omega
      simpa [hnext] using hp

/-- Exact matching of all literal completion outputs, with future input
beginning at the first unused label of the entire decorated state. -/
theorem completion_fixed_block (pre block suffix : State) (word output : List Nat) (n : Nat)
    (fixed : ∀ digits, denotes block digits ↔ digits = word) :
    Completion (pre ++ block ++ suffix) n output ↔
      Feasible (height pre+1) word (PrefixOrders (height pre+1) (denotes pre))
        (fun digits => denotes suffix digits ∧ digits.length = height suffix)
        (height (pre ++ block ++ suffix)+1) n output := by
  unfold Completion Feasible
  exact exists_congr fun physical =>
    and_congr (represents_fixed_block pre block suffix word physical fixed) Iff.rfl

theorem source_completion (pre suffix : State) (q n : Nat) (output : List Nat) :
    Completion (source pre suffix q) n output ↔
      Feasible (height pre+1) (0 :: List.replicate q 1)
        (PrefixOrders (height pre+1) (denotes pre))
        (fun digits => denotes suffix digits ∧ digits.length = height suffix)
        (height pre+1+q+height suffix+1) n output := by
  have h := completion_fixed_block pre (.Z :: List.replicate q .O) suffix
    (0 :: List.replicate q 1) output n (denotes_source_block q)
  change Completion (source pre suffix q) n output ↔
    Feasible (height pre+1) (0 :: List.replicate q 1)
      (PrefixOrders (height pre+1) (denotes pre))
      (fun digits => denotes suffix digits ∧ digits.length = height suffix)
      (height (source pre suffix q)+1) n output at h
  rw [source_height] at h
  exact h

theorem target_completion (pre suffix : State) (q n : Nat) (output : List Nat) :
    Completion (target pre suffix q) n output ↔
      Feasible (height pre+1) (List.replicate (q+1) 0)
        (PrefixOrders (height pre+1) (denotes pre))
        (fun digits => denotes suffix digits ∧ digits.length = height suffix)
        (height pre+1+q+height suffix+1) n output := by
  have h := completion_fixed_block pre (List.replicate (q+1) .Z) suffix
    (List.replicate (q+1) 0) output n (denotes_target_block q)
  change Completion (target pre suffix q) n output ↔
    Feasible (height pre+1) (List.replicate (q+1) 0)
      (PrefixOrders (height pre+1) (denotes pre))
      (fun digits => denotes suffix digits ∧ digits.length = height suffix)
      (height (target pre suffix q)+1) n output at h
  rw [target_height] at h
  exact h

/-- The already reviewed explicit bijection applied to the exact decorated
languages. This object counts only output lists, never physical witnesses. -/
def completionBijection (pre suffix : State) (q n : Nat) :
    OutputBijection
      {output // Completion (source pre suffix q) n output}
      {output // Completion (target pre suffix q) n output} where
  forward output := ⟨(coordinateOutputBijection (height pre+1) q (height suffix) n
    (denotes pre) (denotes suffix)).forward
      ⟨output.val, (source_completion pre suffix q n output.val).mp output.property⟩,
      (target_completion pre suffix q n _).mpr
        ((coordinateOutputBijection (height pre+1) q (height suffix) n
          (denotes pre) (denotes suffix)).forward
          ⟨output.val, (source_completion pre suffix q n output.val).mp output.property⟩).property⟩
  backward output := ⟨(coordinateOutputBijection (height pre+1) q (height suffix) n
    (denotes pre) (denotes suffix)).backward
      ⟨output.val, (target_completion pre suffix q n output.val).mp output.property⟩,
      (source_completion pre suffix q n _).mpr
        ((coordinateOutputBijection (height pre+1) q (height suffix) n
          (denotes pre) (denotes suffix)).backward
          ⟨output.val, (target_completion pre suffix q n output.val).mp output.property⟩).property⟩
  left_inverse output := by apply Subtype.ext; exact map_rhoInv_rho (height pre+1) q output.val
  right_inverse output := by apply Subtype.ext; exact map_rho_rhoInv (height pre+1) q output.val

/-- The finite, duplicate-free list of actual source outputs is carried
permutationally to the target list by the reviewed fixed label cycle. -/
theorem completionOutputs_perm (pre suffix : State) (q n : Nat) :
    ((completionOutputs (source pre suffix q) n).map
      (List.map (rho (height pre+1) q))).Perm
        (completionOutputs (target pre suffix q) n) := by
  have hn : ((completionOutputs (source pre suffix q) n).map
      (List.map (rho (height pre+1) q))).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := completionOutputs_nodup (source pre suffix q) n)
    intro a b _ _ hne he
    apply hne
    have hi := congrArg (List.map (rhoInv (height pre+1) q)) he
    simpa only [map_rhoInv_rho] using hi
  apply (List.perm_ext_iff_of_nodup hn
    (completionOutputs_nodup (target pre suffix q) n)).mpr
  intro output
  constructor
  · intro hm
    obtain ⟨before, hb, rfl⟩ := List.mem_map.mp hm
    have hc := (mem_completionOutputs (source pre suffix q) n before).mp hb
    exact (mem_completionOutputs (target pre suffix q) n _).mpr
      ((completionBijection pre suffix q n).forward ⟨before, hc⟩).property
  · intro hm
    have hc := (mem_completionOutputs (target pre suffix q) n output).mp hm
    let back := (completionBijection pre suffix q n).backward ⟨output, hc⟩
    refine List.mem_map.mpr ⟨back.val,
      (mem_completionOutputs (source pre suffix q) n back.val).mpr back.property, ?_⟩
    exact map_rho_rhoInv (height pre+1) q output

/-- Ambient validity is preserved by the same literal decoder identity.
This lets a valid unary-deletion successor return to the O-free induction
domain after its single anchored O-run is replaced. -/
theorem valid_source_target (pre suffix : State) (q : Nat)
    (valid : Valid (source pre suffix q)) : Valid (target pre suffix q) := by
  intro digits hd
  change denotes (pre ++ List.replicate (q+1) .Z ++ suffix) digits at hd
  rw [List.append_assoc] at hd
  obtain ⟨earlier, tail, he, ht, rfl⟩ :=
    (denotes_append pre (List.replicate (q+1) .Z ++ suffix) digits).mp hd
  obtain ⟨middle, later, hm, hl, rfl⟩ :=
    (denotes_append (List.replicate (q+1) .Z) suffix tail).mp ht
  have hmiddle := (denotes_target_block q middle).mp hm
  subst middle
  have hs : denotes (source pre suffix q)
      (earlier ++ (0 :: List.replicate q 1) ++ later) := by
    unfold source
    rw [List.append_assoc, List.append_assoc]
    exact (denotes_append pre ((.Z :: List.replicate q .O) ++ suffix) _).mpr
      ⟨earlier, (0 :: List.replicate q 1) ++ later, he,
        (denotes_append (.Z :: List.replicate q .O) suffix _).mpr
          ⟨0 :: List.replicate q 1, later, (denotes_source_block q _).mpr rfl, hl, rfl⟩, rfl⟩
  obtain ⟨physical, hp⟩ := valid _ hs
  have hi := whole_word_identity earlier later q
  unfold Coordinates.Decodes at hp
  rw [hp] at hi
  refine ⟨physical.map (rho (earlier.length+1) q), ?_⟩
  simpa only [Coordinates.Decodes, List.append_assoc, Option.map_some] using hi.symm

/-- Actual finite cardinality equality for the single anchored O-run,
for every prefix, suffix, run length, and future input length. -/
theorem completionCount_eq (pre suffix : State) (q n : Nat) :
    completionCount (pre ++ (.Z :: List.replicate q .O) ++ suffix) n =
      completionCount (pre ++ List.replicate (q+1) .Z ++ suffix) n := by
  have hl := (completionOutputs_perm pre suffix q n).length_eq
  simpa only [List.length_map, completionCount, source, target] using hl

#print axioms represents_fixed_block
#print axioms source_completion
#print axioms target_completion
#print axioms completionBijection
#print axioms completionOutputs_perm
#print axioms valid_source_target
#print axioms completionCount_eq
end ORunCount
end StackSorting.Generalized.Decorated
