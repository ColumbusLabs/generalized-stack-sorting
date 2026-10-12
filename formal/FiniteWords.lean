import OperationWords

/-! # Local finiteness of the exact operation-word language -/
namespace StackSorting.Labelled

theorem word_step_size (op : Op) (s t : WState)
    (h : wordStep op s = some t) :
    1 + t.1.length ≤ 2 * opWeight op + s.1.length := by
  rcases s with ⟨w, flag⟩
  cases op <;> cases w with
  | nil =>
    simp [wordStep] at h
    all_goals subst t
    all_goals simp [opWeight]
  | cons a rest =>
    cases a <;> cases rest <;> cases flag <;> simp [wordStep] at h
    all_goals subst t
    all_goals (simp [opWeight] <;> omega)

theorem word_run_size (ops : List Op) (s t : WState)
    (h : wordRun ops s = some t) :
    ops.length + t.1.length ≤ 2 * weight ops + s.1.length := by
  induction ops generalizing s t with
  | nil => simp [wordRun] at h; subst t; simp [weight]
  | cons op ops ih =>
    cases hs : wordStep op s with
    | none => simp [wordRun, hs] at h
    | some u =>
      simp [wordRun, hs] at h
      have hf := word_step_size op s u hs
      have ht := ih u t h
      simp only [List.length_cons, weight]
      omega

/-- At fixed input size n, every complete operation word has length at most 2n.
In particular zero-input-weight pops do not create infinitely many histories. -/
theorem accepted_length_bound (n : Nat) (ops : List Op) (h : AcceptedWord n ops) :
    ops.length ≤ 2 * n := by
  obtain ⟨⟨c, hc⟩, hw⟩ := h
  have hp := project_run ops (Forest.nil, true)
  have hr : wordRun ops ([], true) = some ([], c) := by
    simpa [hc, project, word] using hp.symm
  have hs := word_run_size ops ([], true) ([], c) hr
  simpa [hw] using hs

def alphabet : List Op := [.bypass, .push0, .push1, .pop0, .pop1]

def allWords : Nat → List (List Op)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun op => (allWords n).map (op :: ·))

theorem mem_alphabet (op : Op) : op ∈ alphabet := by
  cases op <;> simp [alphabet]

theorem allWords_complete (n : Nat) (ops : List Op) (h : ops.length ≤ n) :
    ops ∈ allWords n := by
  induction n generalizing ops with
  | zero =>
    have he : ops = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ops
    simp [allWords]
  | succ n ih =>
    cases ops with
    | nil => simp [allWords]
    | cons op ops =>
      have ht : ops.length ≤ n := by simp at h; omega
      apply List.mem_cons_of_mem []
      apply List.mem_flatMap.mpr
      exact ⟨op, mem_alphabet op, List.mem_map.mpr ⟨ops, ih ops ht, rfl⟩⟩

theorem allWords_sound (n : Nat) (ops : List Op) (h : ops ∈ allWords n) :
    ops.length ≤ n := by
  induction n generalizing ops with
  | zero => simp [allWords] at h; subst ops; simp
  | succ n ih =>
    rcases List.mem_cons.mp h with he | hm
    · subst ops; simp
    · obtain ⟨op, _, hw⟩ := List.mem_flatMap.mp hm
      obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp hw
      have hl := ih tail ht
      simp
      omega

/-- A finite, explicit covering list for every size-n accepted language. -/
theorem accepted_enumerated (n : Nat) (ops : List Op) (h : AcceptedWord n ops) :
    ops ∈ allWords (2 * n) :=
  allWords_complete (2 * n) ops (accepted_length_bound n ops h)

instance decidableAcceptedWord (n : Nat) (ops : List Op) : Decidable (AcceptedWord n ops) := by
  unfold AcceptedWord
  infer_instance

/-- An explicit finite enumeration, with repetitions removed rather than counted. -/
def acceptedWords (n : Nat) : List (List Op) :=
  ((allWords (2 * n)).filter (fun ops => decide (AcceptedWord n ops))).eraseDups

theorem mem_acceptedWords (n : Nat) (ops : List Op) :
    ops ∈ acceptedWords n ↔ AcceptedWord n ops := by
  simp only [acceptedWords, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun h => ⟨accepted_enumerated n ops h, h⟩⟩

theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · intro hm
      have hf := List.mem_filter.mp (List.mem_eraseDups.mp hm)
      simp at hf
    · exact eraseDups_nodup _
termination_by xs.length
decreasing_by
  have hl := List.length_filter_le (fun b => !b == a) xs
  simp
  omega

theorem acceptedWords_nodup (n : Nat) : (acceptedWords n).Nodup :=
  eraseDups_nodup _

/-- This list enumerates each sortable permutation of size n exactly once. -/
def sortableInputs (n : Nat) : List (List Nat) := (acceptedWords n).map decode

theorem mem_sortableInputs (n : Nat) (input : List Nat) :
    input ∈ sortableInputs n ↔ CanSort [] input (List.range' 1 n) := by
  constructor
  · intro hm
    obtain ⟨ops, hop, rfl⟩ := List.mem_map.mp hm
    exact decode_sound n ops ((mem_acceptedWords n ops).mp hop)
  · intro hs
    obtain ⟨ops, ha, he⟩ := decode_surjective n input hs
    exact List.mem_map.mpr ⟨ops, (mem_acceptedWords n ops).mpr ha, he⟩

theorem sortableInputs_nodup (n : Nat) : (sortableInputs n).Nodup := by
  apply List.pairwise_map.mpr
  apply (acceptedWords_nodup n).imp_of_mem
  intro as bs ha hb hne heq
  exact hne (decode_injective n as bs ((mem_acceptedWords n as).mp ha)
    ((mem_acceptedWords n bs).mp hb) heq)

/-- Finite cardinality equality for two proved duplicate-free enumerations. -/
theorem sortable_count_eq_word_count (n : Nat) :
    (sortableInputs n).length = (acceptedWords n).length := by
  simp [sortableInputs]

#print axioms accepted_length_bound
#print axioms accepted_enumerated
#print axioms mem_sortableInputs
#print axioms sortableInputs_nodup
#print axioms sortable_count_eq_word_count

end StackSorting.Labelled
