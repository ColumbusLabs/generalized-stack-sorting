import RawWiring

/-! # Size-preserving decoder from accepted operation words to sortable inputs -/
namespace StackSorting.Labelled

def opWeight : Op → Nat
  | .bypass | .push0 | .push1 => 1
  | .pop0 | .pop1 => 0

def weight : List Op → Nat
  | [] => 0
  | op :: ops => opWeight op + weight ops

def nameActions : List Op → Nat → List Action
  | [], _ => []
  | .bypass :: ops, a => .bypass a :: nameActions ops (a + 1)
  | .push0 :: ops, a => .push0 a :: nameActions ops (a + 1)
  | .push1 :: ops, a => .push1 a :: nameActions ops (a + 1)
  | .pop0 :: ops, a => .pop0 :: nameActions ops a
  | .pop1 :: ops, a => .pop1 :: nameActions ops a

theorem erase_named (ops : List Op) (a : Nat) :
    (nameActions ops a).map eraseAction = ops := by
  induction ops generalizing a with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [nameActions, eraseAction, ih]

theorem inputs_named (ops : List Op) (a : Nat) :
    inputs (nameActions ops a) = List.range' a (weight ops) := by
  induction ops generalizing a with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | bypass =>
      change a :: inputs (nameActions ops (a + 1)) = List.range' a (1 + weight ops)
      rw [ih, Nat.add_comm 1 (weight ops), List.range'_succ]
    | push0 =>
      change a :: inputs (nameActions ops (a + 1)) = List.range' a (1 + weight ops)
      rw [ih, Nat.add_comm 1 (weight ops), List.range'_succ]
    | push1 =>
      change a :: inputs (nameActions ops (a + 1)) = List.range' a (1 + weight ops)
      rw [ih, Nat.add_comm 1 (weight ops), List.range'_succ]
    | pop0 => simpa [nameActions, inputs, introduced, weight, opWeight] using ih a
    | pop1 => simpa [nameActions, inputs, introduced, weight, opWeight] using ih a

theorem named_nodup (ops : List Op) (a : Nat) : (inputs (nameActions ops a)).Nodup := by
  rw [inputs_named]
  exact List.nodup_range'

theorem weight_erased (acts : List Action) : weight (acts.map eraseAction) = (inputs acts).length := by
  induction acts with
  | nil => rfl
  | cons act acts ih =>
    cases act <;> simp [eraseAction, weight, opWeight, inputs, introduced, ih, Nat.add_comm] at ih ⊢
    all_goals exact ih

def AcceptedWord (n : Nat) (ops : List Op) : Prop :=
  (∃ c, forestRun ops (Forest.nil, true) = some (Forest.nil, c)) ∧ weight ops = n

def decode (ops : List Op) : List Nat :=
  match tokenRun (nameActions ops 0) (TForest.nil, true) with
  | none => []
  | some (_, out) => inputs ((nameActions ops 0).map (relabelAction (outputRank out)))

theorem named_complete (n : Nat) (ops : List Op) (h : AcceptedWord n ops) :
    ∃ c out, tokenRun (nameActions ops 0) (TForest.nil, true) =
      some ((TForest.nil, c), out) ∧ out.length = n := by
  obtain ⟨⟨c, hc⟩, hw⟩ := h
  have he : forestRun ((nameActions ops 0).map eraseAction)
      (eraseState (TForest.nil, true)) = some (Forest.nil, c) := by
    simpa [erase_named, eraseState, erase] using hc
  obtain ⟨⟨f, b⟩, out, hr, hs⟩ := lift_run (nameActions ops 0) (TForest.nil, true) (Forest.nil, c) he
  have hf : f = TForest.nil := by
    have hf' := congrArg Prod.fst hs
    cases f with
    | nil => rfl
    | cons a d r => simp [eraseState, erase] at hf'
  subst f
  refine ⟨b, out, hr, ?_⟩
  have hl := (complete_permutation (nameActions ops 0) true b out hr).length_eq
  simpa [inputs_named, hw] using hl.symm

/-- The decoder is witnessed by a trace with the same operation labels and
exact increasing output. -/
theorem decoded_trace (n : Nat) (ops : List Op) (h : AcceptedWord n ops) :
    ∃ acts c, acts.map eraseAction = ops ∧
      tokenRun acts (TForest.nil, true) = some ((TForest.nil, c), List.range' 1 n) ∧
      inputs acts = decode ops := by
  obtain ⟨c, out, hr, hlen⟩ := named_complete n ops h
  let acts := (nameActions ops 0).map (relabelAction (outputRank out))
  have hn := complete_nodup (nameActions ops 0) true c out hr (named_nodup ops 0)
  have hrun := relabel_run (outputRank out) (nameActions ops 0) (TForest.nil, true)
  simp [hr, relabelState, relabelResult, relabel, map_outputRank out hn, hlen] at hrun
  refine ⟨acts, c, ?_, hrun, ?_⟩
  · simp [acts, List.map_map, Function.comp_def, erase_relabel_action, erase_named]
  · simp [decode, hr, acts]

theorem decode_sound (n : Nat) (ops : List Op) (h : AcceptedWord n ops) :
    CanSort [] (decode ops) (List.range' 1 n) := by
  obtain ⟨acts, c, _, hr, hi⟩ := decoded_trace n ops h
  exact (original_iff_forest (decode ops) n).mpr ⟨acts, c, hr, hi⟩

theorem decode_injective (n : Nat) (as bs : List Op)
    (ha : AcceptedWord n as) (hb : AcceptedWord n bs) (he : decode as = decode bs) : as = bs := by
  obtain ⟨acts, c, hka, hra, hia⟩ := decoded_trace n as ha
  obtain ⟨acts', d, hkb, hrb, hib⟩ := decoded_trace n bs hb
  have hin : inputs acts = inputs acts' := hia.trans (he.trans hib.symm)
  have ht := complete_trace_unique acts acts' (TForest.nil, true) c d _ hra hrb hin List.pairwise_lt_range'
  exact hka.symm.trans ((congrArg (List.map eraseAction) ht).trans hkb)

theorem decode_surjective (n : Nat) (input : List Nat)
    (h : CanSort [] input (List.range' 1 n)) :
    ∃ ops, AcceptedWord n ops ∧ decode ops = input := by
  obtain ⟨acts, c, hr, hi⟩ := sortable_has_forest input n h
  let ops := acts.map eraseAction
  have haccept : AcceptedWord n ops := by
    constructor
    · refine ⟨c, ?_⟩
      have he := erase_run acts (TForest.nil, true)
      simpa [ops, hr, eraseState, erase] using he.symm
    · have hlen := (canSort_supply [] input (List.range' 1 n) h).length_eq
      simpa [ops, weight_erased, hi] using hlen
  obtain ⟨acts', d, hkind, hr', hi'⟩ := decoded_trace n ops haccept
  have heinput := forest_wiring_unique acts' acts true d c (List.range' 1 n) hr' hr hkind
  exact ⟨ops, haccept, hi'.symm.trans (heinput.trans hi)⟩

#print axioms decode_sound
#print axioms decode_injective
#print axioms decode_surjective

end StackSorting.Labelled
