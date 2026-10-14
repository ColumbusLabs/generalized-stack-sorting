import GeneralizedSubsetPeeling

/-!
An explicit finite-relational monadic second-order fragment for endpoint peeling.
There are four binary comparison symbols, indexed by left/right endpoint sides.
The syntax has equality, set membership, Boolean connectives, finite blocks of
first-order existential quantifiers, and universal monadic set quantifiers.
A block of length k is the usual finite first-order quantifier notation; k is a
syntax parameter, not an element or a set variable. No counting, eligibility,
peeling, permutation, or machine-run predicate is a syntactic atom.

Finite models are represented by a list of natural-number token labels. First-
order quantifiers range over that list, and set quantifiers range over exactly
its subsets. The equivalence below needs a duplicate-free universe. This file
does not translate the dense comparison vocabulary to sparse event-path MSO.
-/
namespace StackSorting.EndpointMSO
open List IntervalCritical

inductive Side where
  | left | right
  deriving DecidableEq

/-- A finite structure with four uninterpreted binary relation symbols. -/
structure Model where
  domain : List Nat
  before : Side → Side → Nat → Nat → Prop

/-- Intrinsically scoped variables. A closed sentence has zero free variables
of either sort. `existsFO k` binds k individual variables, not a set/relation. -/
inductive Formula : Nat → Nat → Type where
  | truth : Formula a b
  | equal : Fin a → Fin a → Formula a b
  | member : Fin a → Fin b → Formula a b
  | before : Side → Side → Fin a → Fin a → Formula a b
  | neg : Formula a b → Formula a b
  | conj : Formula a b → Formula a b → Formula a b
  | implies : Formula a b → Formula a b → Formula a b
  | existsFO (k : Nat) : Formula (k + a) b → Formula a b
  | allSet : Formula a (b + 1) → Formula a b

/-- Standard bounded finite-model semantics, independent of endpoint counts. -/
def Eval (M : Model) : Formula a b → (Fin a → Nat) →
    (Fin b → Nat → Prop) → Prop
  | .truth, _, _ => True
  | .equal i j, env, _ => env i = env j
  | .member i X, env, sets => sets X (env i)
  | .before p q i j, env, _ => M.before p q (env i) (env j)
  | .neg f, env, sets => ¬ Eval M f env sets
  | .conj f g, env, sets => Eval M f env sets ∧ Eval M g env sets
  | .implies f g, env, sets => Eval M f env sets → Eval M g env sets
  | .existsFO k f, env, sets => ∃ values : Fin k → Nat,
      (∀ i, values i ∈ M.domain) ∧ Eval M f (Fin.addCases values env) sets
  | .allSet f, env, sets => ∀ X : Nat → Prop,
      (∀ v, X v → v ∈ M.domain) → Eval M f env (Fin.cases X sets)

def Satisfies (M : Model) (sentence : Formula 0 0) : Prop :=
  Eval M sentence Fin.elim0 Fin.elim0

/-- A finite conjunction is syntax, not a semantic quantifier. -/
def conjoin : List (Formula a b) → Formula a b
  | [] => .truth
  | f :: fs => .conj f (conjoin fs)

def allFin (fs : Fin k → Formula a b) : Formula a b := conjoin (List.ofFn fs)

@[simp] theorem eval_conjoin (M : Model) (fs : List (Formula a b))
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval M (conjoin fs) env sets ↔ ∀ f ∈ fs, Eval M f env sets := by
  induction fs with
  | nil => simp [conjoin, Eval]
  | cons f fs ih => simp [conjoin, Eval, ih]

@[simp] theorem eval_allFin (M : Model) (fs : Fin k → Formula a b)
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval M (allFin fs) env sets ↔ ∀ i, Eval M (fs i) env sets := by
  simp [allFin, List.mem_ofFn]

/-- Finite-block quantification expands one individual quantifier at a time.
This includes the zero block, which binds no values. -/
theorem exists_tuple_succ (U : List Nat) (P : (Fin (k + 1) → Nat) → Prop) :
    (∃ f, (∀ i, f i ∈ U) ∧ P f) ↔
      ∃ x, x ∈ U ∧ ∃ tail : Fin k → Nat,
        (∀ i, tail i ∈ U) ∧ P (Fin.cases x tail) := by
  constructor
  · rintro ⟨f, hf, hP⟩
    refine ⟨f 0, hf 0, (fun i => f i.succ), (fun i => hf i.succ), ?_⟩
    have heq : Fin.cases (f 0) (fun i => f i.succ) = f := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    simpa [heq] using hP
  · rintro ⟨x, hx, tail, ht, hP⟩
    exact ⟨Fin.cases x tail, fun i => Fin.cases hx ht i, hP⟩

theorem exists_tuple_zero (U : List Nat) (P : (Fin 0 → Nat) → Prop) :
    (∃ f, (∀ i, f i ∈ U) ∧ P f) ↔ P Fin.elim0 := by
  constructor
  · rintro ⟨f, _, h⟩
    have heq : f = Fin.elim0 := by funext i; exact Fin.elim0 i
    simpa [heq] using h
  · exact fun h => ⟨Fin.elim0, fun i => Fin.elim0 i, h⟩

/-- Pairwise distinctness is a finite conjunction of negated equality atoms. -/
def distinct (k : Nat) : Formula (k + 1) 1 :=
  allFin fun i : Fin k => allFin fun j : Fin k =>
    if i = j then .truth else .neg (.equal (i.castAdd 1) (j.castAdd 1))

/-- For a fixed endpoint side, exhibit k distinct members of U covering that
endpoint of the same free token x. Original strict endpoint ordering is retained. -/
def witnesses (side : Side) (k : Nat) : Formula 1 1 :=
  .existsFO k (.conj (distinct k) (allFin fun i : Fin k =>
    .conj (.member (i.castAdd 1) 0)
      (.conj (.before .left side (i.castAdd 1) (Fin.natAdd k 0))
        (.before side .right (Fin.natAdd k 0) (i.castAdd 1)))))

/-- Both negated witness blocks refer to the SAME existential token variable. -/
def eligibilitySentence (r s : Nat) : Formula 0 0 :=
  .allSet (.implies (.existsFO 1 (.member 0 0))
    (.existsFO 1 (.conj (.member 0 0)
      (.conj (.neg (witnesses .left r)) (.neg (witnesses .right s))))))

def endpoint (e : Endpoints) : Side → Nat → Nat
  | .left => e.left
  | .right => e.right

/-- The four comparison relations are interpreted directly from the original
endpoints. There is no endpoint relabeling or physical-order choice. -/
def endpointModel (e : Endpoints) (U : List Nat) : Model :=
  ⟨U, fun p q u v => endpoint e p u < endpoint e q v⟩

@[simp] theorem eval_distinct (M : Model) (k : Nat) (w : Fin k → Nat)
    (env : Fin 1 → Nat) (sets : Fin 1 → Nat → Prop) :
    Eval M (distinct k) (Fin.addCases w env) sets ↔ Function.Injective w := by
  simp only [distinct, eval_allFin]
  constructor
  · intro h i j hij
    by_cases hne : i = j
    · exact hne
    · have hn := h i j
      simp only [hne, ↓reduceIte, Eval, Fin.addCases_left] at hn
      exact False.elim (hn hij)
  · intro h i j
    by_cases hij : i = j
    · simp [hij, Eval]
    · simp only [hij, ↓reduceIte, Eval, Fin.addCases_left]
      exact fun he => hij (h he)

/-- This generic combinatorial fact is proved from lists, independently of the
formula. Distinct k-tuples in a duplicate-free finite list measure its size. -/
theorem exists_injective_tuple_iff {L : List Nat} (hL : L.Nodup) (k : Nat) :
    (∃ w : Fin k → Nat, Function.Injective w ∧ ∀ i, w i ∈ L) ↔ k ≤ L.length := by
  constructor
  · rintro ⟨w, hw, hm⟩
    have hn : (List.ofFn w).Nodup := by
      apply List.nodup_iff_eq_of_getElem_eq.mpr
      intro i hi j hj heq
      simp only [List.getElem_ofFn] at heq
      exact congrArg Fin.val (hw heq)
    have hs : List.ofFn w ⊆ L := by
      intro v hv
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact hm i
    simpa using hn.length_le_of_subset hs
  · intro hk
    let w : Fin k → Nat := fun i => L[i.val]'(Nat.lt_of_lt_of_le i.isLt hk)
    refine ⟨w, ?_, ?_⟩
    · intro i j heq
      apply Fin.ext
      exact hL.eq_of_getElem_eq _ _ heq
    · intro i
      exact List.getElem_mem _

noncomputable def selected (U : List Nat) (X : Nat → Prop) : List Nat := by
  classical
  exact U.filter (fun v => decide (X v))

@[simp] theorem mem_selected {U : List Nat} {X : Nat → Prop} {v : Nat} :
    v ∈ selected U X ↔ v ∈ U ∧ X v := by
  classical
  simp [selected]

theorem selected_nodup {U : List Nat} (hU : U.Nodup) (X : Nat → Prop) :
    (selected U X).Nodup := by
  classical
  exact hU.filter _

/-- Direct semantics of the finite tuple syntax, before any cardinality step. -/
theorem eval_witnesses (e : Endpoints) (U : List Nat) (X : Nat → Prop)
    (v : Nat) (side : Side) (k : Nat) :
    Eval (endpointModel e U) (witnesses side k) (fun _ => v) (fun _ => X) ↔
      ∃ w : Fin k → Nat, Function.Injective w ∧
        ∀ i, w i ∈ selected U X ∧ Covers e (w i) (endpoint e side v) := by
  simp only [witnesses, Eval, eval_distinct, eval_allFin, Fin.addCases_left,
    Fin.addCases_right, endpointModel, endpoint, mem_selected, Covers]
  constructor
  · rintro ⟨w, hU, hd, h⟩
    exact ⟨w, hd, fun i => ⟨⟨hU i, (h i).1⟩, (h i).2⟩⟩
  · rintro ⟨w, hd, h⟩
    exact ⟨w, fun i => (h i).1.1, hd, fun i => ⟨(h i).1.2, (h i).2⟩⟩

/-- Negating k distinct witnesses is EXACTLY a strict count bound, including k=0. -/
theorem eval_witnesses_iff_count (e : Endpoints) (U : List Nat) (hU : U.Nodup)
    (X : Nat → Prop) (v : Nat) (side : Side) (k : Nat) :
    Eval (endpointModel e U) (witnesses side k) (fun _ => v) (fun _ => X) ↔
      k ≤ endpointCount e (selected U X) (endpoint e side v) := by
  classical
  rw [eval_witnesses]
  let L := (selected U X).filter (fun u => decide (Covers e u (endpoint e side v)))
  have hL : L.Nodup := (selected_nodup hU X).filter _
  have hm : ∀ w : Fin k → Nat,
      (∀ i, w i ∈ selected U X ∧ Covers e (w i) (endpoint e side v)) ↔
      ∀ i, w i ∈ L := by
    intro w
    simp [L]
  simp only [hm]
  rw [exists_injective_tuple_iff hL]
  simp [L, endpointCount, List.countP_eq_length_filter]

@[simp] theorem addCases_singleton (values : Fin 1 → Nat) :
    (fun i : Fin 1 => Fin.addCases values (Fin.elim0 : Fin 0 → Nat) i) =
      (fun _ => values 0) := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

@[simp] theorem cases_singleton {α : Type} (x : α) :
    (fun i : Fin 1 => Fin.cases x (Fin.elim0 : Fin 0 → α) i) = (fun _ => x) := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

/-- The semantic sentence reduces to the independently defined endpoint
criterion on the chosen subset. The witness v is shared by both bounds. -/
theorem satisfies_iff_selected (e : Endpoints) (U : List Nat) (hU : U.Nodup)
    (r s : Nat) :
    Satisfies (endpointModel e U) (eligibilitySentence r s) ↔
      ∀ X : Nat → Prop, (∀ v, X v → v ∈ U) → (∃ v, X v) →
        ∃ v, X v ∧ Eligible e r s (selected U X) v := by
  classical
  simp only [Satisfies, eligibilitySentence, Eval, addCases_singleton, cases_singleton]
  constructor
  · intro h X hX hn
    obtain ⟨v, hv⟩ := hn
    obtain ⟨values, _, hm, hl, hr⟩ := h X hX
      ⟨fun _ => v, fun _ => hX v hv, hv⟩
    rw [eval_witnesses_iff_count e U hU] at hl hr
    exact ⟨values 0, hm, Nat.lt_of_not_ge hl, Nat.lt_of_not_ge hr⟩
  · intro h X hX ha
    obtain ⟨values, _, hv⟩ := ha
    obtain ⟨v, hv, hl, hr⟩ := h X hX ⟨values 0, hv⟩
    refine ⟨fun _ => v, fun _ => hX v hv, hv, ?_, ?_⟩
    · rw [eval_witnesses_iff_count e U hU]
      exact Nat.not_le.mpr hl
    · rw [eval_witnesses_iff_count e U hU]
      exact Nat.not_le.mpr hr

/-- Exact bridge to the already certified order-independent endpoint criterion. -/
theorem satisfies_iff_everySubsetEligible (e : Endpoints) (U : List Nat)
    (hU : U.Nodup) (r s : Nat) :
    Satisfies (endpointModel e U) (eligibilitySentence r s) ↔
      EverySubsetEligible e r s U := by
  classical
  rw [satisfies_iff_selected e U hU]
  constructor
  · intro h V hV hsub hne
    have hp : (selected U (fun v => v ∈ V)).Perm V := by
      apply (List.perm_ext_iff_of_nodup (selected_nodup hU _) hV).mpr
      intro v
      simp only [mem_selected]
      exact ⟨fun hv => hv.2, fun hv => ⟨hsub hv, hv⟩⟩
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil V hne
    obtain ⟨w, hw, he⟩ := h (fun v => v ∈ V) (fun _ h => hsub h) ⟨v, hv⟩
    exact ⟨w, hw, he.perm hp⟩
  · intro h X hX hn
    have hsub : selected U X ⊆ U := fun _ hv => (mem_selected.mp hv).1
    have hne : selected U X ≠ [] := by
      obtain ⟨v, hv⟩ := hn
      exact List.ne_nil_of_mem (mem_selected.mpr ⟨hX v hv, hv⟩)
    obtain ⟨v, hv, he⟩ := h (selected U X) (selected_nodup hU X) hsub hne
    exact ⟨v, (mem_selected.mp hv).2, he⟩

/-- All widths and lengths, including zero, with the genuine permutation premise.
The finite model uses the ACTUAL canonical endpoints from the original machine. -/
theorem generated_iff_endpointMSO {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    Generalized.Run r s [] (List.range n) output [] ↔
      Satisfies (endpointModel
        (Generalized.extractedEndpoints (Generalized.canonicalEvents 0 output))
        (List.range n)) (eligibilitySentence r s) :=
  (Generalized.generated_iff_everySubsetEligible hp).trans
    (satisfies_iff_everySubsetEligible _ _ List.nodup_range _ _).symm

#print generated_iff_endpointMSO
#print axioms exists_injective_tuple_iff
#print axioms eval_witnesses_iff_count
#print axioms satisfies_iff_everySubsetEligible
#print axioms generated_iff_endpointMSO
end StackSorting.EndpointMSO
