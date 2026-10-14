import SparseHamiltonianPath

namespace StackSorting.SparseEndpointMSO

def disjunction (f g : Formula a b) : Formula a b := .neg (.conj (.neg f) (.neg g))
def equivalence (f g : Formula a b) : Formula a b := .conj (.implies f g) (.implies g f)

theorem eval_disjunction (D : Model) (f g : Formula a b) (env : Fin a → Nat)
    (sets : Fin b → Nat → Prop) : Eval D (disjunction f g) env sets ↔
      Eval D f env sets ∨ Eval D g env sets := by
  classical
  constructor
  · intro h
    by_cases hf : Eval D f env sets
    · exact Or.inl hf
    · exact Or.inr (Classical.byContradiction (fun hg => h ⟨hf, hg⟩))
  · rintro (hf | hg) hn
    · exact hn.1 hf
    · exact hn.2 hg

theorem eval_equivalence (D : Model) (f g : Formula a b) (env : Fin a → Nat)
    (sets : Fin b → Nat → Prop) : Eval D (equivalence f g) env sets ↔
      (Eval D f env sets ↔ Eval D g env sets) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem eval_all_one (D : Model) (f : Formula (1 + a) b)
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (.allFO 1 f) env sets ↔
      ∀ x ∈ D.domain, Eval D f (Fin.addCases (fun _ => x) env) sets := by
  constructor
  · intro h x hx; exact h (fun _ => x) (fun _ => hx)
  · intro h values hv
    have he : values = fun _ => values 0 := by funext i; exact congrArg values (Subsingleton.elim i 0)
    exact Eq.mpr (congrArg (fun v => Eval D f (Fin.addCases v env) sets) he)
      (h (values 0) (hv 0))

theorem eval_exists_one (D : Model) (f : Formula (1 + a) b)
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (.existsFO 1 f) env sets ↔
      ∃ x ∈ D.domain, Eval D f (Fin.addCases (fun _ => x) env) sets := by
  constructor
  · rintro ⟨values, hv, hf⟩
    have he : values = fun _ => values 0 := by funext i; exact congrArg values (Subsingleton.elim i 0)
    exact ⟨values 0, hv 0, Eq.mp (congrArg (fun v => Eval D f (Fin.addCases v env) sets) he) hf⟩
  · rintro ⟨x, hx, hf⟩; exact ⟨fun _ => x, fun _ => hx, hf⟩

theorem eval_conj' (D : Model) (f g : Formula a b) (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (.conj f g) env sets ↔ Eval D f env sets ∧ Eval D g env sets := Iff.rfl
theorem eval_neg' (D : Model) (f : Formula a b) (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (.neg f) env sets ↔ ¬ Eval D f env sets := Iff.rfl
theorem eval_implies' (D : Model) (f g : Formula a b) (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (.implies f g) env sets ↔ (Eval D f env sets → Eval D g env sets) := Iff.rfl

def partitionSentence : Formula 0 0 := .allFO 1
  (.conj (disjunction (.insert 0) (.remove 0)) (.neg (.conj (.insert 0) (.remove 0))))

def symmetricSentence : Formula 0 0 := .allFO 1 (.allFO 1
  (.implies (.matching 1 0) (.matching 0 1)))

def perfectSentence : Formula 0 0 := .allFO 1 (.existsFO 1
  (.conj (.matching 1 0) (.allFO 1 (.implies (.matching 2 0) (.equal 0 1)))))

def oppositeSentence : Formula 0 0 := .allFO 1 (.allFO 1
  (.implies (.matching 1 0) (equivalence (.insert 1) (.remove 0))))

def forwardSentence : Formula 0 0 := .allFO 1 (.allFO 1
  (.implies (.conj (.insert 1) (.matching 1 0)) (strictBefore 1 0)))

def lazySentence : Formula 0 0 := .allFO 1 (.allFO 1
  (.implies (.conj (.insert 1) (.conj (.remove 0) (.successor 1 0))) (.matching 1 0)))

def outgoingUniqueSentence : Formula 0 0 := .allFO 1 (.allFO 1 (.allFO 1
  (.implies (.conj (.successor 2 1) (.successor 2 0)) (.equal 1 0))))

def incomingUniqueSentence : Formula 0 0 := .allFO 1 (.allFO 1 (.allFO 1
  (.implies (.conj (.successor 1 2) (.successor 0 2)) (.equal 1 0))))

def rootedReachSentence : Formula 0 0 := .existsFO 1
  (.conj (.allFO 1 (.neg (.successor 0 1))) (.allFO 1 (reach 1 0)))

def pathSentence : Formula 0 0 :=
  .conj rootedReachSentence (.conj outgoingUniqueSentence incomingUniqueSentence)

def matchingSentence : Formula 0 0 :=
  .conj partitionSentence (.conj symmetricSentence (.conj perfectSentence
    (.conj oppositeSentence forwardSentence)))

/-- The entire structural sentence uses only I,R,S,M, equality, ordinary first
order quantifiers, and the already-expanded monadic reachability formula. -/
def structuralSentence : Formula 0 0 :=
  .conj pathSentence (.conj matchingSentence lazySentence)

theorem satisfies_partitionSentence (D : Model) : Satisfies D partitionSentence ↔
    ∀ x ∈ D.domain, (D.I x ∨ D.R x) ∧ ¬ (D.I x ∧ D.R x) := by
  simp only [Satisfies, partitionSentence, eval_all_one, eval_conj', eval_neg', eval_disjunction]
  simp [Eval, Fin.addCases]

theorem satisfies_symmetricSentence (D : Model) : Satisfies D symmetricSentence ↔
    ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.M x y → D.M y x := by
  simp only [Satisfies, symmetricSentence, eval_all_one, eval_implies']
  simp [Eval, Fin.addCases]

theorem satisfies_perfectSentence (D : Model) : Satisfies D perfectSentence ↔
    ∀ x ∈ D.domain, ∃ y ∈ D.domain, D.M x y ∧
      ∀ z ∈ D.domain, D.M x z → z = y := by
  simp only [Satisfies, perfectSentence, eval_all_one, eval_exists_one, eval_conj', eval_implies']
  simp [Eval, Fin.addCases]

theorem satisfies_oppositeSentence (D : Model) : Satisfies D oppositeSentence ↔
    ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.M x y → (D.I x ↔ D.R y) := by
  simp only [Satisfies, oppositeSentence, eval_all_one, eval_implies', eval_equivalence]
  simp [Eval, Fin.addCases]

theorem satisfies_forwardSentence (D : Model) : Satisfies D forwardSentence ↔
    ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.I x → D.M x y → x ≠ y ∧ ClosedReach D x y := by
  simp only [Satisfies, forwardSentence, eval_all_one, eval_implies', strictBefore,
    eval_conj', eval_neg', eval_reach]
  simp [Eval, Fin.addCases, and_imp]

theorem satisfies_lazySentence (D : Model) : Satisfies D lazySentence ↔ LazyBoundary D := by
  simp only [Satisfies, lazySentence, eval_all_one, eval_implies', eval_conj']
  simp [Eval, Fin.addCases, LazyBoundary, and_imp]

theorem satisfies_outgoingUniqueSentence (D : Model) : Satisfies D outgoingUniqueSentence ↔
    ∀ x ∈ D.domain, ∀ y ∈ D.domain, ∀ z ∈ D.domain, D.S x y → D.S x z → y = z := by
  simp only [Satisfies, outgoingUniqueSentence, eval_all_one, eval_implies', eval_conj']
  simp [Eval, Fin.addCases, and_imp]

theorem satisfies_incomingUniqueSentence (D : Model) : Satisfies D incomingUniqueSentence ↔
    ∀ x ∈ D.domain, ∀ y ∈ D.domain, ∀ z ∈ D.domain, D.S y x → D.S z x → y = z := by
  simp only [Satisfies, incomingUniqueSentence, eval_all_one, eval_implies', eval_conj']
  simp [Eval, Fin.addCases, and_imp]

theorem satisfies_rootedReachSentence (D : Model) : Satisfies D rootedReachSentence ↔
    ∃ root ∈ D.domain, (∀ x ∈ D.domain, ¬ D.S x root) ∧
      ∀ x ∈ D.domain, ClosedReach D root x := by
  simp only [Satisfies, rootedReachSentence, eval_exists_one, eval_all_one,
    eval_conj', eval_neg', eval_reach]
  simp [Eval, Fin.addCases]

theorem satisfies_pathSentence (D : Model) : Satisfies D pathSentence ↔
    ∃ root, RootedPathAxioms D root := by
  change (Satisfies D rootedReachSentence ∧
    Satisfies D outgoingUniqueSentence ∧ Satisfies D incomingUniqueSentence) ↔ _
  rw [satisfies_rootedReachSentence, satisfies_outgoingUniqueSentence, satisfies_incomingUniqueSentence]
  constructor
  · rintro ⟨⟨root, hr, hn, ha⟩, ho, hi⟩
    exact ⟨root, hr, hn, ha, ho, hi⟩
  · rintro ⟨root, h⟩
    exact ⟨⟨root, h.root_mem, h.no_incoming, h.reachable⟩, h.outgoing_unique, h.incoming_unique⟩

theorem satisfies_matchingSentence (D : Model) : Satisfies D matchingSentence ↔
    PathMatchingAxioms D := by
  change (Satisfies D partitionSentence ∧ Satisfies D symmetricSentence ∧
    Satisfies D perfectSentence ∧ Satisfies D oppositeSentence ∧ Satisfies D forwardSentence) ↔ _
  rw [satisfies_partitionSentence, satisfies_symmetricSentence, satisfies_perfectSentence,
    satisfies_oppositeSentence, satisfies_forwardSentence]
  exact ⟨fun ⟨hp, hs, he, ho, hf⟩ => ⟨hp, hs, he, ho, hf⟩,
    fun h => ⟨h.partition, h.symmetric, h.perfect, h.opposite, h.forward⟩⟩

theorem satisfies_structuralSentence (D : Model) : Satisfies D structuralSentence ↔
    (∃ root, RootedPathAxioms D root) ∧ PathMatchingAxioms D ∧ LazyBoundary D := by
  change (Satisfies D pathSentence ∧ Satisfies D matchingSentence ∧ Satisfies D lazySentence) ↔ _
  rw [satisfies_pathSentence, satisfies_matchingSentence, satisfies_lazySentence]

/-- A model of the exact syntactic structural sentence, with arbitrary vertex
names and no supplied ordering, is isomorphic to a canonical permutation
diagram. This is the missing arbitrary-model converse direction. -/
theorem structuralSentence_canonical_converse {D : Model} (hs : Satisfies D structuralSentence) :
    ∃ n output, output.Perm (List.range n) ∧ Nonempty (Isomorphism D (canonicalDiagram output)) := by
  obtain ⟨⟨root, hp⟩, hm, hl⟩ := (satisfies_structuralSentence D).mp hs
  obtain ⟨order, he⟩ := hp.enumeration
  obtain ⟨output, ho, hiso⟩ := enumeratedModel_exists_canonical he hm hl
  exact ⟨_, output, ho, hiso⟩

/-- Adding the actual sparse eligibility sentence yields an original-machine
generated permutation, with no physical-history or ordering witness supplied. -/
theorem acceptedModel_generated_permutation {D : Model} {r s : Nat}
    (hs : Satisfies D structuralSentence) (hf : Satisfies D (eligibilitySentence r s)) :
    ∃ n output, output.Perm (List.range n) ∧ Generalized.Run r s [] (List.range n) output [] ∧
      Nonempty (Isomorphism D (canonicalDiagram output)) := by
  obtain ⟨⟨root, hp⟩, hm, hl⟩ := (satisfies_structuralSentence D).mp hs
  obtain ⟨order, he⟩ := hp.enumeration
  have hp' := reindexed_timePath he
  let iso := chronologicalIsomorphism he
  have hm' := hm.to_indexed iso hp'
  have hl' := hl.transport iso
  have hcan := supported_eq_canonicalDiagram hp' hm' hl'
  refine ⟨_, decodedPermutation (reindexed D order), decodedPermutation_perm hp' hm',
    (enumeratedModel_generated_iff he hm hl).mpr hf, ?_⟩
  exact ⟨hcan ▸ iso.trans (supportIsomorphism _)⟩

#print axioms satisfies_structuralSentence
#print axioms structuralSentence_canonical_converse
#print axioms acceptedModel_generated_permutation
end StackSorting.SparseEndpointMSO
