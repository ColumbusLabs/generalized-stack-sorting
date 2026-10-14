import SparseIncidenceOwnership

namespace StackSorting.SparseEndpointMSO.IncidenceOwnership

/-- Explicit sparse syntax. Chronology is the previously expanded closed-set
reachability formula, not a new atomic predicate. -/
def matchingOnlyFormula (i j : Fin a) : Formula a b :=
  .conj (strictBefore i j) (.conj (.matching i j)
    (.neg (disjunction (.successor i j) (.successor j i))))

theorem eval_matchingOnlyFormula (D : Model) (i j : Fin a)
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (matchingOnlyFormula i j) env sets ↔ MatchingOnly D (env i) (env j) := by
  change (Eval D (strictBefore i j) env sets ∧ D.M (env i) (env j) ∧
    ¬ Eval D (disjunction (.successor i j) (.successor j i)) env sets) ↔ _
  have hb : Eval D (strictBefore i j) env sets ↔ Before D (env i) (env j) :=
    and_congr Iff.rfl (eval_reach D i j env sets)
  rw [hb, eval_disjunction]
  rfl

/-- Tag 0 is a vertex, tag 1 owns one chronological successor edge, and tag 2
owns one matching edge not already present in the successor copy. -/
def domainFormula : Fin 3 → Formula 1 0 :=
  Fin.cases .truth (Fin.cases (.existsFO 1 (.successor 1 0))
    (fun _ => .existsFO 1 (matchingOnlyFormula 1 0)))

theorem domainFormula_correct (D : Model) (c : Fin 3) (x : Nat) :
    (x ∈ D.domain ∧ Eval D (domainFormula c) (fun _ => x) Fin.elim0) ↔ ValidCode D c x := by
  refine Fin.cases ?_ (fun c => Fin.cases ?_ (fun c => ?_) c) c
  · simp [domainFormula, Eval, valid_vertex]
  · simp only [domainFormula, Fin.cases_succ, Fin.cases_zero, eval_exists_one, Eval]
    rfl
  · have hc : c = 0 := Subsingleton.elim c 0
    subst c
    simp only [domainFormula, Fin.cases_succ, eval_exists_one, eval_matchingOnlyFormula]
    rfl

/-- Directed incidence: the first argument is a vertex, the second an edge.
The copy-domain guards are supplied by the ambient interpretation. -/
def incidenceFormula (c d : Fin 3) : Formula 2 0 :=
  if c = 0 then
    if d = 1 then disjunction (.equal 0 1) (.successor 1 0)
    else if d = 2 then disjunction (.equal 0 1) (.matching 1 0)
    else .neg .truth
  else .neg .truth

def CodeIncident (D : Model) (c d : Fin 3) (x y : Nat) : Prop :=
  c = 0 ∧ ((d = 1 ∧ (x = y ∨ D.S y x)) ∨ (d = 2 ∧ (x = y ∨ D.M y x)))

theorem incidenceFormula_correct (D : Model) (c d : Fin 3) (env : Fin 2 → Nat) :
    Eval D (incidenceFormula c d) env Fin.elim0 ↔ CodeIncident D c d (env 0) (env 1) := by
  classical
  by_cases hc : c = 0
  · by_cases hd : d = 1
    · simp [incidenceFormula, hc, hd, eval_disjunction, Eval, CodeIncident]
    · by_cases hd' : d = 2
      · simp [incidenceFormula, hc, hd', eval_disjunction, Eval, CodeIncident]
      · simp [incidenceFormula, hc, hd, hd', Eval, CodeIncident]
  · simp [incidenceFormula, hc, Eval, CodeIncident]

/-- The explicit sparse incidence test agrees with the real endpoint relation,
including edges belonging to both S and M. -/
theorem represented_incidence {D : Model} (h : Laws D)
    (v : Vertex D) (e : Edge D) {c d : Fin 3} {x y : Nat}
    (hv : Represents D c x (.inl v)) (he : Represents D d y (.inr e)) :
    CodeIncident D c d x y ↔ Incident v e := by
  rcases hv with ⟨rfl, rfl⟩
  rcases he with ⟨rfl, ⟨rfl, hs⟩ | ⟨rfl, hm⟩⟩
  · change (0 = (0 : Fin 3) ∧ ((1 = (1 : Fin 3) ∧
      (v.val = e.val.1 ∨ D.S e.val.1 v.val)) ∨
      (1 = (2 : Fin 3) ∧ (v.val = e.val.1 ∨ D.M e.val.1 v.val)))) ↔ _
    simp only [show ¬ (1 : Fin 3) = 2 from by decide, true_and, or_false, false_and]
    constructor
    · rintro (hv | hvs)
      · exact Or.inl hv
      · exact Or.inr (h.successor_functional _ e.property.2.1 _ v.property
          _ e.property.2.2.1 hvs hs)
    · rintro (hv | hv)
      · exact Or.inl hv
      · exact Or.inr (hv.symm ▸ hs)
  · change (0 = (0 : Fin 3) ∧ ((2 = (1 : Fin 3) ∧
      (v.val = e.val.1 ∨ D.S e.val.1 v.val)) ∨
      (2 = (2 : Fin 3) ∧ (v.val = e.val.1 ∨ D.M e.val.1 v.val)))) ↔ _
    simp only [show ¬ (2 : Fin 3) = 1 from by decide, true_and, false_or, false_and]
    constructor
    · rintro (hv | hvm)
      · exact Or.inl hv
      · exact Or.inr (h.matching_functional _ e.property.2.1 _ v.property
          _ e.property.2.2.1 hvm hm.2.1)
    · rintro (hv | hv)
      · exact Or.inl hv
      · exact Or.inr (hv.symm ▸ hm.2.1)

#print axioms domainFormula_correct
#print axioms incidenceFormula_correct
#print axioms represented_incidence
end StackSorting.SparseEndpointMSO.IncidenceOwnership
