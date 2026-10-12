import RawCanonical

/-! # Reverse completeness: successful original-machine inputs have forest paths -/
namespace StackSorting.Labelled
open TForest

def PopAllowed (f : TForest) (flag : Bool) (out : List Nat) : Prop :=
  flag = true ∨ match out with
    | [] => True
    | a :: _ => a ∉ tokens f

def ForestSorts (f : TForest) (flag : Bool) (input out : List Nat) : Prop :=
  ∃ acts c, tokenRun acts (f, flag) = some ((nil, c), out) ∧ inputs acts = input

theorem mem_canonicalInsert (a z : Nat) (held : List Nat) :
    z ∈ canonicalInsert a held ↔ z = a ∨ z ∈ held := by
  cases held with
  | nil => simp [canonicalInsert]
  | cons b rest =>
    by_cases h : a < b <;> simp [canonicalInsert, h, or_left_comm]

/-- Canonical numeric insertion lifts to a forest insertion and preserves all
comparison obligations. -/
theorem forest_push_lift (f : TForest) (flag : Bool) (a : Nat)
    (hf : Heap f) (ha : a ∉ tokens f) :
    ∃ act g, introduced act = [a] ∧
      tokenStep act (f, flag) = some ((g, false), []) ∧
      tokens g = canonicalInsert a (tokens f) ∧ Heap g := by
  cases f with
  | nil =>
    exact ⟨.push0 a, cons a nil nil, rfl, rfl, rfl, by simp [Heap, tokens]⟩
  | cons b c r =>
    by_cases hab : a < b
    · refine ⟨.push0 a, cons a (cons b c nil) r, rfl, rfl, ?_, ?_⟩
      · simp [tokens, canonicalInsert, hab]
      · refine ⟨?_, ⟨hf.1, hf.2.1, trivial⟩, hf.2.2⟩
        intro z hz
        simp [tokens] at hz
        rcases hz with rfl | hz
        · exact hab
        · exact Nat.lt_trans hab (hf.1 z hz)
    · have hba : b < a := by
        have hne : a ≠ b := by intro he; subst a; exact ha (by simp [tokens])
        omega
      refine ⟨.push1 a, cons b (cons a nil c) r, rfl, rfl, ?_, ?_⟩
      · simp [tokens, canonicalInsert, hab]
      · refine ⟨?_, ⟨by simp [tokens], trivial, hf.2.1⟩, hf.2.2⟩
        intro z hz
        simp [tokens] at hz
        rcases hz with rfl | hz
        · exact hba
        · exact hf.1 z hz

/-- If the required output is held, it is a removable forest root. Numeric
comparison obligations rule out removing a child before its smaller parent. -/
theorem forest_pop_lift (f : TForest) (input : List Nat) (o : Nat) (out : List Nat)
    (hf : Heap f) (h : CanSort (tokens f) input (o :: out))
    (hs : (o :: out).Pairwise (· < ·)) (ho : o ∈ tokens f) :
    ∃ act g, introduced act = [] ∧
      tokenStep act (f, true) = some ((g, true), [o]) ∧
      CanSort (tokens g) input out ∧ Heap g := by
  have hp := canSort_pop (tokens f) input o out h hs ho
  have hn := (List.nodup_append.mp (canSort_nodup _ _ _ h hs)).1
  cases f with
  | nil => simp [tokens] at ho
  | cons b c r =>
    by_cases hbo : b = o
    · subst b
      have hnot : o ∉ tokens c ++ tokens r := (List.nodup_cons.mp hn).1
      have he : deleteToken o (tokens (cons o c r)) = tokens (append c r) := by
        have hfilter : (tokens c ++ tokens r).filter (· != o) = tokens c ++ tokens r :=
          deleteToken_eq_self o _ hnot
        simp [tokens, deleteToken, tokens_append, hfilter]
      refine ⟨.pop0, append c r, rfl, rfl, ?_, ?_⟩
      · simpa [he] using hp.2
      · exact (heap_append c r).mpr ⟨hf.2.1, hf.2.2⟩
    · cases c with
      | cons a d e =>
        have hao : a = o := by
          by_cases hao : a = o
          · exact hao
          · simp [tokens, popChoice, hbo, hao] at hp
        have hba : b < a := hf.1 a (by simp [tokens])
        have hbout : b ∈ o :: out := (canSort_supply _ _ _ h).mem_iff.mp
          (by simp [tokens])
        have hb : b ∈ out := by simpa [hbo] using hbout
        have hob : o < b := (List.pairwise_cons.mp hs).1 b hb
        omega
      | nil =>
        cases r with
        | nil => simp [tokens, popChoice, hbo] at hp
        | cons a d r =>
          have hao : a = o := by
            by_cases hao : a = o
            · exact hao
            · simp [tokens, popChoice, hbo, hao] at hp
          subst a
          have hnrest : (o :: (tokens d ++ tokens r)).Nodup :=
            (List.nodup_cons.mp hn).2
          have hnot : o ∉ tokens d ++ tokens r := (List.nodup_cons.mp hnrest).1
          have he : deleteToken o (tokens (cons b nil (cons o d r))) =
              tokens (cons b nil (append d r)) := by
            have hfilter : (tokens d ++ tokens r).filter (· != o) = tokens d ++ tokens r :=
              deleteToken_eq_self o _ hnot
            simp [tokens, deleteToken, tokens_append, hfilter, hbo]
          refine ⟨.pop1, cons b nil (append d r), rfl, rfl, ?_, ?_⟩
          · simpa [he] using hp.2
          · refine ⟨by simp [tokens], trivial, ?_⟩
            exact (heap_append d r).mpr ⟨hf.2.2.2.1, hf.2.2.2.2⟩

/-- Reverse completeness for arbitrary residual configurations. Successful raw
sorting plus the comparison and pop-permission invariants constructs a finite
forest trace with exactly the same unread input and output. -/
theorem original_to_forest (f : TForest) (flag : Bool) (input out : List Nat)
    (hf : Heap f) (hs : out.Pairwise (· < ·))
    (hp : PopAllowed f flag out) (h : CanSort (tokens f) input out) :
    ForestSorts f flag input out := by
  suffices aux : ∀ n, ∀ (f : TForest) (flag : Bool) (input out : List Nat),
      input.length + out.length = n → Heap f → out.Pairwise (· < ·) →
      PopAllowed f flag out → CanSort (tokens f) input out →
      ForestSorts f flag input out by
    exact aux _ f flag input out rfl hf hs hp h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f flag input out hsize hf hs hp h
    cases out with
    | nil =>
      have he := (canSort_supply (tokens f) input [] h).eq_nil
      have hparts := List.append_eq_nil_iff.mp he
      have hfnil : f = nil := by
        cases f with
        | nil => rfl
        | cons a c r => simp [tokens] at hparts
      have hinil := hparts.2
      subst f
      subst input
      exact ⟨[], flag, rfl, rfl⟩
    | cons o out =>
      have htail : out.Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
      by_cases ho : o ∈ tokens f
      · have hflag : flag = true := by
          rcases hp with he | hnot
          · exact he
          · exact False.elim (hnot ho)
        subst flag
        obtain ⟨act, g, hintro, hstep, hsort, hheap⟩ := forest_pop_lift f input o out hf h hs ho
        have hlt : input.length + out.length < n := by
          simp only [List.length_cons] at hsize
          omega
        obtain ⟨acts, c, hr, hi⟩ := ih _ hlt g true input out rfl hheap htail (Or.inl rfl) hsort
        refine ⟨act :: acts, c, ?_, ?_⟩
        · simp [tokenRun, hstep, hr]
        · change introduced act ++ inputs acts = input
          simp [hintro, hi]
      · cases input with
        | nil =>
          have hm : o ∈ tokens f ++ [] := (canSort_supply _ _ _ h).mem_iff.mpr (by simp)
          exact False.elim (ho (by simpa using hm))
        | cons a input =>
          by_cases hao : a = o
          · subst a
            have hsort := canSort_bypass (tokens f) input o out h hs ho
            have hlt : input.length + out.length < n := by
              simp only [List.length_cons] at hsize
              omega
            obtain ⟨acts, c, hr, hi⟩ := ih _ hlt f true input out rfl hf htail (Or.inl rfl) hsort
            refine ⟨.bypass o :: acts, c, ?_, ?_⟩
            · simp [tokenRun, tokenStep, hr]
            · change o :: inputs acts = o :: input
              simp [hi]
          · have hanot : a ∉ tokens f := by
              have hn := canSort_nodup _ _ _ h hs
              intro hm
              exact (List.nodup_append.mp hn).2.2 a hm a (by simp) rfl
            obtain ⟨act, g, hintro, hstep, htoks, hheap⟩ := forest_push_lift f flag a hf hanot
            have hsort : CanSort (tokens g) input (o :: out) := by
              rw [htoks]
              exact canSort_push (tokens f) input a o out h hs ho
            have hnot : o ∉ tokens g := by
              rw [htoks, mem_canonicalInsert]
              intro hm
              rcases hm with he | hm
              · exact hao he.symm
              · exact ho hm
            have hlt : input.length + (o :: out).length < n := by
              simp only [List.length_cons] at hsize ⊢
              omega
            obtain ⟨acts, c, hr, hi⟩ := ih _ hlt g false input (o :: out) rfl hheap hs (Or.inr hnot) hsort
            refine ⟨act :: acts, c, ?_, ?_⟩
            · simp [tokenRun, hstep, hr]
            · change introduced act ++ inputs acts = a :: input
              simp [hintro, hi]

/-- Every permutation sortable by the original machine has a complete forest
trace with that exact input and increasing output. No canonical-sorter theorem
is assumed: its local normalization facts were proved for raw traces. -/
theorem sortable_has_forest (input : List Nat) (n : Nat)
    (h : CanSort [] input (List.range' 1 n)) :
    ForestSorts nil true input (List.range' 1 n) := by
  exact original_to_forest nil true input (List.range' 1 n) trivial
    List.pairwise_lt_range' (Or.inl rfl) h

/-- Exact equivalence of original-machine sortability and complete forest
traces, with identical input and increasing output. -/
theorem original_iff_forest (input : List Nat) (n : Nat) :
    CanSort [] input (List.range' 1 n) ↔
      ForestSorts nil true input (List.range' 1 n) := by
  constructor
  · exact sortable_has_forest input n
  · rintro ⟨acts, c, hr, hi⟩
    have hstack := stack_run acts (nil, true) (nil, c) (List.range' 1 n) hr
    have hraw := expand_run acts ([], true) ([], c) (List.range' 1 n) hstack
    exact ⟨expandTrace acts, hraw, (expand_inputs acts).trans hi⟩

/-- Every sortable input has exactly one complete increasing-output labelled
forest operation trace. This is a theorem of the original machine, with no
canonical-sorter or bijection axiom. -/
theorem sortable_unique_trace (input : List Nat) (n : Nat)
    (h : CanSort [] input (List.range' 1 n)) :
    ∃ acts c, tokenRun acts (nil, true) = some ((nil, c), List.range' 1 n) ∧
      inputs acts = input ∧
      ∀ bs d, tokenRun bs (nil, true) = some ((nil, d), List.range' 1 n) →
        inputs bs = input → bs = acts := by
  obtain ⟨acts, c, hr, hi⟩ := sortable_has_forest input n h
  refine ⟨acts, c, hr, hi, ?_⟩
  intro bs d hb hbi
  exact complete_trace_unique bs acts (nil, true) d c (List.range' 1 n)
    hb hr (hbi.trans hi.symm) List.pairwise_lt_range'

#print axioms forest_push_lift
#print axioms forest_pop_lift
#print axioms original_to_forest
#print axioms sortable_has_forest
#print axioms original_iff_forest
#print axioms sortable_unique_trace

end StackSorting.Labelled
