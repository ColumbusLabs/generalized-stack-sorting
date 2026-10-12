import RawDeletion

/-! # Eager output and bypass normalization of the original machine -/
namespace StackSorting.Labelled

theorem deleteToken_eq_self (a : Nat) (xs : List Nat) (h : a ∉ xs) :
    deleteToken a xs = xs := by
  apply List.filter_eq_self.mpr
  intro b hb
  have hne : b ≠ a := by intro he; subst b; exact h hb
  simpa using hne

/-- The next output cannot also be unread when it is already held, since
successful increasing output makes the combined token supply duplicate-free. -/
theorem next_not_input (ops : List RawOp) (held : List Nat) (a : Nat) (out : List Nat)
    (h : rawRun ops held = some ([], a :: out))
    (hs : (a :: out).Pairwise (· < ·)) (ha : a ∈ held) : a ∉ rawInputs ops := by
  have hn : (a :: out).Nodup := hs.imp (fun hlt => Nat.ne_of_lt hlt)
  have hd := (raw_complete_permutation ops held (a :: out) h).nodup_iff.mpr hn
  intro hi
  exact (List.nodup_append.mp hd).2.2 a ha a hi rfl

/-- Deleting the next held output preserves every unread input and leaves a
successful continuation for precisely the remaining output. -/
theorem delete_next_output (ops : List RawOp) (held : List Nat) (a : Nat) (out : List Nat)
    (h : rawRun ops held = some ([], a :: out))
    (hs : (a :: out).Pairwise (· < ·)) (ha : a ∈ held) :
    ∃ ops', rawRun ops' (deleteToken a held) = some ([], out) ∧
      rawInputs ops' = rawInputs ops := by
  have hn : (a :: out).Nodup := hs.imp (fun hlt => Nat.ne_of_lt hlt)
  have hnotout := (List.nodup_cons.mp hn).1
  have hnotin := next_not_input ops held a out h hs ha
  have hd := delete_run a ops held [] (a :: out) h
  refine ⟨deleteTrace a ops held, ?_, ?_⟩
  · have heout : out.filter (· != a) = out := deleteToken_eq_self a out hnotout
    simpa [deleteToken, heout] using hd.1
  · simpa [deleteToken_eq_self a (rawInputs ops) hnotin] using hd.2

/-- If a held token is the next output and cannot be read again, it is already
in one of the two accessible positions. Pushes cannot make it more accessible. -/
theorem first_held_accessible (ops : List RawOp) (held : List Nat) (a : Nat)
    (out : List Nat) (h : rawRun ops held = some ([], a :: out))
    (ha : a ∈ held) (hnot : a ∉ rawInputs ops) : popChoice held a ≠ none := by
  induction ops generalizing held out with
  | nil => simp [rawRun] at h
  | cons op ops ih =>
    obtain ⟨u, emitted, tail, hs, hr, hout⟩ := raw_split_run op ops held [] _ h
    cases op with
    | push0 b =>
      have hne : b ≠ a := by
        intro he; subst b; exact hnot (by simp [rawInputs, rawIntroduced])
      have hnot' : a ∉ rawInputs ops := by
        intro hm; apply hnot; change a ∈ b :: rawInputs ops; exact List.mem_cons_of_mem b hm
      simp [rawStep] at hs
      rcases hs with ⟨rfl, rfl⟩
      simp at hout
      subst tail
      have hacc := ih (b :: held) out hr (by simp [ha]) hnot'
      cases held with
      | nil => simp at ha
      | cons c rest =>
        by_cases hc : c = a
        · simp [popChoice, hc]
        · simp [popChoice, hne, hc] at hacc
    | push1 b =>
      have hne : b ≠ a := by
        intro he; subst b; exact hnot (by simp [rawInputs, rawIntroduced])
      have hnot' : a ∉ rawInputs ops := by
        intro hm; apply hnot; change a ∈ b :: rawInputs ops; exact List.mem_cons_of_mem b hm
      cases held with
      | nil => simp [rawStep] at hs
      | cons c rest =>
        simp [rawStep] at hs
        rcases hs with ⟨rfl, rfl⟩
        simp at hout
        subst tail
        have hacc := ih (c :: b :: rest) out hr (by simpa [or_left_comm] using List.mem_cons_of_mem b ha) hnot'
        by_cases hc : c = a
        · simp [popChoice, hc]
        · simp [popChoice, hne, hc] at hacc
    | pop0 =>
      cases held with
      | nil => simp [rawStep] at hs
      | cons b rest =>
        simp [rawStep] at hs
        rcases hs with ⟨rfl, rfl⟩
        simp at hout
        rcases hout with ⟨rfl, rfl⟩
        simp [popChoice]
    | pop1 =>
      cases held with
      | nil => simp [rawStep] at hs
      | cons b rest =>
        cases rest with
        | nil => simp [rawStep] at hs
        | cons c rest =>
          simp [rawStep] at hs
          rcases hs with ⟨rfl, rfl⟩
          simp at hout
          rcases hout with ⟨rfl, rfl⟩
          by_cases hb : b = c <;> simp [popChoice, hb]

#print axioms delete_next_output
#print axioms first_held_accessible

end StackSorting.Labelled
