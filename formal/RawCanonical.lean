import RawNormalization

/-! # Canonical local choices preserve original-machine sortability -/
namespace StackSorting.Labelled

def CanSort (held input output : List Nat) : Prop :=
  ∃ ops, rawRun ops held = some ([], output) ∧ rawInputs ops = input

def canonicalInsert (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: rest => if a < b then a :: b :: rest else b :: a :: rest

theorem canSort_supply (held input output : List Nat)
    (h : CanSort held input output) : (held ++ input).Perm output := by
  obtain ⟨ops, hr, hi⟩ := h
  simpa [hi] using raw_complete_permutation ops held output hr

theorem canSort_nodup (held input output : List Nat)
    (h : CanSort held input output) (hs : output.Pairwise (· < ·)) :
    (held ++ input).Nodup := by
  exact (canSort_supply held input output h).nodup_iff.mpr
    (hs.imp (fun hlt => Nat.ne_of_lt hlt))

theorem canSort_pop (held input : List Nat) (a : Nat) (out : List Nat)
    (h : CanSort held input (a :: out)) (hs : (a :: out).Pairwise (· < ·))
    (ha : a ∈ held) :
    popChoice held a ≠ none ∧ CanSort (deleteToken a held) input out := by
  obtain ⟨ops, hr, hi⟩ := h
  refine ⟨first_held_accessible ops held a out hr ha (next_not_input ops held a out hr hs ha), ?_⟩
  obtain ⟨ops', hr', hi'⟩ := delete_next_output ops held a out hr hs ha
  exact ⟨ops', hr', hi'.trans hi⟩

/-- Reading the next output may be normalized to an immediate bypass. -/
theorem canSort_bypass (held input : List Nat) (a : Nat) (out : List Nat)
    (h : CanSort held (a :: input) (a :: out))
    (hs : (a :: out).Pairwise (· < ·)) (ha : a ∉ held) :
    CanSort held input out := by
  obtain ⟨ops, hr, hi⟩ := h
  have hn : (a :: out).Nodup := hs.imp (fun hlt => Nat.ne_of_lt hlt)
  have hfull := (raw_complete_permutation ops held (a :: out) hr).nodup_iff.mpr hn
  rw [hi] at hfull
  have hni := (List.nodup_cons.mp (List.nodup_append.mp hfull).2.1).1
  have hno := (List.nodup_cons.mp hn).1
  have hd := delete_run a ops held [] (a :: out) hr
  refine ⟨deleteTrace a ops held, ?_, ?_⟩
  · have eh : deleteToken a held = held := deleteToken_eq_self a held ha
    have eo : out.filter (· != a) = out := deleteToken_eq_self a out hno
    rw [eh] at hd
    simpa [deleteToken, eo] using hd.1
  · have ei : input.filter (· != a) = input := deleteToken_eq_self a input hni
    simpa [hi, deleteToken, ei] using hd.2

/-- If the next output is not held, the next input can be pushed in the
smaller-on-top slot while preserving a successful continuation. -/
theorem canSort_push (held input : List Nat) (a o : Nat) (out : List Nat)
    (h : CanSort held (a :: input) (o :: out))
    (hsorted : (o :: out).Pairwise (· < ·)) (ho : o ∉ held) :
    CanSort (canonicalInsert a held) input (o :: out) := by
  have hn := canSort_nodup held (a :: input) (o :: out) h hsorted
  have hanot : a ∉ held := by
    intro hm
    exact (List.nodup_append.mp hn).2.2 a hm a (by simp) rfl
  obtain ⟨ops, hr, hi⟩ := h
  cases ops with
  | nil => simp [rawInputs] at hi
  | cons op ops =>
    obtain ⟨u, emitted, tail, hstep, hrun, hout⟩ := raw_split_run op ops held [] _ hr
    cases op with
    | push0 b =>
      simp [rawInputs, rawIntroduced] at hi
      rcases hi with ⟨hba, hi⟩
      subst b
      simp [rawStep] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      simp at hout
      subst tail
      cases held with
      | nil => exact ⟨ops, hrun, hi⟩
      | cons b rest =>
        by_cases hab : a < b
        · exact ⟨ops, by simpa [canonicalInsert, hab] using hrun, hi⟩
        · have hba : b < a := by
            have hne : a ≠ b := by intro he; subst a; exact hanot (by simp)
            omega
          obtain ⟨ops', hv, hvinput⟩ := top_pair_exchange ops rest b a hba _ hrun hsorted
          exact ⟨ops', by simpa [canonicalInsert, hab] using hv, hvinput.trans hi⟩
    | push1 b =>
      simp [rawInputs, rawIntroduced] at hi
      rcases hi with ⟨hba, hi⟩
      subst b
      cases held with
      | nil => simp [rawStep] at hstep
      | cons b rest =>
        simp [rawStep] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        simp at hout
        subst tail
        by_cases hab : a < b
        · obtain ⟨ops', hv, hvinput⟩ := top_pair_exchange ops rest a b hab _ hrun hsorted
          exact ⟨ops', by simpa [canonicalInsert, hab] using hv, hvinput.trans hi⟩
        · exact ⟨ops, by simpa [canonicalInsert, hab] using hrun, hi⟩
    | pop0 =>
      cases held with
      | nil => simp [rawStep] at hstep
      | cons b rest =>
        simp [rawStep] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        simp at hout
        rcases hout with ⟨rfl, _⟩
        exact False.elim (ho (by simp))
    | pop1 =>
      cases held with
      | nil => simp [rawStep] at hstep
      | cons b rest =>
        cases rest with
        | nil => simp [rawStep] at hstep
        | cons d rest =>
          simp [rawStep] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          simp at hout
          rcases hout with ⟨rfl, _⟩
          exact False.elim (ho (by simp))

#print axioms canSort_pop
#print axioms canSort_bypass
#print axioms canSort_push

end StackSorting.Labelled
