import GeneralizedRangeLazy

/-! Literal zero-based infinite-family permutations and erasure-minimality
infrastructure. These definitions do not assume the family is forbidden. -/
namespace StackSorting.Generalized
namespace BasisFamily

def pairs (s m : Nat) : List Nat :=
  (List.range m).flatMap (fun j => [s+3+2*j, s+2*j])

def rho (s m : Nat) : List Nat :=
  [s+1, 0] ++ List.range' 2 (s-2) ++ pairs s m ++
    [2*s+1+2*m, 1, s+2*m] ++ List.range' (s+2+2*m) (s-1)

def core (s m : Nat) : List Nat := (s+1) :: pairs s m ++ [s+2*m]

theorem pairs_succ (s m : Nat) :
    pairs s (m+1) = pairs s m ++ [s+3+2*m, s+2*m] := by
  simp [pairs, List.range_succ]

theorem pairs_length (s m : Nat) : (pairs s m).length = 2*m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [pairs_succ, ih]; omega

theorem rho_length (s m : Nat) (hs : 2 ≤ s) : (rho s m).length = 2*s+2+2*m := by
  simp [rho, pairs_length]
  omega

theorem core_perm (s m : Nat) : (core s m).Perm (List.range' s (2*m+2)) := by
  induction m with
  | zero =>
    change [s+1, s].Perm [s, s+1]
    exact List.Perm.swap _ _ _
  | succ m ih =>
    have hp : [s+3+2*m, s+2*m, s+2*m+2].Perm [s+2*m, s+2*m+2, s+3+2*m] := by
      exact List.perm_append_comm (l₁ := [s+3+2*m]) (l₂ := [s+2*m, s+2*m+2])
    have h₁ : (core s (m+1)).Perm (core s m ++ [s+2*m+2, s+2*m+3]) := by
      have hz := List.Perm.append_left ((s+1) :: pairs s m) hp
      simpa [core, pairs_succ, Nat.mul_add, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz
    have h₂ : (core s m ++ [s+2*m+2, s+2*m+3]).Perm
        (List.range' s (2*m+2) ++ List.range' (s+2*m+2) 2) := by
      have he : [s+2*m+2, s+2*m+3] = List.range' (s+2*m+2) 2 := by
        simp [List.range'_succ, Nat.add_assoc]
      rw [← he]
      exact ih.append (List.Perm.refl _)
    have he : List.range' s (2*m+2) ++ List.range' (s+2*m+2) 2 =
        List.range' s (2*(m+1)+2) := by
      simp [Nat.mul_add, Nat.add_assoc]
    rw [← he]
    exact h₁.trans h₂

theorem shuffle_parts (b t a e : Nat) (low mid high : List Nat) :
    (b :: (low ++ mid ++ t :: a :: e :: high)).Perm
      ((low ++ [a]) ++ (b :: mid ++ [e]) ++ (t :: high)) := by
  have h₀ : (b :: (low ++ mid ++ t :: a :: e :: high)).Perm
      (low ++ b :: (mid ++ t :: a :: e :: high)) := by
    simpa only [List.append_assoc] using
      (List.perm_middle (a := b) (l₁ := low) (l₂ := mid ++ t :: a :: e :: high)).symm
  have h₁ : (low ++ b :: (mid ++ t :: a :: e :: high)).Perm
      (low ++ a :: b :: (mid ++ t :: e :: high)) := by
    have hz := List.Perm.append_left low
      (List.perm_middle (a := a) (l₁ := b :: mid ++ [t]) (l₂ := e :: high))
    simpa [List.append_assoc] using hz
  have h₂ : (low ++ a :: b :: (mid ++ t :: e :: high)).Perm
      ((low ++ [a]) ++ (b :: mid ++ [e]) ++ (t :: high)) := by
    have hz := List.Perm.append_left (low ++ a :: b :: mid) (List.Perm.swap e t high)
    simpa [List.append_assoc] using hz
  exact (h₀.trans h₁).trans h₂

theorem rho_perm (s m : Nat) (hs : 2 ≤ s) :
    (rho s m).Perm (List.range (2*s+2+2*m)) := by
  let low := 0 :: List.range' 2 (s-2)
  let high := List.range' (s+2+2*m) (s-1)
  have hlo : (low ++ [1]).Perm (List.range s) := by
    have hz := List.Perm.cons 0
      (List.perm_append_comm (l₁ := List.range' 2 (s-2)) (l₂ := [1]))
    have he : 0 :: 1 :: List.range' 2 (s-2) = List.range s := by
      have hn : s = (s-2)+1+1 := by omega
      rw [List.range_eq_range', hn]
      simp [List.range'_succ]
    simpa [low, he] using hz
  have hhi : ((2*s+1+2*m) :: high).Perm (List.range' (s+2*m+2) s) := by
    have hz := List.perm_append_comm (l₁ := [2*s+1+2*m]) (l₂ := high)
    have he : high ++ [2*s+1+2*m] = List.range' (s+2*m+2) s := by
      have hn : s = (s-1)+1 := by omega
      rw [hn, List.range'_concat]
      simp [high]
      omega
    rw [he] at hz
    exact hz
  have hp : (rho s m).Perm ((low ++ [1]) ++ core s m ++ ((2*s+1+2*m) :: high)) := by
    simpa [rho, core, low, high, List.append_assoc] using
      shuffle_parts (s+1) (2*s+1+2*m) 1 (s+2*m) low (pairs s m) high
  have hq := (hlo.append (core_perm s m)).append hhi
  have he : (List.range s ++ List.range' s (2*m+2)) ++ List.range' (s+2*m+2) s =
      List.range (2*s+2+2*m) := by
    rw [List.range_eq_range']
    have h₁ : List.range' 0 s ++ List.range' s (2*m+2) = List.range' 0 (s+(2*m+2)) := by
      simpa only [Nat.one_mul, Nat.zero_add] using
        (List.range'_append (s := 0) (m := s) (n := 2*m+2) (step := 1))
    rw [h₁]
    have hz := List.range'_append (s := 0) (m := s+(2*m+2)) (n := s) (step := 1)
    simpa [List.range_eq_range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.two_mul] using hz
  rw [he] at hq
  exact hp.trans hq

theorem rho_nodup (s m : Nat) (hs : 2 ≤ s) : (rho s m).Nodup :=
  (rho_perm s m hs).nodup_iff.mpr List.nodup_range

theorem rho_injective (s : Nat) (hs : 2 ≤ s) : Function.Injective (rho s) := by
  intro m k he
  have hl := congrArg List.length he
  rw [rho_length s m hs, rho_length s k hs] at hl
  omega

theorem rho_unbounded (s bound : Nat) (hs : 2 ≤ s) :
    ∃ m, bound < (rho s m).length := by
  refine ⟨bound, ?_⟩
  rw [rho_length s bound hs]
  omega

example : rho 3 0 = [4,0,2,7,1,3,5,6] := by decide
example : rho 3 1 = [4,0,2,6,3,9,1,5,7,8] := by decide

/-- Literal semantics of deleting just the token a, without silently changing
its numerical labels or confusing sorting and generation orientations. -/
def delete (a : Nat) (xs : List Nat) : List Nat := xs.filter (· != a)

def MinimalForbidden (r s n : Nat) (output : List Nat) : Prop :=
  output.Perm (List.range n) ∧ ¬ Run r s [] (List.range n) output [] ∧
    ∀ a, a < n → Run r s [] (delete a (List.range n)) (delete a output) []

theorem filter_delete (a : Nat) (xs : List Nat) (keep : Nat → Bool)
    (ha : keep a = false) : (delete a xs).filter keep = xs.filter keep := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x = a
    · subst x; simp [delete, ha] at ih ⊢; exact ih
    · simp only [delete] at ih
      cases hk : keep x <;> simp [delete, hx, hk, ih]

/-- Single-token minimality implies every proper retained-token subset is
sortable, at the exact original input/output semantics. -/
theorem MinimalForbidden.proper_filter {r s n : Nat} {output : List Nat}
    (h : MinimalForbidden r s n output) (keep : Nat → Bool)
    (proper : ∃ a, a < n ∧ keep a = false) :
    Run r s [] ((List.range n).filter keep) (output.filter keep) [] := by
  obtain ⟨a, ha, hk⟩ := proper
  have hr := (h.2.2 a ha).filter keep
  simpa [filter_delete a _ keep hk] using hr

/-- Relabelling any proper deletion gives a successful history as well;
standardizing the surviving labels is a particular choice of f. -/
theorem MinimalForbidden.proper_filter_map {r s n : Nat} {output : List Nat}
    (h : MinimalForbidden r s n output) (keep : Nat → Bool)
    (proper : ∃ a, a < n ∧ keep a = false) (f : Nat → Nat) :
    Run r s [] (((List.range n).filter keep).map f) ((output.filter keep).map f) [] := by
  simpa using (h.proper_filter keep proper).map f

#print axioms rho_length
#print axioms core_perm
#print axioms rho_perm
#print axioms rho_injective
#print axioms MinimalForbidden.proper_filter
end BasisFamily
end StackSorting.Generalized
