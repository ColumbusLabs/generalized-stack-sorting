import Std

/-!
A finite interval critical-overlap theorem, independent of stack schedules.
Token labels and all endpoints are natural numbers. A cut `c` denotes the open
physical gap after endpoint `c` and before endpoint `c+1`; an interval is active
at that cut iff `left v ≤ c ∧ c < right v`. Endpoint counts use strict coverage.
-/
namespace StackSorting.IntervalCritical

abbrev Tokens := List Nat

structure Endpoints where
  left : Nat → Nat
  right : Nat → Nat

/-- The usual schedule endpoint hypotheses, stated only for the finite token list. -/
structure WellFormed (e : Endpoints) (U : Tokens) : Prop where
  nodup : U.Nodup
  proper : ∀ v ∈ U, e.left v < e.right v
  left_unique : ∀ u ∈ U, ∀ v ∈ U, e.left u = e.left v → u = v
  right_unique : ∀ u ∈ U, ∀ v ∈ U, e.right u = e.right v → u = v
  cross_distinct : ∀ u ∈ U, ∀ v ∈ U, e.left u ≠ e.right v

def Covers (e : Endpoints) (v t : Nat) : Prop :=
  e.left v < t ∧ t < e.right v

instance (e : Endpoints) (v t : Nat) : Decidable (Covers e v t) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Active (e : Endpoints) (v cut : Nat) : Prop :=
  e.left v ≤ cut ∧ cut < e.right v

instance (e : Endpoints) (v cut : Nat) : Decidable (Active e v cut) :=
  inferInstanceAs (Decidable (_ ∧ _))

def endpointCount (e : Endpoints) (U : Tokens) (t : Nat) : Nat :=
  U.countP (fun v => decide (Covers e v t))

def overlap (e : Endpoints) (U : Tokens) (cut : Nat) : Nat :=
  U.countP (fun v => decide (Active e v cut))

/-- Slot thresholds are strict: counts `r-1` and `s-1` are allowed. -/
def Eligible (e : Endpoints) (r s : Nat) (U : Tokens) (v : Nat) : Prop :=
  endpointCount e U (e.left v) < r ∧ endpointCount e U (e.right v) < s

/-- An existential successful endpoint-peeling sequence. No recognition bridge is assumed. -/
inductive Peelable (e : Endpoints) (r s : Nat) : Tokens → Prop where
  | nil : Peelable e r s []
  | step {U : Tokens} (v : Nat) (mem : v ∈ U) (eligible : Eligible e r s U v)
      (rest : Peelable e r s (U.erase v)) : Peelable e r s U

/-- Rejected, but deleting any one token makes this interval system peelable. -/
def Critical (e : Endpoints) (r s : Nat) (U : Tokens) : Prop :=
  ¬ Peelable e r s U ∧ ∀ v ∈ U, Peelable e r s (U.erase v)

theorem critical_no_eligible {e : Endpoints} {r s : Nat} {U : Tokens}
    (h : Critical e r s U) : ∀ v ∈ U, ¬ Eligible e r s U v := by
  intro v hv he
  exact h.1 (.step v hv he (h.2 v hv))

theorem not_peelable_of_no_eligible {e : Endpoints} {r s : Nat} {U : Tokens}
    (hne : U ≠ []) (h : ∀ v ∈ U, ¬ Eligible e r s U v) :
    ¬ Peelable e r s U := by
  intro hp
  cases hp with
  | nil => exact hne rfl
  | step v hv he _ => exact h v hv he

theorem own_left_not_covered (e : Endpoints) (v : Nat) : ¬ Covers e v (e.left v) := by
  simp [Covers]

theorem own_right_not_covered (e : Endpoints) (v : Nat) : ¬ Covers e v (e.right v) := by
  simp [Covers]

/-- A duplicate-free list of covering witnesses is a lower bound on the endpoint count. -/
theorem witnesses_le_count {e : Endpoints} {W U : Tokens} {t : Nat}
    (hn : W.Nodup) (hs : W ⊆ U) (hc : ∀ w ∈ W, Covers e w t) :
    W.length ≤ endpointCount e U t := by
  rw [endpointCount, List.countP_eq_length_filter]
  apply hn.length_le_of_subset
  intro w hw
  exact List.mem_filter.mpr ⟨hs hw, by simpa using hc w hw⟩

/-- Deleting a token that does not cover an endpoint leaves its count unchanged. -/
theorem endpointCount_erase_of_not_covered {e : Endpoints} {U : Tokens} {v t : Nat}
    (hn : U.Nodup) (hc : ¬ Covers e v t) :
    endpointCount e (U.erase v) t = endpointCount e U t := by
  rw [endpointCount, endpointCount, hn.erase_eq_filter v, List.countP_filter]
  apply List.countP_congr
  intro w hw
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun hEq => hc (hEq ▸ h)⟩

/-- Once a deletion leaves `k` covering witnesses at every affected endpoint,
all forbidden thresholds at most `k` stay forbidden. -/
theorem forbidden_survives {e : Endpoints} {U : Tokens} {v k q t : Nat}
    (hn : U.Nodup) (hq : q ≤ k)
    (hw : ∀ t, Covers e v t → k ≤ endpointCount e (U.erase v) t)
    (hf : q ≤ endpointCount e U t) :
    q ≤ endpointCount e (U.erase v) t := by
  by_cases hc : Covers e v t
  · exact Nat.le_trans hq (hw t hc)
  · rw [endpointCount_erase_of_not_covered hn hc]
    exact hf

/-- Such a witness deletion preserves ineligibility of every remaining token. -/
theorem no_eligible_survives {e : Endpoints} {U : Tokens} {v k r s : Nat}
    (hn : U.Nodup) (hr : r ≤ k) (hs : s ≤ k)
    (hw : ∀ t, Covers e v t → k ≤ endpointCount e (U.erase v) t)
    (he : ∀ u ∈ U, ¬ Eligible e r s U u) :
    ∀ u ∈ U.erase v, ¬ Eligible e r s (U.erase v) u := by
  intro u hu hallow
  have hforbid := he u (List.mem_of_mem_erase hu)
  unfold Eligible at hforbid hallow
  by_cases hl : r ≤ endpointCount e U (e.left u)
  · have h := forbidden_survives hn hr hw hl
    omega
  · have hh : s ≤ endpointCount e U (e.right u) := by omega
    have h := forbidden_survives hn hs hw hh
    omega

/-- If more than `2*k` tokens are active, one can be deleted while leaving at
least `k` strict covering witnesses at every endpoint it used to cover.
The selected token has at least `k` earlier starts and at least `k` later ends.
This statement protects every natural time, not just another token's endpoints. -/
theorem overlap_witness {e : Endpoints} {U : Tokens} {cut k : Nat}
    (wf : WellFormed e U) (hk : 2 * k < overlap e U cut) :
    ∃ v ∈ U, ∀ t, Covers e v t → k ≤ endpointCount e (U.erase v) t := by
  let K := U.filter (fun v => decide (Active e v cut))
  let le : Nat → Nat → Bool := fun u v => decide (e.left u ≤ e.left v)
  let S := K.mergeSort le
  have hSsub : S ⊆ U := by
    intro v hv
    have hK : v ∈ K := List.mem_mergeSort.mp hv
    exact (List.mem_filter.mp hK).1
  have hSact : ∀ v ∈ S, Active e v cut := by
    intro v hv
    have hK : v ∈ K := List.mem_mergeSort.mp hv
    simpa using (List.mem_filter.mp hK).2
  have hSn : S.Nodup := by
    exact (List.mergeSort_perm K le).nodup_iff.mpr (wf.nodup.filter _)
  have hSlen : 2 * k < S.length := by
    simpa [S, K, overlap, List.countP_eq_length_filter] using hk
  have hSsort : S.Pairwise (fun u v => e.left u ≤ e.left v) := by
    have hp := List.pairwise_mergeSort (le := le)
      (by intro u v w h₁ h₂; simp only [le, decide_eq_true_eq] at *; omega)
      (by intro u v; simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) K
    simpa [S, le] using hp
  let L := S.take k
  let M := S.drop k
  have hMn : M.Nodup := hSn.drop
  have hMlen : k < M.length := by
    dsimp [M]
    rw [List.length_drop]
    omega
  have hMne : M ≠ [] := by
    intro h
    simp [h] at hMlen
  let v := M.minOn e.right hMne
  have hvM : v ∈ M := List.minOn_mem
  have hMsub : M ⊆ S := List.drop_subset k S
  have hLsub : L ⊆ S := List.take_subset k S
  have hvU : v ∈ U := hSsub (hMsub hvM)
  have hLlen : L.length = k := by
    dsimp [L]
    rw [List.length_take]
    omega
  have hLleft : ∀ w ∈ L, e.left w < e.left v := by
    intro w hw
    have hle := hSsort.rel_of_mem_take_of_mem_drop hw hvM
    have hne := hSn.rel_of_mem_take_of_mem_drop hw hvM
    have hneq : e.left w ≠ e.left v := by
      intro heq
      exact hne (wf.left_unique w (hSsub (hLsub hw)) v hvU heq)
    omega
  have hLerase : L ⊆ U.erase v := by
    intro w hw
    apply (List.mem_erase_of_ne (by
      intro heq
      have hlt := hLleft w hw
      subst w
      omega)).mpr
    exact hSsub (hLsub hw)
  let R := M.erase v
  have hRlen : k ≤ R.length := by
    dsimp [R]
    rw [List.length_erase_of_mem hvM]
    omega
  have hRn : R.Nodup := List.Nodup.erase v hMn
  have hRsub : R ⊆ M := List.erase_subset
  have hRerase : R ⊆ U.erase v := by
    intro w hw
    have hne : w ≠ v := (hMn.mem_erase_iff.mp hw).1
    exact (List.mem_erase_of_ne hne).mpr (hSsub (hMsub (hRsub hw)))
  have hRright : ∀ w ∈ R, e.right v < e.right w := by
    intro w hw
    have hle : e.right v ≤ e.right w := List.apply_minOn_le_of_mem (hRsub hw)
    have hne : w ≠ v := (hMn.mem_erase_iff.mp hw).1
    have hneq : e.right v ≠ e.right w := by
      intro heq
      exact hne (wf.right_unique v hvU w (hSsub (hMsub (hRsub hw))) heq).symm
    omega
  refine ⟨v, hvU, ?_⟩
  intro t hvt
  by_cases ht : t ≤ cut
  · have hcover : ∀ w ∈ L, Covers e w t := by
      intro w hw
      have ha := hSact w (hLsub hw)
      have hl := hLleft w hw
      dsimp [Covers, Active] at *
      omega
    have hLn : L.Nodup := hSn.take
    have hcount : L.length ≤ endpointCount e (U.erase v) t :=
      witnesses_le_count hLn hLerase hcover
    simpa [hLlen] using hcount
  · have hcover : ∀ w ∈ R, Covers e w t := by
      intro w hw
      have ha := hSact w (hMsub (hRsub hw))
      have hr := hRright w hw
      dsimp [Covers, Active] at *
      omega
    exact Nat.le_trans hRlen (witnesses_le_count hRn hRerase hcover)

/-- A finite vertex-critical rejected endpoint system has overlap at most
`2 * max r s`. The positivity hypotheses exclude the zero-threshold singleton.
This is the interval theorem only: it does not identify peeling with physical
stack realization, or identify permutation-basis deletions with interval deletion. -/
theorem critical_overlap_le {e : Endpoints} {U : Tokens} {r s : Nat}
    (wf : WellFormed e U) (_hr : 0 < r) (hs : 0 < s)
    (hc : Critical e r s U) (cut : Nat) :
    overlap e U cut ≤ 2 * max r s := by
  by_cases hnot : overlap e U cut ≤ 2 * max r s
  · exact hnot
  have hlarge : 2 * max r s < overlap e U cut := by omega
  obtain ⟨v, hv, hw⟩ := overlap_witness wf hlarge
  have hn := no_eligible_survives wf.nodup (Nat.le_max_left r s)
    (Nat.le_max_right r s) hw (critical_no_eligible hc)
  have hlen : 2 * max r s < U.length :=
    Nat.lt_of_lt_of_le hlarge (List.countP_le_length)
  have hremain : U.erase v ≠ [] := by
    intro heq
    have hh := List.length_erase_of_mem hv
    simp [heq] at hh
    omega
  exact False.elim (not_peelable_of_no_eligible hremain hn (hc.2 v hv))

/-- The `(3,3)` interval specialization is a nonrecord overlap bound of six.
An additional record interval and the permutation/schedule bridges are outside
this module. -/
theorem critical_three_three_overlap_le {e : Endpoints} {U : Tokens}
    (wf : WellFormed e U) (hc : Critical e 3 3 U) (cut : Nat) :
    overlap e U cut ≤ 6 := by
  simpa using critical_overlap_le wf (by decide : 0 < 3) (by decide : 0 < 3) hc cut

#print axioms critical_no_eligible
#print axioms witnesses_le_count
#print axioms endpointCount_erase_of_not_covered
#print axioms forbidden_survives
#print axioms no_eligible_survives
#print axioms overlap_witness
#print axioms critical_overlap_le
#print axioms critical_three_three_overlap_le
end StackSorting.IntervalCritical
