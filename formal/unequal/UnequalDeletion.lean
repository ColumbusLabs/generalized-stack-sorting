import UnequalScript

/-! Every single deletion of the unequal-width family is generated.

Each case follows the matching subsection of §5 of
`docs/infinite-basis-unequal-draft.md`. The histories are built from literal
original-machine steps (`Good.record`, `Good.pop`, and so on). Each pop is
justified either by the token being in the protected prefix of at most `r-1`
tokens, or by the whole stack having at most `s` tokens. -/
namespace StackSorting.Generalized
namespace Unequal
open BasisFamily (delete)

variable {r s m : Nat}

def lateSeg (r s m : Nat) : List Nat := lateRelays r s m
def termSeg (r s m : Nat) : List Nat := List.range' (s+2*r-2+2*m) (s-r+1)

theorem family_segments (r s m : Nat) :
    family r s m = lowSeg s 0 (r-1) ++ (List.range' r (s-r) ++ (relaySeg r s 0 m ++
      ((2*s+r+2*m-1) :: (r-1) :: (lateSeg r s m ++ termSeg r s m)))) := by
  simp [family, lowPairs, relayPairs, lowSeg, relaySeg, lateSeg, termSeg,
    List.range_eq_range', List.append_assoc]

theorem mem_lateSeg {x : Nat} : x ∈ lateSeg r s m ↔ ∃ j, j < r - 1 ∧ x = s+2*(m+j) := by
  simp only [lateSeg, lateRelays, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

theorem mem_termSeg {x : Nat} :
    x ∈ termSeg r s m ↔ s+2*r-2+2*m ≤ x ∧ x < s+2*r-2+2*m + (s-r+1) := by
  simp only [termSeg, List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro hx; exact ⟨x-(s+2*r-2+2*m), by omega, by omega⟩

theorem length_lateSeg : (lateSeg r s m).length = r - 1 := by
  simp [lateSeg, lateRelays]

theorem length_termSeg : (termSeg r s m).length = s - r + 1 := by
  simp [termSeg]

theorem delete_eq_self {d : Nat} {l : List Nat} (h : ∀ x ∈ l, x ≠ d) : delete d l = l := by
  simp only [delete]
  exact List.filter_eq_self.mpr (fun x hx => by simpa using h x hx)

theorem mem_delete {d x : Nat} {l : List Nat} : x ∈ delete d l ↔ x ∈ l ∧ x ≠ d := by
  simp [delete, List.mem_filter]

theorem length_delete_le {d : Nat} {l : List Nat} : (delete d l).length ≤ l.length :=
  List.length_filter_le _ _

theorem delete_nodup {d : Nat} {l : List Nat} (h : l.Nodup) : (delete d l).Nodup :=
  List.Nodup.sublist List.filter_sublist h

theorem delete_family_length {d : Nat} (hr : 2 ≤ r) (hrs : r < s) (hd : d < 2*s+r+2*m) :
    (delete d (family r s m)).length = 2*s+r+2*m-1 := by
  have hp := (family_perm r s m hr hrs).filter (· != d)
  have hl := hp.length_eq
  have he : (List.filter (· != d) (List.range (2*s+r+2*m))).length =
      readCount d (2*s+r+2*m) := by
    have := length_delete_range' d (2*s+r+2*m)
    simpa [delete, List.range_eq_range'] using this
  simp only [delete] at hl ⊢
  rw [hl, he]
  simp [readCount, hd]

/-- The common terminal script when the deleted value lies before the
terminal record, inside the late relays, or inside the terminal values. -/
theorem tail_std {d next : Nat} {out : List Nat} {S : Nat → Prop}
    (hr : 2 ≤ r) (hrs : r < s)
    (h : Prog r s d next out ((2*s+r+2*m-1) :: (r-1) ::
      (delete d (lateSeg r s m) ++ delete d (termSeg r s m))) S)
    (hn : next ≤ 2*s+r+2*m-1) (hNd : 2*s+r+2*m-1 ≠ d) (hPd : r - 1 ≠ d)
    (hP : S (r-1) ∨ readCount d (2*s+r+2*m) - (out.length + 1) ≤ s)
    (hL : readCount d (2*s+r+2*m) - (out.length + 2) ≤ s) :
    Prog r s d (2*s+r+2*m) (out ++ ((2*s+r+2*m-1) :: (r-1) ::
      (delete d (lateSeg r s m) ++ delete d (termSeg r s m)))) [] S := by
  have h₁ := Prog.record (by omega) (by omega) h hn hNd
  have he : 2*s+r+2*m-1+1 = 2*s+r+2*m := by omega
  rw [he] at h₁
  have h₂ := Prog.pop (by omega) h₁ (by omega) hPd (by simpa using hP)
  have h₃ := Prog.drain (by omega) (delete d (lateSeg r s m)) h₂
    (by
      intro y hy
      obtain ⟨hy, hyd⟩ := mem_delete.mp hy
      obtain ⟨j, hj, rfl⟩ := mem_lateSeg.mp hy
      exact ⟨by omega, hyd⟩)
    (by simpa using hL)
  have h₃' : Prog r s d (2*s+r+2*m)
      (out ++ [2*s+r+2*m-1] ++ [r-1] ++ delete d (lateSeg r s m))
      (delete d (termSeg r s m) ++ []) S := by simpa using h₃
  have h₄ := Prog.drain (by omega) (delete d (termSeg r s m)) h₃'
    (by
      intro y hy
      obtain ⟨hy, hyd⟩ := mem_delete.mp hy
      have := mem_termSeg.mp hy
      exact ⟨by omega, hyd⟩)
    (by
      have hl := length_delete_le (d := d) (l := lateSeg r s m)
      rw [length_lateSeg] at hl
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
  simpa [List.append_assoc] using h₄

theorem length_lowSeg (s a c : Nat) : (lowSeg s a c).length = 2*c := by
  induction c generalizing a with
  | zero => simp [lowSeg]
  | succ c ih => rw [lowSeg_succ, List.length_append, ih]; simp; omega

theorem length_relaySeg (r s a c : Nat) : (relaySeg r s a c).length = 2*c := by
  induction c generalizing a with
  | zero => simp [relaySeg]
  | succ c ih => rw [relaySeg_succ, List.length_append, ih]; simp; omega

theorem Prog.not_out {r s d next x : Nat} {out rem : List Nat} {S : Nat → Prop}
    (h : Prog r s d next out rem S) (hx : x ∈ rem) : x ∉ out := by
  intro ho
  have hd := List.nodup_append.mp h.2
  exact hd.2.2 x ho x hx rfl

/-- Low pairs from `a`, possibly none, with every low protected. -/
theorem Prog.lowAll {d next : Nat} {out rem : List Nat} {S : Nat → Prop}
    (hr : 1 ≤ r) (hs : 0 < s) (hrs : r ≤ s) (a c : Nat)
    (h : Prog r s d next out (lowSeg s a c ++ rem) S) (hn : next ≤ s+1+2*a)
    (hi : ∀ i, a ≤ i → i < a + c → S i ∧ i ≠ d ∧ s+1+2*i ≠ d ∧ i < s) :
    ∃ next', Prog r s d next' (out ++ lowSeg s a c) rem S ∧
      (c = 0 → next' = next) ∧ (0 < c → next' = s+2*(a+c)) := by
  rcases c with _ | c
  · exact ⟨next, by simpa [lowSeg] using h, fun _ => rfl, fun h => absurd h (by omega)⟩
  · refine ⟨_, Prog.lowLoop hr hs hrs c h hn (fun i h₁ h₂ => hi i h₁ (by omega)),
      fun h => absurd h (by omega), fun _ => by omega⟩

/-- Relay pairs from `a`, possibly none, with no deletion inside. -/
theorem Prog.relayAll {d next : Nat} {out rem : List Nat} {S : Nat → Prop}
    (hr : 1 ≤ r) (hs : 0 < s) (hrs : r ≤ s) (a c : Nat)
    (h : Prog r s d next out (relaySeg r s a c ++ rem) S) (hn : next ≤ s+2*r-1+2*a)
    (hj : ∀ j, a ≤ j → j < a + c → s+2*r-1+2*j ≠ d ∧ s+2*j ≠ d ∧
      (S (s+2*j) ∨ readCount d (s+2*r+2*j) - (out.length + 2*(j-a) + 1) ≤ s)) :
    ∃ next', Prog r s d next' (out ++ relaySeg r s a c) rem S ∧
      (c = 0 → next' = next) ∧ (0 < c → next' = s+2*r-2+2*(a+c)) := by
  rcases c with _ | c
  · exact ⟨next, by simpa [relaySeg] using h, fun _ => rfl, fun h => absurd h (by omega)⟩
  · refine ⟨_, Prog.relayLoop hr hs hrs c h hn (fun j h₁ h₂ => hj j h₁ (by omega)),
      fun h => absurd h (by omega), fun _ => by omega⟩

/-- Terminal script when the permanent token itself was deleted. -/
theorem tail_P {next : Nat} {out : List Nat} {S : Nat → Prop}
    (hr : 2 ≤ r) (hrs : r < s)
    (h : Prog r s (r-1) next out ((2*s+r+2*m-1) :: (lateSeg r s m ++ termSeg r s m)) S)
    (hn : next ≤ 2*s+r+2*m-1)
    (hfin : out.length + 1 + (r-1) + (s-r+1) = 2*s+r+2*m-1) :
    Prog r s (r-1) (2*s+r+2*m) (out ++ ((2*s+r+2*m-1) :: (lateSeg r s m ++ termSeg r s m))) [] S := by
  have h₁ := Prog.record (by omega) (by omega) h hn (by omega)
  have he : 2*s+r+2*m-1+1 = 2*s+r+2*m := by omega
  rw [he] at h₁
  have hrc : readCount (r-1) (2*s+r+2*m) = 2*s+r+2*m-1 := by unfold readCount; split <;> omega
  have h₂ := Prog.drain (by omega) (lateSeg r s m) h₁
    (by intro y hy; obtain ⟨j, hj, rfl⟩ := mem_lateSeg.mp hy; exact ⟨by omega, by omega⟩)
    (by rw [hrc]; simp; omega)
  have h₂' : Prog r s (r-1) (2*s+r+2*m) (out ++ [2*s+r+2*m-1] ++ lateSeg r s m)
      (termSeg r s m ++ []) S := by simpa using h₂
  have h₃ := Prog.drain (by omega) (termSeg r s m) h₂'
    (by intro y hy; have := mem_termSeg.mp hy; exact ⟨by omega, by omega⟩)
    (by rw [hrc]; simp [length_lateSeg]; omega)
  simpa [List.append_assoc] using h₃

/-- Terminal script when the final record was deleted: the terminal values
become successive new maxima. -/
theorem tail_N {out : List Nat} {S : Nat → Prop}
    (hr : 2 ≤ r) (hrs : r < s)
    (h : Prog r s (2*s+r+2*m-1) (s+2*r-2+2*m) out ((r-1) :: (lateSeg r s m ++ termSeg r s m)) S)
    (hfin : out.length + 1 + (r-1) + (s-r+1) = 2*s+r+2*m-1) :
    Prog r s (2*s+r+2*m-1) (2*s+r+2*m-1) (out ++ ((r-1) :: (lateSeg r s m ++ termSeg r s m))) [] S := by
  have hrc : readCount (2*s+r+2*m-1) (s+2*r-2+2*m) = s+2*r-2+2*m := by
    unfold readCount; split <;> omega
  have h₁ := Prog.pop (by omega) h (by omega) (by omega) (Or.inr (by rw [hrc]; omega))
  have h₂ := Prog.drain (by omega) (lateSeg r s m) h₁
    (by intro y hy; obtain ⟨j, hj, rfl⟩ := mem_lateSeg.mp hy; exact ⟨by omega, by omega⟩)
    (by rw [hrc]; simp; omega)
  have h₂' : Prog r s (2*s+r+2*m-1) (s+2*r-2+2*m) (out ++ [r-1] ++ lateSeg r s m)
      (List.range' (s+2*r-2+2*m) (s-r+1) ++ []) S := by simpa [termSeg] using h₂
  have h₃ := Prog.records (by omega) (by omega) (s-r+1) h₂' (fun i hi => by omega)
  have he : s+2*r-2+2*m+(s-r+1) = 2*s+r+2*m-1 := by omega
  rw [he] at h₃
  simpa [termSeg, List.append_assoc] using h₃

theorem readCount_lt {d next : Nat} (h : d < next) : readCount d next = next - 1 := by
  unfold readCount; split <;> omega

theorem readCount_ge {d next : Nat} (h : next ≤ d) : readCount d next = next := by
  unfold readCount; split <;> omega

theorem delete_append (d : Nat) (a b : List Nat) : delete d (a ++ b) = delete d a ++ delete d b := by
  simp [delete, List.filter_append]

theorem delete_cons_self (d : Nat) (l : List Nat) : delete d (d :: l) = delete d l := by
  simp [delete]

theorem delete_cons_ne {d x : Nat} (l : List Nat) (h : x ≠ d) :
    delete d (x :: l) = x :: delete d l := by
  simp [delete, h]

theorem lowSeg_split (s a c k : Nat) (h₁ : a ≤ k) (h₂ : k < a + c) :
    lowSeg s a c = lowSeg s a (k-a) ++ ([s+1+2*k, k] ++ lowSeg s (k+1) (a+c-k-1)) := by
  have he := lowSeg_append s a (k-a) (c-(k-a))
  have hk : a + (k-a) = k := by omega
  have hc : k - a + (c - (k-a)) = c := by omega
  rw [hk, hc] at he
  have hs : c - (k-a) = (a+c-k-1) + 1 := by omega
  rw [hs, lowSeg_succ] at he
  exact he.symm

theorem relaySeg_split (r s a c k : Nat) (h₁ : a ≤ k) (h₂ : k < a + c) :
    relaySeg r s a c = relaySeg r s a (k-a) ++
      ([s+2*r-1+2*k, s+2*k] ++ relaySeg r s (k+1) (a+c-k-1)) := by
  have he := relaySeg_append r s a (k-a) (c-(k-a))
  have hk : a + (k-a) = k := by omega
  have hc : k - a + (c - (k-a)) = c := by omega
  rw [hk, hc] at he
  have hs : c - (k-a) = (a+c-k-1) + 1 := by omega
  rw [hs, relaySeg_succ] at he
  exact he.symm

theorem lowSeg_ne {s a c d : Nat} (h : ∀ i, a ≤ i → i < a + c → s+1+2*i ≠ d ∧ i ≠ d) :
    ∀ x ∈ lowSeg s a c, x ≠ d := by
  intro x hx
  obtain ⟨i, h₁, h₂, hx⟩ := mem_lowSeg.mp hx
  have := h i h₁ h₂
  omega

theorem relaySeg_ne {r s a c d : Nat}
    (h : ∀ j, a ≤ j → j < a + c → s+2*r-1+2*j ≠ d ∧ s+2*j ≠ d) :
    ∀ x ∈ relaySeg r s a c, x ≠ d := by
  intro x hx
  obtain ⟨j, h₁, h₂, hx⟩ := mem_relaySeg.mp hx
  have := h j h₁ h₂
  omega

theorem lateSeg_ne {d : Nat} (h : ∀ j, j < r - 1 → s+2*(m+j) ≠ d) :
    ∀ x ∈ lateSeg r s m, x ≠ d := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := mem_lateSeg.mp hx
  exact h j hj

theorem termSeg_ne {d : Nat} (h : d < s+2*r-2+2*m ∨ s+2*r-2+2*m+(s-r+1) ≤ d) :
    ∀ x ∈ termSeg r s m, x ≠ d := by
  intro x hx
  have := mem_termSeg.mp hx
  omega

theorem delete_range'_top (d : Nat) : delete d (List.range' 0 (d+1)) = List.range' 0 d := by
  rw [delete_range'_succ]
  have he : (if d = d then ([] : List Nat) else [d]) = [] := by simp
  rw [he, List.append_nil]
  exact delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega)

theorem delete_range'_above {d k : Nat} (h : k ≤ d) : delete d (List.range' 0 k) = List.range' 0 k :=
  delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega)

#print axioms family_segments
#print axioms delete_family_length
#print axioms tail_std
end Unequal
end StackSorting.Generalized
