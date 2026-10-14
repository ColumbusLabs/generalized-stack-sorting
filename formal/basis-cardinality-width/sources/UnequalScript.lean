import UnequalReach

/-! Scripted construction of accepting histories.

`St` adds a protected-set invariant to a partial history: the protected
prefix has length at most `r-1`, and every not-yet-output token of the
declared set `S` is still in it. `Prog` also records the remaining target
word, so every "not yet output" side condition follows from distinctness. -/
namespace StackSorting.Generalized
namespace Unequal
open BasisFamily (delete)

def St (r s d next : Nat) (out : List Nat) (S : Nat → Prop) : Prop :=
  ∃ prot, Good r s d next prot out ∧ prot.length ≤ r - 1 ∧
    ∀ x, S x → x ∉ out → x ∈ prot

def Prog (r s d next : Nat) (out rem : List Nat) (S : Nat → Prop) : Prop :=
  St r s d next out S ∧ (out ++ rem).Nodup

variable {r s d : Nat}

theorem Prog.record {next a : Nat} {out rem : List Nat} {S : Nat → Prop}
    (hr : 1 ≤ r) (hs : 0 < s) (h : Prog r s d next out (a :: rem) S)
    (ha : next ≤ a) (had : a ≠ d) : Prog r s d (a+1) (out ++ [a]) rem S := by
  obtain ⟨⟨prot, hg, hl, hS⟩, hn⟩ := h
  refine ⟨⟨prot, hg.record (by omega) hs ha had, hl, ?_⟩, by simpa using hn⟩
  intro x hx hxo
  exact hS x hx (fun h' => hxo (List.mem_append_left _ h'))

theorem Prog.pop {next y : Nat} {out rem : List Nat} {S : Nat → Prop}
    (hrs : r ≤ s) (h : Prog r s d next out (y :: rem) S) (hy : y < next) (hyd : y ≠ d)
    (hacc : S y ∨ readCount d next - out.length ≤ s) :
    Prog r s d next (out ++ [y]) rem S := by
  obtain ⟨⟨prot, hg, hl, hS⟩, hn⟩ := h
  have hyo : y ∉ out := not_mem_prefix hn
  have hacc' : y ∈ prot ∨ readCount d next - out.length ≤ s := by
    rcases hacc with h' | h'
    · exact Or.inl (hS y h' hyo)
    · exact Or.inr h'
  obtain ⟨prot', hg', hl', hm'⟩ := hg.pop hy hyd hyo hl hrs hacc'
  refine ⟨⟨prot', hg', by omega, ?_⟩, by simpa using hn⟩
  intro x hx hxo
  have hxo' : x ∉ out := fun h' => hxo (List.mem_append_left _ h')
  have hxy : x ≠ y := fun h' => hxo (by simp [h'])
  exact hm' x (hS x hx hxo') hxy

/-- Protect the whole current stack once it has at most `r-1` tokens. -/
theorem Prog.reprotect {next : Nat} {out rem : List Nat} {S : Nat → Prop}
    (h : Prog r s d next out rem S) (hh : readCount d next - out.length ≤ r - 1) :
    Prog r s d next out rem (fun x => x < next ∧ x ≠ d ∧ x ∉ out) := by
  obtain ⟨⟨prot, hg, _, _⟩, hn⟩ := h
  obtain ⟨prot', hg', hl', hm'⟩ := hg.reprotect
  refine ⟨⟨prot', hg', by omega, ?_⟩, hn⟩
  intro x hx _
  exact hm' x hx.1 hx.2.1 hx.2.2

theorem Prog.weaken {next : Nat} {out rem : List Nat} {S S' : Nat → Prop}
    (h : Prog r s d next out rem S) (hS : ∀ x, S' x → S x) :
    Prog r s d next out rem S' := by
  obtain ⟨⟨prot, hg, hl, hm⟩, hn⟩ := h
  exact ⟨⟨prot, hg, hl, fun x hx hxo => hm x (hS x hx) hxo⟩, hn⟩

/-- Drain held tokens while the whole stack has at most `s` tokens. -/
theorem Prog.drain {next : Nat} {S : Nat → Prop} (hrs : r ≤ s) :
    ∀ (seg : List Nat) {out rem : List Nat}, Prog r s d next out (seg ++ rem) S →
      (∀ y ∈ seg, y < next ∧ y ≠ d) → readCount d next - out.length ≤ s →
      Prog r s d next (out ++ seg) rem S := by
  intro seg
  induction seg with
  | nil => intro out rem h _ _; simpa using h
  | cons y seg ih =>
    intro out rem h hseg hh
    have hy := hseg y (by simp)
    have h₁ := Prog.pop hrs (by simpa using h) hy.1 hy.2 (Or.inr hh)
    have h₂ := ih h₁ (fun z hz => hseg z (by simp [hz])) (by simp; omega)
    simpa using h₂

/-- Successive new maxima `a,a+1,...,a+c-1` pass through slot zero. -/
theorem Prog.records {S : Nat → Prop} (hr : 1 ≤ r) (hs : 0 < s) :
    ∀ (c : Nat) {a : Nat} {out rem : List Nat},
      Prog r s d a out (List.range' a c ++ rem) S → (∀ i, i < c → a + i ≠ d) →
      Prog r s d (a+c) (out ++ List.range' a c) rem S := by
  intro c
  induction c with
  | zero => intro a out rem h _; simpa using h
  | succ c ih =>
    intro a out rem h hd
    have h₀ : Prog r s d a out (a :: (List.range' (a+1) c ++ rem)) S := by
      simpa [List.range'_succ] using h
    have h₁ := Prog.record hr hs h₀ (Nat.le_refl a) (by simpa using hd 0 (by omega))
    have h₂ := ih h₁ (fun i hi => by have := hd (i+1) (by omega); omega)
    have he : a + 1 + c = a + (c+1) := by omega
    rw [he] at h₂
    simpa [List.range'_succ, List.append_assoc] using h₂

theorem Prog.start {k : Nat} {S : Nat → Prop} (prot rest W : List Nat)
    (hW : W.Nodup) (hk : readCount d k ≤ r)
    (hp : (prot ++ rest).Perm (delete d (List.range' 0 k)))
    (hprot : prot.length ≤ r - 1) (hS : ∀ x, S x → x ∈ prot) :
    Prog r s d k [] W S :=
  ⟨⟨prot, Good.prefill prot rest hk hp, hprot, fun x hx _ => hS x hx⟩, by simpa using hW⟩

theorem Prog.finish {next : Nat} {out : List Nat} {S : Nat → Prop}
    (h : Prog r s d next out [] S) (hl : out.length = readCount d next) :
    Run r s [] (delete d (List.range' 0 next)) out [] := by
  obtain ⟨⟨prot, hg, _, _⟩, _⟩ := h
  exact hg.finish hl

/-! Family segments indexed by `range'`, so loops can be split anywhere. -/

def lowSeg (s a c : Nat) : List Nat :=
  (List.range' a c).flatMap (fun i => [s+1+2*i, i])

def relaySeg (r s a c : Nat) : List Nat :=
  (List.range' a c).flatMap (fun j => [s+2*r-1+2*j, s+2*j])

theorem lowSeg_succ (s a c : Nat) :
    lowSeg s a (c+1) = [s+1+2*a, a] ++ lowSeg s (a+1) c := by
  simp [lowSeg, List.range'_succ]

theorem relaySeg_succ (r s a c : Nat) :
    relaySeg r s a (c+1) = [s+2*r-1+2*a, s+2*a] ++ relaySeg r s (a+1) c := by
  simp [relaySeg, List.range'_succ]

theorem lowSeg_append (s a b c : Nat) :
    lowSeg s a b ++ lowSeg s (a+b) c = lowSeg s a (b+c) := by
  have h := List.range'_append (s := a) (m := b) (n := c) (step := 1)
  simp only [Nat.one_mul] at h
  simp only [lowSeg, ← List.flatMap_append, h]

theorem relaySeg_append (r s a b c : Nat) :
    relaySeg r s a b ++ relaySeg r s (a+b) c = relaySeg r s a (b+c) := by
  have h := List.range'_append (s := a) (m := b) (n := c) (step := 1)
  simp only [Nat.one_mul] at h
  simp only [relaySeg, ← List.flatMap_append, h]

theorem mem_lowSeg {s a c x : Nat} :
    x ∈ lowSeg s a c ↔ ∃ i, a ≤ i ∧ i < a + c ∧ (x = s+1+2*i ∨ x = i) := by
  simp only [lowSeg, List.mem_flatMap, List.mem_range', List.mem_cons, List.not_mem_nil]
  constructor
  · rintro ⟨i, ⟨k, hk, rfl⟩, hx⟩
    refine ⟨a+k, by omega, by omega, ?_⟩
    simp at hx; omega
  · rintro ⟨i, h₁, h₂, hx⟩
    exact ⟨i, ⟨i-a, by omega, by omega⟩, by omega⟩

theorem mem_relaySeg {r s a c x : Nat} :
    x ∈ relaySeg r s a c ↔ ∃ j, a ≤ j ∧ j < a + c ∧ (x = s+2*r-1+2*j ∨ x = s+2*j) := by
  simp only [relaySeg, List.mem_flatMap, List.mem_range', List.mem_cons, List.not_mem_nil]
  constructor
  · rintro ⟨j, ⟨k, hk, rfl⟩, hx⟩
    refine ⟨a+k, by omega, by omega, ?_⟩
    simp at hx; omega
  · rintro ⟨j, h₁, h₂, hx⟩
    exact ⟨j, ⟨j-a, by omega, by omega⟩, by omega⟩

/-- A run of low pairs whose lows are all protected and none deleted. -/
theorem Prog.lowLoop {S : Nat → Prop} (hr : 1 ≤ r) (hs : 0 < s) (hrs : r ≤ s) :
    ∀ (c : Nat) {a next : Nat} {out rem : List Nat},
      Prog r s d next out (lowSeg s a (c+1) ++ rem) S → next ≤ s+1+2*a →
      (∀ i, a ≤ i → i ≤ a + c → S i ∧ i ≠ d ∧ s+1+2*i ≠ d ∧ i < s) →
      Prog r s d (s+2*(a+c+1)) (out ++ lowSeg s a (c+1)) rem S := by
  intro c
  induction c with
  | zero =>
    intro a next out rem h hn hi
    have hA := hi a (Nat.le_refl a) (by omega)
    have h₀ : Prog r s d next out ((s+1+2*a) :: a :: rem) S := by
      simpa [lowSeg_succ, lowSeg] using h
    have h₁ := Prog.record hr hs h₀ hn hA.2.2.1
    have h₂ := Prog.pop hrs h₁ (by omega) hA.2.1 (Or.inl hA.1)
    have he : s+1+2*a+1 = s+2*(a+0+1) := by omega
    rw [he] at h₂
    simpa [lowSeg_succ, lowSeg, List.append_assoc] using h₂
  | succ c ih =>
    intro a next out rem h hn hi
    have hA := hi a (Nat.le_refl a) (by omega)
    have h₀ : Prog r s d next out ((s+1+2*a) :: a :: (lowSeg s (a+1) (c+1) ++ rem)) S := by
      simpa [lowSeg_succ, List.append_assoc] using h
    have h₁ := Prog.record hr hs h₀ hn hA.2.2.1
    have h₂ := Prog.pop hrs h₁ (by omega) hA.2.1 (Or.inl hA.1)
    have h₃ := ih (a := a+1) h₂ (by omega) (fun i h₁ h₂ => hi i (by omega) (by omega))
    have he : s+2*(a+1+c+1) = s+2*(a+(c+1)+1) := by omega
    rw [he] at h₃
    simpa [lowSeg_succ, List.append_assoc] using h₃

/-- A run of ordinary relay steps with no deletion inside. The relay output
of step `j` happens at the stated height bound. -/
theorem Prog.relayLoop {S : Nat → Prop} (hr : 1 ≤ r) (hs : 0 < s) (hrs : r ≤ s) :
    ∀ (c : Nat) {a next : Nat} {out rem : List Nat},
      Prog r s d next out (relaySeg r s a (c+1) ++ rem) S → next ≤ s+2*r-1+2*a →
      (∀ j, a ≤ j → j ≤ a + c → s+2*r-1+2*j ≠ d ∧ s+2*j ≠ d ∧
        (S (s+2*j) ∨ readCount d (s+2*r+2*j) - (out.length + 2*(j-a) + 1) ≤ s)) →
      Prog r s d (s+2*r-2+2*(a+c+1)) (out ++ relaySeg r s a (c+1)) rem S := by
  intro c
  induction c with
  | zero =>
    intro a next out rem h hn hj
    have hA := hj a (Nat.le_refl a) (by omega)
    have h₀ : Prog r s d next out ((s+2*r-1+2*a) :: (s+2*a) :: rem) S := by
      simpa [relaySeg_succ, relaySeg] using h
    have h₁ := Prog.record hr hs h₀ hn hA.1
    have hn₁ : s+2*r-1+2*a+1 = s+2*r+2*a := by omega
    rw [hn₁] at h₁
    have h₂ := Prog.pop hrs h₁ (by omega) hA.2.1 (by simpa using hA.2.2)
    have he : s+2*r+2*a = s+2*r-2+2*(a+0+1) := by omega
    rw [he] at h₂
    simpa [relaySeg_succ, relaySeg, List.append_assoc] using h₂
  | succ c ih =>
    intro a next out rem h hn hj
    have hA := hj a (Nat.le_refl a) (by omega)
    have h₀ : Prog r s d next out
        ((s+2*r-1+2*a) :: (s+2*a) :: (relaySeg r s (a+1) (c+1) ++ rem)) S := by
      simpa [relaySeg_succ, List.append_assoc] using h
    have h₁ := Prog.record hr hs h₀ hn hA.1
    have hn₁ : s+2*r-1+2*a+1 = s+2*r+2*a := by omega
    rw [hn₁] at h₁
    have h₂ := Prog.pop hrs h₁ (by omega) hA.2.1 (by simpa using hA.2.2)
    have h₃ := ih (a := a+1) h₂ (by omega) (by
      intro j h₁ h₂
      have hJ := hj j (by omega) (by omega)
      refine ⟨hJ.1, hJ.2.1, ?_⟩
      rcases hJ.2.2 with hJ | hJ
      · exact Or.inl hJ
      · refine Or.inr ?_
        simp only [List.length_append, List.length_cons, List.length_nil]
        have : out.length + 2*(j-a) + 1 = out.length + (1+1) + 2*(j-(a+1)) + 1 := by omega
        omega)
    have he : s+2*r-2+2*(a+1+c+1) = s+2*r-2+2*(a+(c+1)+1) := by omega
    rw [he] at h₃
    simpa [relaySeg_succ, List.append_assoc] using h₃

#print axioms Prog.drain
#print axioms Prog.records
#print axioms Prog.lowLoop
#print axioms Prog.relayLoop
end Unequal
end StackSorting.Generalized
