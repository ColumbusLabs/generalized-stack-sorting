import UnequalObstruction

/-! Constructive partial histories for single deletions.

`Reach r s d next prot rest out` is a literal original-machine history from
the empty stack. It has read every value below `next` except the deleted value
`d`, has output `out`, and has stack `prot ++ rest`. Non-record tokens are
inserted at slot `prot.length` (just below the protected prefix), and a
requested new maximum is pushed and popped at slot zero. The stack height is
determined by the counts alone, so every accessibility side condition becomes
arithmetic. -/
namespace StackSorting.Generalized
namespace Unequal
open BasisFamily (delete)

def Reach (r s d next : Nat) (prot rest out : List Nat) : Prop :=
  Run r s [] (delete d (List.range' 0 next)) out (prot ++ rest)

def Good (r s d next : Nat) (prot out : List Nat) : Prop :=
  ∃ rest, Reach r s d next prot rest out

/-- How many values have been read once everything below `next` except `d`
has been read. -/
def readCount (d next : Nat) : Nat := next - (if d < next then 1 else 0)

theorem delete_range'_succ (d k : Nat) :
    delete d (List.range' 0 (k+1)) =
      delete d (List.range' 0 k) ++ (if k = d then [] else [k]) := by
  rw [List.range'_concat]
  by_cases h : k = d <;> simp [delete, List.filter_append, h]

theorem length_delete_range' (d next : Nat) :
    (delete d (List.range' 0 next)).length = readCount d next := by
  induction next with
  | zero => simp [delete, readCount]
  | succ k ih =>
    rw [delete_range'_succ, List.length_append, ih]
    unfold readCount
    by_cases h : k = d
    · subst h
      have h₁ : ¬ k < k := Nat.lt_irrefl k
      have h₂ : k < k + 1 := Nat.lt_succ_self k
      simp [h₁, h₂]
    · by_cases hd : d < k
      · have h₂ : d < k + 1 := by omega
        simp [hd, h₂, h] <;> omega
      · have h₂ : ¬ d < k + 1 := by omega
        simp [hd, h₂, h]

theorem mem_delete_range' {d next x : Nat} :
    x ∈ delete d (List.range' 0 next) ↔ x < next ∧ x ≠ d := by
  simp [delete, List.mem_filter, List.mem_range']

theorem Reach.height {r s d next : Nat} {prot rest out : List Nat}
    (h : Reach r s d next prot rest out) :
    (prot ++ rest).length + out.length = readCount d next := by
  have hp := h.supply
  have hl := hp.length_eq
  simp only [List.nil_append, List.length_append, length_delete_range'] at hl
  simp only [List.length_append]
  omega

theorem Reach.mem {r s d next x : Nat} {prot rest out : List Nat}
    (h : Reach r s d next prot rest out) (hx : x < next) (hxd : x ≠ d)
    (hxo : x ∉ out) : x ∈ prot ++ rest := by
  have hm : x ∈ [] ++ delete d (List.range' 0 next) := by
    simpa using (mem_delete_range' (d := d) (next := next) (x := x)).mpr ⟨hx, hxd⟩
  have hm' := h.supply.mem_iff.mp hm
  simp only [List.mem_append] at hm'
  rcases hm' with hm' | hm'
  · exact absurd hm' hxo
  · simpa [List.mem_append] using hm'

theorem Good.push_one {r s d k : Nat} {prot out : List Nat}
    (h : Good r s d k prot out) (hp : prot.length < r) :
    Good r s d (k+1) prot out := by
  obtain ⟨rest, hr⟩ := h
  by_cases hk : k = d
  · refine ⟨rest, ?_⟩
    unfold Reach at hr ⊢
    rw [delete_range'_succ]
    simpa [hk] using hr
  · refine ⟨k :: rest, ?_⟩
    have hs := Run.single (Step.push (r := r) (s := s) prot rest k hp)
    have hz := hr.append hs
    unfold Reach
    rw [delete_range'_succ]
    simpa [hk] using hz

theorem Good.read {r s d k : Nat} {prot out : List Nat} (hp : prot.length < r) :
    ∀ c, Good r s d k prot out → Good r s d (k+c) prot out := by
  intro c
  induction c with
  | zero => intro h; simpa using h
  | succ c ih =>
    intro h
    have := (ih h).push_one hp
    simpa [Nat.add_assoc] using this

/-- Read a whole record batch below the protected prefix, then pass the new
maximum through slot zero. Its transient height is counted. -/
theorem Good.record {r s d next a : Nat} {prot out : List Nat}
    (h : Good r s d next prot out) (hp : prot.length < r) (hs : 0 < s)
    (ha : next ≤ a) (had : a ≠ d) : Good r s d (a+1) prot (out ++ [a]) := by
  have hr := Good.read (s := s) (d := d) (k := next) (out := out) hp (a - next) h
  have he : next + (a - next) = a := by omega
  rw [he] at hr
  obtain ⟨rest, hrest⟩ := hr
  refine ⟨rest, ?_⟩
  have hpush := Step.push (r := r) (s := s) [] (prot ++ rest) a (by simpa using Nat.lt_of_le_of_lt (Nat.zero_le _) hp)
  have hpop := Step.pop (r := r) (s := s) [] (prot ++ rest) a (by simpa using hs)
  have hpair := Run.cons hpush (Run.single hpop)
  have hz := hrest.append hpair
  unfold Reach
  rw [delete_range'_succ]
  simpa [had] using hz

/-- Output an already-held value, either from the protected prefix or from
anywhere in a stack of height at most `s`. -/
theorem Good.pop {r s d next y : Nat} {prot out : List Nat}
    (h : Good r s d next prot out) (hy : y < next) (hyd : y ≠ d) (hyo : y ∉ out)
    (hprot : prot.length ≤ r - 1) (hrs : r ≤ s)
    (hacc : y ∈ prot ∨ readCount d next - out.length ≤ s) :
    ∃ prot', Good r s d next prot' (out ++ [y]) ∧ prot'.length ≤ prot.length ∧
      ∀ x ∈ prot, x ≠ y → x ∈ prot' := by
  obtain ⟨rest, hr⟩ := h
  have hheight := hr.height
  by_cases hyp : y ∈ prot
  · obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hyp
    have hlen : p₁.length < s := by simp at hprot; omega
    have hstep := Step.pop (r := r) (s := s) p₁ (p₂ ++ rest) y hlen
    refine ⟨p₁ ++ p₂, ⟨rest, ?_⟩, by simp, ?_⟩
    · unfold Reach at hr
      rw [List.append_assoc, List.cons_append] at hr
      have hz := hr.append (Run.single hstep)
      unfold Reach
      simpa [List.append_assoc] using hz
    · intro x hx hxy
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      rcases hx with hx | hx | hx
      · exact Or.inl hx
      · exact absurd hx hxy
      · exact Or.inr hx
  · have hm := hr.mem hy hyd hyo
    have hyr : y ∈ rest := by
      simp only [List.mem_append] at hm
      rcases hm with hm | hm
      · exact absurd hm hyp
      · exact hm
    have hacc' : (prot ++ rest).length ≤ s := by
      rcases hacc with hacc | hacc
      · exact absurd hacc hyp
      · omega
    obtain ⟨q₁, q₂, rfl⟩ := List.append_of_mem hyr
    have hlen : (prot ++ q₁).length < s := by
      simp only [List.length_append, List.length_cons] at hacc' ⊢
      omega
    have hstep := Step.pop (r := r) (s := s) (prot ++ q₁) q₂ y hlen
    refine ⟨prot, ⟨q₁ ++ q₂, ?_⟩, Nat.le_refl _, fun x hx _ => hx⟩
    unfold Reach at hr
    rw [← List.append_assoc] at hr
    have hz := hr.append (Run.single hstep)
    unfold Reach
    simpa [List.append_assoc] using hz

/-- Re-declare the whole current stack as the protected prefix. -/
theorem Good.reprotect {r s d next : Nat} {prot out : List Nat}
    (h : Good r s d next prot out) :
    ∃ prot', Good r s d next prot' out ∧
      prot'.length + out.length = readCount d next ∧
      ∀ x, x < next → x ≠ d → x ∉ out → x ∈ prot' := by
  obtain ⟨rest, hr⟩ := h
  refine ⟨prot ++ rest, ⟨[], by simpa [Reach] using hr⟩, hr.height, ?_⟩
  intro x hx hxd hxo
  exact hr.mem hx hxd hxo

/-- Any order of at most `r` initial tokens is reachable without output. -/
theorem arrange {r s : Nat} :
    ∀ (n : Nat) (xs target : List Nat), xs.length = n → n ≤ r →
      target.Perm xs → Run r s [] xs [] target := by
  intro n
  induction n with
  | zero =>
    intro xs target hl _ hp
    have hx : xs = [] := List.eq_nil_of_length_eq_zero hl
    subst hx
    have ht : target = [] := hp.eq_nil
    subst ht
    exact Run.nil _
  | succ n ih =>
    intro xs target hl hn hp
    rcases List.eq_nil_or_concat xs with hx | ⟨init, x, hx⟩
    · subst hx; simp at hl
    rw [List.concat_eq_append] at hx
    subst hx
    have hxt : x ∈ target := hp.mem_iff.mpr (by simp)
    obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem hxt
    have hperm : (t₁ ++ t₂).Perm init := by
      have h₁ : (x :: (t₁ ++ t₂)).Perm (x :: init) :=
        (List.perm_middle.symm.trans hp).trans (List.perm_append_singleton x init)
      exact h₁.cons_inv
    have hli : init.length = n := by simpa using hl
    have hrun := ih init (t₁ ++ t₂) hli (by omega) hperm
    have htl : t₁.length < r := by
      have := hp.length_eq
      simp at this
      omega
    have hz := hrun.append (Run.single (Step.push (r := r) (s := s) t₁ t₂ x htl))
    simpa using hz

/-- Prefill: read the first `k` values (except `d`) into any chosen order. -/
theorem Good.prefill {r s d k : Nat} (prot rest : List Nat)
    (hk : readCount d k ≤ r)
    (hp : (prot ++ rest).Perm (delete d (List.range' 0 k))) :
    Good r s d k prot [] :=
  ⟨rest, arrange _ _ _ rfl (by rw [length_delete_range']; exact hk) hp⟩

theorem Good.finish {r s d next : Nat} {prot out : List Nat}
    (h : Good r s d next prot out) (hl : out.length = readCount d next) :
    Run r s [] (delete d (List.range' 0 next)) out [] := by
  obtain ⟨rest, hr⟩ := h
  have hh := hr.height
  have he : prot ++ rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  unfold Reach at hr
  rw [he] at hr
  exact hr

theorem not_mem_prefix {out rem : List Nat} {y : Nat} (h : (out ++ y :: rem).Nodup) :
    y ∉ out := by
  intro hy
  have hd := List.nodup_append.mp h
  exact hd.2.2 y hy y (by simp) rfl

#print axioms Good.record
#print axioms Good.pop
#print axioms Good.reprotect
#print axioms Good.prefill
#print axioms Good.finish
end Unequal
end StackSorting.Generalized
