import EqualReject

/-! Constructive partial histories of the original `(r,r)` machine.

`Hist r d next top bot out` says that some literal history from the empty
stack has read every value below `next` except the deleted value `d`, has
output `out`, and holds the stack `top ++ mid ++ bot` for some `mid`. The
lists `top` and `bot` are tracked exactly; `mid` is not. Every operation below
is one or two literal `Step`s, and its legality is either a position in
`top`/`bot` or a count: the whole stack has `readCount d next - out.length`
tokens. `Prog` adds the remaining target word, so "not yet output" follows
from distinctness. -/
namespace StackSorting.Generalized
namespace Equal
open BasisFamily (delete)
open Unequal (readCount delete_range'_succ length_delete_range' mem_delete_range')

def Hist (r d next : Nat) (top bot out : List Nat) : Prop :=
  ∃ mid, Run r r [] (delete d (List.range' 0 next)) out (top ++ mid ++ bot)

def Prog (r d next : Nat) (top bot out rem : List Nat) : Prop :=
  Hist r d next top bot out ∧ (out ++ rem).Nodup

variable {r d : Nat}

theorem run_height {next : Nat} {out st : List Nat}
    (h : Run r r [] (delete d (List.range' 0 next)) out st) :
    st.length + out.length = readCount d next := by
  have hl := h.supply.length_eq
  simp only [List.nil_append, List.length_append, length_delete_range'] at hl
  omega

theorem run_mem {next x : Nat} {out st : List Nat}
    (h : Run r r [] (delete d (List.range' 0 next)) out st) (hx : x < next) (hxd : x ≠ d)
    (hxo : x ∉ out) : x ∈ st := by
  have hm : x ∈ [] ++ delete d (List.range' 0 next) := by
    simpa using (mem_delete_range' (d := d) (next := next) (x := x)).mpr ⟨hx, hxd⟩
  have hm' := h.supply.mem_iff.mp hm
  simp only [List.mem_append] at hm'
  rcases hm' with hm' | hm'
  · exact absurd hm' hxo
  · exact hm'

theorem run_push {next : Nat} {out : List Nat} (pre post : List Nat)
    (h : Run r r [] (delete d (List.range' 0 next)) out (pre ++ post))
    (hp : pre.length < r) (hd : next ≠ d) :
    Run r r [] (delete d (List.range' 0 (next+1))) out (pre ++ next :: post) := by
  have hz := h.append (Run.single (Step.push (r := r) (s := r) pre post next hp))
  rw [delete_range'_succ]
  simpa [hd] using hz

theorem run_pop {next y : Nat} {out : List Nat} (pre post : List Nat)
    (h : Run r r [] (delete d (List.range' 0 next)) out (pre ++ y :: post))
    (hp : pre.length < r) :
    Run r r [] (delete d (List.range' 0 next)) (out ++ [y]) (pre ++ post) := by
  simpa using h.append (Run.single (Step.pop (r := r) (s := r) pre post y hp))

/-! Basic moves on `Hist`. -/

theorem Hist.start : Hist r d 0 [] [] [] := ⟨[], by simpa [delete] using Run.nil []⟩

theorem Hist.height {next : Nat} {top bot out : List Nat} (h : Hist r d next top bot out) :
    ∃ mid, (top ++ mid ++ bot).length + out.length = readCount d next := by
  obtain ⟨mid, hm⟩ := h
  exact ⟨mid, run_height hm⟩

theorem Hist.skip {top bot out : List Nat} (h : Hist r d d top bot out) :
    Hist r d (d+1) top bot out := by
  obtain ⟨mid, hm⟩ := h
  refine ⟨mid, ?_⟩
  rw [delete_range'_succ]
  simpa using hm

theorem Hist.push_top {next : Nat} {top bot out : List Nat} (h : Hist r d next top bot out)
    (hp : top.length < r) (hd : next ≠ d) : Hist r d (next+1) top bot out := by
  obtain ⟨mid, hm⟩ := h
  refine ⟨next :: mid, ?_⟩
  have hz := run_push top (mid ++ bot) (by simpa [List.append_assoc] using hm) hp hd
  simpa [List.append_assoc] using hz

theorem Hist.push_protect {next : Nat} {top bot out : List Nat} (h : Hist r d next top bot out)
    (hp : top.length < r) (hd : next ≠ d) : Hist r d (next+1) (top ++ [next]) bot out := by
  obtain ⟨mid, hm⟩ := h
  refine ⟨mid, ?_⟩
  have hz := run_push top (mid ++ bot) (by simpa [List.append_assoc] using hm) hp hd
  simpa [List.append_assoc] using hz

theorem Hist.push_in_top {next : Nat} {p q bot out : List Nat} (h : Hist r d next (p ++ q) bot out)
    (hp : p.length < r) (hd : next ≠ d) : Hist r d (next+1) (p ++ next :: q) bot out := by
  obtain ⟨mid, hm⟩ := h
  refine ⟨mid, ?_⟩
  have hz := run_push p (q ++ mid ++ bot) (by simpa [List.append_assoc] using hm) hp hd
  simpa [List.append_assoc] using hz

/-- Insert inside `bot`, after its prefix `p`: legal when fewer than `r`
tokens lie above the insertion point, which the count determines. -/
theorem Hist.push_in_bot {next : Nat} {top p q out : List Nat} (h : Hist r d next top (p ++ q) out)
    (hc : readCount d next < out.length + q.length + r) (hd : next ≠ d) :
    Hist r d (next+1) top (p ++ next :: q) out := by
  obtain ⟨mid, hm⟩ := h
  have hh := run_height hm
  refine ⟨mid, ?_⟩
  have hp : (top ++ mid ++ p).length < r := by
    simp only [List.length_append] at hh ⊢
    omega
  have hz := run_push (top ++ mid ++ p) q (by simpa [List.append_assoc] using hm) hp hd
  simpa [List.append_assoc] using hz

/-- A new maximum is pushed at slot zero and popped at once; its transient
height is part of the history. -/
theorem Hist.record {next : Nat} {top bot out : List Nat} (h : Hist r d next top bot out)
    (hr : 0 < r) (hd : next ≠ d) : Hist r d (next+1) top bot (out ++ [next]) := by
  obtain ⟨mid, hm⟩ := h
  refine ⟨mid, ?_⟩
  have h₁ := run_push [] (top ++ mid ++ bot) (by simpa using hm) (by simpa using hr) hd
  have h₂ := run_pop (y := next) [] (top ++ mid ++ bot) (by simpa using h₁) (by simpa using hr)
  simpa using h₂

theorem Hist.pop_top {next y : Nat} {p q bot out : List Nat} (h : Hist r d next (p ++ y :: q) bot out)
    (hp : p.length < r) : Hist r d next (p ++ q) bot (out ++ [y]) := by
  obtain ⟨mid, hm⟩ := h
  refine ⟨mid, ?_⟩
  have hz := run_pop p (q ++ mid ++ bot) (by simpa [List.append_assoc] using hm) hp
  simpa [List.append_assoc] using hz

theorem Hist.pop_bot {next y : Nat} {top p q out : List Nat} (h : Hist r d next top (p ++ y :: q) out)
    (hc : readCount d next < out.length + q.length + 1 + r) :
    Hist r d next top (p ++ q) (out ++ [y]) := by
  obtain ⟨mid, hm⟩ := h
  have hh := run_height hm
  refine ⟨mid, ?_⟩
  have hp : (top ++ mid ++ p).length < r := by
    simp only [List.length_append, List.length_cons] at hh ⊢
    omega
  have hz := run_pop (top ++ mid ++ p) q (by simpa [List.append_assoc] using hm) hp
  simpa [List.append_assoc] using hz

/-- Output a held token from the untracked middle, when the whole stack has
at most `r` tokens. -/
theorem Hist.pop_mid {next y : Nat} {top bot out : List Nat} (h : Hist r d next top bot out)
    (hy : y < next) (hyd : y ≠ d) (hyo : y ∉ out) (ht : y ∉ top) (hb : y ∉ bot)
    (hc : readCount d next ≤ out.length + r) : Hist r d next top bot (out ++ [y]) := by
  obtain ⟨mid, hm⟩ := h
  have hh := run_height hm
  have hmem := run_mem hm hy hyd hyo
  have hym : y ∈ mid := by
    simp only [List.mem_append] at hmem
    rcases hmem with (h' | h') | h'
    · exact absurd h' ht
    · exact h'
    · exact absurd h' hb
  obtain ⟨m₁, m₂, rfl⟩ := List.append_of_mem hym
  refine ⟨m₁ ++ m₂, ?_⟩
  have hp : (top ++ m₁).length < r := by
    simp only [List.length_append, List.length_cons] at hh ⊢
    omega
  have hz := run_pop (top ++ m₁) (m₂ ++ bot) (by simpa [List.append_assoc] using hm) hp
  simpa [List.append_assoc] using hz

/-- Output any held token when the whole stack has at most `r` tokens, with a
`bot` of `[]`; the tracked prefix only loses that token. -/
theorem Hist.pop_any {next y : Nat} {top out : List Nat} (h : Hist r d next top [] out)
    (hy : y < next) (hyd : y ≠ d) (hyo : y ∉ out) (hc : readCount d next ≤ out.length + r) :
    ∃ top', Hist r d next top' [] (out ++ [y]) ∧ top'.length ≤ top.length ∧
      ∀ x ∈ top, x ≠ y → x ∈ top' := by
  by_cases hyt : y ∈ top
  · obtain ⟨p, q, rfl⟩ := List.append_of_mem hyt
    obtain ⟨mid, hm⟩ := h
    have hh := run_height hm
    refine ⟨p ++ q, Hist.pop_top ⟨mid, hm⟩ ?_, by simp, ?_⟩
    · simp only [List.length_append, List.length_cons] at hh
      omega
    · intro x hx hxy
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      rcases hx with hx | hx | hx
      · exact Or.inl hx
      · exact absurd hx hxy
      · exact Or.inr hx
  · exact ⟨top, h.pop_mid hy hyd hyo hyt (by simp) hc, Nat.le_refl _, fun x hx _ => hx⟩

theorem Hist.demote_top {next : Nat} {p q bot out : List Nat} (h : Hist r d next (p ++ q) bot out) :
    Hist r d next p bot out := by
  obtain ⟨mid, hm⟩ := h
  exact ⟨q ++ mid, by simpa [List.append_assoc] using hm⟩

theorem Hist.demote_bot {next : Nat} {top p q out : List Nat} (h : Hist r d next top (p ++ q) out) :
    Hist r d next top q out := by
  obtain ⟨mid, hm⟩ := h
  exact ⟨mid ++ p, by simpa [List.append_assoc] using hm⟩

/-- Make the whole current stack the tracked prefix. -/
theorem Hist.absorb {next : Nat} {top bot out : List Nat} (h : Hist r d next top bot out) :
    ∃ t, Hist r d next (top ++ t ++ bot) [] out ∧
      (top ++ t ++ bot).length + out.length = readCount d next := by
  obtain ⟨mid, hm⟩ := h
  exact ⟨mid, ⟨[], by simpa using hm⟩, run_height hm⟩

/-- Read `c` values (skipping `d`) at slot `top.length`, just below `top`. -/
theorem Hist.read {top bot out : List Nat} (hp : top.length < r) :
    ∀ c {next : Nat}, Hist r d next top bot out → Hist r d (next+c) top bot out := by
  intro c
  induction c with
  | zero => intro next h; simpa using h
  | succ c ih =>
    intro next h
    have h₁ := ih h
    by_cases hd : next + c = d
    · subst hd
      simpa [Nat.add_assoc] using h₁.skip
    · simpa [Nat.add_assoc] using h₁.push_top hp hd

/-- Push `next,...,next+c-1` (none deleted) each at the end of `top`. -/
theorem Hist.protect_range {top bot out : List Nat} :
    ∀ c {next : Nat}, Hist r d next top bot out → top.length + c ≤ r →
      (∀ i, i < c → next + i ≠ d) → Hist r d (next+c) (top ++ List.range' next c) bot out := by
  intro c
  induction c generalizing top with
  | zero => intro next h _ _; simpa using h
  | succ c ih =>
    intro next h hl hd
    have h₁ := h.push_protect (by omega) (by simpa using hd 0 (by omega))
    have h₂ := ih h₁ (by simp; omega) (fun i hi => by have := hd (i+1) (by omega); omega)
    simpa [List.range'_succ, Nat.add_assoc, Nat.add_comm 1 c] using h₂

theorem Hist.finish {n : Nat} {out : List Nat} (h : Hist r d n [] [] out)
    (hl : out.length = readCount d n) :
    Run r r [] (delete d (List.range' 0 n)) out [] := by
  obtain ⟨mid, hm⟩ := h
  have hh := run_height hm
  have he : [] ++ mid ++ [] = ([] : List Nat) := List.eq_nil_of_length_eq_zero (by omega)
  rw [he] at hm
  exact hm

/-! `Prog`: the same moves, consuming the remaining target word. -/

theorem Prog.not_out {next y : Nat} {top bot out rem : List Nat}
    (h : Prog r d next top bot out (y :: rem)) : y ∉ out := by
  intro hy
  have hd := List.nodup_append.mp h.2
  exact hd.2.2 y hy y (by simp) rfl

theorem Prog.nodup' {next y : Nat} {top bot out rem : List Nat}
    (h : Prog r d next top bot out (y :: rem)) : (out ++ [y] ++ rem).Nodup := by
  simpa using h.2

theorem Prog.record {next : Nat} {top bot out rem : List Nat}
    (h : Prog r d next top bot out (next :: rem)) (hr : 0 < r) (hd : next ≠ d) :
    Prog r d (next+1) top bot (out ++ [next]) rem :=
  ⟨h.1.record hr hd, by simpa using h.2⟩

/-- A new maximum `v`: read the pending values below it at slot `top.length`,
then push and pop `v` at slot zero. -/
theorem Prog.recordAt {next v : Nat} {top bot out rem : List Nat}
    (h : Prog r d next top bot out (v :: rem)) (hp : top.length < r) (hn : next ≤ v)
    (hd : v ≠ d) : Prog r d (v+1) top bot (out ++ [v]) rem := by
  have h₁ := h.1.read hp (v - next)
  have he : next + (v - next) = v := by omega
  rw [he] at h₁
  exact ⟨h₁.record (by omega) hd, by simpa using h.2⟩

theorem Prog.pop_top {next y : Nat} {p q bot out rem : List Nat}
    (h : Prog r d next (p ++ y :: q) bot out (y :: rem)) (hp : p.length < r) :
    Prog r d next (p ++ q) bot (out ++ [y]) rem :=
  ⟨h.1.pop_top hp, by simpa using h.2⟩

theorem Prog.pop_bot {next y : Nat} {top p q out rem : List Nat}
    (h : Prog r d next top (p ++ y :: q) out (y :: rem))
    (hc : readCount d next < out.length + q.length + 1 + r) :
    Prog r d next top (p ++ q) (out ++ [y]) rem :=
  ⟨h.1.pop_bot hc, by simpa using h.2⟩

theorem Prog.pop_mid {next y : Nat} {top bot out rem : List Nat}
    (h : Prog r d next top bot out (y :: rem)) (hy : y < next) (hyd : y ≠ d)
    (ht : y ∉ top) (hb : y ∉ bot) (hc : readCount d next ≤ out.length + r) :
    Prog r d next top bot (out ++ [y]) rem :=
  ⟨h.1.pop_mid hy hyd h.not_out ht hb hc, by simpa using h.2⟩

theorem Prog.recordEq {next v : Nat} {top bot out rem : List Nat}
    (h : Prog r d next top bot out (v :: rem)) (he : next = v) (hr : 0 < r) (hd : v ≠ d) :
    Prog r d (v+1) top bot (out ++ [v]) rem := by
  subst he
  exact h.record hr hd

theorem Prog.skipEq {next : Nat} {top bot out rem : List Nat}
    (h : Prog r d next top bot out rem) (he : next = d) :
    Prog r d (d+1) top bot out rem := by
  subst he
  exact ⟨h.1.skip, h.2⟩

theorem Prog.cast {next next' : Nat} {top bot out rem : List Nat}
    (h : Prog r d next top bot out rem) (he : next = next') :
    Prog r d next' top bot out rem := by
  subst he
  exact h

theorem Prog.skip {top bot out rem : List Nat} (h : Prog r d d top bot out rem) :
    Prog r d (d+1) top bot out rem := ⟨h.1.skip, h.2⟩

theorem Prog.push_top {next : Nat} {top bot out rem : List Nat} (h : Prog r d next top bot out rem)
    (hp : top.length < r) (hd : next ≠ d) : Prog r d (next+1) top bot out rem :=
  ⟨h.1.push_top hp hd, h.2⟩

theorem Prog.push_protect {next : Nat} {top bot out rem : List Nat}
    (h : Prog r d next top bot out rem) (hp : top.length < r) (hd : next ≠ d) :
    Prog r d (next+1) (top ++ [next]) bot out rem :=
  ⟨h.1.push_protect hp hd, h.2⟩

theorem Prog.push_in_top {next : Nat} {p q bot out rem : List Nat}
    (h : Prog r d next (p ++ q) bot out rem) (hp : p.length < r) (hd : next ≠ d) :
    Prog r d (next+1) (p ++ next :: q) bot out rem :=
  ⟨h.1.push_in_top hp hd, h.2⟩

theorem Prog.push_in_bot {next : Nat} {top p q out rem : List Nat}
    (h : Prog r d next top (p ++ q) out rem)
    (hc : readCount d next < out.length + q.length + r) (hd : next ≠ d) :
    Prog r d (next+1) top (p ++ next :: q) out rem :=
  ⟨h.1.push_in_bot hc hd, h.2⟩

theorem Prog.read {top bot out rem : List Nat} (hp : top.length < r) (c : Nat) {next : Nat}
    (h : Prog r d next top bot out rem) : Prog r d (next+c) top bot out rem :=
  ⟨h.1.read hp c, h.2⟩

theorem Prog.demote_top {next : Nat} {p q bot out rem : List Nat}
    (h : Prog r d next (p ++ q) bot out rem) : Prog r d next p bot out rem :=
  ⟨h.1.demote_top, h.2⟩

theorem Prog.demote_bot {next : Nat} {top p q out rem : List Nat}
    (h : Prog r d next top (p ++ q) out rem) : Prog r d next top q out rem :=
  ⟨h.1.demote_bot, h.2⟩

/-- Drain held tokens while the whole stack has at most `r` tokens. -/
theorem Prog.drain {next : Nat} :
    ∀ (seg : List Nat) {out rem : List Nat}, Prog r d next [] [] out (seg ++ rem) →
      (∀ y ∈ seg, y < next ∧ y ≠ d) → readCount d next ≤ out.length + r →
      Prog r d next [] [] (out ++ seg) rem := by
  intro seg
  induction seg with
  | nil => intro out rem h _ _; simpa using h
  | cons y seg ih =>
    intro out rem h hseg hh
    have hy := hseg y (by simp)
    have h₁ := Prog.pop_mid (by simpa using h) hy.1 hy.2 (by simp) (by simp) hh
    have h₂ := ih h₁ (fun z hz => hseg z (by simp [hz])) (by simp; omega)
    simpa using h₂

/-- Successive new maxima `a,...,a+c-1`. -/
theorem Prog.records {top bot : List Nat} (hr : 0 < r) :
    ∀ (c : Nat) {a : Nat} {out rem : List Nat},
      Prog r d a top bot out (List.range' a c ++ rem) → (∀ i, i < c → a + i ≠ d) →
      Prog r d (a+c) top bot (out ++ List.range' a c) rem := by
  intro c
  induction c with
  | zero => intro a out rem h _; simpa using h
  | succ c ih =>
    intro a out rem h hd
    have h₀ : Prog r d a top bot out (a :: (List.range' (a+1) c ++ rem)) := by
      simpa [List.range'_succ] using h
    have h₁ := Prog.record h₀ hr (by simpa using hd 0 (by omega))
    have h₂ := ih h₁ (fun i hi => by have := hd (i+1) (by omega); omega)
    have he : a + 1 + c = a + (c+1) := by omega
    rw [he] at h₂
    simpa [List.range'_succ, List.append_assoc] using h₂

theorem Prog.finish {n : Nat} {out : List Nat} (h : Prog r d n [] [] out [])
    (hl : out.length = readCount d n) :
    Run r r [] (delete d (List.range' 0 n)) out [] := h.1.finish hl

theorem readCount_lt' {d next : Nat} (h : d < next) : readCount d next = next - 1 := by
  unfold readCount; split <;> omega

theorem readCount_ge' {d next : Nat} (h : next ≤ d) : readCount d next = next := by
  unfold readCount; split <;> omega

#print axioms Hist.push_in_bot
#print axioms Hist.pop_any
#print axioms Prog.drain
#print axioms Prog.records
end Equal
end StackSorting.Generalized
