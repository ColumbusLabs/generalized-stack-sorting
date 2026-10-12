import EqualFinals

/-! Section 5.1 and 5.4: the prefix `PI_r`, with or without a deletion.

Zero-based names: lows `0..r-2`, `P = r-1`, `E_i = r+2i`, `Q_i = r+1+2i`,
`C = 3r-2`, `U = 3r-1`, `M1 = 3r`, `V = 3r+1`, `M2 = 3r+2`.

In the low phase the not-yet-output lows are the tracked prefix, and each
record `Q_j` reads its relay just below them. When a low or a `Q` value (or
`E_0`) is deleted, `P` is also tracked, so the relays go below `P`; the
resulting state `X` has `P` on top of `r-1` tokens, and the common tail
(`tail_X`) leaves regime L with `C` on top. Otherwise `P` is kept at the
bottom (`std_qphase`) and one of the `M`-phase scripts follows. Each script
is checked here step by step, with its own legality conditions. -/
namespace StackSorting.Generalized
namespace Equal
open BasisFamily (delete)
open Unequal (readCount lowSeg lowSeg_succ lowSeg_append length_lowSeg mem_lowSeg)

variable {r d : Nat}

/-- Low pairs `Q_j, j` for `a <= j < a+c` (none deleted): each record reads
the pending relay at slot `top.length`, and the low `j` is popped from the
top. -/
theorem Prog.lowLoop {T bot : List Nat} (hr : 1 ≤ r) :
    ∀ c a {out rem : List Nat},
      Prog r d (r+2*a) (List.range' a c ++ T) bot out (lowSeg r a c ++ rem) →
      c + T.length < r →
      (∀ j, a ≤ j → j < a + c → r+1+2*j ≠ d ∧ j ≠ d) →
      Prog r d (r+2*(a+c)) T bot (out ++ lowSeg r a c) rem := by
  intro c
  induction c with
  | zero => intro a out rem h _ _; simpa [lowSeg] using h
  | succ c ih =>
    intro a out rem h hl hd
    have hA := hd a (Nat.le_refl a) (by omega)
    rw [lowSeg_succ] at h
    have h₀ : Prog r d (r+2*a) (a :: (List.range' (a+1) c ++ T)) bot out
        ((r+1+2*a) :: a :: (lowSeg r (a+1) c ++ rem)) := by
      simpa [List.range'_succ] using h
    have h₁ := h₀.recordAt (by simp; omega) (by omega) hA.1
    have h₂ := Prog.pop_top (p := []) (by simpa using h₁) (by simp only [List.length_nil]; omega)
    have h₃ := ih (a+1) ((by simpa using h₂ : Prog r d (r+1+2*a+1) _ bot _ _).cast
      (by omega : r+1+2*a+1 = r+2*(a+1))) (by omega)
      (fun j h₁ h₂ => hd j (by omega) (by omega))
    rw [show a + 1 + c = a + (c+1) by omega] at h₃
    rw [lowSeg_succ]
    simpa using h₃

theorem Prog.start {W : List Nat} (hW : W.Nodup) : Prog r d 0 [] [] [] W :=
  ⟨Hist.start, by simpa using hW⟩

theorem Prog.protect_range {top bot out rem : List Nat} (c : Nat) {next : Nat}
    (h : Prog r d next top bot out rem) (hl : top.length + c ≤ r)
    (hd : ∀ i, i < c → next + i ≠ d) :
    Prog r d (next+c) (top ++ List.range' next c) bot out rem :=
  ⟨h.1.protect_range c hl hd, h.2⟩

/-- From the regime-S shape with `r-2` tokens, or none, leave for L/Z. -/
theorem Prog.toLooseZ {next : Nat} {out rem : List Nat} (h : Prog r d next [] [] out rem)
    (hc : readCount d next + 2 ≤ out.length + r) (hC : 3*r-2 = d) :
    Loose r d next out rem := by
  obtain ⟨t, h', hl⟩ := h.absorb
  refine ⟨t, by simpa using h', ?_, Or.inl hC⟩
  simp at hl
  omega

/-- The common tail from the state `X`: `P` on top, `r-1` tokens in all,
everything below `C` read. -/
theorem tail_X (hr : 3 ≤ r) {out rem : List Nat}
    (h : Prog r d (3*r-2) [r-1] [] out ([3*r, r-1, 3*r+2, 3*r-1, r+2] ++ rem))
    (hd : d < 3*r-2) (hdE : d ≠ r+2)
    (hcount : readCount d (3*r-2) ≤ out.length + (r-1)) :
    Loose r d (3*r+3) (out ++ [3*r, r-1, 3*r+2, 3*r-1, r+2]) rem := by
  rw [readCount_lt' hd] at hcount
  have h₁ := h.push_protect (by simp; omega) (by omega)
  have h₂ := Prog.push_in_top (p := [r-1]) (q := [3*r-2])
    ((by simpa using h₁ : Prog r d (3*r-2+1) _ _ _ _).cast (by omega : 3*r-2+1 = 3*r-1))
    (by simp; omega) (by omega)
  have h₃ := Prog.recordEq (v := 3*r) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.pop_top (p := []) (by simpa using h₃) (by simp only [List.length_nil]; omega)
  have h₅ := Prog.push_top ((by simpa using h₄ : Prog r d (3*r+1) _ _ _ _)) (by simp; omega)
    (by omega)
  have h₆ := Prog.recordEq (v := 3*r+2) (by simpa using h₅) (by omega) (by omega) (by omega)
  have h₇ := Prog.pop_top (p := []) (by simpa using h₆) (by simp only [List.length_nil]; omega)
  have h₈ := Prog.pop_mid (by simpa using h₇) (by omega) hdE.symm (by simp; omega) (by simp)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  refine ⟨[3*r-2], ?_, by simp; omega, Or.inr (by simp)⟩
  simpa using h₈.cast (show 3*r+2+1 = 3*r+3 by omega)

theorem lowSeg_zero (r a : Nat) : lowSeg r a 0 = [] := by simp [lowSeg]

/-- `lowSeg r 0 (r-1)` with the pair of index `i` displayed. -/
theorem lowSeg_cut (r i : Nat) (hi : i + 2 ≤ r) :
    lowSeg r 0 (r-1) = lowSeg r 0 i ++ ([r+1+2*i, i] ++ lowSeg r (i+1) (r-2-i)) := by
  have h₁ := lowSeg_append r 0 i (r-2-i+1)
  have h₂ := lowSeg_succ r i (r-2-i)
  have h₃ : 0 + i = i := by omega
  have h₄ : i + (r-2-i+1) = r-1 := by omega
  rw [h₃, h₄, h₂] at h₁
  exact h₁.symm

theorem lowSeg_zero_succ (r c : Nat) :
    lowSeg r 0 (c+1) = [r+1, 0] ++ lowSeg r 1 c := by
  rw [lowSeg_succ]

theorem range'_zero_succ (c : Nat) : List.range' 0 (c+1) = 0 :: List.range' 1 c := by
  simp [List.range'_succ]

theorem range'_ends (a c : Nat) :
    List.range' a (c+2) = a :: (List.range' (a+1) c ++ [a+c+1]) := by
  rw [List.range'_succ, show c + 1 = c + 1 from rfl, List.range'_concat]
  simp only [Nat.one_mul]
  congr 3
  omega

/-! Deletions inside the low phase: the state `X`, then `tail_X`. -/

/-- (P2) Deleting a low `i`. -/
theorem prefix_low (hr : 3 ≤ r) {i : Nat} (hi : i + 2 ≤ r) {rem : List Nat}
    (hW : ((lowSeg r 0 i ++ ([r+1+2*i] ++ lowSeg r (i+1) (r-2-i))) ++
      (prefixTail r ++ rem)).Nodup) :
    Loose r i (3*r+3) (lowSeg r 0 i ++ ([r+1+2*i] ++ lowSeg r (i+1) (r-2-i)) ++ prefixTail r)
      rem := by
  have h₀ := Prog.start (r := r) (d := i) hW
  have h₁ := h₀.protect_range i (by simp; omega) (fun j hj => by omega)
  have h₂ := ((h₁.cast (by omega : 0 + i = i)).skipEq rfl).protect_range (r-2-i)
    (by simp; omega) (fun j hj => by omega)
  have h₃ := (h₂.cast (by omega : i+1+(r-2-i) = r-1)).push_protect (by simp; omega) (by omega)
  have h₄ := (h₃.cast (by omega : r-1+1 = r)).push_top (by simp; omega) (by omega)
  have hX : Prog r i (3*r-2) [r-1] []
      (lowSeg r 0 i ++ ([r+1+2*i] ++ lowSeg r (i+1) (r-2-i))) (prefixTail r ++ rem) := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have h₅ := Prog.recordEq (v := r+1) (by simpa [lowSeg_zero] using h₄) rfl (by omega)
        (by omega)
      have h₆ := Prog.lowLoop (T := [r-1]) (bot := []) (by omega) (r-2) 1
        ((by simpa using h₅ : Prog r 0 (r+1+1) _ _ _ _).cast (by omega : r+1+1 = r+2*1))
        (by simp; omega) (fun j h₁ h₂ => ⟨by omega, by omega⟩)
      simpa [lowSeg_zero] using h₆.cast (by omega : r+2*(1+(r-2)) = 3*r-2)
    · obtain ⟨i', rfl⟩ : ∃ i', i = i'+1 := ⟨i-1, by omega⟩
      have h₅ := Prog.recordEq (v := r+1)
        (by simpa [lowSeg_zero_succ, range'_zero_succ] using h₄) rfl (by omega) (by omega)
      have h₆ := Prog.pop_top (p := []) (y := 0) (by simpa using h₅)
        (by simp only [List.length_nil]; omega)
      have h₇ := Prog.lowLoop (T := List.range' (i'+1+1) (r-2-(i'+1)) ++ [r-1]) (bot := [])
        (by omega) i' 1 ((by simpa using h₆ : Prog r _ (r+1+1) _ _ _ _).cast
          (by omega : r+1+1 = r+2*1)) (by simp; omega)
        (fun j h₁ h₂ => ⟨by omega, by omega⟩)
      have h₈ := Prog.recordAt (v := r+1+2*(i'+1)) (by simpa using h₇) (by simp; omega)
        (by omega) (by omega)
      have h₉ := Prog.lowLoop (T := [r-1]) (bot := []) (by omega) (r-2-(i'+1)) (i'+1+1)
        ((by simpa using h₈ : Prog r _ (r+1+2*(i'+1)+1) _ _ _ _).cast
          (by omega : r+1+2*(i'+1)+1 = r+2*(i'+1+1))) (by simp; omega)
        (fun j h₁ h₂ => ⟨by omega, by omega⟩)
      simpa [lowSeg_zero_succ] using h₉.cast (by omega : r+2*(i'+1+1+(r-2-(i'+1))) = 3*r-2)
  have h₁₁ := Prog.pop_mid (y := r) (by simpa [prefixTail] using hX) (by omega) (by omega)
    (by simp; omega) (by simp)
    (by rw [readCount_lt' (by omega)]; simp [length_lowSeg]; omega)
  have h₁₂ := tail_X hr (by simpa using h₁₁) (by omega) (by omega)
    (by rw [readCount_lt' (by omega)]; simp [length_lowSeg]; omega)
  simpa [prefixTail] using h₁₂

theorem lowSeg_full (r : Nat) (hr : 3 ≤ r) : lowSeg r 0 (r-1) = [r+1, 0] ++ lowSeg r 1 (r-2) := by
  have := lowSeg_zero_succ r (r-2)
  rwa [show r-2+1 = r-1 by omega] at this

/-- (P2) Deleting `E_0 = r`. -/
theorem prefix_E0 (hr : 3 ≤ r) {rem : List Nat}
    (hW : (lowSeg r 0 (r-1) ++ ([3*r, r-1, 3*r+2, 3*r-1, r+2] ++ rem)).Nodup) :
    Loose r r (3*r+3) (lowSeg r 0 (r-1) ++ [3*r, r-1, 3*r+2, 3*r-1, r+2]) rem := by
  rw [lowSeg_full r hr] at hW ⊢
  have h₀ := Prog.start (r := r) (d := r) hW
  have h₁ := h₀.protect_range r (by simp) (fun j hj => by omega)
  have h₂ := (h₁.cast (by omega : 0 + r = r)).skipEq rfl
  have ht : List.range' 0 r = 0 :: (List.range' 1 (r-2) ++ [r-1]) := by
    have := range'_ends 0 (r-2)
    rwa [show r-2+2 = r by omega, show 0+(r-2)+1 = r-1 by omega] at this
  have h₃ := Prog.recordEq (v := r+1) (by simpa [ht] using h₂) rfl (by omega) (by omega)
  have h₄ := Prog.pop_top (p := []) (y := 0) (by simpa using h₃)
    (by simp only [List.length_nil]; omega)
  have h₅ := Prog.lowLoop (T := [r-1]) (bot := []) (by omega) (r-2) 1
    ((by simpa using h₄ : Prog r _ (r+1+1) _ _ _ _).cast (by omega : r+1+1 = r+2*1))
    (by simp; omega) (fun j h₁ h₂ => ⟨by omega, by omega⟩)
  have h₆ := tail_X hr ((by simpa using h₅ : Prog r _ (r+2*(1+(r-2))) _ _ _ _).cast
    (by omega : r+2*(1+(r-2)) = 3*r-2)) (by omega) (by omega)
    (by rw [readCount_lt' (by omega)]; simp [length_lowSeg]; omega)
  simpa using h₆

/-- (P1) Deleting `Q_0 = r+1`. -/
theorem prefix_Q0 (hr : 3 ≤ r) {rem : List Nat}
    (hW : (([0] ++ lowSeg r 1 (r-2)) ++ (prefixTail r ++ rem)).Nodup) :
    Loose r (r+1) (3*r+3) ([0] ++ lowSeg r 1 (r-2) ++ prefixTail r) rem := by
  have hl : lowSeg r 1 (r-2) = [r+3, 1] ++ lowSeg r 2 (r-3) := by
    have := lowSeg_succ r 1 (r-3)
    rwa [show r-3+1 = r-2 by omega] at this
  rw [hl] at hW ⊢
  have h₀ := Prog.start (r := r) (d := r+1) hW
  have h₁ := Prog.recordEq (v := 0) (by simpa using h₀) rfl (by omega) (by omega)
  have h₂ := (h₁.cast (by omega : 0+1 = 1)).protect_range (r-2)
    (by simp only [List.length_nil]; omega)
    (fun j hj => by omega)
  have h₃ := (h₂.cast (by omega : 1+(r-2) = r-1)).push_protect (by simp; omega) (by omega)
  have h₄ := (h₃.cast (by omega : r-1+1 = r)).push_top (by simp; omega) (by omega)
  have h₅ := (h₄.skipEq rfl).cast (by omega : r+1+1 = r+2)
  have h₆ := h₅.push_top (by simp; omega) (by omega)
  have ht : List.range' 1 (r-2) = 1 :: List.range' 2 (r-3) := by
    have := List.range'_succ (s := 1) (n := r-3) (step := 1)
    rwa [show r-3+1 = r-2 by omega] at this
  have h₇ := Prog.recordEq (v := r+3) (by simpa [ht] using h₆) (by omega) (by omega) (by omega)
  have h₈ := Prog.pop_top (p := []) (y := 1) (by simpa using h₇)
    (by simp only [List.length_nil]; omega)
  have h₉ := Prog.lowLoop (T := [r-1]) (bot := []) (by omega) (r-3) 2
    ((by simpa using h₈ : Prog r _ (r+3+1) _ _ _ _).cast (by omega : r+3+1 = r+2*2))
    (by simp; omega) (fun j h₁ h₂ => ⟨by omega, by omega⟩)
  have h₁₀ := Prog.pop_mid (y := r) ((by simpa [prefixTail] using h₉ :
      Prog r _ (r+2*(2+(r-3))) _ _ _ _).cast (by omega : r+2*(2+(r-3)) = 3*r-2))
    (by omega) (by omega) (by simp; omega) (by simp)
    (by rw [readCount_lt' (by omega)]; simp [length_lowSeg]; omega)
  have h₁₁ := tail_X hr (by simpa using h₁₀) (by omega) (by omega)
    (by rw [readCount_lt' (by omega)]; simp [length_lowSeg]; omega)
  simpa [prefixTail] using h₁₁

/-- (P2) Deleting `Q_t = r+1+2t` with `t >= 1`: the low `t` sits at the
bottom and is output from depth `r-1`, by the count. -/
theorem prefix_Q (hr : 3 ≤ r) {t : Nat} (ht1 : 1 ≤ t) (ht : t + 2 ≤ r) {rem : List Nat}
    (hW : ((lowSeg r 0 t ++ ([t] ++ lowSeg r (t+1) (r-2-t))) ++ (prefixTail r ++ rem)).Nodup) :
    Loose r (r+1+2*t) (3*r+3)
      (lowSeg r 0 t ++ ([t] ++ lowSeg r (t+1) (r-2-t)) ++ prefixTail r) rem := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t'+1 := ⟨t-1, by omega⟩
  rw [lowSeg_zero_succ] at hW ⊢
  have h₀ := Prog.start (r := r) (d := r+1+2*(t'+1)) hW
  have h₁ := h₀.protect_range (t'+1) (by simp; omega) (fun j hj => by omega)
  have h₂ := Prog.push_in_bot (p := []) (q := []) (by simpa using h₁)
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₃ := h₂.protect_range (r-2-(t'+1))
    (by simp; omega) (fun j hj => by omega)
  have h₄ := (h₃.cast (by omega : t'+1+1+(r-2-(t'+1)) = r-1)).push_protect (by simp; omega)
    (by omega)
  have h₅ := (h₄.cast (by omega : r-1+1 = r)).push_top (by simp; omega) (by omega)
  have h₆ := Prog.recordEq (v := r+1) (by simpa [range'_zero_succ] using h₅) rfl (by omega)
    (by omega)
  have h₇ := Prog.pop_top (p := []) (y := 0) (by simpa using h₆)
    (by simp only [List.length_nil]; omega)
  have h₈ := Prog.lowLoop (T := List.range' (t'+1+1) (r-2-(t'+1)) ++ [r-1]) (bot := [t'+1])
    (by omega) t' 1 ((by simpa using h₇ : Prog r _ (r+1+1) _ _ _ _).cast
      (by omega : r+1+1 = r+2*1)) (by simp; omega) (fun j h₁ h₂ => ⟨by omega, by omega⟩)
  have h₉ := Prog.pop_bot (p := []) (q := []) (y := t'+1) (by simpa using h₈)
    (by rw [readCount_ge' (by omega)]; simp [length_lowSeg]; omega)
  have h₉' : Prog r (r+1+2*(t'+1)) (r+2*(1+t')) (List.range' (t'+1+1) (r-2-(t'+1)) ++ [r-1]) []
      ([r+1, 0] ++ lowSeg r 1 t' ++ [t'+1])
      (lowSeg r (t'+1+1) (r-2-(t'+1)) ++ (prefixTail r ++ rem)) := by
    simpa using h₉
  have h₁₀ := h₉'.read (by simp; omega) 2
  have h₁₁ := Prog.lowLoop (T := [r-1]) (bot := []) (by omega) (r-2-(t'+1)) (t'+1+1)
    ((by simpa using h₁₀ : Prog r _ (r+2*(1+t')+2) _ _ _ _).cast
      (by omega : r+2*(1+t')+2 = r+2*(t'+1+1))) (by simp; omega)
    (fun j h₁ h₂ => ⟨by omega, by omega⟩)
  have h₁₂ := Prog.pop_mid (y := r) ((by simpa [prefixTail] using h₁₁ :
      Prog r _ (r+2*(t'+1+1+(r-2-(t'+1)))) _ _ _ _).cast
      (by omega : r+2*(t'+1+1+(r-2-(t'+1))) = 3*r-2))
    (by omega) (by omega) (by simp; omega) (by simp)
    (by rw [readCount_lt' (by omega)]; simp [length_lowSeg]; omega)
  have h₁₃ := tail_X hr (by simpa using h₁₂) (by omega) (by omega)
    (by rw [readCount_lt' (by omega)]; simp [length_lowSeg]; omega)
  simpa [prefixTail] using h₁₃

/-- (P6) Deleting `P = r-1`. -/
theorem prefix_P (hr : 3 ≤ r) {rem : List Nat}
    (hW : (lowSeg r 0 (r-1) ++ ([r, 3*r, 3*r+2, 3*r-1, r+2] ++ rem)).Nodup) :
    Loose r (r-1) (3*r+3) (lowSeg r 0 (r-1) ++ [r, 3*r, 3*r+2, 3*r-1, r+2]) rem := by
  rw [lowSeg_full r hr] at hW ⊢
  have h₀ := Prog.start (r := r) (d := r-1) hW
  have h₁ := h₀.protect_range (r-1) (by simp only [List.length_nil]; omega)
    (fun j hj => by omega)
  have h₂ := ((h₁.cast (by omega : 0 + (r-1) = r-1)).skipEq rfl).cast (by omega : r-1+1 = r)
  have h₃ := h₂.push_top (by simp; omega) (by omega)
  have ht : List.range' 0 (r-1) = 0 :: List.range' 1 (r-2) := by
    have := range'_zero_succ (r-2)
    rwa [show r-2+1 = r-1 by omega] at this
  have h₄ := Prog.recordEq (v := r+1) (by simpa [ht] using h₃) rfl (by omega) (by omega)
  have h₅ := Prog.pop_top (p := []) (y := 0) (by simpa using h₄)
    (by simp only [List.length_nil]; omega)
  have h₆ := Prog.lowLoop (T := []) (bot := []) (by omega) (r-2) 1
    ((by simpa using h₅ : Prog r _ (r+1+1) _ _ _ _).cast (by omega : r+1+1 = r+2*1))
    (by simp; omega) (fun j h₁ h₂ => ⟨by omega, by omega⟩)
  have h₇ := Prog.pop_mid (y := r) ((by simpa using h₆ :
      Prog r _ (r+2*(1+(r-2))) _ _ _ _).cast (by omega : r+2*(1+(r-2)) = 3*r-2))
    (by omega) (by omega) (by simp) (by simp)
    (by rw [readCount_lt' (by omega)]; simp [length_lowSeg]; omega)
  have h₈ := h₇.push_protect (by simp; omega) (by omega)
  have h₉ := (h₈.cast (by omega : 3*r-2+1 = 3*r-1)).push_protect (by simp; omega) (by omega)
  have h₁₀ := Prog.recordEq (v := 3*r) (by simpa using h₉) (by omega) (by omega) (by omega)
  have h₁₁ := h₁₀.push_top (by simp; omega) (by omega)
  have h₁₂ := Prog.recordEq (v := 3*r+2) (by simpa using h₁₁) (by omega) (by omega) (by omega)
  have h₁₃ := Prog.pop_top (p := [3*r-2]) (q := []) (by simpa using h₁₂) (by simp; omega)
  have h₁₄ := Prog.pop_mid (y := r+2) (by simpa using h₁₃) (by omega) (by omega)
    (by simp; omega) (by simp)
    (by rw [readCount_lt' (by omega)]; simp [length_lowSeg]; omega)
  refine ⟨[3*r-2], ?_, by simp; omega, Or.inr (by simp)⟩
  simpa using h₁₄.cast (show 3*r+2+1 = 3*r+3 by omega)

/-! The standard low phase, with `P` kept at the bottom. -/

theorem std_qphase (hr : 3 ≤ r) {rem : List Nat} (hd : r < d)
    (hdQ : ∀ j, j + 2 ≤ r → d ≠ r+1+2*j)
    (hW : (lowSeg r 0 (r-1) ++ (r :: rem)).Nodup) :
    Prog r d (3*r-2) [] [r-1] (lowSeg r 0 (r-1) ++ [r]) rem := by
  rw [lowSeg_full r hr] at hW ⊢
  have h₀ := Prog.start (r := r) (d := d) hW
  have h₁ := h₀.protect_range (r-1) (by simp only [List.length_nil]; omega)
    (fun j hj => by omega)
  have h₂ := Prog.push_in_bot (p := []) (q := []) (by simpa using h₁)
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₃ := (h₂.cast (by omega : r-1+1 = r)).push_top (by simp; omega) (by omega)
  have ht : List.range' 0 (r-1) = 0 :: List.range' 1 (r-2) := by
    have := range'_zero_succ (r-2)
    rwa [show r-2+1 = r-1 by omega] at this
  have h₄ := Prog.recordEq (v := r+1) (by simpa [ht] using h₃) rfl (by omega)
    (by have := hdQ 0 (by omega); omega)
  have h₅ := Prog.pop_top (p := []) (y := 0) (by simpa using h₄)
    (by simp only [List.length_nil]; omega)
  have h₆ := Prog.lowLoop (T := []) (bot := [r-1]) (by omega) (r-2) 1
    ((by simpa using h₅ : Prog r _ (r+1+1) _ _ _ _).cast (by omega : r+1+1 = r+2*1))
    (by simp; omega) (fun j h₁ h₂ => ⟨hdQ j (by omega) |>.symm, by omega⟩)
  have h₇ := Prog.pop_mid (y := r) ((by simpa using h₆ :
      Prog r _ (r+2*(1+(r-2))) _ _ _ _).cast (by omega : r+2*(1+(r-2)) = 3*r-2))
    (by omega) (by omega) (by simp) (by simp; omega)
    (by unfold readCount; simp [length_lowSeg]; split <;> omega)
  simpa using h₇

#print axioms Prog.lowLoop
#print axioms tail_X
#print axioms prefix_low
#print axioms prefix_E0
#print axioms prefix_Q0
#print axioms prefix_Q
#print axioms prefix_P
#print axioms std_qphase
end Equal
end StackSorting.Generalized
