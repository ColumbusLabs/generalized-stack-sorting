import UnequalDeletion

/-! Deletion cases that keep the unmodified initial arrangement: §5.5–5.9
(the permanent token, a relay introduced during the relay phase, a relay
record, the final record, or a terminal value). -/
namespace StackSorting.Generalized
namespace Unequal
open BasisFamily (delete)

variable {r s m : Nat}

/-- §5.5: deleting the permanent token `r-1`. -/
theorem del_permanent (hr : 2 ≤ r) (hrs : r < s) :
    Run r s [] (delete (r-1) (List.range (2*s+r+2*m))) (delete (r-1) (family r s m)) [] := by
  have hW : delete (r-1) (family r s m) =
      lowSeg s 0 (r-1) ++ (List.range' r (s-r) ++ (relaySeg r s 0 m ++
        ((2*s+r+2*m-1) :: (lateSeg r s m ++ termSeg r s m)))) := by
    rw [family_segments, delete_append, delete_eq_self (lowSeg_ne (fun i _ _ => ⟨by omega, by omega⟩)),
      delete_append, delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega),
      delete_append, delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_self, delete_append,
      delete_eq_self (lateSeg_ne (fun j _ => by omega)),
      delete_eq_self (termSeg_ne (by omega))]
  have hnd := delete_nodup (d := r-1) (family_nodup r s m hr hrs)
  rw [hW] at hnd ⊢
  have hpre : delete (r-1) (List.range' 0 r) = List.range' 0 (r-1) := by
    have h := delete_range'_top (r-1)
    rwa [show r - 1 + 1 = r by omega] at h
  have h₀ : Prog r s (r-1) r [] _ (fun x => x < r - 1) :=
    Prog.start (List.range' 0 (r-1)) [] _ hnd
      (by rw [readCount_lt (by omega)]; omega)
      (by rw [hpre]; simp)
      (by simp)
      (fun x hx => by rw [List.mem_range']; exact ⟨x, hx, by omega⟩)
  obtain ⟨n₁, h₁, -, hn₁⟩ := Prog.lowAll (by omega) (by omega) (by omega) 0 (r-1) h₀
    (by omega) (fun i _ hi => ⟨show i < r - 1 by omega, by omega, by omega, by omega⟩)
  rw [hn₁ (by omega)] at h₁
  have h₂ := Prog.drain (by omega) (List.range' r (s-r)) h₁
    (fun y hy => by rw [List.mem_range'] at hy; omega)
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg] <;> omega)
  obtain ⟨n₃, h₃, hz₃, hp₃⟩ := Prog.relayAll (by omega) (by omega) (by omega) 0 m h₂
    (by omega)
    (fun j _ hj => ⟨by omega, by omega, Or.inr (by
      rw [readCount_lt (by omega)]; simp [length_lowSeg] <;> omega)⟩)
  have hn₃ : n₃ ≤ 2*s+r+2*m-1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hz₃ hm]; omega
    · rw [hp₃ hm]; omega
  have h₄ := tail_P hr hrs (by simpa using h₃) hn₃
    (by simp [length_lowSeg, length_relaySeg] <;> omega)
  have h₅ := Prog.finish h₄ (by
    rw [readCount_lt (by omega)]
    simp [length_lowSeg, length_relaySeg, length_lateSeg, length_termSeg] <;> omega)
  simpa [List.range_eq_range', List.append_assoc] using h₅

/-- The unmodified prefill and low phase: lows increasing with the permanent
token last, then the extras, for any deleted value above the low phase. -/
theorem unmod_prefix (hr : 2 ≤ r) (hrs : r < s) {d : Nat} (hd : s+2*r-2 ≤ d)
    (rem : List Nat) (hnd : (lowSeg s 0 (r-1) ++ (List.range' r (s-r) ++ rem)).Nodup) :
    Prog r s d (s+2*r-2) (lowSeg s 0 (r-1) ++ List.range' r (s-r)) rem (fun x => x < r - 1) := by
  have hpre : delete d (List.range' 0 r) = List.range' 0 r := delete_range'_above (by omega)
  have hcat : List.range' 0 (r-1) ++ [r-1] = List.range' 0 r := by
    have h := (List.range'_concat (s := 0) (n := r-1) (step := 1)).symm
    rwa [show r - 1 + 1 = r by omega, show 0 + 1 * (r-1) = r - 1 by omega] at h
  have h₀ : Prog r s d r [] _ (fun x => x < r - 1) :=
    Prog.start (List.range' 0 (r-1)) [r-1] _ hnd
      (by rw [readCount_ge (by omega)] <;> omega)
      (by rw [hpre, hcat])
      (by simp)
      (fun x hx => by rw [List.mem_range']; exact ⟨x, hx, by omega⟩)
  obtain ⟨n₁, h₁, -, hn₁⟩ := Prog.lowAll (by omega) (by omega) (by omega) 0 (r-1) h₀
    (by omega) (fun i _ hi => ⟨show i < r - 1 by omega, by omega, by omega, by omega⟩)
  rw [hn₁ (by omega)] at h₁
  have h₂ := Prog.drain (by omega) (List.range' r (s-r)) h₁
    (fun y hy => by rw [List.mem_range'] at hy; omega)
    (by rw [readCount_ge (by omega)]; simp [length_lowSeg] <;> omega)
  have he : s + 2*(0+(r-1)) = s+2*r-2 := by omega
  rw [he] at h₂
  simpa using h₂

/-- §5.8: deleting the final record. -/
theorem del_final (hr : 2 ≤ r) (hrs : r < s) :
    Run r s [] (delete (2*s+r+2*m-1) (List.range (2*s+r+2*m)))
      (delete (2*s+r+2*m-1) (family r s m)) [] := by
  have hW : delete (2*s+r+2*m-1) (family r s m) =
      lowSeg s 0 (r-1) ++ (List.range' r (s-r) ++ (relaySeg r s 0 m ++
        ((r-1) :: (lateSeg r s m ++ termSeg r s m)))) := by
    rw [family_segments, delete_append, delete_eq_self (lowSeg_ne (fun i _ _ => ⟨by omega, by omega⟩)),
      delete_append, delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega),
      delete_append, delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_self, delete_cons_ne _ (by omega), delete_append,
      delete_eq_self (lateSeg_ne (fun j _ => by omega)),
      delete_eq_self (termSeg_ne (by omega))]
  have hnd := delete_nodup (d := 2*s+r+2*m-1) (family_nodup r s m hr hrs)
  rw [hW] at hnd ⊢
  have h₂ := unmod_prefix hr hrs (d := 2*s+r+2*m-1) (by omega) _ hnd
  obtain ⟨n₃, h₃, hz₃, hp₃⟩ := Prog.relayAll (by omega) (by omega) (by omega) 0 m h₂
    (by omega)
    (fun j _ hj => ⟨by omega, by omega, Or.inr (by
      rw [readCount_ge (by omega)]; simp [length_lowSeg] <;> omega)⟩)
  have hn₃ : n₃ = s+2*r-2+2*m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hz₃ hm]; omega
    · rw [hp₃ hm]; omega
  rw [hn₃] at h₃
  have h₄ := tail_N hr hrs (by simpa using h₃)
    (by simp [length_lowSeg, length_relaySeg] <;> omega)
  have h₅ := Prog.finish h₄ (by
    rw [readCount_ge (by omega)]
    simp [length_lowSeg, length_relaySeg, length_lateSeg, length_termSeg] <;> omega)
  have hin : delete (2*s+r+2*m-1) (List.range (2*s+r+2*m)) =
      delete (2*s+r+2*m-1) (List.range' 0 (2*s+r+2*m-1)) := by
    have h := delete_range'_top (2*s+r+2*m-1)
    rw [show 2*s+r+2*m-1+1 = 2*s+r+2*m by omega] at h
    rw [List.range_eq_range', h, delete_range'_above (by omega)]
  rw [hin]
  simpa [List.append_assoc] using h₅

/-- §5.9: deleting a terminal value. -/
theorem del_terminal (hr : 2 ≤ r) (hrs : r < s) {d : Nat}
    (hd₁ : s+2*r-2+2*m ≤ d) (hd₂ : d < 2*s+r+2*m-1) :
    Run r s [] (delete d (List.range (2*s+r+2*m))) (delete d (family r s m)) [] := by
  have hlen := delete_family_length (m := m) (d := d) hr hrs (by omega)
  have hW : delete d (family r s m) =
      lowSeg s 0 (r-1) ++ (List.range' r (s-r) ++ (relaySeg r s 0 m ++
        ((2*s+r+2*m-1) :: (r-1) :: (delete d (lateSeg r s m) ++ delete d (termSeg r s m))))) := by
    rw [family_segments, delete_append, delete_eq_self (lowSeg_ne (fun i _ _ => ⟨by omega, by omega⟩)),
      delete_append, delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega),
      delete_append, delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append]
  have hnd := delete_nodup (d := d) (family_nodup r s m hr hrs)
  rw [hW] at hnd hlen ⊢
  have h₂ := unmod_prefix hr hrs (d := d) (by omega) _ hnd
  obtain ⟨n₃, h₃, hz₃, hp₃⟩ := Prog.relayAll (by omega) (by omega) (by omega) 0 m h₂
    (by omega)
    (fun j _ hj => ⟨by omega, by omega, Or.inr (by
      rw [readCount_ge (by omega)]; simp [length_lowSeg] <;> omega)⟩)
  have hn₃ : n₃ ≤ 2*s+r+2*m-1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hz₃ hm]; omega
    · rw [hp₃ hm]; omega
  have hlate := length_delete_le (d := d) (l := lateSeg r s m)
  have hterm := length_delete_le (d := d) (l := termSeg r s m)
  rw [length_lateSeg] at hlate
  rw [length_termSeg] at hterm
  simp only [List.length_append, List.length_cons, length_lowSeg, length_relaySeg,
    List.length_range'] at hlen
  have h₄ := tail_std hr hrs (by simpa using h₃) hn₃ (by omega) (by omega)
    (Or.inr (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega))
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)
  have h₅ := Prog.finish h₄ (by
    rw [readCount_lt (by omega)]
    simp [length_lowSeg, length_relaySeg] <;> omega)
  simpa [List.range_eq_range', List.append_assoc] using h₅

theorem relaySeg_split0 (r s m k : Nat) (hk : k < m) :
    relaySeg r s 0 m = relaySeg r s 0 k ++
      ((s+2*r-1+2*k) :: (s+2*k) :: relaySeg r s (k+1) (m-k-1)) := by
  have h := relaySeg_split r s 0 m k (by omega) (by omega)
  simpa [Nat.sub_zero, Nat.zero_add] using h

/-- §5.7: deleting an ordinary relay record `A_j0`. -/
theorem del_relayRecord (hr : 2 ≤ r) (hrs : r < s) {j₀ : Nat} (hj : j₀ < m) :
    Run r s [] (delete (s+2*r-1+2*j₀) (List.range (2*s+r+2*m)))
      (delete (s+2*r-1+2*j₀) (family r s m)) [] := by
  have hlen := delete_family_length (m := m) (d := s+2*r-1+2*j₀) hr hrs (by omega)
  have hW : delete (s+2*r-1+2*j₀) (family r s m) =
      lowSeg s 0 (r-1) ++ (List.range' r (s-r) ++ (relaySeg r s 0 j₀ ++
        ((s+2*j₀) :: (relaySeg r s (j₀+1) (m-j₀-1) ++
        ((2*s+r+2*m-1) :: (r-1) :: (delete (s+2*r-1+2*j₀) (lateSeg r s m) ++
          delete (s+2*r-1+2*j₀) (termSeg r s m))))))) := by
    rw [family_segments, relaySeg_split0 r s m j₀ hj]
    simp only [List.append_assoc, List.cons_append]
    rw [delete_append,
      delete_eq_self (lowSeg_ne (fun i _ _ => ⟨by omega, by omega⟩)),
      delete_append, delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega),
      delete_append,
      delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_self, delete_cons_ne _ (by omega), delete_append,
      delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append]
  have hnd := delete_nodup (d := s+2*r-1+2*j₀) (family_nodup r s m hr hrs)
  rw [hW] at hnd hlen ⊢
  have h₂ := unmod_prefix hr hrs (d := s+2*r-1+2*j₀) (by omega) _ hnd
  obtain ⟨n₁, h₁, hz₁, hp₁⟩ := Prog.relayAll (by omega) (by omega) (by omega) 0 j₀ h₂
    (by omega)
    (fun j _ hj' => ⟨by omega, by omega, Or.inr (by
      rw [readCount_ge (by omega)]; simp [length_lowSeg] <;> omega)⟩)
  have hn₁ : n₁ = s+2*r-2+2*j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h0 | h0
    · rw [hz₁ h0]; omega
    · rw [hp₁ h0]; omega
  rw [hn₁] at h₁
  have h₃ := Prog.pop (by omega) h₁ (by omega) (by omega)
    (Or.inr (by rw [readCount_ge (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega))
  have hPout := Prog.not_out h₃ (x := r-1) (by simp)
  have h₄ := Prog.reprotect h₃
    (by rw [readCount_ge (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)
  obtain ⟨n₅, h₅, hz₅, hp₅⟩ := Prog.relayAll (by omega) (by omega) (by omega)
    (j₀+1) (m-j₀-1) h₄ (by omega)
    (fun j h₁ h₂ => ⟨by omega, by omega, Or.inr (by
      rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)⟩)
  have hn₅ : n₅ ≤ 2*s+r+2*m-1 := by
    rcases Nat.eq_zero_or_pos (m-j₀-1) with h0 | h0
    · rw [hz₅ h0]; omega
    · rw [hp₅ h0]; omega
  have hlate := length_delete_le (d := s+2*r-1+2*j₀) (l := lateSeg r s m)
  have hterm := length_delete_le (d := s+2*r-1+2*j₀) (l := termSeg r s m)
  rw [length_lateSeg] at hlate
  rw [length_termSeg] at hterm
  simp only [List.length_append, List.length_cons, length_lowSeg, length_relaySeg,
    List.length_range'] at hlen
  have h₆ := tail_std hr hrs (by simpa using h₅) hn₅ (by omega) (by omega)
    (Or.inl (by exact ⟨by omega, by omega, by simpa using hPout⟩))
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)
  have h₇ := Prog.finish h₆ (by
    rw [readCount_lt (by omega)]
    simp [length_lowSeg, length_relaySeg] <;> omega)
  simpa [List.range_eq_range', List.append_assoc] using h₇

/-- §5.6, late output: deleting a relay `E_k` introduced at relay step
`k-(r-1)` whose own output comes after the permanent token. -/
theorem del_relayIntro_late (hr : 2 ≤ r) (hrs : r < s) {k : Nat}
    (hk₁ : r - 1 ≤ k) (hk₂ : k ≤ m + r - 2) (hkm : m ≤ k) :
    Run r s [] (delete (s+2*k) (List.range (2*s+r+2*m))) (delete (s+2*k) (family r s m)) [] := by
  have hj : k - (r-1) < m := by omega
  have hlen := delete_family_length (m := m) (d := s+2*k) hr hrs (by omega)
  have hW : delete (s+2*k) (family r s m) =
      lowSeg s 0 (r-1) ++ (List.range' r (s-r) ++ (relaySeg r s 0 (k-(r-1)) ++
        ((s+2*r-1+2*(k-(r-1))) :: (s+2*(k-(r-1))) ::
        (relaySeg r s (k-(r-1)+1) (m-(k-(r-1))-1) ++
        ((2*s+r+2*m-1) :: (r-1) :: (delete (s+2*k) (lateSeg r s m) ++
          delete (s+2*k) (termSeg r s m))))))) := by
    rw [family_segments, relaySeg_split0 r s m (k-(r-1)) hj]
    simp only [List.append_assoc, List.cons_append]
    rw [delete_append,
      delete_eq_self (lowSeg_ne (fun i _ _ => ⟨by omega, by omega⟩)),
      delete_append, delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega),
      delete_append,
      delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append,
      delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append]
  have hnd := delete_nodup (d := s+2*k) (family_nodup r s m hr hrs)
  rw [hW] at hnd hlen ⊢
  have h₂ := unmod_prefix hr hrs (d := s+2*k) (by omega) _ hnd
  obtain ⟨n₁, h₁, hz₁, hp₁⟩ := Prog.relayAll (by omega) (by omega) (by omega) 0 (k-(r-1)) h₂
    (by omega)
    (fun j _ hj' => ⟨by omega, by omega, Or.inr (by
      rw [readCount_ge (by omega)]; simp [length_lowSeg] <;> omega)⟩)
  have hn₁ : n₁ = s+2*r-2+2*(k-(r-1)) := by
    rcases Nat.eq_zero_or_pos (k-(r-1)) with h0 | h0
    · rw [hz₁ h0]; omega
    · rw [hp₁ h0]; omega
  rw [hn₁] at h₁
  have h₂' := Prog.record (by omega) (by omega) h₁ (by omega) (by omega)
  rw [show s+2*r-1+2*(k-(r-1))+1 = s+2*r+2*(k-(r-1)) by omega] at h₂'
  have h₃ := Prog.pop (by omega) h₂' (by omega) (by omega)
    (Or.inr (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega))
  have hPout := Prog.not_out h₃ (x := r-1) (by simp)
  have h₄ := Prog.reprotect h₃
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)
  obtain ⟨n₅, h₅, hz₅, hp₅⟩ := Prog.relayAll (by omega) (by omega) (by omega)
    (k-(r-1)+1) (m-(k-(r-1))-1) h₄ (by omega)
    (fun j h₁ h₂ => ⟨by omega, by omega, Or.inr (by
      rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)⟩)
  have hn₅ : n₅ ≤ 2*s+r+2*m-1 := by
    rcases Nat.eq_zero_or_pos (m-(k-(r-1))-1) with h0 | h0
    · rw [hz₅ h0]; omega
    · rw [hp₅ h0]; omega
  have hlate := length_delete_le (d := s+2*k) (l := lateSeg r s m)
  have hterm := length_delete_le (d := s+2*k) (l := termSeg r s m)
  rw [length_lateSeg] at hlate
  rw [length_termSeg] at hterm
  simp only [List.length_append, List.length_cons, length_lowSeg, length_relaySeg,
    List.length_range'] at hlen
  have h₆ := tail_std hr hrs (by simpa using h₅) hn₅ (by omega) (by omega)
    (Or.inl (by exact ⟨by omega, by omega, by simpa using hPout⟩))
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)
  have h₇ := Prog.finish h₆ (by
    rw [readCount_lt (by omega)]
    simp [length_lowSeg, length_relaySeg] <;> omega)
  simpa [List.range_eq_range', List.append_assoc] using h₇

/-- §5.6, early output: deleting a relay `E_k`, introduced at relay step
`k-(r-1)`, whose own output is the relay output of step `k < m`. -/
theorem del_relayIntro_early (hr : 2 ≤ r) (hrs : r < s) {k : Nat}
    (hk₁ : r - 1 ≤ k) (hkm : k < m) :
    Run r s [] (delete (s+2*k) (List.range (2*s+r+2*m))) (delete (s+2*k) (family r s m)) [] := by
  have hj : k - (r-1) < m := by omega
  have hlen := delete_family_length (m := m) (d := s+2*k) hr hrs (by omega)
  have hs₂ : relaySeg r s (k-(r-1)+1) (m-(k-(r-1))-1) =
      relaySeg r s (k-(r-1)+1) (k-(k-(r-1))-1) ++
        ((s+2*r-1+2*k) :: (s+2*k) :: relaySeg r s (k+1) (m-k-1)) := by
    have h := relaySeg_split r s (k-(r-1)+1) (m-(k-(r-1))-1) k (by omega) (by omega)
    rw [show k-(k-(r-1)+1) = k-(k-(r-1))-1 by omega,
      show k-(r-1)+1+(m-(k-(r-1))-1)-k-1 = m-k-1 by omega] at h
    simpa using h
  have hW : delete (s+2*k) (family r s m) =
      lowSeg s 0 (r-1) ++ (List.range' r (s-r) ++ (relaySeg r s 0 (k-(r-1)) ++
        ((s+2*r-1+2*(k-(r-1))) :: (s+2*(k-(r-1))) ::
        (relaySeg r s (k-(r-1)+1) (k-(k-(r-1))-1) ++ ((s+2*r-1+2*k) ::
        (relaySeg r s (k+1) (m-k-1) ++
        ((2*s+r+2*m-1) :: (r-1) :: (delete (s+2*k) (lateSeg r s m) ++
          delete (s+2*k) (termSeg r s m))))))))) := by
    rw [family_segments, relaySeg_split0 r s m (k-(r-1)) hj, hs₂]
    simp only [List.append_assoc, List.cons_append]
    rw [delete_append,
      delete_eq_self (lowSeg_ne (fun i _ _ => ⟨by omega, by omega⟩)),
      delete_append, delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega),
      delete_append,
      delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append,
      delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_self, delete_append,
      delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append]
  have hnd := delete_nodup (d := s+2*k) (family_nodup r s m hr hrs)
  rw [hW] at hnd hlen ⊢
  have h₂ := unmod_prefix hr hrs (d := s+2*k) (by omega) _ hnd
  obtain ⟨n₁, h₁, hz₁, hp₁⟩ := Prog.relayAll (by omega) (by omega) (by omega) 0 (k-(r-1)) h₂
    (by omega)
    (fun j _ hj' => ⟨by omega, by omega, Or.inr (by
      rw [readCount_ge (by omega)]; simp [length_lowSeg] <;> omega)⟩)
  have hn₁ : n₁ = s+2*r-2+2*(k-(r-1)) := by
    rcases Nat.eq_zero_or_pos (k-(r-1)) with h0 | h0
    · rw [hz₁ h0]; omega
    · rw [hp₁ h0]; omega
  rw [hn₁] at h₁
  have h₂' := Prog.record (by omega) (by omega) h₁ (by omega) (by omega)
  rw [show s+2*r-1+2*(k-(r-1))+1 = s+2*r+2*(k-(r-1)) by omega] at h₂'
  have h₃ := Prog.pop (by omega) h₂' (by omega) (by omega)
    (Or.inr (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega))
  have hPout := Prog.not_out h₃ (x := r-1) (by simp)
  have h₄ := Prog.reprotect h₃
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)
  obtain ⟨n₅, h₅, hz₅, hp₅⟩ := Prog.relayAll (by omega) (by omega) (by omega)
    (k-(r-1)+1) (k-(k-(r-1))-1) h₄ (by omega)
    (fun j h₁ h₂ => ⟨by omega, by omega, Or.inr (by
      rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)⟩)
  have hn₅ : n₅ ≤ s+2*r-1+2*k := by
    rcases Nat.eq_zero_or_pos (k-(k-(r-1))-1) with h0 | h0
    · rw [hz₅ h0]; omega
    · rw [hp₅ h0]; omega
  have h₆ := Prog.record (by omega) (by omega) h₅ hn₅ (by omega)
  rw [show s+2*r-1+2*k+1 = s+2*r+2*k by omega] at h₆
  obtain ⟨n₇, h₇, hz₇, hp₇⟩ := Prog.relayAll (by omega) (by omega) (by omega)
    (k+1) (m-k-1) h₆ (by omega)
    (fun j h₁ h₂ => ⟨by omega, by omega, Or.inr (by
      rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)⟩)
  have hn₇ : n₇ ≤ 2*s+r+2*m-1 := by
    rcases Nat.eq_zero_or_pos (m-k-1) with h0 | h0
    · rw [hz₇ h0]; omega
    · rw [hp₇ h0]; omega
  have hlate := length_delete_le (d := s+2*k) (l := lateSeg r s m)
  have hterm := length_delete_le (d := s+2*k) (l := termSeg r s m)
  rw [length_lateSeg] at hlate
  rw [length_termSeg] at hterm
  simp only [List.length_append, List.length_cons, length_lowSeg, length_relaySeg,
    List.length_range'] at hlen
  have h₈ := tail_std hr hrs (by simpa using h₇) hn₇ (by omega) (by omega)
    (Or.inl (by exact ⟨by omega, by omega, by simpa using hPout⟩))
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)
  have h₉ := Prog.finish h₈ (by
    rw [readCount_lt (by omega)]
    simp [length_lowSeg, length_relaySeg] <;> omega)
  simpa [List.range_eq_range', List.append_assoc] using h₉

#print axioms del_permanent
#print axioms del_relayIntro_late
#print axioms del_relayIntro_early
#print axioms del_relayRecord
#print axioms del_final
#print axioms del_terminal
end Unequal
end StackSorting.Generalized
