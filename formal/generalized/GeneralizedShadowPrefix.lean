import GeneralizedShadowGlobal

/-! Exact deletion-shadow semantics for genuine finite prefixes. The original
prefix is decoded by the same literal H/N steps as a complete word, but it may
stop at any frontier and held dictionary. The shortened output is the actual
standardized output prefix, not a code-equivalence premise. -/
namespace StackSorting.Generalized
namespace LazyCode
open List

/-- Literal prefix decoding. Unlike `Decodes`, termination is permitted with
arbitrary unread frontier and held labels. The nonempty steps are unchanged. -/
inductive PartialDecodes : Nat → List Nat → List Letter → List Nat → Prop where
  | nil {next : Nat} {held : List Nat} : PartialDecodes next held [] []
  | held {next a : Nat} {pre post : List Nat} {code : List Letter} {output : List Nat}
      (old : a < next)
      (tail : PartialDecodes next (pre ++ post) code output) :
      PartialDecodes next (pre ++ a :: post) (.H (pre.length+1) :: code) (a :: output)
  | record {next a : Nat} {held : List Nat} {code : List Letter} {output : List Nat}
      (new : next ≤ a)
      (tail : PartialDecodes (a+1) (held ++ List.range' next (a-next)) code output) :
      PartialDecodes next held (.N (a+1-next) :: code) (a :: output)

/-- Every complete literal decoding is also a prefix decoding. -/
theorem Decodes.partial {limit next : Nat} {held output : List Nat} {code : List Letter}
    (h : Decodes limit next held code output) : PartialDecodes next held code output := by
  induction h with
  | nil => exact .nil
  | held old tail ih => exact .held old ih
  | record new tail ih => exact .record new ih

theorem PartialDecodes.length {next : Nat} {held output : List Nat} {code : List Letter}
    (h : PartialDecodes next held code output) : code.length = output.length := by
  induction h <;> simp_all

/-- Prefix truncation uses the same number of actual output labels as code
letters; no assumption about the shadow's emitted code is involved. -/
theorem PartialDecodes.take {next : Nat} {held output : List Nat} {code : List Letter}
    (h : PartialDecodes next held code output) (k : Nat) :
    PartialDecodes next held (code.take k) (output.take k) := by
  induction h generalizing k with
  | nil => simp only [List.take_nil]; exact .nil
  | held old tail ih =>
    cases k with
    | zero => exact .nil
    | succ k => simp only [List.take_succ_cons]; exact .held old (ih k)
  | record new tail ih =>
    cases k with
    | zero => exact .nil
    | succ k => simp only [List.take_succ_cons]; exact .record new (ih k)

/-- Every prefix of a complete literal decoding has genuine prefix semantics. -/
theorem Decodes.partial_take {limit next : Nat} {held output : List Nat} {code : List Letter}
    (h : Decodes limit next held code output) (k : Nat) :
    PartialDecodes next held (code.take k) (output.take k) := h.partial.take k

/-- The same fact stated for an arbitrary split of the original code. -/
theorem Decodes.partial_prefix {limit next : Nat} {held output : List Nat}
    {front rest : List Letter}
    (h : Decodes limit next held (front ++ rest) output) :
    PartialDecodes next held front (output.take front.length) := by
  simpa using h.partial_take front.length

/-- A well-formed prefix re-encodes to its literal original letters. This
connects the decoding relation to the existing encoder without redefining it. -/
theorem PartialDecodes.encode_eq {next : Nat} {held output : List Nat} {code : List Letter}
    (h : PartialDecodes next held code output) (inv : HeldInvariant next held) :
    encode next held output = code := by
  induction h with
  | nil => rfl
  | @held next a pre post code output old tail ih =>
    have hn : a ∉ pre := by
      intro ha
      have hp := (List.nodup_append.mp inv.nodup).2.2
      exact hp a ha a (by simp) rfl
    have ht := ih inv.remove
    simp [encode, old, List.idxOf_append, hn, List.erase_append_right, ht]
  | @record next a held code output new tail ih =>
    simpa [encode, Nat.not_lt.mpr new] using ih (inv.record new)

namespace Shadow

/-- Exact global semantics at an arbitrary prefix boundary. Termination does
not require the held dictionary to be empty: the global update invariant is
sufficient for each actual H/N step. -/
theorem transduce_partial_eq_encode {v originalNext next : Nat}
    {originalHeld held output : List Nat} {cells : List Cell} {code : List Letter}
    (hd : PartialDecodes originalNext originalHeld code output)
    (h : GlobalInvariant v originalNext originalHeld next held cells) :
    transduce v originalNext cells code = some (encode next held (deleteWord v output)) := by
  induction hd generalizing next held cells with
  | nil => simp [transduce, deleteWord, encode]
  | @held originalNext a pre post code output old tail ih =>
    obtain ⟨before, selected, after, hcells, hpre, ha, hpost⟩ := aligned_split h.2.1
    have hlen : pre.length = before.length := by rw [← hpre]; simp
    subst cells
    have hglobal : GlobalInvariant v originalNext
        (before.map (originalValue v) ++ originalValue v selected :: after.map (originalValue v))
        next held (before ++ selected :: after) := by simpa [hpre, ha, hpost] using h
    obtain ⟨next', held', hinv, hencode⟩ := global_update hglobal
    have htail : GlobalInvariant v originalNext (pre ++ post) next' held'
        (update before selected after).2 := by simpa [hpre, hpost] using hinv
    have hrun := ih htail
    rw [← ha, hencode]
    simp [transduce, hlen, hrun]
  | @record originalNext a originalHeld code output new tail ih =>
    let before := cells ++ arrivals v originalNext (a-originalNext)
    let selected := arrivalCell v a
    have hbefore : before.map (originalValue v) = originalHeld ++ List.range' originalNext (a-originalNext) := by
      simp [before, h.2.1]
    have hselected : originalValue v selected = a := originalValue_arrivalCell v a
    have hfull : cells ++ arrivals v originalNext (a+1-originalNext) = before ++ selected :: [] := by
      simp only [arrivals_record new, List.append_assoc, before, selected]
    have hnext : originalNext+(a+1-originalNext) = a+1 := by omega
    have hidx : cells.length+(a+1-originalNext)-1 = before.length := by
      simp [before]; omega
    have hglobal : GlobalInvariant v (a+1)
        (before.map (originalValue v) ++ originalValue v selected :: [].map (originalValue v))
        next held (before ++ selected :: []) := by
      have hg := global_arrivals h (a+1-originalNext)
      rw [hnext, hfull] at hg
      have hb : a+1-originalNext = (a-originalNext)+1 := by omega
      have he : originalNext+(a-originalNext) = a := by omega
      simpa [hbefore, hselected, hb, List.range'_concat, he] using hg
    obtain ⟨next', held', hinv, hencode⟩ := global_update hglobal
    have htail : GlobalInvariant v (a+1) (originalHeld ++ List.range' originalNext (a-originalNext))
        next' held' (update before selected []).2 := by simpa [hbefore] using hinv
    have hrun := ih htail
    have he := hencode output
    rw [hselected] at he
    rw [he]
    have positive : 0 < a+1-originalNext := by omega
    simp only [transduce, positive, ite_true, hnext, hfull, hidx, updateCellsAt_split]
    simp [hrun]

/-- Exact standardized-output semantics from the initial state, even when
the original word has not finished and still holds labels. -/
theorem transduce_partial_initial_eq_encode {v : Nat}
    {code : List Letter} {output : List Nat}
    (hd : PartialDecodes 0 [] code output) :
    transduce v 0 [] code = some (encode 0 [] (deleteWord v output)) :=
  transduce_partial_eq_encode hd (global_initial v)

/-- The label-free executable transducer emits the encoding of the actual
standardized output prefix. -/
theorem transduceTags_partial_initial_eq_encode {v : Nat}
    {code : List Letter} {output : List Nat}
    (hd : PartialDecodes 0 [] code output) :
    transduceTags v 0 [] code = some (encode 0 [] (deleteWord v output)) := by
  rw [← show tags [] = [] from rfl]
  rw [transduce_tags]
  exact transduce_partial_initial_eq_encode hd

/-- Specialization to every take-prefix of an actual complete original word. -/
theorem transduceTags_take_eq_encode {v n : Nat}
    {code : List Letter} {output : List Nat}
    (hd : Decodes n 0 [] code output) (k : Nat) :
    transduceTags v 0 [] (code.take k) =
      some (encode 0 [] (deleteWord v (output.take k))) :=
  transduceTags_partial_initial_eq_encode (hd.partial_take k)

/-- Split-prefix form for incremental executions of a complete original word. -/
theorem transduceTags_prefix_eq_encode {v n : Nat}
    {front rest : List Letter} {output : List Nat}
    (hd : Decodes n 0 [] (front ++ rest) output) :
    transduceTags v 0 [] front =
      some (encode 0 [] (deleteWord v (output.take front.length))) :=
  transduceTags_partial_initial_eq_encode hd.partial_prefix

#print axioms Decodes.partial
#print axioms PartialDecodes.take
#print axioms Decodes.partial_take
#print axioms Decodes.partial_prefix
#print axioms PartialDecodes.encode_eq
#print axioms transduce_partial_eq_encode
#print axioms transduce_partial_initial_eq_encode
#print axioms transduceTags_partial_initial_eq_encode
#print axioms transduceTags_take_eq_encode
#print axioms transduceTags_prefix_eq_encode

end Shadow
end LazyCode
end StackSorting.Generalized
