import GeneralizedShadowRecognizer

/-! An executable certificate for finite, actually serialized recognizer tables.
All semantic steps are the existing rank transitions. No assumption about the
Python worklist is used; its returned finite output must pass the checker. -/
namespace StackSorting.Generalized.LazyCode.Shadow.Merging.Recognition
namespace BoundedTable
open List

structure Entry where
  height : Nat
  orders : List (List Nat)
  row : List (Letter × Option Nat)
  deriving DecidableEq, Repr

abbrev Data := List Entry

def emptyEntry : Entry := ⟨0, [], []⟩
def entry (t : Data) (q : Nat) : Entry := t[q]?.getD emptyEntry
def height (t : Data) (q : Nat) : Nat := (entry t q).height
def orders (t : Data) (q : Nat) : List (List Nat) := (entry t q).orders

/-- The outer option distinguishes missing columns from explicit dead (-1) edges. -/
def lookup (row : List (Letter × Option Nat)) (l : Letter) : Option (Option Nat) :=
  match row with
  | [] => none
  | (key, value) :: rest => if key = l then some value else lookup rest l

/-- Literal lookup: missing or dead maps to rejection; nonnegative IDs are live. -/
def table (t : Data) (q : Nat) (l : Letter) : Option Nat :=
  (lookup (entry t q).row l).join

def Legal (H h : Nat) : Letter → Prop
  | .N b => 0 < b ∧ h+b ≤ H
  | .H k => 0 < k ∧ k ≤ h

instance (H h : Nat) (l : Letter) : Decidable (Legal H h l) := by
  cases l <;> simp only [Legal] <;> infer_instance

/-- Exactly the Python dictionary insertion order. There are H columns when h<H. -/
def letters (H h : Nat) : List Letter :=
  ((List.range (H-h)).map (fun b => Letter.N (b+1))) ++
    ((List.range h).map (fun k => Letter.H (k+1)))

theorem mem_letters (H h : Nat) (l : Letter) : l ∈ letters H h ↔ Legal H h l := by
  cases l with
  | N b =>
    constructor
    · intro hm
      simp [letters] at hm
      obtain ⟨a, ha, hb⟩ := hm
      simp only [Legal]
      omega
    · intro hl
      simp only [Legal] at hl
      simp [letters]
      exact ⟨b-1, by omega, by omega⟩
  | H k =>
    constructor
    · intro hm
      simp [letters] at hm
      obtain ⟨a, ha, hb⟩ := hm
      simp only [Legal]
      omega
    · intro hl
      simp only [Legal] at hl
      simp [letters]
      exact ⟨k-1, by omega, by omega⟩

/-- Extensional set equality, with a finite decidable presentation. -/
def SetEq (xs ys : List (List Nat)) : Prop :=
  (∀ x ∈ xs, x ∈ ys) ∧ (∀ y ∈ ys, y ∈ xs)
instance (xs ys : List (List Nat)) : Decidable (SetEq xs ys) := by
  unfold SetEq
  infer_instance

theorem setEq_same {xs ys : List (List Nat)} (h : SetEq xs ys) : SameMembers xs ys :=
  fun x => ⟨h.1 x, h.2 x⟩

def StateOK (H : Nat) (st : Entry) : Prop :=
  st.orders ≠ [] ∧ st.height < H ∧
    ∀ physical ∈ st.orders, physical.Perm (List.range' 1 st.height)
instance (H : Nat) (st : Entry) : Decidable (StateOK H st) := by
  unfold StateOK
  infer_instance

def successors (r s : Nat) (t : Data) (q : Nat) (l : Letter) : List (List Nat) :=
  (orders t q).flatMap (rankTransition r s (height t q) l)

/-- Checks presence separately from rejection. A live target must be in range,
have the arithmetic target height, and represent the FULL transition set. -/
def EdgeOK (r s : Nat) (t : Data) (q : Nat) (l : Letter) : Prop :=
  match lookup (entry t q).row l with
  | none => False
  | some none => successors r s t q l = []
  | some (some q') => q' < t.length ∧
      height t q' = rankHeight (height t q) l ∧
      SetEq (orders t q') (successors r s t q l)
instance (r s : Nat) (t : Data) (q : Nat) (l : Letter) : Decidable (EdgeOK r s t q l) := by
  unfold EdgeOK
  split <;> infer_instance

def RowOK (r s H : Nat) (t : Data) (q : Nat) : Prop :=
  StateOK H (entry t q) ∧
    (entry t q).row.map Prod.fst = letters H (height t q) ∧
    ∀ l ∈ letters H (height t q), EdgeOK r s t q l
instance (r s H : Nat) (t : Data) (q : Nat) : Decidable (RowOK r s H t q) := by
  unfold RowOK
  infer_instance

def Certificate (r s H : Nat) (t : Data) : Prop :=
  t ≠ [] ∧ height t 0 = 0 ∧ orders t 0 = [[]] ∧
    ∀ q ∈ List.range t.length, RowOK r s H t q
instance (r s H : Nat) (t : Data) : Decidable (Certificate r s H t) := by
  unfold Certificate
  infer_instance

def certify (r s H : Nat) (t : Data) : Bool := decide (Certificate r s H t)

theorem certify_sound {r s H : Nat} {t : Data} (h : certify r s H t = true) :
    Certificate r s H t := of_decide_eq_true h

/-- Sequential finite conjunction; lets large artifacts be checked in independent
row-sized kernel reductions, without changing what the certificate means. -/
def AllRows (P : Nat → Prop) : Nat → Nat → Prop
  | _, 0 => True
  | start, n+1 => P start ∧ AllRows P (start+1) n

theorem allRows_sound {P : Nat → Prop} {start n : Nat} (h : AllRows P start n)
    (q : Nat) (lo : start ≤ q) (hi : q < start+n) : P q := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    by_cases he : q = start
    · subst q
      exact h.1
    · exact ih h.2 (by omega) (by omega)

theorem certify_of_rows {r s H : Nat} {t : Data}
    (hne : t ≠ []) (hh : height t 0 = 0) (ho : orders t 0 = [[]])
    (rows : AllRows (RowOK r s H t) 0 t.length) : certify r s H t = true := by
  apply decide_eq_true
  refine ⟨hne, hh, ho, ?_⟩
  intro q hq
  exact allRows_sound rows q (Nat.zero_le q) (by simpa using List.mem_range.mp hq)

theorem lookup_mem {row : List (Letter × Option Nat)} {l : Letter} {target : Option Nat}
    (h : lookup row l = some target) : l ∈ row.map Prod.fst := by
  induction row with
  | nil => simp [lookup] at h
  | cons e row ih =>
    rcases e with ⟨key, value⟩
    simp only [lookup] at h
    split at h
    · simp_all
    · exact List.mem_cons_of_mem key (ih h)

theorem lookup_of_live {t : Data} {q q' : Nat} {l : Letter}
    (h : table t q l = some q') : lookup (entry t q).row l = some (some q') := by
  unfold table at h
  cases he : lookup (entry t q).row l with
  | none => simp [he] at h
  | some value =>
    cases value with
    | none => simp [he] at h
    | some target => simpa [he] using h

theorem row_ok {r s H : Nat} {t : Data} (h : Certificate r s H t)
    {q : Nat} (hq : q < t.length) : RowOK r s H t q :=
  h.2.2.2 q (List.mem_range.mpr hq)

theorem legal_edge {r s H : Nat} {t : Data} (h : Certificate r s H t)
    {q : Nat} {l : Letter} (hq : q < t.length) (hl : Legal H (height t q) l) :
    EdgeOK r s t q l :=
  (row_ok h hq).2.2 l ((mem_letters _ _ _).mpr hl)

theorem live_legal {r s H : Nat} {t : Data} (h : Certificate r s H t)
    {q q' : Nat} {l : Letter} (hq : q < t.length) (hl : table t q l = some q') :
    Legal H (height t q) l := by
  have hm := lookup_mem (lookup_of_live hl)
  rw [(row_ok h hq).2.1] at hm
  exact (mem_letters _ _ _).mp hm

theorem live_exact {r s H : Nat} {t : Data} (h : Certificate r s H t)
    {q q' : Nat} {l : Letter} (hq : q < t.length) (hl : table t q l = some q') :
    q' < t.length ∧ height t q' = rankHeight (height t q) l ∧
      SameMembers (orders t q') (successors r s t q l) := by
  have he := legal_edge h hq (live_legal h hq hl)
  simp only [EdgeOK, lookup_of_live hl] at he
  exact ⟨he.1, he.2.1, setEq_same he.2.2⟩

theorem dead_iff_empty {r s H : Nat} {t : Data} (h : Certificate r s H t)
    {q : Nat} {l : Letter} (hq : q < t.length) (hl : Legal H (height t q) l) :
    table t q l = none ↔ successors r s t q l = [] := by
  have he := legal_edge h hq hl
  cases ht : lookup (entry t q).row l with
  | none => simp [EdgeOK, ht] at he
  | some value =>
    cases value with
    | none => simp [EdgeOK, ht] at he; simp [table, ht, he]
    | some q' =>
      simp only [EdgeOK, ht] at he
      have hn := (row_ok h he.1).1.1
      have hne : successors r s t q l ≠ [] := by
        intro hz
        have hempty : orders t q' = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro x hx
          have hh := he.2.2.1 x hx
          simp [hz] at hh
        exact hn hempty
      simp [table, ht, hne]

theorem all_columns_present {r s H : Nat} {t : Data} (h : Certificate r s H t)
    {q : Nat} {l : Letter} (hq : q < t.length) (hl : Legal H (height t q) l) :
    ∃ value, lookup (entry t q).row l = some value := by
  have he := legal_edge h hq hl
  cases ht : lookup (entry t q).row l with
  | none => simp [EdgeOK, ht] at he
  | some value => exact ⟨value, rfl⟩

theorem reachable_in_range {r s H : Nat} {t : Data} (h : Certificate r s H t)
    {q : Nat} (hr : TableReachable (table t) 0 q) : q < t.length := by
  induction hr with
  | initial => exact List.length_pos_iff.mpr h.1
  | step _ edge ih => exact (live_exact h ih edge).1

/-- This instantiates the PREVIOUS local table contract from a successful finite
certificate. No local semantic table obligations remain for a concrete caller. -/
theorem checked_live_rank_table {r s H : Nat} {t : Data} (h : certify r s H t = true) :
    LiveRankTable (table t) (height t) (orders t) 0 r s := by
  have hc := certify_sound h
  refine ⟨hc.2.1, ?_, ?_⟩
  · simp only [hc.2.2.1]
    exact same_refl _
  · intro q l q' hr he
    exact (live_exact hc (reachable_in_range hc hr) he).2

/-- Complete bounded semantics of the actual indexed data accepted by the
certifier. Invalid/out-of-bound N letters are intentionally excluded. -/
theorem checked_constructed_table_complete {r s H : Nat} {t : Data}
    (h : certify r s H t = true) :
    height t 0 = 0 ∧ orders t 0 = [[]] ∧
    (∀ q, q < t.length →
      orders t q ≠ [] ∧ height t q < H ∧
        ∀ physical ∈ orders t q, physical.Perm (List.range' 1 (height t q))) ∧
    (∀ q l, q < t.length → Legal H (height t q) l →
      (∃ value, lookup (entry t q).row l = some value) ∧
      (table t q l = none ↔ successors r s t q l = []) ∧
      (∀ q', table t q l = some q' → q' < t.length ∧
        height t q' = rankHeight (height t q) l ∧
        SameMembers (orders t q') (successors r s t q l))) := by
  have hc := certify_sound h
  refine ⟨hc.2.1, hc.2.2.1, ?_, ?_⟩
  · intro q hq
    exact (row_ok hc hq).1
  · intro q l hq hl
    exact ⟨all_columns_present hc hq hl, dead_iff_empty hc hq hl,
      fun _ hq' => live_exact hc hq hq'⟩

/-- Even though illegal letters may have nonempty unbounded semantic successors,
the actual checked dictionary has no such column and rejects them. -/
theorem invalid_none {r s H : Nat} {t : Data} (h : Certificate r s H t)
    {q : Nat} {l : Letter} (hq : q < t.length) (hl : ¬ Legal H (height t q) l) :
    table t q l = none := by
  cases he : table t q l with
  | none => rfl
  | some q' => exact False.elim (hl (live_legal h hq he))

/-- A registered state's interpretation accepts the empty physical stack exactly
at height zero. Nonempty live states are derived from the certificate. -/
theorem nil_mem_iff_height_zero {r s H : Nat} {t : Data} (h : Certificate r s H t)
    {q : Nat} (hq : q < t.length) : [] ∈ orders t q ↔ height t q = 0 := by
  have hs := (row_ok h hq).1
  constructor
  · intro hm
    have hh := (hs.2.2 [] hm).length_eq
    simpa [height] using hh.symm
  · intro hz
    obtain ⟨physical, hp⟩ := List.exists_mem_of_ne_nil _ hs.1
    have hperm := hs.2.2 physical hp
    have he : physical = [] := List.perm_nil.mp (by simpa [show (entry t q).height = 0 from hz] using hperm)
    simpa [he, orders] using hp

#print axioms certify_sound
#print axioms checked_live_rank_table
#print axioms checked_constructed_table_complete
#print axioms nil_mem_iff_height_zero
#print axioms certify_of_rows
end BoundedTable
end StackSorting.Generalized.LazyCode.Shadow.Merging.Recognition
