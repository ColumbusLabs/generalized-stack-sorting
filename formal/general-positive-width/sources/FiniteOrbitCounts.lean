import RectangleVertexOrbits

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

/-- Explicit finite cardinality witness, with both encoding inverses proved. -/
structure FiniteCode (α : Type) (n : Nat) where
  encode : α → Fin n
  decode : Fin n → α
  decode_encode : ∀ a, decode (encode a)=a
  encode_decode : ∀ i, encode (decode i)=i

theorem FiniteCode.injective {α n} (C : FiniteCode α n) {a b : α}
    (h : C.encode a=C.encode b) : a=b := by
  have he := congrArg C.decode h
  simpa only [C.decode_encode] using he

def productCode (m n : Nat) (hn : 0<n) : FiniteCode (Fin m × Fin n) (m*n) where
  encode := fun ⟨x,y⟩ => ⟨x.val*n+y.val,by
    have hx := x.isLt
    have hy := y.isLt
    have hm : (x.val+1)*n≤m*n := Nat.mul_le_mul_right n (by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hm
    omega⟩
  decode := fun i => (⟨i.val/n,(Nat.div_lt_iff_lt_mul hn).mpr i.isLt⟩,
    ⟨i.val%n,Nat.mod_lt _ hn⟩)
  decode_encode := by
    intro a
    obtain ⟨x,y⟩ := a
    apply Prod.ext <;> apply Fin.ext
    · change (x.val*n+y.val)/n=x.val
      rw [Nat.mul_comm x.val n,Nat.mul_add_div hn,Nat.div_eq_of_lt y.isLt]
      omega
    · change (x.val*n+y.val)%n=y.val
      simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt y.isLt]
  encode_decode := by
    intro i
    apply Fin.ext
    change (i.val/n)*n+i.val%n=i.val
    simpa only [Nat.mul_comm] using Nat.div_add_mod i.val n

def sumCode {α β m n} (A : FiniteCode α m) (B : FiniteCode β n) :
    FiniteCode (Sum α β) (m+n) where
  encode := fun v => match v with
    | .inl a => ⟨(A.encode a).val,by have := (A.encode a).isLt; omega⟩
    | .inr b => ⟨m+(B.encode b).val,by have := (B.encode b).isLt; omega⟩
  decode := fun i => if hi : i.val<m then .inl (A.decode ⟨i.val,hi⟩)
    else .inr (B.decode ⟨i.val-m,by have := i.isLt; omega⟩)
  decode_encode := by
    intro v
    cases v with
    | inl a =>
      simp only [dite_eq_left (A.encode a).isLt]
      exact congrArg Sum.inl (A.decode_encode a)
    | inr b =>
      have hn : ¬m+(B.encode b).val<m := by omega
      simp only [dite_eq_right hn]
      have he : (⟨m+(B.encode b).val-m,by have := (B.encode b).isLt; omega⟩ : Fin n)=B.encode b := by
        apply Fin.ext
        change m+(B.encode b).val-m=(B.encode b).val
        omega
      rw [he,B.decode_encode]
  encode_decode := by
    intro i
    by_cases hi : i.val<m
    · simp only [dite_eq_left hi]
      change (⟨(A.encode (A.decode ⟨i.val,_⟩)).val,_⟩ : Fin (m+n))=i
      apply Fin.ext
      change (A.encode (A.decode ⟨i.val,hi⟩)).val=i.val
      rw [A.encode_decode]
    · simp only [dite_eq_right hi]
      change (⟨m+(B.encode (B.decode ⟨i.val-m,_⟩)).val,_⟩ : Fin (m+n))=i
      apply Fin.ext
      change m+(B.encode (B.decode ⟨i.val-m,_⟩)).val=i.val
      rw [B.encode_decode]
      change m+(i.val-m)=i.val
      omega

def optionCode {α n} (C : FiniteCode α n) : FiniteCode (Option α) (n+1) where
  encode := fun v => match v with
    | none => ⟨0,by omega⟩
    | some a => ⟨(C.encode a).val+1,by have := (C.encode a).isLt; omega⟩
  decode := fun i => if hi : i.val=0 then none
    else some (C.decode ⟨i.val-1,by have := i.isLt; omega⟩)
  decode_encode := by
    intro v
    cases v with
    | none => rfl
    | some a =>
      have hn : (C.encode a).val+1≠0 := by omega
      simp only [dite_eq_right hn]
      have he : (⟨(C.encode a).val+1-1,by have := (C.encode a).isLt; omega⟩ : Fin n)=C.encode a := by
        apply Fin.ext
        change (C.encode a).val+1-1=(C.encode a).val
        omega
      rw [he,C.decode_encode]
  encode_decode := by
    intro i
    by_cases hi : i.val=0
    · simp only [dite_eq_left hi]
      apply Fin.ext
      change 0=i.val
      exact hi.symm
    · simp only [dite_eq_right hi]
      change (⟨(C.encode (C.decode ⟨i.val-1,_⟩)).val+1,_⟩ : Fin (n+1))=i
      apply Fin.ext
      change (C.encode (C.decode ⟨i.val-1,_⟩)).val+1=i.val
      rw [C.encode_decode]
      change i.val-1+1=i.val
      exact Nat.sub_add_cancel (by omega)

/-- A cardinality certificate for the actual components of a permutation.
The connectivity equivalence is a proved field, never assumed by callers. -/
structure OrbitCount {α : Type} (f : α → α) (n : Nat) where
  label : α → Fin n
  surjective : ∀ i, ∃ a, label a=i
  exact_components : ∀ a b, Walk (OrbitStep f) (fun _ => True) a b ↔ label a=label b

def orbitCountFromCode {α β n} (f : α → α) (label : α → β) (C : FiniteCode β n)
    (hs : ∀ b, ∃ a, label a=b)
    (he : ∀ a b, Walk (OrbitStep f) (fun _ => True) a b ↔ label a=label b) : OrbitCount f n where
  label := C.encode ∘ label
  surjective := by
    intro i
    obtain ⟨a,ha⟩ := hs (C.decode i)
    exact ⟨a,by change C.encode (label a)=i; rw [ha,C.encode_decode]⟩
  exact_components := by
    intro a b
    constructor
    · intro h
      exact congrArg C.encode ((he a b).mp h)
    · intro h
      exact (he a b).mpr (C.injective h)

end StackSorting.GraphWidth.UCurve.PlaneGrid
