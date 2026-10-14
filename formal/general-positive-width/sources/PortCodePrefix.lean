import EncodedPortReadInverse

namespace StackSorting.FinitePort

/-- Reads from a vertex depend only on labels at its rank prefix. Root ports
must be empty, because the dummy parent pointer of rank zero is unrestricted. -/
theorem readPort_eq_of_prefix {n colors relations} (T : RootedTree n)
    (C D : Code n colors relations)
    (hroot : ∀ v, v.val=0 → (C v).ports=[])
    (fuel : Nat) (v : Vertex n) (i : Nat)
    (heq : ∀ w, w.val ≤ v.val → C w=D w) :
    readPort T C fuel v i = readPort T D fuel v i := by
  induction fuel generalizing v i with
  | zero => cases i <;> rfl
  | succ fuel ih =>
    cases i with
    | zero => rfl
    | succ i =>
      by_cases hv : v.val=0
      · have hd : (D v).ports=[] :=
          (congrArg NodeLabel.ports (heq v (Nat.le_refl _))).symm.trans (hroot v hv)
        simp only [readPort,hroot v hv,hd,List.getElem?_nil,Option.bind_none]
      · simp only [readPort,heq v (Nat.le_refl _)]
        apply congrArg (fun f => ((D v).ports[i]?).bind f)
        funext e
        apply ih (T.parent v) e.parentPort
        intro w hw
        exact heq w (Nat.le_trans hw (Nat.le_of_lt (T.parent_lt v hv)))

#print axioms readPort_eq_of_prefix
end StackSorting.FinitePort
