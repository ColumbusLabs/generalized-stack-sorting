import UnitSplitFactorSharedNodes043
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn2465E : RingExpr := (.mul usfn362E usfn2464E)
def usfn2465P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-11) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit)))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.add (5) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-3) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)) (.num (0)))))))))))))
theorem usfn2465_norm : (reflectRing usfn2465E).toPoly=usfn2465P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn2464E).toPoly=usfn2465P
  rw [usfn362_norm, usfn2464_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn2464P == usfn2465P)

def usfn2466E : RingExpr := (.mul usfn382E usfn2465E)
def usfn2466P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-11) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit)))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.add (5) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit))) (.num (0)))))))))))))
theorem usfn2466_norm : (reflectRing usfn2466E).toPoly=usfn2466P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn2465E).toPoly=usfn2466P
  rw [usfn382_norm, usfn2465_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn2465P == usfn2466P)

def usfn2467E : RingExpr := (.mul usfn2E usfn2466E)
def usfn2467P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-11) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (5) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))))
theorem usfn2467_norm : (reflectRing usfn2467E).toPoly=usfn2467P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn2466E).toPoly=usfn2467P
  rw [usfn2_norm, usfn2466_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn2466P == usfn2467P)

def usfn2468E : RingExpr := (.mul usfn1E usfn2467E)
def usfn2468P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-11) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (5) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))))
theorem usfn2468_norm : (reflectRing usfn2468E).toPoly=usfn2468P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn2467E).toPoly=usfn2468P
  rw [usfn1_norm, usfn2467_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn2467P == usfn2468P)

def usfn2469E : RingExpr := (.mul usfn1944E usfn2468E)
def usfn2469P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-44) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (20) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))))
theorem usfn2469_norm : (reflectRing usfn2469E).toPoly=usfn2469P := by
  change (reflectRing usfn1944E).toPoly.mul (reflectRing usfn2468E).toPoly=usfn2469P
  rw [usfn1944_norm, usfn2468_norm]
  exact eq_of_beq (by decide : usfn1944P.mul usfn2468P == usfn2469P)

def usfn2470E : RingExpr := (.mul usfn751E usfn2469E)
def usfn2470P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-44) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (20) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-12) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.num (0)))))))))))))
theorem usfn2470_norm : (reflectRing usfn2470E).toPoly=usfn2470P := by
  change (reflectRing usfn751E).toPoly.mul (reflectRing usfn2469E).toPoly=usfn2470P
  rw [usfn751_norm, usfn2469_norm]
  exact eq_of_beq (by decide : usfn751P.mul usfn2469P == usfn2470P)

def usfn2471E : RingExpr := (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-2)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int 2) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.var 3) (.mul (.var 8) (.var 4))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))) (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))))))))))))))))
def usfn2471P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-24) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn2471_norm : (reflectRing usfn2471E).toPoly=usfn2471P := by
  exact eq_of_beq (by decide : (reflectRing usfn2471E).toPoly == usfn2471P)

def usfn2472E : RingExpr := (.mul usfn1972E usfn2471E)
def usfn2472P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-8) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.num (0))))))))))
theorem usfn2472_norm : (reflectRing usfn2472E).toPoly=usfn2472P := by
  change (reflectRing usfn1972E).toPoly.mul (reflectRing usfn2471E).toPoly=usfn2472P
  rw [usfn1972_norm, usfn2471_norm]
  exact eq_of_beq (by decide : usfn1972P.mul usfn2471P == usfn2472P)

def usfn2473E : RingExpr := (.mul (.mul (.var 14) (.mul (.var 1) (.pow (.var 2) 3))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))
def usfn2473P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit))))))))) (.num (0))))
theorem usfn2473_norm : (reflectRing usfn2473E).toPoly=usfn2473P := by
  exact eq_of_beq (by decide : (reflectRing usfn2473E).toPoly == usfn2473P)

def usfn2474E : RingExpr := (.mul (.int (-3)) (.mul (.var 10) (.var 8)))
def usfn2474P : Lean.Grind.CommRing.Poly := (.add (-3) (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)) (.num (0)))
theorem usfn2474_norm : (reflectRing usfn2474E).toPoly=usfn2474P := by
  exact eq_of_beq (by decide : (reflectRing usfn2474E).toPoly == usfn2474P)

def usfn2475E : RingExpr := (.mul (.var 10) (.mul (.var 3) (.pow (.var 8) 2)))
def usfn2475P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn2475_norm : (reflectRing usfn2475E).toPoly=usfn2475P := by
  exact eq_of_beq (by decide : (reflectRing usfn2475E).toPoly == usfn2475P)

def usfn2476E : RingExpr := (.mul (.int (-4)) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))
def usfn2476P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2476_norm : (reflectRing usfn2476E).toPoly=usfn2476P := by
  exact eq_of_beq (by decide : (reflectRing usfn2476E).toPoly == usfn2476P)

def usfn2477E : RingExpr := (.mul (.int 4) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.pow (.var 4) 2)))))
def usfn2477P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2477_norm : (reflectRing usfn2477E).toPoly=usfn2477P := by
  exact eq_of_beq (by decide : (reflectRing usfn2477E).toPoly == usfn2477P)

def usfn2478E : RingExpr := (.mul (.int 4) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 10) 2)))))
def usfn2478P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0)))
theorem usfn2478_norm : (reflectRing usfn2478E).toPoly=usfn2478P := by
  exact eq_of_beq (by decide : (reflectRing usfn2478E).toPoly == usfn2478P)

def usfn2479E : RingExpr := (.mul (.int 11) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9)))))
def usfn2479P : Lean.Grind.CommRing.Poly := (.add (11) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2479_norm : (reflectRing usfn2479E).toPoly=usfn2479P := by
  exact eq_of_beq (by decide : (reflectRing usfn2479E).toPoly == usfn2479P)

def usfn2480E : RingExpr := (.mul (.int (-26)) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))))
def usfn2480P : Lean.Grind.CommRing.Poly := (.add (-26) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))
theorem usfn2480_norm : (reflectRing usfn2480E).toPoly=usfn2480P := by
  exact eq_of_beq (by decide : (reflectRing usfn2480E).toPoly == usfn2480P)

def usfn2481E : RingExpr := (.mul (.int (-4)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 3))))))
def usfn2481P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2481_norm : (reflectRing usfn2481E).toPoly=usfn2481P := by
  exact eq_of_beq (by decide : (reflectRing usfn2481E).toPoly == usfn2481P)

def usfn2482E : RingExpr := (.mul (.int (-4)) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))
def usfn2482P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2482_norm : (reflectRing usfn2482E).toPoly=usfn2482P := by
  exact eq_of_beq (by decide : (reflectRing usfn2482E).toPoly == usfn2482P)

def usfn2483E : RingExpr := (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2))))))
def usfn2483P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2483_norm : (reflectRing usfn2483E).toPoly=usfn2483P := by
  exact eq_of_beq (by decide : (reflectRing usfn2483E).toPoly == usfn2483P)

def usfn2484E : RingExpr := (.mul (.int 6) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))
def usfn2484P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2484_norm : (reflectRing usfn2484E).toPoly=usfn2484P := by
  exact eq_of_beq (by decide : (reflectRing usfn2484E).toPoly == usfn2484P)

def usfn2485E : RingExpr := (.mul (.int 8) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 4) 3))))))
def usfn2485P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))
theorem usfn2485_norm : (reflectRing usfn2485E).toPoly=usfn2485P := by
  exact eq_of_beq (by decide : (reflectRing usfn2485E).toPoly == usfn2485P)

def usfn2486E : RingExpr := (.mul (.int 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))
def usfn2486P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))
theorem usfn2486_norm : (reflectRing usfn2486E).toPoly=usfn2486P := by
  exact eq_of_beq (by decide : (reflectRing usfn2486E).toPoly == usfn2486P)

def usfn2487E : RingExpr := (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))
def usfn2487P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))
theorem usfn2487_norm : (reflectRing usfn2487E).toPoly=usfn2487P := by
  exact eq_of_beq (by decide : (reflectRing usfn2487E).toPoly == usfn2487P)

def usfn2488E : RingExpr := (.add usfn2486E usfn2487E)
def usfn2488P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn2488_norm : (reflectRing usfn2488E).toPoly=usfn2488P := by
  change (reflectRing usfn2486E).toPoly.combine (reflectRing usfn2487E).toPoly=usfn2488P
  rw [usfn2486_norm, usfn2487_norm]
  exact eq_of_beq (by decide : usfn2486P.combine usfn2487P == usfn2488P)

def usfn2489E : RingExpr := (.add usfn2485E usfn2488E)
def usfn2489P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0))))))))
theorem usfn2489_norm : (reflectRing usfn2489E).toPoly=usfn2489P := by
  change (reflectRing usfn2485E).toPoly.combine (reflectRing usfn2488E).toPoly=usfn2489P
  rw [usfn2485_norm, usfn2488_norm]
  exact eq_of_beq (by decide : usfn2485P.combine usfn2488P == usfn2489P)

def usfn2490E : RingExpr := (.add usfn2484E usfn2489E)
def usfn2490P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))))))))
theorem usfn2490_norm : (reflectRing usfn2490E).toPoly=usfn2490P := by
  change (reflectRing usfn2484E).toPoly.combine (reflectRing usfn2489E).toPoly=usfn2490P
  rw [usfn2484_norm, usfn2489_norm]
  exact eq_of_beq (by decide : usfn2484P.combine usfn2489P == usfn2490P)

def usfn2491E : RingExpr := (.add usfn2483E usfn2490E)
def usfn2491P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn2491_norm : (reflectRing usfn2491E).toPoly=usfn2491P := by
  change (reflectRing usfn2483E).toPoly.combine (reflectRing usfn2490E).toPoly=usfn2491P
  rw [usfn2483_norm, usfn2490_norm]
  exact eq_of_beq (by decide : usfn2483P.combine usfn2490P == usfn2491P)

def usfn2492E : RingExpr := (.add usfn2482E usfn2491E)
def usfn2492P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))
theorem usfn2492_norm : (reflectRing usfn2492E).toPoly=usfn2492P := by
  change (reflectRing usfn2482E).toPoly.combine (reflectRing usfn2491E).toPoly=usfn2492P
  rw [usfn2482_norm, usfn2491_norm]
  exact eq_of_beq (by decide : usfn2482P.combine usfn2491P == usfn2492P)

def usfn2493E : RingExpr := (.add usfn2481E usfn2492E)
def usfn2493P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))
theorem usfn2493_norm : (reflectRing usfn2493E).toPoly=usfn2493P := by
  change (reflectRing usfn2481E).toPoly.combine (reflectRing usfn2492E).toPoly=usfn2493P
  rw [usfn2481_norm, usfn2492_norm]
  exact eq_of_beq (by decide : usfn2481P.combine usfn2492P == usfn2493P)

def usfn2494E : RingExpr := (.add usfn2480E usfn2493E)
def usfn2494P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-26) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))))
theorem usfn2494_norm : (reflectRing usfn2494E).toPoly=usfn2494P := by
  change (reflectRing usfn2480E).toPoly.combine (reflectRing usfn2493E).toPoly=usfn2494P
  rw [usfn2480_norm, usfn2493_norm]
  exact eq_of_beq (by decide : usfn2480P.combine usfn2493P == usfn2494P)

def usfn2495E : RingExpr := (.add usfn2479E usfn2494E)
def usfn2495P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-26) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (11) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))
theorem usfn2495_norm : (reflectRing usfn2495E).toPoly=usfn2495P := by
  change (reflectRing usfn2479E).toPoly.combine (reflectRing usfn2494E).toPoly=usfn2495P
  rw [usfn2479_norm, usfn2494_norm]
  exact eq_of_beq (by decide : usfn2479P.combine usfn2494P == usfn2495P)

def usfn2496E : RingExpr := (.add usfn2478E usfn2495E)
def usfn2496P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-26) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (11) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))))))
theorem usfn2496_norm : (reflectRing usfn2496E).toPoly=usfn2496P := by
  change (reflectRing usfn2478E).toPoly.combine (reflectRing usfn2495E).toPoly=usfn2496P
  rw [usfn2478_norm, usfn2495_norm]
  exact eq_of_beq (by decide : usfn2478P.combine usfn2495P == usfn2496P)

def usfn2497E : RingExpr := (.add usfn2477E usfn2496E)
def usfn2497P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-26) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (11) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))
theorem usfn2497_norm : (reflectRing usfn2497E).toPoly=usfn2497P := by
  change (reflectRing usfn2477E).toPoly.combine (reflectRing usfn2496E).toPoly=usfn2497P
  rw [usfn2477_norm, usfn2496_norm]
  exact eq_of_beq (by decide : usfn2477P.combine usfn2496P == usfn2497P)

def usfn2498E : RingExpr := (.add usfn2476E usfn2497E)
def usfn2498P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-26) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (11) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))))))))
theorem usfn2498_norm : (reflectRing usfn2498E).toPoly=usfn2498P := by
  change (reflectRing usfn2476E).toPoly.combine (reflectRing usfn2497E).toPoly=usfn2498P
  rw [usfn2476_norm, usfn2497_norm]
  exact eq_of_beq (by decide : usfn2476P.combine usfn2497P == usfn2498P)

def usfn2499E : RingExpr := (.add usfn958E usfn2498E)
def usfn2499P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-26) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (11) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit))) (.num (0))))))))))))))))))
theorem usfn2499_norm : (reflectRing usfn2499E).toPoly=usfn2499P := by
  change (reflectRing usfn958E).toPoly.combine (reflectRing usfn2498E).toPoly=usfn2499P
  rw [usfn958_norm, usfn2498_norm]
  exact eq_of_beq (by decide : usfn958P.combine usfn2498P == usfn2499P)

def usfn2500E : RingExpr := (.add usfn2475E usfn2499E)
def usfn2500P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-26) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))) (.add (11) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))))))))))))))))))
theorem usfn2500_norm : (reflectRing usfn2500E).toPoly=usfn2500P := by
  change (reflectRing usfn2475E).toPoly.combine (reflectRing usfn2499E).toPoly=usfn2500P
  rw [usfn2475_norm, usfn2499_norm]
  exact eq_of_beq (by decide : usfn2475P.combine usfn2499P == usfn2500P)

def usfn2501E : RingExpr := (.add usfn2474E usfn2500E)
def usfn2501P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-26) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))) (.add (11) (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit))) (.add (-3) (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)) (.num (0))))))))))))))))))))
theorem usfn2501_norm : (reflectRing usfn2501E).toPoly=usfn2501P := by
  change (reflectRing usfn2474E).toPoly.combine (reflectRing usfn2500E).toPoly=usfn2501P
  rw [usfn2474_norm, usfn2500_norm]
  exact eq_of_beq (by decide : usfn2474P.combine usfn2500P == usfn2501P)

def usfn2502E : RingExpr := (.mul usfn4E usfn2501E)
def usfn2502P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-26) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))) (.add (11) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (-3) (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)) (.num (0))))))))))))))))))))
theorem usfn2502_norm : (reflectRing usfn2502E).toPoly=usfn2502P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn2501E).toPoly=usfn2502P
  rw [usfn4_norm, usfn2501_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn2501P == usfn2502P)

def usfn2503E : RingExpr := (.mul usfn382E usfn2502E)
def usfn2503P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-26) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))) (.add (11) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))))))))))
theorem usfn2503_norm : (reflectRing usfn2503E).toPoly=usfn2503P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn2502E).toPoly=usfn2503P
  rw [usfn382_norm, usfn2502_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn2502P == usfn2503P)

def usfn2504E : RingExpr := (.mul usfn1E usfn2503E)
def usfn2504P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-26) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (11) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ .unit))))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))))))
theorem usfn2504_norm : (reflectRing usfn2504E).toPoly=usfn2504P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn2503E).toPoly=usfn2504P
  rw [usfn1_norm, usfn2503_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn2503P == usfn2504P)

def usfn2505E : RingExpr := (.mul usfn360E usfn2504E)
def usfn2505P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-26) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (11) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-3) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.num (0))))))))))))))))))))
theorem usfn2505_norm : (reflectRing usfn2505E).toPoly=usfn2505P := by
  change (reflectRing usfn360E).toPoly.mul (reflectRing usfn2504E).toPoly=usfn2505P
  rw [usfn360_norm, usfn2504_norm]
  exact eq_of_beq (by decide : usfn360P.mul usfn2504P == usfn2505P)

def usfn2506E : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.var 3)))
def usfn2506P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ .unit)) (.num (0)))
theorem usfn2506_norm : (reflectRing usfn2506E).toPoly=usfn2506P := by
  exact eq_of_beq (by decide : (reflectRing usfn2506E).toPoly == usfn2506P)

def usfn2507E : RingExpr := (.mul (.int 4) (.mul (.var 9) (.pow (.var 4) 2)))
def usfn2507P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))
theorem usfn2507_norm : (reflectRing usfn2507E).toPoly=usfn2507P := by
  exact eq_of_beq (by decide : (reflectRing usfn2507E).toPoly == usfn2507P)

def usfn2508E : RingExpr := (.mul (.var 3) (.mul (.var 8) (.var 4)))
def usfn2508P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit))) (.num (0)))
theorem usfn2508_norm : (reflectRing usfn2508E).toPoly=usfn2508P := by
  exact eq_of_beq (by decide : (reflectRing usfn2508E).toPoly == usfn2508P)

def usfn2509E : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))
def usfn2509P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem usfn2509_norm : (reflectRing usfn2509E).toPoly=usfn2509P := by
  exact eq_of_beq (by decide : (reflectRing usfn2509E).toPoly == usfn2509P)

def usfn2510E : RingExpr := (.mul (.int 4) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2))))
def usfn2510P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn2510_norm : (reflectRing usfn2510E).toPoly=usfn2510P := by
  exact eq_of_beq (by decide : (reflectRing usfn2510E).toPoly == usfn2510P)

def usfn2511E : RingExpr := (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))
def usfn2511P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2511_norm : (reflectRing usfn2511E).toPoly=usfn2511P := by
  exact eq_of_beq (by decide : (reflectRing usfn2511E).toPoly == usfn2511P)

def usfn2512E : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))
def usfn2512P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2512_norm : (reflectRing usfn2512E).toPoly=usfn2512P := by
  exact eq_of_beq (by decide : (reflectRing usfn2512E).toPoly == usfn2512P)

def usfn2513E : RingExpr := (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))) (.add (.mul (.int (-12)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))))))))
def usfn2513P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))
theorem usfn2513_norm : (reflectRing usfn2513E).toPoly=usfn2513P := by
  exact eq_of_beq (by decide : (reflectRing usfn2513E).toPoly == usfn2513P)

def usfn2514E : RingExpr := (.add usfn2512E usfn2513E)
def usfn2514P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn2514_norm : (reflectRing usfn2514E).toPoly=usfn2514P := by
  change (reflectRing usfn2512E).toPoly.combine (reflectRing usfn2513E).toPoly=usfn2514P
  rw [usfn2512_norm, usfn2513_norm]
  exact eq_of_beq (by decide : usfn2512P.combine usfn2513P == usfn2514P)

def usfn2515E : RingExpr := (.add usfn2511E usfn2514E)
def usfn2515P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))))
theorem usfn2515_norm : (reflectRing usfn2515E).toPoly=usfn2515P := by
  change (reflectRing usfn2511E).toPoly.combine (reflectRing usfn2514E).toPoly=usfn2515P
  rw [usfn2511_norm, usfn2514_norm]
  exact eq_of_beq (by decide : usfn2511P.combine usfn2514P == usfn2515P)

def usfn2516E : RingExpr := (.add usfn2510E usfn2515E)
def usfn2516P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))
theorem usfn2516_norm : (reflectRing usfn2516E).toPoly=usfn2516P := by
  change (reflectRing usfn2510E).toPoly.combine (reflectRing usfn2515E).toPoly=usfn2516P
  rw [usfn2510_norm, usfn2515_norm]
  exact eq_of_beq (by decide : usfn2510P.combine usfn2515P == usfn2516P)

def usfn2517E : RingExpr := (.add usfn2509E usfn2516E)
def usfn2517P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))
theorem usfn2517_norm : (reflectRing usfn2517E).toPoly=usfn2517P := by
  change (reflectRing usfn2509E).toPoly.combine (reflectRing usfn2516E).toPoly=usfn2517P
  rw [usfn2509_norm, usfn2516_norm]
  exact eq_of_beq (by decide : usfn2509P.combine usfn2516P == usfn2517P)

def usfn2518E : RingExpr := (.add usfn2508E usfn2517E)
def usfn2518P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit))) (.num (0)))))))))))))
theorem usfn2518_norm : (reflectRing usfn2518E).toPoly=usfn2518P := by
  change (reflectRing usfn2508E).toPoly.combine (reflectRing usfn2517E).toPoly=usfn2518P
  rw [usfn2508_norm, usfn2517_norm]
  exact eq_of_beq (by decide : usfn2508P.combine usfn2517P == usfn2518P)

def usfn2519E : RingExpr := (.add usfn2507E usfn2518E)
def usfn2519P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))))))
theorem usfn2519_norm : (reflectRing usfn2519E).toPoly=usfn2519P := by
  change (reflectRing usfn2507E).toPoly.combine (reflectRing usfn2518E).toPoly=usfn2519P
  rw [usfn2507_norm, usfn2518_norm]
  exact eq_of_beq (by decide : usfn2507P.combine usfn2518P == usfn2519P)

def usfn2520E : RingExpr := (.add usfn2506E usfn2519E)
def usfn2520P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ .unit)) (.num (0)))))))))))))))
theorem usfn2520_norm : (reflectRing usfn2520E).toPoly=usfn2520P := by
  change (reflectRing usfn2506E).toPoly.combine (reflectRing usfn2519E).toPoly=usfn2520P
  rw [usfn2506_norm, usfn2519_norm]
  exact eq_of_beq (by decide : usfn2506P.combine usfn2519P == usfn2520P)

def usfn2521E : RingExpr := (.add usfn410E usfn2520E)
def usfn2521P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ .unit)) (.add (-2) (.mult ⟨4,1⟩ .unit) (.num (0))))))))))))))))
theorem usfn2521_norm : (reflectRing usfn2521E).toPoly=usfn2521P := by
  change (reflectRing usfn410E).toPoly.combine (reflectRing usfn2520E).toPoly=usfn2521P
  rw [usfn410_norm, usfn2520_norm]
  exact eq_of_beq (by decide : usfn410P.combine usfn2520P == usfn2521P)

def usfn2522E : RingExpr := (.mul usfn52E usfn2521E)
def usfn2522P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,3⟩ .unit))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)) (.num (0))))))))))))))))
theorem usfn2522_norm : (reflectRing usfn2522E).toPoly=usfn2522P := by
  change (reflectRing usfn52E).toPoly.mul (reflectRing usfn2521E).toPoly=usfn2522P
  rw [usfn52_norm, usfn2521_norm]
  exact eq_of_beq (by decide : usfn52P.mul usfn2521P == usfn2522P)

def usfn2523E : RingExpr := (.mul usfn409E usfn2522E)
def usfn2523P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-12) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit)))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,3⟩ .unit))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit))) (.num (0))))))))))))))))
theorem usfn2523_norm : (reflectRing usfn2523E).toPoly=usfn2523P := by
  change (reflectRing usfn409E).toPoly.mul (reflectRing usfn2522E).toPoly=usfn2523P
  rw [usfn409_norm, usfn2522_norm]
  exact eq_of_beq (by decide : usfn409P.mul usfn2522P == usfn2523P)

def usfn2524E : RingExpr := (.mul usfn2E usfn2523E)
def usfn2524P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))
theorem usfn2524_norm : (reflectRing usfn2524E).toPoly=usfn2524P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn2523E).toPoly=usfn2524P
  rw [usfn2_norm, usfn2523_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn2523P == usfn2524P)

def usfn2525E : RingExpr := (.mul usfn1E usfn2524E)
def usfn2525P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))))
theorem usfn2525_norm : (reflectRing usfn2525E).toPoly=usfn2525P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn2524E).toPoly=usfn2525P
  rw [usfn1_norm, usfn2524_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn2524P == usfn2525P)

def usfn2526E : RingExpr := (.mul usfn361E usfn2525E)
def usfn2526P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-24) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))))
theorem usfn2526_norm : (reflectRing usfn2526E).toPoly=usfn2526P := by
  change (reflectRing usfn361E).toPoly.mul (reflectRing usfn2525E).toPoly=usfn2526P
  rw [usfn361_norm, usfn2525_norm]
  exact eq_of_beq (by decide : usfn361P.mul usfn2525P == usfn2526P)

def usfn2527E : RingExpr := (.mul usfn788E usfn2526E)
def usfn2527P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.num (0))))))))))))))))
theorem usfn2527_norm : (reflectRing usfn2527E).toPoly=usfn2527P := by
  change (reflectRing usfn788E).toPoly.mul (reflectRing usfn2526E).toPoly=usfn2527P
  rw [usfn788_norm, usfn2526_norm]
  exact eq_of_beq (by decide : usfn788P.mul usfn2526P == usfn2527P)

def usfn2528E : RingExpr := (.mul (.mul (.var 14) (.mul (.var 1) (.pow (.var 2) 2))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))
def usfn2528P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))) (.num (0))))
theorem usfn2528_norm : (reflectRing usfn2528E).toPoly=usfn2528P := by
  exact eq_of_beq (by decide : (reflectRing usfn2528E).toPoly == usfn2528P)

def usfn2529E : RingExpr := (.mul (.mul (.var 15) (.mul (.var 1) (.pow (.var 2) 2))) (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.var 4) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-1)) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))))))))))))))
def usfn2529P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.num (0))))))))
theorem usfn2529_norm : (reflectRing usfn2529E).toPoly=usfn2529P := by
  exact eq_of_beq (by decide : (reflectRing usfn2529E).toPoly == usfn2529P)

def usfn2530E : RingExpr := (.mul (.mul (.var 16) (.mul (.var 1) (.pow (.var 2) 2))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))
def usfn2530P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit)))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit))))))))) (.num (0))))
theorem usfn2530_norm : (reflectRing usfn2530E).toPoly=usfn2530P := by
  exact eq_of_beq (by decide : (reflectRing usfn2530E).toPoly == usfn2530P)

def usfn2531E : RingExpr := (.mul (.int (-6)) (.mul (.var 10) (.var 4)))
def usfn2531P : Lean.Grind.CommRing.Poly := (.add (-6) (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)) (.num (0)))
theorem usfn2531_norm : (reflectRing usfn2531E).toPoly=usfn2531P := by
  exact eq_of_beq (by decide : (reflectRing usfn2531E).toPoly == usfn2531P)

def usfn2532E : RingExpr := (.mul (.var 8) (.mul (.var 9) (.pow (.var 10) 2)))
def usfn2532P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))) (.num (0)))
theorem usfn2532_norm : (reflectRing usfn2532E).toPoly=usfn2532P := by
  exact eq_of_beq (by decide : (reflectRing usfn2532E).toPoly == usfn2532P)

def usfn2533E : RingExpr := (.mul (.int 2) (.mul (.var 10) (.mul (.var 8) (.var 9))))
def usfn2533P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn2533_norm : (reflectRing usfn2533E).toPoly=usfn2533P := by
  exact eq_of_beq (by decide : (reflectRing usfn2533E).toPoly == usfn2533P)

def usfn2534E : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.pow (.var 3) 2)))))
def usfn2534P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2534_norm : (reflectRing usfn2534E).toPoly=usfn2534P := by
  exact eq_of_beq (by decide : (reflectRing usfn2534E).toPoly == usfn2534P)

def usfn2535E : RingExpr := (.mul (.int (-5)) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2)))))
def usfn2535P : Lean.Grind.CommRing.Poly := (.add (-5) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0)))
theorem usfn2535_norm : (reflectRing usfn2535E).toPoly=usfn2535P := by
  exact eq_of_beq (by decide : (reflectRing usfn2535E).toPoly == usfn2535P)

def usfn2536E : RingExpr := (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))
def usfn2536P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2536_norm : (reflectRing usfn2536E).toPoly=usfn2536P := by
  exact eq_of_beq (by decide : (reflectRing usfn2536E).toPoly == usfn2536P)

def usfn2537E : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))
def usfn2537P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2537_norm : (reflectRing usfn2537E).toPoly=usfn2537P := by
  exact eq_of_beq (by decide : (reflectRing usfn2537E).toPoly == usfn2537P)

def usfn2538E : RingExpr := (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 4)))))
def usfn2538P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2538_norm : (reflectRing usfn2538E).toPoly=usfn2538P := by
  exact eq_of_beq (by decide : (reflectRing usfn2538E).toPoly == usfn2538P)

def usfn2539E : RingExpr := (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2))))))
def usfn2539P : Lean.Grind.CommRing.Poly := (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2539_norm : (reflectRing usfn2539E).toPoly=usfn2539P := by
  exact eq_of_beq (by decide : (reflectRing usfn2539E).toPoly == usfn2539P)

def usfn2540E : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.var 9))))))
def usfn2540P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2540_norm : (reflectRing usfn2540E).toPoly=usfn2540P := by
  exact eq_of_beq (by decide : (reflectRing usfn2540E).toPoly == usfn2540P)

def usfn2541E : RingExpr := (.mul (.int 4) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 4) 2))))))
def usfn2541P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))
theorem usfn2541_norm : (reflectRing usfn2541E).toPoly=usfn2541P := by
  exact eq_of_beq (by decide : (reflectRing usfn2541E).toPoly == usfn2541P)

def usfn2542E : RingExpr := (.mul (.int 20) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))
def usfn2542P : Lean.Grind.CommRing.Poly := (.add (20) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))
theorem usfn2542_norm : (reflectRing usfn2542E).toPoly=usfn2542P := by
  exact eq_of_beq (by decide : (reflectRing usfn2542E).toPoly == usfn2542P)

def usfn2543E : RingExpr := (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))
def usfn2543P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn2543_norm : (reflectRing usfn2543E).toPoly=usfn2543P := by
  exact eq_of_beq (by decide : (reflectRing usfn2543E).toPoly == usfn2543P)

def usfn2544E : RingExpr := (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 3) 2))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))))))))
def usfn2544P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn2544_norm : (reflectRing usfn2544E).toPoly=usfn2544P := by
  exact eq_of_beq (by decide : (reflectRing usfn2544E).toPoly == usfn2544P)

#print axioms usfn2544_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
