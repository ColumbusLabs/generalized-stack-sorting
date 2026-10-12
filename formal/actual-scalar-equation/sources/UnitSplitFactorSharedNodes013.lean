import UnitSplitFactorSharedNodes012
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn884E : RingExpr := (.mul usfn409E usfn883E)
def usfn884P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ .unit)) (.num (0))))))))))))
theorem usfn884_norm : (reflectRing usfn884E).toPoly=usfn884P := by
  change (reflectRing usfn409E).toPoly.mul (reflectRing usfn883E).toPoly=usfn884P
  rw [usfn409_norm, usfn883_norm]
  exact eq_of_beq (by decide : usfn409P.mul usfn883P == usfn884P)

def usfn885E : RingExpr := (.mul usfn3E usfn884E)
def usfn885P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))
theorem usfn885_norm : (reflectRing usfn885E).toPoly=usfn885P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn884E).toPoly=usfn885P
  rw [usfn3_norm, usfn884_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn884P == usfn885P)

def usfn886E : RingExpr := (.mul usfn452E usfn885E)
def usfn886P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-8) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨15,1⟩ .unit))))) (.num (0))))))))))))
theorem usfn886_norm : (reflectRing usfn886E).toPoly=usfn886P := by
  change (reflectRing usfn452E).toPoly.mul (reflectRing usfn885E).toPoly=usfn886P
  rw [usfn452_norm, usfn885_norm]
  exact eq_of_beq (by decide : usfn452P.mul usfn885P == usfn886P)

def usfn887E : RingExpr := (.mul (.mul (.var 16) (.var 1)) (.mul (.int (-1)) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.int 1) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 3))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2))))))))))))))))
def usfn887P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨16,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨16,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit)))))))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨16,1⟩ .unit))))) (.num (0))))))
theorem usfn887_norm : (reflectRing usfn887E).toPoly=usfn887P := by
  exact eq_of_beq (by decide : (reflectRing usfn887E).toPoly == usfn887P)

def usfn888E : RingExpr := (.mul (.mul (.var 11) (.pow (.var 2) 5)) (.mul (.int 8) (.mul (.var 0) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))))
def usfn888P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,5⟩ (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,5⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.num (0))))
theorem usfn888_norm : (reflectRing usfn888E).toPoly=usfn888P := by
  exact eq_of_beq (by decide : (reflectRing usfn888E).toPoly == usfn888P)

def usfn889E : RingExpr := (.mul (.var 11) (.pow (.var 2) 4))
def usfn889P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨2,4⟩ (.mult ⟨11,1⟩ .unit)) (.num (0)))
theorem usfn889_norm : (reflectRing usfn889E).toPoly=usfn889P := by
  exact eq_of_beq (by decide : (reflectRing usfn889E).toPoly == usfn889P)

def usfn890E : RingExpr := (.int (-4))
def usfn890P : Lean.Grind.CommRing.Poly := (.num (-4))
theorem usfn890_norm : (reflectRing usfn890E).toPoly=usfn890P := by
  exact eq_of_beq (by decide : (reflectRing usfn890E).toPoly == usfn890P)

def usfn891E : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int 1) (.add (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.var 8))))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 3))))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))) (.mul (.int 4) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))))))))))))
def usfn891P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (1) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))
theorem usfn891_norm : (reflectRing usfn891E).toPoly=usfn891P := by
  exact eq_of_beq (by decide : (reflectRing usfn891E).toPoly == usfn891P)

def usfn892E : RingExpr := (.mul usfn890E usfn891E)
def usfn892P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))
theorem usfn892_norm : (reflectRing usfn892E).toPoly=usfn892P := by
  change (reflectRing usfn890E).toPoly.mul (reflectRing usfn891E).toPoly=usfn892P
  rw [usfn890_norm, usfn891_norm]
  exact eq_of_beq (by decide : usfn890P.mul usfn891P == usfn892P)

def usfn893E : RingExpr := (.mul usfn889E usfn892E)
def usfn893P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨2,4⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨2,4⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.num (0)))))))
theorem usfn893_norm : (reflectRing usfn893E).toPoly=usfn893P := by
  change (reflectRing usfn889E).toPoly.mul (reflectRing usfn892E).toPoly=usfn893P
  rw [usfn889_norm, usfn892_norm]
  exact eq_of_beq (by decide : usfn889P.mul usfn892P == usfn893P)

def usfn894E : RingExpr := (.mul (.int 2) (.mul (.var 10) (.mul (.var 9) (.pow (.var 8) 2))))
def usfn894P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn894_norm : (reflectRing usfn894E).toPoly=usfn894P := by
  exact eq_of_beq (by decide : (reflectRing usfn894E).toPoly == usfn894P)

def usfn895E : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 3)))))))
def usfn895P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn895_norm : (reflectRing usfn895E).toPoly=usfn895P := by
  exact eq_of_beq (by decide : (reflectRing usfn895E).toPoly == usfn895P)

def usfn896E : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))
def usfn896P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn896_norm : (reflectRing usfn896E).toPoly=usfn896P := by
  exact eq_of_beq (by decide : (reflectRing usfn896E).toPoly == usfn896P)

def usfn897E : RingExpr := (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2))))))))
def usfn897P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))
theorem usfn897_norm : (reflectRing usfn897E).toPoly=usfn897P := by
  exact eq_of_beq (by decide : (reflectRing usfn897E).toPoly == usfn897P)

def usfn898E : RingExpr := (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.pow (.var 9) 2)))))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2)))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.pow (.var 9) 2))))))))))
def usfn898P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0)))))
theorem usfn898_norm : (reflectRing usfn898E).toPoly=usfn898P := by
  exact eq_of_beq (by decide : (reflectRing usfn898E).toPoly == usfn898P)

def usfn899E : RingExpr := (.add usfn897E usfn898E)
def usfn899P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0))))))
theorem usfn899_norm : (reflectRing usfn899E).toPoly=usfn899P := by
  change (reflectRing usfn897E).toPoly.combine (reflectRing usfn898E).toPoly=usfn899P
  rw [usfn897_norm, usfn898_norm]
  exact eq_of_beq (by decide : usfn897P.combine usfn898P == usfn899P)

def usfn900E : RingExpr := (.add usfn896E usfn899E)
def usfn900P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn900_norm : (reflectRing usfn900E).toPoly=usfn900P := by
  change (reflectRing usfn896E).toPoly.combine (reflectRing usfn899E).toPoly=usfn900P
  rw [usfn896_norm, usfn899_norm]
  exact eq_of_beq (by decide : usfn896P.combine usfn899P == usfn900P)

def usfn901E : RingExpr := (.add usfn895E usfn900E)
def usfn901P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))
theorem usfn901_norm : (reflectRing usfn901E).toPoly=usfn901P := by
  change (reflectRing usfn895E).toPoly.combine (reflectRing usfn900E).toPoly=usfn901P
  rw [usfn895_norm, usfn900_norm]
  exact eq_of_beq (by decide : usfn895P.combine usfn900P == usfn901P)

def usfn902E : RingExpr := (.add usfn894E usfn901E)
def usfn902P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))
theorem usfn902_norm : (reflectRing usfn902E).toPoly=usfn902P := by
  change (reflectRing usfn894E).toPoly.combine (reflectRing usfn901E).toPoly=usfn902P
  rw [usfn894_norm, usfn901_norm]
  exact eq_of_beq (by decide : usfn894P.combine usfn901P == usfn902P)

def usfn903E : RingExpr := (.add usfn533E usfn902E)
def usfn903P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ .unit) (.num (0))))))))))
theorem usfn903_norm : (reflectRing usfn903E).toPoly=usfn903P := by
  change (reflectRing usfn533E).toPoly.combine (reflectRing usfn902E).toPoly=usfn903P
  rw [usfn533_norm, usfn902_norm]
  exact eq_of_beq (by decide : usfn533P.combine usfn902P == usfn903P)

def usfn904E : RingExpr := (.mul usfn4E usfn903E)
def usfn904P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨8,2⟩ .unit)) (.num (0))))))))))
theorem usfn904_norm : (reflectRing usfn904E).toPoly=usfn904P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn903E).toPoly=usfn904P
  rw [usfn4_norm, usfn903_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn903P == usfn904P)

def usfn905E : RingExpr := (.mul usfn362E usfn904E)
def usfn905P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit))) (.num (0))))))))))
theorem usfn905_norm : (reflectRing usfn905E).toPoly=usfn905P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn904E).toPoly=usfn905P
  rw [usfn362_norm, usfn904_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn904P == usfn905P)

def usfn906E : RingExpr := (.mul usfn1E usfn905E)
def usfn906P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ .unit)))) (.num (0))))))))))
theorem usfn906_norm : (reflectRing usfn906E).toPoly=usfn906P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn905E).toPoly=usfn906P
  rw [usfn1_norm, usfn905_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn905P == usfn906P)

def usfn907E : RingExpr := (.mul usfn408E usfn906E)
def usfn907P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ .unit)))) (.num (0))))))))))
theorem usfn907_norm : (reflectRing usfn907E).toPoly=usfn907P := by
  change (reflectRing usfn408E).toPoly.mul (reflectRing usfn906E).toPoly=usfn907P
  rw [usfn408_norm, usfn906_norm]
  exact eq_of_beq (by decide : usfn408P.mul usfn906P == usfn907P)

def usfn908E : RingExpr := (.mul usfn459E usfn907E)
def usfn908P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))))) (.num (0))))))))))
theorem usfn908_norm : (reflectRing usfn908E).toPoly=usfn908P := by
  change (reflectRing usfn459E).toPoly.mul (reflectRing usfn907E).toPoly=usfn908P
  rw [usfn459_norm, usfn907_norm]
  exact eq_of_beq (by decide : usfn459P.mul usfn907P == usfn908P)

def usfn909E : RingExpr := (.mul (.mul (.var 12) (.pow (.var 2) 3)) (.mul (.int (-2)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-8)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2))))))) (.mul (.int 16) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 4) (.pow (.var 4) 3))))))))))))))))
def usfn909P : Lean.Grind.CommRing.Poly := (.add (-32) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (2) (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨12,1⟩ .unit))))) (.num (0))))))
theorem usfn909_norm : (reflectRing usfn909E).toPoly=usfn909P := by
  exact eq_of_beq (by decide : (reflectRing usfn909E).toPoly == usfn909P)

def usfn910E : RingExpr := (.mul (.mul (.var 14) (.pow (.var 2) 3)) (.mul (.int 2) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))
def usfn910P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit))))))))) (.add (-2) (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨14,1⟩ .unit))))) (.num (0))))
theorem usfn910_norm : (reflectRing usfn910E).toPoly=usfn910P := by
  exact eq_of_beq (by decide : (reflectRing usfn910E).toPoly == usfn910P)

def usfn911E : RingExpr := (.mul (.mul (.var 15) (.pow (.var 2) 3)) (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))))
def usfn911P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.num (0))))
theorem usfn911_norm : (reflectRing usfn911E).toPoly=usfn911P := by
  exact eq_of_beq (by decide : (reflectRing usfn911E).toPoly == usfn911P)

def usfn912E : RingExpr := (.mul (.var 10) (.mul (.var 9) (.pow (.var 8) 2)))
def usfn912P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn912_norm : (reflectRing usfn912E).toPoly=usfn912P := by
  exact eq_of_beq (by decide : (reflectRing usfn912E).toPoly == usfn912P)

def usfn913E : RingExpr := (.mul (.int (-2)) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 2))))
def usfn913P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem usfn913_norm : (reflectRing usfn913E).toPoly=usfn913P := by
  exact eq_of_beq (by decide : (reflectRing usfn913E).toPoly == usfn913P)

def usfn914E : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.var 9)))))
def usfn914P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn914_norm : (reflectRing usfn914E).toPoly=usfn914P := by
  exact eq_of_beq (by decide : (reflectRing usfn914E).toPoly == usfn914P)

def usfn915E : RingExpr := (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))
def usfn915P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn915_norm : (reflectRing usfn915E).toPoly=usfn915P := by
  exact eq_of_beq (by decide : (reflectRing usfn915E).toPoly == usfn915P)

def usfn916E : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))
def usfn916P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn916_norm : (reflectRing usfn916E).toPoly=usfn916P := by
  exact eq_of_beq (by decide : (reflectRing usfn916E).toPoly == usfn916P)

def usfn917E : RingExpr := (.mul (.int 4) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))
def usfn917P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn917_norm : (reflectRing usfn917E).toPoly=usfn917P := by
  exact eq_of_beq (by decide : (reflectRing usfn917E).toPoly == usfn917P)

def usfn918E : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.pow (.var 9) 2))))))))
def usfn918P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0)))
theorem usfn918_norm : (reflectRing usfn918E).toPoly=usfn918P := by
  exact eq_of_beq (by decide : (reflectRing usfn918E).toPoly == usfn918P)

def usfn919E : RingExpr := (.add (.mul (.int 2) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3)))))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2)))))))) (.mul (.int 32) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.pow (.var 9) 2))))))))))
def usfn919P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))))
theorem usfn919_norm : (reflectRing usfn919E).toPoly=usfn919P := by
  exact eq_of_beq (by decide : (reflectRing usfn919E).toPoly == usfn919P)

def usfn920E : RingExpr := (.add usfn918E usfn919E)
def usfn920P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0))))))
theorem usfn920_norm : (reflectRing usfn920E).toPoly=usfn920P := by
  change (reflectRing usfn918E).toPoly.combine (reflectRing usfn919E).toPoly=usfn920P
  rw [usfn918_norm, usfn919_norm]
  exact eq_of_beq (by decide : usfn918P.combine usfn919P == usfn920P)

def usfn921E : RingExpr := (.add usfn917E usfn920E)
def usfn921P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn921_norm : (reflectRing usfn921E).toPoly=usfn921P := by
  change (reflectRing usfn917E).toPoly.combine (reflectRing usfn920E).toPoly=usfn921P
  rw [usfn917_norm, usfn920_norm]
  exact eq_of_beq (by decide : usfn917P.combine usfn920P == usfn921P)

def usfn922E : RingExpr := (.add usfn916E usfn921E)
def usfn922P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))
theorem usfn922_norm : (reflectRing usfn922E).toPoly=usfn922P := by
  change (reflectRing usfn916E).toPoly.combine (reflectRing usfn921E).toPoly=usfn922P
  rw [usfn916_norm, usfn921_norm]
  exact eq_of_beq (by decide : usfn916P.combine usfn921P == usfn922P)

def usfn923E : RingExpr := (.add usfn895E usfn922E)
def usfn923P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))))
theorem usfn923_norm : (reflectRing usfn923E).toPoly=usfn923P := by
  change (reflectRing usfn895E).toPoly.combine (reflectRing usfn922E).toPoly=usfn923P
  rw [usfn895_norm, usfn922_norm]
  exact eq_of_beq (by decide : usfn895P.combine usfn922P == usfn923P)

def usfn924E : RingExpr := (.add usfn915E usfn923E)
def usfn924P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn924_norm : (reflectRing usfn924E).toPoly=usfn924P := by
  change (reflectRing usfn915E).toPoly.combine (reflectRing usfn923E).toPoly=usfn924P
  rw [usfn915_norm, usfn923_norm]
  exact eq_of_beq (by decide : usfn915P.combine usfn923P == usfn924P)

def usfn925E : RingExpr := (.add usfn914E usfn924E)
def usfn925P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))
theorem usfn925_norm : (reflectRing usfn925E).toPoly=usfn925P := by
  change (reflectRing usfn914E).toPoly.combine (reflectRing usfn924E).toPoly=usfn925P
  rw [usfn914_norm, usfn924_norm]
  exact eq_of_beq (by decide : usfn914P.combine usfn924P == usfn925P)

def usfn926E : RingExpr := (.add usfn913E usfn925E)
def usfn926P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn926_norm : (reflectRing usfn926E).toPoly=usfn926P := by
  change (reflectRing usfn913E).toPoly.combine (reflectRing usfn925E).toPoly=usfn926P
  rw [usfn913_norm, usfn925_norm]
  exact eq_of_beq (by decide : usfn913P.combine usfn925P == usfn926P)

def usfn927E : RingExpr := (.add usfn912E usfn926E)
def usfn927P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))))
theorem usfn927_norm : (reflectRing usfn927E).toPoly=usfn927P := by
  change (reflectRing usfn912E).toPoly.combine (reflectRing usfn926E).toPoly=usfn927P
  rw [usfn912_norm, usfn926_norm]
  exact eq_of_beq (by decide : usfn912P.combine usfn926P == usfn927P)

def usfn928E : RingExpr := (.add usfn533E usfn927E)
def usfn928P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ .unit) (.num (0))))))))))))))
theorem usfn928_norm : (reflectRing usfn928E).toPoly=usfn928P := by
  change (reflectRing usfn533E).toPoly.combine (reflectRing usfn927E).toPoly=usfn928P
  rw [usfn533_norm, usfn927_norm]
  exact eq_of_beq (by decide : usfn533P.combine usfn927P == usfn928P)

def usfn929E : RingExpr := (.mul usfn4E usfn928E)
def usfn929P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨8,2⟩ .unit)) (.num (0))))))))))))))
theorem usfn929_norm : (reflectRing usfn929E).toPoly=usfn929P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn928E).toPoly=usfn929P
  rw [usfn4_norm, usfn928_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn928P == usfn929P)

def usfn930E : RingExpr := (.mul usfn1E usfn929E)
def usfn930P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ .unit))) (.num (0))))))))))))))
theorem usfn930_norm : (reflectRing usfn930E).toPoly=usfn930P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn929E).toPoly=usfn930P
  rw [usfn1_norm, usfn929_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn929P == usfn930P)

def usfn931E : RingExpr := (.mul usfn100E usfn930E)
def usfn931P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ .unit))) (.num (0))))))))))))))
theorem usfn931_norm : (reflectRing usfn931E).toPoly=usfn931P := by
  change (reflectRing usfn100E).toPoly.mul (reflectRing usfn930E).toPoly=usfn931P
  rw [usfn100_norm, usfn930_norm]
  exact eq_of_beq (by decide : usfn100P.mul usfn930P == usfn931P)

def usfn932E : RingExpr := (.mul usfn134E usfn931E)
def usfn932P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-1) (.mult ⟨2,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))) (.num (0))))))))))))))
theorem usfn932_norm : (reflectRing usfn932E).toPoly=usfn932P := by
  change (reflectRing usfn134E).toPoly.mul (reflectRing usfn931E).toPoly=usfn932P
  rw [usfn134_norm, usfn931_norm]
  exact eq_of_beq (by decide : usfn134P.mul usfn931P == usfn932P)

def usfn933E : RingExpr := (.mul (.var 12) (.pow (.var 2) 2))
def usfn933P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨2,2⟩ (.mult ⟨12,1⟩ .unit)) (.num (0)))
theorem usfn933_norm : (reflectRing usfn933E).toPoly=usfn933P := by
  exact eq_of_beq (by decide : (reflectRing usfn933E).toPoly == usfn933P)

def usfn934E : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.pow (.var 4) 2))))))
def usfn934P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn934_norm : (reflectRing usfn934E).toPoly=usfn934P := by
  exact eq_of_beq (by decide : (reflectRing usfn934E).toPoly == usfn934P)

def usfn935E : RingExpr := (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 8) 2))))))) (.mul (.int 32) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 4) (.pow (.var 4) 3)))))))))))
def usfn935P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))
theorem usfn935_norm : (reflectRing usfn935E).toPoly=usfn935P := by
  exact eq_of_beq (by decide : (reflectRing usfn935E).toPoly == usfn935P)

def usfn936E : RingExpr := (.add usfn934E usfn935E)
def usfn936P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))
theorem usfn936_norm : (reflectRing usfn936E).toPoly=usfn936P := by
  change (reflectRing usfn934E).toPoly.combine (reflectRing usfn935E).toPoly=usfn936P
  rw [usfn934_norm, usfn935_norm]
  exact eq_of_beq (by decide : usfn934P.combine usfn935P == usfn936P)

def usfn937E : RingExpr := (.add usfn506E usfn936E)
def usfn937P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0))))))))
theorem usfn937_norm : (reflectRing usfn937E).toPoly=usfn937P := by
  change (reflectRing usfn506E).toPoly.combine (reflectRing usfn936E).toPoly=usfn937P
  rw [usfn506_norm, usfn936_norm]
  exact eq_of_beq (by decide : usfn506P.combine usfn936P == usfn937P)

def usfn938E : RingExpr := (.add usfn100E usfn937E)
def usfn938P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (-1))))))))
theorem usfn938_norm : (reflectRing usfn938E).toPoly=usfn938P := by
  change (reflectRing usfn100E).toPoly.combine (reflectRing usfn937E).toPoly=usfn938P
  rw [usfn100_norm, usfn937_norm]
  exact eq_of_beq (by decide : usfn100P.combine usfn937P == usfn938P)

def usfn939E : RingExpr := (.mul usfn4E usfn938E)
def usfn939P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (-1) (.mult ⟨8,2⟩ .unit) (.num (0)))))))))
theorem usfn939_norm : (reflectRing usfn939E).toPoly=usfn939P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn938E).toPoly=usfn939P
  rw [usfn4_norm, usfn938_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn938P == usfn939P)

def usfn940E : RingExpr := (.mul usfn3E usfn939E)
def usfn940P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-1) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))))))))
theorem usfn940_norm : (reflectRing usfn940E).toPoly=usfn940P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn939E).toPoly=usfn940P
  rw [usfn3_norm, usfn939_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn939P == usfn940P)

def usfn941E : RingExpr := (.mul usfn100E usfn940E)
def usfn941P : Lean.Grind.CommRing.Poly := (.add (-32) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))))))))
theorem usfn941_norm : (reflectRing usfn941E).toPoly=usfn941P := by
  change (reflectRing usfn100E).toPoly.mul (reflectRing usfn940E).toPoly=usfn941P
  rw [usfn100_norm, usfn940_norm]
  exact eq_of_beq (by decide : usfn100P.mul usfn940P == usfn941P)

def usfn942E : RingExpr := (.mul usfn933E usfn941E)
def usfn942P : Lean.Grind.CommRing.Poly := (.add (-32) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.add (1) (.mult ⟨2,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0)))))))))
theorem usfn942_norm : (reflectRing usfn942E).toPoly=usfn942P := by
  change (reflectRing usfn933E).toPoly.mul (reflectRing usfn941E).toPoly=usfn942P
  rw [usfn933_norm, usfn941_norm]
  exact eq_of_beq (by decide : usfn933P.mul usfn941P == usfn942P)

def usfn943E : RingExpr := (.mul (.mul (.var 14) (.pow (.var 2) 2)) (.mul (.int (-1)) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.mul (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))
def usfn943P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨14,1⟩ .unit))))))) (.add (-1) (.mult ⟨2,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨14,1⟩ .unit)))) (.num (0))))))
theorem usfn943_norm : (reflectRing usfn943E).toPoly=usfn943P := by
  exact eq_of_beq (by decide : (reflectRing usfn943E).toPoly == usfn943P)

def usfn944E : RingExpr := (.mul (.var 15) (.pow (.var 2) 2))
def usfn944P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨2,2⟩ (.mult ⟨15,1⟩ .unit)) (.num (0)))
theorem usfn944_norm : (reflectRing usfn944E).toPoly=usfn944P := by
  exact eq_of_beq (by decide : (reflectRing usfn944E).toPoly == usfn944P)

def usfn945E : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2))))))
def usfn945P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn945_norm : (reflectRing usfn945E).toPoly=usfn945P := by
  exact eq_of_beq (by decide : (reflectRing usfn945E).toPoly == usfn945P)

def usfn946E : RingExpr := (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-4)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2)))))))) (.mul (.int 8) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 4) (.pow (.var 4) 3)))))))))))
def usfn946P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))
theorem usfn946_norm : (reflectRing usfn946E).toPoly=usfn946P := by
  exact eq_of_beq (by decide : (reflectRing usfn946E).toPoly == usfn946P)

def usfn947E : RingExpr := (.add usfn945E usfn946E)
def usfn947P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))
theorem usfn947_norm : (reflectRing usfn947E).toPoly=usfn947P := by
  change (reflectRing usfn945E).toPoly.combine (reflectRing usfn946E).toPoly=usfn947P
  rw [usfn945_norm, usfn946_norm]
  exact eq_of_beq (by decide : usfn945P.combine usfn946P == usfn947P)

def usfn948E : RingExpr := (.add usfn100E usfn947E)
def usfn948P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (-1)))))))
theorem usfn948_norm : (reflectRing usfn948E).toPoly=usfn948P := by
  change (reflectRing usfn100E).toPoly.combine (reflectRing usfn947E).toPoly=usfn948P
  rw [usfn100_norm, usfn947_norm]
  exact eq_of_beq (by decide : usfn100P.combine usfn947P == usfn948P)

def usfn949E : RingExpr := (.mul usfn4E usfn948E)
def usfn949P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨8,2⟩ .unit) (.num (0))))))))
theorem usfn949_norm : (reflectRing usfn949E).toPoly=usfn949P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn948E).toPoly=usfn949P
  rw [usfn4_norm, usfn948_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn948P == usfn949P)

def usfn950E : RingExpr := (.mul usfn3E usfn949E)
def usfn950P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))
theorem usfn950_norm : (reflectRing usfn950E).toPoly=usfn950P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn949E).toPoly=usfn950P
  rw [usfn3_norm, usfn949_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn949P == usfn950P)

def usfn951E : RingExpr := (.mul usfn362E usfn950E)
def usfn951P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))
theorem usfn951_norm : (reflectRing usfn951E).toPoly=usfn951P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn950E).toPoly=usfn951P
  rw [usfn362_norm, usfn950_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn950P == usfn951P)

def usfn952E : RingExpr := (.mul usfn382E usfn951E)
def usfn952P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))
theorem usfn952_norm : (reflectRing usfn952E).toPoly=usfn952P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn951E).toPoly=usfn952P
  rw [usfn382_norm, usfn951_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn951P == usfn952P)

def usfn953E : RingExpr := (.mul usfn408E usfn952E)
def usfn953P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))
theorem usfn953_norm : (reflectRing usfn953E).toPoly=usfn953P := by
  change (reflectRing usfn408E).toPoly.mul (reflectRing usfn952E).toPoly=usfn953P
  rw [usfn408_norm, usfn952_norm]
  exact eq_of_beq (by decide : usfn408P.mul usfn952P == usfn953P)

def usfn954E : RingExpr := (.mul usfn944E usfn953E)
def usfn954P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (2) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨15,1⟩ .unit)))))) (.num (0))))))))
theorem usfn954_norm : (reflectRing usfn954E).toPoly=usfn954P := by
  change (reflectRing usfn944E).toPoly.mul (reflectRing usfn953E).toPoly=usfn954P
  rw [usfn944_norm, usfn953_norm]
  exact eq_of_beq (by decide : usfn944P.mul usfn953P == usfn954P)

def usfn955E : RingExpr := (.mul (.mul (.var 16) (.pow (.var 2) 2)) (.mul (.int 2) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))))
def usfn955P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit))))))))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨16,1⟩ .unit)))))) (.num (0))))
theorem usfn955_norm : (reflectRing usfn955E).toPoly=usfn955P := by
  exact eq_of_beq (by decide : (reflectRing usfn955E).toPoly == usfn955P)

def usfn956E : RingExpr := (.mul (.pow (.var 0) 2) (.pow (.var 3) 2))
def usfn956P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨0,2⟩ (.mult ⟨3,2⟩ .unit)) (.num (0)))
theorem usfn956_norm : (reflectRing usfn956E).toPoly=usfn956P := by
  exact eq_of_beq (by decide : (reflectRing usfn956E).toPoly == usfn956P)

def usfn957E : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 10) (.var 9))))
def usfn957P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn957_norm : (reflectRing usfn957E).toPoly=usfn957P := by
  exact eq_of_beq (by decide : (reflectRing usfn957E).toPoly == usfn957P)

def usfn958E : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.var 4))))
def usfn958P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem usfn958_norm : (reflectRing usfn958E).toPoly=usfn958P := by
  exact eq_of_beq (by decide : (reflectRing usfn958E).toPoly == usfn958P)

def usfn959E : RingExpr := (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))
def usfn959P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn959_norm : (reflectRing usfn959E).toPoly=usfn959P := by
  exact eq_of_beq (by decide : (reflectRing usfn959E).toPoly == usfn959P)

def usfn960E : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 2))))))
def usfn960P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn960_norm : (reflectRing usfn960E).toPoly=usfn960P := by
  exact eq_of_beq (by decide : (reflectRing usfn960E).toPoly == usfn960P)

def usfn961E : RingExpr := (.mul (.int (-4)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2))))))
def usfn961P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn961_norm : (reflectRing usfn961E).toPoly=usfn961P := by
  exact eq_of_beq (by decide : (reflectRing usfn961E).toPoly == usfn961P)

def usfn962E : RingExpr := (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 8) 2)))))))
def usfn962P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn962_norm : (reflectRing usfn962E).toPoly=usfn962P := by
  exact eq_of_beq (by decide : (reflectRing usfn962E).toPoly == usfn962P)

def usfn963E : RingExpr := (.mul (.int 8) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))
def usfn963P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn963_norm : (reflectRing usfn963E).toPoly=usfn963P := by
  exact eq_of_beq (by decide : (reflectRing usfn963E).toPoly == usfn963P)

#print axioms usfn963_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
