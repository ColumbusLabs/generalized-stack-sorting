import UnitSplitFactorSharedNodes072
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn3962E : RingExpr := (.add usfn364E usfn3961E)
def usfn3962P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))
theorem usfn3962_norm : (reflectRing usfn3962E).toPoly=usfn3962P := by
  change (reflectRing usfn364E).toPoly.combine (reflectRing usfn3961E).toPoly=usfn3962P
  rw [usfn364_norm, usfn3961_norm]
  exact eq_of_beq (by decide : usfn364P.combine usfn3961P == usfn3962P)

def usfn3963E : RingExpr := (.add usfn3956E usfn3962E)
def usfn3963P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit)) (.num (0))))))))))
theorem usfn3963_norm : (reflectRing usfn3963E).toPoly=usfn3963P := by
  change (reflectRing usfn3956E).toPoly.combine (reflectRing usfn3962E).toPoly=usfn3963P
  rw [usfn3956_norm, usfn3962_norm]
  exact eq_of_beq (by decide : usfn3956P.combine usfn3962P == usfn3963P)

def usfn3964E : RingExpr := (.mul usfn133E usfn3963E)
def usfn3964P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.num (0))))))))))
theorem usfn3964_norm : (reflectRing usfn3964E).toPoly=usfn3964P := by
  change (reflectRing usfn133E).toPoly.mul (reflectRing usfn3963E).toPoly=usfn3964P
  rw [usfn133_norm, usfn3963_norm]
  exact eq_of_beq (by decide : usfn133P.mul usfn3963P == usfn3964P)

def usfn3965E : RingExpr := (.mul usfn409E usfn3964E)
def usfn3965P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.num (0))))))))))
theorem usfn3965_norm : (reflectRing usfn3965E).toPoly=usfn3965P := by
  change (reflectRing usfn409E).toPoly.mul (reflectRing usfn3964E).toPoly=usfn3965P
  rw [usfn409_norm, usfn3964_norm]
  exact eq_of_beq (by decide : usfn409P.mul usfn3964P == usfn3965P)

def usfn3966E : RingExpr := (.mul usfn102E usfn3965E)
def usfn3966P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit)))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0))))))))))
theorem usfn3966_norm : (reflectRing usfn3966E).toPoly=usfn3966P := by
  change (reflectRing usfn102E).toPoly.mul (reflectRing usfn3965E).toPoly=usfn3966P
  rw [usfn102_norm, usfn3965_norm]
  exact eq_of_beq (by decide : usfn102P.mul usfn3965P == usfn3966P)

def usfn3967E : RingExpr := (.mul usfn3E usfn3966E)
def usfn3967P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0))))))))))
theorem usfn3967_norm : (reflectRing usfn3967E).toPoly=usfn3967P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn3966E).toPoly=usfn3967P
  rw [usfn3_norm, usfn3966_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn3966P == usfn3967P)

def usfn3968E : RingExpr := (.mul usfn362E usfn3967E)
def usfn3968P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0))))))))))
theorem usfn3968_norm : (reflectRing usfn3968E).toPoly=usfn3968P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn3967E).toPoly=usfn3968P
  rw [usfn362_norm, usfn3967_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn3967P == usfn3968P)

def usfn3969E : RingExpr := (.mul usfn1E usfn3968E)
def usfn3969P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))))
theorem usfn3969_norm : (reflectRing usfn3969E).toPoly=usfn3969P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn3968E).toPoly=usfn3969P
  rw [usfn1_norm, usfn3968_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn3968P == usfn3969P)

def usfn3970E : RingExpr := (.mul usfn3666E usfn3969E)
def usfn3970P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (48) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (12) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-36) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-24) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (24) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-6) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))))
theorem usfn3970_norm : (reflectRing usfn3970E).toPoly=usfn3970P := by
  change (reflectRing usfn3666E).toPoly.mul (reflectRing usfn3969E).toPoly=usfn3970P
  rw [usfn3666_norm, usfn3969_norm]
  exact eq_of_beq (by decide : usfn3666P.mul usfn3969P == usfn3970P)

def usfn3971E : RingExpr := (.mul usfn743E usfn3970E)
def usfn3971P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (12) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-36) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-6) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-6) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.num (0))))))))))
theorem usfn3971_norm : (reflectRing usfn3971E).toPoly=usfn3971P := by
  change (reflectRing usfn743E).toPoly.mul (reflectRing usfn3970E).toPoly=usfn3971P
  rw [usfn743_norm, usfn3970_norm]
  exact eq_of_beq (by decide : usfn743P.mul usfn3970P == usfn3971P)

def usfn3972E : RingExpr := (.mul (.mul (.var 15) (.mul (.var 2) (.pow (.var 1) 2))) (.mul (.int 12) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.mul (.add (.int 1) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))))
def usfn3972P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit)))))))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))))) (.add (-12) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.num (0))))))
theorem usfn3972_norm : (reflectRing usfn3972E).toPoly=usfn3972P := by
  exact eq_of_beq (by decide : (reflectRing usfn3972E).toPoly == usfn3972P)

def usfn3973E : RingExpr := (.mul (.mul (.var 11) (.mul (.var 5) (.pow (.var 1) 2))) (.mul (.int 4) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def usfn3973P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨1,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.num (0))))
theorem usfn3973_norm : (reflectRing usfn3973E).toPoly=usfn3973P := by
  exact eq_of_beq (by decide : (reflectRing usfn3973E).toPoly == usfn3973P)

def usfn3974E : RingExpr := (.mul (.mul (.var 12) (.mul (.var 5) (.pow (.var 1) 2))) (.mul (.int 8) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def usfn3974P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-8) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.num (0))))
theorem usfn3974_norm : (reflectRing usfn3974E).toPoly=usfn3974P := by
  exact eq_of_beq (by decide : (reflectRing usfn3974E).toPoly == usfn3974P)

def usfn3975E : RingExpr := (.mul (.var 11) (.pow (.var 1) 2))
def usfn3975P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨1,2⟩ (.mult ⟨11,1⟩ .unit)) (.num (0)))
theorem usfn3975_norm : (reflectRing usfn3975E).toPoly=usfn3975P := by
  exact eq_of_beq (by decide : (reflectRing usfn3975E).toPoly == usfn3975P)

def usfn3976E : RingExpr := (.mul usfn2456E usfn3653E)
def usfn3976P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-48) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-12) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (24) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (6) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (3) (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.num (0))))))))))
theorem usfn3976_norm : (reflectRing usfn3976E).toPoly=usfn3976P := by
  change (reflectRing usfn2456E).toPoly.mul (reflectRing usfn3653E).toPoly=usfn3976P
  rw [usfn2456_norm, usfn3653_norm]
  exact eq_of_beq (by decide : usfn2456P.mul usfn3653P == usfn3976P)

def usfn3977E : RingExpr := (.mul usfn3975E usfn3976E)
def usfn3977P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-48) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-12) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (6) (.mult ⟨1,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (6) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (3) (.mult ⟨1,2⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))) (.num (0))))))))))
theorem usfn3977_norm : (reflectRing usfn3977E).toPoly=usfn3977P := by
  change (reflectRing usfn3975E).toPoly.mul (reflectRing usfn3976E).toPoly=usfn3977P
  rw [usfn3975_norm, usfn3976_norm]
  exact eq_of_beq (by decide : usfn3975P.mul usfn3976P == usfn3977P)

def usfn3978E : RingExpr := (.mul (.var 12) (.pow (.var 1) 2))
def usfn3978P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨1,2⟩ (.mult ⟨12,1⟩ .unit)) (.num (0)))
theorem usfn3978_norm : (reflectRing usfn3978E).toPoly=usfn3978P := by
  exact eq_of_beq (by decide : (reflectRing usfn3978E).toPoly == usfn3978P)

def usfn3979E : RingExpr := (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))) (.mul (.int 24) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))))))
def usfn3979P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))
theorem usfn3979_norm : (reflectRing usfn3979E).toPoly=usfn3979P := by
  exact eq_of_beq (by decide : (reflectRing usfn3979E).toPoly == usfn3979P)

def usfn3980E : RingExpr := (.add usfn843E usfn3979E)
def usfn3980P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))
theorem usfn3980_norm : (reflectRing usfn3980E).toPoly=usfn3980P := by
  change (reflectRing usfn843E).toPoly.combine (reflectRing usfn3979E).toPoly=usfn3980P
  rw [usfn843_norm, usfn3979_norm]
  exact eq_of_beq (by decide : usfn843P.combine usfn3979P == usfn3980P)

def usfn3981E : RingExpr := (.add usfn3643E usfn3980E)
def usfn3981P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.num (0))))))))
theorem usfn3981_norm : (reflectRing usfn3981E).toPoly=usfn3981P := by
  change (reflectRing usfn3643E).toPoly.combine (reflectRing usfn3980E).toPoly=usfn3981P
  rw [usfn3643_norm, usfn3980_norm]
  exact eq_of_beq (by decide : usfn3643P.combine usfn3980P == usfn3981P)

def usfn3982E : RingExpr := (.add usfn3642E usfn3981E)
def usfn3982P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (-1) (.mult ⟨10,1⟩ .unit) (.num (0)))))))))
theorem usfn3982_norm : (reflectRing usfn3982E).toPoly=usfn3982P := by
  change (reflectRing usfn3642E).toPoly.combine (reflectRing usfn3981E).toPoly=usfn3982P
  rw [usfn3642_norm, usfn3981_norm]
  exact eq_of_beq (by decide : usfn3642P.combine usfn3981P == usfn3982P)

def usfn3983E : RingExpr := (.mul usfn133E usfn3982E)
def usfn3983P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit))) (.add (-1) (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)) (.num (0)))))))))
theorem usfn3983_norm : (reflectRing usfn3983E).toPoly=usfn3983P := by
  change (reflectRing usfn133E).toPoly.mul (reflectRing usfn3982E).toPoly=usfn3983P
  rw [usfn133_norm, usfn3982_norm]
  exact eq_of_beq (by decide : usfn133P.mul usfn3982P == usfn3983P)

def usfn3984E : RingExpr := (.mul usfn534E usfn3983E)
def usfn3984P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))
theorem usfn3984_norm : (reflectRing usfn3984E).toPoly=usfn3984P := by
  change (reflectRing usfn534E).toPoly.mul (reflectRing usfn3983E).toPoly=usfn3984P
  rw [usfn534_norm, usfn3983_norm]
  exact eq_of_beq (by decide : usfn534P.mul usfn3983P == usfn3984P)

def usfn3985E : RingExpr := (.mul usfn102E usfn3984E)
def usfn3985P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-2) (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit))) (.num (0)))))))))
theorem usfn3985_norm : (reflectRing usfn3985E).toPoly=usfn3985P := by
  change (reflectRing usfn102E).toPoly.mul (reflectRing usfn3984E).toPoly=usfn3985P
  rw [usfn102_norm, usfn3984_norm]
  exact eq_of_beq (by decide : usfn102P.mul usfn3984P == usfn3985P)

def usfn3986E : RingExpr := (.mul usfn3E usfn3985E)
def usfn3986P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))) (.num (0)))))))))
theorem usfn3986_norm : (reflectRing usfn3986E).toPoly=usfn3986P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn3985E).toPoly=usfn3986P
  rw [usfn3_norm, usfn3985_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn3985P == usfn3986P)

def usfn3987E : RingExpr := (.mul usfn362E usfn3986E)
def usfn3987P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.num (0)))))))))
theorem usfn3987_norm : (reflectRing usfn3987E).toPoly=usfn3987P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn3986E).toPoly=usfn3987P
  rw [usfn362_norm, usfn3986_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn3986P == usfn3987P)

def usfn3988E : RingExpr := (.mul usfn1E usfn3987E)
def usfn3988P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.num (0)))))))))
theorem usfn3988_norm : (reflectRing usfn3988E).toPoly=usfn3988P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn3987E).toPoly=usfn3988P
  rw [usfn1_norm, usfn3987_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn3987P == usfn3988P)

def usfn3989E : RingExpr := (.mul usfn3743E usfn3988E)
def usfn3989P : Lean.Grind.CommRing.Poly := (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-24) (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (12) (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.num (0)))))))))
theorem usfn3989_norm : (reflectRing usfn3989E).toPoly=usfn3989P := by
  change (reflectRing usfn3743E).toPoly.mul (reflectRing usfn3988E).toPoly=usfn3989P
  rw [usfn3743_norm, usfn3988_norm]
  exact eq_of_beq (by decide : usfn3743P.mul usfn3988P == usfn3989P)

def usfn3990E : RingExpr := (.mul usfn3978E usfn3989E)
def usfn3990P : Lean.Grind.CommRing.Poly := (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (12) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (12) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (6) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit)))))))) (.num (0)))))))))
theorem usfn3990_norm : (reflectRing usfn3990E).toPoly=usfn3990P := by
  change (reflectRing usfn3978E).toPoly.mul (reflectRing usfn3989E).toPoly=usfn3990P
  rw [usfn3978_norm, usfn3989_norm]
  exact eq_of_beq (by decide : usfn3978P.mul usfn3989P == usfn3990P)

def usfn3991E : RingExpr := (.mul (.mul (.var 15) (.pow (.var 1) 2)) (.mul (.int 24) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.mul (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))) (.add (.mul (.int (-1)) (.var 4)) (.mul (.var 0) (.var 3))))))))))))
def usfn3991P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.num (0))))))
theorem usfn3991_norm : (reflectRing usfn3991E).toPoly=usfn3991P := by
  exact eq_of_beq (by decide : (reflectRing usfn3991E).toPoly == usfn3991P)

def usfn3992E : RingExpr := (.mul (.mul (.var 16) (.pow (.var 1) 2)) (.mul (.int (-24)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))))
def usfn3992P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨16,1⟩ .unit))))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨16,1⟩ .unit))))))))) (.num (0))))
theorem usfn3992_norm : (reflectRing usfn3992E).toPoly=usfn3992P := by
  exact eq_of_beq (by decide : (reflectRing usfn3992E).toPoly == usfn3992P)

def usfn3993E : RingExpr := (.mul (.mul (.var 11) (.mul (.var 1) (.pow (.var 2) 5))) (.mul (.int (-24)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def usfn3993P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨1,1⟩ (.mult ⟨2,5⟩ (.mult ⟨3,1⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨2,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.num (0))))
theorem usfn3993_norm : (reflectRing usfn3993E).toPoly=usfn3993P := by
  exact eq_of_beq (by decide : (reflectRing usfn3993E).toPoly == usfn3993P)

def usfn3994E : RingExpr := (.mul (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.pow (.var 2) 4)))) (.mul (.int (-8)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def usfn3994P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.num (0))))
theorem usfn3994_norm : (reflectRing usfn3994E).toPoly=usfn3994P := by
  exact eq_of_beq (by decide : (reflectRing usfn3994E).toPoly == usfn3994P)

def usfn3995E : RingExpr := (.mul usfn3942E usfn3661E)
def usfn3995P : Lean.Grind.CommRing.Poly := (.add (96) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (12) (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))
theorem usfn3995_norm : (reflectRing usfn3995E).toPoly=usfn3995P := by
  change (reflectRing usfn3942E).toPoly.mul (reflectRing usfn3661E).toPoly=usfn3995P
  rw [usfn3942_norm, usfn3661_norm]
  exact eq_of_beq (by decide : usfn3942P.mul usfn3661P == usfn3995P)

def usfn3996E : RingExpr := (.mul usfn1943E usfn3995E)
def usfn3996P : Lean.Grind.CommRing.Poly := (.add (96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-24) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.num (0))))))))
theorem usfn3996_norm : (reflectRing usfn3996E).toPoly=usfn3996P := by
  change (reflectRing usfn1943E).toPoly.mul (reflectRing usfn3995E).toPoly=usfn3996P
  rw [usfn1943_norm, usfn3995_norm]
  exact eq_of_beq (by decide : usfn1943P.mul usfn3995P == usfn3996P)

def usfn3997E : RingExpr := (.mul (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.pow (.var 2) 3)))) (.mul (.int 8) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def usfn3997P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))))) (.add (-16) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.num (0))))))
theorem usfn3997_norm : (reflectRing usfn3997E).toPoly=usfn3997P := by
  exact eq_of_beq (by decide : (reflectRing usfn3997E).toPoly == usfn3997P)

def usfn3998E : RingExpr := (.mul usfn3743E usfn3685E)
def usfn3998P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (96) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-48) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (84) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-6) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-24) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))))))))
theorem usfn3998_norm : (reflectRing usfn3998E).toPoly=usfn3998P := by
  change (reflectRing usfn3743E).toPoly.mul (reflectRing usfn3685E).toPoly=usfn3998P
  rw [usfn3743_norm, usfn3685_norm]
  exact eq_of_beq (by decide : usfn3743P.mul usfn3685P == usfn3998P)

def usfn3999E : RingExpr := (.mul usfn751E usfn3998E)
def usfn3999P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-48) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (84) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-6) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-24) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.num (0))))))))))))))
theorem usfn3999_norm : (reflectRing usfn3999E).toPoly=usfn3999P := by
  change (reflectRing usfn751E).toPoly.mul (reflectRing usfn3998E).toPoly=usfn3999P
  rw [usfn751_norm, usfn3998_norm]
  exact eq_of_beq (by decide : usfn751P.mul usfn3998P == usfn3999P)

def usfn4000E : RingExpr := (.mul (.mul (.var 12) (.mul (.var 1) (.pow (.var 2) 3))) (.mul (.int 12) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.add (.mul (.int 2) (.var 10)) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.var 8)))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))))))))))
def usfn4000P : Lean.Grind.CommRing.Poly := (.add (96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-12) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.num (0))))))
theorem usfn4000_norm : (reflectRing usfn4000E).toPoly=usfn4000P := by
  exact eq_of_beq (by decide : (reflectRing usfn4000E).toPoly == usfn4000P)

def usfn4001E : RingExpr := (.mul (.mul (.var 15) (.mul (.var 1) (.pow (.var 2) 3))) (.mul (.int 24) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def usfn4001P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-24) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.num (0))))
theorem usfn4001_norm : (reflectRing usfn4001E).toPoly=usfn4001P := by
  exact eq_of_beq (by decide : (reflectRing usfn4001E).toPoly == usfn4001P)

def usfn4002E : RingExpr := (.mul (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.pow (.var 2) 2)))) (.mul (.int 2) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))) (.add (.int (-1)) (.add (.mul (.int 8) (.mul (.var 3) (.pow (.var 4) 2))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
def usfn4002P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))))) (.add (32) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))))) (.add (-16) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.num (0))))))))
theorem usfn4002_norm : (reflectRing usfn4002E).toPoly=usfn4002P := by
  exact eq_of_beq (by decide : (reflectRing usfn4002E).toPoly == usfn4002P)

def usfn4003E : RingExpr := (.mul (.mul (.var 12) (.mul (.var 5) (.mul (.var 1) (.pow (.var 2) 2)))) (.mul (.int 24) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))))
def usfn4003P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit))))))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))))) (.num (0))))
theorem usfn4003_norm : (reflectRing usfn4003E).toPoly=usfn4003P := by
  exact eq_of_beq (by decide : (reflectRing usfn4003E).toPoly == usfn4003P)

def usfn4004E : RingExpr := (.mul (.mul (.var 15) (.mul (.var 5) (.mul (.var 1) (.pow (.var 2) 2)))) (.mul (.int 8) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def usfn4004P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit)))))))))) (.add (-8) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))))) (.num (0))))
theorem usfn4004_norm : (reflectRing usfn4004E).toPoly=usfn4004P := by
  exact eq_of_beq (by decide : (reflectRing usfn4004E).toPoly == usfn4004P)

def usfn4005E : RingExpr := (.mul usfn2456E usfn3708E)
def usfn4005P : Lean.Grind.CommRing.Poly := (.add (-192) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-72) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (18) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (36) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (48) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-3) (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))))))))
theorem usfn4005_norm : (reflectRing usfn4005E).toPoly=usfn4005P := by
  change (reflectRing usfn2456E).toPoly.mul (reflectRing usfn3708E).toPoly=usfn4005P
  rw [usfn2456_norm, usfn3708_norm]
  exact eq_of_beq (by decide : usfn2456P.mul usfn3708P == usfn4005P)

def usfn4006E : RingExpr := (.mul usfn360E usfn4005E)
def usfn4006P : Lean.Grind.CommRing.Poly := (.add (-192) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-72) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (6) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (18) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-3) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-6) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.num (0))))))))))))))
theorem usfn4006_norm : (reflectRing usfn4006E).toPoly=usfn4006P := by
  change (reflectRing usfn360E).toPoly.mul (reflectRing usfn4005E).toPoly=usfn4006P
  rw [usfn360_norm, usfn4005_norm]
  exact eq_of_beq (by decide : usfn360P.mul usfn4005P == usfn4006P)

def usfn4007E : RingExpr := (.pow (.var 4) 2)
def usfn4007P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨4,2⟩ .unit) (.num (0)))
theorem usfn4007_norm : (reflectRing usfn4007E).toPoly=usfn4007P := by
  exact eq_of_beq (by decide : (reflectRing usfn4007E).toPoly == usfn4007P)

def usfn4008E : RingExpr := (.add (.mul (.int (-6)) (.var 10)) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 3))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))) (.mul (.int 16) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))))))))
def usfn4008P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-6) (.mult ⟨10,1⟩ .unit) (.num (0))))))))
theorem usfn4008_norm : (reflectRing usfn4008E).toPoly=usfn4008P := by
  exact eq_of_beq (by decide : (reflectRing usfn4008E).toPoly == usfn4008P)

def usfn4009E : RingExpr := (.add usfn83E usfn4008E)
def usfn4009P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-6) (.mult ⟨10,1⟩ .unit) (.num (1))))))))
theorem usfn4009_norm : (reflectRing usfn4009E).toPoly=usfn4009P := by
  change (reflectRing usfn83E).toPoly.combine (reflectRing usfn4008E).toPoly=usfn4009P
  rw [usfn83_norm, usfn4008_norm]
  exact eq_of_beq (by decide : usfn83P.combine usfn4008P == usfn4009P)

def usfn4010E : RingExpr := (.mul usfn4007E usfn4009E)
def usfn4010P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit))) (.add (-6) (.mult ⟨4,2⟩ (.mult ⟨10,1⟩ .unit)) (.add (1) (.mult ⟨4,2⟩ .unit) (.num (0)))))))))
theorem usfn4010_norm : (reflectRing usfn4010E).toPoly=usfn4010P := by
  change (reflectRing usfn4007E).toPoly.mul (reflectRing usfn4009E).toPoly=usfn4010P
  rw [usfn4007_norm, usfn4009_norm]
  exact eq_of_beq (by decide : usfn4007P.mul usfn4009P == usfn4010P)

def usfn4011E : RingExpr := (.mul usfn133E usfn4010E)
def usfn4011P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-6) (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)) (.num (0)))))))))
theorem usfn4011_norm : (reflectRing usfn4011E).toPoly=usfn4011P := by
  change (reflectRing usfn133E).toPoly.mul (reflectRing usfn4010E).toPoly=usfn4011P
  rw [usfn133_norm, usfn4010_norm]
  exact eq_of_beq (by decide : usfn133P.mul usfn4010P == usfn4011P)

def usfn4012E : RingExpr := (.mul usfn409E usfn4011E)
def usfn4012P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit))) (.num (0)))))))))
theorem usfn4012_norm : (reflectRing usfn4012E).toPoly=usfn4012P := by
  change (reflectRing usfn409E).toPoly.mul (reflectRing usfn4011E).toPoly=usfn4012P
  rw [usfn409_norm, usfn4011_norm]
  exact eq_of_beq (by decide : usfn409P.mul usfn4011P == usfn4012P)

def usfn4013E : RingExpr := (.mul usfn102E usfn4012E)
def usfn4013P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit)))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0)))))))))
theorem usfn4013_norm : (reflectRing usfn4013E).toPoly=usfn4013P := by
  change (reflectRing usfn102E).toPoly.mul (reflectRing usfn4012E).toPoly=usfn4013P
  rw [usfn102_norm, usfn4012_norm]
  exact eq_of_beq (by decide : usfn102P.mul usfn4012P == usfn4013P)

def usfn4014E : RingExpr := (.mul usfn3E usfn4013E)
def usfn4014P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))))))))
theorem usfn4014_norm : (reflectRing usfn4014E).toPoly=usfn4014P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn4013E).toPoly=usfn4014P
  rw [usfn3_norm, usfn4013_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn4013P == usfn4014P)

def usfn4015E : RingExpr := (.mul usfn1E usfn4014E)
def usfn4015P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))))
theorem usfn4015_norm : (reflectRing usfn4015E).toPoly=usfn4015P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn4014E).toPoly=usfn4015P
  rw [usfn1_norm, usfn4014_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn4014P == usfn4015P)

def usfn4016E : RingExpr := (.mul usfn3743E usfn4015E)
def usfn4016P : Lean.Grind.CommRing.Poly := (.add (-96) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-72) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (36) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (36) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))))
theorem usfn4016_norm : (reflectRing usfn4016E).toPoly=usfn4016P := by
  change (reflectRing usfn3743E).toPoly.mul (reflectRing usfn4015E).toPoly=usfn4016P
  rw [usfn3743_norm, usfn4015_norm]
  exact eq_of_beq (by decide : usfn3743P.mul usfn4015P == usfn4016P)

def usfn4017E : RingExpr := (.mul usfn788E usfn4016E)
def usfn4017P : Lean.Grind.CommRing.Poly := (.add (-96) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-72) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (36) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-6) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.num (0)))))))))
theorem usfn4017_norm : (reflectRing usfn4017E).toPoly=usfn4017P := by
  change (reflectRing usfn788E).toPoly.mul (reflectRing usfn4016E).toPoly=usfn4017P
  rw [usfn788_norm, usfn4016_norm]
  exact eq_of_beq (by decide : usfn788P.mul usfn4016P == usfn4017P)

def usfn4018E : RingExpr := (.mul (.mul (.var 15) (.mul (.var 1) (.pow (.var 2) 2))) (.mul (.int (-12)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.var 10)))))))))))
def usfn4018P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.num (0))))
theorem usfn4018_norm : (reflectRing usfn4018E).toPoly=usfn4018P := by
  exact eq_of_beq (by decide : (reflectRing usfn4018E).toPoly == usfn4018P)

def usfn4019E : RingExpr := (.mul (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.var 2)))) (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))) (.add (.mul (.int (-4)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))
def usfn4019P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))))) (.add (16) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-8) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.num (0))))))))
theorem usfn4019_norm : (reflectRing usfn4019E).toPoly=usfn4019P := by
  exact eq_of_beq (by decide : (reflectRing usfn4019E).toPoly == usfn4019P)

def usfn4020E : RingExpr := (.mul (.mul (.var 12) (.mul (.var 5) (.mul (.var 1) (.var 2)))) (.mul (.int 12) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))))
def usfn4020P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit))))))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))))) (.num (0))))
theorem usfn4020_norm : (reflectRing usfn4020E).toPoly=usfn4020P := by
  exact eq_of_beq (by decide : (reflectRing usfn4020E).toPoly == usfn4020P)

def usfn4021E : RingExpr := (.mul (.mul (.var 15) (.mul (.var 5) (.mul (.var 1) (.var 2)))) (.mul (.int 4) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.add (.int 1) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))))
def usfn4021P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit))))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit)))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))))) (.num (0))))))
theorem usfn4021_norm : (reflectRing usfn4021E).toPoly=usfn4021P := by
  exact eq_of_beq (by decide : (reflectRing usfn4021E).toPoly == usfn4021P)

def usfn4022E : RingExpr := (.mul usfn3177E usfn3739E)
def usfn4022P : Lean.Grind.CommRing.Poly := (.add (96) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-48) (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-18) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-36) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (18) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (9) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.num (0))))))))))))))))))
theorem usfn4022_norm : (reflectRing usfn4022E).toPoly=usfn4022P := by
  change (reflectRing usfn3177E).toPoly.mul (reflectRing usfn3739E).toPoly=usfn4022P
  rw [usfn3177_norm, usfn3739_norm]
  exact eq_of_beq (by decide : usfn3177P.mul usfn3739P == usfn4022P)

def usfn4023E : RingExpr := (.mul usfn381E usfn4022E)
def usfn4023P : Lean.Grind.CommRing.Poly := (.add (96) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-18) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (3) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (18) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (9) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.num (0))))))))))))))))))
theorem usfn4023_norm : (reflectRing usfn4023E).toPoly=usfn4023P := by
  change (reflectRing usfn381E).toPoly.mul (reflectRing usfn4022E).toPoly=usfn4023P
  rw [usfn381_norm, usfn4022_norm]
  exact eq_of_beq (by decide : usfn381P.mul usfn4022P == usfn4023P)

def usfn4024E : RingExpr := (.mul (.int (-2)) (.var 10))
def usfn4024P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨10,1⟩ .unit) (.num (0)))
theorem usfn4024_norm : (reflectRing usfn4024E).toPoly=usfn4024P := by
  exact eq_of_beq (by decide : (reflectRing usfn4024E).toPoly == usfn4024P)

def usfn4025E : RingExpr := (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))
def usfn4025P : Lean.Grind.CommRing.Poly := (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem usfn4025_norm : (reflectRing usfn4025E).toPoly=usfn4025P := by
  exact eq_of_beq (by decide : (reflectRing usfn4025E).toPoly == usfn4025P)

def usfn4026E : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.var 8))))))
def usfn4026P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn4026_norm : (reflectRing usfn4026E).toPoly=usfn4026P := by
  exact eq_of_beq (by decide : (reflectRing usfn4026E).toPoly == usfn4026P)

def usfn4027E : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))
def usfn4027P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn4027_norm : (reflectRing usfn4027E).toPoly=usfn4027P := by
  exact eq_of_beq (by decide : (reflectRing usfn4027E).toPoly == usfn4027P)

def usfn4028E : RingExpr := (.add (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 3))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))))))
def usfn4028P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))
theorem usfn4028_norm : (reflectRing usfn4028E).toPoly=usfn4028P := by
  exact eq_of_beq (by decide : (reflectRing usfn4028E).toPoly == usfn4028P)

def usfn4029E : RingExpr := (.add usfn4027E usfn4028E)
def usfn4029P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn4029_norm : (reflectRing usfn4029E).toPoly=usfn4029P := by
  change (reflectRing usfn4027E).toPoly.combine (reflectRing usfn4028E).toPoly=usfn4029P
  rw [usfn4027_norm, usfn4028_norm]
  exact eq_of_beq (by decide : usfn4027P.combine usfn4028P == usfn4029P)

def usfn4030E : RingExpr := (.add usfn4026E usfn4029E)
def usfn4030P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))
theorem usfn4030_norm : (reflectRing usfn4030E).toPoly=usfn4030P := by
  change (reflectRing usfn4026E).toPoly.combine (reflectRing usfn4029E).toPoly=usfn4030P
  rw [usfn4026_norm, usfn4029_norm]
  exact eq_of_beq (by decide : usfn4026P.combine usfn4029P == usfn4030P)

def usfn4031E : RingExpr := (.add usfn2766E usfn4030E)
def usfn4031P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn4031_norm : (reflectRing usfn4031E).toPoly=usfn4031P := by
  change (reflectRing usfn2766E).toPoly.combine (reflectRing usfn4030E).toPoly=usfn4031P
  rw [usfn2766_norm, usfn4030_norm]
  exact eq_of_beq (by decide : usfn2766P.combine usfn4030P == usfn4031P)

def usfn4032E : RingExpr := (.add usfn4025E usfn4031E)
def usfn4032P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0))))))))))
theorem usfn4032_norm : (reflectRing usfn4032E).toPoly=usfn4032P := by
  change (reflectRing usfn4025E).toPoly.combine (reflectRing usfn4031E).toPoly=usfn4032P
  rw [usfn4025_norm, usfn4031_norm]
  exact eq_of_beq (by decide : usfn4025P.combine usfn4031P == usfn4032P)

def usfn4033E : RingExpr := (.add usfn3643E usfn4032E)
def usfn4033P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.num (0)))))))))))
theorem usfn4033_norm : (reflectRing usfn4033E).toPoly=usfn4033P := by
  change (reflectRing usfn3643E).toPoly.combine (reflectRing usfn4032E).toPoly=usfn4033P
  rw [usfn3643_norm, usfn4032_norm]
  exact eq_of_beq (by decide : usfn3643P.combine usfn4032P == usfn4033P)

def usfn4034E : RingExpr := (.add usfn4024E usfn4033E)
def usfn4034P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (-2) (.mult ⟨10,1⟩ .unit) (.num (0))))))))))))
theorem usfn4034_norm : (reflectRing usfn4034E).toPoly=usfn4034P := by
  change (reflectRing usfn4024E).toPoly.combine (reflectRing usfn4033E).toPoly=usfn4034P
  rw [usfn4024_norm, usfn4033_norm]
  exact eq_of_beq (by decide : usfn4024P.combine usfn4033P == usfn4034P)

def usfn4035E : RingExpr := (.mul usfn133E usfn4034E)
def usfn4035P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit))) (.add (-2) (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)) (.num (0))))))))))))
theorem usfn4035_norm : (reflectRing usfn4035E).toPoly=usfn4035P := by
  change (reflectRing usfn133E).toPoly.mul (reflectRing usfn4034E).toPoly=usfn4035P
  rw [usfn133_norm, usfn4034_norm]
  exact eq_of_beq (by decide : usfn133P.mul usfn4034P == usfn4035P)

def usfn4036E : RingExpr := (.mul usfn409E usfn4035E)
def usfn4036P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))
theorem usfn4036_norm : (reflectRing usfn4036E).toPoly=usfn4036P := by
  change (reflectRing usfn409E).toPoly.mul (reflectRing usfn4035E).toPoly=usfn4036P
  rw [usfn409_norm, usfn4035_norm]
  exact eq_of_beq (by decide : usfn409P.mul usfn4035P == usfn4036P)

def usfn4037E : RingExpr := (.mul usfn102E usfn4036E)
def usfn4037P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit))) (.num (0))))))))))))
theorem usfn4037_norm : (reflectRing usfn4037E).toPoly=usfn4037P := by
  change (reflectRing usfn102E).toPoly.mul (reflectRing usfn4036E).toPoly=usfn4037P
  rw [usfn102_norm, usfn4036_norm]
  exact eq_of_beq (by decide : usfn102P.mul usfn4036P == usfn4037P)

def usfn4038E : RingExpr := (.mul usfn3E usfn4037E)
def usfn4038P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))) (.num (0))))))))))))
theorem usfn4038_norm : (reflectRing usfn4038E).toPoly=usfn4038P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn4037E).toPoly=usfn4038P
  rw [usfn3_norm, usfn4037_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn4037P == usfn4038P)

def usfn4039E : RingExpr := (.mul usfn362E usfn4038E)
def usfn4039P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.num (0))))))))))))
theorem usfn4039_norm : (reflectRing usfn4039E).toPoly=usfn4039P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn4038E).toPoly=usfn4039P
  rw [usfn362_norm, usfn4038_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn4038P == usfn4039P)

def usfn4040E : RingExpr := (.mul usfn1E usfn4039E)
def usfn4040P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.num (0))))))))))))
theorem usfn4040_norm : (reflectRing usfn4040E).toPoly=usfn4040P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn4039E).toPoly=usfn4040P
  rw [usfn1_norm, usfn4039_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn4039P == usfn4040P)

def usfn4041E : RingExpr := (.mul usfn3743E usfn4040E)
def usfn4041P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-36) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (18) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (12) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.num (0))))))))))))
theorem usfn4041_norm : (reflectRing usfn4041E).toPoly=usfn4041P := by
  change (reflectRing usfn3743E).toPoly.mul (reflectRing usfn4040E).toPoly=usfn4041P
  rw [usfn3743_norm, usfn4040_norm]
  exact eq_of_beq (by decide : usfn3743P.mul usfn4040P == usfn4041P)

#print axioms usfn4041_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
