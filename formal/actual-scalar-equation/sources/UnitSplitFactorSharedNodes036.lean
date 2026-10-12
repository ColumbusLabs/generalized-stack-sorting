import UnitSplitFactorSharedNodes035
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn2074E : RingExpr := (.add usfn2065E usfn2073E)
def usfn2074P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))
theorem usfn2074_norm : (reflectRing usfn2074E).toPoly=usfn2074P := by
  change (reflectRing usfn2065E).toPoly.combine (reflectRing usfn2073E).toPoly=usfn2074P
  rw [usfn2065_norm, usfn2073_norm]
  exact eq_of_beq (by decide : usfn2065P.combine usfn2073P == usfn2074P)

def usfn2075E : RingExpr := (.add usfn2064E usfn2074E)
def usfn2075P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn2075_norm : (reflectRing usfn2075E).toPoly=usfn2075P := by
  change (reflectRing usfn2064E).toPoly.combine (reflectRing usfn2074E).toPoly=usfn2075P
  rw [usfn2064_norm, usfn2074_norm]
  exact eq_of_beq (by decide : usfn2064P.combine usfn2074P == usfn2075P)

def usfn2076E : RingExpr := (.add usfn100E usfn2075E)
def usfn2076P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (-1))))))))))))
theorem usfn2076_norm : (reflectRing usfn2076E).toPoly=usfn2076P := by
  change (reflectRing usfn100E).toPoly.combine (reflectRing usfn2075E).toPoly=usfn2076P
  rw [usfn100_norm, usfn2075_norm]
  exact eq_of_beq (by decide : usfn100P.combine usfn2075P == usfn2076P)

def usfn2077E : RingExpr := (.mul usfn4E usfn2076E)
def usfn2077P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨8,2⟩ .unit) (.num (0)))))))))))))
theorem usfn2077_norm : (reflectRing usfn2077E).toPoly=usfn2077P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn2076E).toPoly=usfn2077P
  rw [usfn4_norm, usfn2076_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn2076P == usfn2077P)

def usfn2078E : RingExpr := (.mul usfn409E usfn2077E)
def usfn2078P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ .unit)) (.num (0)))))))))))))
theorem usfn2078_norm : (reflectRing usfn2078E).toPoly=usfn2078P := by
  change (reflectRing usfn409E).toPoly.mul (reflectRing usfn2077E).toPoly=usfn2078P
  rw [usfn409_norm, usfn2077_norm]
  exact eq_of_beq (by decide : usfn409P.mul usfn2077P == usfn2078P)

def usfn2079E : RingExpr := (.mul usfn362E usfn2078E)
def usfn2079P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit))) (.num (0)))))))))))))
theorem usfn2079_norm : (reflectRing usfn2079E).toPoly=usfn2079P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn2078E).toPoly=usfn2079P
  rw [usfn362_norm, usfn2078_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn2078P == usfn2079P)

def usfn2080E : RingExpr := (.mul usfn408E usfn2079E)
def usfn2080P : Lean.Grind.CommRing.Poly := (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit))) (.num (0)))))))))))))
theorem usfn2080_norm : (reflectRing usfn2080E).toPoly=usfn2080P := by
  change (reflectRing usfn408E).toPoly.mul (reflectRing usfn2079E).toPoly=usfn2080P
  rw [usfn408_norm, usfn2079_norm]
  exact eq_of_beq (by decide : usfn408P.mul usfn2079P == usfn2080P)

def usfn2081E : RingExpr := (.mul usfn407E usfn2080E)
def usfn2081P : Lean.Grind.CommRing.Poly := (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit)))))) (.num (0)))))))))))))
theorem usfn2081_norm : (reflectRing usfn2081E).toPoly=usfn2081P := by
  change (reflectRing usfn407E).toPoly.mul (reflectRing usfn2080E).toPoly=usfn2081P
  rw [usfn407_norm, usfn2080_norm]
  exact eq_of_beq (by decide : usfn407P.mul usfn2080P == usfn2081P)

def usfn2082E : RingExpr := (.mul (.mul (.var 14) (.mul (.var 1) (.var 2))) (.mul (.int 2) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))))
def usfn2082P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨14,1⟩ .unit)))))))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨14,1⟩ .unit)))))) (.num (0))))
theorem usfn2082_norm : (reflectRing usfn2082E).toPoly=usfn2082P := by
  exact eq_of_beq (by decide : (reflectRing usfn2082E).toPoly == usfn2082P)

def usfn2083E : RingExpr := (.add (.mul (.int 6) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.pow (.var 4) 3))))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2)))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.pow (.var 9) 2)))))))))))
def usfn2083P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))
theorem usfn2083_norm : (reflectRing usfn2083E).toPoly=usfn2083P := by
  exact eq_of_beq (by decide : (reflectRing usfn2083E).toPoly == usfn2083P)

def usfn2084E : RingExpr := (.add usfn1605E usfn2083E)
def usfn2084P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn2084_norm : (reflectRing usfn2084E).toPoly=usfn2084P := by
  change (reflectRing usfn1605E).toPoly.combine (reflectRing usfn2083E).toPoly=usfn2084P
  rw [usfn1605_norm, usfn2083_norm]
  exact eq_of_beq (by decide : usfn1605P.combine usfn2083P == usfn2084P)

def usfn2085E : RingExpr := (.add usfn512E usfn2084E)
def usfn2085P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))
theorem usfn2085_norm : (reflectRing usfn2085E).toPoly=usfn2085P := by
  change (reflectRing usfn512E).toPoly.combine (reflectRing usfn2084E).toPoly=usfn2085P
  rw [usfn512_norm, usfn2084_norm]
  exact eq_of_beq (by decide : usfn512P.combine usfn2084P == usfn2085P)

def usfn2086E : RingExpr := (.add usfn1732E usfn2085E)
def usfn2086P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))))
theorem usfn2086_norm : (reflectRing usfn2086E).toPoly=usfn2086P := by
  change (reflectRing usfn1732E).toPoly.combine (reflectRing usfn2085E).toPoly=usfn2086P
  rw [usfn1732_norm, usfn2085_norm]
  exact eq_of_beq (by decide : usfn1732P.combine usfn2085P == usfn2086P)

def usfn2087E : RingExpr := (.add usfn508E usfn2086E)
def usfn2087P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn2087_norm : (reflectRing usfn2087E).toPoly=usfn2087P := by
  change (reflectRing usfn508E).toPoly.combine (reflectRing usfn2086E).toPoly=usfn2087P
  rw [usfn508_norm, usfn2086_norm]
  exact eq_of_beq (by decide : usfn508P.combine usfn2086P == usfn2087P)

def usfn2088E : RingExpr := (.add usfn1579E usfn2087E)
def usfn2088P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))
theorem usfn2088_norm : (reflectRing usfn2088E).toPoly=usfn2088P := by
  change (reflectRing usfn1579E).toPoly.combine (reflectRing usfn2087E).toPoly=usfn2088P
  rw [usfn1579_norm, usfn2087_norm]
  exact eq_of_beq (by decide : usfn1579P.combine usfn2087P == usfn2088P)

def usfn2089E : RingExpr := (.add usfn945E usfn2088E)
def usfn2089P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))
theorem usfn2089_norm : (reflectRing usfn2089E).toPoly=usfn2089P := by
  change (reflectRing usfn945E).toPoly.combine (reflectRing usfn2088E).toPoly=usfn2089P
  rw [usfn945_norm, usfn2088_norm]
  exact eq_of_beq (by decide : usfn945P.combine usfn2088P == usfn2089P)

def usfn2090E : RingExpr := (.add usfn100E usfn2089E)
def usfn2090P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (-1))))))))))))
theorem usfn2090_norm : (reflectRing usfn2090E).toPoly=usfn2090P := by
  change (reflectRing usfn100E).toPoly.combine (reflectRing usfn2089E).toPoly=usfn2090P
  rw [usfn100_norm, usfn2089_norm]
  exact eq_of_beq (by decide : usfn100P.combine usfn2089P == usfn2090P)

def usfn2091E : RingExpr := (.mul usfn4E usfn2090E)
def usfn2091P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨8,2⟩ .unit) (.num (0)))))))))))))
theorem usfn2091_norm : (reflectRing usfn2091E).toPoly=usfn2091P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn2090E).toPoly=usfn2091P
  rw [usfn4_norm, usfn2090_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn2090P == usfn2091P)

def usfn2092E : RingExpr := (.mul usfn409E usfn2091E)
def usfn2092P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ .unit)) (.num (0)))))))))))))
theorem usfn2092_norm : (reflectRing usfn2092E).toPoly=usfn2092P := by
  change (reflectRing usfn409E).toPoly.mul (reflectRing usfn2091E).toPoly=usfn2092P
  rw [usfn409_norm, usfn2091_norm]
  exact eq_of_beq (by decide : usfn409P.mul usfn2091P == usfn2092P)

def usfn2093E : RingExpr := (.mul usfn841E usfn2092E)
def usfn2093P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))))) (.add (-16) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-8) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (6) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨15,1⟩ .unit))))) (.num (0)))))))))))))
theorem usfn2093_norm : (reflectRing usfn2093E).toPoly=usfn2093P := by
  change (reflectRing usfn841E).toPoly.mul (reflectRing usfn2092E).toPoly=usfn2093P
  rw [usfn841_norm, usfn2092_norm]
  exact eq_of_beq (by decide : usfn841P.mul usfn2092P == usfn2093P)

def usfn2094E : RingExpr := (.mul (.mul (.var 16) (.mul (.var 1) (.var 2))) (.mul (.int (-1)) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))
def usfn2094P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit)))))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨16,1⟩ .unit))))) (.num (0))))
theorem usfn2094_norm : (reflectRing usfn2094E).toPoly=usfn2094P := by
  exact eq_of_beq (by decide : (reflectRing usfn2094E).toPoly == usfn2094P)

def usfn2095E : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.var 9)))
def usfn2095P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))
theorem usfn2095_norm : (reflectRing usfn2095E).toPoly=usfn2095P := by
  exact eq_of_beq (by decide : (reflectRing usfn2095E).toPoly == usfn2095P)

def usfn2096E : RingExpr := (.mul (.int (-1)) (.mul (.var 3) (.pow (.var 8) 2)))
def usfn2096P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ .unit)) (.num (0)))
theorem usfn2096_norm : (reflectRing usfn2096E).toPoly=usfn2096P := by
  exact eq_of_beq (by decide : (reflectRing usfn2096E).toPoly == usfn2096P)

def usfn2097E : RingExpr := (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))
def usfn2097P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2097_norm : (reflectRing usfn2097E).toPoly=usfn2097P := by
  exact eq_of_beq (by decide : (reflectRing usfn2097E).toPoly == usfn2097P)

def usfn2098E : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 2)))))
def usfn2098P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2098_norm : (reflectRing usfn2098E).toPoly=usfn2098P := by
  exact eq_of_beq (by decide : (reflectRing usfn2098E).toPoly == usfn2098P)

def usfn2099E : RingExpr := (.mul (.int (-3)) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))))
def usfn2099P : Lean.Grind.CommRing.Poly := (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2099_norm : (reflectRing usfn2099E).toPoly=usfn2099P := by
  exact eq_of_beq (by decide : (reflectRing usfn2099E).toPoly == usfn2099P)

def usfn2100E : RingExpr := (.mul (.int 6) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2))))))
def usfn2100P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2100_norm : (reflectRing usfn2100E).toPoly=usfn2100P := by
  exact eq_of_beq (by decide : (reflectRing usfn2100E).toPoly == usfn2100P)

def usfn2101E : RingExpr := (.add (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.pow (.var 9) 2))))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 3)))))))))))
def usfn2101P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))
theorem usfn2101_norm : (reflectRing usfn2101E).toPoly=usfn2101P := by
  exact eq_of_beq (by decide : (reflectRing usfn2101E).toPoly == usfn2101P)

def usfn2102E : RingExpr := (.add usfn2100E usfn2101E)
def usfn2102P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))
theorem usfn2102_norm : (reflectRing usfn2102E).toPoly=usfn2102P := by
  change (reflectRing usfn2100E).toPoly.combine (reflectRing usfn2101E).toPoly=usfn2102P
  rw [usfn2100_norm, usfn2101_norm]
  exact eq_of_beq (by decide : usfn2100P.combine usfn2101P == usfn2102P)

def usfn2103E : RingExpr := (.add usfn2099E usfn2102E)
def usfn2103P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))
theorem usfn2103_norm : (reflectRing usfn2103E).toPoly=usfn2103P := by
  change (reflectRing usfn2099E).toPoly.combine (reflectRing usfn2102E).toPoly=usfn2103P
  rw [usfn2099_norm, usfn2102_norm]
  exact eq_of_beq (by decide : usfn2099P.combine usfn2102P == usfn2103P)

def usfn2104E : RingExpr := (.add usfn2098E usfn2103E)
def usfn2104P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))))))))
theorem usfn2104_norm : (reflectRing usfn2104E).toPoly=usfn2104P := by
  change (reflectRing usfn2098E).toPoly.combine (reflectRing usfn2103E).toPoly=usfn2104P
  rw [usfn2098_norm, usfn2103_norm]
  exact eq_of_beq (by decide : usfn2098P.combine usfn2103P == usfn2104P)

def usfn2105E : RingExpr := (.add usfn2097E usfn2104E)
def usfn2105P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))))
theorem usfn2105_norm : (reflectRing usfn2105E).toPoly=usfn2105P := by
  change (reflectRing usfn2097E).toPoly.combine (reflectRing usfn2104E).toPoly=usfn2105P
  rw [usfn2097_norm, usfn2104_norm]
  exact eq_of_beq (by decide : usfn2097P.combine usfn2104P == usfn2105P)

def usfn2106E : RingExpr := (.add usfn2096E usfn2105E)
def usfn2106P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ .unit)) (.num (0)))))))))))
theorem usfn2106_norm : (reflectRing usfn2106E).toPoly=usfn2106P := by
  change (reflectRing usfn2096E).toPoly.combine (reflectRing usfn2105E).toPoly=usfn2106P
  rw [usfn2096_norm, usfn2105_norm]
  exact eq_of_beq (by decide : usfn2096P.combine usfn2105P == usfn2106P)

def usfn2107E : RingExpr := (.add usfn2095E usfn2106E)
def usfn2107P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ .unit)) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))))
theorem usfn2107_norm : (reflectRing usfn2107E).toPoly=usfn2107P := by
  change (reflectRing usfn2095E).toPoly.combine (reflectRing usfn2106E).toPoly=usfn2107P
  rw [usfn2095_norm, usfn2106_norm]
  exact eq_of_beq (by decide : usfn2095P.combine usfn2106P == usfn2107P)

def usfn2108E : RingExpr := (.mul usfn4E usfn2107E)
def usfn2108P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ .unit)) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))
theorem usfn2108_norm : (reflectRing usfn2108E).toPoly=usfn2108P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn2107E).toPoly=usfn2108P
  rw [usfn4_norm, usfn2107_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn2107P == usfn2108P)

def usfn2109E : RingExpr := (.mul usfn382E usfn2108E)
def usfn2109P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-3) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ .unit)) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn2109_norm : (reflectRing usfn2109E).toPoly=usfn2109P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn2108E).toPoly=usfn2109P
  rw [usfn382_norm, usfn2108_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn2108P == usfn2109P)

def usfn2110E : RingExpr := (.mul usfn2E usfn2109E)
def usfn2110P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-3) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))
theorem usfn2110_norm : (reflectRing usfn2110E).toPoly=usfn2110P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn2109E).toPoly=usfn2110P
  rw [usfn2_norm, usfn2109_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn2109P == usfn2110P)

def usfn2111E : RingExpr := (.mul usfn1E usfn2110E)
def usfn2111P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-3) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))))))
theorem usfn2111_norm : (reflectRing usfn2111E).toPoly=usfn2111P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn2110E).toPoly=usfn2111P
  rw [usfn1_norm, usfn2110_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn2110P == usfn2111P)

def usfn2112E : RingExpr := (.mul usfn100E usfn2111E)
def usfn2112P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (3) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))))))
theorem usfn2112_norm : (reflectRing usfn2112E).toPoly=usfn2112P := by
  change (reflectRing usfn100E).toPoly.mul (reflectRing usfn2111E).toPoly=usfn2112P
  rw [usfn100_norm, usfn2111_norm]
  exact eq_of_beq (by decide : usfn100P.mul usfn2111P == usfn2112P)

def usfn2113E : RingExpr := (.mul usfn425E usfn2112E)
def usfn2113P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-6) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (3) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.num (0))))))))))))
theorem usfn2113_norm : (reflectRing usfn2113E).toPoly=usfn2113P := by
  change (reflectRing usfn425E).toPoly.mul (reflectRing usfn2112E).toPoly=usfn2113P
  rw [usfn425_norm, usfn2112_norm]
  exact eq_of_beq (by decide : usfn425P.mul usfn2112P == usfn2113P)

def usfn2114E : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))
def usfn2114P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2114_norm : (reflectRing usfn2114E).toPoly=usfn2114P := by
  exact eq_of_beq (by decide : (reflectRing usfn2114E).toPoly == usfn2114P)

def usfn2115E : RingExpr := (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2))))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 3)))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2))))))))))))
def usfn2115P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))))))
theorem usfn2115_norm : (reflectRing usfn2115E).toPoly=usfn2115P := by
  exact eq_of_beq (by decide : (reflectRing usfn2115E).toPoly == usfn2115P)

def usfn2116E : RingExpr := (.add usfn2114E usfn2115E)
def usfn2116P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))
theorem usfn2116_norm : (reflectRing usfn2116E).toPoly=usfn2116P := by
  change (reflectRing usfn2114E).toPoly.combine (reflectRing usfn2115E).toPoly=usfn2116P
  rw [usfn2114_norm, usfn2115_norm]
  exact eq_of_beq (by decide : usfn2114P.combine usfn2115P == usfn2116P)

def usfn2117E : RingExpr := (.add usfn2096E usfn2116E)
def usfn2117P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ .unit)) (.num (0)))))))))
theorem usfn2117_norm : (reflectRing usfn2117E).toPoly=usfn2117P := by
  change (reflectRing usfn2096E).toPoly.combine (reflectRing usfn2116E).toPoly=usfn2117P
  rw [usfn2096_norm, usfn2116_norm]
  exact eq_of_beq (by decide : usfn2096P.combine usfn2116P == usfn2117P)

def usfn2118E : RingExpr := (.add usfn2095E usfn2117E)
def usfn2118P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ .unit)) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))
theorem usfn2118_norm : (reflectRing usfn2118E).toPoly=usfn2118P := by
  change (reflectRing usfn2095E).toPoly.combine (reflectRing usfn2117E).toPoly=usfn2118P
  rw [usfn2095_norm, usfn2117_norm]
  exact eq_of_beq (by decide : usfn2095P.combine usfn2117P == usfn2118P)

def usfn2119E : RingExpr := (.mul usfn4E usfn2118E)
def usfn2119P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ .unit)) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))
theorem usfn2119_norm : (reflectRing usfn2119E).toPoly=usfn2119P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn2118E).toPoly=usfn2119P
  rw [usfn4_norm, usfn2118_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn2118P == usfn2119P)

def usfn2120E : RingExpr := (.mul usfn409E usfn2119E)
def usfn2120P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ .unit)) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))))
theorem usfn2120_norm : (reflectRing usfn2120E).toPoly=usfn2120P := by
  change (reflectRing usfn409E).toPoly.mul (reflectRing usfn2119E).toPoly=usfn2120P
  rw [usfn409_norm, usfn2119_norm]
  exact eq_of_beq (by decide : usfn409P.mul usfn2119P == usfn2120P)

def usfn2121E : RingExpr := (.mul usfn362E usfn2120E)
def usfn2121P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.num (0))))))))))
theorem usfn2121_norm : (reflectRing usfn2121E).toPoly=usfn2121P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn2120E).toPoly=usfn2121P
  rw [usfn362_norm, usfn2120_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn2120P == usfn2121P)

def usfn2122E : RingExpr := (.mul usfn2E usfn2121E)
def usfn2122P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))))
theorem usfn2122_norm : (reflectRing usfn2122E).toPoly=usfn2122P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn2121E).toPoly=usfn2122P
  rw [usfn2_norm, usfn2121_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn2121P == usfn2122P)

def usfn2123E : RingExpr := (.mul usfn1E usfn2122E)
def usfn2123P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.num (0))))))))))
theorem usfn2123_norm : (reflectRing usfn2123E).toPoly=usfn2123P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn2122E).toPoly=usfn2123P
  rw [usfn1_norm, usfn2122_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn2122P == usfn2123P)

def usfn2124E : RingExpr := (.mul usfn408E usfn2123E)
def usfn2124P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.num (0))))))))))
theorem usfn2124_norm : (reflectRing usfn2124E).toPoly=usfn2124P := by
  change (reflectRing usfn408E).toPoly.mul (reflectRing usfn2123E).toPoly=usfn2124P
  rw [usfn408_norm, usfn2123_norm]
  exact eq_of_beq (by decide : usfn408P.mul usfn2123P == usfn2124P)

def usfn2125E : RingExpr := (.mul usfn440E usfn2124E)
def usfn2125P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.num (0))))))))))
theorem usfn2125_norm : (reflectRing usfn2125E).toPoly=usfn2125P := by
  change (reflectRing usfn440E).toPoly.mul (reflectRing usfn2124E).toPoly=usfn2125P
  rw [usfn440_norm, usfn2124_norm]
  exact eq_of_beq (by decide : usfn440P.mul usfn2124P == usfn2125P)

def usfn2126E : RingExpr := (.mul (.mul (.var 15) (.var 1)) (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.pow (.var 8) 2)) (.add (.mul (.int (-2)) (.mul (.var 0) (.var 4))) (.add (.mul (.int 2) (.mul (.var 10) (.pow (.var 8) 2))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.pow (.var 8) 3))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.mul (.int 4) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2))))))))))))))))))))
def usfn2126P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.num (0))))))))
theorem usfn2126_norm : (reflectRing usfn2126E).toPoly=usfn2126P := by
  exact eq_of_beq (by decide : (reflectRing usfn2126E).toPoly == usfn2126P)

def usfn2127E : RingExpr := (.mul (.mul (.var 11) (.pow (.var 2) 5)) (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int 1) (.add (.mul (.int (-1)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2)))))))))))))))))
def usfn2127P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,5⟩ (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,5⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨2,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (4) (.mult ⟨2,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.num (0))))))
theorem usfn2127_norm : (reflectRing usfn2127E).toPoly=usfn2127P := by
  exact eq_of_beq (by decide : (reflectRing usfn2127E).toPoly == usfn2127P)

def usfn2128E : RingExpr := (.mul (.int 2) (.mul (.var 4) (.var 9)))
def usfn2128P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))
theorem usfn2128_norm : (reflectRing usfn2128E).toPoly=usfn2128P := by
  exact eq_of_beq (by decide : (reflectRing usfn2128E).toPoly == usfn2128P)

def usfn2129E : RingExpr := (.mul (.int (-1)) (.mul (.var 10) (.mul (.var 4) (.var 9))))
def usfn2129P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn2129_norm : (reflectRing usfn2129E).toPoly=usfn2129P := by
  exact eq_of_beq (by decide : (reflectRing usfn2129E).toPoly == usfn2129P)

def usfn2130E : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))
def usfn2130P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2130_norm : (reflectRing usfn2130E).toPoly=usfn2130P := by
  exact eq_of_beq (by decide : (reflectRing usfn2130E).toPoly == usfn2130P)

def usfn2131E : RingExpr := (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2)))))))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))) (.mul (.int 4) (.mul (.var 7) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.mul (.pow (.var 4) 3) (.pow (.var 9) 2)))))))))))
def usfn2131P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.num (0))))))
theorem usfn2131_norm : (reflectRing usfn2131E).toPoly=usfn2131P := by
  exact eq_of_beq (by decide : (reflectRing usfn2131E).toPoly == usfn2131P)

def usfn2132E : RingExpr := (.add usfn2130E usfn2131E)
def usfn2132P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))))))
theorem usfn2132_norm : (reflectRing usfn2132E).toPoly=usfn2132P := by
  change (reflectRing usfn2130E).toPoly.combine (reflectRing usfn2131E).toPoly=usfn2132P
  rw [usfn2130_norm, usfn2131_norm]
  exact eq_of_beq (by decide : usfn2130P.combine usfn2131P == usfn2132P)

def usfn2133E : RingExpr := (.add usfn506E usfn2132E)
def usfn2133P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0))))))))
theorem usfn2133_norm : (reflectRing usfn2133E).toPoly=usfn2133P := by
  change (reflectRing usfn506E).toPoly.combine (reflectRing usfn2132E).toPoly=usfn2133P
  rw [usfn506_norm, usfn2132_norm]
  exact eq_of_beq (by decide : usfn506P.combine usfn2132P == usfn2133P)

def usfn2134E : RingExpr := (.add usfn2129E usfn2133E)
def usfn2134P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))
theorem usfn2134_norm : (reflectRing usfn2134E).toPoly=usfn2134P := by
  change (reflectRing usfn2129E).toPoly.combine (reflectRing usfn2133E).toPoly=usfn2134P
  rw [usfn2129_norm, usfn2133_norm]
  exact eq_of_beq (by decide : usfn2129P.combine usfn2133P == usfn2134P)

def usfn2135E : RingExpr := (.add usfn2128E usfn2134E)
def usfn2135P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))
theorem usfn2135_norm : (reflectRing usfn2135E).toPoly=usfn2135P := by
  change (reflectRing usfn2128E).toPoly.combine (reflectRing usfn2134E).toPoly=usfn2135P
  rw [usfn2128_norm, usfn2134_norm]
  exact eq_of_beq (by decide : usfn2128P.combine usfn2134P == usfn2135P)

def usfn2136E : RingExpr := (.add usfn100E usfn2135E)
def usfn2136P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (-1))))))))))
theorem usfn2136_norm : (reflectRing usfn2136E).toPoly=usfn2136P := by
  change (reflectRing usfn100E).toPoly.combine (reflectRing usfn2135E).toPoly=usfn2136P
  rw [usfn100_norm, usfn2135_norm]
  exact eq_of_beq (by decide : usfn100P.combine usfn2135P == usfn2136P)

def usfn2137E : RingExpr := (.mul usfn133E usfn2136E)
def usfn2137P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))) (.add (-1) (.mult ⟨8,4⟩ .unit) (.num (0)))))))))))
theorem usfn2137_norm : (reflectRing usfn2137E).toPoly=usfn2137P := by
  change (reflectRing usfn133E).toPoly.mul (reflectRing usfn2136E).toPoly=usfn2137P
  rw [usfn133_norm, usfn2136_norm]
  exact eq_of_beq (by decide : usfn133P.mul usfn2136P == usfn2137P)

def usfn2138E : RingExpr := (.mul usfn362E usfn2137E)
def usfn2138P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-1) (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)) (.num (0)))))))))))
theorem usfn2138_norm : (reflectRing usfn2138E).toPoly=usfn2138P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn2137E).toPoly=usfn2138P
  rw [usfn362_norm, usfn2137_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn2137P == usfn2138P)

def usfn2139E : RingExpr := (.mul usfn2E usfn2138E)
def usfn2139P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (2) (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))
theorem usfn2139_norm : (reflectRing usfn2139E).toPoly=usfn2139P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn2138E).toPoly=usfn2139P
  rw [usfn2_norm, usfn2138_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn2138P == usfn2139P)

def usfn2140E : RingExpr := (.mul usfn1E usfn2139E)
def usfn2140P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))
theorem usfn2140_norm : (reflectRing usfn2140E).toPoly=usfn2140P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn2139E).toPoly=usfn2140P
  rw [usfn1_norm, usfn2139_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn2139P == usfn2140P)

def usfn2141E : RingExpr := (.mul usfn890E usfn2140E)
def usfn2141P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-8) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))
theorem usfn2141_norm : (reflectRing usfn2141E).toPoly=usfn2141P := by
  change (reflectRing usfn890E).toPoly.mul (reflectRing usfn2140E).toPoly=usfn2141P
  rw [usfn890_norm, usfn2140_norm]
  exact eq_of_beq (by decide : usfn890P.mul usfn2140P == usfn2141P)

def usfn2142E : RingExpr := (.mul usfn889E usfn2141E)
def usfn2142P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨2,4⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨2,4⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (4) (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-8) (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (4) (.mult ⟨2,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.num (0)))))))))))
theorem usfn2142_norm : (reflectRing usfn2142E).toPoly=usfn2142P := by
  change (reflectRing usfn889E).toPoly.mul (reflectRing usfn2141E).toPoly=usfn2142P
  rw [usfn889_norm, usfn2141_norm]
  exact eq_of_beq (by decide : usfn889P.mul usfn2141P == usfn2142P)

def usfn2143E : RingExpr := (.mul (.mul (.var 12) (.pow (.var 2) 4)) (.mul (.int 2) (.mul (.var 4) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))
def usfn2143P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-2) (.mult ⟨2,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0))))
theorem usfn2143_norm : (reflectRing usfn2143E).toPoly=usfn2143P := by
  exact eq_of_beq (by decide : (reflectRing usfn2143E).toPoly == usfn2143P)

def usfn2144E : RingExpr := (.mul (.mul (.var 14) (.pow (.var 2) 4)) (.mul (.int (-2)) (.mul (.var 4) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))
def usfn2144P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))) (.add (2) (.mult ⟨2,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨14,1⟩ .unit)))) (.num (0))))
theorem usfn2144_norm : (reflectRing usfn2144E).toPoly=usfn2144P := by
  exact eq_of_beq (by decide : (reflectRing usfn2144E).toPoly == usfn2144P)

def usfn2145E : RingExpr := (.mul (.int 5) (.mul (.var 4) (.var 9)))
def usfn2145P : Lean.Grind.CommRing.Poly := (.add (5) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))
theorem usfn2145_norm : (reflectRing usfn2145E).toPoly=usfn2145P := by
  exact eq_of_beq (by decide : (reflectRing usfn2145E).toPoly == usfn2145P)

def usfn2146E : RingExpr := (.mul (.int (-4)) (.mul (.var 10) (.mul (.var 4) (.var 9))))
def usfn2146P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn2146_norm : (reflectRing usfn2146E).toPoly=usfn2146P := by
  exact eq_of_beq (by decide : (reflectRing usfn2146E).toPoly == usfn2146P)

def usfn2147E : RingExpr := (.mul (.int (-4)) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3))))
def usfn2147P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.num (0)))
theorem usfn2147_norm : (reflectRing usfn2147E).toPoly=usfn2147P := by
  exact eq_of_beq (by decide : (reflectRing usfn2147E).toPoly == usfn2147P)

def usfn2148E : RingExpr := (.mul (.int (-4)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))
def usfn2148P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem usfn2148_norm : (reflectRing usfn2148E).toPoly=usfn2148P := by
  exact eq_of_beq (by decide : (reflectRing usfn2148E).toPoly == usfn2148P)

def usfn2149E : RingExpr := (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))
def usfn2149P : Lean.Grind.CommRing.Poly := (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2149_norm : (reflectRing usfn2149E).toPoly=usfn2149P := by
  exact eq_of_beq (by decide : (reflectRing usfn2149E).toPoly == usfn2149P)

def usfn2150E : RingExpr := (.mul (.int 4) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))
def usfn2150P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2150_norm : (reflectRing usfn2150E).toPoly=usfn2150P := by
  exact eq_of_beq (by decide : (reflectRing usfn2150E).toPoly == usfn2150P)

def usfn2151E : RingExpr := (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))
def usfn2151P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2151_norm : (reflectRing usfn2151E).toPoly=usfn2151P := by
  exact eq_of_beq (by decide : (reflectRing usfn2151E).toPoly == usfn2151P)

def usfn2152E : RingExpr := (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))))))
def usfn2152P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.num (0)))
theorem usfn2152_norm : (reflectRing usfn2152E).toPoly=usfn2152P := by
  exact eq_of_beq (by decide : (reflectRing usfn2152E).toPoly == usfn2152P)

def usfn2153E : RingExpr := (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2))))))))
def usfn2153P : Lean.Grind.CommRing.Poly := (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))
theorem usfn2153_norm : (reflectRing usfn2153E).toPoly=usfn2153P := by
  exact eq_of_beq (by decide : (reflectRing usfn2153E).toPoly == usfn2153P)

#print axioms usfn2153_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
