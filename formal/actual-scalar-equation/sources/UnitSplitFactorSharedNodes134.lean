import UnitSplitFactorSharedNodes133
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn6410E : RingExpr := (.mul (.mul (.var 14) (.pow (.var 2) 2)) (.mul (.int (-1)) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.mul (.add (.int (-1)) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))))))) (.add (.int (-3)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
def usfn6410P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨14,1⟩ .unit))))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨14,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))) (.add (-3) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))) (.num (0))))))
theorem usfn6410_norm : (reflectRing usfn6410E).toPoly=usfn6410P := by
  exact eq_of_beq (by decide : (reflectRing usfn6410E).toPoly == usfn6410P)

def usfn6411E : RingExpr := (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 10) 2) (.pow (.var 8) 3))))
def usfn6411P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0)))
theorem usfn6411_norm : (reflectRing usfn6411E).toPoly=usfn6411P := by
  exact eq_of_beq (by decide : (reflectRing usfn6411E).toPoly == usfn6411P)

def usfn6412E : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 4))))))
def usfn6412P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))
theorem usfn6412_norm : (reflectRing usfn6412E).toPoly=usfn6412P := by
  exact eq_of_beq (by decide : (reflectRing usfn6412E).toPoly == usfn6412P)

def usfn6413E : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2)))))))
def usfn6413P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6413_norm : (reflectRing usfn6413E).toPoly=usfn6413P := by
  exact eq_of_beq (by decide : (reflectRing usfn6413E).toPoly == usfn6413P)

def usfn6414E : RingExpr := (.mul (.int (-4)) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.pow (.var 8) 4)))))))
def usfn6414P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6414_norm : (reflectRing usfn6414E).toPoly=usfn6414P := by
  exact eq_of_beq (by decide : (reflectRing usfn6414E).toPoly == usfn6414P)

def usfn6415E : RingExpr := (.mul (.int 12) (.mul (.var 0) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2)))))))
def usfn6415P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6415_norm : (reflectRing usfn6415E).toPoly=usfn6415P := by
  exact eq_of_beq (by decide : (reflectRing usfn6415E).toPoly == usfn6415P)

def usfn6416E : RingExpr := (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.pow (.var 4) 3))))))))
def usfn6416P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0)))
theorem usfn6416_norm : (reflectRing usfn6416E).toPoly=usfn6416P := by
  exact eq_of_beq (by decide : (reflectRing usfn6416E).toPoly == usfn6416P)

def usfn6417E : RingExpr := (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 3) (.pow (.var 4) 3)))))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.pow (.var 8) 5)))))))) (.mul (.int 16) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 5) (.pow (.var 4) 2))))))))))
def usfn6417P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0)))))
theorem usfn6417_norm : (reflectRing usfn6417E).toPoly=usfn6417P := by
  exact eq_of_beq (by decide : (reflectRing usfn6417E).toPoly == usfn6417P)

def usfn6418E : RingExpr := (.add usfn6416E usfn6417E)
def usfn6418P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0))))))
theorem usfn6418_norm : (reflectRing usfn6418E).toPoly=usfn6418P := by
  change (reflectRing usfn6416E).toPoly.combine (reflectRing usfn6417E).toPoly=usfn6418P
  rw [usfn6416_norm, usfn6417_norm]
  exact eq_of_beq (by decide : usfn6416P.combine usfn6417P == usfn6418P)

def usfn6419E : RingExpr := (.add usfn6415E usfn6418E)
def usfn6419P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))
theorem usfn6419_norm : (reflectRing usfn6419E).toPoly=usfn6419P := by
  change (reflectRing usfn6415E).toPoly.combine (reflectRing usfn6418E).toPoly=usfn6419P
  rw [usfn6415_norm, usfn6418_norm]
  exact eq_of_beq (by decide : usfn6415P.combine usfn6418P == usfn6419P)

def usfn6420E : RingExpr := (.add usfn6414E usfn6419E)
def usfn6420P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))
theorem usfn6420_norm : (reflectRing usfn6420E).toPoly=usfn6420P := by
  change (reflectRing usfn6414E).toPoly.combine (reflectRing usfn6419E).toPoly=usfn6420P
  rw [usfn6414_norm, usfn6419_norm]
  exact eq_of_beq (by decide : usfn6414P.combine usfn6419P == usfn6420P)

def usfn6421E : RingExpr := (.add usfn6413E usfn6420E)
def usfn6421P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))))
theorem usfn6421_norm : (reflectRing usfn6421E).toPoly=usfn6421P := by
  change (reflectRing usfn6413E).toPoly.combine (reflectRing usfn6420E).toPoly=usfn6421P
  rw [usfn6413_norm, usfn6420_norm]
  exact eq_of_beq (by decide : usfn6413P.combine usfn6420P == usfn6421P)

def usfn6422E : RingExpr := (.add usfn6319E usfn6421E)
def usfn6422P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-5) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))))
theorem usfn6422_norm : (reflectRing usfn6422E).toPoly=usfn6422P := by
  change (reflectRing usfn6319E).toPoly.combine (reflectRing usfn6421E).toPoly=usfn6422P
  rw [usfn6319_norm, usfn6421_norm]
  exact eq_of_beq (by decide : usfn6319P.combine usfn6421P == usfn6422P)

def usfn6423E : RingExpr := (.add usfn6412E usfn6422E)
def usfn6423P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-5) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))))))
theorem usfn6423_norm : (reflectRing usfn6423E).toPoly=usfn6423P := by
  change (reflectRing usfn6412E).toPoly.combine (reflectRing usfn6422E).toPoly=usfn6423P
  rw [usfn6412_norm, usfn6422_norm]
  exact eq_of_beq (by decide : usfn6412P.combine usfn6422P == usfn6423P)

def usfn6424E : RingExpr := (.add usfn6317E usfn6423E)
def usfn6424P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-5) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))))))
theorem usfn6424_norm : (reflectRing usfn6424E).toPoly=usfn6424P := by
  change (reflectRing usfn6317E).toPoly.combine (reflectRing usfn6423E).toPoly=usfn6424P
  rw [usfn6317_norm, usfn6423_norm]
  exact eq_of_beq (by decide : usfn6317P.combine usfn6423P == usfn6424P)

def usfn6425E : RingExpr := (.add usfn6411E usfn6424E)
def usfn6425P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-5) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0)))))))))))))
theorem usfn6425_norm : (reflectRing usfn6425E).toPoly=usfn6425P := by
  change (reflectRing usfn6411E).toPoly.combine (reflectRing usfn6424E).toPoly=usfn6425P
  rw [usfn6411_norm, usfn6424_norm]
  exact eq_of_beq (by decide : usfn6411P.combine usfn6424P == usfn6425P)

def usfn6426E : RingExpr := (.add usfn3080E usfn6425E)
def usfn6426P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-5) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-1) (.mult ⟨4,1⟩ .unit) (.num (0))))))))))))))
theorem usfn6426_norm : (reflectRing usfn6426E).toPoly=usfn6426P := by
  change (reflectRing usfn3080E).toPoly.combine (reflectRing usfn6425E).toPoly=usfn6426P
  rw [usfn3080_norm, usfn6425_norm]
  exact eq_of_beq (by decide : usfn3080P.combine usfn6425P == usfn6426P)

def usfn6427E : RingExpr := (.mul usfn4E usfn6426E)
def usfn6427P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-5) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)) (.num (0))))))))))))))
theorem usfn6427_norm : (reflectRing usfn6427E).toPoly=usfn6427P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn6426E).toPoly=usfn6427P
  rw [usfn4_norm, usfn6426_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn6426P == usfn6427P)

def usfn6428E : RingExpr := (.mul usfn3E usfn6427E)
def usfn6428P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-5) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))))
theorem usfn6428_norm : (reflectRing usfn6428E).toPoly=usfn6428P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn6427E).toPoly=usfn6428P
  rw [usfn3_norm, usfn6427_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn6427P == usfn6428P)

def usfn6429E : RingExpr := (.mul usfn362E usfn6428E)
def usfn6429P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-5) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))))
theorem usfn6429_norm : (reflectRing usfn6429E).toPoly=usfn6429P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn6428E).toPoly=usfn6429P
  rw [usfn362_norm, usfn6428_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn6428P == usfn6429P)

def usfn6430E : RingExpr := (.mul usfn382E usfn6429E)
def usfn6430P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-5) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))))))))
theorem usfn6430_norm : (reflectRing usfn6430E).toPoly=usfn6430P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn6429E).toPoly=usfn6430P
  rw [usfn382_norm, usfn6429_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn6429P == usfn6430P)

def usfn6431E : RingExpr := (.mul usfn2E usfn6430E)
def usfn6431P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-5) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))
theorem usfn6431_norm : (reflectRing usfn6431E).toPoly=usfn6431P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn6430E).toPoly=usfn6431P
  rw [usfn2_norm, usfn6430_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn6430P == usfn6431P)

def usfn6432E : RingExpr := (.mul usfn408E usfn6431E)
def usfn6432P : Lean.Grind.CommRing.Poly := (.add (-32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (10) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))
theorem usfn6432_norm : (reflectRing usfn6432E).toPoly=usfn6432P := by
  change (reflectRing usfn408E).toPoly.mul (reflectRing usfn6431E).toPoly=usfn6432P
  rw [usfn408_norm, usfn6431_norm]
  exact eq_of_beq (by decide : usfn408P.mul usfn6431P == usfn6432P)

def usfn6433E : RingExpr := (.mul usfn944E usfn6432E)
def usfn6433P : Lean.Grind.CommRing.Poly := (.add (-32) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (8) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (10) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (2) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))) (.num (0))))))))))))))
theorem usfn6433_norm : (reflectRing usfn6433E).toPoly=usfn6433P := by
  change (reflectRing usfn944E).toPoly.mul (reflectRing usfn6432E).toPoly=usfn6433P
  rw [usfn944_norm, usfn6432_norm]
  exact eq_of_beq (by decide : usfn944P.mul usfn6432P == usfn6433P)

def usfn6434E : RingExpr := (.mul (.mul (.var 16) (.pow (.var 2) 2)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))))))))))))
def usfn6434P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨16,1⟩ .unit))))))))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit))))))) (.num (0))))
theorem usfn6434_norm : (reflectRing usfn6434E).toPoly=usfn6434P := by
  exact eq_of_beq (by decide : (reflectRing usfn6434E).toPoly == usfn6434P)

def usfn6435E : RingExpr := (.mul (.int (-16)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2)))))))
def usfn6435P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6435_norm : (reflectRing usfn6435E).toPoly=usfn6435P := by
  exact eq_of_beq (by decide : (reflectRing usfn6435E).toPoly == usfn6435P)

def usfn6436E : RingExpr := (.mul (.int (-8)) (.mul (.var 7) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 6) (.mul (.pow (.var 8) 3) (.pow (.var 4) 3)))))))
def usfn6436P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6436_norm : (reflectRing usfn6436E).toPoly=usfn6436P := by
  exact eq_of_beq (by decide : (reflectRing usfn6436E).toPoly == usfn6436P)

def usfn6437E : RingExpr := (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2)))))))
def usfn6437P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6437_norm : (reflectRing usfn6437E).toPoly=usfn6437P := by
  exact eq_of_beq (by decide : (reflectRing usfn6437E).toPoly == usfn6437P)

def usfn6438E : RingExpr := (.mul (.int 8) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.pow (.var 8) 3)))))))
def usfn6438P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6438_norm : (reflectRing usfn6438E).toPoly=usfn6438P := by
  exact eq_of_beq (by decide : (reflectRing usfn6438E).toPoly == usfn6438P)

def usfn6439E : RingExpr := (.add (.mul (.int (-8)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 5) (.pow (.var 8) 5)))))))) (.add (.mul (.int 16) (.mul (.var 9) (.mul (.pow (.var 0) 3) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 8) (.mul (.pow (.var 8) 5) (.pow (.var 4) 4)))))))) (.mul (.int 40) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 6) (.mul (.pow (.var 8) 5) (.pow (.var 4) 3))))))))))
def usfn6439P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0)))))
theorem usfn6439_norm : (reflectRing usfn6439E).toPoly=usfn6439P := by
  exact eq_of_beq (by decide : (reflectRing usfn6439E).toPoly == usfn6439P)

def usfn6440E : RingExpr := (.add usfn5067E usfn6439E)
def usfn6440P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0))))))
theorem usfn6440_norm : (reflectRing usfn6440E).toPoly=usfn6440P := by
  change (reflectRing usfn5067E).toPoly.combine (reflectRing usfn6439E).toPoly=usfn6440P
  rw [usfn5067_norm, usfn6439_norm]
  exact eq_of_beq (by decide : usfn5067P.combine usfn6439P == usfn6440P)

def usfn6441E : RingExpr := (.add usfn6438E usfn6440E)
def usfn6441P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))
theorem usfn6441_norm : (reflectRing usfn6441E).toPoly=usfn6441P := by
  change (reflectRing usfn6438E).toPoly.combine (reflectRing usfn6440E).toPoly=usfn6441P
  rw [usfn6438_norm, usfn6440_norm]
  exact eq_of_beq (by decide : usfn6438P.combine usfn6440P == usfn6441P)

def usfn6442E : RingExpr := (.add usfn6437E usfn6441E)
def usfn6442P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))
theorem usfn6442_norm : (reflectRing usfn6442E).toPoly=usfn6442P := by
  change (reflectRing usfn6437E).toPoly.combine (reflectRing usfn6441E).toPoly=usfn6442P
  rw [usfn6437_norm, usfn6441_norm]
  exact eq_of_beq (by decide : usfn6437P.combine usfn6441P == usfn6442P)

def usfn6443E : RingExpr := (.add usfn6436E usfn6442E)
def usfn6443P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))))
theorem usfn6443_norm : (reflectRing usfn6443E).toPoly=usfn6443P := by
  change (reflectRing usfn6436E).toPoly.combine (reflectRing usfn6442E).toPoly=usfn6443P
  rw [usfn6436_norm, usfn6442_norm]
  exact eq_of_beq (by decide : usfn6436P.combine usfn6442P == usfn6443P)

def usfn6444E : RingExpr := (.add usfn6435E usfn6443E)
def usfn6444P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))))
theorem usfn6444_norm : (reflectRing usfn6444E).toPoly=usfn6444P := by
  change (reflectRing usfn6435E).toPoly.combine (reflectRing usfn6443E).toPoly=usfn6444P
  rw [usfn6435_norm, usfn6443_norm]
  exact eq_of_beq (by decide : usfn6435P.combine usfn6443P == usfn6444P)

def usfn6445E : RingExpr := (.add usfn565E usfn6444E)
def usfn6445P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))))))))))
theorem usfn6445_norm : (reflectRing usfn6445E).toPoly=usfn6445P := by
  change (reflectRing usfn565E).toPoly.combine (reflectRing usfn6444E).toPoly=usfn6445P
  rw [usfn565_norm, usfn6444_norm]
  exact eq_of_beq (by decide : usfn565P.combine usfn6444P == usfn6445P)

def usfn6446E : RingExpr := (.add usfn83E usfn6445E)
def usfn6446P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (1)))))))))))
theorem usfn6446_norm : (reflectRing usfn6446E).toPoly=usfn6446P := by
  change (reflectRing usfn83E).toPoly.combine (reflectRing usfn6445E).toPoly=usfn6446P
  rw [usfn83_norm, usfn6445_norm]
  exact eq_of_beq (by decide : usfn83P.combine usfn6445P == usfn6446P)

def usfn6447E : RingExpr := (.mul usfn4E usfn6446E)
def usfn6447P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (1) (.mult ⟨8,2⟩ .unit) (.num (0))))))))))))
theorem usfn6447_norm : (reflectRing usfn6447E).toPoly=usfn6447P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn6446E).toPoly=usfn6447P
  rw [usfn4_norm, usfn6446_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn6446P == usfn6447P)

def usfn6448E : RingExpr := (.mul usfn3E usfn6447E)
def usfn6448P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))))
theorem usfn6448_norm : (reflectRing usfn6448E).toPoly=usfn6448P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn6447E).toPoly=usfn6448P
  rw [usfn3_norm, usfn6447_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn6447P == usfn6448P)

def usfn6449E : RingExpr := (.mul usfn2E usfn6448E)
def usfn6449P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))
theorem usfn6449_norm : (reflectRing usfn6449E).toPoly=usfn6449P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn6448E).toPoly=usfn6449P
  rw [usfn2_norm, usfn6448_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn6448P == usfn6449P)

def usfn6450E : RingExpr := (.mul usfn531E usfn6449E)
def usfn6450P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨2,1⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (40) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))) (.num (0))))))))))))
theorem usfn6450_norm : (reflectRing usfn6450E).toPoly=usfn6450P := by
  change (reflectRing usfn531E).toPoly.mul (reflectRing usfn6449E).toPoly=usfn6450P
  rw [usfn531_norm, usfn6449_norm]
  exact eq_of_beq (by decide : usfn531P.mul usfn6449P == usfn6450P)

def usfn6451E : RingExpr := (.mul (.mul (.var 14) (.var 2)) (.mul (.int (-1)) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.mul (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.int (-1)) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3)))))))))))))))
def usfn6451P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨14,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨14,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))) (.add (-1) (.mult ⟨2,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit))))) (.num (0))))))
theorem usfn6451_norm : (reflectRing usfn6451E).toPoly=usfn6451P := by
  exact eq_of_beq (by decide : (reflectRing usfn6451E).toPoly == usfn6451P)

def usfn6452E : RingExpr := (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 4)))))))
def usfn6452P : Lean.Grind.CommRing.Poly := (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6452_norm : (reflectRing usfn6452E).toPoly=usfn6452P := by
  exact eq_of_beq (by decide : (reflectRing usfn6452E).toPoly == usfn6452P)

def usfn6453E : RingExpr := (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2)))))))
def usfn6453P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6453_norm : (reflectRing usfn6453E).toPoly=usfn6453P := by
  exact eq_of_beq (by decide : (reflectRing usfn6453E).toPoly == usfn6453P)

def usfn6454E : RingExpr := (.mul (.int (-8)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2)))))))
def usfn6454P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6454_norm : (reflectRing usfn6454E).toPoly=usfn6454P := by
  exact eq_of_beq (by decide : (reflectRing usfn6454E).toPoly == usfn6454P)

def usfn6455E : RingExpr := (.mul (.int 16) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.pow (.var 8) 3)))))))
def usfn6455P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6455_norm : (reflectRing usfn6455E).toPoly=usfn6455P := by
  exact eq_of_beq (by decide : (reflectRing usfn6455E).toPoly == usfn6455P)

def usfn6456E : RingExpr := (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2))))))))
def usfn6456P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))
theorem usfn6456_norm : (reflectRing usfn6456E).toPoly=usfn6456P := by
  exact eq_of_beq (by decide : (reflectRing usfn6456E).toPoly == usfn6456P)

def usfn6457E : RingExpr := (.add (.mul (.int (-8)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 5) (.pow (.var 8) 5)))))))) (.add (.mul (.int 24) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.pow (.var 4) 2)))))))) (.mul (.int 32) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 6) (.mul (.pow (.var 8) 5) (.pow (.var 4) 3))))))))))
def usfn6457P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0)))))
theorem usfn6457_norm : (reflectRing usfn6457E).toPoly=usfn6457P := by
  exact eq_of_beq (by decide : (reflectRing usfn6457E).toPoly == usfn6457P)

def usfn6458E : RingExpr := (.add usfn6456E usfn6457E)
def usfn6458P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0))))))
theorem usfn6458_norm : (reflectRing usfn6458E).toPoly=usfn6458P := by
  change (reflectRing usfn6456E).toPoly.combine (reflectRing usfn6457E).toPoly=usfn6458P
  rw [usfn6456_norm, usfn6457_norm]
  exact eq_of_beq (by decide : usfn6456P.combine usfn6457P == usfn6458P)

def usfn6459E : RingExpr := (.add usfn6455E usfn6458E)
def usfn6459P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))
theorem usfn6459_norm : (reflectRing usfn6459E).toPoly=usfn6459P := by
  change (reflectRing usfn6455E).toPoly.combine (reflectRing usfn6458E).toPoly=usfn6459P
  rw [usfn6455_norm, usfn6458_norm]
  exact eq_of_beq (by decide : usfn6455P.combine usfn6458P == usfn6459P)

def usfn6460E : RingExpr := (.add usfn3840E usfn6459E)
def usfn6460P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))
theorem usfn6460_norm : (reflectRing usfn6460E).toPoly=usfn6460P := by
  change (reflectRing usfn3840E).toPoly.combine (reflectRing usfn6459E).toPoly=usfn6460P
  rw [usfn3840_norm, usfn6459_norm]
  exact eq_of_beq (by decide : usfn3840P.combine usfn6459P == usfn6460P)

def usfn6461E : RingExpr := (.add usfn6296E usfn6460E)
def usfn6461P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))))
theorem usfn6461_norm : (reflectRing usfn6461E).toPoly=usfn6461P := by
  change (reflectRing usfn6296E).toPoly.combine (reflectRing usfn6460E).toPoly=usfn6461P
  rw [usfn6296_norm, usfn6460_norm]
  exact eq_of_beq (by decide : usfn6296P.combine usfn6460P == usfn6461P)

def usfn6462E : RingExpr := (.add usfn6454E usfn6461E)
def usfn6462P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))))
theorem usfn6462_norm : (reflectRing usfn6462E).toPoly=usfn6462P := by
  change (reflectRing usfn6454E).toPoly.combine (reflectRing usfn6461E).toPoly=usfn6462P
  rw [usfn6454_norm, usfn6461_norm]
  exact eq_of_beq (by decide : usfn6454P.combine usfn6461P == usfn6462P)

def usfn6463E : RingExpr := (.add usfn6453E usfn6462E)
def usfn6463P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))))))
theorem usfn6463_norm : (reflectRing usfn6463E).toPoly=usfn6463P := by
  change (reflectRing usfn6453E).toPoly.combine (reflectRing usfn6462E).toPoly=usfn6463P
  rw [usfn6453_norm, usfn6462_norm]
  exact eq_of_beq (by decide : usfn6453P.combine usfn6462P == usfn6463P)

def usfn6464E : RingExpr := (.add usfn6452E usfn6463E)
def usfn6464P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))))))
theorem usfn6464_norm : (reflectRing usfn6464E).toPoly=usfn6464P := by
  change (reflectRing usfn6452E).toPoly.combine (reflectRing usfn6463E).toPoly=usfn6464P
  rw [usfn6452_norm, usfn6463_norm]
  exact eq_of_beq (by decide : usfn6452P.combine usfn6463P == usfn6464P)

def usfn6465E : RingExpr := (.add usfn6292E usfn6464E)
def usfn6465P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))))))))))))
theorem usfn6465_norm : (reflectRing usfn6465E).toPoly=usfn6465P := by
  change (reflectRing usfn6292E).toPoly.combine (reflectRing usfn6464E).toPoly=usfn6465P
  rw [usfn6292_norm, usfn6464_norm]
  exact eq_of_beq (by decide : usfn6292P.combine usfn6464P == usfn6465P)

def usfn6466E : RingExpr := (.add usfn6034E usfn6465E)
def usfn6466P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0))))))))))))))
theorem usfn6466_norm : (reflectRing usfn6466E).toPoly=usfn6466P := by
  change (reflectRing usfn6034E).toPoly.combine (reflectRing usfn6465E).toPoly=usfn6466P
  rw [usfn6034_norm, usfn6465_norm]
  exact eq_of_beq (by decide : usfn6034P.combine usfn6465P == usfn6466P)

def usfn6467E : RingExpr := (.add usfn565E usfn6466E)
def usfn6467P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))))))))))))))
theorem usfn6467_norm : (reflectRing usfn6467E).toPoly=usfn6467P := by
  change (reflectRing usfn565E).toPoly.combine (reflectRing usfn6466E).toPoly=usfn6467P
  rw [usfn565_norm, usfn6466_norm]
  exact eq_of_beq (by decide : usfn565P.combine usfn6466P == usfn6467P)

def usfn6468E : RingExpr := (.add usfn83E usfn6467E)
def usfn6468P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (1)))))))))))))))
theorem usfn6468_norm : (reflectRing usfn6468E).toPoly=usfn6468P := by
  change (reflectRing usfn83E).toPoly.combine (reflectRing usfn6467E).toPoly=usfn6468P
  rw [usfn83_norm, usfn6467_norm]
  exact eq_of_beq (by decide : usfn83P.combine usfn6467P == usfn6468P)

def usfn6469E : RingExpr := (.mul usfn4E usfn6468E)
def usfn6469P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (1) (.mult ⟨8,2⟩ .unit) (.num (0))))))))))))))))
theorem usfn6469_norm : (reflectRing usfn6469E).toPoly=usfn6469P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn6468E).toPoly=usfn6469P
  rw [usfn4_norm, usfn6468_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn6468P == usfn6469P)

def usfn6470E : RingExpr := (.mul usfn3E usfn6469E)
def usfn6470P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))))))))
theorem usfn6470_norm : (reflectRing usfn6470E).toPoly=usfn6470P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn6469E).toPoly=usfn6470P
  rw [usfn3_norm, usfn6469_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn6469P == usfn6470P)

def usfn6471E : RingExpr := (.mul usfn362E usfn6470E)
def usfn6471P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))))))
theorem usfn6471_norm : (reflectRing usfn6471E).toPoly=usfn6471P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn6470E).toPoly=usfn6471P
  rw [usfn362_norm, usfn6470_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn6470P == usfn6471P)

def usfn6472E : RingExpr := (.mul usfn382E usfn6471E)
def usfn6472P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))))))))))
theorem usfn6472_norm : (reflectRing usfn6472E).toPoly=usfn6472P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn6471E).toPoly=usfn6472P
  rw [usfn382_norm, usfn6471_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn6471P == usfn6472P)

def usfn6473E : RingExpr := (.mul usfn2E usfn6472E)
def usfn6473P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))))
theorem usfn6473_norm : (reflectRing usfn6473E).toPoly=usfn6473P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn6472E).toPoly=usfn6473P
  rw [usfn2_norm, usfn6472_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn6472P == usfn6473P)

def usfn6474E : RingExpr := (.mul usfn545E usfn6473E)
def usfn6474P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (2) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))) (.num (0))))))))))))))))
theorem usfn6474_norm : (reflectRing usfn6474E).toPoly=usfn6474P := by
  change (reflectRing usfn545E).toPoly.mul (reflectRing usfn6473E).toPoly=usfn6474P
  rw [usfn545_norm, usfn6473_norm]
  exact eq_of_beq (by decide : usfn545P.mul usfn6473P == usfn6474P)

def usfn6475E : RingExpr := (.mul (.mul (.var 16) (.var 2)) (.mul (.int (-1)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.mul (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.int (-1)) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3)))))))))))))))
def usfn6475P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨16,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨16,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit)))))))) (.add (-1) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit))))))) (.num (0))))))
theorem usfn6475_norm : (reflectRing usfn6475E).toPoly=usfn6475P := by
  exact eq_of_beq (by decide : (reflectRing usfn6475E).toPoly == usfn6475P)

def usfn6476E : RingExpr := (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.pow (.var 8) 3)))))))
def usfn6476P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6476_norm : (reflectRing usfn6476E).toPoly=usfn6476P := by
  exact eq_of_beq (by decide : (reflectRing usfn6476E).toPoly == usfn6476P)

def usfn6477E : RingExpr := (.mul (.int 8) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2)))))))
def usfn6477P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn6477_norm : (reflectRing usfn6477E).toPoly=usfn6477P := by
  exact eq_of_beq (by decide : (reflectRing usfn6477E).toPoly == usfn6477P)

def usfn6478E : RingExpr := (.add (.mul (.int (-16)) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 6) (.mul (.pow (.var 8) 5) (.pow (.var 4) 3)))))))) (.add (.mul (.int 8) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 5) (.pow (.var 8) 5)))))))) (.mul (.int 16) (.mul (.var 9) (.mul (.pow (.var 0) 3) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 7) (.mul (.pow (.var 8) 5) (.pow (.var 4) 2))))))))))
def usfn6478P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0)))))
theorem usfn6478_norm : (reflectRing usfn6478E).toPoly=usfn6478P := by
  exact eq_of_beq (by decide : (reflectRing usfn6478E).toPoly == usfn6478P)

def usfn6479E : RingExpr := (.add usfn6477E usfn6478E)
def usfn6479P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))
theorem usfn6479_norm : (reflectRing usfn6479E).toPoly=usfn6479P := by
  change (reflectRing usfn6477E).toPoly.combine (reflectRing usfn6478E).toPoly=usfn6479P
  rw [usfn6477_norm, usfn6478_norm]
  exact eq_of_beq (by decide : usfn6477P.combine usfn6478P == usfn6479P)

def usfn6480E : RingExpr := (.add usfn6476E usfn6479E)
def usfn6480P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))
theorem usfn6480_norm : (reflectRing usfn6480E).toPoly=usfn6480P := by
  change (reflectRing usfn6476E).toPoly.combine (reflectRing usfn6479E).toPoly=usfn6480P
  rw [usfn6476_norm, usfn6479_norm]
  exact eq_of_beq (by decide : usfn6476P.combine usfn6479P == usfn6480P)

def usfn6481E : RingExpr := (.add usfn100E usfn6480E)
def usfn6481P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (-1)))))))
theorem usfn6481_norm : (reflectRing usfn6481E).toPoly=usfn6481P := by
  change (reflectRing usfn100E).toPoly.combine (reflectRing usfn6480E).toPoly=usfn6481P
  rw [usfn100_norm, usfn6480_norm]
  exact eq_of_beq (by decide : usfn100P.combine usfn6480P == usfn6481P)

def usfn6482E : RingExpr := (.mul usfn4E usfn6481E)
def usfn6482P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨8,2⟩ .unit) (.num (0))))))))
theorem usfn6482_norm : (reflectRing usfn6482E).toPoly=usfn6482P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn6481E).toPoly=usfn6482P
  rw [usfn4_norm, usfn6481_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn6481P == usfn6482P)

def usfn6483E : RingExpr := (.mul usfn3E usfn6482E)
def usfn6483P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))
theorem usfn6483_norm : (reflectRing usfn6483E).toPoly=usfn6483P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn6482E).toPoly=usfn6483P
  rw [usfn3_norm, usfn6482_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn6482P == usfn6483P)

def usfn6484E : RingExpr := (.mul usfn362E usfn6483E)
def usfn6484P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))
theorem usfn6484_norm : (reflectRing usfn6484E).toPoly=usfn6484P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn6483E).toPoly=usfn6484P
  rw [usfn362_norm, usfn6483_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn6483P == usfn6484P)

def usfn6485E : RingExpr := (.mul usfn382E usfn6484E)
def usfn6485P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))
theorem usfn6485_norm : (reflectRing usfn6485E).toPoly=usfn6485P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn6484E).toPoly=usfn6485P
  rw [usfn382_norm, usfn6484_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn6484P == usfn6485P)

def usfn6486E : RingExpr := (.mul usfn2E usfn6485E)
def usfn6486P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))
theorem usfn6486_norm : (reflectRing usfn6486E).toPoly=usfn6486P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn6485E).toPoly=usfn6486P
  rw [usfn2_norm, usfn6485_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn6485P == usfn6486P)

def usfn6487E : RingExpr := (.mul usfn1034E usfn6486E)
def usfn6487P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,8⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))) (.num (0))))))))
theorem usfn6487_norm : (reflectRing usfn6487E).toPoly=usfn6487P := by
  change (reflectRing usfn1034E).toPoly.mul (reflectRing usfn6486E).toPoly=usfn6487P
  rw [usfn1034_norm, usfn6486_norm]
  exact eq_of_beq (by decide : usfn1034P.mul usfn6486P == usfn6487P)

def usfn6488E : RingExpr := (.mul (.var 14) (.mul (.int (-1)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 3))))))))))))))))
def usfn6488P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨14,1⟩ .unit)))))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))) (.num (0))))
theorem usfn6488_norm : (reflectRing usfn6488E).toPoly=usfn6488P := by
  exact eq_of_beq (by decide : (reflectRing usfn6488E).toPoly == usfn6488P)

def usfn6489E : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 3))))))
def usfn6489P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))
theorem usfn6489_norm : (reflectRing usfn6489E).toPoly=usfn6489P := by
  exact eq_of_beq (by decide : (reflectRing usfn6489E).toPoly == usfn6489P)

#print axioms usfn6489_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
