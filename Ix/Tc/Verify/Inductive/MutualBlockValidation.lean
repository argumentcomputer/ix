import Ix.Tc.Verify.Check.SingletonInductive
import Ix.Tc.Verify.Inductive.MutualBlockFixture

/-!
# Production validation of the mutual `Tree`/`TreeList` blocks

The exact compiler and ingress fixture is fed to the real anonymous
inductive-block checker.  Its generated two-recursor cache is then consumed
by the real recursor-block checker for the separately owned physical block.
No semantic certificate or oracle participates in either execution.
-/

namespace Ix.Tc.MutualTreeFixture

local instance validationAnonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

def checkerFuel : UInt64 := 4096
def checkerMethods : Methods .anon := methodsN checkerFuel.toNat

def checkerInitial : TcState .anon :=
  { TcState.ofEnvAnon recursorIngressAfter with
    recFuel := checkerFuel
    fuelBudget := checkerFuel }

private theorem checkerFamilyBlockLoadedNative :
    checkerInitial.env.getBlock? familyBlockId = some familyMembers := by
  native_decide

theorem checkerFamilyBlockLoaded :
    checkerInitial.env.getBlock? familyBlockId = some familyMembers :=
  checkerFamilyBlockLoadedNative

private theorem checkerRecursorBlockLoadedNative :
    checkerInitial.env.getBlock? recursorBlockId = some recursorMembers := by
  native_decide

theorem checkerRecursorBlockLoaded :
    checkerInitial.env.getBlock? recursorBlockId = some recursorMembers :=
  checkerRecursorBlockLoadedNative

/-! ## Mutual family and constructor block -/

def familyKernelOutcome :=
  (RecM.checkInductiveBlock familyBlockId familyMembers).run checkerMethods
    checkerInitial

def familyKernelAfter : TcState .anon :=
  match familyKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyKernelSucceeded : Bool :=
  match familyKernelOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem familyKernelSucceededNative :
    familyKernelSucceeded = true := by
  native_decide

theorem familyKernelSucceeded_eq : familyKernelSucceeded = true :=
  familyKernelSucceededNative

theorem familyKernelRun :
    (RecM.checkInductiveBlock familyBlockId familyMembers).run checkerMethods
      checkerInitial = .ok () familyKernelAfter := by
  have success := familyKernelSucceeded_eq
  unfold familyKernelSucceeded at success
  unfold familyKernelAfter
  generalize houtcome : familyKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyKernelOutcome]

private theorem generatedRecursorInventoryNative :
    ∃ generated,
      familyKernelAfter.env.recursorCache[familyBlockId]? = some generated ∧
        generated.size = 2 ∧
        generated.all (fun recursor =>
          recursor.lvls == 2 && recursor.params == 1 &&
            recursor.motives == 2 && recursor.minors == 5) := by
  native_decide

/-- The one successful mutual-family run constructs a coordinated cache with
one candidate per family and the block-wide motive/minor inventory. -/
theorem generatedRecursorInventory :
    ∃ generated,
      familyKernelAfter.env.recursorCache[familyBlockId]? = some generated ∧
        generated.size = 2 ∧
        generated.all (fun recursor =>
          recursor.lvls == 2 && recursor.params == 1 &&
            recursor.motives == 2 && recursor.minors == 5) :=
  generatedRecursorInventoryNative

/-! ## Separate mutual recursor block -/

def recursorKernelOutcome :=
  (RecM.checkRecursorBlock recursorBlockId recursorMembers).run checkerMethods
    familyKernelAfter

def recursorKernelAfter : TcState .anon :=
  match recursorKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def recursorKernelSucceeded : Bool :=
  match recursorKernelOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem recursorKernelSucceededNative :
    recursorKernelSucceeded = true := by
  native_decide

theorem recursorKernelSucceeded_eq : recursorKernelSucceeded = true :=
  recursorKernelSucceededNative

theorem recursorKernelRun :
    (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
      checkerMethods familyKernelAfter = .ok () recursorKernelAfter := by
  have success := recursorKernelSucceeded_eq
  unfold recursorKernelSucceeded at success
  unfold recursorKernelAfter
  generalize houtcome : recursorKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [recursorKernelOutcome]

private theorem completedRecursorInventoryNative :
    ∃ generated,
      recursorKernelAfter.env.recursorCache[familyBlockId]? = some generated ∧
        generated.size = 2 ∧
        generated.foldl (init := 0)
          (fun count recursor => count + recursor.rules.size) = 5 := by
  native_decide

/-- Recursor checking commits the five source-ordered equations across the
two cached recursors only after both stored recursor members compare
successfully. -/
theorem completedRecursorInventory :
    ∃ generated,
      recursorKernelAfter.env.recursorCache[familyBlockId]? = some generated ∧
        generated.size = 2 ∧
        generated.foldl (init := 0)
          (fun count recursor => count + recursor.rules.size) = 5 :=
  completedRecursorInventoryNative

/-- Premise-free operational checkpoint for the first physical mutual slice. -/
structure EndToEndExecution : Prop where
  compiler : familyAuxCompileOutcome = .ok familyAuxCompiled
  familyIngress : familyIngressOutcome =
    .ok familyIngressResult familyIngressAfter
  recursorIngress : recursorIngressOutcome =
    .ok recursorIngressResult recursorIngressAfter
  familyKernel :
    (RecM.checkInductiveBlock familyBlockId familyMembers).run checkerMethods
      checkerInitial = .ok () familyKernelAfter
  recursorKernel :
    (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
      checkerMethods familyKernelAfter = .ok () recursorKernelAfter

theorem endToEndExecution : EndToEndExecution where
  compiler := familyAuxCompileRun
  familyIngress := familyIngressRun
  recursorIngress := recursorIngressRun
  familyKernel := familyKernelRun
  recursorKernel := recursorKernelRun

end Ix.Tc.MutualTreeFixture
