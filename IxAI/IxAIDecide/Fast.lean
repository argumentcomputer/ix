import IxAICore.Chain

/-!
# Faster evaluation of the core's schedule and training

`IxAICore.shuffle` swaps list positions with `setAt`, so one shuffle of `n` indices costs `n²`
steps, and `Config.schedule` shuffles the training indices once per epoch. `shuffleArr` makes the
same swaps in an array (`shuffleArr_eq`), and `scheduleArr` and `trainArr` are the core's
`Config.schedule` and `train` with that shuffle.

The `@[csimp]` theorems below make compiled code and the interpreter run `scheduleArr` and
`trainArr` wherever code compiled after this module calls `Config.schedule` or `train`. Every
statement still names the core's definitions, and the kernel still reduces those, so nothing
certified changes. The array shuffle and its proof are the ones in `IxAIData/Scorer.lean`,
repeated here so the decision library does not depend on the premise-selection library.
-/

namespace IxAIDecide

open IxAICore

theorem setAt_eq_set {α : Type} (l : List α) (i : Nat) (v : α) : setAt l i v = l.set i v := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons a as ih => cases i with
    | zero => rfl
    | succ i => simp [setAt, ih]

/-- `shuffleAux` on an array: the same swaps, each in place. -/
def shuffleArrAux {α : Type} [Inhabited α] : Nat → Array α → Rng → Array α × Rng
  | 0, a, r => (a, r)
  | i + 1, a, r =>
    let (j, r) := r.below (i + 2)
    let x := a[i + 1]?.getD default
    let y := a[j]?.getD default
    shuffleArrAux i ((a.setIfInBounds (i + 1) y).setIfInBounds j x) r

theorem shuffleArrAux_eq {α : Type} [Inhabited α] (i : Nat) :
    ∀ (a : Array α) (r : Rng),
      shuffleAux i a.toList r = ((shuffleArrAux i a r).1.toList, (shuffleArrAux i a r).2) := by
  induction i with
  | zero => intro a r; rfl
  | succ i ih =>
    intro a r
    simp only [shuffleArrAux, shuffleAux]
    generalize r.below (i + 2) = p
    obtain ⟨j, r'⟩ := p
    have key : setAt (setAt a.toList (i + 1) ((List.drop j a.toList).headD default)) j
        ((List.drop (i + 1) a.toList).headD default) =
        ((a.setIfInBounds (i + 1) (a[j]?.getD default)).setIfInBounds j
          (a[i + 1]?.getD default)).toList := by
      simp [setAt_eq_set, List.head?_drop, Array.toList_setIfInBounds, List.headD_eq_head?_getD]
    simp only [key, ih]

/-- `shuffle` through an array. -/
def shuffleArr {α : Type} [Inhabited α] (l : List α) (r : Rng) : List α × Rng :=
  let (a, r) := shuffleArrAux (l.length - 1) l.toArray r
  (a.toList, r)

theorem shuffleArr_eq {α : Type} [Inhabited α] (l : List α) (r : Rng) :
    shuffleArr l r = shuffle l r := by
  have h := shuffleArrAux_eq (l.length - 1) l.toArray r
  simp only [shuffleArr, shuffle, h]

/-- `Config.schedule.go` with the array shuffle. -/
def scheduleArrGo (c : Config) : Nat → Rng → List (List Nat)
  | 0, _ => []
  | e + 1, r =>
    let (perm, r) := shuffleArr (List.range c.trainSize) r
    chunk c.batch perm c.trainSize ++ scheduleArrGo c e r

def scheduleArr (c : Config) : List (List Nat) := scheduleArrGo c c.epochs (Rng.seeded (c.seed + 7))

theorem scheduleArrGo_eq (c : Config) :
    ∀ (e : Nat) (r : Rng), scheduleArrGo c e r = Config.schedule.go c e r
  | 0, r => by rw [schedule_go_zero]; rfl
  | e + 1, r => by
    rw [schedule_go_succ, ← scheduleArrGo_eq c e, ← shuffleArr_eq]
    rfl

@[csimp] theorem schedule_eq_scheduleArr : @Config.schedule = @scheduleArr := by
  funext c
  rw [schedule_eq_go, scheduleArr, scheduleArrGo_eq]

/-- `train` with the array shuffle. -/
def trainArr {σ : Type} [Inhabited σ] (s : Spec σ) (c : Config) : Model :=
  let examples := (c.data s).map s.example
  (scheduleArr c).foldl (c.stepFn s examples) (c.init s)

@[csimp] theorem train_eq_trainArr : @train = @trainArr := by
  funext σ _ s c
  simp only [train, trainArr, ← schedule_eq_scheduleArr]

end IxAIDecide
