/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Expr
import Ix.Kernel.Verify.Consistency.Validation
import Ix.Theory.Certified.Ordinary.RecursorStage
import Ix.Certified.Ixon

/-!
# Singleton inductive shapes read from kernel declarations

A singleton block is one non-indexed family with its constructors, checked
by production as one inductive block, and its canonical recursor stored as a
separate one-member block. The certified `Ordinary.Shape` witness is
determined by the stored declarations as follows.

* `Shape.universes`, `Shape.parameters.length`: the family's `lvls` and
  `params` metadata.
* `Shape.parameters`, `Shape.level`: the outermost `params` binder domains
  and the final sort of the stored family type, read by `readExpr?`.
* `Shape.indices`, every `Constructor.indices`, every
  `RecursiveField.indices`: empty.
* `Constructor.fields`, `Constructor.recursive`: the binder domains of the
  stored constructor type after its parameter prefix, split into the ordinary
  prefix and the family-valued suffix; the `j`th recursive domain is the stored
  domain with the `j` earlier recursive binders removed.
* `ElimMode`: the difference between the recursor's and the family's universe
  arities.
* binder conditions: annotations of the raw readings; the retained inference
  fixes them, and `annotateNever` is exact for binder-free domains.

Every reading is validated by a decidable comparison of the stored block with
the certified `Shape.source` and `Shape.recursorSource` syntax.
-/

namespace Ix.Kernel.Consistency.Inductive

open Theory Theory.Model Theory.Certified Theory.Certified.Ordinary Theory.Inductive

universe u
variable {β : Type u}

/-! ### Erased singleton shapes -/

/-- Constructor field telescopes with every binder condition erased. -/
structure ErasedConstructor (β : Type u) where
  fields : List (VExpr β)
  recursive : List (List (VExpr β))
deriving DecidableEq

structure ErasedShape (β : Type u) where
  universes : Nat
  parameters : List (VExpr β)
  level : VLevel
  constructors : List (ErasedConstructor β)
deriving DecidableEq

def familyHead (source : β) (universes : Nat) : VExpr β :=
  .const (.member source 0) (VLevel.params universes)

def familyApp (source : β) (universes nparams offset : Nat) : VExpr β :=
  (familyHead source universes).appN (VExpr.bvarRevRange offset nparams)

def recursiveType (source : β) (universes nparams ordinary : Nat)
    (domains : List (VExpr β)) : VExpr β :=
  VExpr.forallN domains (familyApp source universes nparams (ordinary + domains.length))

def recursiveTelescope (source : β) (universes nparams ordinary : Nat) :
    List (List (VExpr β)) → Nat → List (VExpr β)
  | [], _ => []
  | domains :: rest, offset =>
      (recursiveType source universes nparams ordinary domains).liftN offset ::
        recursiveTelescope source universes nparams ordinary rest (offset + 1)

def ErasedConstructor.type (ctor : ErasedConstructor β) (source : β) (universes : Nat)
    (parameters : List (VExpr β)) : VExpr β :=
  VExpr.forallN parameters <|
    VExpr.forallN ctor.fields <|
      VExpr.forallN (recursiveTelescope source universes parameters.length ctor.fields.length
          ctor.recursive 0) <|
        familyApp source universes parameters.length (ctor.fields.length + ctor.recursive.length)

def ErasedShape.type (shape : ErasedShape β) : VExpr β :=
  VExpr.forallN shape.parameters (.sort shape.level)

/-! ### Erasure of the certified shape -/

def eraseConstructor (ctor : Constructor β) : ErasedConstructor β :=
  ⟨ctor.fields.map AExpr.erase, ctor.recursive.map fun field => field.domains.map AExpr.erase⟩

def eraseShape (shape : Shape β) : ErasedShape β :=
  ⟨shape.universes, shape.parameters.map AExpr.erase, shape.level,
    shape.constructors.map eraseConstructor⟩

/-- No indices anywhere: the family, every constructor result, and every
recursive field target the bare parameter instance. -/
def SingletonShape (shape : Shape β) : Prop :=
  shape.indices = [] ∧ ∀ ctor ∈ shape.constructors,
    ctor.indices = [] ∧ ∀ field ∈ ctor.recursive, field.indices = []

instance (shape : Shape β) : Decidable (SingletonShape shape) := by
  unfold SingletonShape
  infer_instance

theorem erase_familyApp (shape : Shape β) (source : β) (offset : Nat) :
    (shape.familyApp source offset []).erase =
      familyApp source shape.universes shape.parameters.length offset := by
  simp [Shape.familyApp, familyApp, familyHead, AExpr.erase_appN, AExpr.erase]

theorem erase_recursiveFieldType {shape : Shape β} {field : RecursiveField β} (source : β)
    (ordinary : Nat) (hf : field.indices = []) :
    (field.type shape source ordinary).erase =
      recursiveType source shape.universes shape.parameters.length ordinary
        (field.domains.map AExpr.erase) := by
  simp [RecursiveField.type, recursiveType, hf, erase_familyApp]

theorem erase_recursiveTypesFrom {shape : Shape β} (source : β) (ordinary : Nat)
    (fields : List (RecursiveField β)) (offset : Nat)
    (hf : ∀ field ∈ fields, field.indices = []) :
    (Ordinary.recursiveTypesFrom shape source ordinary fields offset).map AExpr.erase =
      recursiveTelescope source shape.universes shape.parameters.length ordinary
        (fields.map fun field => field.domains.map AExpr.erase) offset := by
  induction fields generalizing offset with
  | nil => rfl
  | cons field fields ih =>
      have head := erase_recursiveFieldType (shape := shape) (field := field) source ordinary
        (hf field (List.mem_cons_self ..))
      have tail := ih (offset + 1) (fun f hm => hf f (List.mem_cons_of_mem field hm))
      simp only [Ordinary.recursiveTypesFrom, List.zipIdx_cons, List.map_cons, List.map_map,
        Function.comp_def, AExpr.erase_liftN, head, recursiveTelescope] at tail ⊢
      rw [tail]

theorem erase_constructorType {shape : Shape β} {ctor : Constructor β} (source : β)
    (hc : ctor.indices = []) (hr : ∀ field ∈ ctor.recursive, field.indices = []) :
    (ctor.type shape source).erase =
      (eraseConstructor ctor).type source shape.universes (eraseShape shape).parameters := by
  simp only [Constructor.type, ErasedConstructor.type, eraseConstructor,
    eraseShape, Constructor.recursiveTypes, AExpr.erase_forallN, List.length_map]
  rw [erase_recursiveTypesFrom source ctor.fields.length ctor.recursive 0 hr]
  simp [hc, erase_familyApp]

theorem erase_shapeType {shape : Shape β} (hs : shape.indices = []) :
    shape.type.erase = (eraseShape shape).type := by
  simp [Shape.type, ErasedShape.type, eraseShape, hs, AExpr.erase]

/-! ### Reading singleton shapes from erased declaration types -/

/-- Peel exactly `n` outermost dependent function binders. -/
def peelForalls? : Nat → VExpr β → Option (List (VExpr β) × VExpr β)
  | 0, e => some ([], e)
  | n + 1, .forallE A B =>
      match peelForalls? n B with
      | some (domains, body) => some (A :: domains, body)
      | none => none
  | _ + 1, _ => none

theorem peelForalls?_forallN {n : Nat} : ∀ {e : VExpr β} {domains : List (VExpr β)} {body : VExpr β},
    peelForalls? n e = some (domains, body) → e = VExpr.forallN domains body ∧ domains.length = n := by
  induction n with
  | zero =>
      intro e domains body h
      simp only [peelForalls?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro e domains body h
      cases e with
      | forallE A B =>
          simp only [peelForalls?] at h
          split at h
          next rest body' hrest =>
            cases h
            obtain ⟨rfl, hlen⟩ := ih hrest
            exact ⟨rfl, by simp [hlen]⟩
          next => contradiction
      | _ => simp [peelForalls?] at h

/-- Peel every outermost binder. -/
def peelAllForalls : VExpr β → List (VExpr β) × VExpr β
  | .forallE A B =>
      match peelAllForalls B with
      | (domains, body) => (A :: domains, body)
  | e => ([], e)

/-- Remove `n` free variables at cutoff `k` from a term with no free
occurrence in that range. -/
def lowerN? (n : Nat) : VExpr β → (k : Nat := 0) → Option (VExpr β)
  | .bvar i, k => if i < k then some (.bvar i) else if n + k ≤ i then some (.bvar (i - n)) else none
  | .sort u, _ => some (.sort u)
  | .const r us, _ => some (.const r us)
  | .app f a, k => do return .app (← lowerN? n f k) (← lowerN? n a k)
  | .lam A b, k => do return .lam (← lowerN? n A k) (← lowerN? n b (k + 1))
  | .forallE A b, k => do return .forallE (← lowerN? n A k) (← lowerN? n b (k + 1))
  | .proj r i e, k => do return .proj r i (← lowerN? n e k)
  | .natLit v, _ => some (.natLit v)

/-- The domains of a recursive field whose lowered type targets the family at
the parameter instance, after `ordinary` earlier fields. -/
def recursiveDomains? [DecidableEq β] (source : β) (universes nparams ordinary : Nat)
    (domain : VExpr β) : Option (List (VExpr β)) :=
  match peelAllForalls domain with
  | (domains, body) =>
      if body = familyApp source universes nparams (ordinary + domains.length) then some domains
      else none

def collectRecursive [DecidableEq β] (source : β) (universes nparams ordinary : Nat) :
    List (VExpr β) → Nat → Option (List (List (VExpr β)))
  | [], _ => some []
  | domain :: rest, previous => do
      let lowered ← lowerN? previous domain
      let domains ← recursiveDomains? source universes nparams ordinary lowered
      let tail ← collectRecursive source universes nparams ordinary rest (previous + 1)
      return domains :: tail

/-- Split field domains into the ordinary prefix and the recursive suffix. -/
def splitFields [DecidableEq β] (source : β) (universes nparams : Nat) :
    List (VExpr β) → List (VExpr β) → Option (ErasedConstructor β)
  | [], fields => some ⟨fields, []⟩
  | domain :: rest, fields =>
      match recursiveDomains? source universes nparams fields.length domain with
      | some domains => do
          let tail ← collectRecursive source universes nparams fields.length rest 1
          return ⟨fields, domains :: tail⟩
      | none => splitFields source universes nparams rest (fields ++ [domain])

/-- Whether an erased term mentions the family being declared. -/
def mentionsFamily [DecidableEq β] (source : β) (e : VExpr β) : Bool :=
  e.mentions (.member source 0)

/-- Read one constructor. The reconstruction is compared with the stored
type, so the split heuristic is not trusted. -/
def constructorShape? [DecidableEq β] (source : β) (universes : Nat)
    (parameters : List (VExpr β)) (type : VExpr β) : Option (ErasedConstructor β) :=
  match peelForalls? parameters.length type with
  | none => none
  | some (ps, rest) =>
      if ps = parameters then
        match splitFields source universes parameters.length (peelAllForalls rest).1 [] with
        | none => none
        | some ctor =>
            if ctor.type source universes parameters = type then
              if ctor.fields.all fun domain => !mentionsFamily source domain then some ctor else none
            else none
      else none

theorem constructorShape?_type [DecidableEq β] {source : β} {universes : Nat}
    {parameters : List (VExpr β)} {type : VExpr β} {ctor : ErasedConstructor β}
    (h : constructorShape? source universes parameters type = some ctor) :
    ctor.type source universes parameters = type ∧
      ∀ domain ∈ ctor.fields, mentionsFamily source domain = false := by
  unfold constructorShape? at h
  split at h
  · contradiction
  · split at h
    · split at h
      · contradiction
      · split at h
        next htype =>
          split at h
          next hfields =>
            cases h
            refine ⟨htype, ?_⟩
            intro domain hd
            have := List.all_eq_true.mp hfields domain hd
            simpa using this
          · contradiction
        · contradiction
    · contradiction

theorem mapM_some {α γ : Type _} {f : α → Option γ} {xs : List α} {ys : List γ}
    (h : xs.mapM f = some ys) :
    ys.length = xs.length ∧ ∀ (i : Nat) (x : α), xs[i]? = some x → ∃ y, ys[i]? = some y ∧ f x = some y := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      simp
  | cons x xs ih =>
      simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨y, hy, tail, htail, rfl⟩ := h
      obtain ⟨hlen, ih⟩ := ih htail
      refine ⟨by simp [hlen], ?_⟩
      intro i x' hx
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨y, rfl, hy⟩
      | succ i =>
          simp only [List.getElem?_cons_succ] at hx ⊢
          exact ih i x' hx

/-- Read the erased singleton shape from the erased family and constructor
types. -/
def erasedShape? [DecidableEq β] (source : β) (universes nparams : Nat)
    (familyType : VExpr β) (constructorTypes : List (VExpr β)) : Option (ErasedShape β) :=
  match peelForalls? nparams familyType with
  | none => none
  | some (parameters, .sort level) =>
      match constructorTypes.mapM (constructorShape? source universes parameters) with
      | none => none
      | some constructors => some ⟨universes, parameters, level, constructors⟩
  | some (_, _) => none

theorem erasedShape?_sound [DecidableEq β] {source : β} {universes nparams : Nat}
    {familyType : VExpr β} {constructorTypes : List (VExpr β)} {shape : ErasedShape β}
    (h : erasedShape? source universes nparams familyType constructorTypes = some shape) :
    shape.universes = universes ∧ shape.parameters.length = nparams ∧
      shape.type = familyType ∧ shape.constructors.length = constructorTypes.length ∧
      ∀ (i : Nat) (type : VExpr β), constructorTypes[i]? = some type →
        ∃ ctor : ErasedConstructor β, shape.constructors[i]? = some ctor ∧
        ctor.type source universes shape.parameters = type ∧
        ∀ domain ∈ ctor.fields, mentionsFamily source domain = false := by
  unfold erasedShape? at h
  split at h
  · contradiction
  next parameters level hpeel =>
    split at h
    · contradiction
    next constructors hmap =>
      cases h
      obtain ⟨hfam, hlen⟩ := peelForalls?_forallN hpeel
      obtain ⟨hclen, hctors⟩ := mapM_some hmap
      refine ⟨rfl, hlen, ?_, hclen, ?_⟩
      · simp [ErasedShape.type, hfam]
      · intro i type ht
        obtain ⟨ctor, hc, hread⟩ := hctors i type ht
        exact ⟨ctor, hc, constructorShape?_type hread⟩
  · contradiction

/-! ### Default annotation -/

/-- The structural annotation whose every binder is never a proposition. It is
exact for binder-free domains; general domains take their conditions from the
retained inference. -/
def annotateNever : VExpr β → AExpr β
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f a => .app (annotateNever f) (annotateNever a)
  | .lam a b => .lam .never (annotateNever a) (annotateNever b)
  | .forallE a b => .forallE .never (annotateNever a) (annotateNever b)
  | .proj r i e => .proj r i (annotateNever e)
  | .natLit v => .natLit v

@[simp] theorem erase_annotateNever (e : VExpr β) : (annotateNever e).erase = e := by
  induction e <;> simp_all [annotateNever, AExpr.erase]

def ErasedConstructor.annotate (ctor : ErasedConstructor β) : Constructor β :=
  ⟨ctor.fields.map annotateNever, ctor.recursive.map fun domains => ⟨domains.map annotateNever, []⟩, []⟩

def ErasedShape.annotate (shape : ErasedShape β) : Shape β :=
  ⟨shape.universes, shape.parameters.map annotateNever, [], shape.level,
    shape.constructors.map ErasedConstructor.annotate⟩

@[simp] theorem eraseConstructor_annotate (ctor : ErasedConstructor β) :
    eraseConstructor ctor.annotate = ctor := by
  cases ctor
  simp [ErasedConstructor.annotate, eraseConstructor, List.map_map, Function.comp_def]

@[simp] theorem eraseShape_annotate (shape : ErasedShape β) : eraseShape shape.annotate = shape := by
  cases shape
  simp [ErasedShape.annotate, eraseShape, List.map_map, Function.comp_def]

theorem annotate_singleton (shape : ErasedShape β) : SingletonShape shape.annotate := by
  refine ⟨rfl, ?_⟩
  intro ctor hc
  obtain ⟨erased, _, rfl⟩ := List.mem_map.mp hc
  refine ⟨rfl, ?_⟩
  intro field hf
  obtain ⟨domains, _, rfl⟩ := List.mem_map.mp hf
  rfl

/-! ### Decidable binder-condition bounds -/

/-- Executable form of `ConditionsScoped`. -/
def conditionsScopedCheck (universes : Nat) : AExpr β → Bool
  | .app fn arg => conditionsScopedCheck universes fn && conditionsScopedCheck universes arg
  | .lam condition domain body | .forallE condition domain body =>
      decide (condition.WF universes) && conditionsScopedCheck universes domain &&
        conditionsScopedCheck universes body
  | .proj _ _ major => conditionsScopedCheck universes major
  | _ => true

theorem conditionsScopedCheck_sound {universes : Nat} :
    ∀ {e : AExpr β}, conditionsScopedCheck universes e = true → ConditionsScoped universes e
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .natLit _, _ => trivial
  | .app fn arg, h => by
      simp only [conditionsScopedCheck, Bool.and_eq_true] at h
      exact ⟨conditionsScopedCheck_sound h.1, conditionsScopedCheck_sound h.2⟩
  | .lam condition domain body, h | .forallE condition domain body, h => by
      simp only [conditionsScopedCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1, conditionsScopedCheck_sound h.1.2, conditionsScopedCheck_sound h.2⟩
  | .proj _ _ major, h => conditionsScopedCheck_sound (e := major) h

/-! ### Certified blocks read from stored kernel declarations -/

/-- The certified constructor read from a stored constructor declaration whose
header agrees with its family. -/
def readCtor? (resolve : Address → Option (ConstRef Address)) (lvls params : UInt64) :
    KConst .anon → Option (Ctor Address)
  | .ctor (isUnsafe := false) (lvls := clvls) (params := cparams) (fields := fields) (ty := ty) .. =>
      if clvls = lvls ∧ cparams = params then
        match readScopedExpr? resolve [] ty with
        | some type => some ⟨lvls.toNat, params.toNat, fields.toNat, type, .safe⟩
        | none => none
      else none
  | _ => none

/-- The certified one-member block of a non-indexed safe family with the given
header, type, and constructor declarations. -/
def familyBlockOf? (resolve : Address → Option (ConstRef Address)) (lvls params : UInt64)
    (ty : KExpr .anon) (ctors : List (KConst .anon)) : Option (Block Address) :=
  match readScopedExpr? resolve [] ty with
  | none => none
  | some type =>
      match ctors.mapM (readCtor? resolve lvls params) with
      | none => none
      | some ctorDecls => some ⟨[.induct lvls.toNat params.toNat 0 type ctorDecls .safe]⟩

/-- The certified one-member block read from a stored non-indexed safe family
and its constructor declarations, in constructor order. -/
def familyBlock? (resolve : Address → Option (ConstRef Address)) :
    KConst .anon → List (KConst .anon) → Option (Block Address)
  | .indc (lvls := lvls) (params := params) (indices := 0) (isUnsafe := false) (ty := ty) .., ctors =>
      familyBlockOf? resolve lvls params ty ctors
  | _, _ => none

/-- The certified rule read from a stored recursor rule. -/
def readRule? (resolve : Address → Option (ConstRef Address)) (rule : Kernel.RecRule .anon) :
    Option (Theory.RecRule Address) :=
  (readScopedExpr? resolve [] rule.rhs).map fun rhs => ⟨rule.fields.toNat, rhs⟩

/-- The certified one-member block of a safe recursor with the given header,
type, and rules. -/
def recursorBlockOf? (resolve : Address → Option (ConstRef Address)) (k : Bool)
    (lvls params indices motives minors : UInt64) (ty : KExpr .anon)
    (rules : List (Kernel.RecRule .anon)) : Option (Block Address) :=
  match readScopedExpr? resolve [] ty with
  | none => none
  | some type =>
      match rules.mapM (readRule? resolve) with
      | none => none
      | some ruleDecls =>
          some ⟨[.recursor lvls.toNat params.toNat indices.toNat motives.toNat minors.toNat
            type ruleDecls k .safe]⟩

/-- The certified one-member block read from a stored safe recursor. -/
def recursorBlock? (resolve : Address → Option (ConstRef Address)) :
    KConst .anon → Option (Block Address)
  | .recr (k := k) (isUnsafe := false) (lvls := lvls) (params := params) (indices := indices)
      (motives := motives) (minors := minors) (ty := ty) (rules := rules) .. =>
      recursorBlockOf? resolve k lvls params indices motives minors ty rules.toList
  | _ => none

/-- The elimination mode determined by the two stored universe arities. -/
def modeOf (familyUniverses recursorUniverses : UInt64) : Option ElimMode :=
  if recursorUniverses = familyUniverses then some .small
  else if recursorUniverses.toNat = familyUniverses.toNat + 1 then some .large
  else none

theorem modeOf_recUvars {familyUniverses recursorUniverses : UInt64} {mode : ElimMode}
    (h : modeOf familyUniverses recursorUniverses = some mode) :
    recursorUniverses.toNat = mode.recUvars familyUniverses.toNat := by
  unfold modeOf at h
  split at h
  · cases h; simp_all [ElimMode.recUvars]
  · split at h
    · cases h; simp_all [ElimMode.recUvars]
    · contradiction

/-- The stored recursor is the certified canonical recursor of the shape. A
`k` flag is accepted only for a supported singleton proposition. -/
def recursorSourceCheck (resolve : Address → Option (ConstRef Address)) (shape : Shape Address)
    (source recursor : Address) (mode : ElimMode) (recr : KConst .anon) : Bool :=
  match recr with
  | .recr (k := k) .. =>
      decide (recursorBlock? resolve recr = some ⟨[shape.recursorSource source recursor mode k]⟩) &&
        (!k || decide shape.SupportsK)
  | _ => false

theorem recursorSourceCheck_sound {resolve : Address → Option (ConstRef Address)}
    {shape : Shape Address} {source recursor : Address} {mode : ElimMode} {recr : KConst .anon}
    {store : Store Address} (check : recursorSourceCheck resolve shape source recursor mode recr = true)
    (stored : store.blocks recursor = recursorBlock? resolve recr) :
    shape.RecursorSourceMatches store source recursor mode := by
  cases recr
  case recr name levelParams k isUnsafe lvls params indices motives minors block memberIdx ty rules leanAll =>
      simp only [recursorSourceCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at check
      obtain ⟨hblock, hk⟩ := check
      unfold Shape.RecursorSourceMatches
      rw [stored, hblock]
      cases k with
      | false => exact Or.inl rfl
      | true =>
          rcases hk with hk | hk
          · simp at hk
          · exact Or.inr ⟨hk, rfl⟩
  all_goals simp [recursorSourceCheck] at check

/-- The complete decidable witness check for one singleton block: the family
block reads to the certified source of `shape`, the recursor block reads to the
certified canonical recursor, the shape has no indices, and every binder
condition is bounded by the family's universe arity. -/
def singletonWitnessCheck (resolve : Address → Option (ConstRef Address)) (source recursor : Address)
    (family : KConst .anon) (ctors : List (KConst .anon)) (recr : KConst .anon)
    (shape : Shape Address) (mode : ElimMode) : Bool :=
  decide (familyBlock? resolve family ctors = some ⟨[shape.source source]⟩) &&
    recursorSourceCheck resolve shape source recursor mode recr &&
    decide (SingletonShape shape) &&
    decide (modeOf family.lvls recr.lvls = some mode) &&
    conditionsScopedCheck shape.universes shape.type &&
    shape.constructors.all (fun ctor => conditionsScopedCheck shape.universes (ctor.type shape source)) &&
    shape.constructors.all (fun ctor =>
      ctor.fields.all (fun A => decide (ConstRef.member source 0 ∉ A.references)) &&
        ctor.recursive.all fun field =>
          field.domains.all fun A => decide (ConstRef.member source 0 ∉ A.references)) &&
    conditionsScopedCheck (mode.recUvars shape.universes) (shape.recursorType source mode) &&
    shape.constructors.zipIdx.all fun (ctor, i) =>
      conditionsScopedCheck (mode.recUvars shape.universes) (shape.ruleRhs source recursor mode i ctor)

theorem singletonWitnessCheck_sound {resolve : Address → Option (ConstRef Address)}
    {source recursor : Address} {family : KConst .anon} {ctors : List (KConst .anon)}
    {recr : KConst .anon} {shape : Shape Address} {mode : ElimMode}
    (check : singletonWitnessCheck resolve source recursor family ctors recr shape mode = true) :
    familyBlock? resolve family ctors = some ⟨[shape.source source]⟩ ∧
      recursorSourceCheck resolve shape source recursor mode recr = true ∧
      SingletonShape shape ∧ modeOf family.lvls recr.lvls = some mode ∧
      ConditionsScoped shape.universes shape.type ∧
      (∀ ctor ∈ shape.constructors, ConditionsScoped shape.universes (ctor.type shape source)) ∧
      (∀ ctor ∈ shape.constructors,
        (∀ A ∈ ctor.fields, ConstRef.member source 0 ∉ A.references) ∧
        ∀ field ∈ ctor.recursive, ∀ A ∈ field.domains, ConstRef.member source 0 ∉ A.references) ∧
      ConditionsScoped (mode.recUvars shape.universes) (shape.recursorType source mode) ∧
      ∀ (i : Nat) (ctor : Constructor Address), shape.constructors[i]? = some ctor →
        ConditionsScoped (mode.recUvars shape.universes) (shape.ruleRhs source recursor mode i ctor) := by
  simp only [singletonWitnessCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at check
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hfam, hrec⟩, hsingle⟩, hmode⟩, htype⟩, hctors⟩, hmention⟩, hrecType⟩, hrules⟩ := check
  refine ⟨hfam, hrec, hsingle, hmode, conditionsScopedCheck_sound htype,
    fun ctor hc => conditionsScopedCheck_sound (hctors ctor hc), ?_, conditionsScopedCheck_sound hrecType, ?_⟩
  · intro ctor hc
    obtain ⟨hfields, hrecursive⟩ := hmention ctor hc
    exact ⟨hfields, hrecursive⟩
  · intro i ctor hc
    exact conditionsScopedCheck_sound (hrules (ctor, i) (List.mk_mem_zipIdx_iff_getElem?.mpr hc))

/-- Reading agreement between a stored constructor declaration and the
certified constructor it reads to. -/
theorem readCtor?_source {resolve : Address → Option (ConstRef Address)} {lvls params : UInt64}
    {decl : KConst .anon} {shape : Shape Address} {source : Address} {ctor : Constructor Address}
    (h : readCtor? resolve lvls params decl = some (ctor.source shape source)) :
    ∃ (cty : KExpr .anon) (fields : UInt64) (induct : KId .anon) (cidx : UInt64)
      (cname : Mode.anon.F Name) (clevelParams : Mode.anon.F (Array Name)),
      decl = KConst.ctor cname clevelParams false lvls induct cidx params fields cty ∧
      fields.toNat = ctor.fields.length + ctor.recursive.length ∧
      readScopedExpr? resolve [] cty = some (ctor.type shape source).erase := by
  unfold readCtor? at h
  split at h
  next cname clevelParams clvls induct cidx cparams fields cty =>
    split at h
    next hheader =>
      split at h
      next ctype hctype =>
        simp only [Constructor.source, Option.some.injEq, Ctor.mk.injEq] at h
        obtain ⟨_, _, hfields, hctype', _⟩ := h
        exact ⟨cty, fields, induct, cidx, cname, clevelParams, by rw [hheader.1, hheader.2],
          hfields, by rw [hctype, hctype']⟩
      · contradiction
    · contradiction
  · contradiction

theorem familyBlockOf?_family {resolve : Address → Option (ConstRef Address)} {lvls params : UInt64}
    {ty : KExpr .anon} {ctors : List (KConst .anon)} {shape : Shape Address} {source : Address}
    (h : familyBlockOf? resolve lvls params ty ctors = some ⟨[shape.source source]⟩) :
    lvls.toNat = shape.universes ∧ params.toNat = shape.parameters.length ∧
      shape.indices.length = 0 ∧
      readScopedExpr? resolve [] ty = some shape.type.erase ∧
      ctors.length = shape.constructors.length ∧
      ∀ (i : Nat) (ctor : Constructor Address), shape.constructors[i]? = some ctor →
        ∃ decl : KConst .anon, ctors[i]? = some decl ∧
          readCtor? resolve lvls params decl = some (ctor.source shape source) := by
  unfold familyBlockOf? at h
  cases htype : readScopedExpr? resolve [] ty with
  | none => simp [htype] at h
  | some type =>
    cases hctors : ctors.mapM (readCtor? resolve lvls params) with
    | none => simp [htype, hctors] at h
    | some ctorDecls =>
      simp only [htype, hctors, Option.some.injEq, Block.mk.injEq, List.cons.injEq, and_true,
        Shape.source, Const.induct.injEq] at h
      obtain ⟨hlvls, hparams, hindices, htyeq, hlist⟩ := h
      obtain ⟨hclen, hread⟩ := mapM_some hctors
      refine ⟨hlvls, hparams, hindices.symm, by rw [htyeq], ?_, ?_⟩
      · rw [← hclen, hlist, List.length_map]
      · intro i ctor hc
        have hdecl : ctorDecls[i]? = some (ctor.source shape source) := by
          rw [hlist, List.getElem?_map, hc]
          rfl
        cases hi : ctors[i]? with
        | none =>
            have hlt : i < ctorDecls.length := (List.getElem?_eq_some_iff.mp hdecl).1
            rw [hclen] at hlt
            rw [List.getElem?_eq_getElem hlt] at hi
            cases hi
        | some decl =>
            obtain ⟨read, hread', hdecl'⟩ := hread i decl hi
            rw [hdecl] at hread'
            cases hread'
            exact ⟨decl, rfl, hdecl'⟩

/-- Reading agreement between the stored family declaration and the shape. -/
theorem familyBlock?_family {resolve : Address → Option (ConstRef Address)}
    {family : KConst .anon} {ctors : List (KConst .anon)} {shape : Shape Address} {source : Address}
    (h : familyBlock? resolve family ctors = some ⟨[shape.source source]⟩) :
    ∃ (lvls params : UInt64) (ty : KExpr .anon) (ctorIds : Array (KId .anon)) (block : KId .anon)
      (memberIdx : UInt64) (leanAll : Mode.anon.F (Array (KId .anon))) (name : Mode.anon.F Name)
      (levelParams : Mode.anon.F (Array Name)),
      family = KConst.indc name levelParams lvls params 0 false block memberIdx ty ctorIds leanAll ∧
      lvls.toNat = shape.universes ∧ params.toNat = shape.parameters.length ∧
      shape.indices.length = 0 ∧
      readScopedExpr? resolve [] ty = some shape.type.erase ∧
      ctors.length = shape.constructors.length ∧
      ∀ (i : Nat) (ctor : Constructor Address), shape.constructors[i]? = some ctor →
        ∃ decl : KConst .anon, ctors[i]? = some decl ∧
          readCtor? resolve lvls params decl = some (ctor.source shape source) := by
  unfold familyBlock? at h
  split at h
  next name levelParams lvls params block memberIdx ty ctorIds leanAll =>
    obtain ⟨hlvls, hparams, hindices, htype, hlen, hctors⟩ := familyBlockOf?_family h
    exact ⟨lvls, params, ty, ctorIds, block, memberIdx, leanAll, name, levelParams, rfl, hlvls,
      hparams, hindices, htype, hlen, hctors⟩
  · contradiction

theorem recursorBlockOf?_recursor {resolve : Address → Option (ConstRef Address)} {k : Bool}
    {lvls params indices motives minors : UInt64} {ty : KExpr .anon}
    {rules : List (Kernel.RecRule .anon)} {block : Block Address}
    (h : recursorBlockOf? resolve k lvls params indices motives minors ty rules = some block) :
    ∃ type ruleDecls, readScopedExpr? resolve [] ty = some type ∧
      rules.mapM (readRule? resolve) = some ruleDecls ∧
      block = ⟨[.recursor lvls.toNat params.toNat indices.toNat motives.toNat minors.toNat
        type ruleDecls k .safe]⟩ := by
  unfold recursorBlockOf? at h
  cases htype : readScopedExpr? resolve [] ty with
  | none => simp [htype] at h
  | some type =>
    cases hrules : rules.mapM (readRule? resolve) with
    | none => simp [htype, hrules] at h
    | some ruleDecls =>
      simp only [htype, hrules, Option.some.injEq] at h
      exact ⟨type, ruleDecls, rfl, rfl, h.symm⟩

end Ix.Kernel.Consistency.Inductive
