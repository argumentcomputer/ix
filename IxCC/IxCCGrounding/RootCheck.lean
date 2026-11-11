import IxCCGrounding.Syntax

/-!
# The root's facts and their check (`IxCCGrounding.RootCheck`)

Denotes-free. What the root theorem (`IxCCGrounding.Root`) asks of the root, its arguments and
the observed result, each a Boolean check with a proved soundness lemma, run by `tests-grounding`:

| Check | What it decides |
| --- | --- |
| `rootParts` (`rootMem`, `rootOk`, `rootStored`, `rootEnums`) | the root is in `Sl`, `Ok` at no levels, stored without level parameters at the first-order type `args → res`; its enumerations stored as `EnumStored` says (`RootFacts`) |
| `foArgsB` | the arguments are first-order values with their kernel terms; an enumeration argument is its type's listed constructor (`FoArgs`) |
| `resultTagB` | every member of `Sl` whose readback tag is the observed one and whose kernel entry is a field-less constructor has the named constructor's key (`ResultTag`) |
| `boolListedB` | the pinned `Bool`'s listed constructor `1` is the pinned `Bool.true` (`BoolListed`) |

Why each is needed (each fails a counterexample without it): an enumeration argument outside
`Sl` has an unconstrained key, so SrcEval (which selects by the declaration) and the kernel (which
reads the key) can disagree; a result constructor is read back by its declared index, and a
member of `Sl` declared as something else reads back as tag `0`, a parameterised field-less
constructor at the same index (`Option.none`) is a different set, so the observation would name
the wrong constructor; and nothing else ties the pinned `Bool`'s constructor `1` to the kernel's
`Bool.true`.
-/

namespace IxCC.Grounding

open Ix.Kernel
open IxCC.Src (Value Slot Term CId Program Levels)

/-! ## First-order types, values and observations -/

/-- A first-order type of the fragment: `Nat`, or a field-less enumeration without parameters,
indices or level parameters (`Bool` among them). -/
inductive FoTy where
  | nat
  | enum (ind : CId)
  deriving DecidableEq

def FoTy.kexpr (κ : CId → KKey) : FoTy → KExpr
  | .nat => .const natName []
  | .enum D => .const (κ D) []

/-- A first-order argument and its kernel term: a literal, or an enumeration's listed
constructor (the listed one: a constructor of the enumeration outside its list is not in `Sl`, and
its key is unconstrained). -/
inductive FoVal (p : Program) (κ : CId → KKey) : FoTy → Value → KExpr → Prop
  | nat (n : Nat) : FoVal p κ .nat (.lit n) (litE n)
  | enum {D c : CId} {i : Nat} {safe : Bool} {cs : List CId} {ty : Term} :
      p.decl? D = some (.induct safe 0 0 0 ty cs) → cs[i]? = some c →
      FoVal p κ (.enum D) (.con c [] [] []) (.const (κ c) [])

inductive FoArgs (p : Program) (κ : CId → KKey) : List FoTy → List Value → List KExpr → Prop
  | nil : FoArgs p κ [] [] []
  | cons {t : FoTy} {ts : List FoTy} {x : Value} {xs : List Value} {e : KExpr} {es : List KExpr} :
      FoVal p κ t x e → FoArgs p κ ts xs es → FoArgs p κ (t :: ts) (x :: xs) (e :: es)

/-- **What an observation names** at a first-order type: a literal, or the result type's listed
constructor at the observed index. -/
inductive FoObs (p : Program) (κ : CId → KKey) : FoTy → IxCC.Sem.Obs → KExpr → Prop
  | nat (w : Nat) : FoObs p κ .nat (.nat w) (litE w)
  | enum {D c : CId} {i : Nat} {safe : Bool} {cs : List CId} {ty : Term} :
      p.decl? D = some (.induct safe 0 0 0 ty cs) → cs[i]? = some c →
      FoObs p κ (.enum D) (.ctor i []) (.const (κ c) [])

/-- An enumeration of the fragment, stored as its constructors' types say. -/
def EnumStored (p : Program) (env : KEnv) (κ : CId → KKey) (S : CId → Prop) (D : CId) : Prop :=
  ∃ (safe : Bool) (ty : Term) (cs : List CId),
    p.decl? D = some (.induct safe 0 0 0 ty cs) ∧
    (∃ ci : ConstantInfo .anon, env.find? (κ D) = some ci ∧ ci.toConstantVal.levelParams = []) ∧
    (∀ i c, cs[i]? = some c → S c ∧
      (∃ (safe' : Bool) (ty' : Term), p.decl? c = some (.ctor safe' 0 D i 0 0 ty')) ∧
      ∃ cv : ConstantVal .anon, env.find? (κ c) = some (.ctorInfo cv 0 0) ∧
        cv.levelParams = [] ∧ cv.type = .const (κ D) []) ∧
    (∀ c, S c → ∀ (safe' : Bool) (lv i np nf : Nat) (ty' : Term),
      p.decl? c = some (.ctor safe' lv D i np nf ty') → cs[i]? = some c)

/-- The tag readback gives a constructor value of `c` (`Src.readback`'s: the declared index, `0`
for a constant not declared as a constructor). -/
def readTag (p : Program) (c : CId) : Nat :=
  match p.decl? c with
  | some (.ctor _ _ _ cidx _ _ _) => cidx
  | _ => 0

/-- **The observed tag names one constructor**: every member of `S` that reads back with the
observed tag and whose kernel entry is a field-less constructor (any parameter count) has the
named constructor's key. Checked per observed tag after the run. -/
def ResultTag (p : Program) (env : KEnv) (κ : CId → KKey) (S : CId → Prop) :
    FoTy → IxCC.Sem.Obs → Prop
  | .nat, _ => True
  | .enum D, .ctor i [] =>
    ∀ (safe : Bool) (ty : Term) (cs : List CId) (c' : CId),
      p.decl? D = some (.induct safe 0 0 0 ty cs) → cs[i]? = some c' →
      ∀ c, S c → readTag p c = i → (∃ (cv : ConstantVal .anon) (np : Nat),
        env.find? (κ c) = some (.ctorInfo cv np 0)) → κ c = κ c'
  | .enum _, _ => True

/-- **The root's checked facts**: in `S`, `Ok` at no levels, stored without level parameters at
the first-order type `args → res` (each binder never a proposition), its enumerations stored. -/
structure RootFacts (p : Program) (env : KEnv) (κ : CId → KKey) (ann : IxCC.Src.Relevance.Ann)
    (S : CId → Prop) (root : CId) (args : List FoTy) (res : FoTy) : Prop where
  mem : S root
  ok : Ok p ann root []
  stored : ∃ ci : ConstantInfo .anon, env.find? (κ root) = some ci ∧
    ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type =
      piTele (args.map fun t => (t.kexpr κ, { pw := PropWhen.never })) (res.kexpr κ)
  enums : ∀ D, (FoTy.enum D ∈ args ∨ res = .enum D) → EnumStored p env κ S D

/-- The pinned `Bool`'s listed constructor `1` is the pinned `Bool.true`. -/
def BoolListed (p : Program) (boolD : CId) : Prop :=
  ∃ (safe : Bool) (ty : Term) (cs : List CId),
    p.decl? boolD = some (.induct safe 0 0 0 ty cs) ∧ cs[1]? = p.known.boolTrue ∧
    p.known.boolTrue.isSome

/-! ## The checks -/

section Checks

variable (p : Program) (env : KEnv) (κ : CId → KKey) (Sl : List CId)

def enumStoredB (D : CId) : Bool :=
  match p.decl? D with
  | some (.induct _ 0 0 0 _ cs) =>
    (match env.find? (κ D) with
      | some ci => ci.toConstantVal.levelParams == []
      | none => false) &&
    (List.range cs.length).all (fun i =>
      match cs[i]? with
      | some c =>
        decide (c ∈ Sl) &&
          (match p.decl? c with
            | some (.ctor _ 0 D' i' 0 0 _) => D' == D && i' == i
            | _ => false) &&
          (match env.find? (κ c) with
            | some (.ctorInfo cv 0 0) =>
              cv.levelParams == [] && decide (cv.type = .const (κ D) [])
            | _ => false)
      | none => true) &&
    Sl.all (fun c =>
      match p.decl? c with
      | some (.ctor _ _ D' i _ _ _) => if D' == D then decide (cs[i]? = some c) else true
      | _ => true)
  | _ => false

/-- **The root's conjuncts**, by name. -/
def rootParts (ann : IxCC.Src.Relevance.Ann) (root : CId) (args : List FoTy) (res : FoTy) :
    List (String × Bool) :=
  [("rootMem", decide (root ∈ Sl)),
   ("rootOk", lvlsOf p root == 0 &&
      match constClass ann root with
      | some r => r.irrAt [] == false
      | none => false),
   ("rootStored", match env.find? (κ root) with
      | some ci => ci.toConstantVal.levelParams == [] &&
          decide (ci.toConstantVal.type =
            piTele (args.map fun t => (t.kexpr κ, { pw := PropWhen.never })) (res.kexpr κ))
      | none => false),
   ("rootEnums", ((res :: args).filterMap fun
      | .enum D => some D
      | .nat => none).all (enumStoredB p env κ Sl))]

def rootCheck (ann : IxCC.Src.Relevance.Ann) (root : CId) (args : List FoTy) (res : FoTy) : Bool :=
  (rootParts p env κ Sl ann root args res).all (·.2)

/-- The listed constructors of an enumeration of the fragment. -/
def enumCtors (D : CId) : Option (List CId) :=
  match p.decl? D with
  | some (.induct _ 0 0 0 _ cs) => some cs
  | _ => none

def foValB : FoTy → Value → KExpr → Bool
  | .nat, .lit n, e => decide (e = litE n)
  | .enum D, .con c [] [] [], e =>
    decide (e = .const (κ c) []) &&
      match enumCtors p D with
      | some cs => decide (c ∈ cs)
      | none => false
  | _, _, _ => false

def foArgsB : List FoTy → List Value → List KExpr → Bool
  | [], [], [] => true
  | t :: ts, x :: xs, e :: es => foValB p κ t x e && foArgsB ts xs es
  | _, _, _ => false

def resultTagB : FoTy → IxCC.Sem.Obs → Bool
  | .nat, _ => true
  | .enum D, .ctor i [] =>
    match p.decl? D with
    | some (.induct _ 0 0 0 _ cs) =>
      match cs[i]? with
      | some c' => Sl.all fun c =>
          readTag p c != i ||
            (match env.find? (κ c) with
              | some (.ctorInfo _ _ 0) => decide (κ c = κ c')
              | _ => true)
      | none => true
    | _ => true
  | .enum _, _ => true

def boolListedB (boolD : CId) : Bool :=
  match p.decl? boolD with
  | some (.induct _ 0 0 0 _ cs) => decide (cs[1]? = p.known.boolTrue) && p.known.boolTrue.isSome
  | _ => false

end Checks

/-! ## Soundness -/

section Lemmas

variable {p : Program} {env : KEnv} {κ : CId → KKey} {Sl : List CId}

theorem enumStored_of_check {D : CId} (h : enumStoredB p env κ Sl D = true) :
    EnumStored p env κ (· ∈ Sl) D := by
  unfold enumStoredB at h
  split at h
  · rename_i safe ty cs hd
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨safe, ty, cs, hd, ?_, fun i c hc => ?_, fun c hcS sf lv i np nf ty' hdc => ?_⟩
    · split at h1
      · rename_i ci hf; exact ⟨ci, hf, by simpa using h1⟩
      · cases h1
    · have hl := (List.getElem?_eq_some_iff.mp hc).1
      have := List.all_eq_true.mp h2 i (List.mem_range.mpr hl)
      simp only [hc, Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨⟨hS, hdc⟩, hfc⟩ := this
      refine ⟨hS, ?_, ?_⟩
      · split at hdc
        · rename_i sf' D' i' ty' hdc'
          simp only [Bool.and_eq_true, beq_iff_eq] at hdc
          obtain ⟨rfl, rfl⟩ := hdc
          exact ⟨sf', ty', hdc'⟩
        · cases hdc
      · split at hfc
        · rename_i cv hf
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfc
          exact ⟨cv, hf, hfc.1, hfc.2⟩
        · cases hfc
    · have := List.all_eq_true.mp h3 c hcS
      simp only [hdc, beq_self_eq_true, ↓reduceIte, decide_eq_true_eq] at this
      exact this
  · cases h

theorem rootFacts_of_check {ann : IxCC.Src.Relevance.Ann} {root : CId} {args : List FoTy}
    {res : FoTy} (h : rootCheck p env κ Sl ann root args res = true) :
    RootFacts p env κ ann (· ∈ Sl) root args res := by
  unfold rootCheck rootParts at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨hm, ho, hs, he⟩ := h
  refine ⟨hm, ?_, ?_, fun D hD => ?_⟩
  · simp only [beq_iff_eq] at ho
    obtain ⟨hl, ho⟩ := ho
    split at ho
    · rename_i r hr
      exact ⟨by simp [hl], r, hr, by simpa using ho⟩
    · cases ho
  · split at hs
    · rename_i ci hf
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
      exact ⟨ci, hf, hs.1, hs.2⟩
    · cases hs
  · refine enumStored_of_check (List.all_eq_true.mp he D ?_)
    rw [List.mem_filterMap]
    rcases hD with hD | hD
    · exact ⟨.enum D, List.mem_cons_of_mem _ hD, rfl⟩
    · exact ⟨.enum D, by rw [hD]; exact List.mem_cons_self .., rfl⟩

theorem enumCtors_some {D : CId} {cs : List CId} (h : enumCtors p D = some cs) :
    ∃ safe ty, p.decl? D = some (.induct safe 0 0 0 ty cs) := by
  unfold enumCtors at h
  split at h
  · rename_i safe ty cs' hd
    cases h
    exact ⟨safe, ty, hd⟩
  · cases h

theorem foVal_of_check {t : FoTy} {x : Value} {e : KExpr} (h : foValB p κ t x e = true) :
    FoVal p κ t x e := by
  unfold foValB at h
  split at h
  · rename_i n
    simp only [decide_eq_true_eq] at h
    subst h; exact .nat n
  · rename_i D c
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · rename_i cs hcs
      obtain ⟨safe, ty, hd⟩ := enumCtors_some hcs
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (of_decide_eq_true h)
      exact .enum hd hi
    · cases h
  · cases h

theorem foArgs_length : ∀ {ts : List FoTy} {xs : List Value} {es : List KExpr},
    FoArgs p κ ts xs es → es.length = ts.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => by simp [foArgs_length h]

theorem foArgs_of_check : ∀ {ts : List FoTy} {xs : List Value} {es : List KExpr},
    foArgsB p κ ts xs es = true → FoArgs p κ ts xs es
  | [], [], [], _ => .nil
  | _ :: _, _ :: _, _ :: _, h => by
    simp only [foArgsB, Bool.and_eq_true] at h
    exact .cons (foVal_of_check h.1) (foArgs_of_check h.2)
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [foArgsB] at h

theorem resultTag_of_check {res : FoTy} {o : IxCC.Sem.Obs}
    (h : resultTagB p env κ Sl res o = true) : ResultTag p env κ (· ∈ Sl) res o := by
  match res, o, h with
  | .nat, _, _ => trivial
  | .enum D, .ctor i [], h =>
    intro safe ty cs c' hd hc' c hc htag ⟨cv, np, hf⟩
    simp only [resultTagB, hd, hc'] at h
    have := List.all_eq_true.mp h c hc
    simp only [htag, bne_self_eq_false, Bool.false_or, hf, decide_eq_true_eq] at this
    exact this
  | .enum _, .ctor _ (_ :: _), _ => trivial
  | .enum _, .nat _, _ | .enum _, .word _, _ | .enum _, .bytes _, _ => trivial

theorem boolListed_of_check {boolD : CId} (h : boolListedB p boolD = true) :
    BoolListed p boolD := by
  unfold boolListedB at h
  split at h
  · rename_i safe ty cs hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨safe, ty, cs, hd, h.1, h.2⟩
  · cases h

end Lemmas

end IxCC.Grounding
