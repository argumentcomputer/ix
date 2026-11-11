import IxCCGrounding.Ok
import IxCCGrounding.CaseCheck

/-!
# The check (`IxCCGrounding.Check`)

**Every decidable fact the grounding theorems consume, decided by one Boolean function with a
proved soundness lemma** (`groundCheck`, `groundFacts_of_check`): over the program SrcEval runs,
the kernel's reading of the closure, the key map, the level parameters, the certificate's
annotation and a finite list `Sl` of constants. It imports neither the kernel's model nor any
proof about it, so `tests-grounding` runs it on closure bytes, conjunct by conjunct
(`checkParts`): each conjunct has a name, and the suite's negative controls assert that a
mutation targeting one makes exactly that one false.

| Conjunct | What it decides |
| --- | --- |
| `stored` | every constant of `Sl` is stored under its key, with its level parameters |
| `lvls` | the program's level count is the stored one |
| `nodup` | the level parameters are distinct |
| `noCsimp`, `declOk`, `notOpaque` | the fragment: no `csimp` entry, recursor or quotient constant, opaque by value |
| `prim` | a `prim` entry is the operation's role, stored with no level parameters, telescope long enough |
| `ctor` | a constructor is stored with the program's counts, telescope long enough |
| `caseRec` | a `case` entry's recursor is ordinary, the key's telescope long enough |
| `defn` | a δ-unfolded definition is stored as a definition; its value names only `Sl` |
| `eqnNames` | an `eqn` body names only `Sl` |
| `proj` | a projected structure has a projection table naming its constructor |
| `pins` | the `Nat` and `Bool` pins are the kernel's roles; the `Bool` constructors in `Sl` |
| `natBasis` | `Nat`, `Nat.zero` and `Nat.succ` stored as the literal reading needs |
| `eqBasis` | `Eq` stored with its type |
| `eqnShape` | each `eqn` entry's theorem has the checked shape (`EqnShape`) |
| `eqnCorr`, `eqnClosed` | each `eqn` body corresponds to the equation body, which is closed |
| `valueCorr`, `valueClosed` | each δ value corresponds to the stored value, which is closed |
| `okClosed` | `Ok`'s closure (`okClosedB`) |
| `caseShape` | each `case` entry's stored `casesOn`, recursor and constructors have the checked shape (`CaseStored`, read by `caseShape?`) |
| `caseProg` | each `case` entry's recursor and constructors in the program agree with the shape (`CaseProg`) |
-/

namespace IxCC.Grounding

open Ix.Kernel
open IxCC.Src (Value Slot Term CId Program Levels)

/-! ## Constants a term names -/

/-- The constants a Src term names (with repeats). -/
def constsOf : Term → List CId
  | .const c _ => [c]
  | .app f a _ _ => constsOf f ++ constsOf a
  | .lam _ d t | .pi _ _ d t => constsOf d ++ constsOf t
  | .letE _ _ t v b => constsOf t ++ constsOf v ++ constsOf b
  | .proj s _ e => s :: constsOf e
  | _ => []

theorem mentions_constsOf {c : CId} : ∀ {t : Term}, t.mentions c = true → c ∈ constsOf t
  | .var _, h | .sort _, h | .natLit _, h | .strLit _, h => by simp [Term.mentions] at h
  | .const d _, h => by simp only [Term.mentions, beq_iff_eq] at h; simp [constsOf, h]
  | .app f a _ _, h => by
    simp only [Term.mentions, Bool.or_eq_true] at h
    simp only [constsOf, List.mem_append]
    exact h.imp mentions_constsOf mentions_constsOf
  | .lam _ d t, h => by
    simp only [Term.mentions, Bool.or_eq_true] at h
    simp only [constsOf, List.mem_append]
    exact h.imp mentions_constsOf mentions_constsOf
  | .pi _ _ d t, h => by
    simp only [Term.mentions, Bool.or_eq_true] at h
    simp only [constsOf, List.mem_append]
    exact h.imp mentions_constsOf mentions_constsOf
  | .letE _ _ t v b, h => by
    simp only [Term.mentions, Bool.or_eq_true] at h
    simp only [constsOf, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (mentions_constsOf h))
    · exact Or.inl (Or.inr (mentions_constsOf h))
    · exact Or.inr (mentions_constsOf h)
  | .proj s _ e, h => by
    simp only [Term.mentions, Bool.or_eq_true, beq_iff_eq] at h
    simp only [constsOf, List.mem_cons]
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (mentions_constsOf h)

/-- Every constant `t` names is in `Sl`. -/
def namesInB (Sl : List CId) (t : Term) : Bool := (constsOf t).all fun c => decide (c ∈ Sl)

theorem constsIn_of_check {Sl : List CId} {t : Term} (h : namesInB Sl t = true) :
    ConstsIn (· ∈ Sl) t := by
  intro c hc
  have := List.all_eq_true.mp h c (mentions_constsOf hc)
  simpa using this

/-! ## The correspondence of terms -/

def univCorrB (lps : List Nat) : IxCC.Ixon.Univ → Level → Bool
  | .zero, .zero => true
  | .succ u, .succ l => univCorrB lps u l
  | .max a b, .max c d => univCorrB lps a c && univCorrB lps b d
  | .imax a b, .imax c d => univCorrB lps a c && univCorrB lps b d
  | .var i, .param p => lps[i.toNat]? == some p
  | _, _ => false

theorem univCorr_of_check {lps : List Nat} :
    ∀ (u : IxCC.Ixon.Univ) (l : Level), univCorrB lps u l = true → UnivCorr lps u l := by
  intro u
  induction u with
  | zero => intro l h; cases l <;> simp [univCorrB] at h; exact .zero
  | succ u ih => intro l h; cases l <;> simp [univCorrB] at h; exact .succ (ih _ h)
  | max a b iha ihb =>
    intro l h; cases l <;> simp [univCorrB] at h; exact .max (iha _ h.1) (ihb _ h.2)
  | imax a b iha ihb =>
    intro l h; cases l <;> simp [univCorrB] at h; exact .imax (iha _ h.1) (ihb _ h.2)
  | var i => intro l h; cases l <;> simp [univCorrB] at h; exact .var h

def termCorrB (κ : CId → KKey) (lps : List Nat) : Term → KExpr → Bool
  | .var i, .bvar j => i == j
  | .sort u, .sort l => univCorrB lps u l
  | .const c us, .const k ls =>
    decide (k = κ c) && us.length == ls.length && (us.zip ls).all fun (u, l) => univCorrB lps u l
  | .app f a _ _, .app f' a' => termCorrB κ lps f f' && termCorrB κ lps a a'
  | .lam _ d b, .lam d' b' _ => termCorrB κ lps d d' && termCorrB κ lps b b'
  | .pi _ _ d c, .forallE d' c' _ => termCorrB κ lps d d' && termCorrB κ lps c c'
  | .proj s i e, .proj k j e' => decide (k = κ s) && i == j && termCorrB κ lps e e'
  | .natLit n, .lit (.natVal m) => n == m
  | _, _ => false

theorem termCorr_of_check {κ : CId → KKey} {lps : List Nat} :
    ∀ (t : Term) (e : KExpr), termCorrB κ lps t e = true → TermCorr κ lps t e := by
  intro t
  induction t with
  | var i => intro e h; cases e <;> simp [termCorrB] at h; subst h; exact .var
  | sort u => intro e h; cases e <;> simp [termCorrB] at h; exact .sort (univCorr_of_check _ _ h)
  | const c us =>
    intro e h
    cases e <;> simp only [termCorrB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.all_eq_true, Bool.false_eq_true] at h
    obtain ⟨⟨rfl, hlen⟩, hall⟩ := h
    refine .const hlen fun i u l hu hl => univCorr_of_check _ _ ?_
    exact hall (u, l) (List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hu, hl⟩))
  | app f a m r ihf iha =>
    intro e h; cases e <;> simp [termCorrB] at h; exact .app (ihf _ h.1) (iha _ h.2)
  | lam b d body ihd ihb =>
    intro e h; cases e <;> simp [termCorrB] at h; exact .lam (ihd _ h.1) (ihb _ h.2)
  | pi b r d c ihd ihc =>
    intro e h; cases e <;> simp [termCorrB] at h; exact .pi (ihd _ h.1) (ihc _ h.2)
  | letE => intro e h; cases e <;> simp [termCorrB] at h
  | proj s i e ih =>
    intro e' h
    cases e' <;> simp only [termCorrB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.false_eq_true] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    exact .proj (ih _ h)
  | natLit n =>
    intro e h
    cases e with
    | lit l => cases l <;> simp [termCorrB] at h; subst h; exact .natLit
    | _ => simp [termCorrB] at h
  | strLit => intro e h; cases e <;> simp [termCorrB] at h

/-! ## The shape of an `eqn` entry -/

/-- A `∀`-telescope's binders, all of them, and what remains. -/
def splitAll : KExpr → List (KExpr × BinderMeta) × KExpr
  | .forallE d b m => ((d, m) :: (splitAll b).1, (splitAll b).2)
  | e => ([], e)

/-- Exactly `n` leading binders of a `∀`-telescope, and what remains. -/
def splitPi : Nat → KExpr → Option (List (KExpr × BinderMeta) × KExpr)
  | 0, e => some ([], e)
  | n + 1, .forallE d b m => (splitPi n b).map fun r => ((d, m) :: r.1, r.2)
  | _ + 1, _ => none

/-- An `eqn` entry's data, read off the stored theorem and function (the check then verifies
the shape against it, so this reading needs no proof). -/
def eqnData? (env : KEnv) (kc kt : KKey) : Option EqnData :=
  match env.find? kt, env.find? kc with
  | some (.thmInfo cvT _), some ciF =>
    match splitAll cvT.type with
    | (Ds, .app (.app (.app (.const _ [u]) T) _) rhs) =>
      (splitPi Ds.length ciF.toConstantVal.type).map fun r =>
        { Ds, ms := r.1.map (·.2), u, T, rhs, R := r.2 }
    | _ => none
  | _, _ => none

def eqBasisB (env : KEnv) : Bool :=
  match env.find? eqName with
  | some ci => ci.toConstantVal.levelParams == [0] && decide (ci.toConstantVal.type = eqType)
  | none => false

theorem eqBasis_of_check {env : KEnv} (h : eqBasisB env = true) : EqBasis env := by
  unfold eqBasisB at h
  split at h
  · rename_i ci hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨ci, hf, h.1, h.2⟩
  · exact absurd h (by simp)

/-- `EqnShape` without the `Eq` basis, decided. -/
def eqnShapeB (env : KEnv) (κ : CId → KKey) (c thm : CId) (d : EqnData) : Bool :=
  match env.find? (κ c), env.find? (κ thm) with
  | some ciF, some (.thmInfo cvT _) =>
    d.Ds.length == d.ms.length && cvT.levelParams == ciF.toConstantVal.levelParams &&
      decide (cvT.type = piTele d.Ds (Expr.mkAppN (.const eqName [d.u])
        [d.T, Expr.mkAppN (.const (κ c) (cvT.levelParams.map Level.param))
          (bvarsFrom 0 d.Ds.length), d.rhs])) &&
      decide (ciF.toConstantVal.type = piTele (d.Ds.zipWith (fun b m => (b.1, m)) d.ms) d.R)
  | _, _ => false

theorem eqnShape_of_check {env : KEnv} {κ : CId → KKey} {c thm : CId} {d : EqnData}
    (hE : EqBasis env) (h : eqnShapeB env κ c thm d = true) : EqnShape env κ c thm d := by
  unfold eqnShapeB at h
  split at h
  · rename_i ciF cvT pf hf ht
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨hE, ciF, cvT, pf, hf, ht, h1, h2, h3, h4⟩
  · exact absurd h (by simp)

theorem piTele_inj_app : ∀ (bs bs' : List (KExpr × BinderMeta)) (f a f' a' : KExpr),
    piTele bs (.app f a) = piTele bs' (.app f' a') → bs = bs' ∧ f = f' ∧ a = a'
  | [], [], _, _, _, _, h => by simp only [piTele, Expr.app.injEq] at h; exact ⟨rfl, h⟩
  | [], _ :: _, _, _, _, _, h => by simp [piTele] at h
  | _ :: _, [], _, _, _, _, h => by simp [piTele] at h
  | (A, m) :: bs, (A', m') :: bs', f, a, f', a', h => by
    simp only [piTele, Expr.forallE.injEq] at h
    obtain ⟨rfl, h2, rfl⟩ := h
    obtain ⟨rfl, h3⟩ := piTele_inj_app bs bs' f a f' a' h2
    exact ⟨rfl, h3⟩

theorem piTele_inj : ∀ (bs bs' : List (KExpr × BinderMeta)) (X X' : KExpr),
    bs.length = bs'.length → piTele bs X = piTele bs' X' → bs = bs' ∧ X = X'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | (A, m) :: bs, (A', m') :: bs', X, X', hl, h => by
    simp only [piTele, Expr.forallE.injEq] at h
    obtain ⟨rfl, h2, rfl⟩ := h
    obtain ⟨rfl, h3⟩ := piTele_inj bs bs' X X' (by simpa using hl) h2
    exact ⟨rfl, h3⟩

/-- **An `eqn` entry's equation body is determined by its shape.** -/
theorem eqnShape_body {env : KEnv} {κ : CId → KKey} {c thm : CId} {d d' : EqnData}
    (h : EqnShape env κ c thm d) (h' : EqnShape env κ c thm d') : d.body = d'.body := by
  obtain ⟨_, ciF, cvT, pf, hf, ht, hl, _, htT, htF⟩ := h
  obtain ⟨_, ciF', cvT', pf', hf', ht', hl', _, htT', htF'⟩ := h'
  rw [hf] at hf'; cases hf'
  rw [ht] at ht'; cases ht'
  simp only [Expr.mkAppN] at htT htT'
  obtain ⟨hD, hf1, hrhs⟩ := piTele_inj_app _ _ _ _ _ _ (htT.symm.trans htT')
  have hzl : (d.Ds.zipWith (fun b m => (b.1, m)) d.ms).length =
      (d'.Ds.zipWith (fun b m => (b.1, m)) d'.ms).length := by
    have e1 : d.Ds.length = d'.Ds.length := by rw [hD]
    simp only [List.length_zipWith]; omega
  obtain ⟨hz, _⟩ := piTele_inj _ _ _ _ hzl (htF.symm.trans htF')
  simp only [EqnData.body, hz, hrhs]

/-! ## The conjuncts -/

section Checks

variable (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat) (Sl : List CId)

def storedB (c : CId) : Bool :=
  match env.find? (κ c) with
  | some ci => ci.toConstantVal.levelParams == lpsOf c
  | none => false

def lvlsB (c : CId) : Bool := lvlsOf p c == (lpsOf c).length

def nodupB (c : CId) : Bool := decide (lpsOf c).Nodup

def noCsimpB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.csimp ..) => false
  | _ => true

def declOkB (c : CId) : Bool :=
  match p.decl? c with
  | some (.recr ..) => false
  | some (.quot ..) => false
  | _ => true

def primB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.prim op) =>
    decide (κ c = (primKey op : KKey)) &&
      match env.find? (primKey op) with
      | some ci => (ci.toConstantVal.levelParams == []) &&
          decide (op.arity ≤ kPis ci.toConstantVal.type)
      | none => false
  | _ => true

def ctorB (c : CId) : Bool :=
  match p.decl? c with
  | some (.ctor _ _ _ _ np nf _) =>
    match env.find? (κ c) with
    | some (.ctorInfo cv np' nf') => (np' == np) && (nf' == nf) && decide (np + nf ≤ kPis cv.type)
    | _ => false
  | _ => true

def caseRecB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.case r) =>
    (match p.table.recKindOf r with
      | some .ordinary => true
      | _ => false) &&
    (match env.find? (κ c) with
      | some ci => decide (p.headArity (.cases c) ≤ kPis ci.toConstantVal.type)
      | none => false)
  | _ => true

def defnB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | none =>
    match p.decl? c with
    | some (.defn .defn .safe _ _ v) =>
      (match env.find? (κ c) with
        | some (.defnInfo ..) => true
        | _ => false) && namesInB Sl v
    | _ => true
  | some _ => true

def eqnNamesB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.eqn _ body) => namesInB Sl body
  | _ => true

def projB (c : CId) : Bool :=
  match p.decl? c with
  | some (.induct _ _ _ _ _ [c₁]) =>
    match env.find? (κ c₁) with
    | some (.ctorInfo _ _ nf) =>
      (List.range nf).all fun i =>
        match env.findProj? (κ c) i with
        | some e => decide (e.ctor = κ c₁)
        | none => false
    | _ => true
  | _ => true

def boolPinB (b : Bool) : Bool :=
  match (if b then p.known.boolTrue else p.known.boolFalse) with
  | some c =>
    decide (c ∈ Sl) && decide (κ c = if b then boolTrueName else boolFalseName) &&
      match env.find? (κ c) with
      | some (.ctorInfo cv 0 0) => cv.levelParams == []
      | _ => false
  | none => true

def pinsB : Bool :=
  (match p.known.natZero with
    | some c => decide (κ c = natZeroName)
    | none => true) &&
  (match p.known.natSucc with
    | some c => decide (κ c = natSuccName)
    | none => true) &&
  boolPinB p env κ Sl true && boolPinB p env κ Sl false

def natBasisB : Bool :=
  (match env.find? natName with
    | some ci => ci.toConstantVal.levelParams == []
    | none => false) &&
  (match env.find? natZeroName with
    | some (.ctorInfo cv 0 0) =>
      decide (cv.name = natZeroName ∧ cv.type = .const natName [] ∧ cv.levelParams = [])
    | _ => false) &&
  (match env.find? natSuccName with
    | some (.ctorInfo cv 0 1) =>
      decide (cv.name = natSuccName ∧
        cv.type = .forallE (.const natName []) (.const natName []) { pw := PropWhen.never } ∧
        cv.levelParams = [])
    | _ => false)

/-- An `eqn` entry's shape, decided against the data read off the stored terms. -/
def eqnShapeOkB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.eqn thm _) =>
    match eqnData? env (κ c) (κ thm) with
    | some d => eqnShapeB env κ c thm d
    | none => false
  | _ => true

def eqnCorrB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.eqn thm body) =>
    match eqnData? env (κ c) (κ thm) with
    | some d => termCorrB κ (lpsOf c) body d.body
    | none => false
  | _ => true

def eqnClosedB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.eqn thm _) =>
    match eqnData? env (κ c) (κ thm) with
    | some d => bvarsLt 0 d.body
    | none => false
  | _ => true

def valueCorrB (c : CId) : Bool :=
  match p.table.resolveOf c, p.decl? c, env.find? (κ c) with
  | none, some (.defn .defn .safe _ _ v), some (.defnInfo _ val _) => termCorrB κ (lpsOf c) v val
  | _, _, _ => true

def valueClosedB (c : CId) : Bool :=
  match p.table.resolveOf c, p.decl? c, env.find? (κ c) with
  | none, some (.defn .defn .safe _ _ _), some (.defnInfo _ val _) => bvarsLt 0 val
  | _, _, _ => true

/-- A `case` entry's stored shape. -/
def caseShapeB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match caseShape? env (κ c) (κ r) with
    | some sh => caseStoredB env (κ c) (κ r) sh
    | none => false
  | _ => true

/-- A `case` entry's program side (true when no shape is read: `caseShape` reports that). -/
def caseProgOkB (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match caseShape? env (κ c) (κ r) with
    | some sh => caseProgB p κ Sl r sh
    | none => true
  | _ => true

end Checks

/-- **The conjuncts of the check**, by name. -/
def checkParts (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : List (String × Bool) :=
  [("stored", Sl.all (storedB env κ lpsOf)),
   ("lvls", Sl.all (lvlsB p lpsOf)),
   ("nodup", Sl.all (nodupB lpsOf)),
   ("noCsimp", Sl.all (noCsimpB p)),
   ("declOk", Sl.all (declOkB p)),
   ("notOpaque", Sl.all fun c => p.table.isOpaqueByValue c == false),
   ("prim", Sl.all (primB p env κ)),
   ("ctor", Sl.all (ctorB p env κ)),
   ("caseRec", Sl.all (caseRecB p env κ)),
   ("defn", Sl.all (defnB p env κ Sl)),
   ("eqnNames", Sl.all (eqnNamesB p Sl)),
   ("proj", Sl.all (projB p env κ)),
   ("pins", pinsB p env κ Sl),
   ("natBasis", natBasisB env),
   ("eqBasis", eqBasisB env),
   ("eqnShape", Sl.all (eqnShapeOkB p env κ)),
   ("eqnCorr", Sl.all (eqnCorrB p env κ lpsOf)),
   ("eqnClosed", Sl.all (eqnClosedB p env κ)),
   ("valueCorr", Sl.all (valueCorrB p env κ lpsOf)),
   ("valueClosed", Sl.all (valueClosedB p env κ)),
   ("okClosed", okClosedB p ann Sl),
   ("caseShape", Sl.all (caseShapeB p env κ)),
   ("caseProg", Sl.all (caseProgOkB p env κ Sl))]

/-- **The check.** -/
def groundCheck (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  (checkParts p env κ lpsOf ann Sl).all (·.2)

/-! ## Soundness -/

section Lemmas

variable {p : Program} {env : KEnv} {κ : CId → KKey} {lpsOf : CId → List Nat} {Sl : List CId}

theorem part_of {ann : IxCC.Src.Relevance.Ann} {name : String} {b : Bool}
    (h : groundCheck p env κ lpsOf ann Sl = true) (hm : (name, b) ∈ checkParts p env κ lpsOf ann Sl) :
    b = true :=
  List.all_eq_true.mp h _ hm

theorem stored_of {c : CId} (h : storedB env κ lpsOf c = true) :
    ∃ ci, env.find? (κ c) = some ci ∧ ci.toConstantVal.levelParams = lpsOf c := by
  unfold storedB at h
  split at h
  · rename_i ci hf
    exact ⟨ci, hf, beq_iff_eq.mp h⟩
  · exact absurd h (by simp)

theorem noCsimp_of {c : CId} (h : noCsimpB p c = true) :
    ∀ g us thm, p.table.resolveOf c ≠ some (.csimp g us thm) := by
  intro g us thm hr
  simp [noCsimpB, hr] at h

theorem noRecr_of {c : CId} (h : declOkB p c = true) :
    ∀ sf kk lvls np nmot nmin ni ind rules ty,
      p.decl? c ≠ some (.recr sf kk lvls np nmot nmin ni ind rules ty) := by
  intro sf kk lvls np nmot nmin ni ind rules ty hd
  simp [declOkB, hd] at h

theorem noQuot_of {c : CId} (h : declOkB p c = true) :
    ∀ qk lvls ty, p.decl? c ≠ some (.quot qk lvls ty) := by
  intro qk lvls ty hd
  simp [declOkB, hd] at h

theorem prim_of {c : CId} (h : primB p env κ c = true) :
    ∀ op, p.table.resolveOf c = some (.prim op) → κ c = primKey op ∧
      ∃ ci, env.find? (primKey op) = some ci ∧ ci.toConstantVal.levelParams = [] ∧
        op.arity ≤ kPis ci.toConstantVal.type := by
  intro op hr
  simp only [primB, hr, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hk, h⟩ := h
  refine ⟨hk, ?_⟩
  split at h
  · rename_i ci hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨ci, hf, h.1, h.2⟩
  · exact absurd h (by simp)

theorem ctor_of {c : CId} (h : ctorB p env κ c = true) :
    ∀ sf lvls ind cidx np nf ty, p.decl? c = some (.ctor sf lvls ind cidx np nf ty) →
      ∃ cv, env.find? (κ c) = some (.ctorInfo cv np nf) ∧ np + nf ≤ kPis cv.type := by
  intro sf lvls ind cidx np nf ty hd
  simp only [ctorB, hd] at h
  split at h
  · rename_i cv np' nf' hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, rfl⟩, hle⟩ := h
    exact ⟨cv, hf, hle⟩
  · exact absurd h (by simp)

theorem caseRec_of {c : CId} (h : caseRecB p env κ c = true) :
    ∀ r, p.table.resolveOf c = some (.case r) →
      p.table.recKindOf r = some .ordinary ∧
        ∃ ci, env.find? (κ c) = some ci ∧ p.headArity (.cases c) ≤ kPis ci.toConstantVal.type := by
  intro r hr
  simp only [caseRecB, hr, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · split at h1
    · rename_i hk; exact hk
    · exact absurd h1 (by simp)
  · split at h2
    · rename_i ci hf; exact ⟨ci, hf, of_decide_eq_true h2⟩
    · exact absurd h2 (by simp)

theorem defn_of {c : CId} (h : defnB p env κ Sl c = true) :
    p.table.resolveOf c = none → ∀ lvls ty v, p.decl? c = some (.defn .defn .safe lvls ty v) →
      (∃ cv val hint, env.find? (κ c) = some (.defnInfo cv val hint)) ∧ ConstsIn (· ∈ Sl) v := by
  intro hr lvls ty v hd
  simp only [defnB, hr, hd, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, constsIn_of_check h2⟩
  split at h1
  · rename_i cv val hint hf; exact ⟨cv, val, hint, hf⟩
  · exact absurd h1 (by simp)

theorem eqnNames_of {c : CId} (h : eqnNamesB p Sl c = true) :
    ∀ thm body, p.table.resolveOf c = some (.eqn thm body) → ConstsIn (· ∈ Sl) body := by
  intro thm body hr
  simp only [eqnNamesB, hr] at h
  exact constsIn_of_check h

theorem proj_of {s : CId} (h : projB p env κ s = true) :
    ∀ sf lvls np ni ty c, p.decl? s = some (.induct sf lvls np ni ty [c]) →
      ∀ cvC np' nf, env.find? (κ c) = some (.ctorInfo cvC np' nf) → ∀ i, i < nf →
        ∃ entry, env.findProj? (κ s) i = some entry ∧ entry.ctor = κ c := by
  intro sf lvls np ni ty c hd cvC np' nf hf i hi
  simp only [projB, hd, hf] at h
  have hall := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  split at hall
  · rename_i e he; exact ⟨e, he, of_decide_eq_true hall⟩
  · exact absurd hall (by simp)

theorem boolPin_of {b : Bool} (h : boolPinB p env κ Sl b = true) :
    ∀ c, (if b then p.known.boolTrue else p.known.boolFalse) = some c →
      c ∈ Sl ∧ κ c = (if b then boolTrueName else boolFalseName) ∧
        ∃ cv, env.find? (κ c) = some (.ctorInfo cv 0 0) ∧ cv.levelParams = [] := by
  intro c hc
  simp only [boolPinB, hc, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · rename_i cv hf; exact ⟨cv, hf, beq_iff_eq.mp h3⟩
  · exact absurd h3 (by simp)

theorem natBasis_of (h : natBasisB env = true) : NatBasis env := by
  simp only [natBasisB, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · split at h1
    · rename_i ci hf; exact ⟨ci, hf, beq_iff_eq.mp h1⟩
    · exact absurd h1 (by simp)
  · split at h2
    · rename_i cv hf
      obtain ⟨a, b, c⟩ := of_decide_eq_true h2
      exact ⟨cv, hf, a, b, c⟩
    · exact absurd h2 (by simp)
  · split at h3
    · rename_i cv hf
      obtain ⟨a, b, c⟩ := of_decide_eq_true h3
      exact ⟨cv, hf, a, b, c⟩
    · exact absurd h3 (by simp)

/-- **The check is sound**: it establishes every fact `GroundFacts` names. -/
theorem groundFacts_of_check {ann : IxCC.Src.Relevance.Ann}
    (h : groundCheck p env κ lpsOf ann Sl = true) :
    GroundFacts p env κ lpsOf ann (· ∈ Sl) := by
  have P : ∀ name b, (name, b) ∈ checkParts p env κ lpsOf ann Sl → b = true :=
    fun _ _ hm => part_of h hm
  have all : ∀ {f : CId → Bool} (name : String), (name, Sl.all f) ∈ checkParts p env κ lpsOf ann Sl →
      ∀ c, c ∈ Sl → f c = true :=
    fun name hm c hc => List.all_eq_true.mp (P name _ hm) c hc
  have hE : EqBasis env := eqBasis_of_check (P "eqBasis" (eqBasisB env) (by simp [checkParts]))
  have hpins := P "pins" (pinsB p env κ Sl) (by simp [checkParts])
  simp only [pinsB, Bool.and_eq_true] at hpins
  obtain ⟨⟨⟨hz, hs⟩, hbt⟩, hbf⟩ := hpins
  have hfaith : Faith p env κ lpsOf (· ∈ Sl) := by
    refine ⟨fun c hc => stored_of (all "stored" (by simp [checkParts]) c hc),
      fun c hc => beq_iff_eq.mp (all (f := lvlsB p lpsOf) "lvls" (by simp [checkParts]) c hc),
      fun c hc => of_decide_eq_true (all (f := nodupB lpsOf) "nodup" (by simp [checkParts]) c hc),
      fun c g us thm hc => noCsimp_of (all "noCsimp" (by simp [checkParts]) c hc) g us thm,
      fun c hc => noRecr_of (all "declOk" (by simp [checkParts]) c hc),
      fun c hc => noQuot_of (all "declOk" (by simp [checkParts]) c hc),
      fun c hc => by
        have := all (f := fun c => p.table.isOpaqueByValue c == false) "notOpaque"
          (by simp [checkParts]) c hc
        simpa using this,
      fun c op hc => prim_of (all "prim" (by simp [checkParts]) c hc) op,
      fun c hc => ctor_of (all "ctor" (by simp [checkParts]) c hc),
      fun c r hc hr => caseRec_of (all "caseRec" (by simp [checkParts]) c hc) r hr,
      fun c hc => defn_of (all "defn" (by simp [checkParts]) c hc),
      fun c thm body hc hr => eqnNames_of (all "eqnNames" (by simp [checkParts]) c hc) thm body hr,
      fun s hc => proj_of (all "proj" (by simp [checkParts]) s hc),
      fun c hc => by simp only [hc, decide_eq_true_eq] at hz; exact hz,
      fun c hc => by simp only [hc, decide_eq_true_eq] at hs; exact hs, ?_⟩
    intro b c hbc
    cases b
    · exact boolPin_of hbf c hbc
    · exact boolPin_of hbt c hbc
  -- the `eqn` entries
  have heqn : ∀ c thm body, c ∈ Sl → p.table.resolveOf c = some (.eqn thm body) →
      ∃ d, eqnData? env (κ c) (κ thm) = some d ∧ EqnShape env κ c thm d ∧
        TermCorr κ (lpsOf c) body d.body ∧ bvarsLt 0 d.body = true := by
    intro c thm body hc hr
    have h1 := all (f := eqnShapeOkB p env κ) "eqnShape" (by simp [checkParts]) c hc
    have h2 := all (f := eqnCorrB p env κ lpsOf) "eqnCorr" (by simp [checkParts]) c hc
    have h3 := all (f := eqnClosedB p env κ) "eqnClosed" (by simp [checkParts]) c hc
    simp only [eqnShapeOkB, eqnCorrB, eqnClosedB, hr] at h1 h2 h3
    split at h1
    · rename_i d hd
      rw [hd] at h2 h3
      exact ⟨d, hd, eqnShape_of_check hE h1, termCorr_of_check _ _ h2, h3⟩
    · exact absurd h1 (by simp)
  refine ⟨hfaith, natBasis_of (P "natBasis" (natBasisB env) (by simp [checkParts])), ?_, ?_, ?_,
    okClosed_of_check (P "okClosed" (okClosedB p ann Sl) (by simp [checkParts]))⟩
  · intro c thm body hc hr
    obtain ⟨d, _, hsh, hcorr, _⟩ := heqn c thm body hc hr
    exact ⟨⟨d, hsh⟩, fun d' hsh' => eqnShape_body hsh hsh' ▸ hcorr⟩
  · intro c lvls ty v cv val hint hc hr hd hf
    have h1 := all (f := valueCorrB p env κ lpsOf) "valueCorr" (by simp [checkParts]) c hc
    simp only [valueCorrB, hr, hd, hf] at h1
    exact termCorr_of_check _ _ h1
  · intro c t e hc hrp
    cases hrp with
    | value hr hd hf =>
      have h1 := all (f := valueClosedB p env κ) "valueClosed" (by simp [checkParts]) c hc
      simp only [valueClosedB, hr, hd, hf] at h1
      exact h1
    | eqn hr hsh =>
      obtain ⟨d, _, hsh', _, hcl⟩ := heqn c _ _ hc hr
      rw [eqnShape_body hsh hsh']
      exact hcl

/-- **The check is sound for the `case` entries**: it establishes `CaseFacts`. -/
theorem caseFacts_of_check {ann : IxCC.Src.Relevance.Ann}
    (h : groundCheck p env κ lpsOf ann Sl = true) : CaseFacts p env κ (· ∈ Sl) := by
  intro c r hc hr
  have h1 := List.all_eq_true.mp (part_of (name := "caseShape") (b := Sl.all (caseShapeB p env κ)) h (by simp [checkParts])) c hc
  have h2 := List.all_eq_true.mp (part_of (name := "caseProg") (b := Sl.all (caseProgOkB p env κ Sl)) h (by simp [checkParts])) c hc
  simp only [caseShapeB, caseProgOkB, hr] at h1 h2
  split at h1
  · rename_i sh hsh
    rw [hsh] at h2
    exact ⟨sh, caseStored_of_check h1, caseProg_of_check h2⟩
  · exact absurd h1 (by simp)

end Lemmas

end IxCC.Grounding
