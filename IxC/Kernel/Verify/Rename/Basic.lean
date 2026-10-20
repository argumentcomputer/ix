module

public import IxC.Kernel.Roles

@[expose] public section

/-!
# Renaming the input keys (IxC step 7.3, the data)

The renaming lemma (IXC-PLAN §12; LOCALITY §7 (d2)) says that the
reference fold commutes with a renaming of the input keys `Key.map f`,
`f : md.Id → md'.Id`, injective on the ids the run can meet. Locality is
the same statement at `f = id` with two environments that agree on the
keys a check can consult. Both are one walk over the pure checker
(`IxC/Kernel/Verify/Rename/*`), stated success-only: every success of the
original run is a success of the renamed run, with the renamed result.

This module is the data the walk is stated over:

* `Key.Good P`: every id of a key satisfies `P`, the predicate the
  renaming is injective on (`InjOn f P`); a role key has no ids, a derived
  key the ids of its base;
* `Expr.mapKeys f` and the renaming of every structure that carries keys
  (`ConstantVal`, `RecRule`, `IndCaps`, `ProjTable`, `ProjEntry`,
  `ConstantInfo`, `Declaration`, `Env`, the evidence), each with its
  `Good P`: what the renaming is injective on;
* injectivity (`*.mapKeys_inj`): on good values, renaming reflects
  equality, so every equality test of the checker answers alike;
* functoriality: `mapKeys` at the identity is the identity, and two
  renamings compose.

The renaming of the statements lane (`Ix.Cert.Rename`, over `σ = Key.map
f`) is this one.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' md'' : Mode}

/-! ## Keys -/

/-- **A key scope**: the input ids a run may meet (`id`, what the renaming
is injective on) and the roles it may read (`role`). The renaming walk
allows every role (`KeyScope.ofId`); the union of two lists allows, at each
step, the roles the left run has installed. -/
structure KeyScope (md : Mode) where
  id : md.Id → Prop
  role : Role → Prop

instance : CoeFun (KeyScope md) (fun _ => md.Id → Prop) := ⟨KeyScope.id⟩

/-- The scope of an id predicate: every role allowed. -/
def KeyScope.ofId (P : md.Id → Prop) : KeyScope md := ⟨P, fun _ => True⟩

/-- An id predicate is the scope allowing every role. -/
instance : Coe (md.Id → Prop) (KeyScope md) := ⟨KeyScope.ofId⟩

@[simp] theorem KeyScope.ofId_id (P : md.Id → Prop) (i : md.Id) : (KeyScope.ofId P) i ↔ P i :=
  Iff.rfl
@[simp] theorem KeyScope.ofId_role (P : md.Id → Prop) (r : Role) :
    (KeyScope.ofId (md := md) P).role r :=
  trivial

/-- **A good key**: every input id it names satisfies `P`. A role key names
no id; a derived key names its base's. -/
def Key.Good (P : KeyScope md) : Key md → Prop
  | .id i => P i
  | .role r => P.role r
  | .aux k _ => Key.Good P k

@[simp] theorem Key.good_id {P : KeyScope md} {i : md.Id} : (Key.id i).Good P ↔ P i := Iff.rfl
@[simp] theorem Key.good_role {P : KeyScope md} {r : Role} : (Key.role r : Key md).Good P ↔ P.role r :=
  Iff.rfl
@[simp] theorem Key.good_aux {P : KeyScope md} {k : Key md} {d : Derived} :
    (Key.aux k d).Good P ↔ k.Good P := Iff.rfl

/-- **`f` is injective on the ids satisfying `P`.** -/
def InjOn (f : md.Id → md'.Id) (P : md.Id → Prop) : Prop :=
  ∀ ⦃a b : md.Id⦄, P a → P b → f a = f b → a = b

/-- The identity is injective everywhere. -/
theorem InjOn.id (P : md.Id → Prop) : InjOn (md := md) (fun i => i) P :=
  fun _ _ _ _ h => h

/-- Injectivity on a smaller set. -/
theorem InjOn.mono {f : md.Id → md'.Id} {P Q : md.Id → Prop} (h : InjOn f P)
    (hQ : ∀ i, Q i → P i) : InjOn f Q :=
  fun _ _ ha hb e => h (hQ _ ha) (hQ _ hb) e

@[simp] theorem Key.map_ident {f : md.Id → md'.Id} {i : md.Id} :
    (Key.id i).map f = .id (f i) := rfl
@[simp] theorem Key.map_role {f : md.Id → md'.Id} {r : Role} :
    (Key.role r : Key md).map f = .role r := rfl
@[simp] theorem Key.map_aux {f : md.Id → md'.Id} {k : Key md} {d : Derived} :
    (Key.aux k d).map f = .aux (k.map f) d := rfl

/-- Renaming at the identity is the identity. -/
@[simp] theorem Key.map_id (k : Key md) : k.map (fun i => i) = k := by
  induction k with
  | id i => rfl
  | role r => rfl
  | aux k d ih => simp [ih]

/-- Two renamings compose. -/
theorem Key.map_map (f : md.Id → md'.Id) (g : md'.Id → md''.Id) (k : Key md) :
    (k.map f).map g = k.map (fun i => g (f i)) := by
  induction k with
  | id i => rfl
  | role r => rfl
  | aux k d ih => simp [ih]

/-- **Renaming reflects key equality on good keys.** -/
theorem Key.map_inj {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P) :
    ∀ {a b : Key md}, a.Good P → b.Good P → a.map f = b.map f → a = b := by
  intro a
  induction a with
  | id i =>
    intro b ha hb h
    cases b with
    | id j => simp only [map_ident, Key.id.injEq] at h; rw [hf ha hb h]
    | role _ => simp at h
    | aux _ _ => simp at h
  | role r =>
    intro b _ _ h
    cases b with
    | id _ => simp at h
    | role s => simpa using h
    | aux _ _ => simp at h
  | aux k d ih =>
    intro b ha hb h
    cases b with
    | id _ => simp at h
    | role _ => simp at h
    | aux k' d' =>
      simp only [map_aux, Key.aux.injEq] at h
      rw [ih (b := k') ha hb h.1, h.2]

theorem Key.map_eq_map_iff {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {a b : Key md} (ha : a.Good P) (hb : b.Good P) : a.map f = b.map f ↔ a = b :=
  ⟨Key.map_inj hf ha hb, fun h => h ▸ rfl⟩

/-- A renamed key is a role key exactly when the key is (roles are fixed,
and an input key stays an input key). -/
@[simp] theorem Key.map_eq_role_iff {f : md.Id → md'.Id} {k : Key md} {r : Role} :
    k.map f = .role r ↔ k = .role r := by
  cases k <;> simp

/-- A renamed key compares with a role key as the key does. -/
@[simp] theorem Key.map_beq_role {f : md.Id → md'.Id} {k : Key md} {r : Role} :
    (k.map f == Key.role r) = (k == Key.role r) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Key.map_eq_role_iff]

@[simp] theorem Key.role_eq_map_iff {f : md.Id → md'.Id} {k : Key md} {r : Role} :
    Key.role r = k.map f ↔ Key.role r = k := by
  constructor
  · intro h; exact (Key.map_eq_role_iff.mp h.symm).symm
  · intro h; subst h; rfl

@[simp] theorem Key.map_isModelSuffix {f : md.Id → md'.Id} (k : Key md) :
    (k.map f).isModelSuffix = k.isModelSuffix := by
  cases k with
  | aux k d => cases d <;> rfl
  | _ => rfl

@[simp] theorem Key.map_isProjFnShape {f : md.Id → md'.Id} (k : Key md) :
    (k.map f).isProjFnShape = k.isProjFnShape := by
  cases k with
  | aux k d => cases d <;> rfl
  | _ => rfl

@[simp] theorem Key.map_isProjIota {f : md.Id → md'.Id} (k : Key md) :
    (k.map f).isProjIota = k.isProjIota := by
  cases k with
  | aux k d => cases d <;> rfl
  | _ => rfl

/-- Good keys at a larger predicate. -/
theorem Key.Good.mono {P Q : KeyScope md} (hPQ : ∀ i, P i → Q i)
    (hR : ∀ r, P.role r → Q.role r) :
    ∀ {k : Key md}, k.Good P → k.Good Q
  | .id i, h => hPQ i h
  | .role r, h => hR r h
  | .aux k _, h => Key.Good.mono hPQ hR (k := k) h

/-! ## Expressions -/

/-- **Rename the keys of an expression.** -/
@[simp] def Expr.mapKeys (f : md.Id → md'.Id) : Expr md → Expr md'
  | .bvar i => .bvar i
  | .fvar i t => .fvar i (Expr.mapKeys f t)
  | .sort u => .sort u
  | .const n us => .const (n.map f) us
  | .app a b => .app (Expr.mapKeys f a) (Expr.mapKeys f b)
  | .lam t b m => .lam (Expr.mapKeys f t) (Expr.mapKeys f b) m
  | .forallE t b m => .forallE (Expr.mapKeys f t) (Expr.mapKeys f b) m
  | .letE t v b l => .letE (Expr.mapKeys f t) (Expr.mapKeys f v) (Expr.mapKeys f b) l
  | .lit l => .lit l
  | .proj s i e => .proj (s.map f) i (Expr.mapKeys f e)

/-- **The string-support roles**: the seven declarations a string literal
implicitly references besides the `Nat` trio (`Expr.constsResolve`'s
`strVal` clause). -/
def strRoles : List Role :=
  [.string, .stringOfList, .list, .listNil, .listCons, .char, .charOfNat]

/-- **The roles a literal mentions** beyond the prelude's: none for a `Nat`
literal (its type's declarations are the prelude's), the string-support
roles for a string literal. -/
def Literal.roles : Literal → List Role
  | .natVal _ => []
  | .strVal _ => strRoles

@[simp] theorem Literal.roles_natVal (n : Nat) : (Literal.natVal n).roles = [] := rfl
@[simp] theorem Literal.roles_strVal (s : String) : (Literal.strVal s).roles = strRoles := rfl

/-- **The prelude's roles**: those of its twelve declarations (`Eq`, `Nat`,
`PUnit`, `Empty`, `False`, the quotient package, `And`, `Bool`;
`IxC/Kernel/Ixon/Prelude.lean`). The walk reads them unprompted (literal
support, the operations' guards, the pins), so a related pair of
environments agrees on all of them (`EnvRelG.pre`). -/
def preludeRoles : List Role :=
  [.nat, .natZero, .natSucc, .natRec, .bool, .boolFalse, .boolTrue, .boolRec, .eq, .eqRefl,
   .eqRec, .punit, .punitUnit, .punitRec, .empty, .emptyRec, .false, .falseRec, .and, .andIntro,
   .andRec, .quot, .quotMk, .quotLift, .quotInd, .quotSound]

/-- A scope that allows every prelude role. -/
def KeyScope.Pre (P : KeyScope md) : Prop := ∀ r ∈ preludeRoles, P.role r

/-- A scope that allows every string-support role. -/
def KeyScope.Str (P : KeyScope md) : Prop := ∀ r ∈ strRoles, P.role r

/-- A scope that allows every role (the renaming's, `KeyScope.ofId`). -/
def KeyScope.All (P : KeyScope md) : Prop := ∀ r, P.role r

@[simp] theorem KeyScope.ofId_pre (P : md.Id → Prop) : (KeyScope.ofId P).Pre := fun _ _ => trivial
@[simp] theorem KeyScope.ofId_str (P : md.Id → Prop) : (KeyScope.ofId P).Str := fun _ _ => trivial
@[simp] theorem KeyScope.ofId_all (P : md.Id → Prop) : (KeyScope.ofId P).All := fun _ => trivial
theorem KeyScope.All.pre {P : KeyScope md} (h : P.All) : P.Pre := fun r _ => h r
theorem KeyScope.All.str {P : KeyScope md} (h : P.All) : P.Str := fun r _ => h r


/-- **A good expression**: every key it contains is good. -/
@[simp] def Expr.Good (P : KeyScope md) : Expr md → Prop
  | .bvar _ => True
  | .fvar _ t => Expr.Good P t
  | .sort _ => True
  | .const n _ => n.Good P
  | .app a b => Expr.Good P a ∧ Expr.Good P b
  | .lam t b _ => Expr.Good P t ∧ Expr.Good P b
  | .forallE t b _ => Expr.Good P t ∧ Expr.Good P b
  | .letE t v b _ => Expr.Good P t ∧ Expr.Good P v ∧ Expr.Good P b
  | .lit (.natVal _) => True
  | .lit (.strVal _) => P.Str
  | .proj s _ e => s.Good P ∧ Expr.Good P e

@[simp] theorem Expr.mapKeys_id (e : Expr md) : e.mapKeys (fun i => i) = e := by
  induction e <;> simp_all

theorem Expr.mapKeys_mapKeys (f : md.Id → md'.Id) (g : md'.Id → md''.Id) (e : Expr md) :
    (e.mapKeys f).mapKeys g = e.mapKeys (fun i => g (f i)) := by
  induction e <;> simp_all [Key.map_map]

theorem Expr.Good.mono {P Q : KeyScope md} (hPQ : ∀ i, P i → Q i)
    (hR : ∀ r, P.role r → Q.role r) :
    ∀ {e : Expr md}, e.Good P → e.Good Q := by
  intro e
  induction e with
  | lit l =>
    cases l with
    | natVal => exact fun _ => trivial
    | strVal => exact fun h r hr => hR r (h r hr)
  | _ => simp_all [Key.Good.mono hPQ hR]

/-- **Renaming reflects equality on good expressions.** -/
theorem Expr.mapKeys_inj {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P) :
    ∀ {a b : Expr md}, a.Good P → b.Good P → a.mapKeys f = b.mapKeys f → a = b := by
  intro a
  induction a with
  | bvar i =>
    intro b _ _ h; cases b <;> simp_all
  | fvar i t ih =>
    intro b ha hb h
    cases b with
    | fvar j u =>
      simp only [mapKeys, Expr.fvar.injEq] at h
      simp only [Good] at ha hb
      rw [h.1, ih ha hb h.2]
    | _ => simp at h
  | sort u =>
    intro b _ _ h; cases b <;> simp_all
  | const n us =>
    intro b ha hb h
    cases b with
    | const n' us' =>
      simp only [mapKeys, Expr.const.injEq] at h
      simp only [Good] at ha hb
      rw [Key.map_inj hf ha hb h.1, h.2]
    | _ => simp at h
  | app a₁ a₂ ih₁ ih₂ =>
    intro b ha hb h
    cases b with
    | app b₁ b₂ =>
      simp only [mapKeys, Expr.app.injEq] at h
      simp only [Good] at ha hb
      rw [ih₁ ha.1 hb.1 h.1, ih₂ ha.2 hb.2 h.2]
    | _ => simp at h
  | lam t₁ b₁ m₁ ih₁ ih₂ =>
    intro b ha hb h
    cases b with
    | lam t₂ b₂ m₂ =>
      simp only [mapKeys, Expr.lam.injEq] at h
      simp only [Good] at ha hb
      rw [ih₁ ha.1 hb.1 h.1, ih₂ ha.2 hb.2 h.2.1, h.2.2]
    | _ => simp at h
  | forallE t₁ b₁ m₁ ih₁ ih₂ =>
    intro b ha hb h
    cases b with
    | forallE t₂ b₂ m₂ =>
      simp only [mapKeys, Expr.forallE.injEq] at h
      simp only [Good] at ha hb
      rw [ih₁ ha.1 hb.1 h.1, ih₂ ha.2 hb.2 h.2.1, h.2.2]
    | _ => simp at h
  | letE t₁ v₁ b₁ l₁ ih₁ ih₂ ih₃ =>
    intro b ha hb h
    cases b with
    | letE t₂ v₂ b₂ l₂ =>
      simp only [mapKeys, Expr.letE.injEq] at h
      simp only [Good] at ha hb
      rw [ih₁ ha.1 hb.1 h.1, ih₂ ha.2.1 hb.2.1 h.2.1, ih₃ ha.2.2 hb.2.2 h.2.2.1, h.2.2.2]
    | _ => simp at h
  | lit l =>
    intro b _ _ h; cases b <;> simp_all
  | proj s i e ih =>
    intro b ha hb h
    cases b with
    | proj s' i' e' =>
      simp only [mapKeys, Expr.proj.injEq] at h
      simp only [Good] at ha hb
      rw [Key.map_inj hf ha.1 hb.1 h.1, h.2.1, ih ha.2 hb.2 h.2.2]
    | _ => simp at h

theorem Expr.mapKeys_eq_iff {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {a b : Expr md} (ha : a.Good P) (hb : b.Good P) : a.mapKeys f = b.mapKeys f ↔ a = b :=
  ⟨Expr.mapKeys_inj hf ha hb, fun h => h ▸ rfl⟩

/-- `==` on renamed good expressions is `==` on the expressions. -/
theorem Expr.mapKeys_beq {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {a b : Expr md} (ha : a.Good P) (hb : b.Good P) :
    (a.mapKeys f == b.mapKeys f) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact Expr.mapKeys_eq_iff hf ha hb

/-- `==` on renamed good keys is `==` on the keys. -/
theorem Key.map_beq {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {a b : Key md} (ha : a.Good P) (hb : b.Good P) :
    (a.map f == b.map f) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact Key.map_eq_map_iff hf ha hb

/-! ## Lists of expressions -/

/-- A list of good expressions. -/
def Expr.GoodList (P : KeyScope md) (es : List (Expr md)) : Prop := ∀ e ∈ es, e.Good P

@[simp] theorem Expr.goodList_nil {P : KeyScope md} : Expr.GoodList P ([] : List (Expr md)) :=
  fun _ h => nomatch h

@[simp] theorem Expr.goodList_cons {P : KeyScope md} {e : Expr md} {es : List (Expr md)} :
    Expr.GoodList P (e :: es) ↔ e.Good P ∧ Expr.GoodList P es := by
  simp [Expr.GoodList]

@[simp] theorem Expr.goodList_append {P : KeyScope md} {as bs : List (Expr md)} :
    Expr.GoodList P (as ++ bs) ↔ Expr.GoodList P as ∧ Expr.GoodList P bs := by
  simp [Expr.GoodList, or_imp, forall_and]

theorem Expr.mapKeys_list_inj {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P) :
    ∀ {as bs : List (Expr md)}, Expr.GoodList P as → Expr.GoodList P bs →
      as.map (Expr.mapKeys f) = bs.map (Expr.mapKeys f) → as = bs
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, ha, hb, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [goodList_cons] at ha hb
    rw [Expr.mapKeys_inj hf ha.1 hb.1 h.1, Expr.mapKeys_list_inj hf ha.2 hb.2 h.2]

/-! ## Constants -/

/-- Rename a constant's header. -/
def ConstantVal.mapKeys (f : md.Id → md'.Id) (cv : ConstantVal md) : ConstantVal md' :=
  { name := cv.name.map f, levelParams := cv.levelParams, type := cv.type.mapKeys f }

/-- A good header: its name and type are good. -/
abbrev ConstantVal.Good (P : KeyScope md) (cv : ConstantVal md) : Prop :=
  cv.name.Good P ∧ cv.type.Good P

@[simp] theorem ConstantVal.mapKeys_name (f : md.Id → md'.Id) (cv : ConstantVal md) :
    (cv.mapKeys f).name = cv.name.map f := rfl
@[simp] theorem ConstantVal.mapKeys_levelParams (f : md.Id → md'.Id) (cv : ConstantVal md) :
    (cv.mapKeys f).levelParams = cv.levelParams := rfl
@[simp] theorem ConstantVal.mapKeys_type (f : md.Id → md'.Id) (cv : ConstantVal md) :
    (cv.mapKeys f).type = cv.type.mapKeys f := rfl

theorem ConstantVal.mapKeys_inj {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {a b : ConstantVal md} (ha : a.Good P) (hb : b.Good P) (h : a.mapKeys f = b.mapKeys f) :
    a = b := by
  obtain ⟨n, l, t⟩ := a
  obtain ⟨n', l', t'⟩ := b
  simp only [mapKeys, ConstantVal.mk.injEq] at h
  simp only [Good] at ha hb
  rw [Key.map_inj hf ha.1 hb.1 h.1, h.2.1, Expr.mapKeys_inj hf ha.2 hb.2 h.2.2]

/-- Rename a recursor rule's firing mode. -/
def RecRuleFire.mapKeys (f : md.Id → md'.Id) : RecRuleFire md → RecRuleFire md'
  | .inert => .inert
  | .plain => .plain
  | .nested lvls pins => .nested lvls (pins.map (Expr.mapKeys f))

def RecRuleFire.Good (P : KeyScope md) : RecRuleFire md → Prop
  | .inert => True
  | .plain => True
  | .nested _ pins => Expr.GoodList P pins

attribute [simp] RecRuleFire.mapKeys.eq_1 RecRuleFire.mapKeys.eq_2 RecRuleFire.mapKeys.eq_3
  RecRuleFire.Good.eq_1 RecRuleFire.Good.eq_2 RecRuleFire.Good.eq_3

/-- Rename a recursor rule. -/
def RecRule.mapKeys (f : md.Id → md'.Id) (r : RecRule md) : RecRule md' :=
  { ctor := r.ctor.map f, nfields := r.nfields, ctorParams := r.ctorParams,
    fire := r.fire.mapKeys f, rhs := r.rhs.mapKeys f, k := r.k, eta := r.eta,
    paramsBlind := r.paramsBlind }

abbrev RecRule.Good (P : KeyScope md) (r : RecRule md) : Prop :=
  r.ctor.Good P ∧ r.fire.Good P ∧ r.rhs.Good P

/-- Rename an inductive's capabilities (only the η constructor is a key). -/
def IndCaps.mapKeys (f : md.Id → md'.Id) (c : IndCaps md) : IndCaps md' :=
  { eta := c.eta, etaCtor := c.etaCtor.map (Key.map f), etaParams := c.etaParams,
    etaFields := c.etaFields, unitlike := c.unitlike, unitParams := c.unitParams,
    ruleK := c.ruleK, sortZ := c.sortZ }

abbrev IndCaps.Good (P : KeyScope md) (c : IndCaps md) : Prop :=
  ∀ k ∈ c.etaCtor, k.Good P

/-- Rename a projection table. -/
def ProjTable.mapKeys (f : md.Id → md'.Id) (t : ProjTable md) : ProjTable md' :=
  { structName := t.structName.map f, levelParams := t.levelParams, numParams := t.numParams,
    ctor := t.ctor.map f, numFields := t.numFields, structSort := t.structSort,
    bodies := t.bodies.map (Expr.mapKeys f), guards := t.guards, off := t.off }

abbrev ProjTable.Good (P : KeyScope md) (t : ProjTable md) : Prop :=
  t.structName.Good P ∧ t.ctor.Good P ∧ ∀ b ∈ t.bodies, b.Good P

/-- Rename a projection-table entry. -/
def ProjEntry.mapKeys (f : md.Id → md'.Id) (e : ProjEntry md) : ProjEntry md' :=
  { structName := e.structName.map f, idx := e.idx, levelParams := e.levelParams,
    numParams := e.numParams, ctor := e.ctor.map f, numFields := e.numFields,
    body := e.body.mapKeys f, fieldSort := e.fieldSort, structSort := e.structSort,
    off := e.off }

abbrev ProjEntry.Good (P : KeyScope md) (e : ProjEntry md) : Prop :=
  e.structName.Good P ∧ e.ctor.Good P ∧ e.body.Good P

/-- A table's entry, renamed, is the renamed table's entry. -/
theorem ProjTable.mapKeys_entry (f : md.Id → md'.Id) (t : ProjTable md) (i : Nat) :
    (t.mapKeys f).entry i = (t.entry i).mapKeys f := by
  simp only [ProjTable.entry, mapKeys, ProjEntry.mapKeys, Array.getD_eq_getD_getElem?,
    Array.getElem?_map]
  cases t.bodies[i]? <;> rfl

theorem ProjTable.good_entry {P : KeyScope md} {t : ProjTable md} (h : t.Good P) (i : Nat) :
    (t.entry i).Good P := by
  obtain ⟨hs, hc, hb⟩ := h
  refine ⟨hs, hc, ?_⟩
  simp only [ProjTable.entry, Array.getD_eq_getD_getElem?]
  cases hi : t.bodies[i]? with
  | none => exact True.intro
  | some b => exact hb b (Array.mem_of_getElem? hi)

/-- **Rename a stored constant.** -/
def ConstantInfo.mapKeys (f : md.Id → md'.Id) : ConstantInfo md → ConstantInfo md'
  | .axiomInfo v => .axiomInfo (v.mapKeys f)
  | .defnInfo v e h => .defnInfo (v.mapKeys f) (e.mapKeys f) h
  | .thmInfo v e => .thmInfo (v.mapKeys f) (e.mapKeys f)
  | .indInfo v caps => .indInfo (v.mapKeys f) (caps.mapKeys f)
  | .ctorInfo v nP nF => .ctorInfo (v.mapKeys f) nP nF
  | .recInfo v major pre rules => .recInfo (v.mapKeys f) major pre (rules.map (RecRule.mapKeys f))
  | .projInfo tbl => .projInfo (tbl.mapKeys f)

/-- A good stored constant: every key it carries is good. -/
def ConstantInfo.Good (P : KeyScope md) : ConstantInfo md → Prop
  | .axiomInfo v => v.Good P
  | .defnInfo v e _ => v.Good P ∧ e.Good P
  | .thmInfo v e => v.Good P ∧ e.Good P
  | .indInfo v caps => v.Good P ∧ caps.Good P
  | .ctorInfo v _ _ => v.Good P
  | .recInfo v _ _ rules => v.Good P ∧ ∀ r ∈ rules, r.Good P
  | .projInfo tbl => tbl.Good P

attribute [simp] ConstantInfo.mapKeys.eq_1 ConstantInfo.mapKeys.eq_2 ConstantInfo.mapKeys.eq_3
  ConstantInfo.mapKeys.eq_4 ConstantInfo.mapKeys.eq_5 ConstantInfo.mapKeys.eq_6
  ConstantInfo.mapKeys.eq_7 ConstantInfo.Good.eq_1 ConstantInfo.Good.eq_2 ConstantInfo.Good.eq_3
  ConstantInfo.Good.eq_4 ConstantInfo.Good.eq_5 ConstantInfo.Good.eq_6 ConstantInfo.Good.eq_7

@[simp] theorem ConstantInfo.mapKeys_toConstantVal (f : md.Id → md'.Id) (c : ConstantInfo md) :
    (c.mapKeys f).toConstantVal = c.toConstantVal.mapKeys f := by
  cases c <;> rfl

@[simp] theorem ConstantInfo.mapKeys_name (f : md.Id → md'.Id) (c : ConstantInfo md) :
    (c.mapKeys f).name = c.name.map f := by
  cases c <;> rfl

@[simp] theorem ConstantInfo.mapKeys_type (f : md.Id → md'.Id) (c : ConstantInfo md) :
    (c.mapKeys f).type = c.type.mapKeys f := by
  cases c <;> rfl

theorem ConstantInfo.Good.toConstantVal {P : KeyScope md} :
    ∀ {c : ConstantInfo md}, c.Good P → c.toConstantVal.Good P
  | .axiomInfo _, h => h
  | .defnInfo _ _ _, h => h.1
  | .thmInfo _ _, h => h.1
  | .indInfo _ _, h => h.1
  | .ctorInfo _ _ _, h => h
  | .recInfo _ _ _ _, h => h.1
  | .projInfo _, h => ⟨h.1, trivial⟩

theorem ConstantInfo.Good.name {P : KeyScope md} {c : ConstantInfo md} (h : c.Good P) :
    c.name.Good P :=
  h.toConstantVal.1

theorem ConstantInfo.Good.type {P : KeyScope md} {c : ConstantInfo md} (h : c.Good P) :
    c.type.Good P :=
  h.toConstantVal.2

/-- Renaming the rules of a recursor reflects their equality. -/
theorem RecRule.mapKeys_inj {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {a b : RecRule md} (ha : a.Good P) (hb : b.Good P) (h : a.mapKeys f = b.mapKeys f) :
    a = b := by
  obtain ⟨c, nf, cp, fi, rhs, k, e, pb⟩ := a
  obtain ⟨c', nf', cp', fi', rhs', k', e', pb'⟩ := b
  simp only [mapKeys, RecRule.mk.injEq] at h
  simp only [Good] at ha hb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hfi : fi = fi' := by
    cases fi with
    | inert => cases fi' <;> simp_all
    | plain => cases fi' <;> simp_all
    | nested l ps =>
      cases fi' with
      | nested l' ps' =>
        simp only [RecRuleFire.mapKeys, RecRuleFire.nested.injEq] at h4
        rw [h4.1, Expr.mapKeys_list_inj hf ha.2.1 hb.2.1 h4.2]
      | _ => simp at h4
  subst h2 h3 h6 h7 h8 hfi
  rw [Key.map_inj hf ha.1 hb.1 h1, Expr.mapKeys_inj hf ha.2.2 hb.2.2 h5]

theorem RecRule.mapKeys_list_inj {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P) :
    ∀ {as bs : List (RecRule md)}, (∀ r ∈ as, r.Good P) → (∀ r ∈ bs, r.Good P) →
      as.map (RecRule.mapKeys f) = bs.map (RecRule.mapKeys f) → as = bs
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, ha, hb, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.mem_cons, forall_eq_or_imp] at ha hb
    rw [RecRule.mapKeys_inj hf ha.1 hb.1 h.1, RecRule.mapKeys_list_inj hf ha.2 hb.2 h.2]

theorem IndCaps.mapKeys_inj {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {a b : IndCaps md} (ha : a.Good P) (hb : b.Good P) (h : a.mapKeys f = b.mapKeys f) :
    a = b := by
  obtain ⟨e, ec, ep, ef, u, up, rk, sz⟩ := a
  obtain ⟨e', ec', ep', ef', u', up', rk', sz'⟩ := b
  simp only [mapKeys, IndCaps.mk.injEq] at h
  simp only [Good] at ha hb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hec : ec = ec' := by
    cases ec with
    | none => cases ec' <;> simp_all
    | some k =>
      cases ec' with
      | none => simp at h2
      | some k' =>
        simp only [Option.map_some, Option.some.injEq] at h2
        exact congrArg some (Key.map_inj hf (ha k rfl) (hb k' rfl) h2)
  subst h1 h3 h4 h5 h6 h7 h8 hec
  rfl

theorem ProjTable.mapKeys_inj {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {a b : ProjTable md} (ha : a.Good P) (hb : b.Good P) (h : a.mapKeys f = b.mapKeys f) :
    a = b := by
  obtain ⟨s, lp, np, c, nf, ss, bs, gs, off⟩ := a
  obtain ⟨s', lp', np', c', nf', ss', bs', gs', off'⟩ := b
  simp only [mapKeys, ProjTable.mk.injEq] at h
  simp only [Good] at ha hb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hbs : bs = bs' := by
    have h7' := congrArg Array.toList h7
    simp only [Array.toList_map] at h7'
    exact Array.toList_inj.mp (Expr.mapKeys_list_inj hf
      (fun e he => ha.2.2 e (Array.mem_toList_iff.mp he))
      (fun e he => hb.2.2 e (Array.mem_toList_iff.mp he)) h7')
  subst h2 h3 h5 h6 h8 h9 hbs
  rw [Key.map_inj hf ha.1 hb.1 h1, Key.map_inj hf ha.2.1 hb.2.1 h4]

/-- **Renaming reflects equality on good stored constants.** -/
theorem ConstantInfo.mapKeys_inj {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {a b : ConstantInfo md} (ha : a.Good P) (hb : b.Good P) (h : a.mapKeys f = b.mapKeys f) :
    a = b := by
  cases a <;> cases b <;> simp only [mapKeys, reduceCtorEq] at h <;> simp only [Good] at ha hb
  · rw [ConstantVal.mapKeys_inj hf ha hb (ConstantInfo.axiomInfo.inj h)]
  · simp only [ConstantInfo.defnInfo.injEq] at h
    rw [ConstantVal.mapKeys_inj hf ha.1 hb.1 h.1, Expr.mapKeys_inj hf ha.2 hb.2 h.2.1, h.2.2]
  · simp only [ConstantInfo.thmInfo.injEq] at h
    rw [ConstantVal.mapKeys_inj hf ha.1 hb.1 h.1, Expr.mapKeys_inj hf ha.2 hb.2 h.2]
  · simp only [ConstantInfo.indInfo.injEq] at h
    rw [ConstantVal.mapKeys_inj hf ha.1 hb.1 h.1, IndCaps.mapKeys_inj hf ha.2 hb.2 h.2]
  · simp only [ConstantInfo.ctorInfo.injEq] at h
    rw [ConstantVal.mapKeys_inj hf ha hb h.1, h.2.1, h.2.2]
  · simp only [ConstantInfo.recInfo.injEq] at h
    rw [ConstantVal.mapKeys_inj hf ha.1 hb.1 h.1, h.2.1, h.2.2.1,
      RecRule.mapKeys_list_inj hf ha.2 hb.2 h.2.2.2]
  · simp only [ConstantInfo.projInfo.injEq] at h
    rw [ProjTable.mapKeys_inj hf ha hb h]

theorem ConstantInfo.mapKeys_eq_iff {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {a b : ConstantInfo md} (ha : a.Good P) (hb : b.Good P) :
    a.mapKeys f = b.mapKeys f ↔ a = b :=
  ⟨ConstantInfo.mapKeys_inj hf ha hb, fun h => h ▸ rfl⟩

/-! ## Declarations -/

/-- **Rename a declaration.** -/
def Declaration.mapKeys (f : md.Id → md'.Id) : Declaration md → Declaration md'
  | .axiomDecl v => .axiomDecl (v.mapKeys f)
  | .defnDecl v e h => .defnDecl (v.mapKeys f) (e.mapKeys f) h
  | .thmDecl v e => .thmDecl (v.mapKeys f) (e.mapKeys f)
  | .opaqueDecl v e => .opaqueDecl (v.mapKeys f) (e.mapKeys f)
  | .basisDecl k => .basisDecl k
  | .indDecl block nP => .indDecl (block.map (ConstantInfo.mapKeys f)) nP
  | .quotDecl k v => .quotDecl k (v.mapKeys f)

/-- A good declaration: every key it carries is good. -/
def Declaration.Good (P : KeyScope md) : Declaration md → Prop
  | .axiomDecl v => v.Good P
  | .defnDecl v e _ => v.Good P ∧ e.Good P
  | .thmDecl v e => v.Good P ∧ e.Good P
  | .opaqueDecl v e => v.Good P ∧ e.Good P
  | .basisDecl _ => True
  | .indDecl block _ => ∀ c ∈ block, c.Good P
  | .quotDecl _ v => v.Good P

attribute [simp] Declaration.mapKeys.eq_1 Declaration.mapKeys.eq_2 Declaration.mapKeys.eq_3
  Declaration.mapKeys.eq_4 Declaration.mapKeys.eq_5 Declaration.mapKeys.eq_6
  Declaration.mapKeys.eq_7 Declaration.Good.eq_1 Declaration.Good.eq_2 Declaration.Good.eq_3
  Declaration.Good.eq_4 Declaration.Good.eq_5 Declaration.Good.eq_6 Declaration.Good.eq_7

/-! ## Environments -/

/-- **Rename an environment**: every stored constant. -/
def Env.mapKeys (f : md.Id → md'.Id) (env : Env md) : Env md' :=
  ⟨env.consts.map (ConstantInfo.mapKeys f)⟩

/-- A good environment: every stored constant is good. -/
abbrev Env.Good (P : KeyScope md) (env : Env md) : Prop := ∀ c ∈ env.consts, c.Good P

/-- **Lookup in a renamed environment** of a good key: the renamed lookup,
when the environment is good and the renaming is injective on it. -/
theorem Env.find?_mapKeys {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {env : Env md} (henv : env.Good P) {k : Key md} (hk : k.Good P) :
    (env.mapKeys f).find? (k.map f) = (env.find? k).map (ConstantInfo.mapKeys f) := by
  obtain ⟨cs⟩ := env
  simp only [Env.find?, Env.mapKeys]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [Env.Good, List.mem_cons, forall_eq_or_imp] at henv
    simp only [List.map_cons, List.find?_cons, ConstantInfo.mapKeys_name]
    rw [Key.map_beq hf henv.1.name hk]
    cases (c.name == k) <;> simp [ih henv.2]

/-- A lookup in a good environment finds a good constant. -/
theorem Env.Good.find? {P : KeyScope md} {env : Env md} (henv : env.Good P) {k : Key md}
    {c : ConstantInfo md} (h : env.find? k = some c) : c.Good P :=
  henv c (List.mem_of_find?_eq_some h)

/-! ## Evidence -/

/-- Rename one evidence entry: a proof's theorem key and its proof term. -/
def Evidence.mapKeys (f : md.Id → md'.Id) :
    Evidence (Key md × Expr md) → Evidence (Key md' × Expr md')
  | .defeq => .defeq
  | .proof (k, v) => .proof (k.map f, v.mapKeys f)

def Evidence.Good (P : KeyScope md) : Evidence (Key md × Expr md) → Prop
  | .defeq => True
  | .proof (k, v) => k.Good P ∧ v.Good P

attribute [simp] Evidence.mapKeys.eq_1 Evidence.mapKeys.eq_2 Evidence.Good.eq_1 Evidence.Good.eq_2

/-- **Rename the fold's evidence**: roles are fixed, their entries renamed. -/
def Evidences.mapKeys (f : md.Id → md'.Id) (ev : Evidences md) : Evidences md' :=
  ev.map fun (r, es) => (r, es.map (Evidence.mapKeys f))

/-- Good evidence: every entry is good. -/
abbrev Evidences.Good (P : KeyScope md) (ev : Evidences md) : Prop :=
  ∀ p ∈ ev, ∀ e ∈ p.2, e.Good P

/-- A role's evidence, renamed. -/
theorem Evidences.mapKeys_of (f : md.Id → md'.Id) (ev : Evidences md) (r : Role) :
    (ev.mapKeys f).of r = (ev.of r).map (Evidence.mapKeys f) := by
  simp only [Evidences.of, Evidences.mapKeys]
  induction ev with
  | nil => rfl
  | cons p ev ih =>
    obtain ⟨r', es⟩ := p
    simp only [List.map_cons, List.find?_cons]
    cases h : (r' == r) <;> simp_all

theorem Evidences.Good.of {P : KeyScope md} {ev : Evidences md} (h : ev.Good P) (r : Role) :
    ∀ e ∈ ev.of r, e.Good P := by
  simp only [Evidences.of]
  cases hf : ev.find? (·.1 == r) with
  | none => simp
  | some p =>
    obtain ⟨r', es⟩ := p
    exact h _ (List.mem_of_find?_eq_some hf)

end Ix.Kernel
