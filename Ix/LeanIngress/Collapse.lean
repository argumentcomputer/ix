module

public import Ix.Ixon
public import Ix.LeanIngress.Expr
public import IxC.Kernel.Env
public import IxC.Kernel.Tier.Basic

@[expose] public section

/-! # Quotient Source: alias fibers collapsed (`ALPHA-COLLAPSE.md` §8.4)

Lean names constants; Ix addresses them by content. Two Lean constants whose
content agrees once their references are identified (an *alias fiber*) are one
constant to Ixon. **Quotient Source** checks a Lean environment with every
fiber collapsed to one representative: the lowered declarations are renamed so
that every key of a fiber becomes the fiber's representative (`substKeys`),
and of the declarations that become equal only the first is kept
(`collapseDecls`). A dropped declaration must be the kept one after renaming
— `FiberHyp`, checked here decidably (`Declaration.beqF`) for every drop; a
declaration whose renamed form meets an earlier declaration without equalling
it is refused (`CollapseError.mismatch`), so no fiber is ever trusted.

**The fibers** are data, and verified: any fiber map may be given, since a
wrong one only produces a refusal. `fiberAlias` reads them off a compiled
artifact (the published names sharing an address); Source's own content keys
would serve equally.

**Role-aware representatives** (§8.4, B5c option (i)): a fiber that holds a
role's Lean name is represented by the role's key (`.role r`), so Source runs
the role's validation on every alias of a role constant, exactly as Ixon does
for an address its role table binds. A fiber holding two roles' names is not
collapsed (no Init+Std fiber does; collapsing it would identify two roles).

**Grouping is unchanged**: the ingress still groups definitions by strongly
connected component (`Ix.LeanIngress.componentGroup`); a fiber may span
groups, and is collapsed like any other (the two partial
`Std.Http.Protocol.H1.Machine` handler fibers are each their own component).
-/

set_option linter.unusedSimpArgs false

namespace Ix.LeanIngress

open Ix.Kernel

/-! ## Renaming keys to their representatives -/

/-- A fiber map: the representative key of an input id that is not its own
representative. -/
abbrev FiberMap := Std.HashMap Ix.Kernel.Name (Ix.Kernel.Key .source)

/-- A key's representative: an input id by the map, a derived key through its
base; a role key is fixed. -/
def Key.subst (ρ : FiberMap) : Ix.Kernel.Key .source → Ix.Kernel.Key .source
  | .id n => ρ[n]?.getD (.id n)
  | .role r => .role r
  | .aux k d => .aux (Key.subst ρ k) d

/-- Rename every key of a term (constants and projections' structures). -/
def Expr.substKeys (ρ : FiberMap) : Ix.Kernel.Expr .source → Ix.Kernel.Expr .source
  | .bvar i => .bvar i
  | .fvar i ty => .fvar i (Expr.substKeys ρ ty)
  | .sort u => .sort u
  | .const n us => .const (Key.subst ρ n) us
  | .app f a => .app (Expr.substKeys ρ f) (Expr.substKeys ρ a)
  | .lam ty b m => .lam (Expr.substKeys ρ ty) (Expr.substKeys ρ b) m
  | .forallE ty b m => .forallE (Expr.substKeys ρ ty) (Expr.substKeys ρ b) m
  | .letE t v b l => .letE (Expr.substKeys ρ t) (Expr.substKeys ρ v) (Expr.substKeys ρ b) l
  | .lit l => .lit l
  | .proj s i e => .proj (Key.subst ρ s) i (Expr.substKeys ρ e)

/-! ### `Expr.substKeys`, memoised

The pure walk above rebuilds a DAG-shared term as a tree. The memoised walk
below, keyed by the node (the cached data word and `Expr.beq`, whose first test
is pointer equality), visits each distinct subterm once; it is swapped in by
`@[csimp]`, on `substKeysGo_spec`, as the kernel's `renameConsts` is. -/

/-- The memo's invariant: every recorded answer is the real one. -/
def SubstMemoInv (ρ : FiberMap) (memo : Std.HashMap (Ix.Kernel.Expr .source) (Ix.Kernel.Expr .source)) :
    Prop :=
  ∀ k v, memo[k]? = some v → v = Expr.substKeys ρ k

theorem SubstMemoInv.empty {ρ : FiberMap} : SubstMemoInv ρ {} := by
  intro k v h; simp at h

theorem SubstMemoInv.insert {ρ : FiberMap}
    {memo : Std.HashMap (Ix.Kernel.Expr .source) (Ix.Kernel.Expr .source)}
    (hm : SubstMemoInv ρ memo) {e r : Ix.Kernel.Expr .source} (heq : r = Expr.substKeys ρ e) :
    SubstMemoInv ρ (memo.insert e r) := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k v hk

/-- Memoised `Expr.substKeys`. -/
def Expr.substKeysGo (ρ : FiberMap) (memo : Std.HashMap (Ix.Kernel.Expr .source) (Ix.Kernel.Expr .source)) :
    Ix.Kernel.Expr .source → Ix.Kernel.Expr .source × Std.HashMap (Ix.Kernel.Expr .source) (Ix.Kernel.Expr .source)
  | e@(.bvar _) => (e, memo)
  | e@(.sort _) => (e, memo)
  | e@(.lit _) => (e, memo)
  | .const n us => (.const (Key.subst ρ n) us, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Ix.Kernel.Expr .source × Std.HashMap (Ix.Kernel.Expr .source) (Ix.Kernel.Expr .source) :=
        match e with
        | .fvar i ty =>
          let (t, memo) := Expr.substKeysGo ρ memo ty
          (.fvar i t, memo)
        | .app a b =>
          let (a', memo) := Expr.substKeysGo ρ memo a
          let (b', memo) := Expr.substKeysGo ρ memo b
          (.app a' b', memo)
        | .lam ty body m =>
          let (t, memo) := Expr.substKeysGo ρ memo ty
          let (b, memo) := Expr.substKeysGo ρ memo body
          (.lam t b m, memo)
        | .forallE ty body m =>
          let (t, memo) := Expr.substKeysGo ρ memo ty
          let (b, memo) := Expr.substKeysGo ρ memo body
          (.forallE t b m, memo)
        | .letE ty v body l =>
          let (t, memo) := Expr.substKeysGo ρ memo ty
          let (v', memo) := Expr.substKeysGo ρ memo v
          let (b, memo) := Expr.substKeysGo ρ memo body
          (.letE t v' b l, memo)
        | .proj s i sub =>
          let (u, memo) := Expr.substKeysGo ρ memo sub
          (.proj (Key.subst ρ s) i u, memo)
        | e => (e, memo)
      (r, memo.insert e r)

/-- **The memoised walk is `Expr.substKeys`.** -/
theorem Expr.substKeysGo_spec {ρ : FiberMap} :
    ∀ (e : Ix.Kernel.Expr .source) {memo : Std.HashMap (Ix.Kernel.Expr .source) (Ix.Kernel.Expr .source)},
      SubstMemoInv ρ memo →
      (Expr.substKeysGo ρ memo e).1 = Expr.substKeys ρ e ∧
        SubstMemoInv ρ (Expr.substKeysGo ρ memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty ih =>
    intro memo hm
    rw [Expr.substKeysGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih hm
      refine ⟨by simp [Expr.substKeys, h1], ?_⟩
      exact h2.insert (by simp [Expr.substKeys, h1])
  | app a b iha ihb =>
    intro memo hm
    rw [Expr.substKeysGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [Expr.substKeys, h1, h3], ?_⟩
      exact h4.insert (by simp [Expr.substKeys, h1, h3])
  | lam ty body m iht ihb =>
    intro memo hm
    rw [Expr.substKeysGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [Expr.substKeys, h1, h3], ?_⟩
      exact h4.insert (by simp [Expr.substKeys, h1, h3])
  | forallE ty body m iht ihb =>
    intro memo hm
    rw [Expr.substKeysGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [Expr.substKeys, h1, h3], ?_⟩
      exact h4.insert (by simp [Expr.substKeys, h1, h3])
  | letE ty v body _ iht ihv ihb =>
    intro memo hm
    rw [Expr.substKeysGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihv h2
      obtain ⟨h5, h6⟩ := ihb h4
      refine ⟨by simp [Expr.substKeys, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [Expr.substKeys, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [Expr.substKeysGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih hm
      refine ⟨by simp [Expr.substKeys, h1], ?_⟩
      exact h2.insert (by simp [Expr.substKeys, h1])

/-- The executed `Expr.substKeys` (one memoised DAG walk). -/
def Expr.substKeysFast (ρ : FiberMap) (e : Ix.Kernel.Expr .source) : Ix.Kernel.Expr .source :=
  (Expr.substKeysGo ρ {} e).1

@[csimp] theorem Expr.substKeys_eq_substKeysFast :
    @Expr.substKeys = @Expr.substKeysFast := by
  funext ρ e
  exact (Expr.substKeysGo_spec e SubstMemoInv.empty).1.symm

def ConstantVal.substKeys (ρ : FiberMap) (cv : Ix.Kernel.ConstantVal .source) : Ix.Kernel.ConstantVal .source :=
  { cv with name := Key.subst ρ cv.name, type := Expr.substKeys ρ cv.type }

def RecRuleFire.substKeys (ρ : FiberMap) : Ix.Kernel.RecRuleFire .source → Ix.Kernel.RecRuleFire .source
  | .inert => .inert
  | .plain => .plain
  | .nested lvls pins => .nested lvls (pins.map (Expr.substKeys ρ))

def RecRule.substKeys (ρ : FiberMap) (r : Ix.Kernel.RecRule .source) : Ix.Kernel.RecRule .source :=
  { r with ctor := Key.subst ρ r.ctor, fire := RecRuleFire.substKeys ρ r.fire,
           rhs := Expr.substKeys ρ r.rhs }

def IndCaps.substKeys (ρ : FiberMap) (c : Ix.Kernel.IndCaps .source) : Ix.Kernel.IndCaps .source :=
  { c with etaCtor := c.etaCtor.map (Key.subst ρ) }

def ProjTable.substKeys (ρ : FiberMap) (t : Ix.Kernel.ProjTable .source) : Ix.Kernel.ProjTable .source :=
  { t with structName := Key.subst ρ t.structName, ctor := Key.subst ρ t.ctor,
           bodies := t.bodies.map (Expr.substKeys ρ) }

def ConstantInfo.substKeys (ρ : FiberMap) : Ix.Kernel.ConstantInfo .source → Ix.Kernel.ConstantInfo .source
  | .axiomInfo v => .axiomInfo (ConstantVal.substKeys ρ v)
  | .defnInfo v e h => .defnInfo (ConstantVal.substKeys ρ v) (Expr.substKeys ρ e) h
  | .thmInfo v e => .thmInfo (ConstantVal.substKeys ρ v) (Expr.substKeys ρ e)
  | .indInfo v caps => .indInfo (ConstantVal.substKeys ρ v) (IndCaps.substKeys ρ caps)
  | .ctorInfo v nP nF => .ctorInfo (ConstantVal.substKeys ρ v) nP nF
  | .recInfo v mI rP rules =>
    .recInfo (ConstantVal.substKeys ρ v) mI rP (rules.map (RecRule.substKeys ρ))
  | .projInfo t => .projInfo (ProjTable.substKeys ρ t)

/-- **Rename a declaration's keys to their representatives.** -/
def Declaration.substKeys (ρ : FiberMap) : Ix.Kernel.Declaration .source → Ix.Kernel.Declaration .source
  | .axiomDecl v => .axiomDecl (ConstantVal.substKeys ρ v)
  | .defnDecl v e h => .defnDecl (ConstantVal.substKeys ρ v) (Expr.substKeys ρ e) h
  | .thmDecl v e => .thmDecl (ConstantVal.substKeys ρ v) (Expr.substKeys ρ e)
  | .opaqueDecl v e => .opaqueDecl (ConstantVal.substKeys ρ v) (Expr.substKeys ρ e)
  | .basisDecl k => .basisDecl k
  | .indDecl block nP => .indDecl (block.map (ConstantInfo.substKeys ρ)) nP
  | .quotDecl k v => .quotDecl k (ConstantVal.substKeys ρ v)

/-- Rename a typing-tier declaration's keys (`partial` and `unsafe` groups,
checked by the tier against the logical environment). -/
def TierDecl.substKeys (ρ : FiberMap) : Ix.Kernel.Tier.TierDecl .source → Ix.Kernel.Tier.TierDecl .source
  | .defs s ms => .defs s (ms.map fun (cv, v) => (ConstantVal.substKeys ρ cv, Expr.substKeys ρ v))
  | .unsafeOpaque cv v => .unsafeOpaque (ConstantVal.substKeys ρ cv) (Expr.substKeys ρ v)
  | .unsafeAxiom cv => .unsafeAxiom (ConstantVal.substKeys ρ cv)

/-! ## Comparing declarations

`decide (d₁ = d₂)` on declarations compares their terms structurally, which
on a DAG-shared term is a tree walk. `Declaration.beqF` compares the terms with
`Expr.beq` (the memoised comparison) and everything else structurally; it is
`decide (d₁ = d₂)` (`Declaration.beqF_eq`). -/

def ConstantVal.beqF (a b : Ix.Kernel.ConstantVal .source) : Bool :=
  decide (a.name = b.name) && decide (a.levelParams = b.levelParams) && Ix.Kernel.Expr.beq a.type b.type

def Expr.listBeqF : List (Ix.Kernel.Expr .source) → List (Ix.Kernel.Expr .source) → Bool
  | [], [] => true
  | a :: as, b :: bs => Ix.Kernel.Expr.beq a b && Expr.listBeqF as bs
  | _, _ => false

def RecRuleFire.beqF : Ix.Kernel.RecRuleFire .source → Ix.Kernel.RecRuleFire .source → Bool
  | .inert, .inert => true
  | .plain, .plain => true
  | .nested l ps, .nested l' ps' => decide (l = l') && Expr.listBeqF ps ps'
  | _, _ => false

def RecRule.beqF (a b : Ix.Kernel.RecRule .source) : Bool :=
  decide (a.ctor = b.ctor) && decide (a.nfields = b.nfields) &&
    decide (a.ctorParams = b.ctorParams) && RecRuleFire.beqF a.fire b.fire &&
    Ix.Kernel.Expr.beq a.rhs b.rhs && decide (a.k = b.k) && decide (a.eta = b.eta) &&
    decide (a.paramsBlind = b.paramsBlind)

def RecRule.listBeqF : List (Ix.Kernel.RecRule .source) → List (Ix.Kernel.RecRule .source) → Bool
  | [], [] => true
  | a :: as, b :: bs => RecRule.beqF a b && RecRule.listBeqF as bs
  | _, _ => false

def ProjTable.beqF (a b : Ix.Kernel.ProjTable .source) : Bool :=
  decide (a.structName = b.structName) && decide (a.levelParams = b.levelParams) &&
    decide (a.numParams = b.numParams) && decide (a.ctor = b.ctor) &&
    decide (a.numFields = b.numFields) && decide (a.structSort = b.structSort) &&
    Expr.listBeqF a.bodies.toList b.bodies.toList && decide (a.guards = b.guards) &&
    decide (a.off = b.off)

def ConstantInfo.beqF : Ix.Kernel.ConstantInfo .source → Ix.Kernel.ConstantInfo .source → Bool
  | .axiomInfo v, .axiomInfo v' => ConstantVal.beqF v v'
  | .defnInfo v e h, .defnInfo v' e' h' => ConstantVal.beqF v v' && Ix.Kernel.Expr.beq e e' && decide (h = h')
  | .thmInfo v e, .thmInfo v' e' => ConstantVal.beqF v v' && Ix.Kernel.Expr.beq e e'
  | .indInfo v c, .indInfo v' c' => ConstantVal.beqF v v' && decide (c = c')
  | .ctorInfo v p f, .ctorInfo v' p' f' => ConstantVal.beqF v v' && decide (p = p') && decide (f = f')
  | .recInfo v m r rs, .recInfo v' m' r' rs' =>
    ConstantVal.beqF v v' && decide (m = m') && decide (r = r') && RecRule.listBeqF rs rs'
  | .projInfo t, .projInfo t' => ProjTable.beqF t t'
  | _, _ => false

def ConstantInfo.listBeqF : List (Ix.Kernel.ConstantInfo .source) → List (Ix.Kernel.ConstantInfo .source) → Bool
  | [], [] => true
  | a :: as, b :: bs => ConstantInfo.beqF a b && ConstantInfo.listBeqF as bs
  | _, _ => false

/-- Two typing-tier declarations are equal (the memoised term comparison). -/
def TierDecl.beqF : Ix.Kernel.Tier.TierDecl .source → Ix.Kernel.Tier.TierDecl .source → Bool
  | .defs s ms, .defs s' ms' =>
    decide (s = s') && ms.length == ms'.length &&
      (ms.zip ms').all fun ((cv, v), (cv', v')) => ConstantVal.beqF cv cv' && Ix.Kernel.Expr.beq v v'
  | .unsafeOpaque cv v, .unsafeOpaque cv' v' => ConstantVal.beqF cv cv' && Ix.Kernel.Expr.beq v v'
  | .unsafeAxiom cv, .unsafeAxiom cv' => ConstantVal.beqF cv cv'
  | _, _ => false

/-- The names a typing-tier declaration declares. -/
def TierDecl.names : Ix.Kernel.Tier.TierDecl .source → List (Ix.Kernel.Key .source)
  | .defs _ ms => ms.map (·.1.name)
  | .unsafeOpaque cv _ => [cv.name]
  | .unsafeAxiom cv => [cv.name]

/-- **The declarations are equal**, deciding `d₁ = d₂` with the memoised term
comparison. -/
def Declaration.beqF : Ix.Kernel.Declaration .source → Ix.Kernel.Declaration .source → Bool
  | .axiomDecl v, .axiomDecl v' => ConstantVal.beqF v v'
  | .defnDecl v e h, .defnDecl v' e' h' => ConstantVal.beqF v v' && Ix.Kernel.Expr.beq e e' && decide (h = h')
  | .thmDecl v e, .thmDecl v' e' => ConstantVal.beqF v v' && Ix.Kernel.Expr.beq e e'
  | .opaqueDecl v e, .opaqueDecl v' e' => ConstantVal.beqF v v' && Ix.Kernel.Expr.beq e e'
  | .basisDecl k, .basisDecl k' => decide (k = k')
  | .indDecl b n, .indDecl b' n' => ConstantInfo.listBeqF b b' && decide (n = n')
  | .quotDecl k v, .quotDecl k' v' => decide (k = k') && ConstantVal.beqF v v'
  | _, _ => false

theorem ConstantVal.beqF_eq (a b : Ix.Kernel.ConstantVal .source) : ConstantVal.beqF a b = decide (a = b) := by
  obtain ⟨n, l, t⟩ := a; obtain ⟨n', l', t'⟩ := b
  simp [ConstantVal.beqF, Ix.Kernel.Expr.beq, Ix.Kernel.ConstantVal.mk.injEq, Bool.and_eq_true, and_assoc, Bool.and_assoc]

theorem Expr.listBeqF_eq : ∀ (as bs : List (Ix.Kernel.Expr .source)), Expr.listBeqF as bs = decide (as = bs)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    simp [Expr.listBeqF, Ix.Kernel.Expr.beq, Expr.listBeqF_eq as bs, Bool.and_eq_true, Bool.and_assoc]

theorem RecRuleFire.beqF_eq (a b : Ix.Kernel.RecRuleFire .source) : RecRuleFire.beqF a b = decide (a = b) := by
  cases a <;> cases b <;> simp [RecRuleFire.beqF, Expr.listBeqF_eq, Bool.and_eq_true, Bool.and_assoc]

theorem RecRule.beqF_eq (a b : Ix.Kernel.RecRule .source) : RecRule.beqF a b = decide (a = b) := by
  obtain ⟨c, nf, cp, fi, rhs, k, e, pb⟩ := a; obtain ⟨c', nf', cp', fi', rhs', k', e', pb'⟩ := b
  simp [RecRule.beqF, RecRuleFire.beqF_eq, Ix.Kernel.Expr.beq, Ix.Kernel.RecRule.mk.injEq, Bool.and_eq_true, and_assoc, Bool.and_assoc]

theorem RecRule.listBeqF_eq : ∀ (as bs : List (Ix.Kernel.RecRule .source)),
    RecRule.listBeqF as bs = decide (as = bs)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    simp [RecRule.listBeqF, RecRule.beqF_eq, RecRule.listBeqF_eq as bs, Bool.and_eq_true, Bool.and_assoc]

theorem ProjTable.beqF_eq (a b : Ix.Kernel.ProjTable .source) : ProjTable.beqF a b = decide (a = b) := by
  obtain ⟨s, l, np, c, nf, ss, bs, g, o⟩ := a; obtain ⟨s', l', np', c', nf', ss', bs', g', o'⟩ := b
  simp [ProjTable.beqF, Expr.listBeqF_eq, Ix.Kernel.ProjTable.mk.injEq, Bool.and_eq_true, and_assoc, Bool.and_assoc,
    Array.toList_inj]

theorem ConstantInfo.beqF_eq (a b : Ix.Kernel.ConstantInfo .source) :
    ConstantInfo.beqF a b = decide (a = b) := by
  cases a <;> cases b <;>
    simp [ConstantInfo.beqF, ConstantVal.beqF_eq, RecRule.listBeqF_eq, ProjTable.beqF_eq, Ix.Kernel.Expr.beq,
      Bool.and_eq_true, and_assoc, Bool.and_assoc]

theorem ConstantInfo.listBeqF_eq : ∀ (as bs : List (Ix.Kernel.ConstantInfo .source)),
    ConstantInfo.listBeqF as bs = decide (as = bs)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    simp [ConstantInfo.listBeqF, ConstantInfo.beqF_eq, ConstantInfo.listBeqF_eq as bs,
      Bool.and_eq_true, Bool.and_assoc]

theorem Declaration.beqF_eq (a b : Ix.Kernel.Declaration .source) : Declaration.beqF a b = decide (a = b) := by
  cases a <;> cases b <;>
    simp [Declaration.beqF, ConstantVal.beqF_eq, ConstantInfo.listBeqF_eq, Ix.Kernel.Expr.beq,
      Bool.and_eq_true, and_assoc, Bool.and_assoc]

/-! ## Collapsing -/

/-- Why a collapse refuses: a declaration whose renamed form declares a name an
earlier declaration declares, without being that declaration. -/
inductive CollapseError where
  | mismatch (name : Ix.Kernel.Key .source) (representative : Ix.Kernel.Key .source)
  deriving Repr

instance : ToString CollapseError where
  toString
    | .mismatch n r => s!"alias fiber mismatch: {n} renames to {r}, which an unequal declaration declares"

/-- What a collapse keeps: the renamed declarations, one per fiber, and for every
dropped declaration's names their representatives. -/
structure Collapsed where
  decls : Array (Ix.Kernel.Declaration .source)
  /-- each dropped name, with the representative its fiber's kept declaration declares -/
  dropped : Array (Ix.Kernel.Key .source × Ix.Kernel.Key .source) := #[]

/-- **The collapse** (`FiberHyp`, decided): rename every declaration by `ρ`, in
order; a renamed declaration none of whose names is declared yet is kept; one
whose every name an earlier kept declaration declares, and which is that
declaration, is dropped; anything else is refused. -/
def collapseDecls (ρ : FiberMap) (ds : Array (Ix.Kernel.Declaration .source)) :
    Except CollapseError Collapsed := do
  let mut kept : Array (Ix.Kernel.Declaration .source) := #[]
  let mut owner : Std.HashMap (Ix.Kernel.Key .source) Nat := {}
  let mut dropped : Array (Ix.Kernel.Key .source × Ix.Kernel.Key .source) := #[]
  for d in ds do
    let d' := Declaration.substKeys ρ d
    let ns := d'.names
    match ns.findSome? (owner[·]?) with
    | none =>
      for n in ns do owner := owner.insert n kept.size
      kept := kept.push d'
    | some k =>
      let first := d.names.head?.getD (.id .anonymous)
      let rep := ns.head?.getD (.id .anonymous)
      unless ns.all (owner[·]? == some k) && Declaration.beqF d' kept[k]! do
        throw (.mismatch first rep)
      dropped := dropped ++ (d.names.zip ns).toArray
  return { decls := kept, dropped }

/-! ## The artifact's fibers -/

/-- **The alias fibers of a compiled artifact**, role-aware: the published
names sharing an address form a fiber; its representative is the key of the
role whose Lean name it holds, or else the key of its least name (Lean's name
order of their spellings, for determinism); a fiber holding two roles' names is left
alone. Every member that is
not its own representative is mapped. -/
def fiberAliasMap (ixe : Ixon.Env) : FiberMap := Id.run do
  let mut byAddr : Std.HashMap Address (Array Ix.Name) := {}
  for (n, named) in ixe.named.toList do
    byAddr := byAddr.insert named.addr ((byAddr.getD named.addr #[]).push n)
  let mut m : Std.HashMap Ix.Kernel.Name (Ix.Kernel.Key .source) := {}
  for (_, names) in byAddr.toList do
    if names.size < 2 then continue
    let keys := names.map ingressKey
    let roles := keys.filter fun k => match k with | .role _ => true | _ => false
    if roles.size > 1 then continue
    let least := (names.qsort fun a b => toString (ingressName a) < toString (ingressName b))[0]!
    let rep := roles[0]?.getD (ingressKey least)
    for n in names do
      let k := ingressKey n
      if k != rep then
        match k with
        | .id i => m := m.insert i rep
        | _ => pure ()
  return m

/-- The fiber map of an artifact (`fiberAliasMap`). -/
def fiberAlias (ixe : Ixon.Env) : FiberMap := fiberAliasMap ixe

end Ix.LeanIngress
