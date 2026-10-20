module

public import Ix.Ixon
public import Ix.LeanIngress.Expr
public import IxC.Kernel.Env
public import IxC.Kernel.Tier.Basic
public import IxC.Kernel.Ixon.RoleTable
import IxC.Kernel.Ingress.Records

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
The rule is by name: a fiber holding a role's content but not the role's name
(a closure without `Bool` that holds an enum ≅ `Bool`) keeps a user key where
Ixon's table binds the role, which leaves such a closure outside the renaming
(coverage, not soundness); a content rule (meets role r's spec ⇒ `.role r`)
would close it.

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
earlier declaration declares, without being that declaration; and, at an
artifact (`prepareSourceCollapsedAt`), a prepared stream or evidence that names
a key the artifact does not represent. -/
inductive CollapseError where
  | mismatch (name : Ix.Kernel.Key .source) (representative : Ix.Kernel.Key .source)
  /-- a prepared declaration names a key that is not a representative of the artifact's
  (`prepareSourceCollapsedAt`'s check) -/
  | notRepresentative
  /-- the bundle's evidence names a key that is neither a representative nor a
  bundle-only name -/
  | evidence
  /-- a bundle-only name's name hash is an address the artifact publishes
  (`bundleDisjointB`) -/
  | bundleAlias
  deriving Repr

instance : ToString CollapseError where
  toString
    | .mismatch n r => s!"alias fiber mismatch: {n} renames to {r}, which an unequal declaration declares"
    | .notRepresentative => "a prepared declaration names a key that is not a representative"
    | .evidence => "the bundle's evidence names a key that is neither a representative nor bundle-only"
    | .bundleAlias => "a bundle-only name's name hash is an address the artifact publishes"

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

/-! ## The artifact's fibers

The fibers of a compiled artifact are its address classes: the published
names (as Source names) at each address. `fiberAliasMap` is built in four
steps that each say one thing (`sourceAddrs`, `fiberMembers`, `fiberRep`,
`aliasEntry`), so that its one property the statements need — **two names at
one address are renamed to one key** (`fiberAlias_addr_inj`), i.e. distinct
representatives have distinct addresses — is a lemma rather than a check. -/

/-- **The address of each published name**, keyed by its Source name. -/
def sourceAddrs (ixe : Ixon.Env) : Std.HashMap Ix.Kernel.Name Address :=
  ixe.named.fold (fun m n d => m.insert (ingressName n) d.addr) {}

/-- One step of `fiberMembers`: file a name under its address. -/
def fiberMembersStep (m : Std.HashMap Address (List Ix.Kernel.Name))
    (p : Ix.Kernel.Name × Address) : Std.HashMap Address (List Ix.Kernel.Name) :=
  m.insert p.2 (p.1 :: m.getD p.2 [])

/-- **The fibers**: the names at each address. -/
def fiberMembers (addrs : Std.HashMap Ix.Kernel.Name Address) :
    Std.HashMap Address (List Ix.Kernel.Name) :=
  addrs.toList.foldl fiberMembersStep {}

/-- The role a Source name is bound to (`Key.ofName`), if any. -/
def roleOf (i : Ix.Kernel.Name) : Option Ix.Kernel.Role :=
  match Ix.Kernel.Key.ofName i with
  | .role r => some r
  | _ => none

/-- The least of a list of names by spelling (only for determinism). -/
def leastName : Ix.Kernel.Name → List Ix.Kernel.Name → Ix.Kernel.Name
  | b, [] => b
  | b, x :: xs => leastName (if toString x < toString b then x else b) xs

/-- **A fiber's representative**: the key of the role whose name it holds,
else the key of its least name; none for a fiber holding two roles' names. -/
def fiberRep : List Ix.Kernel.Name → Option (Ix.Kernel.Key .source)
  | [] => none
  | n :: ns =>
    match (n :: ns).filterMap roleOf with
    | [] => some (.id (leastName n ns))
    | r :: rs => if rs.all (fun r' => decide (r' = r)) then some (.role r) else none

/-- A name's entry in the fiber map: its fiber's representative, unless the
name is a role's (a role key is never renamed) or is the representative. -/
def aliasEntry (reps : Std.HashMap Address (Option (Ix.Kernel.Key .source)))
    (p : Ix.Kernel.Name × Address) : Option (Ix.Kernel.Name × Ix.Kernel.Key .source) :=
  match reps[p.2]? with
  | some (some rep) =>
    if roleOf p.1 = none ∧ Ix.Kernel.Key.ofName p.1 ≠ rep then some (p.1, rep) else none
  | _ => none

/-- **The alias fibers of a compiled artifact**, role-aware: the published
names sharing an address form a fiber; its representative is the key of the
role whose Lean name it holds, or else the key of its least name (by
spelling, for determinism); a fiber holding two roles' names is left alone.
Every member that is not its own representative is mapped. -/
def fiberAliasMap (ixe : Ixon.Env) : FiberMap :=
  let addrs := sourceAddrs ixe
  let reps := (fiberMembers addrs).map fun _ ns => fiberRep ns
  Std.HashMap.ofList (addrs.toList.filterMap (aliasEntry reps))

/-- The fiber map of an artifact (`fiberAliasMap`). -/
def fiberAlias (ixe : Ixon.Env) : FiberMap := fiberAliasMap ixe

/-! ### Distinct representatives have distinct addresses -/

theorem fiberMembers_foldl_mem {k : Ix.Kernel.Name} {a : Address} :
    ∀ (l : List (Ix.Kernel.Name × Address)) (init : Std.HashMap Address (List Ix.Kernel.Name)),
      k ∈ (l.foldl fiberMembersStep init).getD a [] ↔ k ∈ init.getD a [] ∨ (k, a) ∈ l
  | [], init => by simp
  | (i, b) :: l, init => by
    rw [List.foldl_cons, fiberMembers_foldl_mem l]
    simp only [fiberMembersStep, Std.HashMap.getD_insert, List.mem_cons, Prod.mk.injEq]
    by_cases h : b = a
    · subst h
      simp only [beq_self_eq_true, ite_true, List.mem_cons, and_true]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    · have hb : (b == a) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ite_false]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | ⟨_, h'⟩ | h)
        · exact Or.inl h
        · exact absurd h'.symm h
        · exact Or.inr h

/-- A name is in its address's fiber, and only there. -/
theorem mem_fiberMembers {addrs : Std.HashMap Ix.Kernel.Name Address} {k : Ix.Kernel.Name}
    {a : Address} : k ∈ (fiberMembers addrs).getD a [] ↔ addrs[k]? = some a := by
  rw [fiberMembers, fiberMembers_foldl_mem, Std.HashMap.getD_empty,
    Std.HashMap.mem_toList_iff_getElem?_eq_some]
  simp

theorem roleOf_eq_none {i : Ix.Kernel.Name} (h : roleOf i = none) :
    Ix.Kernel.Key.ofName i = .id i := by
  unfold roleOf at h
  unfold Ix.Kernel.Key.ofName at h ⊢
  cases hb : Ix.Kernel.Role.byLeanName[i]? <;> simp_all

theorem roleOf_eq_some {i : Ix.Kernel.Name} {r : Ix.Kernel.Role} (h : roleOf i = some r) :
    Ix.Kernel.Key.ofName i = .role r := by
  unfold roleOf at h
  unfold Ix.Kernel.Key.ofName at h ⊢
  cases hb : Ix.Kernel.Role.byLeanName[i]? <;> simp_all

theorem leastName_mem : ∀ (b : Ix.Kernel.Name) (xs : List Ix.Kernel.Name),
    leastName b xs ∈ b :: xs
  | b, [] => by simp [leastName]
  | b, x :: xs => by
    show leastName (if toString x < toString b then x else b) xs ∈ b :: x :: xs
    by_cases hc : toString x < toString b
    · have ih := leastName_mem x xs
      rw [ite_eq_left hc]
      rcases List.mem_cons.mp ih with h | h
      · rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
    · have ih := leastName_mem b xs
      rw [ite_eq_right hc]
      rcases List.mem_cons.mp ih with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- A fiber whose role names all name one role has a representative. -/
theorem fiberRep_isSome {l : List Ix.Kernel.Name} (hne : l ≠ [])
    (hroles : ∀ x y r₁ r₂, x ∈ l → y ∈ l → roleOf x = some r₁ → roleOf y = some r₂ → r₁ = r₂) :
    ∃ rep, fiberRep l = some rep := by
  match l, hne with
  | n :: ns, _ =>
    simp only [fiberRep]
    split
    · exact ⟨_, rfl⟩
    · next r rs hf =>
      have hr : r ∈ (n :: ns).filterMap roleOf := hf ▸ List.mem_cons_self ..
      obtain ⟨x, hx, hxr⟩ := List.mem_filterMap.mp hr
      have hall : (rs.all fun r' => decide (r' = r)) = true := by
        refine List.all_eq_true.mpr fun r' hr' => decide_eq_true ?_
        have hr'' : r' ∈ (n :: ns).filterMap roleOf := hf ▸ List.mem_cons_of_mem _ hr'
        obtain ⟨y, hy, hyr⟩ := List.mem_filterMap.mp hr''
        exact hroles y x r' r hy hx hyr hxr
      exact ⟨_, ite_eq_left hall⟩

/-- A role name in a fiber with a representative: the representative is that
role's key. -/
theorem fiberRep_role {l : List Ix.Kernel.Name} {x : Ix.Kernel.Name} {r : Ix.Kernel.Role}
    {rep : Ix.Kernel.Key .source} (hx : x ∈ l) (hxr : roleOf x = some r)
    (h : fiberRep l = some rep) : rep = .role r := by
  have hm : r ∈ l.filterMap roleOf := List.mem_filterMap.mpr ⟨x, hx, hxr⟩
  match l, hx with
  | n :: ns, _ =>
    simp only [fiberRep] at h
    split at h
    · next hf => rw [hf] at hm; cases hm
    · next r₀ rs hf =>
      rw [hf] at hm
      split at h
      · next hall =>
        cases h
        rcases List.mem_cons.mp hm with rfl | hm'
        · rfl
        · have := List.all_eq_true.mp hall _ hm'
          simp only [decide_eq_true_eq] at this
          rw [this]
      · cases h

/-- A fiber's representative is the key of one of its names. -/
theorem fiberRep_mem {l : List Ix.Kernel.Name} {rep : Ix.Kernel.Key .source}
    (h : fiberRep l = some rep) : ∃ k ∈ l, Ix.Kernel.Key.ofName k = rep := by
  match l with
  | [] => simp [fiberRep] at h
  | n :: ns =>
    simp only [fiberRep] at h
    split at h
    · next hf =>
      cases h
      refine ⟨leastName n ns, leastName_mem n ns, roleOf_eq_none ?_⟩
      have := List.filterMap_eq_nil_iff.mp hf _ (leastName_mem n ns)
      exact this
    · next r rs hf =>
      split at h
      · cases h
        have hr : r ∈ (n :: ns).filterMap roleOf := hf ▸ List.mem_cons_self ..
        obtain ⟨x, hx, hxr⟩ := List.mem_filterMap.mp hr
        exact ⟨x, hx, roleOf_eq_some hxr⟩
      · cases h

theorem aliasEntry_fst {reps : Std.HashMap Address (Option (Ix.Kernel.Key .source))}
    {p : Ix.Kernel.Name × Address} {e : Ix.Kernel.Name × Ix.Kernel.Key .source}
    (h : aliasEntry reps p = some e) : e.1 = p.1 := by
  unfold aliasEntry at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

/-- The fiber map's entries have distinct names. -/
theorem fiberAliasMap_distinct (ixe : Ixon.Env) (reps : Std.HashMap Address (Option (Ix.Kernel.Key .source))) :
    ((sourceAddrs ixe).toList.filterMap (aliasEntry reps)).Pairwise
      (fun a b => (a.1 == b.1) = false) :=
  Std.HashMap.distinct_keys_toList.filterMap _ fun p q hpq e he e' he' => by
    rw [aliasEntry_fst he, aliasEntry_fst he']
    exact hpq

/-- The representatives' table at an address of a fiber. -/
theorem fiberReps_at {ixe : Ixon.Env} {i : Ix.Kernel.Name} {a : Address}
    (hi : (sourceAddrs ixe)[i]? = some a) :
    ((fiberMembers (sourceAddrs ixe)).map fun _ ns => fiberRep ns)[a]? =
      some (fiberRep ((fiberMembers (sourceAddrs ixe)).getD a [])) := by
  have hm := mem_fiberMembers.mpr hi
  rw [Std.HashMap.getElem?_map]
  rw [Std.HashMap.getD_eq_getD_getElem?] at hm ⊢
  cases h : (fiberMembers (sourceAddrs ixe))[a]? with
  | none => rw [h] at hm; cases hm
  | some l => rfl

/-- **Every name of a fiber with a representative is renamed to it.** -/
theorem fiberAlias_subst {ixe : Ixon.Env} {i : Ix.Kernel.Name} {a : Address}
    {rep : Ix.Kernel.Key .source} (hi : (sourceAddrs ixe)[i]? = some a)
    (hrep : fiberRep ((fiberMembers (sourceAddrs ixe)).getD a []) = some rep) :
    Key.subst (fiberAlias ixe) (Ix.Kernel.Key.ofName i) = rep := by
  have hreps := fiberReps_at hi
  rw [hrep] at hreps
  have hmem : (i, a) ∈ (sourceAddrs ixe).toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hi
  cases hr : roleOf i with
  | some r =>
    rw [roleOf_eq_some hr, fiberRep_role (mem_fiberMembers.mpr hi) hr hrep]
    rfl
  | none =>
    rw [roleOf_eq_none hr]
    simp only [Key.subst, fiberAlias, fiberAliasMap]
    by_cases heq : (Ix.Kernel.Key.id i : Ix.Kernel.Key .source) = rep
    · rw [Std.HashMap.getElem?_ofList_of_contains_eq_false]
      · exact heq
      · refine Bool.eq_false_iff.mpr fun hc => ?_
        obtain ⟨e, he, he1⟩ : ∃ e ∈ (sourceAddrs ixe).toList.filterMap
            (aliasEntry ((fiberMembers (sourceAddrs ixe)).map fun _ ns => fiberRep ns)), e.1 = i := by
          simpa using hc
        obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
        have hp1 : p.1 = i := (aliasEntry_fst hpe).symm.trans he1
        obtain ⟨pi, pa⟩ := p
        simp only at hp1
        subst hp1
        have hpa : pa = a := by
          have := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
          rw [hi] at this
          exact (Option.some.inj this).symm
        subst hpa
        unfold aliasEntry at hpe
        simp only [hreps, roleOf_eq_none hr, heq, ne_eq, not_true_eq_false, and_false,
          ite_false] at hpe
        cases hpe
    · rw [Std.HashMap.getElem?_ofList_of_mem (k := i) (v := rep) (BEq.refl i)
        (fiberAliasMap_distinct ixe _)]
      · rfl
      · refine List.mem_filterMap.mpr ⟨(i, a), hmem, ?_⟩
        unfold aliasEntry
        simp only [hreps, hr, roleOf_eq_none hr, true_and]
        rw [ite_eq_left heq]

/-- **Two names at one address are renamed to one key** (unless their fiber
holds two roles' names): so distinct representatives have distinct
addresses. -/
theorem fiberAlias_addr_inj {ixe : Ixon.Env} {i j : Ix.Kernel.Name} {a : Address}
    (hi : (sourceAddrs ixe)[i]? = some a) (hj : (sourceAddrs ixe)[j]? = some a)
    (hroles : ∀ x y r₁ r₂, (sourceAddrs ixe)[x]? = some a → (sourceAddrs ixe)[y]? = some a →
      roleOf x = some r₁ → roleOf y = some r₂ → r₁ = r₂) :
    Key.subst (fiberAlias ixe) (Ix.Kernel.Key.ofName i) =
      Key.subst (fiberAlias ixe) (Ix.Kernel.Key.ofName j) := by
  have hne : (fiberMembers (sourceAddrs ixe)).getD a [] ≠ [] := by
    intro h
    have := mem_fiberMembers.mpr hi
    rw [h] at this
    cases this
  obtain ⟨rep, hrep⟩ := fiberRep_isSome hne fun x y r₁ r₂ hx hy =>
    hroles x y r₁ r₂ (mem_fiberMembers.mp hx) (mem_fiberMembers.mp hy)
  rw [fiberAlias_subst hi hrep, fiberAlias_subst hj hrep]

/-- **A representative is at its fiber's address**: a renamed name's
representative is the key of a name at the same address. -/
theorem fiberAlias_rep_addr {ixe : Ixon.Env} {i : Ix.Kernel.Name} {a : Address}
    {rep : Ix.Kernel.Key .source} (hi : (sourceAddrs ixe)[i]? = some a)
    (h : (fiberAlias ixe)[i]? = some rep) :
    ∃ k, (sourceAddrs ixe)[k]? = some a ∧ Ix.Kernel.Key.ofName k = rep := by
  have hreps := fiberReps_at hi
  simp only [fiberAlias, fiberAliasMap] at h
  have hc : List.contains (List.map Prod.fst ((sourceAddrs ixe).toList.filterMap
      (aliasEntry ((fiberMembers (sourceAddrs ixe)).map fun _ ns => fiberRep ns)))) i = true := by
    refine Classical.byContradiction fun hne => ?_
    rw [Std.HashMap.getElem?_ofList_of_contains_eq_false (Bool.eq_false_iff.mpr hne)] at h
    cases h
  obtain ⟨e, he, he1⟩ : ∃ e ∈ (sourceAddrs ixe).toList.filterMap
      (aliasEntry ((fiberMembers (sourceAddrs ixe)).map fun _ ns => fiberRep ns)), e.1 = i := by
    simpa using hc
  obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
  have hp1 : p.1 = i := (aliasEntry_fst hpe).symm.trans he1
  obtain ⟨pi, pa⟩ := p
  simp only at hp1
  subst hp1
  have hpa : pa = a := by
    have := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
    rw [hi] at this
    exact (Option.some.inj this).symm
  subst hpa
  rw [Std.HashMap.getElem?_ofList_of_mem (k := e.1) (k' := pi) (v := e.2)
    (by rw [he1]; exact BEq.refl pi) (fiberAliasMap_distinct ixe _) he] at h
  cases hfr : fiberRep ((fiberMembers (sourceAddrs ixe)).getD pa []) with
  | none =>
    unfold aliasEntry at hpe
    simp only [hreps, hfr] at hpe
    cases hpe
  | some rep' =>
    unfold aliasEntry at hpe
    simp only [hreps, hfr] at hpe
    split at hpe
    · cases hpe
      have hr : rep' = rep := Option.some.inj h
      subst hr
      obtain ⟨k, hk, hkr⟩ := fiberRep_mem hfr
      exact ⟨k, mem_fiberMembers.mp hk, hkr⟩
    · cases hpe


/-! ## The role read off the table

`fiberAlias` keys a fiber `.role r` only when it holds role `r`'s Lean name.
The **table rule** keys it by the address: a fiber whose address the role
table binds to `r` is represented by `.role r` (when its role names, if any,
are `r`'s), whatever names it holds, so an alias of a role's content keyed
by a user name (a two-constructor enum at `Bool`'s address, in a closure
without `Bool`) is that role's, as the Ixon reader keys it. Elsewhere the
name rule stands. `roles` is the table's inverse (`roleAtMap`). -/

/-- **The table's inverse**: the role each bound address is bound to. -/
def roleAtMap (t : Ix.Kernel.RoleTable) : Std.HashMap Address Ix.Kernel.Role :=
  t.bound.foldl (fun m p => m.insert p.2 p.1) {}

/-- A fiber's representative under the table rule: the role its address is
bound to (when the fiber's role names are that role's), else the name rule. -/
def repAt (bound : Option Ix.Kernel.Role) (q : Option (Ix.Kernel.Key .source) × List Ix.Kernel.Role) :
    Option (Ix.Kernel.Key .source) :=
  match bound with
  | some r => if q.2.all (fun r' => decide (r' = r)) then some (.role r) else none
  | none => q.1

/-- A name's entry in the fiber map under the table rule. -/
def aliasEntryAt (roles : Std.HashMap Address Ix.Kernel.Role)
    (reps : Std.HashMap Address (Option (Ix.Kernel.Key .source) × List Ix.Kernel.Role))
    (p : Ix.Kernel.Name × Address) : Option (Ix.Kernel.Name × Ix.Kernel.Key .source) :=
  match reps[p.2]? with
  | some q =>
    match repAt roles[p.2]? q with
    | some rep => if roleOf p.1 = none ∧ Ix.Kernel.Key.ofName p.1 ≠ rep then some (p.1, rep) else none
    | none => none
  | none => none

/-- **The alias fibers of a compiled artifact, the role read off the table**
(`roles`, the table's inverse). -/
def fiberAliasAt (ixe : Ixon.Env) (roles : Std.HashMap Address Ix.Kernel.Role) : FiberMap :=
  let addrs := sourceAddrs ixe
  let reps := (fiberMembers addrs).map fun _ ns => (fiberRep ns, ns.filterMap roleOf)
  Std.HashMap.ofList (addrs.toList.filterMap (aliasEntryAt roles reps))

/-- **Every published role name sits at an address the table binds to its
role**, by ingress name (the names `sourceAddrs` recomputes, never a stored
`Ix.Name` hash). This is what the statements' decided `PublishedRolesBound`
checks, over every published name (`tableBound_of`, with a well-formed table);
B5a's `RolesBound` does not give it: it reads names by their stored hashes and
covers only the roles the input declares. -/
def TableBound (ixe : Ixon.Env) (roles : Std.HashMap Address Ix.Kernel.Role) : Prop :=
  ∀ x r a, (sourceAddrs ixe)[x]? = some a → roleOf x = some r → roles[a]? = some r

/-! ### The table rule's lemmas -/

theorem repAt_role {bound : Option Ix.Kernel.Role} {l : List Ix.Kernel.Name} {x : Ix.Kernel.Name}
    {r : Ix.Kernel.Role} {rep : Ix.Kernel.Key .source} (hx : x ∈ l) (hxr : roleOf x = some r)
    (h : repAt bound (fiberRep l, l.filterMap roleOf) = some rep) : rep = .role r := by
  cases bound with
  | none => exact fiberRep_role hx hxr h
  | some r' =>
    simp only [repAt] at h
    split at h
    · next hall =>
      cases h
      have hm : r ∈ l.filterMap roleOf := List.mem_filterMap.mpr ⟨x, hx, hxr⟩
      have := List.all_eq_true.mp hall r hm
      simp only [decide_eq_true_eq] at this
      rw [this]
    · cases h

theorem repAt_isSome {bound : Option Ix.Kernel.Role} {l : List Ix.Kernel.Name} (hne : l ≠ [])
    (hb : ∀ x ∈ l, ∀ r, roleOf x = some r → bound = some r) :
    ∃ rep, repAt bound (fiberRep l, l.filterMap roleOf) = some rep := by
  cases bound with
  | none =>
    refine fiberRep_isSome hne fun x y r₁ r₂ hx _ hxr _ => ?_
    exact absurd (hb x hx r₁ hxr) (by simp)
  | some r' =>
    refine ⟨.role r', ?_⟩
    simp only [repAt]
    rw [ite_eq_left]
    refine List.all_eq_true.mpr fun r hr => ?_
    obtain ⟨x, hx, hxr⟩ := List.mem_filterMap.mp hr
    have := hb x hx r hxr
    simp only [Option.some.injEq] at this
    exact decide_eq_true this.symm

theorem repAt_mem {bound : Option Ix.Kernel.Role} {l : List Ix.Kernel.Name}
    {rep : Ix.Kernel.Key .source} (h : repAt bound (fiberRep l, l.filterMap roleOf) = some rep) :
    (∃ k ∈ l, Ix.Kernel.Key.ofName k = rep) ∨ ∃ r, rep = .role r := by
  cases bound with
  | none => exact Or.inl (fiberRep_mem h)
  | some r' =>
    simp only [repAt] at h
    split at h
    · cases h; exact Or.inr ⟨r', rfl⟩
    · cases h

theorem fiberRepsAt_at {ixe : Ixon.Env} {i : Ix.Kernel.Name} {a : Address}
    (hi : (sourceAddrs ixe)[i]? = some a) :
    ((fiberMembers (sourceAddrs ixe)).map fun _ ns => (fiberRep ns, ns.filterMap roleOf))[a]? =
      some (fiberRep ((fiberMembers (sourceAddrs ixe)).getD a []),
        ((fiberMembers (sourceAddrs ixe)).getD a []).filterMap roleOf) := by
  have hm := mem_fiberMembers.mpr hi
  rw [Std.HashMap.getElem?_map]
  rw [Std.HashMap.getD_eq_getD_getElem?] at hm ⊢
  cases h : (fiberMembers (sourceAddrs ixe))[a]? with
  | none => rw [h] at hm; cases hm
  | some l => rfl

theorem aliasEntryAt_fst {roles : Std.HashMap Address Ix.Kernel.Role}
    {reps : Std.HashMap Address (Option (Ix.Kernel.Key .source) × List Ix.Kernel.Role)}
    {p : Ix.Kernel.Name × Address} {e : Ix.Kernel.Name × Ix.Kernel.Key .source}
    (h : aliasEntryAt roles reps p = some e) : e.1 = p.1 := by
  unfold aliasEntryAt at h
  split at h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h
  · cases h

theorem fiberAliasAt_distinct (ixe : Ixon.Env) (roles : Std.HashMap Address Ix.Kernel.Role)
    (reps : Std.HashMap Address (Option (Ix.Kernel.Key .source) × List Ix.Kernel.Role)) :
    ((sourceAddrs ixe).toList.filterMap (aliasEntryAt roles reps)).Pairwise
      (fun a b => (a.1 == b.1) = false) :=
  Std.HashMap.distinct_keys_toList.filterMap _ fun p q hpq e he e' he' => by
    rw [aliasEntryAt_fst he, aliasEntryAt_fst he']
    exact hpq

/-- **Under the table rule, every name of a fiber with a representative is
renamed to it.** -/
theorem fiberAliasAt_subst {ixe : Ixon.Env} {roles : Std.HashMap Address Ix.Kernel.Role}
    {i : Ix.Kernel.Name} {a : Address} {rep : Ix.Kernel.Key .source}
    (hi : (sourceAddrs ixe)[i]? = some a)
    (hrep : repAt roles[a]? (fiberRep ((fiberMembers (sourceAddrs ixe)).getD a []),
      ((fiberMembers (sourceAddrs ixe)).getD a []).filterMap roleOf) = some rep) :
    Key.subst (fiberAliasAt ixe roles) (Ix.Kernel.Key.ofName i) = rep := by
  have hreps := fiberRepsAt_at hi
  have hmem : (i, a) ∈ (sourceAddrs ixe).toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hi
  cases hr : roleOf i with
  | some r =>
    rw [roleOf_eq_some hr, repAt_role (mem_fiberMembers.mpr hi) hr hrep]
    rfl
  | none =>
    rw [roleOf_eq_none hr]
    simp only [Key.subst, fiberAliasAt]
    by_cases heq : (Ix.Kernel.Key.id i : Ix.Kernel.Key .source) = rep
    · rw [Std.HashMap.getElem?_ofList_of_contains_eq_false]
      · exact heq
      · refine Bool.eq_false_iff.mpr fun hc => ?_
        obtain ⟨e, he, he1⟩ : ∃ e ∈ (sourceAddrs ixe).toList.filterMap
            (aliasEntryAt roles ((fiberMembers (sourceAddrs ixe)).map
              fun _ ns => (fiberRep ns, ns.filterMap roleOf))), e.1 = i := by
          simpa using hc
        obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
        have hp1 : p.1 = i := (aliasEntryAt_fst hpe).symm.trans he1
        obtain ⟨pi, pa⟩ := p
        simp only at hp1
        subst hp1
        have hpa : pa = a := by
          have := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
          rw [hi] at this
          exact (Option.some.inj this).symm
        subst hpa
        unfold aliasEntryAt at hpe
        simp only [hreps, hrep, roleOf_eq_none hr, heq, ne_eq, not_true_eq_false, and_false,
          ite_false] at hpe
        cases hpe
    · rw [Std.HashMap.getElem?_ofList_of_mem (k := i) (v := rep) (BEq.refl i)
        (fiberAliasAt_distinct ixe roles _)]
      · rfl
      · refine List.mem_filterMap.mpr ⟨(i, a), hmem, ?_⟩
        unfold aliasEntryAt
        simp only [hreps, hrep, hr, roleOf_eq_none hr, true_and]
        rw [ite_eq_left heq]

/-- **Under the table rule, two names at one address are renamed to one key**,
when every published role name sits at its role's bound address. -/
theorem fiberAliasAt_addr_inj {ixe : Ixon.Env} {roles : Std.HashMap Address Ix.Kernel.Role}
    (hbound : TableBound ixe roles) {i j : Ix.Kernel.Name} {a : Address}
    (hi : (sourceAddrs ixe)[i]? = some a) (hj : (sourceAddrs ixe)[j]? = some a) :
    Key.subst (fiberAliasAt ixe roles) (Ix.Kernel.Key.ofName i) =
      Key.subst (fiberAliasAt ixe roles) (Ix.Kernel.Key.ofName j) := by
  have hne : (fiberMembers (sourceAddrs ixe)).getD a [] ≠ [] := by
    intro h
    have := mem_fiberMembers.mpr hi
    rw [h] at this
    cases this
  obtain ⟨rep, hrep⟩ := repAt_isSome (bound := roles[a]?) hne fun x hx r hxr =>
    hbound x r a (mem_fiberMembers.mp hx) hxr
  rw [fiberAliasAt_subst hi hrep, fiberAliasAt_subst hj hrep]

/-- **Under the table rule, a representative is a name at the fiber's address,
or a role key.** -/
theorem fiberAliasAt_rep_addr {ixe : Ixon.Env} {roles : Std.HashMap Address Ix.Kernel.Role}
    {i : Ix.Kernel.Name} {a : Address} {rep : Ix.Kernel.Key .source}
    (hi : (sourceAddrs ixe)[i]? = some a) (h : (fiberAliasAt ixe roles)[i]? = some rep) :
    (∃ k, (sourceAddrs ixe)[k]? = some a ∧ Ix.Kernel.Key.ofName k = rep) ∨ ∃ r, rep = .role r := by
  have hreps := fiberRepsAt_at hi
  simp only [fiberAliasAt] at h
  have hc : List.contains (List.map Prod.fst ((sourceAddrs ixe).toList.filterMap
      (aliasEntryAt roles ((fiberMembers (sourceAddrs ixe)).map
        fun _ ns => (fiberRep ns, ns.filterMap roleOf))))) i = true := by
    refine Classical.byContradiction fun hne => ?_
    rw [Std.HashMap.getElem?_ofList_of_contains_eq_false (Bool.eq_false_iff.mpr hne)] at h
    cases h
  obtain ⟨e, he, he1⟩ : ∃ e ∈ (sourceAddrs ixe).toList.filterMap
      (aliasEntryAt roles ((fiberMembers (sourceAddrs ixe)).map
        fun _ ns => (fiberRep ns, ns.filterMap roleOf))), e.1 = i := by
    simpa using hc
  obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
  have hp1 : p.1 = i := (aliasEntryAt_fst hpe).symm.trans he1
  obtain ⟨pi, pa⟩ := p
  simp only at hp1
  subst hp1
  have hpa : pa = a := by
    have := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
    rw [hi] at this
    exact (Option.some.inj this).symm
  subst hpa
  rw [Std.HashMap.getElem?_ofList_of_mem (k := e.1) (k' := pi) (v := e.2)
    (by rw [he1]; exact BEq.refl pi) (fiberAliasAt_distinct ixe roles _) he] at h
  cases hfr : repAt roles[pa]? (fiberRep ((fiberMembers (sourceAddrs ixe)).getD pa []),
      ((fiberMembers (sourceAddrs ixe)).getD pa []).filterMap roleOf) with
  | none =>
    unfold aliasEntryAt at hpe
    simp only [hreps, hfr] at hpe
    cases hpe
  | some rep' =>
    unfold aliasEntryAt at hpe
    simp only [hreps, hfr] at hpe
    split at hpe
    · cases hpe
      have hr : rep' = rep := Option.some.inj h
      subst hr
      rcases repAt_mem hfr with ⟨k, hk, hkr⟩ | hrole
      · exact Or.inl ⟨k, mem_fiberMembers.mp hk, hkr⟩
      · exact Or.inr hrole
    · cases hpe

/-! ## Deciding that a prepared stream's keys are representatives'

`Key.goodB q` decides that every input id of a key passes `q`; `Expr.goodBGo` is
the memoised walk over a term's distinct subterms (a stream's terms share
subterms, as `Expr.substKeysGo`'s walk does), and `declsGoodB` the walk over a
stream, the memo shared across its declarations. -/

/-- Every input id of a key passes `q`. -/
def Key.goodB (q : Ix.Kernel.Name → Bool) : Ix.Kernel.Key .source → Bool
  | .id n => q n
  | .role _ => true
  | .aux k _ => Key.goodB q k

/-- **Memoised: every key of a term's subterms passes `q`**; `seen` holds the
subterms already found good. -/
def Expr.goodBGo (q : Ix.Kernel.Name → Bool) (seen : Std.HashSet (Ix.Kernel.Expr .source)) :
    Ix.Kernel.Expr .source → Bool × Std.HashSet (Ix.Kernel.Expr .source)
  | .bvar _ => (true, seen)
  | .sort _ => (true, seen)
  | .lit _ => (true, seen)
  | .const n _ => (Key.goodB q n, seen)
  | e =>
    if seen.contains e then (true, seen)
    else
      let r : Bool × Std.HashSet (Ix.Kernel.Expr .source) :=
        match e with
        | .fvar _ ty => Expr.goodBGo q seen ty
        | .app a b =>
          let ra := Expr.goodBGo q seen a
          if ra.1 then Expr.goodBGo q ra.2 b else ra
        | .lam ty body _ =>
          let rt := Expr.goodBGo q seen ty
          if rt.1 then Expr.goodBGo q rt.2 body else rt
        | .forallE ty body _ =>
          let rt := Expr.goodBGo q seen ty
          if rt.1 then Expr.goodBGo q rt.2 body else rt
        | .letE ty v body _ =>
          let rt := Expr.goodBGo q seen ty
          if rt.1 then
            let rv := Expr.goodBGo q rt.2 v
            if rv.1 then Expr.goodBGo q rv.2 body else rv
          else rt
        | .proj s _ sub => if Key.goodB q s then Expr.goodBGo q seen sub else (false, seen)
        | _ => (true, seen)
      if r.1 then (true, r.2.insert e) else (false, r.2)

/-- The memoised walk over a list of terms. -/
def exprsGoodB (q : Ix.Kernel.Name → Bool) :
    Std.HashSet (Ix.Kernel.Expr .source) → List (Ix.Kernel.Expr .source) →
      Bool × Std.HashSet (Ix.Kernel.Expr .source)
  | seen, [] => (true, seen)
  | seen, e :: es =>
    match Expr.goodBGo q seen e with
    | (true, seen) => exprsGoodB q seen es
    | r => r

/-- A constant's keys outside its terms, and its terms. -/
def ConstantInfo.parts : Ix.Kernel.ConstantInfo .source →
    List (Ix.Kernel.Key .source) × List (Ix.Kernel.Expr .source)
  | .axiomInfo v => ([v.name], [v.type])
  | .defnInfo v e _ => ([v.name], [v.type, e])
  | .thmInfo v e => ([v.name], [v.type, e])
  | .indInfo v caps => (v.name :: caps.etaCtor.toList, [v.type])
  | .ctorInfo v _ _ => ([v.name], [v.type])
  | .recInfo v _ _ rules =>
    (v.name :: rules.map (·.ctor), v.type :: rules.flatMap fun r => r.rhs :: match r.fire with
      | .nested _ ps => ps
      | _ => [])
  | .projInfo t => ([t.structName, t.ctor], t.bodies.toList)

/-- A declaration's keys outside its terms, and its terms. -/
def Declaration.parts : Ix.Kernel.Declaration .source →
    List (Ix.Kernel.Key .source) × List (Ix.Kernel.Expr .source)
  | .axiomDecl v => ([v.name], [v.type])
  | .defnDecl v e _ => ([v.name], [v.type, e])
  | .thmDecl v e => ([v.name], [v.type, e])
  | .opaqueDecl v e => ([v.name], [v.type, e])
  | .basisDecl _ => ([], [])
  | .indDecl block _ => (block.flatMap fun c => (ConstantInfo.parts c).1,
      block.flatMap fun c => (ConstantInfo.parts c).2)
  | .quotDecl _ v => ([v.name], [v.type])

/-- **Every key of a stream passes `q`**, decided (one memo across the stream). -/
def declsGoodB (q : Ix.Kernel.Name → Bool) (ds : Array (Ix.Kernel.Declaration .source)) : Bool :=
  (ds.foldl (fun (acc : Bool × Std.HashSet (Ix.Kernel.Expr .source)) d =>
    if acc.1 then
      if (Declaration.parts d).1.all (Key.goodB q) then exprsGoodB q acc.2 (Declaration.parts d).2
      else (false, acc.2)
    else acc) (true, {})).1

/-- An evidence table's keys and terms. -/
def evidenceParts (ev : Ix.Kernel.Evidences .source) :
    List (Ix.Kernel.Key .source) × List (Ix.Kernel.Expr .source) :=
  (ev.flatMap fun p => p.2.flatMap fun
    | .proof (k, _) => [k]
    | .defeq => [],
   ev.flatMap fun p => p.2.flatMap fun
    | .proof (_, v) => [v]
    | .defeq => [])

/-- **Every key of an evidence table passes `q`**, decided. -/
def evidenceGoodB (q : Ix.Kernel.Name → Bool) (ev : Ix.Kernel.Evidences .source) : Bool :=
  (evidenceParts ev).1.all (Key.goodB q) && (exprsGoodB q {} (evidenceParts ev).2).1
end Ix.LeanIngress
