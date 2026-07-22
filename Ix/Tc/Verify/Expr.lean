import Ix.Tc.Env
import Ix.Tc.Verify.Level
import Std.Data.HashMap.Lemmas

/-!
# Expr slice foundations: erasure, `CollisionFree`, and the intern tables

M2 of plans/tc-verify-roadmap.md, first layer: the full collision-freedom
formulation. M1's pilot (`KUniv.AddrFaithful`, Verify/Level.lean) is
pairwise — one hypothesis per compared pair. This module generalizes it to
the composable *support set* form (`CollisionFreeOn`, `Set.InjOn`-style
over bare predicates — no Mathlib here): the set in practice is an intern
table's range extended by the candidates being interned, so support growth
is monotone by construction and one hypothesis over a final support covers
every intermediate step (risk R1's mitigation).

Interop finding (extends the M1/A3 outcome): classic proof files unfold
not only `@[expose]` bodies of module-system production files but also
NON-exposed `public` ones — `ByteArray.beq` (Ix/ByteArray.lean, no
`@[expose]`) reduces to its `beqNoFFI` model by `rfl` here. That makes
`LawfulBEq ByteArray` / `LawfulBEq Address` provable in-slice with zero
production changes, retiring M1's "no `LawfulBEq ByteArray`" friction:
every `==` on `Address` converts to `=`, and the `Std.HashMap` lemma
library fires for the Address-keyed intern tables.

`==` on `KUniv`/`KExpr` stays UNLAWFUL by design: those compare Blake3
addresses, and lawfulness there is exactly the collision-freedom this
module keeps as a named finite-support hypothesis — never a global axiom
(false by pigeonhole over the fixed 2²⁵⁶-value address space), never an
instance.
-/

namespace Ix.Tc

variable {m : Mode}

/-! ### Lawful equality for raw addresses -/

instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := by
    cases a; cases b
    exact congrArg ByteArray.mk (eq_of_beq h)
  rfl {a} := beq_self_eq_true a.data

instance : LawfulBEq Address where
  eq_of_beq {a b} h := by
    cases a; cases b
    exact congrArg Address.mk (eq_of_beq h)
  rfl {a} := by cases a; exact beq_self_eq_true (α := ByteArray) _

/-! ### Support-set collision-freedom

Generic in the key and the erasure so one definition covers universes
(`addr`-keyed in both modes) and expressions (`internKey`-keyed for the
intern table: `addr` in anon mode, the metadata-aware `metaAddr` in meta
mode; plain `addr` for the `==` fast paths in both modes). -/

/-- `key` determines `erase`-classes on the support `S`: within `S`, terms
    agreeing on their Blake3 key agree up to metadata erasure. This is the
    finite-support collision-freedom hypothesis in its composable form. -/
def CollisionFreeOn (key : α → Address) (erase : α → β) (S : α → Prop) :
    Prop :=
  ∀ ⦃x⦄, S x → ∀ ⦃y⦄, S y → key x = key y → erase x = erase y

/-- Collision-freedom is downward closed: shrinking the support weakens the
    hypothesis. Chained with monotone intern-table growth, one hypothesis
    over the final support serves every intermediate step. -/
theorem CollisionFreeOn.mono {key : α → Address} {erase : α → β}
    {S S' : α → Prop} (hsub : ∀ x, S' x → S x)
    (h : CollisionFreeOn key erase S) : CollisionFreeOn key erase S' :=
  fun _ hx _ hy => h (hsub _ hx) (hsub _ hy)

/-- Universe collision-freedom over a support set. -/
abbrev KUniv.CollisionFree (S : KUniv m → Prop) : Prop :=
  CollisionFreeOn KUniv.addr KUniv.eraseMeta S

/-- The support-set form recovers M1's pairwise pilot on any two members. -/
theorem KUniv.CollisionFree.addrFaithful {S : KUniv m → Prop}
    (h : KUniv.CollisionFree S) {u v : KUniv m} (hu : S u) (hv : S v) :
    u.AddrFaithful v :=
  fun heq => h hu hv (eq_of_beq heq)

/-! ### Anon erasure for expressions

Mirrors `KUniv.eraseMeta` (Verify/Level.lean): drop names, binder infos,
and mdata; keep structure, literals, and every stored address verbatim —
addresses are metadata-blind by the hash contract, so the erased term is
the anon twin with the SAME semantic Merkle addresses. -/

namespace KId

/-- Anon erasure of a kernel id: keep the address, drop the display name. -/
def eraseMeta (i : KId m) : KId .anon := ⟨i.addr, ()⟩

@[simp] theorem addr_eraseMeta (i : KId m) : i.eraseMeta.addr = i.addr := rfl

@[simp] theorem eraseMeta_anon (i : KId .anon) : i.eraseMeta = i := rfl

end KId

namespace ExprInfo

/-- Anon erasure of per-node info: the semantic fields (address,
    substitution annotations, fvar flag) are metadata-blind and survive;
    mdata and the metadata-aware address are dropped. -/
def eraseMeta (i : ExprInfo m) : ExprInfo .anon :=
  { addr := i.addr, lbr := i.lbr, count0 := i.count0,
    hasFVars := i.hasFVars, mdata := (), metaAddr := () }

@[simp] theorem eraseMeta_anon (i : ExprInfo .anon) : i.eraseMeta = i := rfl

end ExprInfo

/-- Anon erasure of a universe is the identity in anon mode. -/
theorem KUniv.eraseMeta_anon : ∀ u : KUniv .anon, u.eraseMeta = u
  | .zero _ => rfl
  | .succ u _ => by rw [eraseMeta, eraseMeta_anon u]
  | .max a b _ => by rw [eraseMeta, eraseMeta_anon a, eraseMeta_anon b]
  | .imax a b _ => by rw [eraseMeta, eraseMeta_anon a, eraseMeta_anon b]
  | .param .. => rfl

namespace KExpr

/-- Anon erasure of an expression. -/
def eraseMeta : KExpr m → KExpr .anon
  | .var idx _ i => .var idx () i.eraseMeta
  | .fvar id _ i => .fvar id () i.eraseMeta
  | .sort u i => .sort u.eraseMeta i.eraseMeta
  | .const id us i => .const id.eraseMeta (us.map KUniv.eraseMeta) i.eraseMeta
  | .app f a i => .app f.eraseMeta a.eraseMeta i.eraseMeta
  | .lam _ _ ty body i => .lam () () ty.eraseMeta body.eraseMeta i.eraseMeta
  | .all _ _ ty body i => .all () () ty.eraseMeta body.eraseMeta i.eraseMeta
  | .letE _ ty val body nd i =>
    .letE () ty.eraseMeta val.eraseMeta body.eraseMeta nd i.eraseMeta
  | .prj id field val i => .prj id.eraseMeta field val.eraseMeta i.eraseMeta
  | .nat v b i => .nat v b i.eraseMeta
  | .str v b i => .str v b i.eraseMeta

@[simp] theorem info_eraseMeta (e : KExpr m) :
    e.eraseMeta.info = e.info.eraseMeta := by
  cases e <;> rfl

@[simp] theorem addr_eraseMeta (e : KExpr m) : e.eraseMeta.addr = e.addr := by
  cases e <;> rfl

@[simp] theorem lbr_eraseMeta (e : KExpr m) : e.eraseMeta.lbr = e.lbr := by
  cases e <;> rfl

@[simp] theorem count0_eraseMeta (e : KExpr m) :
    e.eraseMeta.count0 = e.count0 := by
  cases e <;> rfl

@[simp] theorem hasFVars_eraseMeta (e : KExpr m) :
    e.eraseMeta.hasFVars = e.hasFVars := by
  cases e <;> rfl

/-- The erased twin's intern key is the semantic address (anon `internKey`
    is `addr`, and erasure preserves `addr`). -/
@[simp] theorem internKey_eraseMeta (e : KExpr m) :
    e.eraseMeta.internKey = e.addr :=
  addr_eraseMeta e

/-- Anon erasure of an expression is the identity in anon mode. -/
theorem eraseMeta_anon : ∀ e : KExpr .anon, e.eraseMeta = e
  | .var .. => rfl
  | .fvar .. => rfl
  | .sort u _ => by rw [eraseMeta, KUniv.eraseMeta_anon u]; rfl
  | .const _ us _ => by
    rw [eraseMeta,
      show KUniv.eraseMeta (m := .anon) = id from funext KUniv.eraseMeta_anon,
      Array.map_id]
    rfl
  | .app f a _ => by rw [eraseMeta, eraseMeta_anon f, eraseMeta_anon a]; rfl
  | .lam _ _ ty body _ => by
    rw [eraseMeta, eraseMeta_anon ty, eraseMeta_anon body]; rfl
  | .all _ _ ty body _ => by
    rw [eraseMeta, eraseMeta_anon ty, eraseMeta_anon body]; rfl
  | .letE _ ty val body _ _ => by
    rw [eraseMeta, eraseMeta_anon ty, eraseMeta_anon val, eraseMeta_anon body]
    rfl
  | .prj _ _ val _ => by rw [eraseMeta, eraseMeta_anon val]; rfl
  | .nat .. => rfl
  | .str .. => rfl

/-- `==` on `KExpr` is Blake3 address equality — the definitional bridge
    the fast-path proofs use (mirrors `KUniv.beq_def`). -/
theorem beq_def (a b : KExpr m) : (a == b) = (a.addr == b.addr) := rfl

/-- Pairwise addr-faithfulness — the M1 pilot shape, for expressions:
    concluding anything semantic from an `==` fast path is sound only if
    the compared pair doesn't collide. -/
def AddrFaithful (a b : KExpr m) : Prop :=
  (a.addr == b.addr) = true → a.eraseMeta = b.eraseMeta

/-- Expression collision-freedom keyed by the SEMANTIC address — what `==`
    compares (the defeq/cache fast paths) in both modes. -/
abbrev CollisionFree (S : KExpr m → Prop) : Prop :=
  CollisionFreeOn KExpr.addr KExpr.eraseMeta S

/-- Expression collision-freedom keyed by the INTERN key — what the expr
    intern table dedups by (`addr` in anon mode, metadata-aware `metaAddr`
    in meta mode). In anon mode this is literally `CollisionFree`. -/
abbrev KeyCollisionFree (S : KExpr m → Prop) : Prop :=
  CollisionFreeOn KExpr.internKey KExpr.eraseMeta S

theorem keyCollisionFree_anon {S : KExpr .anon → Prop} :
    KeyCollisionFree S ↔ CollisionFree S :=
  Iff.rfl

/-- The support-set form recovers the pairwise shape on any two members. -/
theorem CollisionFree.addrFaithful {S : KExpr m → Prop}
    (h : CollisionFree S) {a b : KExpr m} (ha : S a) (hb : S b) :
    a.AddrFaithful b :=
  fun heq => h ha hb (eq_of_beq heq)

end KExpr

/-! ### The intern tables

`InternTable.internUniv`/`internExpr` return the FIRST value stored for a
key in place of the candidate; the kernel then uses that canonical value.
This is semantically transparent exactly up to collision-freedom of the
table's *support* (its range) extended by the candidate — the composable
per-call obligation the theorems below discharge. Key coherence (`WF`:
every entry is stored at its own key) is what turns a table hit into an
equation between the candidate's key and the canonical entry's. -/

namespace InternTable

variable {it : InternTable m}

/-- The universe support set: values the table has interned (its range). -/
def UnivSupport (it : InternTable m) (u : KUniv m) : Prop :=
  ∃ a : Address, it.univs[a]? = some u

/-- The expression support set. -/
def ExprSupport (it : InternTable m) (e : KExpr m) : Prop :=
  ∃ a : Address, it.exprs[a]? = some e

/-- Key coherence: every entry is stored at its own key. Established at
    `empty`, preserved by interning. -/
structure WF (it : InternTable m) : Prop where
  univ_key : ∀ {a : Address} {u : KUniv m}, it.univs[a]? = some u → u.addr = a
  expr_key : ∀ {a : Address} {e : KExpr m},
    it.exprs[a]? = some e → e.internKey = a

theorem WF.empty : WF (.empty : InternTable m) := by
  constructor
  · intro a u h
    simp [InternTable.empty] at h
  · intro a e h
    simp [InternTable.empty] at h

/-! #### `internUniv` -/

/-- Interning never touches the expression table. -/
@[simp] theorem internUniv_exprs (u : KUniv m) :
    ((it.internUniv u).2).exprs = it.exprs := by
  cases hscrut : it.univs[u.addr]? <;>
    simp only [InternTable.internUniv, hscrut]

/-- Key coherence is preserved by universe interning. -/
theorem WF.internUniv (hwf : it.WF) (u : KUniv m) :
    ((it.internUniv u).2).WF := by
  cases hscrut : it.univs[u.addr]? with
  | some canon => simpa only [InternTable.internUniv, hscrut] using hwf
  | none =>
    simp only [InternTable.internUniv, hscrut]
    refine ⟨fun {a v} h => ?_, fun {a e} h => hwf.expr_key h⟩
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · next hbeq => cases h; exact eq_of_beq hbeq
    · exact hwf.univ_key h

/-- The support only grows. -/
theorem UnivSupport.internUniv (hv : it.UnivSupport v) (u : KUniv m) :
    ((it.internUniv u).2).UnivSupport v := by
  cases hscrut : it.univs[u.addr]? with
  | some canon => simpa only [InternTable.internUniv, hscrut] using hv
  | none =>
    obtain ⟨a, ha⟩ := hv
    refine ⟨a, ?_⟩
    simp only [InternTable.internUniv, hscrut]
    rw [Std.HashMap.getElem?_insert]
    split
    · next hbeq =>
      rw [eq_of_beq hbeq] at hscrut
      rw [hscrut] at ha
      cases ha
    · exact ha

/-- New support ⊆ old support ∪ {candidate}. -/
theorem UnivSupport.of_internUniv
    (hv : ((it.internUniv u).2).UnivSupport v) :
    it.UnivSupport v ∨ v = u := by
  cases hscrut : it.univs[u.addr]? with
  | some canon =>
    rw [InternTable.internUniv, hscrut] at hv
    exact .inl hv
  | none =>
    obtain ⟨a, ha⟩ := hv
    rw [InternTable.internUniv, hscrut] at ha
    rw [Std.HashMap.getElem?_insert] at ha
    split at ha
    · cases ha; exact .inr rfl
    · exact .inl ⟨a, ha⟩

/-- The returned canonical value lands in the updated support. -/
theorem internUniv_result_support (u : KUniv m) :
    ((it.internUniv u).2).UnivSupport ((it.internUniv u).1) := by
  cases hscrut : it.univs[u.addr]? with
  | some canon =>
    simp only [InternTable.internUniv, hscrut]
    exact ⟨u.addr, hscrut⟩
  | none =>
    simp only [InternTable.internUniv, hscrut]
    exact ⟨u.addr, by simp⟩

/-- Key coherence alone pins the result's address — no collision-freedom
    needed for the address-level contract. -/
theorem internUniv_addr (hwf : it.WF) (u : KUniv m) :
    ((it.internUniv u).1).addr = u.addr := by
  cases hscrut : it.univs[u.addr]? with
  | some canon =>
    simp only [InternTable.internUniv, hscrut]
    exact hwf.univ_key hscrut
  | none => simp only [InternTable.internUniv, hscrut]

/-- THE payoff: under collision-freedom of the support extended by the
    candidate, interning is a semantic no-op — the canonical result is
    erasure-equal to the candidate. -/
theorem internUniv_eraseMeta (hwf : it.WF)
    (hcf : KUniv.CollisionFree fun v => it.UnivSupport v ∨ v = u) :
    ((it.internUniv u).1).eraseMeta = u.eraseMeta := by
  cases hscrut : it.univs[u.addr]? with
  | some canon =>
    simp only [InternTable.internUniv, hscrut]
    exact hcf (.inl ⟨u.addr, hscrut⟩) (.inr rfl) (hwf.univ_key hscrut)
  | none => simp only [InternTable.internUniv, hscrut]

/-! #### `internExpr` -/

/-- Interning never touches the universe table. -/
@[simp] theorem internExpr_univs (e : KExpr m) :
    ((it.internExpr e).2).univs = it.univs := by
  cases hscrut : it.exprs[e.internKey]? <;>
    simp only [InternTable.internExpr, hscrut]

/-- Key coherence is preserved by expression interning. -/
theorem WF.internExpr (hwf : it.WF) (e : KExpr m) :
    ((it.internExpr e).2).WF := by
  cases hscrut : it.exprs[e.internKey]? with
  | some canon => simpa only [InternTable.internExpr, hscrut] using hwf
  | none =>
    simp only [InternTable.internExpr, hscrut]
    refine ⟨fun {a v} h => hwf.univ_key h, fun {a v} h => ?_⟩
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · next hbeq => cases h; exact eq_of_beq hbeq
    · exact hwf.expr_key h

/-- The support only grows. -/
theorem ExprSupport.internExpr (hv : it.ExprSupport v) (e : KExpr m) :
    ((it.internExpr e).2).ExprSupport v := by
  cases hscrut : it.exprs[e.internKey]? with
  | some canon => simpa only [InternTable.internExpr, hscrut] using hv
  | none =>
    obtain ⟨a, ha⟩ := hv
    refine ⟨a, ?_⟩
    simp only [InternTable.internExpr, hscrut]
    rw [Std.HashMap.getElem?_insert]
    split
    · next hbeq =>
      rw [eq_of_beq hbeq] at hscrut
      rw [hscrut] at ha
      cases ha
    · exact ha

/-- New support ⊆ old support ∪ {candidate}. -/
theorem ExprSupport.of_internExpr
    (hv : ((it.internExpr e).2).ExprSupport v) :
    it.ExprSupport v ∨ v = e := by
  cases hscrut : it.exprs[e.internKey]? with
  | some canon =>
    rw [InternTable.internExpr, hscrut] at hv
    exact .inl hv
  | none =>
    obtain ⟨a, ha⟩ := hv
    rw [InternTable.internExpr, hscrut] at ha
    rw [Std.HashMap.getElem?_insert] at ha
    split at ha
    · cases ha; exact .inr rfl
    · exact .inl ⟨a, ha⟩

/-- The returned canonical value lands in the updated support. -/
theorem internExpr_result_support (e : KExpr m) :
    ((it.internExpr e).2).ExprSupport ((it.internExpr e).1) := by
  cases hscrut : it.exprs[e.internKey]? with
  | some canon =>
    simp only [InternTable.internExpr, hscrut]
    exact ⟨e.internKey, hscrut⟩
  | none =>
    simp only [InternTable.internExpr, hscrut]
    exact ⟨e.internKey, by simp⟩

/-- Key coherence alone pins the result's intern key. -/
theorem internExpr_internKey (hwf : it.WF) (e : KExpr m) :
    ((it.internExpr e).1).internKey = e.internKey := by
  cases hscrut : it.exprs[e.internKey]? with
  | some canon =>
    simp only [InternTable.internExpr, hscrut]
    exact hwf.expr_key hscrut
  | none => simp only [InternTable.internExpr, hscrut]

/-- THE payoff: under key collision-freedom of the support extended by the
    candidate, expression interning is a semantic no-op. -/
theorem internExpr_eraseMeta (hwf : it.WF)
    (hcf : KExpr.KeyCollisionFree fun v => it.ExprSupport v ∨ v = e) :
    ((it.internExpr e).1).eraseMeta = e.eraseMeta := by
  cases hscrut : it.exprs[e.internKey]? with
  | some canon =>
    simp only [InternTable.internExpr, hscrut]
    exact hcf (.inl ⟨e.internKey, hscrut⟩) (.inr rfl) (hwf.expr_key hscrut)
  | none => simp only [InternTable.internExpr, hscrut]

/-- Under the same hypotheses the SEMANTIC address is preserved in both
    modes (in meta mode via erasure: erased twins share addresses). -/
theorem internExpr_addr (hwf : it.WF)
    (hcf : KExpr.KeyCollisionFree fun v => it.ExprSupport v ∨ v = e) :
    ((it.internExpr e).1).addr = e.addr := by
  rw [← KExpr.addr_eraseMeta, internExpr_eraseMeta hwf hcf,
    KExpr.addr_eraseMeta]

end InternTable

end Ix.Tc
