import Ix.Tc.Verify.State
import Ix.Tc.Lctx

/-!
# Dual-context reconciliation: `CtxRecon` (M3)

The checker keeps TWO context stacks that never record their
interleaving: the de Bruijn side (`ctx`/`letVals` parallel arrays,
types stored UNLIFTED at their binding depth) and the fvar side
(`lctx : LocalContext`, insertion-ordered). De Bruijn indices are
blind to fvar frames (`lookupVar` reads `ctx` only) — exactly
`KVLCtx`'s design, where `none`-tagged entries consume bvar levels and
`some`-tagged entries are transparent to them. So one interleaved
ghost `Δ : KVLCtx` describes both stacks, but the concrete state
cannot reconstruct the interleaving: `CtxRecon` carries Δ as PER-CALL
ghost data with projection conditions instead of a reconstruction
function.

Divergence from upstream: their checker opens every binder with an
fvar immediately, so upstream `TrLCtx'` (Verify/LocalContext.lean:209)
relates `lctx` to an ALL-fvar `VLCtx` (they prove `noBV`). Our
`CtxRecon'` is `TrLCtx'` extended with the two bvar constructors; the
per-declaration payload relation `TrKLocalDecl` is upstream
`TrLocalDecl` re-keyed verbatim.

Freshness design (recorded in the roadmap): the strictly-increasing
fvar-id condition (`incr`) plus the id ceiling (`fresh`) live HERE,
not in `TcStateWF` — they are positional in `lctx.decls` and monotone
in `nextFVarId` (`.toNat` form; overflow bounds are the caller's
obligation, M2 discipline), so they survive sub-call
truncate-restores, and `incr` yields the fvar `Nodup` directly
(bypassing upstream's map-coherence route). `lctx.index` coherence is
the `LocalContext.WF` inductive (upstream `LocalContext.WF` re-key);
its full `find?`-correspondence kit is the NEXT slice, alongside the
`lookupVar`/`Δ.find? (.inl i)` bvar-side bridge.

Step lemmas are hypothesis-style (fields of the post-state given by
equations) so they are robust to record-update spelling; the pop
lemmas require the Δ-head to be the popped `(none, d)` entry — Δ is
per-call ghost data, so M5/M6 walkers always know the head form at a
pop site (popping under live newer fvars would be a scoping bug and is
deliberately unrepresentable). `truncate`/`restoreDepth` step lemmas
are deferred with the Tier-B rewrites (both are `while`-loops —
partial `Loop.forIn`, opaque to the logic).
-/

namespace Ix.Tc

open Lean4Lean (VExpr VEnv VLocalDecl)

/-! ### List helpers (local, no stdlib-name gambling) -/

theorem zip_concat {α β : Type _} :
    ∀ (l₁ : List α) (l₂ : List β) (a : α) (b : β),
      l₁.length = l₂.length →
      (l₁ ++ [a]).zip (l₂ ++ [b]) = l₁.zip l₂ ++ [(a, b)]
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: l₁, y :: l₂, a, b, h => by
    simp only [List.cons_append, List.zip_cons_cons]
    rw [zip_concat l₁ l₂ a b (by simpa using h)]

theorem zip_dropLast {α β : Type _} :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      l₁.dropLast.zip l₂.dropLast = (l₁.zip l₂).dropLast
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | [_], [_], _ => rfl
  | x :: x' :: l₁, y :: y' :: l₂, h => by
    simp only [List.zip_cons_cons, List.dropLast,
      zip_dropLast (x' :: l₁) (y' :: l₂) (by simpa using h)]

theorem zip_getElem?_of {α β : Type _} :
    ∀ {l₁ : List α} {l₂ : List β} {i : Nat} {a : α} {b : β},
      l₁[i]? = some a → l₂[i]? = some b →
      (l₁.zip l₂)[i]? = some (a, b)
  | _ :: _, _ :: _, 0, _, _, h1, h2 => by
    simp only [List.getElem?_cons_zero] at h1 h2
    cases h1; cases h2; rfl
  | _ :: l₁, _ :: l₂, i + 1, a, b, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    rw [List.zip_cons_cons, List.getElem?_cons_succ]
    exact zip_getElem?_of h1 h2
  | [], _, _, _, _, h1, _ => by simp at h1
  | _ :: _, [], _, _, _, _, h2 => by simp at h2

/-! ### The Δ-side let counter -/

/-- Number of de Bruijn let frames (`(none, .vlet ..)` entries) — the
    ghost image of `numLetBindings`. Fvar-side lets are deliberately
    NOT counted: production `openLet` does not touch
    `numLetBindings`. -/
def KVLCtx.bvarLets : KVLCtx → Nat
  | [] => 0
  | (none, .vlet ..) :: Δ => bvarLets Δ + 1
  | _ :: Δ => bvarLets Δ

@[simp] theorem KVLCtx.bvarLets_nil : KVLCtx.bvarLets [] = 0 := rfl

@[simp] theorem KVLCtx.bvarLets_cons_lam {Δ : KVLCtx} {ty : VExpr} :
    KVLCtx.bvarLets ((none, .vlam ty) :: Δ) = KVLCtx.bvarLets Δ := rfl

@[simp] theorem KVLCtx.bvarLets_cons_let {Δ : KVLCtx} {ty v : VExpr} :
    KVLCtx.bvarLets ((none, .vlet ty v) :: Δ) =
      KVLCtx.bvarLets Δ + 1 := rfl

@[simp] theorem KVLCtx.bvarLets_cons_fvar {Δ : KVLCtx}
    {fv : FVarId × List FVarId} {d : VLocalDecl} :
    KVLCtx.bvarLets ((some fv, d) :: Δ) = KVLCtx.bvarLets Δ := rfl

/-! ### Concrete `LocalContext` well-formedness

Upstream `LocalContext.WF` (Verify/LocalContext.lean:119) re-keyed
over our production `push`: each pushed id is absent from the index.
Only the `mem_of_index` inversion is needed this slice (it discharges
mint-freshness); the full `find?`-correspondence kit is next. -/

inductive LocalContext.WF {m : Mode} : LocalContext m → Prop
  | empty : WF {}
  | push {lctx : LocalContext m} {fv : FVarId} {d : LocalDecl m} :
    WF lctx → lctx.index[fv]? = none → WF (lctx.push fv d)

theorem LocalContext.WF.mem_of_index {m : Mode}
    {lctx : LocalContext m} (h : lctx.WF) {fv : FVarId} {i : Nat}
    (hi : lctx.index[fv]? = some i) :
    ∃ p ∈ lctx.decls.toList, p.1 = fv := by
  induction h with
  | empty => simp at hi
  | @push lctx fv' d _ h2 ih =>
    simp only [LocalContext.push] at hi ⊢
    rw [Std.HashMap.getElem?_insert] at hi
    split at hi
    · next heq =>
      have h3 : fv' = fv := eq_of_beq heq
      subst h3
      exact ⟨(fv', d), by simp [Array.toList_push], rfl⟩
    · obtain ⟨p, hp, hfst⟩ := ih hi
      have hp' : p ∈ (lctx.decls.push (fv', d)).toList := by
        rw [Array.toList_push]
        exact List.mem_append.mpr (.inl hp)
      exact ⟨p, hp', hfst⟩

theorem LocalContext.WF.index_lt {m : Mode} {lctx : LocalContext m}
    (h : lctx.WF) {fv : FVarId} {i : Nat}
    (hi : lctx.index[fv]? = some i) : i < lctx.decls.size := by
  induction h with
  | empty => simp at hi
  | @push lctx fv' d _ h2 ih =>
    simp only [LocalContext.push] at hi ⊢
    rw [Std.HashMap.getElem?_insert] at hi
    split at hi
    · cases hi
      rw [Array.size_push]
      omega
    · have := ih hi
      rw [Array.size_push]
      omega

/-- The index is positionally coherent: a hit points at an entry
    carrying exactly the queried id. -/
theorem LocalContext.WF.getElem?_of_index {m : Mode}
    {lctx : LocalContext m} (h : lctx.WF) {fv : FVarId} {i : Nat}
    (hi : lctx.index[fv]? = some i) :
    ∃ d, lctx.decls[i]? = some (fv, d) := by
  induction h with
  | empty => simp at hi
  | @push lctx fv' d hwf h2 ih =>
    simp only [LocalContext.push] at hi ⊢
    rw [Std.HashMap.getElem?_insert] at hi
    split at hi
    · next heq =>
      cases hi
      have h3 : fv' = fv := eq_of_beq heq
      subst h3
      refine ⟨d, ?_⟩
      rw [← Array.getElem?_toList, Array.toList_push,
        ← Array.length_toList, List.getElem?_concat_length]
    · obtain ⟨d', hd⟩ := ih hi
      have hlt : i < lctx.decls.size := hwf.index_lt hi
      refine ⟨d', ?_⟩
      rw [← Array.getElem?_toList, Array.toList_push,
        List.getElem?_append_left (by simpa using hlt),
        Array.getElem?_toList]
      exact hd

/-- Unpack the concrete `find?` read into a positional hit. -/
theorem LocalContext.WF.find?_pos {m : Mode} {lctx : LocalContext m}
    (h : lctx.WF) {fv : FVarId} {d : LocalDecl m}
    (hf : lctx.find? fv = some d) :
    ∃ i, i < lctx.decls.size ∧ lctx.decls[i]? = some (fv, d) := by
  match hi : lctx.index[fv]? with
  | none => simp [LocalContext.find?, hi] at hf
  | some i =>
    obtain ⟨d', hd⟩ := h.getElem?_of_index hi
    have hlt := h.index_lt hi
    refine ⟨i, hlt, ?_⟩
    simp [LocalContext.find?, hi, hd] at hf
    rw [hd, hf]

/-! ### Per-declaration translation (upstream `TrLocalDecl`) -/

variable (env : VEnv) (uvars : Nat) (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop)
    (Δ : KVLCtx) in
/-- The concrete declaration's payloads translate at `Δ` and are
    well-typed there (upstream `TrLocalDecl`,
    Verify/LocalContext.lean:189). -/
inductive TrKLocalDecl : LocalDecl .anon → VLocalDecl → Prop
  | vlam {nm : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {ty : KExpr .anon} {ty' : VExpr} :
    TrKExprS env uvars nameOf trProj Δ ty ty' →
    env.IsType uvars Δ.toCtx ty' →
    TrKLocalDecl (.cdecl nm bi ty) (.vlam ty')
  | vlet {nm : Mode.anon.F Name} {ty val : KExpr .anon}
      {ty' val' : VExpr} :
    TrKExprS env uvars nameOf trProj Δ ty ty' →
    TrKExprS env uvars nameOf trProj Δ val val' →
    env.HasType uvars Δ.toCtx val' ty' →
    TrKLocalDecl (.ldecl nm ty val) (.vlet ty' val')

theorem TrKLocalDecl.wf {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {Δ : KVLCtx} {d : LocalDecl .anon} {vd : VLocalDecl}
    (H : TrKLocalDecl env uvars nameOf trProj Δ d vd) :
    vd.WF env uvars Δ.toCtx :=
  match H with
  | .vlam _ h => h
  | .vlet _ _ h => h

theorem TrKLocalDecl.mono {env env' : VEnv} (henv : env ≤ env')
    {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {Δ : KVLCtx} {d : LocalDecl .anon} {vd : VLocalDecl}
    (H : TrKLocalDecl env uvars nameOf trProj Δ d vd) :
    TrKLocalDecl env' uvars nameOf trProj Δ d vd :=
  match H with
  | .vlam h1 h2 => .vlam (h1.mono henv) (h2.mono henv)
  | .vlet h1 h2 h3 => .vlet (h1.mono henv) (h2.mono henv) (h3.mono henv)

variable (env : VEnv) (uvars : Nat) (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop)
    (Δ : KVLCtx) in
/-- A de Bruijn frame's payloads (type + optional let value) translate
    at `Δ` — the pair-side sibling of `TrKLocalDecl`, produced by the
    lookup bridge. -/
inductive TrKBvarFrame :
    KExpr .anon → Option (KExpr .anon) → VLocalDecl → Prop
  | vlam {ty : KExpr .anon} {ty' : VExpr} :
    TrKExprS env uvars nameOf trProj Δ ty ty' →
    env.IsType uvars Δ.toCtx ty' →
    TrKBvarFrame ty none (.vlam ty')
  | vlet {ty val : KExpr .anon} {ty' val' : VExpr} :
    TrKExprS env uvars nameOf trProj Δ ty ty' →
    TrKExprS env uvars nameOf trProj Δ val val' →
    env.HasType uvars Δ.toCtx val' ty' →
    TrKBvarFrame ty (some val) (.vlet ty' val')

/-! ### The interleaved reconciliation relation -/

variable (env : VEnv) (uvars : Nat) (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- The two concrete stacks (both innermost-first) merge into one
    interleaved `KVLCtx`: `bvar_*` steps consume a de Bruijn frame
    (`(ty, none)` ↦ `.vlam`, `(ty, some val)` ↦ `.vlet`), `fvar` steps
    consume an `lctx` declaration. Payloads translate at the entry's
    TAIL — types are stored unlifted at their binding depth, matching
    `KVLCtx.find?`'s lifting on the way out (which is what
    `lookupVar`'s `lift (idx+1)` mirrors, next slice). `deps` is
    hypothesis-driven (`⊆` is all `KVLCtx.WF` needs). -/
inductive CtxRecon' :
    List (KExpr .anon × Option (KExpr .anon)) →
    List (FVarId × LocalDecl .anon) → KVLCtx → Prop
  | nil : CtxRecon' [] [] []
  | bvar_lam {bs : List (KExpr .anon × Option (KExpr .anon))}
      {fs : List (FVarId × LocalDecl .anon)} {Δ : KVLCtx}
      {ty : KExpr .anon} {ty' : VExpr} :
    CtxRecon' bs fs Δ →
    TrKExprS env uvars nameOf trProj Δ ty ty' →
    env.IsType uvars Δ.toCtx ty' →
    CtxRecon' ((ty, none) :: bs) fs ((none, .vlam ty') :: Δ)
  | bvar_let {bs : List (KExpr .anon × Option (KExpr .anon))}
      {fs : List (FVarId × LocalDecl .anon)} {Δ : KVLCtx}
      {ty val : KExpr .anon} {ty' val' : VExpr} :
    CtxRecon' bs fs Δ →
    TrKExprS env uvars nameOf trProj Δ ty ty' →
    TrKExprS env uvars nameOf trProj Δ val val' →
    env.HasType uvars Δ.toCtx val' ty' →
    CtxRecon' ((ty, some val) :: bs) fs ((none, .vlet ty' val') :: Δ)
  | fvar {bs : List (KExpr .anon × Option (KExpr .anon))}
      {fs : List (FVarId × LocalDecl .anon)} {Δ : KVLCtx}
      {fv : FVarId} {deps : List FVarId} {d : LocalDecl .anon}
      {vd : VLocalDecl} :
    CtxRecon' bs fs Δ →
    TrKLocalDecl env uvars nameOf trProj Δ d vd →
    deps ⊆ Δ.fvars →
    CtxRecon' bs ((fv, d) :: fs) ((some (fv, deps), vd) :: Δ)

namespace CtxRecon'

variable {env : VEnv} {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}

/-- Head inversion at a `(none, .vlam)` entry: only `bvar_lam` fits. -/
theorem bvar_lam_inv {bs' : List (KExpr .anon × Option (KExpr .anon))}
    {fs : List (FVarId × LocalDecl .anon)} {Δ : KVLCtx} {ty' : VExpr}
    (H : CtxRecon' env uvars nameOf trProj bs' fs
      ((none, .vlam ty') :: Δ)) :
    ∃ ty bs, bs' = (ty, none) :: bs ∧
      CtxRecon' env uvars nameOf trProj bs fs Δ :=
  match H with
  | .bvar_lam H1 _ _ => ⟨_, _, rfl, H1⟩

/-- Head inversion at a `(none, .vlet)` entry: only `bvar_let` fits. -/
theorem bvar_let_inv {bs' : List (KExpr .anon × Option (KExpr .anon))}
    {fs : List (FVarId × LocalDecl .anon)} {Δ : KVLCtx}
    {ty' val' : VExpr}
    (H : CtxRecon' env uvars nameOf trProj bs' fs
      ((none, .vlet ty' val') :: Δ)) :
    ∃ ty val bs, bs' = (ty, some val) :: bs ∧
      CtxRecon' env uvars nameOf trProj bs fs Δ :=
  match H with
  | .bvar_let H1 _ _ _ => ⟨_, _, _, rfl, H1⟩

theorem bvars_eq {bs : List (KExpr .anon × Option (KExpr .anon))}
    {fs : List (FVarId × LocalDecl .anon)} {Δ : KVLCtx}
    (H : CtxRecon' env uvars nameOf trProj bs fs Δ) :
    Δ.bvars = bs.length := by
  induction H with
  | nil => rfl
  | bvar_lam _ _ _ ih => simp [KVLCtx.bvars, ih]
  | bvar_let _ _ _ _ ih => simp [KVLCtx.bvars, ih]
  | fvar _ _ _ ih => simp [KVLCtx.bvars, ih]

theorem fvars_eq {bs : List (KExpr .anon × Option (KExpr .anon))}
    {fs : List (FVarId × LocalDecl .anon)} {Δ : KVLCtx}
    (H : CtxRecon' env uvars nameOf trProj bs fs Δ) :
    Δ.fvars = fs.map (·.1) := by
  induction H with
  | nil => rfl
  | bvar_lam _ _ _ ih => simpa using ih
  | bvar_let _ _ _ _ ih => simpa using ih
  | fvar _ _ _ ih => simp [ih]

/-- The typing-level context WF, given distinct fvar ids (upstream
    `TrLCtx'.wf`). -/
theorem wf {bs : List (KExpr .anon × Option (KExpr .anon))}
    {fs : List (FVarId × LocalDecl .anon)} {Δ : KVLCtx}
    (H : CtxRecon' env uvars nameOf trProj bs fs Δ)
    (nd : (fs.map (·.1)).Nodup) : KVLCtx.WF env uvars Δ := by
  induction H with
  | nil => trivial
  | bvar_lam _ _ h2 ih => exact ⟨ih nd, nofun, h2⟩
  | bvar_let _ _ _ h3 ih => exact ⟨ih nd, nofun, h3⟩
  | @fvar bs fs Δ fv deps d vd H1 h1 h2 ih =>
    rw [List.map_cons] at nd
    have ⟨nd1, nd2⟩ := List.nodup_cons.mp nd
    refine ⟨ih nd2, ?_, h1.wf⟩
    intro fv' deps' heq
    cases heq
    refine ⟨?_, h2⟩
    rw [H1.fvars_eq]
    exact nd1

/-- The bvar-side lookup bridge: the `i`-innermost de Bruijn frame
    resolves in `Δ`, its payloads sit translated at the frame's tail
    suffix `Δ₀`, and the `KBVLift` witness re-bases `Δ₀` to the full
    `Δ` — KExpr shift `i+1` (every crossed frame, the hit included),
    VExpr lift `vd.depth + m` (`m` = depth sum strictly above the
    hit, matching `find?`'s lift-out). -/
theorem bvar_frame {bs : List (KExpr .anon × Option (KExpr .anon))}
    {fs : List (FVarId × LocalDecl .anon)} {Δ : KVLCtx}
    (H : CtxRecon' env uvars nameOf trProj bs fs Δ) :
    (fs.map (·.1)).Nodup →
    ∀ {i : Nat} {ty : KExpr .anon} {ov : Option (KExpr .anon)},
      bs[i]? = some (ty, ov) →
      ∃ (Δ₀ : KVLCtx) (vd : VLocalDecl) (m : Nat),
        KVLCtx.KBVLift Δ₀ Δ (i + 1) 0 (vd.depth + m) 0 ∧
        KVLCtx.find? Δ (.inl i)
          = some (vd.value.liftN m 0, vd.type.liftN m 0) ∧
        KVLCtx.fvars Δ₀ ⊆ KVLCtx.fvars Δ ∧
        TrKBvarFrame env uvars nameOf trProj Δ₀ ty ov vd := by
  induction H with
  | nil => intro _ i ty ov hb; simp at hb
  | @bvar_lam bs fs Δ ty₀ ty' H1 h1 h2 ih =>
    intro nd i ty ov hb
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at hb
      cases hb
      refine ⟨Δ, .vlam ty', 0, ?_, ?_, ?_, .vlam h1 h2⟩
      · simpa [Lean4Lean.VLocalDecl.depth] using
          KVLCtx.KBVLift.skip (.vlam ty') .refl
      · simp [KVLCtx.find?, KVLCtx.next]
      · simp only [KVLCtx.fvars_cons_none]
        exact fun _ h => h
    | succ i =>
      simp only [List.getElem?_cons_succ] at hb
      obtain ⟨Δ₀, vd, m, W, hf, hsub, htr⟩ := ih nd hb
      refine ⟨Δ₀, vd, m + 1, ?_, ?_, ?_, htr⟩
      · simpa [Lean4Lean.VLocalDecl.depth, Nat.add_assoc] using
          KVLCtx.KBVLift.skip (.vlam ty') W
      · simp only [KVLCtx.find?, KVLCtx.next, Option.bind_eq_bind, hf]
        simp [Lean4Lean.VLocalDecl.depth, Lean4Lean.VExpr.liftN_liftN]
      · simp only [KVLCtx.fvars_cons_none]
        exact hsub
  | @bvar_let bs fs Δ ty₀ val₀ ty' val' H1 h1 h2 h3 ih =>
    intro nd i ty ov hb
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at hb
      cases hb
      refine ⟨Δ, .vlet ty' val', 0, ?_, ?_, ?_, .vlet h1 h2 h3⟩
      · simpa [Lean4Lean.VLocalDecl.depth] using
          KVLCtx.KBVLift.skip (.vlet ty' val') .refl
      · simp [KVLCtx.find?, KVLCtx.next]
      · simp only [KVLCtx.fvars_cons_none]
        exact fun _ h => h
    | succ i =>
      simp only [List.getElem?_cons_succ] at hb
      obtain ⟨Δ₀, vd, m, W, hf, hsub, htr⟩ := ih nd hb
      refine ⟨Δ₀, vd, m, ?_, ?_, ?_, htr⟩
      · simpa [Lean4Lean.VLocalDecl.depth] using
          KVLCtx.KBVLift.skip (.vlet ty' val') W
      · simp only [KVLCtx.find?, KVLCtx.next, Option.bind_eq_bind, hf]
        simp [Lean4Lean.VLocalDecl.depth]
      · simp only [KVLCtx.fvars_cons_none]
        exact hsub
  | @fvar bs fs Δ fv deps d vd' H1 h1 h2 ih =>
    intro nd i ty ov hb
    rw [List.map_cons] at nd
    have ⟨nd1, nd2⟩ := List.nodup_cons.mp nd
    obtain ⟨Δ₀, vd, m, W, hf, hsub, htr⟩ := ih nd2 hb
    have hfresh : fv ∉ KVLCtx.fvars Δ₀ := fun hx =>
      nd1 (H1.fvars_eq ▸ hsub hx)
    refine ⟨Δ₀, vd, m + vd'.depth, ?_, ?_, ?_, htr⟩
    · simpa [Nat.add_assoc] using
        KVLCtx.KBVLift.skip_fvar (fv, deps) vd' hfresh W
    · simp only [KVLCtx.find?, KVLCtx.next, Option.bind_eq_bind, hf]
      simp [Lean4Lean.VExpr.liftN_liftN]
    · simp only [KVLCtx.fvars_cons_some]
      exact fun x hx => List.mem_cons_of_mem _ (hsub hx)

/-- The fvar-side lookup bridge: the `j`-innermost `lctx` declaration
    resolves in `Δ` by id, its payloads sit translated at the entry's
    tail suffix `Δ₀`, and the `KBVLift` witness re-bases `Δ₀` to the
    full `Δ` (`dn` = de Bruijn frames crossed above the entry — the
    KExpr-side shift any stale-read analysis must account for; the
    entry itself shifts nothing). -/
theorem fvar_frame {bs : List (KExpr .anon × Option (KExpr .anon))}
    {fs : List (FVarId × LocalDecl .anon)} {Δ : KVLCtx}
    (H : CtxRecon' env uvars nameOf trProj bs fs Δ) :
    (fs.map (·.1)).Nodup →
    ∀ {j : Nat} {fv : FVarId} {d : LocalDecl .anon},
      fs[j]? = some (fv, d) →
      ∃ (Δ₀ : KVLCtx) (vd : VLocalDecl) (dn m : Nat),
        KVLCtx.KBVLift Δ₀ Δ dn 0 (vd.depth + m) 0 ∧
        KVLCtx.find? Δ (.inr fv)
          = some (vd.value.liftN m 0, vd.type.liftN m 0) ∧
        KVLCtx.fvars Δ₀ ⊆ KVLCtx.fvars Δ ∧
        TrKLocalDecl env uvars nameOf trProj Δ₀ d vd := by
  induction H with
  | nil => intro _ j fv d hb; simp at hb
  | @bvar_lam bs fs Δ ty₀ ty' H1 h1 h2 ih =>
    intro nd j fv d hb
    obtain ⟨Δ₀, vd, dn, m, W, hf, hsub, htr⟩ := ih nd hb
    refine ⟨Δ₀, vd, dn + 1, m + 1, ?_, ?_, ?_, htr⟩
    · simpa [Lean4Lean.VLocalDecl.depth, Nat.add_assoc] using
        KVLCtx.KBVLift.skip (.vlam ty') W
    · simp only [KVLCtx.find?, KVLCtx.next, Option.bind_eq_bind, hf]
      simp [Lean4Lean.VLocalDecl.depth, Lean4Lean.VExpr.liftN_liftN]
    · simp only [KVLCtx.fvars_cons_none]
      exact hsub
  | @bvar_let bs fs Δ ty₀ val₀ ty' val' H1 h1 h2 h3 ih =>
    intro nd j fv d hb
    obtain ⟨Δ₀, vd, dn, m, W, hf, hsub, htr⟩ := ih nd hb
    refine ⟨Δ₀, vd, dn + 1, m, ?_, ?_, ?_, htr⟩
    · simpa [Lean4Lean.VLocalDecl.depth] using
        KVLCtx.KBVLift.skip (.vlet ty' val') W
    · simp only [KVLCtx.find?, KVLCtx.next, Option.bind_eq_bind, hf]
      simp [Lean4Lean.VLocalDecl.depth]
    · simp only [KVLCtx.fvars_cons_none]
      exact hsub
  | @fvar bs fs Δ fv₀ deps₀ d₀ vd₀ H1 h1 h2 ih =>
    intro nd j fv d hb
    rw [List.map_cons] at nd
    have ⟨nd1, nd2⟩ := List.nodup_cons.mp nd
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero] at hb
      cases hb
      have hfresh : fv₀ ∉ KVLCtx.fvars Δ := by
        rw [H1.fvars_eq]; exact nd1
      refine ⟨Δ, vd₀, 0, 0, ?_, ?_, ?_, h1⟩
      · simpa using
          KVLCtx.KBVLift.skip_fvar (fv₀, deps₀) vd₀ hfresh .refl
      · simp [KVLCtx.find?, KVLCtx.next]
      · simp only [KVLCtx.fvars_cons_some]
        exact fun x hx => List.mem_cons_of_mem _ hx
    | succ j =>
      simp only [List.getElem?_cons_succ] at hb
      obtain ⟨Δ₀, vd, dn, m, W, hf, hsub, htr⟩ := ih nd2 hb
      have hfv : fv ∈ fs.map (·.1) :=
        List.mem_map.mpr ⟨(fv, d), List.mem_of_getElem? hb, rfl⟩
      have hne : ¬fv₀ = fv := fun hEq => nd1 (hEq ▸ hfv)
      have hfresh : fv₀ ∉ KVLCtx.fvars Δ₀ := fun hx =>
        nd1 (H1.fvars_eq ▸ hsub hx)
      refine ⟨Δ₀, vd, dn, m + vd₀.depth, ?_, ?_, ?_, htr⟩
      · simpa [Nat.add_assoc] using
          KVLCtx.KBVLift.skip_fvar (fv₀, deps₀) vd₀ hfresh W
      · simp [KVLCtx.find?, KVLCtx.next, hne, hf,
          Lean4Lean.VExpr.liftN_liftN]
      · simp only [KVLCtx.fvars_cons_some]
        exact fun x hx => List.mem_cons_of_mem _ (hsub hx)

/-- Env-extension monotonicity: the ghost env grows mid-check (lazy
    ingress) under a live context. -/
theorem mono {env' : VEnv} (henv : env ≤ env')
    {bs : List (KExpr .anon × Option (KExpr .anon))}
    {fs : List (FVarId × LocalDecl .anon)} {Δ : KVLCtx}
    (H : CtxRecon' env uvars nameOf trProj bs fs Δ) :
    CtxRecon' env' uvars nameOf trProj bs fs Δ := by
  induction H with
  | nil => exact .nil
  | bvar_lam _ h1 h2 ih =>
    exact .bvar_lam ih (h1.mono henv) (h2.mono henv)
  | bvar_let _ h1 h2 h3 ih =>
    exact .bvar_let ih (h1.mono henv) (h2.mono henv) (h3.mono henv)
  | fvar _ h1 h2 ih => exact .fvar ih (h1.mono henv) h2

end CtxRecon'

/-! ### The packaged reconciliation invariant -/

variable (env : VEnv) (uvars : Nat) (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- The per-call context invariant: the ghost `Δ` projects onto both
    concrete stacks, the `lctx` index is coherent, fvar ids are
    strictly increasing and below the mint counter, and the let
    counter matches. Parameterized by `env`/`nameOf` directly — callers
    pass the current ghost `vs.venv`/`vs.nameOf` and transport along
    growth with `mono`. -/
structure CtxRecon (s : TcState .anon) (Δ : KVLCtx) : Prop where
  size_eq : s.ctx.size = s.letVals.size
  recon : CtxRecon' env uvars nameOf trProj
    ((s.ctx.toList.zip s.letVals.toList).reverse)
    (s.lctx.decls.toList.reverse) Δ
  lwf : s.lctx.WF
  incr : List.Pairwise (fun p q => p.1.id.toNat < q.1.id.toNat)
    s.lctx.decls.toList
  fresh : ∀ p ∈ s.lctx.decls.toList,
    p.1.id.toNat < s.env.nextFVarId.toNat
  lets : s.numLetBindings = Δ.bvarLets

namespace CtxRecon

variable {env : VEnv} {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {s s' : TcState .anon} {Δ : KVLCtx}

/-- The mint counter's next id is absent from the index — discharges
    `LocalContext.WF.push`'s freshness at `openBinder` sites. -/
theorem index_fresh (h : CtxRecon env uvars nameOf trProj s Δ) :
    s.lctx.index[(⟨s.env.nextFVarId⟩ : FVarId)]? = none := by
  match hi : s.lctx.index[(⟨s.env.nextFVarId⟩ : FVarId)]? with
  | none => rfl
  | some i =>
    obtain ⟨p, hp, hfst⟩ := h.lwf.mem_of_index hi
    have h2 := h.fresh p hp
    rw [hfst] at h2
    exact absurd h2 (Nat.lt_irrefl _)

/-- Distinctness of the declared fvar ids, from `incr`. -/
theorem fvars_nodup (h : CtxRecon env uvars nameOf trProj s Δ) :
    ((s.lctx.decls.toList.reverse).map (·.1)).Nodup := by
  have h2 : List.Pairwise (fun p q : FVarId × LocalDecl .anon =>
      p.1 ≠ q.1) s.lctx.decls.toList :=
    h.incr.imp fun hlt heq => absurd (heq ▸ hlt) (Nat.lt_irrefl _)
  simpa using List.pairwise_map.mpr h2

/-- The payoff: a reconciled context is well-formed at the typing
    level. -/
theorem wf (h : CtxRecon env uvars nameOf trProj s Δ) :
    KVLCtx.WF env uvars Δ :=
  h.recon.wf h.fvars_nodup

/-- Env-extension monotonicity. -/
theorem mono {env' : VEnv} (henv : env ≤ env')
    (h : CtxRecon env uvars nameOf trProj s Δ) :
    CtxRecon env' uvars nameOf trProj s Δ :=
  { h with recon := h.recon.mono henv }

theorem bvars_eq (h : CtxRecon env uvars nameOf trProj s Δ) :
    Δ.bvars = s.ctx.size := by
  rw [h.recon.bvars_eq, List.length_reverse, List.length_zip,
    Array.length_toList, Array.length_toList, h.size_eq, Nat.min_self]

theorem fvars_length (h : CtxRecon env uvars nameOf trProj s Δ) :
    Δ.fvars.length = s.lctx.decls.size := by
  rw [h.recon.fvars_eq, List.length_map, List.length_reverse,
    Array.length_toList]

/-- The concrete de Bruijn read (`ctx[n-1-idx]` + parallel `letVals`
    entry) feeds the ghost lookup bridge. -/
private theorem frame_of_read
    (h : CtxRecon env uvars nameOf trProj s Δ) {idx : UInt64}
    {ty : KExpr .anon} {ov : Option (KExpr .anon)}
    (hidx : idx.toNat < s.ctx.size)
    (hty : s.ctx[s.ctx.size - 1 - idx.toNat]? = some ty)
    (hov : s.letVals[s.ctx.size - 1 - idx.toNat]? = some ov) :
    ∃ (Δ₀ : KVLCtx) (vd : Lean4Lean.VLocalDecl) (m : Nat),
      KVLCtx.KBVLift Δ₀ Δ (idx.toNat + 1) 0 (vd.depth + m) 0 ∧
      KVLCtx.find? Δ (.inl idx.toNat)
        = some (vd.value.liftN m 0, vd.type.liftN m 0) ∧
      KVLCtx.fvars Δ₀ ⊆ KVLCtx.fvars Δ ∧
      TrKBvarFrame env uvars nameOf trProj Δ₀ ty ov vd := by
  have hzl : (s.ctx.toList.zip s.letVals.toList).length = s.ctx.size := by
    rw [List.length_zip, Array.length_toList, Array.length_toList,
      h.size_eq, Nat.min_self]
  have hidx' : idx.toNat < (s.ctx.toList.zip s.letVals.toList).length := by
    rw [hzl]; exact hidx
  have hbs : ((s.ctx.toList.zip s.letVals.toList).reverse)[idx.toNat]?
      = some (ty, ov) := by
    rw [List.getElem?_reverse hidx', hzl]
    exact zip_getElem?_of (by rw [Array.getElem?_toList]; exact hty)
      (by rw [Array.getElem?_toList]; exact hov)
  exact h.recon.bvar_frame h.fvars_nodup hbs

/-- `lookupVar`'s soundness core: the concrete array read plus the
    `lift (idx+1)` re-basing translates to the TYPE component of the
    ghost `Δ.find?` — the `TrKExprS.var` discharge for M5/M6. The
    overflow side conditions follow M2 discipline (caller's burden). -/
theorem lookupVar {idx : UInt64} {ty : KExpr .anon}
    {ov : Option (KExpr .anon)}
    (h : CtxRecon env uvars nameOf trProj s Δ)
    (henv : env.Ordered) (htp : TrProjOK env uvars trProj)
    (hidx : idx.toNat < s.ctx.size) (hsz : s.ctx.size < UInt64.size)
    (hty : s.ctx[s.ctx.size - 1 - idx.toNat]? = some ty)
    (hov : s.letVals[s.ctx.size - 1 - idx.toNat]? = some ov)
    (hbig : Δ.bvars + ty.size < UInt64.size) :
    ∃ e A, KVLCtx.find? Δ (.inl idx.toNat) = some (e, A) ∧
      TrKExprS env uvars nameOf trProj Δ
        (KExpr.liftSpec ty (idx + 1) 0) A := by
  obtain ⟨Δ₀, vd, m, W, hf, hsub, htr⟩ := h.frame_of_read hidx hty hov
  have hshift : (idx + 1).toNat = idx.toNat + 1 := by
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [UInt64.toNat_add, h1]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hsz)
  cases htr with
  | vlam h1 h2 =>
    refine ⟨_, _, hf, ?_⟩
    have hw := h1.weakBV henv htp.weakN W hshift
      (show (0 : UInt64).toNat = 0 from rfl) hbig
    simpa [Lean4Lean.VLocalDecl.type, Lean4Lean.VLocalDecl.depth,
      Lean4Lean.VExpr.lift, Lean4Lean.VExpr.liftN_liftN] using hw
  | vlet h1 h2 h3 =>
    refine ⟨_, _, hf, ?_⟩
    have hw := h1.weakBV henv htp.weakN W hshift
      (show (0 : UInt64).toNat = 0 from rfl) hbig
    simpa [Lean4Lean.VLocalDecl.type, Lean4Lean.VLocalDecl.depth]
      using hw

/-- `lookupLetVal`'s soundness core: at a let frame, the lifted stored
    VALUE translates to the VALUE component of the ghost `Δ.find?`
    (which inlines let values at use sites) — the zeta-expansion
    discharge. -/
theorem lookupLetVal {idx : UInt64} {ty val : KExpr .anon}
    (h : CtxRecon env uvars nameOf trProj s Δ)
    (henv : env.Ordered) (htp : TrProjOK env uvars trProj)
    (hidx : idx.toNat < s.ctx.size) (hsz : s.ctx.size < UInt64.size)
    (hty : s.ctx[s.ctx.size - 1 - idx.toNat]? = some ty)
    (hov : s.letVals[s.ctx.size - 1 - idx.toNat]? = some (some val))
    (hbig : Δ.bvars + val.size < UInt64.size) :
    ∃ e A, KVLCtx.find? Δ (.inl idx.toNat) = some (e, A) ∧
      TrKExprS env uvars nameOf trProj Δ
        (KExpr.liftSpec val (idx + 1) 0) e := by
  obtain ⟨Δ₀, vd, m, W, hf, hsub, htr⟩ := h.frame_of_read hidx hty hov
  have hshift : (idx + 1).toNat = idx.toNat + 1 := by
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [UInt64.toNat_add, h1]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hsz)
  cases htr with
  | vlet h1 h2 h3 =>
    refine ⟨_, _, hf, ?_⟩
    have hw := h2.weakBV henv htp.weakN W hshift
      (show (0 : UInt64).toNat = 0 from rfl) hbig
    simpa [Lean4Lean.VLocalDecl.value, Lean4Lean.VLocalDecl.depth]
      using hw

/-- The fvar-side lookup bridge at the concrete state: a successful
    `lctx.find?` resolves in the ghost `Δ` with translated payloads at
    the declaration's tail suffix — `TrKExprS.fvar`'s premise plus the
    re-basing data for M6's read-site analysis. -/
theorem lctxFind? {fv : FVarId} {d : LocalDecl .anon}
    (h : CtxRecon env uvars nameOf trProj s Δ)
    (hf : s.lctx.find? fv = some d) :
    ∃ (Δ₀ : KVLCtx) (vd : Lean4Lean.VLocalDecl) (dn m : Nat),
      KVLCtx.KBVLift Δ₀ Δ dn 0 (vd.depth + m) 0 ∧
      KVLCtx.find? Δ (.inr fv)
        = some (vd.value.liftN m 0, vd.type.liftN m 0) ∧
      KVLCtx.fvars Δ₀ ⊆ KVLCtx.fvars Δ ∧
      TrKLocalDecl env uvars nameOf trProj Δ₀ d vd := by
  obtain ⟨i, hlt, hd⟩ := h.lwf.find?_pos hf
  have hj : (s.lctx.decls.toList.reverse)[s.lctx.decls.size - 1 - i]?
      = some (fv, d) := by
    have hidx : s.lctx.decls.size - 1 - (s.lctx.decls.size - 1 - i)
        = i := by omega
    rw [List.getElem?_reverse
      (by rw [Array.length_toList]; omega : s.lctx.decls.size - 1 - i
        < s.lctx.decls.toList.length)]
    rw [Array.length_toList, hidx, Array.getElem?_toList]
    exact hd
  exact h.recon.fvar_frame h.fvars_nodup hj

/-- Fvar leaves resolve — the bare `TrKExprS.fvar` premise. -/
theorem fvar_resolves {fv : FVarId} {d : LocalDecl .anon}
    (h : CtxRecon env uvars nameOf trProj s Δ)
    (hf : s.lctx.find? fv = some d) :
    ∃ e A, KVLCtx.find? Δ (.inr fv) = some (e, A) :=
  let ⟨_, _, _, _, _, hf', _, _⟩ := h.lctxFind? hf
  ⟨_, _, hf'⟩

/-- The empty context (per-check entry state). -/
theorem empty (hctx : s.ctx = #[]) (hlet : s.letVals = #[])
    (hnum : s.numLetBindings = 0) (hlctx : s.lctx = {}) :
    CtxRecon env uvars nameOf trProj s [] where
  size_eq := by rw [hctx, hlet]; rfl
  recon := by rw [hctx, hlet, hlctx]; exact .nil
  lwf := by rw [hlctx]; exact .empty
  incr := by rw [hlctx]; exact .nil
  fresh := by rw [hlctx]; exact fun p hp => nomatch hp
  lets := by rw [hnum]; rfl

/-- The wide frame: any state operation leaving the context fields
    untouched (and not shrinking the mint counter) preserves the
    reconciliation. -/
theorem of_fields_eq (h : CtxRecon env uvars nameOf trProj s Δ)
    (hctx : s'.ctx = s.ctx) (hlet : s'.letVals = s.letVals)
    (hnum : s'.numLetBindings = s.numLetBindings)
    (hlctx : s'.lctx = s.lctx)
    (hnext : s.env.nextFVarId.toNat ≤ s'.env.nextFVarId.toNat) :
    CtxRecon env uvars nameOf trProj s' Δ where
  size_eq := by rw [hctx, hlet]; exact h.size_eq
  recon := by rw [hctx, hlet, hlctx]; exact h.recon
  lwf := by rw [hlctx]; exact h.lwf
  incr := by rw [hlctx]; exact h.incr
  fresh := by
    rw [hlctx]
    exact fun p hp => Nat.lt_of_lt_of_le (h.fresh p hp) hnext
  lets := by rw [hnum]; exact h.lets

/-! #### Step lemmas: the context ops as ghost transitions -/

/-- `pushLocal ty` extends Δ by a de Bruijn lambda frame. -/
theorem pushLocal {ty : KExpr .anon} {ty' : VExpr}
    (h : CtxRecon env uvars nameOf trProj s Δ)
    (hty : TrKExprS env uvars nameOf trProj Δ ty ty')
    (hty' : env.IsType uvars Δ.toCtx ty')
    (hctx : s'.ctx = s.ctx.push ty)
    (hlet : s'.letVals = s.letVals.push none)
    (hnum : s'.numLetBindings = s.numLetBindings)
    (hlctx : s'.lctx = s.lctx)
    (hnext : s.env.nextFVarId.toNat ≤ s'.env.nextFVarId.toNat) :
    CtxRecon env uvars nameOf trProj s' ((none, .vlam ty') :: Δ) where
  size_eq := by rw [hctx, hlet]; simp [h.size_eq]
  recon := by
    have hzip : (s'.ctx.toList.zip s'.letVals.toList).reverse
        = (ty, none) :: (s.ctx.toList.zip s.letVals.toList).reverse := by
      rw [hctx, hlet, Array.toList_push, Array.toList_push,
        zip_concat _ _ _ _ (by simp [h.size_eq])]
      simp
    rw [hzip, hlctx]
    exact .bvar_lam h.recon hty hty'
  lwf := by rw [hlctx]; exact h.lwf
  incr := by rw [hlctx]; exact h.incr
  fresh := by
    rw [hlctx]
    exact fun p hp => Nat.lt_of_lt_of_le (h.fresh p hp) hnext
  lets := by rw [hnum, h.lets]; rfl

/-- `pushLet ty val` extends Δ by a de Bruijn let frame. -/
theorem pushLet {ty val : KExpr .anon} {ty' val' : VExpr}
    (h : CtxRecon env uvars nameOf trProj s Δ)
    (hty : TrKExprS env uvars nameOf trProj Δ ty ty')
    (hval : TrKExprS env uvars nameOf trProj Δ val val')
    (hval' : env.HasType uvars Δ.toCtx val' ty')
    (hctx : s'.ctx = s.ctx.push ty)
    (hlet : s'.letVals = s.letVals.push (some val))
    (hnum : s'.numLetBindings = s.numLetBindings + 1)
    (hlctx : s'.lctx = s.lctx)
    (hnext : s.env.nextFVarId.toNat ≤ s'.env.nextFVarId.toNat) :
    CtxRecon env uvars nameOf trProj s'
      ((none, .vlet ty' val') :: Δ) where
  size_eq := by rw [hctx, hlet]; simp [h.size_eq]
  recon := by
    have hzip : (s'.ctx.toList.zip s'.letVals.toList).reverse
        = (ty, some val) ::
          (s.ctx.toList.zip s.letVals.toList).reverse := by
      rw [hctx, hlet, Array.toList_push, Array.toList_push,
        zip_concat _ _ _ _ (by simp [h.size_eq])]
      simp
    rw [hzip, hlctx]
    exact .bvar_let h.recon hty hval hval'
  lwf := by rw [hlctx]; exact h.lwf
  incr := by rw [hlctx]; exact h.incr
  fresh := by
    rw [hlctx]
    exact fun p hp => Nat.lt_of_lt_of_le (h.fresh p hp) hnext
  lets := by rw [hnum, h.lets]; rfl

/-- `popLocal` at a lambda frame (Δ-head `(none, .vlam _)`; the walker
    knows the head form — Δ is its own ghost data). -/
theorem pop_lam {ty' : VExpr}
    (h : CtxRecon env uvars nameOf trProj s ((none, .vlam ty') :: Δ))
    (hctx : s'.ctx = s.ctx.pop) (hlet : s'.letVals = s.letVals.pop)
    (hnum : s'.numLetBindings = s.numLetBindings)
    (hlctx : s'.lctx = s.lctx)
    (hnext : s.env.nextFVarId.toNat ≤ s'.env.nextFVarId.toNat) :
    CtxRecon env uvars nameOf trProj s' Δ := by
  obtain ⟨ty, bs, hbs, hrec⟩ := h.recon.bvar_lam_inv
  have hlen : s.ctx.toList.length = s.letVals.toList.length := by
    simp [h.size_eq]
  have hz : s.ctx.toList.zip s.letVals.toList
      = bs.reverse ++ [(ty, none)] := by
    have h2 := congrArg List.reverse hbs
    rwa [List.reverse_reverse, List.reverse_cons] at h2
  have hz' : (s'.ctx.toList.zip s'.letVals.toList).reverse = bs := by
    rw [hctx, hlet, Array.toList_pop, Array.toList_pop,
      zip_dropLast _ _ hlen, hz]
    simp
  exact {
    size_eq := by rw [hctx, hlet]; simp [h.size_eq]
    recon := by rw [hz', hlctx]; exact hrec
    lwf := by rw [hlctx]; exact h.lwf
    incr := by rw [hlctx]; exact h.incr
    fresh := by
      rw [hlctx]
      exact fun p hp => Nat.lt_of_lt_of_le (h.fresh p hp) hnext
    lets := by rw [hnum]; exact h.lets }

/-- `popLocal` at a let frame (Δ-head `(none, .vlet _ _)`). -/
theorem pop_let {ty' val' : VExpr}
    (h : CtxRecon env uvars nameOf trProj s
      ((none, .vlet ty' val') :: Δ))
    (hctx : s'.ctx = s.ctx.pop) (hlet : s'.letVals = s.letVals.pop)
    (hnum : s'.numLetBindings = s.numLetBindings - 1)
    (hlctx : s'.lctx = s.lctx)
    (hnext : s.env.nextFVarId.toNat ≤ s'.env.nextFVarId.toNat) :
    CtxRecon env uvars nameOf trProj s' Δ := by
  obtain ⟨ty, val, bs, hbs, hrec⟩ := h.recon.bvar_let_inv
  have hlen : s.ctx.toList.length = s.letVals.toList.length := by
    simp [h.size_eq]
  have hz : s.ctx.toList.zip s.letVals.toList
      = bs.reverse ++ [(ty, some val)] := by
    have h2 := congrArg List.reverse hbs
    rwa [List.reverse_reverse, List.reverse_cons] at h2
  have hz' : (s'.ctx.toList.zip s'.letVals.toList).reverse = bs := by
    rw [hctx, hlet, Array.toList_pop, Array.toList_pop,
      zip_dropLast _ _ hlen, hz]
    simp
  exact {
    size_eq := by rw [hctx, hlet]; simp [h.size_eq]
    recon := by rw [hz', hlctx]; exact hrec
    lwf := by rw [hlctx]; exact h.lwf
    incr := by rw [hlctx]; exact h.incr
    fresh := by
      rw [hlctx]
      exact fun p hp => Nat.lt_of_lt_of_le (h.fresh p hp) hnext
    lets := by rw [hnum, h.lets]; simp }

/-- The fused mint-and-push step: covers `openBinder`,
    `openBinderWithFV`, `openLet` and `pushFVarDeclAnon` (all mint
    `fv = ⟨nextFVarId⟩`, push one declaration, and advance the
    counter — `hnext` is STRICT; its no-overflow discharge is the
    caller's, M2 discipline). -/
theorem openFVar {d : LocalDecl .anon} {vd : VLocalDecl}
    {deps : List FVarId}
    (h : CtxRecon env uvars nameOf trProj s Δ)
    (htr : TrKLocalDecl env uvars nameOf trProj Δ d vd)
    (hdeps : deps ⊆ Δ.fvars)
    (hctx : s'.ctx = s.ctx) (hlet : s'.letVals = s.letVals)
    (hnum : s'.numLetBindings = s.numLetBindings)
    (hlctx : s'.lctx = s.lctx.push ⟨s.env.nextFVarId⟩ d)
    (hnext : s.env.nextFVarId.toNat < s'.env.nextFVarId.toNat) :
    CtxRecon env uvars nameOf trProj s'
      ((some (⟨s.env.nextFVarId⟩, deps), vd) :: Δ) where
  size_eq := by rw [hctx, hlet]; exact h.size_eq
  recon := by
    have hfs : (s.lctx.push ⟨s.env.nextFVarId⟩ d).decls.toList.reverse
        = (⟨s.env.nextFVarId⟩, d) :: s.lctx.decls.toList.reverse := by
      simp [LocalContext.push, Array.toList_push]
    rw [hctx, hlet, hlctx, hfs]
    exact .fvar h.recon htr hdeps
  lwf := by
    rw [hlctx]
    exact h.lwf.push h.index_fresh
  incr := by
    rw [hlctx]
    simp only [LocalContext.push, Array.toList_push]
    rw [List.pairwise_append]
    refine ⟨h.incr, by simp, ?_⟩
    intro p hp q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact h.fresh p hp
  fresh := by
    rw [hlctx]
    simp only [LocalContext.push, Array.toList_push]
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact Nat.lt_trans (h.fresh p hp) hnext
    · rw [List.mem_singleton] at hp
      subst hp
      exact hnext
  lets := by rw [hnum, h.lets]; rfl

end CtxRecon

end Ix.Tc
