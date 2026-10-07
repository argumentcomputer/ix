import Ix.CompileCert.Bridge.Term
import IxC.Kernel.Semantics.EnvFacts

/-!
# M7 X2: the bridge is the lane's export, and the per-compile emission check

**The translation lemma.** The lane already translates an `Ix.Expr` to the reader's syntax:
`ixToKernel tc e = exportExpr tc (← ixExpr e)` (`Translate.lean`), through the `Lean.Expr` it
decompiles to, with the lane's own naming of constants (`ExportContext.name`: the source map's
address key, the pinned name, the recursor convention) and its canonical levels (`exportLevel`).
For a constant W certifies by a direct match, the certified reader's entry *is* `exportExpr` of the
Lean declaration (`checkIndexed'_sound`). `bridge_eq_lane` proves that the bridge, instantiated at
the lane's naming (`laneN`, `laneL`), is that translation (with `mdata` erased on both sides, as
`exportExpr` erases it on Lean terms); `bridge_eq_ixToKernel` is the `mdata`-free case.

**Emission.** For a compiler-built constant (an image, a rewritten definition) no Lean term exists;
the link to the artifact is the hypothesis `Emitted`: the installed definition's value is an
annotation of the bridge of the compiler's value. `checkEmitted` decides it against the certified
fold's environment (`checkEmitted_sound`); L4's emission theorem is what proves it once.
-/

namespace Ix.CompileCert.Bridge

open Ix.CompileCert.Conv (Tm er)

/-! ## The lane's naming as bridge parameters -/

/-- Constants named as the lane names them (the source map, pins, recursor convention). -/
def laneN (cx : ExportContext) (n : Ix.Name) : Option Kernel.Name := (cx.name (ixName n)).toOption

/-- Levels translated as the lane translates them (positional, canonical, checked). -/
def laneL (tc : TermContext) (u : Ix.Level) : Option Kernel.Level :=
  (ixLevel u >>= exportLevel tc).toOption

/-- `ixExpr` with `mdata` erased (as `exportExpr` erases it on `Lean.Expr`). -/
def ixExprE : Ix.Expr → ExportM Lean.Expr
  | .bvar i _ => return .bvar i
  | .sort u _ => return .sort (← ixLevel u)
  | .const n us _ => return .const (ixName n) (← us.toList.mapM ixLevel)
  | .app f a _ => return .app (← ixExprE f) (← ixExprE a)
  | .lam n t b info _ => return .lam (ixName n) (← ixExprE t) (← ixExprE b) info
  | .forallE n t b info _ => return .forallE (ixName n) (← ixExprE t) (← ixExprE b) info
  | .letE n t v b nonDep _ => do
    return .letE (ixName n) (← ixExprE t) (← ixExprE v) (← ixExprE b) nonDep
  | .lit v _ => return .lit v
  | .proj n i e _ => return .proj (ixName n) i (← ixExprE e)
  | .mdata _ e _ => ixExprE e
  | .fvar .. => throw "Ix free variable"
  | .mvar .. => throw "Ix metavariable"

/-- No `mdata` node. -/
def NoMData : Ix.Expr → Prop
  | .app f a _ => NoMData f ∧ NoMData a
  | .lam _ t b _ _ => NoMData t ∧ NoMData b
  | .forallE _ t b _ _ => NoMData t ∧ NoMData b
  | .letE _ t v b _ _ => NoMData t ∧ NoMData v ∧ NoMData b
  | .proj _ _ e _ => NoMData e
  | .mdata .. => False
  | _ => True

theorem ixExprE_eq : ∀ (e : Ix.Expr), NoMData e → ixExprE e = ixExpr e := by
  intro e
  induction e with
  | bvar => intro _; rfl
  | fvar => intro _; rfl
  | mvar => intro _; rfl
  | sort => intro _; rfl
  | const => intro _; rfl
  | app f a _ ihf iha => intro h; simp only [NoMData] at h; simp [ixExprE, ixExpr, ihf h.1, iha h.2]
  | lam n t b i _ iht ihb =>
    intro h; simp only [NoMData] at h; simp [ixExprE, ixExpr, iht h.1, ihb h.2]
  | forallE n t b i _ iht ihb =>
    intro h; simp only [NoMData] at h; simp [ixExprE, ixExpr, iht h.1, ihb h.2]
  | letE n t v b nd _ iht ihv ihb =>
    intro h; simp only [NoMData] at h; simp [ixExprE, ixExpr, iht h.1, ihv h.2.1, ihb h.2.2]
  | lit => intro _; rfl
  | mdata => intro h; simp [NoMData] at h
  | proj n i e _ ih => intro h; simp only [NoMData] at h; simp [ixExprE, ixExpr, ih h]

/-! ## `Except` to `Option` -/

theorem toOption_bind {ε α β : Type} (x : Except ε α) (f : α → Except ε β) :
    (x >>= f).toOption = x.toOption.bind (fun a => (f a).toOption) := by
  cases x <;> rfl

theorem toOption_pure {ε α : Type} (a : α) : (pure a : Except ε α).toOption = some a := rfl

theorem toOption_throw {ε α : Type} (e : ε) : (throw e : Except ε α).toOption = none := rfl

theorem optMap_toOption {α β γ : Type} (g : α → Except String β) (h : β → Except String γ) :
    ∀ (l : List α), optMap (fun a => (g a >>= h).toOption) l =
      (l.mapM g >>= fun bs => bs.mapM h).toOption
  | [] => rfl
  | a :: l => by
    have ih := optMap_toOption g h l
    simp only [optMap, List.mapM_cons]
    cases hg : g a with
    | error e => simp [bind, Except.bind, Except.toOption]
    | ok b =>
      cases hh : h b with
      | error e =>
        simp only [bind, Except.bind, Except.toOption]
        cases l.mapM g <;> simp [pure, Except.pure, List.mapM_cons, hh, bind, Except.bind]
      | ok c =>
        rw [ih]
        cases l.mapM g with
        | error e => simp [bind, Except.bind, Except.toOption]
        | ok bs =>
          simp only [hh, bind, Except.bind, Except.toOption, pure, Except.pure, List.mapM_cons]
          cases bs.mapM h <;> simp

/-! ## The translation lemma -/

/-- The lane's `Ix.Expr → Kernel.Expr` route with `mdata` erased. -/
def ixToKernelE (tc : TermContext) (e : Ix.Expr) : ExportM Kernel.Expr := do
  exportExpr tc (← ixExprE e)

section Translation

variable (tc : TermContext)

local notation "N₀" => laneN tc.context
local notation "L₀" => laneL tc

private theorem lane_bin {x y : Except String Lean.Expr} {X Y : Option Kernel.Expr}
    (hx : X = (x >>= exportExpr tc).toOption) (hy : Y = (y >>= exportExpr tc).toOption)
    (mk : Lean.Expr → Lean.Expr → Lean.Expr) (mk' : Kernel.Expr → Kernel.Expr → Kernel.Expr)
    (hmk : ∀ a b, exportExpr tc (mk a b) = (do return mk' (← exportExpr tc a) (← exportExpr tc b))) :
    app2 mk' X Y = ((do return mk (← x) (← y)) >>= exportExpr tc).toOption := by
  subst hx hy
  cases x with
  | error => simp [bind, Except.bind, Except.toOption]
  | ok a =>
    cases y with
    | error => simp [bind, Except.bind, Except.toOption]
    | ok b =>
      simp only [bind, Except.bind, pure, Except.pure, hmk]
      cases exportExpr tc a <;> cases exportExpr tc b <;> simp [Except.toOption]

/-- **The translation lemma**: at the lane's naming and levels, the bridge is the lane's
translation (through the decompiled `Lean.Expr` and `exportExpr`). -/
theorem bridge_eq_lane : ∀ (e : Ix.Expr), bridge N₀ L₀ e = (ixToKernelE tc e).toOption := by
  intro e
  unfold bridge ixToKernelE
  induction e with
  | bvar i _ => simp [er, bridgeT, ixExprE, exportExpr, bind, Except.bind, pure, Except.pure,
      Except.toOption]
  | fvar => simp [er, bridgeT, ixExprE, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
      Except.toOption]
  | mvar => simp [er, bridgeT, ixExprE, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
      Except.toOption]
  | sort u _ =>
    simp only [er, bridgeT, ixExprE, laneL]
    cases h : ixLevel u with
    | error => simp [bind, Except.bind, Except.toOption]
    | ok l =>
      simp only [bind, Except.bind, pure, Except.pure, exportExpr]
      cases exportLevel tc l <;> simp [Except.toOption]
  | const n us _ =>
    simp only [er, bridgeT, ixExprE, laneN]
    rw [show optMap (laneL tc) us.toList =
      optMap (fun a => (ixLevel a >>= exportLevel tc).toOption) us.toList from rfl,
      optMap_toOption ixLevel (exportLevel tc)]
    cases h : us.toList.mapM ixLevel with
    | error => simp [bind, Except.bind, Except.toOption]
    | ok ls =>
      simp only [bind, Except.bind, pure, Except.pure, exportExpr]
      cases tc.context.name (ixName n) <;> cases ls.mapM (exportLevel tc) <;> simp [Except.toOption]
  | app f a _ ihf iha =>
    simp only [er, bridgeT, ixExprE]
    exact lane_bin tc ihf iha (fun x y => .app x y) (fun x y => .app x y) (fun _ _ => rfl)
  | lam n t b i _ iht ihb =>
    simp only [er, bridgeT, ixExprE]
    exact lane_bin tc iht ihb (fun x y => .lam (ixName n) x y i) (fun x y => .lam x y never)
      (fun _ _ => rfl)
  | forallE n t b i _ iht ihb =>
    simp only [er, bridgeT, ixExprE]
    exact lane_bin tc iht ihb (fun x y => .forallE (ixName n) x y i)
      (fun x y => .forallE x y never) (fun _ _ => rfl)
  | letE n t v b nd _ iht ihv ihb =>
    simp only [er, bridgeT, ixExprE]
    rw [iht, ihv, ihb]
    cases ixExprE t with
    | error => simp [bind, Except.bind, Except.toOption]
    | ok t' =>
      cases ixExprE v with
      | error => simp [bind, Except.bind, Except.toOption]
      | ok v' =>
        cases ixExprE b with
        | error => simp [bind, Except.bind, Except.toOption]
        | ok b' =>
          simp only [bind, Except.bind, pure, Except.pure, exportExpr]
          cases exportExpr tc t' <;> cases exportExpr tc v' <;> cases exportExpr tc b' <;>
            simp [Except.toOption]
  | lit l _ =>
    cases l <;> simp [er, bridgeT, bridgeLit, ixExprE, exportExpr, bind, Except.bind, pure,
      Except.pure, Except.toOption]
  | mdata _ e _ ih => simpa only [er, ixExprE] using ih
  | proj n i e _ ih =>
    simp only [er, bridgeT, ixExprE, laneN]
    rw [ih]
    cases ixExprE e with
    | error => simp [bind, Except.bind, Except.toOption]
    | ok e' =>
      simp only [bind, Except.bind, pure, Except.pure, exportExpr]
      cases tc.context.name (ixName n) <;> cases exportExpr tc e' <;> simp [Except.toOption]

/-- The `mdata`-free case: the bridge is exactly the lane's `ixToKernel`. -/
theorem bridge_eq_ixToKernel {e : Ix.Expr} (h : NoMData e) :
    bridge N₀ L₀ e = (ixToKernel tc e).toOption := by
  rw [bridge_eq_lane, ixToKernelE, ixToKernel, ixExprE_eq e h]

end Translation

/-! ## Emission into the artifact (per-compile hypothesis, L4's theorem) -/

section Emitted

variable (N : Ix.Name → Option Kernel.Name) (L : Ix.Level → Option Kernel.Level)

/-- The artifact's installed definition `c` carries the compiler's type and value: its installed
(annotated) type and value have the bridges of `ty` and `val` as skeletons. -/
def Emitted (env : Kernel.Env) (c : Kernel.Name) (ty val : Ix.Expr) : Prop :=
  ∃ header value hint, Kernel.ConstantInfo.defnInfo header value hint ∈ env.consts ∧
    env.find? c = some (.defnInfo header value hint) ∧
    Skel N L (er ty) header.type ∧ Skel N L (er val) value

/-- The per-compile decision of `Emitted` (recompute and compare against the fold's output). -/
def checkEmitted (env : Kernel.Env) (c : Kernel.Name) (ty val : Ix.Expr) : Bool :=
  match env.find? c with
  | some (.defnInfo header value _) =>
    decide (bridgeT N L (er ty) = some header.type.erasePw) &&
      decide (bridgeT N L (er val) = some value.erasePw)
  | _ => false

theorem checkEmitted_sound {env : Kernel.Env} {c : Kernel.Name} {ty val : Ix.Expr}
    (h : checkEmitted N L env c ty val = true) : Emitted N L env c ty val := by
  unfold checkEmitted at h
  split at h
  · rename_i header value hint hfind
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨header, value, hint, Kernel.Semantics.Env.find?_mem hfind, hfind, h.1, h.2⟩
  · cases h

end Emitted

end Ix.CompileCert.Bridge
