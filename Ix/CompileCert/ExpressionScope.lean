import Ix.CompileCert.DefinitionReading

/-! Expression correctness needs self correspondence only for names occurring
as constants in the source expression. The actual mutual context is retained.
The original whole-context APIs keep their statements and domains. -/

namespace Ix.CompileCert.ExpressionScope

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame Ix.CompileCert.ExpressionState

def Scoped (allows : Name → Prop) : Expr → Prop
  | .const name _ _ => allows name
  | .app first last _ | .lam _ first last _ _ | .forallE _ first last _ _ =>
    Scoped allows first ∧ Scoped allows last
  | .letE _ first middle last _ _ => Scoped allows first ∧ Scoped allows middle ∧ Scoped allows last
  | .proj _ _ child _ | .mdata _ child _ => Scoped allows child
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .lit .. => True

def SelfName (block : BlockEnv) (self : Nat → Option Kernel.Name)
    (names : Name → Kernel.Name → Prop) (name : Name) : Prop :=
  ∀ index, block.mutCtx.get? name = some index → ∃ target, self index = some target ∧ names name target

def NoSelf (block : BlockEnv) (source : Expr) : Prop := Scoped (fun name => block.mutCtx.get? name = none) source

theorem Scoped.mono {first last : Name → Prop} (implies : ∀ name, first name → last name)
    (source : Expr) (scope : Scoped first source) : Scoped last source := by
  induction source with
  | const name _ _ => exact implies name scope
  | app _ _ _ left right | lam _ _ _ _ _ left right | forallE _ _ _ _ _ left right =>
    exact ⟨left scope.1, right scope.2⟩
  | letE _ _ _ _ _ _ first middle last => exact ⟨first scope.1, middle scope.2.1, last scope.2.2⟩
  | proj _ _ _ _ child | mdata _ _ _ child => exact child scope
  | _ => trivial

theorem NoSelf.scoped (block : BlockEnv) (source : Expr) (scope : NoSelf block source)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop) : Scoped (SelfName block self names) source := by
  apply Scoped.mono _ source scope
  intro name missing index found
  rw [missing] at found
  cases found

section Application

variable (cx : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name)
  (self : Nat → Option Kernel.Name) (related : Expr → Kernel.Expr → Prop) (bindings : Bindings)

theorem appTotal_scoped (allows : Name → Prop) (compile : Expr → CompileM (Ixon.Expr × UInt64))
    (context : CompileEnv × BlockEnv) (bound : Nat)
    (recursive : ∀ source, exprCompileDepth source ≤ bound → Scoped allows source →
      ∀ state, Good cx base param self related bindings state →
        Checked cx base param self related bindings source state (rawRun (compile source) context state))
    (applications : ∀ fn arg hash f a, related fn f → related arg a → related (.app fn arg hash) (.app f a)) :
    ∀ source, exprCompileDepth source ≤ bound → Scoped allows source →
      ∀ before, Good cx base param self related bindings before →
        Checked cx base param self related bindings source before (rawRun (compileAppTotal compile source) context before) := by
  intro source
  induction source with
  | app fn arg hash ihfn _ =>
    intro depth scope before good
    have fnDepth : exprCompileDepth fn ≤ bound := by simp only [exprCompileDepth] at depth; omega
    have argDepth : exprCompileDepth arg ≤ bound := by simp only [exprCompileDepth] at depth; omega
    rw [appTotal_app_eq]
    exact app_pair_checked cx base param self related bindings fn arg hash _ _ context before
      (ihfn fnDepth scope.1 before good) (recursive arg argDepth scope.2) (applications fn arg hash)
  | _ => intros; exact recursive _ (by assumption) (by assumption) _ (by assumption)

theorem app_step_scoped (allows : Name → Prop) (compile : Expr → CompileM (Ixon.Expr × UInt64))
    (fn arg : Expr) (hash : Address) (context : CompileEnv × BlockEnv)
    (scope : Scoped allows (.app fn arg hash))
    (before : BlockState) (good : Good cx base param self related bindings before)
    (children : ∀ child, exprCompileDepth child < exprCompileDepth (.app fn arg hash) → Scoped allows child →
      ∀ state, Good cx base param self related bindings state →
        Checked cx base param self related bindings child state (rawRun (compile child) context state))
    (applications : ∀ f a h tf ta, related f tf → related a ta → related (.app f a h) (.app tf ta)) :
    Checked cx base param self related bindings (.app fn arg hash) before
      (rawRun (compileExprTotalStep compile (.app fn arg hash)) context before) := by
  change Checked cx base param self related bindings (.app fn arg hash) before
    (rawRun (compileAppTotal compile (.app fn arg hash)) context before)
  rw [appTotal_app_eq]
  apply app_pair_checked cx base param self related bindings fn arg hash _ _ context before
  · apply appTotal_scoped cx base param self related bindings allows compile context (max (exprCompileDepth fn) (exprCompileDepth arg))
    · intro child depth childScope state valid
      apply children child ?_ childScope state valid
      simp only [exprCompileDepth]
      omega
    · exact applications
    · exact Nat.le_max_left _ _
    · exact scope.1
    · exact good
  · apply children arg
    · simp only [exprCompileDepth]; omega
    · exact scope.2
  · exact applications fn arg hash

end Application

theorem partial_scoped (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) :
    ∀ source, Scoped (SelfName context.2 self names) source → ∀ before,
      Good cx base (Kernel.Reader.paramOf params) self (Related names context.2.univCtx params) bindings before →
      Checked cx base (Kernel.Reader.paramOf params) self (Related names context.2.univCtx params) bindings source before
        (rawRun (compileExprPartial source) context before) := by
  let rel := Related names context.2.univCtx params
  let param := Kernel.Reader.paramOf params
  apply partial_checked_of_step cx base param self rel bindings (Scoped (SelfName context.2 self names)) context
  intro source scope ih before good _
  cases source with
  | bvar index hash => exact bvar_step_checked cx base param self rel bindings _ index hash context before good (.bvar index hash)
  | sort level hash =>
    exact sort_step_checked cx base param self rel bindings _ level hash context before good params rfl arity
      (fun level meaning => .sort hash meaning)
  | const name levels hash =>
    exact const_step_checked_at cx base param self rel bindings _ name levels hash context before good params rfl arity aligned names
      external scope (fun _ targetLevels nameRel levelRel => .const hash levels targetLevels nameRel levelRel)
  | app fn arg hash =>
    apply app_step_scoped cx base param self rel bindings _ _ fn arg hash context scope before good
    · exact ih
    · intro _ _ hash _ _ fnRel argRel; exact .app hash fnRel argRel
  | lam name type body info hash =>
    apply binder_step_checked cx base param self rel bindings false _ name type body info hash context before good aligned
    · intro state valid; exact ih type (by simp only [exprCompileDepth]; omega) scope.1 state valid
    · intro state valid; exact ih body (by simp only [exprCompileDepth]; omega) scope.2 state valid
    · intro _ _ typeRel bodyRel; exact .lam name info hash typeRel bodyRel
  | forallE name type body info hash =>
    apply binder_step_checked cx base param self rel bindings true _ name type body info hash context before good aligned
    · intro state valid; exact ih type (by simp only [exprCompileDepth]; omega) scope.1 state valid
    · intro state valid; exact ih body (by simp only [exprCompileDepth]; omega) scope.2 state valid
    · intro _ _ typeRel bodyRel; exact .all name info hash typeRel bodyRel
  | letE name type value body nonDep hash =>
    apply let_step_checked cx base param self rel bindings _ name type value body nonDep hash context before good aligned
    · intro state valid; exact ih type (by simp only [exprCompileDepth]; omega) scope.1 state valid
    · intro state valid; exact ih value (by simp only [exprCompileDepth]; omega) scope.2.1 state valid
    · intro state valid; exact ih body (by simp only [exprCompileDepth]; omega) scope.2.2 state valid
    · intro _ _ _ typeRel valueRel bodyRel; exact .letE name nonDep hash typeRel valueRel bodyRel
  | lit value hash =>
    cases value with
    | natVal value => exact nat_step_checked cx base param self rel bindings _ value hash context before good aligned (.nat value hash)
    | strVal value => exact string_step_checked cx base param self rel bindings _ value hash context before good aligned (.str value hash)
  | proj name field source hash =>
    apply projection_step_checked cx base param self rel bindings _ name field source hash context before good aligned names external
    · intro state valid; exact ih source (by simp only [exprCompileDepth]; omega) scope state valid
    · intro _ _ nameRel sourceRel; exact .proj field hash nameRel sourceRel
  | mdata data source hash =>
    apply metadata_step_checked cx base param self rel bindings _ data source hash context before good aligned
    · intro state valid; exact ih source (by simp only [exprCompileDepth]; omega) scope state valid
    · intro _ sourceRel; exact .mdata data hash sourceRel
  | fvar name hash => exact ⟨good, extends_refl _, by intro value bad; cases bad⟩
  | mvar name hash => exact ⟨good, extends_refl _, by intro value bad; cases bad⟩

theorem partial_noSelf (cx : Kernel.Reader.Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : Expr) (scope : NoSelf context.2 source)
    (before : BlockState) (good : Good cx base (Kernel.Reader.paramOf params) (fun _ => none)
      (Related names context.2.univCtx params) bindings before) :
    Checked cx base (Kernel.Reader.paramOf params) (fun _ => none) (Related names context.2.univCtx params) bindings source before
      (rawRun (compileExprPartial source) context before) :=
  partial_scoped cx base _ names params bindings context arity aligned external source
    (NoSelf.scoped context.2 source scope _ names) before good

end Ix.CompileCert.ExpressionScope
