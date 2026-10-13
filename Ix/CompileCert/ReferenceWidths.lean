import Ix.CompileCert.PreseedBounds

/-! Reference-width provenance through the actual preseed collector. Named
references inherit widths from the dependency lookup; literal addresses use
the production hash wrapper's proved output length. -/

namespace Ix.CompileCert.ReferenceWidths

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame

def LookupWidths (environment : CompileEnv) (state : BlockState) : Prop :=
  ∀ name address, ExpressionState.lookupBinding environment (ExpressionState.bindingView state) name = some address →
    address.hash.size = 32

def AllWidths (refs : Array Address) : Prop := ∀ address ∈ refs, address.hash.size = 32

theorem AllWidths.push {refs : Array Address} {address : Address}
    (prior : AllWidths refs) (added : address.hash.size = 32) : AllWidths (refs.push address) := by
  intro query member
  rcases Array.mem_push.mp member with old | same
  · exact prior query old
  · exact same ▸ added

def Safe (action : CompileM α) (post : α → Prop) : Prop :=
  ∀ context before, LookupWidths context.1 before →
    LookupWidths context.1 (rawRun action context before).2 ∧
      ∀ value, (rawRun action context before).1 = .ok value → post value

theorem Safe.pure {value : α} {post : α → Prop} (good : post value) : Safe (pure value) post := by
  intro context before widths
  exact ⟨widths, by intro result same; cases Except.ok.inj same; exact good⟩

theorem Safe.throw (error : CompileError) (post : α → Prop) : Safe (throw error) post :=
  fun _ _ widths => ⟨widths, by intro value bad; cases bad⟩

theorem Safe.bind {action : CompileM α} {next : α → CompileM β} {first : α → Prop} {last : β → Prop}
    (head : Safe action first) (tail : ∀ value, first value → Safe (next value) last) : Safe (action >>= next) last := by
  intro context before widths
  have checked := head context before widths
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome after =>
    rw [ran] at checked
    cases outcome with
    | error error => exact ⟨checked.1, by intro value bad; cases bad⟩
    | ok value => exact tail value (checked.2 value rfl) context after checked.1

theorem Safe.framed {action : CompileM α} (frame : PreseedReferences.BindingFrame action) :
    Safe action (fun _ => True) := by
  intro context before widths
  refine ⟨?_, by intros; trivial⟩
  intro name address found
  rw [frame context before] at found
  exact widths name address found

theorem Safe.lookup (name : Name) : Safe (lookupConstAddr name) (fun address => address.hash.size = 32) := by
  intro context before widths
  refine ⟨(Safe.framed (PreseedReferences.BindingFrame.lookup name) context before widths).1, ?_⟩
  intro address ran
  exact widths name address (PreseedReferences.lookup_value context before name address ran)

theorem Safe.blob (bytes : ByteArray) : Safe (storeBlob bytes) (fun address => address.hash.size = 32) := by
  intro context before widths
  refine ⟨(Safe.framed (PreseedReferences.BindingFrame.blob bytes) context before widths).1, ?_⟩
  intro address ran
  rw [BlobWrites.storeBlob_run] at ran
  cases wrote : before.storeBlob context.1.blobs (Address.blake3 bytes) bytes
  all_goals rw [wrote] at ran
  · cases ran
  · cases Except.ok.inj ran
    exact WireTables.blake3_width bytes

theorem structural_widths (hint : Address) (mutualContext : MutCtx) (params : List Name)
    (source : Expr) (initial : ExprTableCollection) (prior : AllWidths initial.1) :
    Safe (collectExprTablesStructural hint mutualContext params source initial) (fun result => AllWidths result.1) := by
  induction source generalizing initial
  all_goals
    rcases initial with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural]
    split
    · exact Safe.pure prior
  case bvar => exact Safe.pure prior
  case fvar => exact Safe.throw _ _
  case mvar => exact Safe.throw _ _
  case sort level hash _ =>
    exact Safe.bind (Safe.framed (PreseedReferences.BindingFrame.compileUniv level)) (fun _ _ => Safe.pure prior)
  case const name levels hash _ =>
    apply Safe.bind (Safe.framed (PreseedReferences.BindingFrame.levels levels.toList univs))
    intro values _
    split
    · exact Safe.bind (Safe.lookup name) (fun _ width => Safe.pure (prior.push width))
    · exact Safe.pure prior
  case app first last hash firstIH lastIH _ =>
    exact Safe.bind (firstIH _ prior) (fun result valid => lastIH result valid)
  case lam name type body info hash firstIH lastIH _ =>
    exact Safe.bind (firstIH _ prior) (fun result valid => lastIH result valid)
  case forallE name type body info hash firstIH lastIH _ =>
    exact Safe.bind (firstIH _ prior) (fun result valid => lastIH result valid)
  case letE name type value body nonDep hash firstIH middleIH lastIH _ =>
    exact Safe.bind (firstIH _ prior) (fun result valid =>
      Safe.bind (middleIH result valid) (fun result valid => lastIH result valid))
  case lit literal hash _ =>
    cases literal
    all_goals exact Safe.bind (Safe.blob _) (fun _ width => Safe.pure (prior.push width))
  case mdata metadata child hash childIH _ => exact childIH _ prior
  case proj name index child hash childIH _ =>
    exact Safe.bind (Safe.lookup name) (fun _ width => childIH _ (prior.push width))

theorem root_widths (context : CompileEnv × BlockEnv) (before after : BlockState)
    (source : Expr) (params : List Name) (initial output : ExprTableCollection)
    (widths : LookupWidths context.1 before) (prior : AllWidths initial.1)
    (ran : rawRun (withUnivCtx params (collectExprTables source (univParamsKey params) initial)) context before = (.ok output, after)) :
    LookupWidths context.1 after ∧ AllWidths output.1 := by
  rw [PreseedReferences.root_run] at ran
  have checked := structural_widths (univParamsKey params) context.2.mutCtx params source initial prior
    (context.1, { context.2 with univCtx := params }) { before with univCache := {} } widths
  rw [ran] at checked
  exact ⟨checked.1, checked.2 output rfl⟩

theorem roots_widths (context : CompileEnv × BlockEnv) (roots : List (Expr × List Name))
    (before after : BlockState) (initial output : ExprTableCollection)
    (widths : LookupWidths context.1 before) (prior : AllWidths initial.1)
    (ran : rawRun (collectPreseedExprs roots initial) context before = (.ok output, after)) :
    LookupWidths context.1 after ∧ AllWidths output.1 := by
  induction roots generalizing before initial with
  | nil =>
    rw [collectPreseedExprs, rawRun_pure] at ran
    obtain ⟨result, state⟩ := Prod.mk.inj ran
    cases Except.ok.inj result
    cases state
    exact ⟨widths, prior⟩
  | cons root rest ih =>
    rcases root with ⟨source, params⟩
    rw [collectPreseedExprs] at ran
    obtain ⟨middle, state, first, last⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    have checked := root_widths context before state source params initial middle widths prior first
    exact ih state middle checked.1 checked.2 last

theorem roots_initial (context : CompileEnv × BlockEnv) (roots : Array (Expr × List Name))
    (before after : BlockState) (output : ExprTableCollection) (widths : LookupWidths context.1 before)
    (ran : rawRun (collectPreseedExprs roots.toList (#[], #[], {})) context before = (.ok output, after)) :
    AllWidths output.1 :=
  (roots_widths context roots.toList before after _ output widths (by simp [AllWidths]) ran).2

end Ix.CompileCert.ReferenceWidths
