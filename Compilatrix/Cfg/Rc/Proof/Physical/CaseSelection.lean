import Compilatrix.Own.Plain.Check
import Compilatrix.Fir.Proof.Unfold

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native

def firCase (key : Key.CtorKey) : List Fir.Alt → Option Fir.Code → Option Fir.Code
  | [], default => default
  | .mk tag body :: rest, default => if tag = key then some body else firCase key rest default

def ownCase (key : Key.CtorKey) : List Own.Plain.Alt → Option Own.Plain.Code → Option Own.Plain.Code
  | [], default => default
  | .mk tag body :: rest, default => if tag = key then some body else ownCase key rest default

theorem firCase_lower (key : Key.CtorKey) (live : List Fir.Var) (joins : Own.Plain.Joins)
    (alts : List Fir.Alt) (default : Option Fir.Code) :
    ownCase key (Own.Plain.lowerAlts live joins alts) (Own.Plain.lowerOpt live joins default) =
      (firCase key alts default).map (Own.Plain.lowerCode live joins) := by
  induction alts with
  | nil => cases default <;> rfl
  | cons alt rest ih =>
    cases alt
    simp only [Own.Plain.lowerAlts, ownCase, firCase]
    split <;> simp_all

theorem firCase_scope {key : Key.CtorKey} {functions : Own.Plain.Signatures}
    {live : List Fir.Var} {joins : Own.Plain.JoinArities}
    {alts : List Fir.Alt} {default : Option Fir.Code} {body : Fir.Code}
    (arms : Own.Plain.scopeAlts functions live joins alts = true)
    (fallback : Own.Plain.scopeOpt functions live joins default = true)
    (selected : firCase key alts default = some body) : Own.Plain.scopeOk functions live joins body = true := by
  induction alts with
  | nil => cases selected; exact fallback
  | cons alt rest ih =>
    cases alt with
    | mk tag code =>
      simp only [firCase] at selected
      simp only [Own.Plain.scopeAlts, Bool.and_eq_true] at arms
      split at selected
      · cases selected; exact arms.1
      · exact ih arms.2 selected

theorem firCase_size {key : Key.CtorKey} {alts : List Fir.Alt}
    {default : Option Fir.Code} {body : Fir.Code}
    (selected : firCase key alts default = some body) :
    body.size ≤ Fir.Code.altsSize alts + Fir.Code.optSize default := by
  induction alts with
  | nil => cases selected; simp [Fir.Code.altsSize, Fir.Code.optSize]
  | cons alt rest ih =>
    cases alt with
    | mk tag code =>
      simp only [firCase] at selected
      split at selected
      · cases selected; simp only [Fir.Code.altsSize]; omega
      · have := ih selected; simp only [Fir.Code.altsSize]; omega

theorem firCase_eval (F : Fir.Program) (clock : Nat) (env : Fir.Env)
    (joins : List Fir.JEntry) (key : Key.CtorKey) (alts : List Fir.Alt) (default : Option Fir.Code) :
    Fir.evalAlts F clock env joins key alts default =
      match firCase key alts default with
      | none => .stuck
      | some body => Fir.eval F clock env joins body := by
  induction alts with
  | nil => cases default <;> simp [Fir.evalAlts_nil, firCase]
  | cons alt rest ih =>
    cases alt
    rw [Fir.evalAlts_cons]
    simp only [firCase]
    split <;> simp_all





end Compilatrix.Cfg.Rc.Native
