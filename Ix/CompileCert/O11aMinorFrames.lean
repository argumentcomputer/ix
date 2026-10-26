import Ix.CompileCert.OptFrames
import Ix.CompileCert.FramePrimitives
import Ix.Cert.Claims

/-! Frames of the actual O11a adapted minor. Emitted domains come from its
selected input minor; this does not establish scope, resources or values. -/
namespace Ix.CompileCert.O11aMinorFrames
open Ix (Name Expr)
open Ix.AuxGen Ix.Compile.Pass.Opt
open SemanticFrames OptFrames

private theorem fits_instantiate (kind : Ix.SemanticContract.Kind) (e v : Expr) (depth : Nat)
    (matched : fits kind e = true) : fits kind (instantiate1At e v depth) = true := by
  cases kind <;> cases e <;> simp only [fits, Bool.false_eq_true] at matched
  all_goals rfl

theorem instantiate1At_frames (e v : Expr) (depth : Nat) (he : Frames e) (hv : Frames v) :
    Frames (instantiate1At e v depth) := by
  induction e generalizing depth
  all_goals simp only [instantiate1At]
  case bvar i hash => split; exact hv; split <;> trivial
  case mdata data inner hash ih =>
    refine ⟨?_, ih depth he.2⟩
    intro present
    obtain ⟨contract, decoded, matched⟩ := he.1 present
    exact ⟨contract, decoded, fits_instantiate _ _ _ _ matched⟩
  all_goals simp_all only [Frames, Expr.mkApp, Expr.mkLam, Expr.mkForallE,
    Expr.mkLetE, Expr.mkProj, Id.run, and_true]

theorem instantiate1_frames (e v : Expr) (he : Frames e) (hv : Frames v) :
    Frames (instantiate1 e v) := instantiate1At_frames e v 0 he hv

private theorem fits_abstract (kind : Ix.SemanticContract.Kind) (lookup : Name → Option Nat)
    (e : Expr) (scope depth : Nat) : fits kind (batchAbstractWith lookup e scope depth) = fits kind e := by
  cases kind <;> cases e
  all_goals simp only [batchAbstractWith]
  all_goals split
  all_goals try rfl
  all_goals split
  all_goals try rfl
  all_goals try split
  all_goals rfl

theorem batchAbstractWith_frames (lookup : Name → Option Nat) (e : Expr) (scope depth : Nat)
    (valid : Frames e) : Frames (batchAbstractWith lookup e scope depth) := by
  induction e generalizing depth
  all_goals simp only [batchAbstractWith]
  all_goals split
  all_goals try exact valid
  case fvar.isFalse =>
    split
    · split <;> exact True.intro
    · exact True.intro
  case bvar.isFalse => split <;> exact True.intro
  case mdata.isFalse data inner hash ih absent =>
    refine ⟨?_, ih depth valid.2⟩
    intro present
    obtain ⟨contract, decoded, matched⟩ := valid.1 present
    exact ⟨contract, decoded, (fits_abstract _ _ _ _ _).trans matched⟩
  all_goals simp_all only [Frames, Expr.mkApp, Expr.mkLam, Expr.mkForallE,
    Expr.mkLetE, Expr.mkProj, Id.run, and_true]

def DomainsFrames (decls : Array LocalDecl) : Prop := ∀ d ∈ decls, Frames d.domain

theorem mkBinderChain_frames (body : Expr) (decls : Array LocalDecl) (kind : BinderKind)
    (hb : Frames body) (hd : DomainsFrames decls) : Frames (mkBinderChain body decls kind) := by
  unfold mkBinderChain
  simp only [Id.run, Ix.Cert.Canon.idBind]
  split
  · exact hb
  · rw [Loop.forIn_id_array _ (fun _ _ => rfl)]
    apply Array.foldl_induction (fun _ e => Frames e) (batchAbstractWith_frames _ _ _ _ hb)
    intro i acc held
    have member := Array.fst_mem_of_mem_zipIdx (Array.mem_reverse.mp (Array.getElem_mem i.isLt))
    cases kind <;> exact ⟨batchAbstractWith_frames _ _ _ _ (hd _ member), held⟩

theorem mkLambda_frames (body : Expr) (decls : Array LocalDecl) (hb : Frames body)
    (hd : DomainsFrames decls) : Frames (mkLambda body decls) :=
  mkBinderChain_frames body decls .lambda hb hd

theorem fresh_frames (supply : FreshFVars) (pfx : String) (index : Nat) :
    Frames (supply.fresh pfx index).1.2 := trivial

private theorem side_ok {α : Type} {value : Option α} {out : α} {cause : String}
    (run : O11aM.side value cause = .ok out) : value = some out := by
  cases value with
  | none => cases run
  | some value => cases Except.ok.inj run; rfl

private theorem lambda_fields {e : Expr} {name : Name} {domain body : Expr}
    {info : Lean.BinderInfo} {cause : String} (valid : Frames e)
    (run : O11aM.side (match e with | .lam n t b bi _ => some (n, t, b, bi) | _ => none) cause =
      .ok (name, domain, body, info)) : Frames domain ∧ Frames body := by
  have selected := side_ok run
  cases e with
  | lam n t b bi hash => cases Option.some.inj selected; exact valid
  | _ => cases selected

private theorem pushP {α : Type} {p : α → Prop} {xs : Array α} {x : α}
    (held : ∀ y ∈ xs, p y) (valid : p x) : ∀ y ∈ xs.push x, p y := by
  intro y member
  rcases Array.mem_push.mp member with old | rfl
  · exact held y old
  · exact valid

private theorem sizeOf_frames (target inst : Name) (level : Ix.Level) (field : Expr) (valid : Frames field) :
    Frames (Ix.Compile.Canon.mkAppN (Expr.mkConst nSizeOf #[level])
      #[Expr.mkConst target #[], Expr.mkConst inst #[], field]) :=
  ⟨⟨⟨trivial, trivial⟩, trivial⟩, valid⟩

private abbrev MinorState := FreshFVars × Expr × Array LocalDecl × Array Expr
private def Good (state : MinorState) : Prop :=
  Frames state.2.1 ∧ DomainsFrames state.2.2.1 ∧ ArgsFrames state.2.2.2

/-- The actual production helper's successful adapted term. The emitted
domains come from the selected user minor, not the classification prefix. -/
theorem sizeOfMinor_frames (env : OptEnv) (rv : Ix.RecursorVal) (inBlock : Array Bool)
    (us : Array Ix.Level) (ps ms mins : Array Expr) (j : Nat) {out : Expr}
    (held : ArgsFrames mins)
    (run : sizeOfMinorWith env (sizeOfInstanceE env) rv inBlock us ps ms mins j = .ok (some out)) :
    Frames out := by
  unfold sizeOfMinorWith at run
  dsimp only at run
  obtain ⟨⟨_, ctor⟩, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨minorTy, _, run⟩ := Loop.except_bind_ok.mp run
  dsimp only at run
  obtain ⟨⟨fieldDecls, _, _⟩, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨⟨supply, recFields⟩, _, run⟩ := Loop.except_bind_ok.mp run
  split at run
  · cases run
  · obtain ⟨minor, chosen, run⟩ := Loop.except_bind_ok.mp run
    have minorGood := held minor (Array.mem_of_getElem? (side_ok chosen))
    obtain ⟨result, walked, returned⟩ := Loop.except_bind_ok.mp run
    have good : Good result := by
      refine Ix.Cert.Claims.forIn_range_inv Good _ _ ?_ ?_ walked
      · intro i acc result prior step
        obtain ⟨⟨name, domain, body, info⟩, opened, rest⟩ := Loop.except_bind_ok.mp step
        have parts := lambda_fields prior.1 opened
        rcases fresh : acc.1.fresh "o11a" i with ⟨⟨fvName, fv⟩, nextSupply⟩
        have fvGood : Frames fv := by simpa only [fresh] using fresh_frames acc.1 "o11a" i
        simp only [fresh] at rest
        by_cases field : i < ctor.numFields
        · simp only [field, ↓reduceIte] at rest
          cases rest
          exact ⟨instantiate1_frames _ _ parts.2 fvGood, pushP prior.2.1 parts.1, pushP prior.2.2 fvGood⟩
        · simp only [field, ↓reduceIte] at rest
          rcases atField : recFields[i - ctor.numFields]! with ⟨fieldIdx, target⟩
          simp only [atField] at rest
          by_cases same : inBlock.getD target.sourcePos false = true
          · simp only [same, ↓reduceIte] at rest
            cases rest
            exact ⟨instantiate1_frames _ _ parts.2 fvGood, pushP prior.2.1 parts.1, prior.2.2⟩
          · simp only [same] at rest
            obtain ⟨targetName, _, rest⟩ := Loop.except_bind_ok.mp rest
            obtain ⟨_, _, rest⟩ := Loop.except_bind_ok.mp rest
            obtain ⟨_, _, rest⟩ := Loop.except_bind_ok.mp rest
            obtain ⟨⟨inst, level⟩, _, rest⟩ := Loop.except_bind_ok.mp rest
            obtain ⟨fieldValue, selected, returned⟩ := Loop.except_bind_ok.mp rest
            have fieldGood := prior.2.2 fieldValue (Array.mem_of_getElem? (side_ok selected))
            cases returned
            exact ⟨instantiate1_frames _ _ parts.2 (sizeOf_frames _ _ _ _ fieldGood), prior.2.1, prior.2.2⟩
      · exact ⟨minorGood, by simp [DomainsFrames], by simp [ArgsFrames]⟩
    cases Option.some.inj (Except.ok.inj returned)
    exact mkLambda_frames _ _ good.1 good.2.1

end Ix.CompileCert.O11aMinorFrames
