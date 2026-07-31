import Ix.Tc.Verify.Whnf.Beta.PrefixSemantics

/-!
# Dependent context chains for simultaneous beta

`simulSubstSpec` performs one structural pass, but its Theory meaning is a
sequence of dependent instantiations.  `KVLCtx.KInsts` records that sequence
without materializing any intermediate concrete term.  It composes under a
syntax binder and transports the abstract projection relation through every
Theory instantiation.
-/

namespace Lean4Lean.VLocalDecl

/-- Instantiate a declaration by outer-to-inner beta arguments. -/
def instBetaArgs (d : VLocalDecl) : List VExpr → (depth : Nat) → VLocalDecl
  | [], _ => d
  | arg :: args, depth =>
      instBetaArgs (d.inst arg (depth + args.length)) args depth

@[simp] theorem instBetaArgs_nil (d : VLocalDecl) (depth : Nat) :
    instBetaArgs d [] depth = d := rfl

/-- Instantiation changes declaration contents but not whether the declaration
contributes a Theory binder. -/
theorem instBetaArgs_depth (d : VLocalDecl) (args : List VExpr)
    (depth : Nat) :
    (instBetaArgs d args depth).depth = d.depth := by
  induction args generalizing d depth with
  | nil => rfl
  | cons arg args ih =>
      rw [instBetaArgs, ih]
      cases d <;> rfl

@[simp] theorem instBetaArgs_vlam (A : VExpr) (args : List VExpr)
    (depth : Nat) :
    instBetaArgs (.vlam A) args depth =
      .vlam (VExpr.instBetaArgs A args depth) := by
  induction args generalizing A depth with
  | nil => rfl
  | cons arg args ih =>
      rw [instBetaArgs, VLocalDecl.inst, VExpr.instBetaArgs, ih]

@[simp] theorem instBetaArgs_vlet (A value : VExpr) (args : List VExpr)
    (depth : Nat) :
    instBetaArgs (.vlet A value) args depth =
      .vlet (VExpr.instBetaArgs A args depth)
        (VExpr.instBetaArgs value args depth) := by
  induction args generalizing A value depth with
  | nil => rfl
  | cons arg args ih =>
      rw [instBetaArgs, VLocalDecl.inst, VExpr.instBetaArgs,
        VExpr.instBetaArgs, ih]

end Lean4Lean.VLocalDecl

namespace Ix.Tc

open Lean4Lean

namespace KVLCtx

/-- A sequence of dependent `KInstN` steps.  `arguments` are stored in
outer-to-inner order.  `dk`/`k` are the mixed-context and Theory depths below
the syntax-local declarations retained by the batch operation. -/
inductive KInsts (env : VEnv) (uvars : Nat) (base : KVLCtx) :
    List VExpr → Nat → Nat → KVLCtx → KVLCtx → Prop
  | nil (context : KVLCtx) (dk k : Nat) :
      KInsts env uvars base [] dk k context context
  | cons {arg : VExpr} {arguments : List VExpr} {A : VExpr}
      {dk k : Nat} {source middle target : KVLCtx} :
      KInstN base arg A (dk + arguments.length) (k + arguments.length)
        source middle →
      env.HasType uvars base.toCtx arg A →
      KInsts env uvars base arguments dk k middle target →
      KInsts env uvars base (arg :: arguments) dk k source target

namespace KInsts

/-- Retaining one syntax declaration above the substituted telescope extends
every constituent `KInstN` step and transforms that declaration pointwise. -/
theorem succ
    {env : VEnv} {uvars : Nat} {base : KVLCtx}
    {arguments : List VExpr} {dk k : Nat}
    {source target : KVLCtx}
    (h : KInsts env uvars base arguments dk k source target)
    (declaration : VLocalDecl) :
    KInsts env uvars base arguments (dk + 1) (k + declaration.depth)
      ((none, declaration) :: source)
      ((none, declaration.instBetaArgs arguments k) :: target) := by
  induction h generalizing declaration with
  | nil => exact .nil _ _ _
  | @cons arg arguments A dk k source middle target hstep harg htail ih =>
      let declaration' := declaration.inst arg (k + arguments.length)
      have hdepth : declaration'.depth = declaration.depth := by
        cases declaration <;> rfl
      have hstep' :
          KInstN base arg A
            ((dk + 1) + arguments.length)
            ((k + declaration.depth) + arguments.length)
            ((none, declaration) :: source)
            ((none, declaration') :: middle) := by
        have := KInstN.succ (d := declaration) hstep
        simpa [declaration', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using this
      have htail' := ih declaration'
      rw [hdepth] at htail'
      exact .cons hstep' harg (by
        simpa [VLocalDecl.instBetaArgs, declaration'] using htail')

private theorem appendAux
    {env : VEnv} {uvars : Nat} {base : KVLCtx}
    {left right : List VExpr}
    {dkLeft kLeft dk k : Nat} {source middle target : KVLCtx}
    (hleft : KInsts env uvars base left dkLeft kLeft source middle)
    (hdk : dkLeft = dk + right.length)
    (hk : kLeft = k + right.length)
    (hright : KInsts env uvars base right dk k middle target) :
    KInsts env uvars base (left ++ right) dk k source target := by
  induction hleft generalizing right dk k target with
  | nil => simpa using hright
  | @cons arg arguments A dkLeft kLeft source next middle hstep harg htail ih =>
      have hstep' :
          KInstN base arg A
            (dk + (arguments ++ right).length)
            (k + (arguments ++ right).length) source next := by
        rw [hdk, hk] at hstep
        simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hstep
      exact .cons hstep' harg (ih hdk hk hright)

/-- Concatenate two chains when the first runs above all binders consumed by
the second. -/
theorem append
    {env : VEnv} {uvars : Nat} {base : KVLCtx}
    {left right : List VExpr} {dk k : Nat}
    {source middle target : KVLCtx}
    (hleft : KInsts env uvars base left
      (dk + right.length) (k + right.length)
      source middle)
    (hright : KInsts env uvars base right dk k middle target) :
    KInsts env uvars base (left ++ right) dk k source target :=
  appendAux hleft rfl rfl hright

/-- Fvar lookups are transformed pointwise by the whole chain. -/
theorem find?_fvar
    {env : VEnv} {uvars : Nat} {base : KVLCtx}
    {arguments : List VExpr} {dk k : Nat}
    {source target : KVLCtx}
    (h : KInsts env uvars base arguments dk k source target)
    {fv : FVarId} {value type : VExpr}
    (hfind : source.find? (.inr fv) = some (value, type)) :
    target.find? (.inr fv) = some
      (VExpr.instBetaArgs value arguments k,
        VExpr.instBetaArgs type arguments k) := by
  induction h generalizing value type with
  | nil => simpa using hfind
  | @cons arg arguments A dk k source middle target hstep harg htail ih =>
      have hfirst := hstep.find?_fvar hfind
      simpa [VExpr.instBetaArgs] using ih hfirst

/-- Syntax-local bvars below the substituted telescope retain their concrete
index while their resolved Theory pair is instantiated pointwise. -/
theorem find?_below
    {env : VEnv} {uvars : Nat} {base : KVLCtx}
    {arguments : List VExpr} {dk k : Nat}
    {source target : KVLCtx}
    (h : KInsts env uvars base arguments dk k source target)
    {index : Nat} (hindex : index < dk) {value type : VExpr}
    (hfind : source.find? (.inl index) = some (value, type)) :
    target.find? (.inl index) = some
      (VExpr.instBetaArgs value arguments k,
        VExpr.instBetaArgs type arguments k) := by
  induction h generalizing value type with
  | nil => simpa using hfind
  | @cons arg arguments A dk k source middle target hstep harg htail ih =>
      have hfirst := hstep.find?_lt (j := index) (by omega) hfind
      simpa [VExpr.instBetaArgs] using ih hindex hfirst

/-- Bvars above the substituted telescope shift down by its length, with
their resolved Theory pair instantiated pointwise. -/
theorem find?_above
    {env : VEnv} {uvars : Nat} {base : KVLCtx}
    {arguments : List VExpr} {dk k : Nat}
    {source target : KVLCtx}
    (h : KInsts env uvars base arguments dk k source target)
    {index : Nat} (hindex : dk + arguments.length ≤ index)
    {value type : VExpr}
    (hfind : source.find? (.inl index) = some (value, type)) :
    target.find? (.inl (index - arguments.length)) = some
      (VExpr.instBetaArgs value arguments k,
        VExpr.instBetaArgs type arguments k) := by
  induction h generalizing index value type with
  | nil => simpa using hfind
  | @cons arg arguments A dk k source middle target hstep harg htail ih =>
      have habove : dk + arguments.length < index := by
        simpa only [List.length_cons] using hindex
      have hfirst := hstep.find?_gt habove hfind
      have hrest : dk + arguments.length ≤ index - 1 := by omega
      have hfinal := ih hrest hfirst
      have hshift : (index - 1) - arguments.length =
          index - (arg :: arguments).length := by
        simp only [List.length_cons]
        omega
      rw [← hshift]
      simpa [VExpr.instBetaArgs] using hfinal

/-- A lookup in the removed telescope is transformed to the corresponding
argument value, lifted only across the syntax-local Theory depth retained
below the batch operation. -/
theorem find?_window
    {env : VEnv} {uvars : Nat} {base : KVLCtx}
    {arguments : List VExpr} {dk k : Nat}
    {source target : KVLCtx}
    (h : KInsts env uvars base arguments dk k source target)
    {offset : Nat} (hoffset : offset < arguments.length)
    {value type : VExpr}
    (hfind : source.find? (.inl (dk + offset)) = some (value, type)) :
    ∃ argument,
      arguments.reverse[offset]? = some argument ∧
        VExpr.instBetaArgs value arguments k = argument.liftN k := by
  induction h generalizing offset value type with
  | nil => simp at hoffset
  | @cons outer arguments A dk k source middle target hstep harg htail ih =>
      by_cases hlast : offset = arguments.length
      · subst offset
        have hhit := hstep.find?_hit hfind
        refine ⟨outer, ?_, ?_⟩
        · simp
        · rw [VExpr.instBetaArgs, hhit]
          exact VExpr.instBetaArgs_liftN outer arguments k
      · have hinner : offset < arguments.length := by
          simp only [List.length_cons] at hoffset
          omega
        have hfirst := hstep.find?_lt (j := dk + offset) (by omega) hfind
        obtain ⟨argument, hget, hmeaning⟩ := ih hinner hfirst
        refine ⟨argument, ?_, ?_⟩
        · rw [List.reverse_cons, List.getElem?_append_left]
          · exact hget
          · simpa using hinner
        · simpa [VExpr.instBetaArgs] using hmeaning

/-- Typing derivations instantiate pointwise through the complete chain. -/
theorem hasType
    {env : VEnv} {uvars : Nat} {base : KVLCtx}
    {arguments : List VExpr} {dk k : Nat} {source target : KVLCtx}
    (h : KInsts env uvars base arguments dk k source target)
    (henv : env.Ordered) {value type : VExpr}
    (htype : env.HasType uvars source.toCtx value type) :
    env.HasType uvars target.toCtx
      (VExpr.instBetaArgs value arguments k)
      (VExpr.instBetaArgs type arguments k) := by
  induction h generalizing value type with
  | nil => exact htype
  | @cons arg arguments A dk k source middle target hstep harg htail ih =>
      have hfirst := htype.instN henv hstep.toCtx harg
      simpa [VExpr.instBetaArgs] using ih hfirst

/-- Typehood is stable through the chain. -/
theorem isType
    {env : VEnv} {uvars : Nat} {base : KVLCtx}
    {arguments : List VExpr} {dk k : Nat} {source target : KVLCtx}
    (h : KInsts env uvars base arguments dk k source target)
    (henv : env.Ordered) {type : VExpr}
    (htype : env.IsType uvars source.toCtx type) :
    env.IsType uvars target.toCtx
      (VExpr.instBetaArgs type arguments k) := by
  obtain ⟨level, hlevel⟩ := htype
  exact ⟨level, by simpa [VExpr.instBetaArgs] using h.hasType henv hlevel⟩

/-- The abstract projection relation is stable through the whole dependent
instantiation chain. -/
theorem projection
    {env : VEnv} {uvars : Nat} {base : KVLCtx}
    {arguments : List VExpr} {dk k : Nat}
    {source target : KVLCtx}
    (h : KInsts env uvars base arguments dk k source target)
    {trProj : RawProjRel}
    (htpI : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {position : Nat}
      {Γ₁ Γ : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
      Lean4Lean.Ctx.InstN Γ₀ e₀ A₀ position Γ₁ Γ →
      trProj Γ₁ s i e e' →
      trProj Γ s i (e.inst e₀ position) (e'.inst e₀ position))
    {structName : Lean.Name} {field : Nat} {value result : VExpr}
    (hproj : trProj source.toCtx structName field value result) :
    trProj target.toCtx structName field
      (VExpr.instBetaArgs value arguments k)
      (VExpr.instBetaArgs result arguments k) := by
  induction h generalizing value result with
  | nil => exact hproj
  | @cons arg arguments A dk k source middle target hstep harg htail ih =>
      have hfirst := htpI hstep.toCtx hproj
      simpa [VExpr.instBetaArgs] using ih hfirst

end KInsts
end KVLCtx
end Ix.Tc
