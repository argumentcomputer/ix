import Ix.Tc.Verify.Inductive.SingletonRecursor

/-!
# Applying closed generated equations

Lean4Lean registers generated iota equations as closed lambda telescopes,
whereas the production Ix reducer sees the recursor application after that
telescope has been supplied.  These lemmas isolate the ordinary dependent
beta reasoning needed to cross that boundary.

Nothing in this module assumes an iota pattern is sound.  In particular,
`VEnv.Params.extra_pat` is not used: its current interface attempts to match
the still-closed left-hand side and therefore cannot justify the generated
lambda-wrapped equations.  The later singleton pattern compiler must provide
the exact telescope arguments and use the lemmas below.
-/

namespace Lean4Lean.VExpr

/-- Positional lookup in the reverse de Bruijn range used by generated rule
telescopes. -/
theorem bvarRevRange_getElem? (off arity index : Nat)
    (hindex : index < arity) :
    (VExpr.bvarRevRange off arity)[index]? =
      some (.bvar (off + (arity - 1 - index))) := by
  induction arity generalizing index with
  | zero => omega
  | succ arity ih =>
      cases index with
      | zero => simp [VExpr.bvarRevRange]
      | succ index =>
          simp only [VExpr.bvarRevRange, List.getElem?_cons_succ]
          rw [ih index (by omega)]
          congr 2
          omega

/-- Instantiating the reverse de Bruijn range consumes the argument spine in
its original left-to-right order. -/
theorem instRev_bvar_at (arguments : List VExpr) (index : Nat)
    (hindex : index < arguments.length) :
    VExpr.instRev
        (.bvar (arguments.length - 1 - index)) arguments =
      arguments[index] := by
  have hrange := congrArg (fun values => values[index]?)
    (VExpr.map_instRev_bvarRevRange arguments)
  change ((VExpr.bvarRevRange 0 arguments.length).map
      (VExpr.instRev · arguments))[index]? = arguments[index]? at hrange
  rw [List.getElem?_map,
    bvarRevRange_getElem? 0 arguments.length index hindex] at hrange
  simp only [Nat.zero_add, Option.map_some] at hrange
  rw [List.getElem?_eq_getElem hindex] at hrange
  exact Option.some.inj hrange

end Lean4Lean.VExpr

namespace Lean4Lean.VEnv

/-- Typing an application spine also types its original head.  This is a
small inversion helper for the equation-application proofs below. -/
theorem HasType.appN_head
    {env : VEnv} {U : Nat} {Gamma : List VExpr}
    (henv : env.WF) (hGamma : OnCtx Gamma (env.IsType U))
    {f : VExpr} {args : List VExpr} {A : VExpr}
    (h : env.HasType U Gamma (VExpr.appN f args) A) :
    ∃ B, env.HasType U Gamma f B := by
  induction args generalizing f A with
  | nil => exact ⟨A, h⟩
  | cons arg args ih =>
      obtain ⟨B, hhead⟩ := ih h
      obtain ⟨domain, codomain, hfun, _⟩ :=
        hhead.app_inv henv.ordered hGamma
      exact ⟨_, hfun⟩

/-- Typing a complete application spine also types every left prefix.  This
is the form needed by indexed iota rules: the recursor prefix provides the
common parameter/motive/minor arguments, while its final index and major are
handled separately. -/
theorem HasType.appN_prefix
    {env : VEnv} {U : Nat} {Gamma : List VExpr}
    (henv : env.WF) (hGamma : OnCtx Gamma (env.IsType U))
    {f : VExpr} {prefixArgs suffixArgs : List VExpr} {A : VExpr}
    (h : env.HasType U Gamma
      (VExpr.appN f (prefixArgs ++ suffixArgs)) A) :
    ∃ B, env.HasType U Gamma (VExpr.appN f prefixArgs) B := by
  rw [VExpr.appN_append] at h
  exact HasType.appN_head henv hGamma h

/-- Recover an application's argument at the domain exposed by a separately
known exact type for its head.  Application inversion alone returns an
existential domain; uniqueness and Π-injectivity align it with the certified
head type. -/
theorem HasType.app_argument_of_head
    {env : VEnv} {U : Nat} {Gamma : List VExpr}
    (henv : env.WF) (hGamma : OnCtx Gamma (env.IsType U))
    {f argument domain body result : VExpr}
    (happlication : env.HasType U Gamma (.app f argument) result)
    (hhead : env.HasType U Gamma f (.forallE domain body)) :
    env.HasType U Gamma argument domain := by
  obtain ⟨actualDomain, actualBody, hactualHead, hactualArgument⟩ :=
    happlication.app_inv henv.ordered hGamma
  have htypes : env.IsDefEqU U Gamma
      (.forallE actualDomain actualBody) (.forallE domain body) :=
    hactualHead.uniqU henv hGamma hhead
  obtain ⟨sortLevel, hdomain⟩ :=
    (htypes.forallE_inv henv hGamma).1
  exact hactualArgument.defeqU_r henv hGamma ⟨.sort sortLevel, hdomain⟩

/-- If two heads expose the same dependent binder telescope, any complete
argument spine which types the first head also types the second.  Their result
bodies may differ.  This is the typed congruence needed to apply a generated
iota equation: the recursor and the equation lambda share motive/minor
binders, but only the recursor retains the final major binder. -/
theorem HasType.transfer_appN_telescope
    {env : VEnv} {U : Nat} {Gamma : List VExpr}
    (henv : env.WF) (hGamma : OnCtx Gamma (env.IsType U))
    {binders : List VExpr} {leftBody rightBody : VExpr}
    {left right : VExpr} {arguments : List VExpr} {A : VExpr}
    (hlength : arguments.length = binders.length)
    (hsource : env.HasType U Gamma (VExpr.appN left arguments) A)
    (hleft : env.HasType U Gamma left
      (VExpr.forallN binders leftBody))
    (hright : env.HasType U Gamma right
      (VExpr.forallN binders rightBody)) :
    ∃ B, env.HasType U Gamma (VExpr.appN right arguments) B := by
  induction arguments generalizing binders left right leftBody rightBody A with
  | nil =>
      cases binders with
      | nil => exact ⟨rightBody, hright⟩
      | cons binder binders => simp at hlength
  | cons argument arguments ih =>
      cases binders with
      | nil => simp at hlength
      | cons binder binders =>
          have hrestLength : arguments.length = binders.length := by
            simpa using hlength
          have hsource' : env.HasType U Gamma
              (VExpr.appN (.app left argument) arguments) A := hsource
          obtain ⟨prefixType, hprefix⟩ :=
            HasType.appN_head henv hGamma hsource'
          obtain ⟨actualDomain, actualBody, hleftActual, hargument⟩ :=
            hprefix.app_inv henv.ordered hGamma
          have hleft' : env.HasType U Gamma left
              (.forallE binder (VExpr.forallN binders leftBody)) := by
            simpa only [VExpr.forallN] using hleft
          have htypes : env.IsDefEqU U Gamma
              (.forallE actualDomain actualBody)
              (.forallE binder (VExpr.forallN binders leftBody)) :=
            hleftActual.uniqU henv hGamma hleft'
          obtain ⟨sortLevel, hdomain⟩ :=
            (htypes.forallE_inv henv hGamma).1
          have hargument' : env.HasType U Gamma argument binder :=
            hargument.defeqU_r henv hGamma ⟨.sort sortLevel, hdomain⟩
          have hleftApp : env.HasType U Gamma (.app left argument)
              ((VExpr.forallN binders leftBody).inst argument) :=
            .app hleft' hargument'
          have hright' : env.HasType U Gamma right
              (.forallE binder (VExpr.forallN binders rightBody)) := by
            simpa only [VExpr.forallN] using hright
          have hrightApp : env.HasType U Gamma (.app right argument)
              ((VExpr.forallN binders rightBody).inst argument) :=
            .app hright' hargument'
          rw [VExpr.instN_forallN] at hleftApp hrightApp
          have hleftApp' : env.HasType U Gamma (.app left argument)
              (VExpr.forallN (VExpr.instTelN argument binders 0)
                (leftBody.inst argument binders.length)) := by
            simpa only [Nat.zero_add] using hleftApp
          have hrightApp' : env.HasType U Gamma (.app right argument)
              (VExpr.forallN (VExpr.instTelN argument binders 0)
                (rightBody.inst argument binders.length)) := by
            simpa only [Nat.zero_add] using hrightApp
          have htransLength : arguments.length =
              (VExpr.instTelN argument binders 0).length := by
            simpa [VExpr.instTelN_length] using hrestLength
          exact ih
            (binders := VExpr.instTelN argument binders 0)
            (leftBody := leftBody.inst argument binders.length)
            (rightBody := rightBody.inst argument binders.length)
            htransLength hsource hleftApp' hrightApp'

/-- Exact-result variant of `transfer_appN_telescope`.  Applying every
binder of a telescope produces `instRev` of its body; retaining that result
is essential when a generated rule has constructor fields after the common
recursor prefix. -/
theorem HasType.transfer_appN_telescope_instRev
    {env : VEnv} {U : Nat} {Gamma : List VExpr}
    (henv : env.WF) (hGamma : OnCtx Gamma (env.IsType U))
    {binders : List VExpr} {leftBody rightBody : VExpr}
    {left right : VExpr} {arguments : List VExpr} {A : VExpr}
    (hlength : arguments.length = binders.length)
    (hsource : env.HasType U Gamma (VExpr.appN left arguments) A)
    (hleft : env.HasType U Gamma left
      (VExpr.forallN binders leftBody))
    (hright : env.HasType U Gamma right
      (VExpr.forallN binders rightBody)) :
    env.HasType U Gamma (VExpr.appN right arguments)
      (VExpr.instRev rightBody arguments) := by
  induction arguments generalizing binders left right leftBody rightBody A with
  | nil =>
      cases binders with
      | nil => exact hright
      | cons binder binders => simp at hlength
  | cons argument arguments ih =>
      cases binders with
      | nil => simp at hlength
      | cons binder binders =>
          have hrestLength : arguments.length = binders.length := by
            simpa using hlength
          have hsource' : env.HasType U Gamma
              (VExpr.appN (.app left argument) arguments) A := hsource
          obtain ⟨prefixType, hprefix⟩ :=
            HasType.appN_head henv hGamma hsource'
          obtain ⟨actualDomain, actualBody, hleftActual, hargument⟩ :=
            hprefix.app_inv henv.ordered hGamma
          have hleft' : env.HasType U Gamma left
              (.forallE binder (VExpr.forallN binders leftBody)) := by
            simpa only [VExpr.forallN] using hleft
          have htypes : env.IsDefEqU U Gamma
              (.forallE actualDomain actualBody)
              (.forallE binder (VExpr.forallN binders leftBody)) :=
            hleftActual.uniqU henv hGamma hleft'
          obtain ⟨sortLevel, hdomain⟩ :=
            (htypes.forallE_inv henv hGamma).1
          have hargument' : env.HasType U Gamma argument binder :=
            hargument.defeqU_r henv hGamma ⟨.sort sortLevel, hdomain⟩
          have hleftApp : env.HasType U Gamma (.app left argument)
              ((VExpr.forallN binders leftBody).inst argument) :=
            .app hleft' hargument'
          have hright' : env.HasType U Gamma right
              (.forallE binder (VExpr.forallN binders rightBody)) := by
            simpa only [VExpr.forallN] using hright
          have hrightApp : env.HasType U Gamma (.app right argument)
              ((VExpr.forallN binders rightBody).inst argument) :=
            .app hright' hargument'
          rw [VExpr.instN_forallN] at hleftApp hrightApp
          have hleftApp' : env.HasType U Gamma (.app left argument)
              (VExpr.forallN (VExpr.instTelN argument binders 0)
                (leftBody.inst argument binders.length)) := by
            simpa only [Nat.zero_add] using hleftApp
          have hrightApp' : env.HasType U Gamma (.app right argument)
              (VExpr.forallN (VExpr.instTelN argument binders 0)
                (rightBody.inst argument binders.length)) := by
            simpa only [Nat.zero_add] using hrightApp
          have htransLength : arguments.length =
              (VExpr.instTelN argument binders 0).length := by
            simpa [VExpr.instTelN_length] using hrestLength
          have hresult := ih
            (binders := VExpr.instTelN argument binders 0)
            (leftBody := leftBody.inst argument binders.length)
            (rightBody := rightBody.inst argument binders.length)
            htransLength hsource hleftApp' hrightApp'
          simpa only [VExpr.appN, VExpr.instRev, hrestLength] using hresult

/-- A typed equality remains valid after applying the same typed spine to
both sides.  The final left-hand typing is enough: application inversion and
unique typing recover each dependent argument type. -/
theorem IsDefEq.appN_same
    {env : VEnv} {U : Nat} {Gamma : List VExpr}
    (henv : env.WF) (hGamma : OnCtx Gamma (env.IsType U))
    {f g T : VExpr} (hfg : env.IsDefEq U Gamma f g T)
    {args : List VExpr} {A : VExpr}
    (hsource : env.HasType U Gamma (VExpr.appN f args) A) :
    env.IsDefEqU U Gamma (VExpr.appN f args) (VExpr.appN g args) := by
  induction args generalizing f g T A with
  | nil => exact ⟨T, hfg⟩
  | cons arg rest ih =>
      have hsource' : env.HasType U Gamma
          (VExpr.appN (.app f arg) rest) A := hsource
      obtain ⟨headType, hhead⟩ :=
        HasType.appN_head henv hGamma hsource'
      obtain ⟨domain, codomain, hfun, harg⟩ :=
        hhead.app_inv henv.ordered hGamma
      have hfg' : env.IsDefEq U Gamma f g (.forallE domain codomain) :=
        (show env.IsDefEqU U Gamma f g from ⟨T, hfg⟩).of_l
          henv hGamma hfun
      exact ih (.appDF hfg' harg) hsource

/-- Contract the first beta redex beneath an arbitrary remaining application
spine.  This is deliberately proved from the Theory beta rule and typing
inversion, not from a syntactic rewrite relation. -/
theorem HasType.beta_head_appN
    {env : VEnv} {U : Nat} {Gamma : List VExpr}
    (henv : env.WF) (hGamma : OnCtx Gamma (env.IsType U))
    {domain body arg : VExpr} {rest : List VExpr} {A : VExpr}
    (hsource : env.HasType U Gamma
      (VExpr.appN (.app (.lam domain body) arg) rest) A) :
    env.IsDefEqU U Gamma
      (VExpr.appN (.app (.lam domain body) arg) rest)
      (VExpr.appN (body.inst arg) rest) := by
  obtain ⟨prefixType, hprefix⟩ :=
    HasType.appN_head henv hGamma hsource
  obtain ⟨actualDomain, actualBody, hlam, harg⟩ :=
    hprefix.app_inv henv.ordered hGamma
  obtain ⟨⟨sortLevel, hdomain⟩, bodyType, hbody⟩ :=
    hlam.lam_inv henv.ordered hGamma
  have hcanonical : env.HasType U Gamma (.lam domain body)
      (.forallE domain bodyType) := .lam hdomain hbody
  have hforallEq : env.IsDefEqU U Gamma
      (.forallE actualDomain actualBody) (.forallE domain bodyType) :=
    hlam.uniqU henv hGamma hcanonical
  have hdomainEq : env.IsDefEqU U Gamma actualDomain domain :=
    let ⟨level, h⟩ :=
      (hforallEq.forallE_inv henv hGamma).1
    ⟨.sort level, h⟩
  have harg' : env.HasType U Gamma arg domain :=
    harg.defeqU_r henv hGamma hdomainEq
  have hbeta : env.IsDefEq U Gamma
      (.app (.lam domain body) arg) (body.inst arg)
      (bodyType.inst arg) := .beta hbody harg'
  exact IsDefEq.appN_same henv hGamma hbeta hsource

/-- Supplying exactly one argument per closed lambda binder beta-reduces to
Lean4Lean's outer-to-inner `instRev` operation.  This is the reusable semantic
bridge from a registered closed equation to an open generated rule body. -/
theorem HasType.lamN_appN_beta
    {env : VEnv} {U : Nat} {Gamma : List VExpr}
    (henv : env.WF) (hGamma : OnCtx Gamma (env.IsType U))
    {binders : List VExpr} {body : VExpr} {args : List VExpr} {A : VExpr}
    (hlength : args.length = binders.length)
    (hsource : env.HasType U Gamma
      (VExpr.appN (VExpr.lamN binders body) args) A) :
    env.IsDefEqU U Gamma
      (VExpr.appN (VExpr.lamN binders body) args)
      (VExpr.instRev body args) := by
  induction args generalizing binders body A with
  | nil =>
      cases binders with
      | nil => exact ⟨A, hsource⟩
      | cons binder binders => simp at hlength
  | cons arg args ih =>
      cases binders with
      | nil => simp at hlength
      | cons binder binders =>
          have hrestLength : args.length = binders.length := by
            simpa using hlength
          have hfirst : env.IsDefEqU U Gamma
              (VExpr.appN
                (.app (.lam binder (VExpr.lamN binders body)) arg) args)
              (VExpr.appN
                ((VExpr.lamN binders body).inst arg) args) :=
            HasType.beta_head_appN henv hGamma hsource
          have hintermediate : env.HasType U Gamma
              (VExpr.appN ((VExpr.lamN binders body).inst arg) args) A :=
            (hfirst.of_l henv hGamma hsource).hasType.2
          rw [VExpr.instN_lamN] at hintermediate hfirst
          have htransLength : args.length =
              (VExpr.instTelN arg binders 0).length := by
            simpa [VExpr.instTelN_length] using hrestLength
          have hrest := ih
            (binders := VExpr.instTelN arg binders 0)
            (body := body.inst arg binders.length)
            htransLength (by simpa using hintermediate)
          have hrest' : env.IsDefEqU U Gamma
              (VExpr.appN
                (VExpr.lamN (VExpr.instTelN arg binders 0)
                  (body.inst arg (0 + binders.length))) args)
              (VExpr.instRev
                (body.inst arg (0 + binders.length)) args) := by
            simpa only [Nat.zero_add] using hrest
          have hcombined := hfirst.trans henv hGamma hrest'
          simpa only [VExpr.lamN, VExpr.appN, VExpr.instRev,
            Nat.zero_add, hrestLength] using hcombined

end Lean4Lean.VEnv
