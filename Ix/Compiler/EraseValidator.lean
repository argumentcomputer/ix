import Ix.Compiler.Sim

/-!
# Proof-producing executable-erasure validator

`Erase.eraseExpr` intentionally accepts more syntax than the core fragment
covered directly by `Sim.PErase`: general dropped-variable reads still need
their simulation machinery. Unfoldable definition projections and non-self
inductive members are checked structurally. Non-self unfoldable-definition and
recursor heads are admitted through a finite `MemberScope`; after public
coverage succeeds, `validateMemberCoverage` checks every named body/rule set
against that same plan, closing cyclic blocks without recursive validator
calls. Configured opaque mutual projections and members are admitted only when
the source extern arity and target declaration agree at the exact synthetic
member address; semantic oracle agreement remains a theorem premise.
Constructor parameter prefixes are certified by `CtorParamSpine`; partial and
split prefixes use ignored target wrappers, while complete visible prefixes
expose the field-arity constructor. Indexed recursor spines use
`RecEraseSpine`; a spine that stops in its source-only index suffix is
certified by structurally reconstructing the let-captured ignored continuation
(`PErase.recW`), including after escape through a variable or let. Rule-local
indexed `recur` heads use the environment's already-certified self member, so
rule validation does not recurse through its own member oracle.
Ordinary unfoldable definition heads use `DefSpine`: declaration-type policy
must agree with the literal implementation binder before a ghost argument is
certified. Definition coverage also reconstructs the fuel-free
`TeleResultOwned` relation, so the emitted declaration's ownership cannot
drift from the source telescope. Configured quotient coverage checks the
address/kind identity, exact compiler-generated lambda body, and the same
result-ownership relation. Opaque definitions and axioms are certified only
when the source evaluator is configured at the compiler-emitted extern arity;
their semantic oracle correspondence remains an explicit theorem premise. Raw
`.share` syntax also stays out of `PErase`, but the
`certifyShared*` entry points validate the real eraser output against the
semantically inlined source. This module provides the roadmap-approved
bridge between the executable pass and the theorem: run the real eraser,
check its exact output against the relation, and return the `PErase` proof
as part of the result.

The validator is deliberately partial in the proof sense, not in Lean's
termination sense.  It rejects an executable erasure that lies outside the
current simulation fragment.  A successful result cannot drift from the
compiler output: `CertifiedExpr.erased` records the actual `eraseExpr`
equation and `CertifiedExpr.related` records the kernel-checked relational
witness for that same target expression. `CertifiedSharedExpr` adds the
inlining/evaluator-coherence bridge while retaining the original erasure
equation.
-/

namespace Ix.Compiler.EraseValidator

open Ix.Compiler.Ixon (Address Constant MutConst Owned Recursor RecursorRule Uses)
open Ix.Compiler.Sim

/-- Use exactly the evaluator's resolver, blob store, and Nat identity when
running the executable eraser for a simulation certificate. Quotient identity
is not an eraser input: it remains on `ectx` and is checked by
`validateCovered` before a quotient reference receives a certificate.

Parameterized constructor heads use the same ignored-wrapper lowering as the
executable eraser. The validator reconstructs that wrapper structurally; no
configuration switch separates raw and certified erasure. -/
def eraseCtxOf (ectx : Ixon.Eval.EvalCtx) : Erase.EraseCtx :=
  { resolve := ectx.resolve, blobs := ectx.blobs, natBlock := ectx.natBlock }

/-- Eraser tables corresponding to semantic full inlining.  Reference and
rule-state metadata are unchanged; source roots in mutual members are inlined
against the same table as the enclosing expression, and the table is cleared. -/
def inlineTables (T : Erase.ETables) : Erase.ETables :=
  { sharing := #[]
    refs := T.refs
    selfMuts := T.selfMuts.map
      (MutConst.mapExprs (Ixon.Sharing.inlineExpr T.sharing))
    curBlock := T.curBlock
    recSelf := T.recSelf }

/-- The eraser-table view of an evaluator frame for a closed expression.
`recSelf` is absent outside an individual recursor-rule certificate. -/
def tablesOfFrame (F : Ixon.Eval.Frame) : Erase.ETables :=
  { sharing := F.sharing
    refs := F.refs
    selfMuts := F.selfMuts
    curBlock := F.selfAddr }

/-- Normalizing eraser tables built from a frame is exactly the eraser-table
view of the normalized evaluator frame. -/
@[simp] theorem inlineTables_tablesOfFrame (F : Ixon.Eval.Frame) :
    inlineTables (tablesOfFrame F) = tablesOfFrame F.inlineSharing := by
  rfl

@[simp] theorem inlineTables_refs (T : Erase.ETables) :
    (inlineTables T).refs = T.refs := rfl

@[simp] theorem inlineTables_curBlock (T : Erase.ETables) :
    (inlineTables T).curBlock = T.curBlock := rfl

@[simp] theorem inlineTables_recSelf (T : Erase.ETables) :
    (inlineTables T).recSelf = T.recSelf := rfl

section MemberScoped

variable [scope : MemberScope]

/-- Program-level facts are supplied independently of expression checking.
This is the usual CompCert split: environment validation establishes
`Covered`; expression validation consumes those facts at references. -/
abbrev CoverOracle (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx) :=
  (a : Address) → Option (PLift (Covered ectx ictx a))

/-- Indexed recursor spines cannot use `Covered`, because their bare target
head has fewer visible arguments than the source head.  An entry-expression
certificate instead supplies the already checked member fact directly. -/
abbrev RecMemberOracle (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx) :=
  (block : Address) → (idx : Nat) → (bc : Constant) → (r : Recursor) →
    Ixon.Eval.resolveMut ectx block idx = .ok (bc, .recr r) →
    Option (PLift (RecMember ectx ictx block idx r))

/-- The index-free default used by the existing public validator API. -/
def noRecMembers {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx} :
    RecMemberOracle ectx ictx :=
  fun _ _ _ _ _ => none

/-- A proof that `e` is an index-free recursor prefix, when it can be
reconstructed directly from the current source frame. -/
def recPrefix? (ectx : Ixon.Eval.EvalCtx) (refs : Array Address)
    (muts : Array MutConst) (sa : Option Address) (e : Ixon.Expr) :
    Option (Σ r : Recursor, PLift (RecPrefix ectx refs muts sa e r)) :=
  match e with
  | .ref refIdx _ =>
    match href : refs[refIdx.toNat]? with
    | some a =>
      match hc : ectx.resolve a with
      | some c =>
        match hi : c.info with
        | .rPrj p =>
          match hm : Ixon.Eval.resolveMut ectx p.block p.idx.toNat with
          | .ok (_bc, .recr r) =>
            if hx : r.indices.toNat = 0 then
              some ⟨r, ⟨.refH href hc hi hm hx⟩⟩
            else none
          | _ => none
        | _ => none
      | none => none
    | none => none
  | .recur recIdx _ =>
    match sa with
    | some _block =>
      match hm : muts[recIdx.toNat]? with
      | some (.recr r) =>
        if hx : r.indices.toNat = 0 then
          some ⟨r, ⟨.recurH rfl hm hx⟩⟩
        else none
      | _ => none
    | none => none
  | _ => none

/-- Reconstruct a guarded recursor spine and its number of supplied
pre-major arguments. The step constructor prevents walking past the
parameter/motive/minor policy. -/
def recSpine? (ectx : Ixon.Eval.EvalCtx) (refs : Array Address)
    (muts : Array MutConst) (sa : Option Address) :
    Nat → (e : Ixon.Expr) →
      Option (Σ r : Recursor, Σ j : Nat,
        PLift (RecSpine ectx refs muts sa e r j))
  | 0, _ => none
  | fuel + 1, e =>
    match recPrefix? ectx refs muts sa e with
    | some ⟨r, h⟩ => some ⟨r, 0, ⟨.head h.down⟩⟩
    | none =>
      match e with
      | .app f _ =>
        match recSpine? ectx refs muts sa fuel f with
        | some ⟨r, j, h⟩ =>
          if hj : j < (recRulePolicy r).length then
            some ⟨r, j + 1, ⟨.step h.down hj⟩⟩
          else none
        | none => none
      | _ => none

/-- Dependent package returned while following an unfoldable ordinary
definition through its literal implementation telescope. -/
structure DefSpineCert (ectx : Ixon.Eval.EvalCtx)
    (refs : Array Address) (e : Ixon.Expr) where
  residual : Ixon.Expr
  spine : DefSpine ectx refs e residual

/-- Reconstruct the implementation-side definition spine used to justify a
ghost application.  Declaration-type policy drives executable erasure; this
second check ensures the lambda actually reached at run time drops the same
argument. -/
def defSpine? (ectx : Ixon.Eval.EvalCtx) (refs : Array Address) :
    Nat → (e : Ixon.Expr) → Option (DefSpineCert ectx refs e)
  | 0, _ => none
  | fuel + 1, e =>
    match e with
    | .ref refIdx univIdxs =>
      match hr : refs[refIdx.toNat]? with
      | some address =>
        match hc : ectx.resolve address with
        | some constant =>
          match hi : constant.info with
          | .defn definition =>
            match hu : Ixon.Eval.unfoldable definition with
            | true => some
                { residual := definition.value
                  spine := .head hr hc hi hu }
            | false => none
          | _ => none
        | none => none
      | none => none
    | .app function argument =>
      match defSpine? ectx refs fuel function with
      | some cert =>
        match hr : cert.residual with
        | .lam uses domain body => by
            have hspine := cert.spine
            rw [hr] at hspine
            exact some
              { residual := body
                spine := .step hspine }
        | _ => none
      | none => none
    | _ => none

/-- Dependent package returned while reconstructing a syntactically visible
constructor parameter spine. -/
structure CtorParamSpineCert (ectx : Ixon.Eval.EvalCtx)
    (refs : Array Address) (e : Ixon.Expr) where
  address : Address
  block : Address
  indIdx : Nat
  cidx : Nat
  params : Nat
  fields : Nat
  consumed : Nat
  spine : CtorParamSpine ectx refs e address block indIdx cidx params fields
    consumed

/-- Reconstruct a constructor head and the dropped-parameter prefix consumed
so far.  Walking stops before the first runtime field. -/
def ctorParamSpine? (ectx : Ixon.Eval.EvalCtx) (refs : Array Address) :
    Nat → (e : Ixon.Expr) → Option (CtorParamSpineCert ectx refs e)
  | 0, _ => none
  | fuel + 1, e =>
    match e with
    | .ref refIdx _univIdxs =>
      match hr : refs[refIdx.toNat]? with
      | some a =>
        match hc : ectx.resolve a with
        | some c =>
          match hi : c.info with
          | .cPrj p =>
            match hm : Ixon.Eval.resolveMut ectx p.block p.idx.toNat with
            | .ok (bc, .indc ind) =>
              match ht : ind.ctors[p.cidx.toNat]? with
              | some ct =>
                if hp : ind.params.toNat = ct.params.toNat then
                  some
                    { address := a
                      block := p.block
                      indIdx := p.idx.toNat
                      cidx := p.cidx.toNat
                      params := ct.params.toNat
                      fields := ct.fields.toNat
                      consumed := 0
                      spine := .head hr hc hi
                        ⟨bc, ind, ct, hm, ht, hp, rfl, rfl⟩ }
                else none
              | none => none
            | _ => none
          | _ => none
        | none => none
      | none => none
    | .app f _arg =>
      match ctorParamSpine? ectx refs fuel f with
      | some cert =>
        if hj : cert.consumed < cert.params then
          some
            { address := cert.address
              block := cert.block
              indIdx := cert.indIdx
              cidx := cert.cidx
              params := cert.params
              fields := cert.fields
              consumed := cert.consumed + 1
              spine := .step cert.spine hj }
        else none
      | none => none
    | _ => none

private def fail {P : Prop} (msg : String) : Except String (PLift P) :=
  .error msg

/-- Construct the fuel-free result-ownership relation.  Fuel controls only
checker termination: exhaustion rejects instead of manufacturing the shared
default, so a successful certificate is independent of the chosen bound. -/
def validateTeleResultOwned (sharing : Array Ixon.Expr) :
    Nat → (typ : Ixon.Expr) →
      Except String (Σ candidate : Option Owned,
        PLift (TeleResultOwned sharing typ candidate))
  | 0, _ => .error "result-ownership validation fuel exhausted"
  | fuel + 1, typ =>
    match typ with
    | .all _uses result _domain codomain => do
      let cert ← validateTeleResultOwned sharing fuel codomain
      match cert with
      | ⟨none, proof⟩ =>
        pure ⟨some result, ⟨.allHere proof.down⟩⟩
      | ⟨some inner, proof⟩ =>
        pure ⟨some inner, ⟨.allInner proof.down⟩⟩
    | .share index =>
      match hlookup : sharing[index.toNat]? with
      | none => .ok ⟨none, ⟨.shareMissing hlookup⟩⟩
      | some target => do
        let cert ← validateTeleResultOwned sharing fuel target
        pure ⟨cert.1, ⟨.share hlookup cert.2.down⟩⟩
    | .sort _ => .ok ⟨none, ⟨.terminal rfl⟩⟩
    | .var _ => .ok ⟨none, ⟨.terminal rfl⟩⟩
    | .ref _ _ => .ok ⟨none, ⟨.terminal rfl⟩⟩
    | .recur _ _ => .ok ⟨none, ⟨.terminal rfl⟩⟩
    | .prj _ _ _ => .ok ⟨none, ⟨.terminal rfl⟩⟩
    | .str _ => .ok ⟨none, ⟨.terminal rfl⟩⟩
    | .nat _ => .ok ⟨none, ⟨.terminal rfl⟩⟩
    | .app _ _ => .ok ⟨none, ⟨.terminal rfl⟩⟩
    | .lam _ _ _ => .ok ⟨none, ⟨.terminal rfl⟩⟩
    | .letE _ _ _ _ => .ok ⟨none, ⟨.terminal rfl⟩⟩

/-- Recognize the four closed quotient definitions emitted by the eraser.
Keeping this structural avoids assuming a global decidable-equality law for
IxIR₀ expressions merely to validate these fixed compiler-generated bodies. -/
private def validateQuotientBody (kind : Ixon.QuotKind)
    (body : IxIR0.Expr) :
    Except String (PLift (body = Erase.quotientBody kind)) :=
  match kind, body with
  | .type, .erased => .ok ⟨rfl⟩
  | .ctor, .lam .many (.lam .many (.lam .many (.var 0))) => .ok ⟨rfl⟩
  | .lift,
      .lam .many (.lam .many (.lam .many (.lam .many (.lam .many
        (.lam .many (.app (.var 2) (.var 0))))))) => .ok ⟨rfl⟩
  | .ind,
      .lam .many (.lam .many (.lam .many (.lam .many
        (.lam .many (.app (.var 1) (.var 0)))))) => .ok ⟨rfl⟩
  | _, _ => .error "erased quotient body mismatch"

/-- Check an ignored constructor-parameter wrapper without assuming global
decidable equality for target expressions. -/
private def validateCtorWrapper : (remaining : Nat) → (address : Address) →
    (body : IxIR0.Expr) →
      Except String (PLift (body = Erase.lamManyN remaining (.ref address)))
  | 0, address, .ref target =>
    if haddress : target = address then by
      subst target
      exact .ok ⟨rfl⟩
    else .error "constructor wrapper address mismatch"
  | remaining + 1, address, .lam .many body =>
    match validateCtorWrapper remaining address body with
    | .ok hbody => by
      rw [hbody.down]
      exact .ok ⟨rfl⟩
    | .error message => .error message
  | _ + 1, _, .lam _ _ => .error "constructor wrapper binder mode mismatch"
  | _, _, _ => .error "constructor wrapper body mismatch"

/-- Check the body of an indexed-recursor continuation.  `anchor` remains
constant while ignored binders are peeled because it names the let-captured
pre-major pap below the entire wrapper telescope. -/
private def validateRecIndexWrapper : (remaining anchor : Nat) →
    (body : IxIR0.Expr) →
      Except String
        (PLift (body = Erase.lamManyN remaining (.var anchor)))
  | 0, anchor, .var target =>
    if hindex : target = anchor then by
      subst target
      exact .ok ⟨rfl⟩
    else .error "indexed recursor wrapper capture mismatch"
  | remaining + 1, anchor, .lam .many body =>
    match validateRecIndexWrapper remaining anchor body with
    | .ok hbody => by
      rw [hbody.down]
      exact .ok ⟨rfl⟩
    | .error message => .error message
  | _ + 1, _, .lam _ _ =>
      .error "indexed recursor wrapper binder mode mismatch"
  | _, _, _ => .error "indexed recursor wrapper body mismatch"

/-- Certify that a pending recursor-policy suffix contains only source drops. -/
private def validateDropSuffix : (rest : List Erase.ArgPolicy) →
    Except String
      (PLift (rest = List.replicate rest.length Erase.ArgPolicy.drop))
  | [] => .ok ⟨rfl⟩
  | .drop :: rest =>
    match validateDropSuffix rest with
    | .ok hrest => by
      rw [hrest.down]
      exact .ok ⟨by simp [List.replicate_succ]⟩
    | .error message => .error message
  | _ :: _ => .error "indexed recursor wrapper begins before the index suffix"

private def validateRecurSafety (muts : Array MutConst) (recIdx : UInt64) :
    Except String (PLift (∀ r, muts[recIdx.toNat]? = some (.recr r) →
      r.indices.toNat = 0)) :=
  match hm : muts[recIdx.toNat]? with
  | some (.recr r) =>
    if hx : r.indices.toNat = 0 then
      .ok ⟨by
        intro r' hr
        injection hr with heq
        cases heq
        exact hx⟩
    else .error "indexed recursive self calls are outside the proved fragment"
  | none => .ok ⟨by
      intro r hr
      simp at hr⟩
  | some (.defn d) => .ok ⟨by
      intro r hr
      simp at hr⟩
  | some (.indc ind) => .ok ⟨by
      intro r hr
      simp at hr⟩

mutual
  /-- Validate one source/target expression pair and construct its `PErase`
  derivation.  This checks the relation rather than merely reimplementing an
  equality test; the return type is the soundness theorem. -/
  def validateExprWithRec (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
      (cover : CoverOracle ectx ictx) (recMembers : RecMemberOracle ectx ictx)
      (sc : Option (Address × Nat)) (refs : Array Address)
      (muts : Array MutConst) (sa : Option Address) (mask : List Bool) :
      Nat → (e : Ixon.Expr) → (e' : IxIR0.Expr) →
        Except String (PLift (PErase ectx ictx sc refs muts sa mask e e'))
    | 0, _, _ => fail "validation fuel exhausted"
    | fuel + 1, e, e' =>
      match validateRecSpine ectx ictx cover recMembers sc refs muts sa mask
          fuel e e' with
      | .ok ⟨r, [], hs⟩ => .ok ⟨.recP hs.down⟩
      | _ =>
        match e, e' with
        | .var i, .var j =>
          if hij : i.toNat = j then
            match hm : mask[i.toNat]? with
            | some true => by
              subst j
              exact .ok ⟨.var hm⟩
            | _ => fail s!"variable {i.toNat} is not a kept slot"
          else fail "variable index mismatch"
        | .sort _, .erased => .ok ⟨.sortE⟩
        | .all _ _ _ _, .erased => .ok ⟨.allE⟩
        | .lam u dom body, .lam u' body' =>
          match hd : dropB u dom with
          | true =>
            if hu : u' = .many then by
              subst u'
              match validateExprWithRec ectx ictx cover recMembers sc refs muts sa
                  (false :: mask) fuel body body' with
              | .ok hb => exact .ok ⟨.lamD hd hb.down⟩
              | .error msg => exact .error msg
            else fail "dropped lambda binder did not lower to many"
          | false =>
            if hu : u' = u then by
              subst u'
              match validateExprWithRec ectx ictx cover recMembers sc refs muts sa
                  (true :: mask) fuel body body' with
              | .ok hb => exact .ok ⟨.lamK hd hb.down⟩
              | .error msg => exact .error msg
            else fail "kept lambda binder mode changed"
        | source, .lam .many body' =>
          match ctorParamSpine? ectx refs (fuel + 1) source with
          | some cert =>
            if hj : cert.consumed < cert.params then
              match validateCtorWrapper
                  (cert.params - cert.consumed - 1) cert.address body' with
              | .error message => .error message
              | .ok hbody => by
                rw [hbody.down]
                exact match he : ictx.env cert.address with
                | some (.ctor tag fields) =>
                  if ht : cert.cidx = tag then by
                    subst tag
                    exact if hf : cert.fields = fields then by
                      subst fields
                      exact .ok ⟨.ctorW cert.spine hj he⟩
                    else fail "constructor field count mismatch"
                  else fail "constructor tag mismatch"
                | _ => fail "erased constructor declaration is missing"
            else fail "constructor wrapper has no remaining parameters"
          | none => fail "source is not a partial constructor parameter spine"
        | .app f a, .app f' .erased =>
          let normal (f₀ a₀ : Ixon.Expr) (f₀' a₀' : IxIR0.Expr) :
              Except String (PLift (PErase ectx ictx sc refs muts sa mask
                (.app f₀ a₀) (.app f₀' a₀'))) := do
            let hf ← validateExprWithRec ectx ictx cover recMembers sc refs muts sa
              mask fuel f₀ f₀'
            let ha ← validateExprWithRec ectx ictx cover recMembers sc refs muts sa
              mask fuel a₀ a₀'
            pure ⟨.app hf.down ha.down⟩
          let fallback : Except String
              (PLift (PErase ectx ictx sc refs muts sa mask
                (.app f a) (.app f' .erased))) :=
            match f with
            | .lam u dom body =>
              match hd : dropB u dom with
              | true => do
                let hf ← validateExprWithRec ectx ictx cover recMembers sc refs muts sa mask
                  fuel (.lam u dom body) f'
                pure ⟨.appE hd hf.down⟩
              | false => normal (.lam u dom body) a f' .erased
            | other => normal other a f' .erased
          let definitionFallback : Except String
              (PLift (PErase ectx ictx sc refs muts sa mask
                (.app f a) (.app f' .erased))) :=
            match defSpine? ectx refs (fuel + 1) f with
            | some cert =>
              match hr : cert.residual with
              | .lam uses domain body =>
                match hd : dropB uses domain with
                | true => by
                  have hspine := cert.spine
                  rw [hr] at hspine
                  exact do
                    let hf ← validateExprWithRec ectx ictx cover recMembers sc
                      refs muts sa mask fuel f f'
                    pure ⟨.appDG hspine hd hf.down⟩
                | false => fallback
              | _ => fallback
            | none => fallback
          match recSpine? ectx refs muts sa (fuel + 1) f with
          | some ⟨r, j, hs⟩ =>
            match hj : (recRulePolicy r)[j]? with
            | some .ghost => do
              let hf ← validateExprWithRec ectx ictx cover recMembers sc refs muts sa mask
                fuel f f'
              pure ⟨.appG hs.down hj hf.down⟩
            | _ => definitionFallback
          | none => definitionFallback
        | .app f a, .app f' a' => do
          let hf ← validateExprWithRec ectx ictx cover recMembers sc refs muts sa
            mask fuel f f'
          let ha ← validateExprWithRec ectx ictx cover recMembers sc refs muts sa
            mask fuel a a'
          pure ⟨.app hf.down ha.down⟩
        | .app f a, .ref a' =>
          match ctorParamSpine? ectx refs (fuel + 1) (.app f a) with
          | some cert =>
            if ha : cert.address = a' then by
              subst a'
              exact if hp : 0 < cert.params then
                if hj : cert.consumed = cert.params then
                  match he : ictx.env cert.address with
                  | some (.ctor tag fields) =>
                    if ht : cert.cidx = tag then by
                      subst tag
                      exact if hf : cert.fields = fields then by
                        subst fields
                        have hspine := cert.spine
                        rw [hj] at hspine
                        exact .ok ⟨.ctorP hp hspine he⟩
                      else fail "constructor field count mismatch"
                    else fail "constructor tag mismatch"
                  | _ => fail "erased constructor declaration is missing"
                else fail "constructor parameter prefix is incomplete"
              else fail "constructor drop spine has no parameters"
            else fail "constructor address mismatch"
          | none => fail "source is not a visible constructor parameter spine"
        | source, .letE .many val' body' =>
          match validateRecSpine ectx ictx cover recMembers sc refs muts sa mask
              fuel source val' with
          | .ok ⟨r, rest, hs⟩ =>
            if hpositive : 0 < rest.length then
              match validateDropSuffix rest with
              | .error message => .error message
              | .ok hrest =>
                match validateRecIndexWrapper rest.length rest.length body' with
                | .error message => .error message
                | .ok hbody => by
                  rw [hrest.down] at hs
                  rw [hbody.down]
                  simpa [Erase.captureThenIgnoreN] using
                    (.ok ⟨PErase.recW hs.down hpositive⟩ :
                      Except String (PLift (PErase ectx ictx sc refs muts sa
                        mask source
                        (Erase.captureThenIgnoreN rest.length val'))))
            else fail "indexed recursor wrapper has no pending indices"
          | .error _ =>
            match source with
            | .letE _ _ val body => do
              let hv ← validateExprWithRec ectx ictx cover recMembers sc refs
                muts sa mask fuel val val'
              let hb ← validateExprWithRec ectx ictx cover recMembers sc refs
                muts sa (true :: mask) fuel body body'
              pure ⟨.letE hv.down hb.down⟩
            | _ => fail "target let is not an indexed recursor wrapper"
        | .ref idx us, .ref a' =>
          match hr : refs[idx.toNat]? with
          | some a =>
            if ha : a = a' then by
              subst a'
              match hc : cover a with
              | some cov => exact .ok ⟨.ref hr cov.down⟩
              | none => exact fail "reference lacks a Covered certificate"
            else fail "reference address mismatch"
          | none => fail s!"reference {idx.toNat} is out of range"
        | .recur recIdx us, .ref member =>
          match sa with
          | some block =>
            if hmember : member =
                Erase.memberAddr block recIdx.toNat then by
              subst member
              exact match hm : Ixon.Eval.resolveMut ectx block
                  recIdx.toNat with
              | .ok (bc, .defn d) =>
                if hrefs : refs = bc.refs then
                  if hmuts : muts = Ixon.selfMutsOf bc.info then
                    match hu : Ixon.Eval.unfoldable d with
                    | true =>
                      if hplan : (⟨block, recIdx.toNat⟩ : MemberKey) ∈
                          scope.plan then
                        .ok ⟨.recurD rfl hm hrefs hmuts hu hplan⟩
                      else fail
                        "definition member is absent from the simultaneous plan"
                    | false =>
                      match hconfigured : ectx.externArity
                          (Erase.memberAddr block recIdx.toNat) with
                      | none => fail
                          "opaque definition member extern is not configured"
                      | some arity =>
                        if hplan : (⟨block, recIdx.toNat⟩ : MemberKey) ∈
                            scope.plan then
                          .ok ⟨.recurO rfl hm hrefs hmuts hu hconfigured hplan⟩
                        else fail
                          "opaque definition member is absent from the simultaneous plan"
                  else fail "definition-member frame table mismatch"
                else fail "definition-member refs mismatch"
              | .ok (bc, .recr r) =>
                if hrefs : refs = bc.refs then
                  if hmuts : muts = Ixon.selfMutsOf bc.info then
                    if hi : r.indices.toNat = 0 then
                      if hplan : (⟨block, recIdx.toNat⟩ : MemberKey) ∈
                          scope.plan then
                        .ok ⟨.recurR rfl hm hrefs hmuts hi hplan⟩
                      else fail
                        "recursor member is absent from the simultaneous plan"
                    else fail
                      "indexed recursor member requires protected-spine validation"
                  else fail "recursor-member frame table mismatch"
                else fail "recursor-member refs mismatch"
              | .ok (bc, .indc ind) =>
                if hrefs : refs = bc.refs then
                  match hi : muts[recIdx.toNat]? with
                  | some (.indc frameInd) =>
                    if hind : frameInd = ind then by
                      subst frameInd
                      exact match he : ictx.env
                          (Erase.memberAddr block recIdx.toNat) with
                      | some (.defn .shared .erased) =>
                        .ok ⟨.recurI rfl hm hrefs hi he⟩
                      | _ => fail "erased inductive member is missing"
                    else fail "non-self recur mutual member mismatch"
                  | _ => fail
                      "non-self recur does not target an inductive member"
                else fail "non-self recur refs mismatch"
              | .error _ => fail "non-self recur member is unresolved"
            else fail "non-self recur member address mismatch"
          | none => fail "non-self recur is outside a mutual block"
        | .recur recIdx us, .var j =>
          match sc with
          | some (block, idx) =>
            if hi : recIdx.toNat = idx then
              if hj : mask.length = j then by
                subst j
                match validateRecurSafety muts recIdx with
                | .ok hs => exact .ok ⟨.recurS hi hs.down⟩
                | .error msg => exact .error msg
              else fail "recursor-self slot mismatch"
            else fail "recursor-self member mismatch"
          | none => fail "non-self recur is outside the proved fragment"
        | .nat idx, .lit (.nat n') =>
          match hr : refs[idx.toNat]? with
          | some a =>
            match hb : ectx.blobs a with
            | some (.natB n) =>
              if hn : n = n' then by
                subst n'
                exact .ok ⟨.natE hr hb⟩
              else fail "nat literal value mismatch"
            | _ => fail "nat literal blob mismatch"
          | none => fail s!"nat literal ref {idx.toNat} is out of range"
        | .str idx, .lit (.str s') =>
          match hr : refs[idx.toNat]? with
          | some a =>
            match hb : ectx.blobs a with
            | some (.strB s) =>
              if hs : s = s' then by
                subst s'
                exact .ok ⟨.strE hr hb⟩
              else fail "string literal value mismatch"
            | _ => fail "string literal blob mismatch"
          | none => fail s!"string literal ref {idx.toNat} is out of range"
        | .prj _ fieldIdx val, .proj fieldIdx' val' =>
          if hi : fieldIdx.toNat = fieldIdx' then by
            subst fieldIdx'
            match validateExprWithRec ectx ictx cover recMembers sc refs muts sa mask
                fuel val val' with
            | .ok hv => exact .ok ⟨.prjE hv.down⟩
            | .error msg => exact .error msg
          else fail "projection field mismatch"
        | .share _, _ =>
          fail "raw shares require sharing-aware inlining before PErase validation"
        | _, _ => fail "source and target erasure shapes do not match"

  /-- Reconstruct the exact visible prefix of an indexed recursor.  A `drop`
  step consumes only the source argument; `keep` and `ghost` steps follow the
  target application spine. -/
  def validateRecSpine (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
      (cover : CoverOracle ectx ictx) (recMembers : RecMemberOracle ectx ictx)
      (sc : Option (Address × Nat)) (refs : Array Address)
      (muts : Array MutConst) (sa : Option Address) (mask : List Bool) :
      Nat → (e : Ixon.Expr) → (e' : IxIR0.Expr) →
        Except String (Σ r : Recursor, Σ rest : List Erase.ArgPolicy,
          PLift (RecEraseSpine ectx ictx sc refs muts sa mask e e' r rest))
    | 0, _, _ => .error "indexed recursor-spine validation fuel exhausted"
    | fuel + 1, e, e' =>
      match e with
      | .ref refIdx univIdxs =>
        match e' with
        | .ref a' =>
          match hr : refs[refIdx.toNat]? with
          | some a =>
            if ha : a = a' then
              match hc : ectx.resolve a with
              | some c =>
                match hi : c.info with
                | .rPrj p =>
                  match hm : Ixon.Eval.resolveMut ectx p.block p.idx.toNat with
                  | .ok (bc, .recr r) =>
                    if hx : 0 < r.indices.toNat then
                      match hd : ictx.env a with
                      | some (.defn .shared (.ref member)) =>
                        if hmember : member =
                            Erase.memberAddr p.block p.idx.toNat then
                          match ho : recMembers p.block p.idx.toNat bc r hm with
                          | some hrec => by
                            subst a'
                            subst member
                            exact .ok ⟨r, recPolicy r,
                              ⟨.head hr hc hi hm hx hd hrec.down⟩⟩
                          | none =>
                            .error
                              "indexed recursor member lacks a certificate"
                        else .error
                          "indexed recursor projection points at the wrong member"
                      | _ => .error
                          "indexed recursor projection declaration is missing"
                    else .error "recursor has no source-only indices"
                  | _ => .error
                      "recursor projection does not resolve to a recursor"
                | _ => .error
                    "source reference is not a recursor projection"
              | none => .error "recursor projection address is unresolved"
            else .error "indexed recursor projection address mismatch"
          | none => .error "indexed recursor source reference is out of range"
        | _ => .error "indexed recursor head did not erase to a reference"
      | .recur recIdx univIdxs =>
        match e' with
        | .var targetIndex =>
          match sc with
          | some (block, idx) =>
            if hself : recIdx.toNat = idx then
              if hslot : mask.length = targetIndex then by
                subst targetIndex
                exact if hsa : sa = some block then
                  match hm : Ixon.Eval.resolveMut ectx block idx with
                  | .ok (bc, .recr r) =>
                    if hx : 0 < r.indices.toNat then
                      if hrefs : refs = bc.refs then
                        match hlookup : muts[recIdx.toNat]? with
                        | some (.recr selfR) =>
                          if hrecur : selfR = r then by
                            subst selfR
                            exact .ok ⟨r, recPolicy r,
                              ⟨.selfHead rfl hsa hself hm hrefs hlookup hx⟩⟩
                          else .error
                            "indexed recursive self recursor mismatch"
                        | _ => .error
                            "indexed recursive self mutual slot mismatch"
                      else .error "indexed recursive self refs mismatch"
                    else .error "recursive self has no source-only indices"
                  | _ => .error "indexed recursive self does not resolve"
                else .error "indexed recursive self block mismatch"
              else .error "indexed recursive self slot mismatch"
            else .error "indexed recursive self member mismatch"
          | none => .error "indexed recursive self lacks a self context"
        | .ref member =>
          match sa with
          | some block =>
            if hmember : member =
                Erase.memberAddr block recIdx.toNat then by
              subst member
              exact match hm : Ixon.Eval.resolveMut ectx block
                  recIdx.toNat with
              | .ok (bc, .recr r) =>
                if hx : 0 < r.indices.toNat then
                  if hrefs : refs = bc.refs then
                    if hmuts : muts = Ixon.selfMutsOf bc.info then
                      if hplan : (⟨block, recIdx.toNat⟩ : MemberKey) ∈
                          scope.plan then
                        .ok ⟨r, recPolicy r,
                          ⟨.memberHead rfl hm hrefs hmuts hx hplan⟩⟩
                      else .error
                        "indexed recursor is absent from the simultaneous plan"
                    else .error "indexed recursor frame table mismatch"
                  else .error "indexed recursor refs mismatch"
                else .error "recursor has no source-only indices"
              | _ => .error "mutual member is not an indexed recursor"
            else .error "indexed mutual recursor member address mismatch"
          | none => .error "indexed mutual recursor is outside a block"
        | _ => .error "indexed recursive self head did not erase to its slot"
      | .app f a =>
        match validateRecSpine ectx ictx cover recMembers sc refs muts sa mask
            fuel f e' with
        | .ok ⟨r, .drop :: rest, hs⟩ =>
          .ok ⟨r, rest, ⟨.drop hs.down⟩⟩
        | _ =>
          match e' with
          | .app f' a' =>
            match validateRecSpine ectx ictx cover recMembers sc refs muts sa
                mask fuel f f' with
            | .ok ⟨r, .keep :: rest, hs⟩ =>
              match validateExprWithRec ectx ictx cover recMembers sc refs muts
                  sa mask fuel a a' with
              | .ok ha => .ok ⟨r, rest, ⟨.keep hs.down ha.down⟩⟩
              | .error msg => .error msg
            | .ok ⟨r, .ghost :: rest, hs⟩ =>
              match a' with
              | .erased => .ok ⟨r, rest, ⟨.ghost hs.down⟩⟩
              | _ => .error "recursor ghost argument is not erased"
            | .ok ⟨_, .drop :: _, _⟩ =>
              .error "recursor drop unexpectedly emitted a target argument"
            | .ok ⟨_, [], _⟩ =>
              .error "recursor spine extends past the pre-major policy"
            | .error msg => .error msg
          | _ => .error "recursor keep/ghost step lacks a target application"
      | _ => .error "source is not a visible indexed recursor spine"
end

/-- Backward-compatible index-free validator entry point. -/
def validateExpr (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (cover : CoverOracle ectx ictx)
    (sc : Option (Address × Nat)) (refs : Array Address)
    (muts : Array MutConst) (sa : Option Address) (mask : List Bool)
    (fuel : Nat) (e : Ixon.Expr) (e' : IxIR0.Expr) :
    Except String (PLift (PErase ectx ictx sc refs muts sa mask e e')) :=
  validateExprWithRec ectx ictx cover noRecMembers sc refs muts sa mask
    fuel e e'

/-- Extract the relation proof from a successful validation.  Concrete
programs normally discharge `h` by reduction (`rfl`/`decide`), replacing a
hand-written `PErase` constructor tree with one checked computation. -/
theorem related_of_validateExprWithRec
    {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {cover : CoverOracle ectx ictx}
    {recMembers : RecMemberOracle ectx ictx}
    {sc : Option (Address × Nat)} {refs : Array Address}
    {muts : Array MutConst} {sa : Option Address}
    {mask : List Bool} {fuel : Nat} {e : Ixon.Expr} {e' : IxIR0.Expr}
    (h : (validateExprWithRec ectx ictx cover recMembers sc refs muts sa
      mask fuel e e').toOption.isSome) :
    PErase ectx ictx sc refs muts sa mask e e' :=
  ((validateExprWithRec ectx ictx cover recMembers sc refs muts sa mask
    fuel e e').toOption.get h).down

theorem related_of_validateExpr
    {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {cover : CoverOracle ectx ictx} {sc : Option (Address × Nat)}
    {refs : Array Address} {muts : Array MutConst} {sa : Option Address}
    {mask : List Bool} {fuel : Nat} {e : Ixon.Expr} {e' : IxIR0.Expr}
    (h : (validateExpr ectx ictx cover sc refs muts sa mask fuel e e').toOption.isSome) :
    PErase ectx ictx sc refs muts sa mask e e' :=
  ((validateExpr ectx ictx cover sc refs muts sa mask fuel e e').toOption.get h).down

/-! ## Program coverage validation

Expression validation consumes `Covered` facts.  The finite database and
validators below construct those facts from the source resolver and target
environment.  Dependencies are supplied in topological order; this is an
explicit certificate schedule, not trusted graph analysis. -/

structure CoveredEntry (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx) where
  address : Address
  covered : Covered ectx ictx address

abbrev CoverageDB (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx) :=
  List (CoveredEntry ectx ictx)

def CoverageDB.lookup {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx} :
    CoverageDB ectx ictx → (a : Address) → Option (PLift (Covered ectx ictx a))
  | [], _ => none
  | entry :: rest, a =>
    if h : entry.address = a then
      some ⟨by cases h; exact entry.covered⟩
    else lookup rest a

def CoverageDB.oracle {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    (db : CoverageDB ectx ictx) : CoverOracle ectx ictx :=
  db.lookup

/-- Validate the finite mutual-block parameter layout stored by `RecMember`.
Only inductive members constrain the common count. -/
def validateBlockParams (params : Nat) :
    (members : List MutConst) →
      Except String (PLift (BlockParams params members))
  | [] => .ok ⟨.nil⟩
  | .defn _ :: rest => do
      let hrest ← validateBlockParams params rest
      pure ⟨.defn hrest.down⟩
  | .recr _ :: rest => do
      let hrest ← validateBlockParams params rest
      pure ⟨.recr hrest.down⟩
  | .indc ind :: rest =>
      if hp : ind.params.toNat = params then do
        let hrest ← validateBlockParams params rest
        pure ⟨.indc hp hrest.down⟩
      else fail "mutual-block inductive parameter count disagrees with recursor"

/-- Validate corresponding recursor rules, including each peeled body. -/
def validateRules (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (db : CoverageDB ectx ictx) (block : Address) (idx : Nat)
    (r : Recursor) (refs : Array Address) (muts : Array MutConst) :
    Nat → (rules : List RecursorRule) → (trules : List IxIR0.RecRule) →
      Except String (PLift
        (RulesRel ectx ictx block idx r refs muts rules trules))
  | 0, _, _ => fail "rule validation fuel exhausted"
  | _ + 1, [], [] => .ok ⟨.nil⟩
  | fuel + 1, rule :: rest, trule :: trest =>
    if hf : trule.fields = rule.fields.toNat then
      match hp : peelChain
          (r.params.toNat + r.motives.toNat + r.minors.toNat +
            rule.fields.toNat)
          rule.rhs with
      | some body => do
        let hb ← validateExpr ectx ictx db.oracle (some (block, idx))
          refs muts (some block)
          (recRuleMask r rule.fields.toNat)
          fuel body trule.rhs
        let hr ← validateRules ectx ictx db block idx r refs muts
          fuel rest trest
        pure ⟨.cons hf hp hb.down hr.down⟩
      | none => fail "recursor rule is not a literal lambda chain"
    else fail "recursor rule field count mismatch"
  | _ + 1, _, _ => fail "recursor rule list length mismatch"

/-- Validate the member-level declaration and rules for one recursor. -/
def validateRecMember (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (db : CoverageDB ectx ictx) (block : Address) (idx : Nat)
    (bc : Constant) (r : Recursor)
    (hm : Ixon.Eval.resolveMut ectx block idx = .ok (bc, .recr r))
    (fuel : Nat) : Except String (PLift (RecMember ectx ictx block idx r)) :=
  match validateBlockParams r.params.toNat
      (Ixon.selfMutsOf bc.info).toList with
  | .error msg => .error msg
  | .ok hparams =>
    match he : ictx.env (Erase.memberAddr block idx) with
    | some (.recursor n natLit trules) =>
      if hn : n = r.params.toNat + r.motives.toNat +
          r.minors.toNat then
        if hl : natLit = (ectx.natBlock == some block) then
          match validateRules ectx ictx db block idx r bc.refs
              (Ixon.selfMutsOf bc.info) fuel r.rules.toList
              trules.toList with
          | .ok hrs => by
            subst n
            subst natLit
            exact .ok ⟨.mk hm hparams.down he hrs.down⟩
          | .error msg => .error msg
        else fail "recursor natLit identity mismatch"
      else fail "recursor erased arity mismatch"
    | _ => fail "erased recursor member declaration is missing"

/-- Extract a member certificate from one successful checked computation. -/
theorem recMember_of_validate
    {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {db : CoverageDB ectx ictx} {block : Address} {idx : Nat}
    {bc : Constant} {r : Recursor}
    {hm : Ixon.Eval.resolveMut ectx block idx = .ok (bc, .recr r)}
    {fuel : Nat}
    (h : (validateRecMember ectx ictx db block idx bc r hm fuel).toOption.isSome) :
    RecMember ectx ictx block idx r :=
  ((validateRecMember ectx ictx db block idx bc r hm fuel).toOption.get h).down

/-- Validate one address against the source resolver and erased target
environment, constructing the corresponding `Covered` proof. -/
def validateCovered (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (db : CoverageDB ectx ictx) (fuel : Nat) (a : Address) :
    Except String (PLift (Covered ectx ictx a)) :=
  match fuel with
  | 0 => fail "coverage validation fuel exhausted"
  | fuel + 1 =>
    match hc : ectx.resolve a with
    | none => fail "coverage address is absent from the source resolver"
    | some c =>
      match hi : c.info with
      | .defn d =>
        match hu : Ixon.Eval.unfoldable d with
        | true =>
          match he : ictx.env a with
          | some (.defn result body') => do
            let hresult ← validateTeleResultOwned c.sharing fuel d.typ
            if heq : result = hresult.1.getD .shared then
              let hb ← validateExpr ectx ictx db.oracle none c.refs
                (Ixon.selfMutsOf c.info) none [] fuel d.value body'
              let howned : DefinitionResultOwned c.sharing d.typ result :=
                ⟨hresult.1, hresult.2.down, heq⟩
              pure ⟨.defn hc hi hu he howned hb.down⟩
            else fail "definition result ownership mismatch"
          | _ => fail "erased definition is missing"
        | false =>
          match hconfigured : ectx.externArity a with
          | none => fail "extern address is not configured"
          | some arity =>
            match he : ictx.env a with
            | some (.extern targetArity) =>
              if harity : targetArity = arity then by
                subst targetArity
                exact .ok ⟨.externDefn hc hi hu hconfigured he⟩
              else fail "configured extern arity mismatch"
            | _ => fail "erased extern declaration is missing"
      | .axio ax =>
        match hconfigured : ectx.externArity a with
        | none => fail "extern address is not configured"
        | some arity =>
          match he : ictx.env a with
          | some (.extern targetArity) =>
            if harity : targetArity = arity then by
              subst targetArity
              exact .ok ⟨.externAxio hc hi hconfigured he⟩
            else fail "configured extern arity mismatch"
          | _ => fail "erased extern declaration is missing"
      | .cPrj p =>
        match hm : Ixon.Eval.resolveMut ectx p.block p.idx.toNat with
        | .ok (bc, .indc ind) =>
          match ht : ind.ctors[p.cidx.toNat]? with
          | some ct =>
            if hip : ind.params.toNat = 0 then
              if hcp : ct.params.toNat = 0 then
                match he : ictx.env a with
                | some (.ctor tag fields) =>
                  if htag : p.cidx.toNat = tag then
                    if hfields : ct.fields.toNat = fields then by
                      subst tag
                      subst fields
                      let shape : CtorShape ectx p.block p.idx.toNat
                          p.cidx.toNat 0 ct.fields.toNat :=
                        ⟨bc, ind, ct, hm, ht, hip, hcp, rfl⟩
                      exact .ok ⟨.ctor hc hi shape he⟩
                    else fail "constructor field count mismatch"
                  else fail "constructor tag mismatch"
                | _ => fail "erased constructor declaration is missing"
              else fail "bare parameterized constructor heads are outside Covered"
            else fail "inductive parameters are outside the current simulation fragment"
          | none => fail "constructor projection is out of range"
        | _ => fail "constructor projection does not resolve to an inductive"
      | .iPrj p =>
        match he : ictx.env a with
        | some (.defn .shared .erased) => .ok ⟨.tyf hc hi he⟩
        | _ => fail "erased inductive-type projection is missing"
      | .quot q =>
        match hconfigured : ectx.quotientKind a with
        | none => fail "quotient address is not configured"
        | some kind =>
          if hkind : kind = q.kind then by
            subst kind
            exact match he : ictx.env a with
            | some (.defn result body) =>
              match validateQuotientBody q.kind body with
              | .error msg => .error msg
              | .ok hbody => by
                rw [hbody.down] at he
                exact do
                  let hresult ← validateTeleResultOwned c.sharing fuel q.typ
                  if heq : result = hresult.1.getD .shared then
                    let howned : DefinitionResultOwned c.sharing q.typ result :=
                      ⟨hresult.1, hresult.2.down, heq⟩
                    pure ⟨.quot hc hi hconfigured he howned⟩
                  else fail "quotient result ownership mismatch"
            | _ => fail "erased quotient declaration is missing"
          else fail "configured quotient kind mismatch"
      | .dPrj p =>
        match hm : Ixon.Eval.resolveMut ectx p.block p.idx.toNat with
        | .ok (bc, .defn d) =>
          match hu : Ixon.Eval.unfoldable d with
          | true =>
            match ha : ictx.env a with
            | some (.defn aliasResult (.ref member)) =>
              if hmember : member =
                  Erase.memberAddr p.block p.idx.toNat then by
                subst member
                exact match he : ictx.env
                    (Erase.memberAddr p.block p.idx.toNat) with
                | some (.defn result body') =>
                  if hresult : aliasResult = result then
                    match ho : validateTeleResultOwned bc.sharing fuel d.typ with
                    | .error message => .error message
                    | .ok ⟨candidate, howned⟩ =>
                      if heq : result = candidate.getD .shared then
                        match hb : validateExpr ectx ictx db.oracle none bc.refs
                            (Ixon.selfMutsOf bc.info) (some p.block) []
                            fuel d.value body' with
                        | .error message => .error message
                        | .ok hbody => by
                          have halias : ictx.env a = some (.defn result
                              (.ref (Erase.memberAddr p.block
                                p.idx.toNat))) := by
                            simpa [hresult] using ha
                          exact .ok ⟨Covered.defnProj hc hi hm hu halias he
                            ⟨candidate, howned.down, heq⟩ hbody.down⟩
                      else fail
                        "definition-projection result ownership mismatch"
                  else fail "definition-projection alias ownership mismatch"
                | _ => fail "erased definition member is missing"
              else fail "definition projection points at the wrong member"
            | _ => fail "erased definition projection is missing"
          | false =>
            match ha : ictx.env a with
            | some (.defn aliasResult (.ref member)) =>
              if hmember : member =
                  Erase.memberAddr p.block p.idx.toNat then by
                subst member
                exact match hconfigured : ectx.externArity
                    (Erase.memberAddr p.block p.idx.toNat) with
                | none => fail
                    "opaque definition member extern is not configured"
                | some arity =>
                  match he : ictx.env
                      (Erase.memberAddr p.block p.idx.toNat) with
                  | some (.extern targetArity) =>
                    if harity : targetArity = arity then by
                      subst targetArity
                      exact match ho : validateTeleResultOwned bc.sharing fuel
                          d.typ with
                      | .error message => .error message
                      | .ok ⟨candidate, howned⟩ =>
                        if heq : aliasResult = candidate.getD .shared then
                          let hresult : DefinitionResultOwned bc.sharing d.typ
                              aliasResult := ⟨candidate, howned.down, heq⟩
                          .ok ⟨Covered.externDefnProj hc hi hm hu hconfigured
                            ha he hresult⟩
                        else fail
                          "definition-projection result ownership mismatch"
                    else fail "opaque definition member extern arity mismatch"
                  | _ => fail "erased opaque definition member extern is missing"
              else fail "definition projection points at the wrong member"
            | _ => fail "erased opaque definition projection is missing"
        | _ => fail "definition projection does not resolve to a definition"
      | .rPrj p =>
        match hm : Ixon.Eval.resolveMut ectx p.block p.idx.toNat with
        | .ok (bc, .recr r) =>
          if hx : r.indices.toNat = 0 then
            match he : ictx.env a with
            | some (.defn .shared (.ref member)) =>
              if ha : member = Erase.memberAddr p.block p.idx.toNat then by
                subst member
                match validateRecMember ectx ictx db p.block p.idx.toNat
                    bc r hm fuel with
                | .ok hr => exact .ok ⟨.recrP hc hi hm hx he hr.down⟩
                | .error msg => exact .error msg
              else fail "recursor projection points at the wrong member"
            | _ => fail "erased recursor projection is missing"
          else fail "bare indexed recursor projections are outside Covered"
        | _ => fail "recursor projection does not resolve to a recursor"
      | _ => fail "constant kind is outside the current Covered fragment"

/-- Check a dependency-ordered address plan, extending the proof database
after each successful entry. -/
def validateCoveragePlan (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx) :
    Nat → CoverageDB ectx ictx → List Address →
      Except String (CoverageDB ectx ictx)
  | 0, _, _ => .error "coverage-plan validation fuel exhausted"
  | _ + 1, db, [] => .ok db
  | fuel + 1, db, a :: rest => do
    let ha ← validateCovered ectx ictx db fuel a
    validateCoveragePlan ectx ictx fuel
      ({ address := a, covered := ha.down } :: db) rest

/-- Extract a `Covered` proof from one successful checked computation. -/
theorem covered_of_validate
    {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {db : CoverageDB ectx ictx} {fuel : Nat} {a : Address}
    (h : (validateCovered ectx ictx db fuel a).toOption.isSome) :
    Covered ectx ictx a :=
  ((validateCovered ectx ictx db fuel a).toOption.get h).down

/-- Validate one entry of a simultaneous mutual-member plan. The expression
and rule bodies are checked against the already completed public coverage
database, but recursive member edges close through `scope.plan` rather than
recursing in the validator. -/
def validateMemberRel (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (db : CoverageDB ectx ictx) :
    Nat → (key : MemberKey) →
      Except String (PLift (MemberRel ectx ictx key))
  | 0, _ => fail "member validation fuel exhausted"
  | fuel + 1, ⟨block, idx⟩ =>
    match hm : Ixon.Eval.resolveMut ectx block idx with
    | .ok (bc, .defn d) =>
      match hu : Ixon.Eval.unfoldable d with
      | false =>
        match hconfigured : ectx.externArity
            (Erase.memberAddr block idx) with
        | none => fail "opaque definition member extern is not configured"
        | some arity =>
          match he : ictx.env (Erase.memberAddr block idx) with
          | some (.extern targetArity) =>
            if harity : targetArity = arity then by
              subst targetArity
              exact .ok ⟨MemberRel.externDefn hm hu hconfigured he⟩
            else fail "opaque definition member extern arity mismatch"
          | _ => fail "erased opaque definition member extern is missing"
      | true =>
        match he : ictx.env (Erase.memberAddr block idx) with
        | some (.defn result body') => do
          let hresult ← validateTeleResultOwned bc.sharing fuel d.typ
          if heq : result = hresult.1.getD .shared then
            let hbody ← validateExpr ectx ictx db.oracle none bc.refs
              (Ixon.selfMutsOf bc.info) (some block) [] fuel d.value body'
            let howned : DefinitionResultOwned bc.sharing d.typ result :=
              ⟨hresult.1, hresult.2.down, heq⟩
            pure ⟨MemberRel.defn hm hu he howned hbody.down⟩
          else fail "mutual-definition result ownership mismatch"
        | _ => fail "erased mutual-definition member is missing"
    | .ok (bc, .recr r) => do
      let hmember ← validateRecMember ectx ictx db block idx bc r hm fuel
      pure ⟨MemberRel.recr hmember.down⟩
    | .ok (_, .indc _) =>
      fail "inductive members do not require simultaneous body coverage"
    | .error _ => fail "simultaneous member is unresolved"

/-- Close every open member edge with one finite certificate. -/
def validateMemberCoverage (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (db : CoverageDB ectx ictx) :
    Nat → (keys : List MemberKey) →
      Except String (PLift (MemberCoverage ectx ictx keys))
  | 0, _ => fail "member-plan validation fuel exhausted"
  | _ + 1, [] =>
    if hneutral : ectx.preserveNeutralElims = false then
      if hstrings : ectx.stringLiteral = none then
        .ok ⟨.nil ⟨hneutral, hstrings⟩⟩
      else
        fail "certified erasure requires String-literal expansion disabled"
    else
      fail "certified erasure requires strict neutral-elimination mode"
  | fuel + 1, key :: rest => do
    let hkey ← validateMemberRel ectx ictx db fuel key
    let hrest ← validateMemberCoverage ectx ictx db fuel rest
    pure ⟨.cons hkey.down hrest.down⟩

/-- Extract simultaneous coverage from a successful checked computation. -/
theorem memberCoverage_of_validate
    {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {db : CoverageDB ectx ictx} {fuel : Nat} {keys : List MemberKey}
    (h : (validateMemberCoverage ectx ictx db fuel keys).toOption.isSome) :
    MemberCoverage ectx ictx keys :=
  ((validateMemberCoverage ectx ictx db fuel keys).toOption.get h).down

inductive CertErr where
  | erase (err : Erase.EraseErr)
  | relation (msg : String)
  deriving BEq, Repr

/-- A whole executable-erasure result plus a database of `Covered` proofs
checked against the target environment built from that exact result. -/
structure CertifiedProgram (ectx : Ixon.Eval.EvalCtx)
    (consts : List (Address × Constant)) (eraseFuel : Nat) where
  target : List (Address × IxIR0.Decl)
  erased : Erase.eraseProgram (eraseCtxOf ectx) consts eraseFuel = .ok target
  coverage : CoverageDB ectx { env := IxIR0.Env.ofList target }
  members : MemberCoverage ectx { env := IxIR0.Env.ofList target } scope.plan

/-- Run the real program eraser and validate a dependency-ordered list of
addresses against its exact output.  The returned database is a reusable
`CoverOracle` for certifying entry expressions. -/
def certifyProgram (ectx : Ixon.Eval.EvalCtx)
    (consts : List (Address × Constant)) (coverageOrder : List Address)
    (eraseFuel : Nat := Erase.defaultFuel)
    (validateFuel : Nat := Erase.defaultFuel) :
    Except CertErr (CertifiedProgram ectx consts eraseFuel) :=
  match he : Erase.eraseProgram (eraseCtxOf ectx) consts eraseFuel with
  | .error err => .error (.erase err)
  | .ok target =>
    let targetIndex := IxIR0.Env.Index.ofList target
    let ictx : IxIR0.Ctx := { env := targetIndex.toEnv }
    match validateCoveragePlan ectx ictx validateFuel [] coverageOrder with
    | .error msg => .error (.relation msg)
    | .ok coverage =>
      match validateMemberCoverage ectx ictx coverage validateFuel
          scope.plan with
      | .error msg => .error (.relation msg)
      | .ok members =>
        have hictx : ictx = { env := IxIR0.Env.ofList target } := by
          simp [ictx, targetIndex]
        .ok ⟨target, he, hictx ▸ coverage, hictx ▸ members.down⟩

end MemberScoped

/-- A real erasure of the original shared program, paired with coverage facts
for the semantically inlined resolver.  The target environment is shared by
both facts, so no unproved eraser/inliner equality is assumed. -/
structure CertifiedSharedProgram (ectx : Ixon.Eval.EvalCtx)
    (consts : List (Address × Constant)) (eraseFuel : Nat)
    [scope : MemberScope] where
  target : List (Address × IxIR0.Decl)
  erased : Erase.eraseProgram (eraseCtxOf ectx) consts eraseFuel = .ok target
  coverage : CoverageDB ectx.inlineSharing
    { env := IxIR0.Env.ofList target }
  members : MemberCoverage ectx.inlineSharing
    { env := IxIR0.Env.ofList target } scope.plan

/-- Run the executable eraser on the original shared constants, then validate
its exact output against fully inlined constants obtained through the source
resolver.  Success produces the `Covered` database needed by sharing-aware
entry-expression certificates. -/
def certifySharedProgram [scope : MemberScope]
    (ectx : Ixon.Eval.EvalCtx)
    (consts : List (Address × Constant)) (coverageOrder : List Address)
    (eraseFuel : Nat := Erase.defaultFuel)
    (validateFuel : Nat := Erase.defaultFuel) :
    Except CertErr (CertifiedSharedProgram ectx consts eraseFuel) :=
  match he : Erase.eraseProgram (eraseCtxOf ectx) consts eraseFuel with
  | .error err => .error (.erase err)
  | .ok target =>
    let targetIndex := IxIR0.Env.Index.ofList target
    let ictx : IxIR0.Ctx := { env := targetIndex.toEnv }
    match validateCoveragePlan ectx.inlineSharing ictx validateFuel []
        coverageOrder with
    | .error msg => .error (.relation msg)
    | .ok coverage =>
      match validateMemberCoverage ectx.inlineSharing ictx coverage
          validateFuel scope.plan with
      | .error msg => .error (.relation msg)
      | .ok members =>
        have hictx : ictx = { env := IxIR0.Env.ofList target } := by
          simp [ictx, targetIndex]
        .ok ⟨target, he, hictx ▸ coverage, hictx ▸ members.down⟩

section MemberScopedExpr

variable [scope : MemberScope]

/-- An executable result and its relational proof, tied to exactly the same
source expression, tables, mask, and eraser invocation. -/
structure CertifiedExpr (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (sc : Option (Address × Nat)) (T : Erase.ETables) (sa : Option Address)
    (mask : List Bool) (eraseFuel : Nat) (source : Ixon.Expr) where
  target : IxIR0.Expr
  erased : Erase.eraseExpr (eraseCtxOf ectx) eraseFuel T mask source = .ok target
  related : PErase ectx ictx sc T.refs T.selfMuts sa mask source target

/-- Run the real executable eraser, then validate its exact result, with
member certificates available for projection-headed indexed recursor spines. -/
def certifyExprWithRec (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (cover : CoverOracle ectx ictx) (recMembers : RecMemberOracle ectx ictx)
    (sc : Option (Address × Nat)) (T : Erase.ETables) (sa : Option Address)
    (mask : List Bool) (source : Ixon.Expr)
    (eraseFuel : Nat := Erase.defaultFuel)
    (validateFuel : Nat := Erase.defaultFuel) :
    Except CertErr (CertifiedExpr ectx ictx sc T sa mask eraseFuel source) :=
  match he : Erase.eraseExpr (eraseCtxOf ectx) eraseFuel T mask source with
  | .error err => .error (.erase err)
  | .ok target =>
    match validateExprWithRec ectx ictx cover recMembers sc T.refs T.selfMuts
        sa mask validateFuel source target with
    | .error msg => .error (.relation msg)
    | .ok related => .ok ⟨target, he, related.down⟩

/-- Index-free compatibility wrapper for existing entry certificates. -/
def certifyExpr (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (cover : CoverOracle ectx ictx)
    (sc : Option (Address × Nat)) (T : Erase.ETables) (sa : Option Address)
    (mask : List Bool) (source : Ixon.Expr)
    (eraseFuel : Nat := Erase.defaultFuel)
    (validateFuel : Nat := Erase.defaultFuel) :
    Except CertErr (CertifiedExpr ectx ictx sc T sa mask eraseFuel source) :=
  certifyExprWithRec ectx ictx cover noRecMembers sc T sa mask source
    eraseFuel validateFuel

end MemberScopedExpr

/-- An executable erasure of an original shared expression and a `PErase`
proof for the fully inlined expression, both tied to the exact same target. -/
structure CertifiedSharedExpr (ectx : Ixon.Eval.EvalCtx)
    (ictx : IxIR0.Ctx) (sc : Option (Address × Nat))
    (T : Erase.ETables) (sa : Option Address) (mask : List Bool)
    (eraseFuel : Nat) (source : Ixon.Expr) [scope : MemberScope] where
  target : IxIR0.Expr
  erased : Erase.eraseExpr (eraseCtxOf ectx) eraseFuel T mask source =
    .ok target
  related : PErase ectx.inlineSharing ictx sc (inlineTables T).refs
    (inlineTables T).selfMuts sa mask
    (Ixon.Sharing.inlineExpr T.sharing source) target

/-- Run the real eraser before inlining, then validate its exact output against
the fully inlined expression and resolver.  This is the executable bridge to
`Sim.erasure_sim_inlineSharing`; malformed sharing still fails either erasure
or relation validation. -/
def certifySharedExpr [scope : MemberScope]
    (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (cover : CoverOracle ectx.inlineSharing ictx)
    (sc : Option (Address × Nat)) (T : Erase.ETables)
    (sa : Option Address) (mask : List Bool) (source : Ixon.Expr)
    (eraseFuel : Nat := Erase.defaultFuel)
    (validateFuel : Nat := Erase.defaultFuel) :
    Except CertErr
      (CertifiedSharedExpr ectx ictx sc T sa mask eraseFuel source) :=
  match he : Erase.eraseExpr (eraseCtxOf ectx) eraseFuel T mask source with
  | .error err => .error (.erase err)
  | .ok target =>
    match validateExpr ectx.inlineSharing ictx cover sc
        (inlineTables T).refs (inlineTables T).selfMuts sa mask validateFuel
        (Ixon.Sharing.inlineExpr T.sharing source) target with
    | .error msg => .error (.relation msg)
    | .ok related => .ok ⟨target, he, related.down⟩

/-- Closed-frame specialization of `certifySharedExpr`.  Its result indexes
the relation by exactly the normalized frame consumed by the semantic
composition theorem. -/
def certifySharedClosedExpr [scope : MemberScope]
    (ectx : Ixon.Eval.EvalCtx)
    (ictx : IxIR0.Ctx) (cover : CoverOracle ectx.inlineSharing ictx)
    (F : Ixon.Eval.Frame) (source : Ixon.Expr)
    (eraseFuel : Nat := Erase.defaultFuel)
    (validateFuel : Nat := Erase.defaultFuel) :
    Except CertErr (CertifiedSharedExpr ectx ictx none (tablesOfFrame F)
      F.selfAddr [] eraseFuel source) :=
  certifySharedExpr ectx ictx cover none (tablesOfFrame F) F.selfAddr []
    source eraseFuel validateFuel

/-- A successful closed sharing-aware expression certificate plugs directly
into the composed semantic theorem.  The conclusion refers to the certificate's
exact executable target, not a separately reconstructed expression. -/
theorem CertifiedSharedExpr.simulatesClosed
    {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {F : Ixon.Eval.Frame} {source : Ixon.Expr} {eraseFuel fuel : Nat}
    {value : Ixon.Eval.Value}
    (cert : CertifiedSharedExpr ectx ictx none (tablesOfFrame F)
      F.selfAddr [] eraseFuel source)
    (hstrict : ectx.Strict)
    (hctx : ectx.SharingWF) (hF : F.SharingWF)
    (horacles : OracleRel ectx.inlineSharing ictx)
    (hsource : Ixon.Sharing.sharesBelow F.sharing.size source = true)
    (heval : Ixon.Eval.eval ectx fuel F [] source = .ok value) :
    ∃ fuel' targetValue,
      IxIR0.eval ictx fuel' [] cert.target = .ok targetValue ∧
      InlinedValRel ectx ictx value targetValue := by
  apply erasure_sim_inlineSharing_closed hstrict hctx hF horacles hsource heval
  have hrelated := cert.related
  rw [inlineTables_tablesOfFrame] at hrelated
  exact hrelated

/-! Small boundary guards: the validator accepts kept and ghost applications
that `PErase` covers, while rejecting a successful erasure which reads a
dropped slot (the exact obligation reserved for usage-checker soundness). -/

private def emptyEctx : Ixon.Eval.EvalCtx :=
  { resolve := fun _ => none }

private def openEctx : Ixon.Eval.EvalCtx :=
  { emptyEctx with preserveNeutralElims := true }

private def stringOpenEctx : Ixon.Eval.EvalCtx :=
  { emptyEctx with
      stringLiteral := some
        { charType := Address.replicate 0xE0
          charOfNat := Address.replicate 0xE1
          stringOfList := Address.replicate 0xE2
          listNil := Address.replicate 0xE3
          listCons := Address.replicate 0xE4 } }

private def emptyIctx : IxIR0.Ctx :=
  { env := fun _ => none }

private def noCover : CoverOracle emptyEctx emptyIctx := fun _ => none

private def noInlineCover : CoverOracle emptyEctx.inlineSharing emptyIctx :=
  fun _ => none

-- Whole-program certification seals the strict runtime boundary used by the
-- constructor-only projection simulation theorem.
#guard (match certifyProgram openEctx [] [] 100 100 with
  | .error (.relation
      "certified erasure requires strict neutral-elimination mode") => true
  | _ => false)

#guard (match certifyProgram stringOpenEctx [] [] 100 100 with
  | .error (.relation
      "certified erasure requires String-literal expansion disabled") => true
  | _ => false)

private def certifies (e : Ixon.Expr) : Bool :=
  match certifyExpr emptyEctx emptyIctx noCover none {} none [] e 100 100 with
  | .ok _ => true
  | .error _ => false

#guard certifies (.app (.lam .many (.var 99) (.var 0)) (.sort 0))
#guard certifies (.app (.lam .erased (.sort 0) (.sort 0)) (.share 99))
#guard !certifies (.lam .erased (.var 99) (.var 0))

-- The ordinary relation still has no `.share` constructor.  The sharing-aware
-- certificate runs the original eraser, inlines semantically, and validates
-- both paths against the same emitted expression.
private def oneShareTables : Erase.ETables :=
  { sharing := #[.sort 0] }

#guard (match certifySharedExpr emptyEctx emptyIctx noInlineCover none
    oneShareTables none [] (.share 0) 100 100 with
  | .ok cert => cert.target == .erased
  | .error _ => false)

private def sharedAddress : Address := Address.replicate 0xE1

private def sharedConstant : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .share 0, value := .share 0 }
    sharing := #[.sort 0], refs := #[], univs := #[] }

private def sharedEctx : Ixon.Eval.EvalCtx :=
  { resolve := fun address =>
      if address == sharedAddress then some sharedConstant else none }

-- Both authoritative roots use the entry, so this is decoder-level layer 1,
-- not merely a raw table accepted by the expression fixture above.
#guard sharedConstant.sharingWF

#guard (match certifySharedProgram sharedEctx
    [(sharedAddress, sharedConstant)] [sharedAddress] 100 100 with
  | .ok cert =>
    cert.target == [(sharedAddress, .defn .shared .erased)] &&
      cert.coverage.length == 1
  | .error _ => false)

end Ix.Compiler.EraseValidator
