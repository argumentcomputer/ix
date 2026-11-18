import Tests.Ix.IxVM.Harness
import Ix.IxVM.Model
import Ix.IxVM.PwHints
import Ix.IxVM.Consistency.StatementRel
import IxC.Kernel.Inductives.TwinInstall

/-! # A second recursor record of a family, against the first, at the compiled records

`ixvm-twin-pair` compiles the family of `Lean.Compiler.LCNF.Alt` twice through the certified
compile: as Lean has it, and with the `autoParam`s of the constructors' fields kept at the
recursors' minor premises and rules (the second record that the suite `ixvm-family-graph-records`
builds, `IX_FAMILY_TWIN`). The block record is the same, the recursor family records differ.

For each choice of the record that is stored first (the canonical one), it evaluates, at the
compiled keys, the second record's members against the canonical ones:

* the environment is IxC's own over the canonical variant's records with their model advice
  (`IxVM.PwHints.KernelEnv.ofView`: IxC's reader and phase A of its fold);
* the second record's members are the statement's reading (`IxVM.Consistency.RecReads`) of the
  projection records of its recursors, at the keys of their addresses;
* member `i` of the second record is compared with member `i` of the canonical record: the front
  door, the stored canonical recursor, the counts and level parameters, the model companion, the
  major premise's domain, and the two comparisons of a member (the canonical type and rules above
  the second record's, or the second record's above the canonical ones, each by `wrapRelOk`);
* IxC's executable twin check (`NativeTwin.check`) is run on the pair.

With `IX_TWIN_PAIR_OUT` set to a directory, for the first orientation it also writes a Lean module
with the second record's members and the part of the environment the check reads, for a
kernel-checked instance of the check. -/

namespace Tests.Ix.IxVM.TwinPairRecords

open IxVM.ClaimHarness Tests.Ix.IxVM

abbrev KE := Ix.Kernel.Expr .anon
abbrev KK := Ix.Kernel.Key .anon
abbrev KL := Ix.Kernel.Level
abbrev CI := Ix.Kernel.ConstantInfo .anon

/-! ## The second record: the recursors with the `autoParam`s kept (as the family-graph suite) -/

private def ctorAutoParams (cv : Lean.ConstructorVal) :
    Array (Option (Lean.Level × Lean.Expr)) := Id.run do
  let mut ty := cv.type
  for _ in [0:cv.numParams] do
    if let .forallE _ _ b _ := ty then ty := b
  let mut out : Array (Option (Lean.Level × Lean.Expr)) := #[]
  for _ in [0:cv.numFields] do
    match ty with
    | .forallE _ d b _ =>
      let entry : Option (Lean.Level × Lean.Expr) :=
        if d.isAppOfArity ``autoParam 2 then
          match d.getAppFn with
          | .const _ [l] =>
            if d.appArg!.hasLooseBVars || l.hasParam then none else some (l, d.appArg!)
          | _ => none
        else none
      out := out.push entry
      ty := b
    | _ => out := out.push none
  return out

private def wrapDom (aps : Array (Option (Lean.Level × Lean.Expr))) (j : Nat)
    (d : Lean.Expr) : Lean.Expr :=
  match aps[j]? with
  | some (some (l, tac)) => Lean.mkApp2 (Lean.mkConst ``autoParam [l]) d tac
  | _ => d

private partial def wrapTele (aps : Array (Option (Lean.Level × Lean.Expr))) :
    Nat → Lean.Expr → Lean.Expr
  | j, .forallE n d b bi =>
    if j < aps.size then .forallE n (wrapDom aps j d) (wrapTele aps (j + 1) b) bi
    else .forallE n d b bi
  | j, .lam n d b bi =>
    if j < aps.size then .lam n (wrapDom aps j d) (wrapTele aps (j + 1) b) bi
    else .lam n d b bi
  | _, e => e

private partial def resultCtor : Lean.Expr → Option Lean.Name
  | .forallE _ _ b _ => resultCtor b
  | e => e.getAppArgs.back?.bind fun major => major.getAppFn.constName?

private def wrapMinor (leanEnv : Lean.Environment) (d : Lean.Expr) : Lean.Expr :=
  match (resultCtor d).bind leanEnv.find? with
  | some (.ctorInfo cv) => wrapTele (ctorAutoParams cv) 0 d
  | _ => d

private partial def wrapTypeGo (leanEnv : Lean.Environment) (lo hi : Nat) :
    Nat → Lean.Expr → Lean.Expr
  | i, .forallE n d b bi =>
    .forallE n (if lo ≤ i && i < hi then wrapMinor leanEnv d else d)
      (wrapTypeGo leanEnv lo hi (i + 1) b) bi
  | _, e => e

private partial def wrapRuleGo (leanEnv : Lean.Environment) (lo hi : Nat)
    (aps : Array (Option (Lean.Level × Lean.Expr))) : Nat → Lean.Expr → Lean.Expr
  | i, .lam n d b bi =>
    if i < hi then
      .lam n (if lo ≤ i then wrapMinor leanEnv d else d) (wrapRuleGo leanEnv lo hi aps (i + 1) b) bi
    else wrapTele aps 0 (.lam n d b bi)
  | _, e => e

private def wrapRecursor (leanEnv : Lean.Environment) (rv : Lean.RecursorVal) :
    Lean.RecursorVal :=
  let lo := rv.numParams + rv.numMotives
  let hi := lo + rv.numMinors
  { rv with
    type := wrapTypeGo leanEnv lo hi 0 rv.type
    rules := rv.rules.map fun r =>
      let aps := match leanEnv.find? r.ctor with
        | some (.ctorInfo cv) => ctorAutoParams cv
        | _ => #[]
      { r with rhs := wrapRuleGo leanEnv lo hi aps 0 r.rhs } }

private def compileWith (leanEnv : Lean.Environment) (names : Array Lean.Name)
    (edit : Lean.Name × Lean.ConstantInfo → Lean.Name × Lean.ConstantInfo) : IO Ixon.Env := do
  let roots := withModeledRecursors
    ((names ++ synthesizedPrimNames ++ roleNames).filter leanEnv.constants.contains) leanEnv
  let constants := (collectCertifiedClosure roots leanEnv).map edit
  match ← Ix.CompileM.compileCertified leanEnv constants 32 with
  | .error e => throw (IO.userError s!"the certified compile failed: {e}")
  | .ok out =>
    unless out.failures.isEmpty do
      let fMap := out.failures.toMap
      throw (IO.userError s!"the certified compile: {fMap.size} constants failed: \
        {Ix.CompileM.recordedFailures fMap}")
    IO.ofExcept (withDefaultRoleBinding out.env)

/-- The environment with its model advice, the block of `first` and its recursor family record. -/
private def familyOf (env0 : Ixon.Env) (first : Lean.Name) : IO (Ixon.Env × Address × Address) := do
  let (env, rep) ← IO.ofExcept (IxVM.Model.generateReport
    { env0 with models := {}, modelRecords := {}, modelHints := {}, modelBlobs := {},
                modelDeps := {}, modelsAttached := false })
  let ty ← lookupAddr env first
  let some block := (env.getConst? ty).bind IxVM.Model.projectionBlock?
    | throw (IO.userError s!"{first} is not a member of a block")
  let some (_, adv) := rep.advice.find? (·.1 == block)
    | throw (IO.userError s!"the block of {first} has no model advice")
  return (env, block, adv.layout.recBlock)

/-! ## The statement's reading of a recursor projection record -/

abbrev Store := Address → Option Ixon.Constant

private def rd {α : Type} (x : Ix.Kernel.Reader.ReadM α) : Except String α :=
  match x with
  | .ok a => .ok a
  | .error e => .error (toString e)

open IxVM.Consistency in
private def indKeyAt (t : Ix.Kernel.RoleTable) (store : Store) (k : KK) :
    Except String (Address × Nat × Ixon.Inductive) := do
  let a ← match k with
    | .id a => pure a
    | .role r => match t.addressOf? r with
      | some a => pure a
      | none => throw "a role key with no bound address"
    | .aux .. => throw "a derived key heads a recursor's family"
  unless keyOf t a == k do throw "keyOf"
  let some c := store a | throw "no projection record of the family's type"
  let .iPrj p := c.info | throw "the family's key is not an inductive projection"
  let some cb := store p.block | throw "no block"
  let .muts ms := cb.info | throw "not a block"
  let some (.indc ind) := ms[p.idx.toNat]? | throw "not an inductive member"
  unless Ixon.serConstant c == Ixon.serConstant (memberProjection p.block p.idx.toNat (.indc ind)) &&
      a == memberAddr p.block p.idx.toNat (.indc ind) do
    throw "the projection record is not the member's"
  pure (p.block, p.idx.toNat, ind)

open IxVM.Consistency in
/-- `RecReads`, computed. -/
private def recReadsFn (t : Ix.Kernel.RoleTable) (store : Store) (blob : Address → Option ByteArray)
    (src : Ixon.Constant) (self : Nat → Option (Ix.Kernel.Reader.ReadM KK)) (name : KK)
    (rc : Ixon.Recursor) : Except String CI := do
  let tyP ← rd ((exprReader t blob src id self).read rc.typ)
  let some kF := familyKey rc tyP | throw "familyKey"
  let (_, _, ind) ← indKeyAt t store kF
  let some kM := majorKey rc tyP | throw "majorKey"
  let (Bm, im, indM) ← indKeyAt t store kM
  let ps := Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
    (List.range ind.lvls.toNat)
  let mr := exprReader t blob src (Ix.Kernel.Reader.recParam ps) self
  let ty ← rd (mr.read rc.typ)
  unless rc.rules.size == indM.ctors.size do throw "rule count"
  let rules ← rc.rules.toList.zipIdx.mapM fun (ru, k) => do
    let rhs ← rd (mr.read ru.rhs)
    pure (Ix.Kernel.RecRule.mk (keyOf t (ctorAddr Bm im k)) ru.fields.toNat 0 .inert rhs
      false false false)
  pure (.recInfo ⟨name, ps, ty⟩
    (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
    (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules)

open IxVM.Consistency in
/-- The reading of the recursor projection record at `a`. -/
private def readRecMember (t : Ix.Kernel.RoleTable) (store : Store)
    (blob : Address → Option ByteArray) (a : Address) : Except String CI := do
  let some c := store a | throw "no record at the constant address"
  let .rPrj p := c.info | throw "not a recursor projection record"
  let some cb := store p.block | throw "no block"
  let .muts ms := cb.info | throw "not a block"
  let some (.recr rc) := ms[p.idx.toNat]? | throw "not a recursor member"
  unless Ixon.serConstant c == Ixon.serConstant (memberProjection p.block p.idx.toNat (.recr rc))
      && a == memberAddr p.block p.idx.toNat (.recr rc) do throw "MemberAt"
  recReadsFn t store blob cb (blockSelf t p.block ms) (keyOf t a) rc

/-- The constant addresses of the members of the recursor family record at `rb`. -/
private def memberAddrs (store : Store) (rb : Address) : List Address :=
  match store rb with
  | some c => match c.info with
    | .muts ms => ms.toList.zipIdx.map fun (m, i) => IxVM.Consistency.memberAddr rb i m
    | _ => []
  | none => []

/-! ## One variant -/

structure Variant where
  label : String
  ixon : Ixon.Env
  rb : Address
  table : Ix.Kernel.RoleTable
  store : Store
  blob : Address → Option ByteArray

private def variantOf (label : String) (E : Ixon.Env) (rb : Address) : IO Variant := do
  let some b := E.roleBinding | throw (IO.userError s!"{label}: no role binding")
  let some t := Ix.Kernel.RoleTable.ofBytes b.bytes | throw (IO.userError s!"{label}: the table does not decode")
  let blobs := E.blobs
  return { label, ixon := E, rb, table := t, store := IxVM.Consistency.recordOf E,
           blob := fun a => blobs[a]? }

/-- IxC's own environment over the variant's records and its model advice. -/
private def kernelEnvOf (v : Variant) : Except String IxVM.PwHints.KernelEnv := do
  let E := v.ixon
  let mut records : Array (Address × Ixon.Constant) := #[]
  for (a, lc) in E.consts do
    if let some c := lc.get? then records := records.push (a, c)
  let mut models : Std.HashSet Address := {}
  for (a, c) in E.modelRecords do
    records := records.push (a, c)
    models := models.insert a
  let mut blobs := E.blobs
  for (a, b) in E.modelBlobs do
    unless blobs.contains a do blobs := blobs.insert a b
  let mut hints := E.anonHints
  for (a, h) in E.modelHints do
    unless hints.contains a do hints := hints.insert a h
  let view : IxVM.PwHints.View :=
    { records := records.qsort (fun x y => x.1.cmpBytes y.1 == .lt), blobs, hints,
      table := E.roleBinding.map (·.bytes), models }
  IxVM.PwHints.KernelEnv.ofView view

/-! ## A member against its canonical member -/

private def okOf {α : Type} (x : Ix.Kernel.CheckM .anon α) : Bool :=
  match x with
  | .ok _ => true
  | .error _ => false

private def errOf {α : Type} (x : Ix.Kernel.CheckM .anon α) : String :=
  match x with
  | .ok _ => ""
  | .error e => String.ofList (((toString e).replace "\n" " ").toList.take 200)

private def majorDom (mI : Nat) (ty : KE) : Option KE :=
  match ty.stripPis mI with
  | some (_, .forallE d _ _) => some d
  | _ => none

private def isBVar : KE → Bool
  | .bvar _ => true
  | _ => false

/-- One member's evaluation. -/
structure MemberEval where
  key : String
  front : Bool := false
  letFree : Bool := false
  canonical : Bool := false
  counts : Bool := false
  lvls : Bool := false
  model : Bool := false
  major : Bool := false
  majorAgrees : Bool := false
  tyEqual : Bool := false
  tyCanonAbove : Bool := false
  tyTwinAbove : Bool := false
  tyTwinTyped : Bool := false
  rules : Nat := 0
  rulesStaged : Bool := false
  rulesEqual : Nat := 0
  rulesCanonAbove : Nat := 0
  rulesTwinAbove : Nat := 0
  rulesTwinTyped : Nat := 0
  note : String := ""

def MemberEval.branch (m : MemberEval) : String :=
  let canon := m.tyCanonAbove && m.rulesCanonAbove == m.rules
  let twin := m.tyTwinAbove && m.rulesTwinAbove == m.rules
  if canon && twin then "both (equal up to WrapRel)"
  else if canon then "CanonAbove"
  else if twin then "TwinAbove"
  else "neither"

def MemberEval.render (m : MemberEval) : String :=
  s!"{m.key}: branch {m.branch}; front {m.front}, letFree {m.letFree}, canonical stored \
    {m.canonical}, counts {m.counts}, level parameters {m.lvls}, model companion {m.model}, \
    major (TwinMemberCmp.major) {m.major}, major domains agree {m.majorAgrees}; type: equal \
    {m.tyEqual}, canonical above {m.tyCanonAbove}, twin above {m.tyTwinAbove} (twin's checked \
    type inferred {m.tyTwinTyped}); rules {m.rules}, staged {m.rulesStaged}: equal \
    {m.rulesEqual}, canonical above {m.rulesCanonAbove}, twin above {m.rulesTwinAbove} \
    (generated typed {m.rulesTwinTyped}){if m.note.isEmpty then "" else "; " ++ m.note}"

/-- Each member of `blk` (the second record, read) against member `i` of the canonical record at
`canonKeys`, in `env`. -/
private def evalMembers (fuel : Nat) (env : Ix.Kernel.Env .anon) (blk : List CI)
    (canonKeys : List KK) : List MemberEval × Option (List (Ix.Kernel.NativeTwin.Part .anon)) :=
  Id.run do
  let ops : Ix.Kernel.CheckerOps .anon (Ix.Kernel.CheckM .anon) := Ix.Kernel.fueledOps .verified fuel
  let mut evals : Array MemberEval := #[]
  let mut parts : Array (Ix.Kernel.NativeTwin.Part .anon) := #[]
  let mut complete := true
  unless blk.all (fun ci => match ci with | .recInfo .. => true | _ => false) do
    return ([{ key := "block", note := "a member is no recursor" }], none)
  for (ci, kC) in blk.zip canonKeys do
    let .recInfo cvW mI rP rulesW := ci
      | continue
    let mut m : MemberEval := { key := toString cvW.name, rules := rulesW.length }
    match Ix.Kernel.checkConstantVal ops env cvW with
    | .error e =>
      evals := evals.push { m with note := s!"front door: {((toString e).replace "\n" " ").take 200}" }
      complete := false
    | .ok cvW' =>
      m := { m with front := true, letFree := Ix.Kernel.Semantics.letFree cvW'.type }
      match env.find? kC with
      | some (.recInfo cvC mIC rPC rulesC) =>
        let model? := match env.find? (Ix.Kernel.auxKey kC .model) with
          | some (.defnInfo cv value hint) => some (cv, value, hint)
          | _ => none
        let major := match majorDom mI cvW'.type, majorDom mI cvC.type with
          | some DW, some DC => decide (DW.getAppFn = DC.getAppFn) &&
              (!(DC.getAppArgs.all isBVar) || decide (DW.getAppArgs = DC.getAppArgs))
          | _, _ => false
        m := { m with canonical := true,
          counts := mI == mIC && rP == rPC && rulesW.length == rulesC.length,
          lvls := cvW.levelParams == cvC.levelParams, model := model?.isSome, major,
          majorAgrees := Ix.Kernel.NativeTwin.majorAgrees mI cvC.type cvW'.type,
          tyEqual := decide (cvC.type = cvW'.type),
          tyCanonAbove := Ix.Kernel.Semantics.wrapRelOk env.find? cvC.type cvW'.type,
          tyTwinAbove := Ix.Kernel.Semantics.wrapRelOk env.find? cvW'.type cvC.type,
          tyTwinTyped := okOf (Ix.Kernel.inferTypeCore .verified env fuel 0 cvW'.type) }
        evals := evals.push m
        parts := parts.push {
          raw := cvW, annotated := cvW', canonical := cvC, canonicalKey := kC,
          majorIndex := mI, rulePrefix := rP, rawRules := rulesW, canonicalRules := rulesC,
          model? := model? }
      | _ =>
        evals := evals.push { m with note := "no canonical recursor at its key" }
        complete := false
  unless complete do return (evals.toList, none)
  -- the rules' stages, then the two comparisons of each rule
  let partsL := parts.toList
  match Ix.Kernel.NativeTwin.checkPartsRules ops env (Ix.Kernel.NativeTwin.selfEnv env partsL) partsL with
  | .error e =>
    let note := s!"rules' stages: {((toString e).replace "\n" " ").take 200}"
    return (evals.toList.map fun m => { m with note := note }, none)
  | .ok checked =>
    let f := Ix.Kernel.NativeTwin.peerRename checked
    let back : KK → KK := fun k =>
      match checked.find? (fun p => p.raw.name == k) with
      | some p => p.canonicalKey
      | none => k
    let out := (evals.toList.zip checked).map fun (m, p) => Id.run do
      let mut m := { m with rulesStaged := true }
      for (rW', rC) in p.checkedRules.zip p.canonicalRules do
        let g := rW'.rhs.renameConsts back
        let typed := okOf (Ix.Kernel.inferTypeCore .verified env fuel 0 g)
        let twinAbove := Ix.Kernel.Semantics.wrapRelOk env.find? g rC.rhs &&
          Ix.Kernel.Semantics.wrapRelOk env.find? (g.renameConsts f) rW'.rhs &&
          (decide (g = rC.rhs) || typed)
        m := { m with
          rulesEqual := m.rulesEqual + (if decide (rC.rhs.renameConsts f = rW'.rhs) then 1 else 0),
          rulesCanonAbove := m.rulesCanonAbove +
            (if Ix.Kernel.Semantics.wrapRelOk env.find? (rC.rhs.renameConsts f) rW'.rhs then 1 else 0),
          rulesTwinAbove := m.rulesTwinAbove + (if twinAbove then 1 else 0),
          rulesTwinTyped := m.rulesTwinTyped + (if typed then 1 else 0) }
      return m
    return (out, some checked)

/-! ## The part of the environment the check reads -/

private partial def exprKeys (acc : Array KK) : KE → Array KK
  | .const k _ => if acc.contains k then acc else acc.push k
  | .app f a => exprKeys (exprKeys acc f) a
  | .lam t b _ => exprKeys (exprKeys acc t) b
  | .forallE t b _ => exprKeys (exprKeys acc t) b
  | .proj s _ e => exprKeys (if acc.contains s then acc else acc.push s) e
  | .fvar _ t => exprKeys acc t
  | .letE t v b _ => exprKeys (exprKeys (exprKeys acc t) v) b
  | _ => acc

/-- A definition whose value is `λ x₁ … xₖ, x₁`: the shape of a type-annotation wrapper. -/
private def wrapperLike : CI → Bool
  | .defnInfo _ v _ =>
    let rec go (n : Nat) : KE → Bool
      | .lam _ b _ => go (n + 1) b
      | .bvar i => n != 0 && i + 1 == n
      | _ => false
    go 0 v
  | _ => false

/-- The keys a constant's type mentions, and its value where `values` asks (definitions only),
and an inductive's η constructor; a recursor's rules where `rules` asks. -/
private def ciRefs (values rules : Bool) (c : CI) : Array KK :=
  let acc := exprKeys #[] c.toConstantVal.type
  match c with
  | .defnInfo _ v _ => if values || wrapperLike c then exprKeys acc v else acc
  | .indInfo _ caps => match caps.etaCtor with
    | some k => if acc.contains k then acc else acc.push k
    | none => acc
  | .recInfo _ _ _ rs =>
    if rules then rs.foldl (fun acc r => exprKeys (if acc.contains r.ctor then acc else acc.push r.ctor) r.rhs) acc
    else acc
  | _ => acc

/-- The keys reachable from `seed` through `ciRefs`. -/
private def closeKeys (env : Ix.Kernel.Env .anon) (values : Bool) (seed : Array KK) :
    Std.HashSet KK := Id.run do
  let mut seen : Std.HashSet KK := {}
  let mut work := seed
  let mut steps := 0
  while !work.isEmpty && steps < 1000000 do
    steps := steps + 1
    let k := work.back!
    work := work.pop
    if seen.contains k then continue
    seen := seen.insert k
    match k with
    | .aux b _ => unless seen.contains b do work := work.push b
    | _ => pure ()
    if let some c := env.find? k then
      for k' in ciRefs values false c do
        unless seen.contains k' do work := work.push k'
  return seen

/-- The environment `env` restricted to `keys`, in its order. -/
private def restrict (env : Ix.Kernel.Env .anon) (keys : Std.HashSet KK) : Ix.Kernel.Env .anon :=
  ⟨env.consts.filter fun c => keys.contains c.name⟩

/-! ## Printing a fixture (the printers of the family fixtures' generator) -/

private def ppLevel : KL → String
  | .zero => "lz"
  | .succ u => s!"(ls {ppLevel u})"
  | .max a b => s!"(lmx {ppLevel a} {ppLevel b})"
  | .imax a b => s!"(lim {ppLevel a} {ppLevel b})"
  | .param p => s!"(lp {p})"

private def ppPw (pw : Ix.Kernel.PropWhen) : String :=
  match pw.toList? with
  | none => "pN"
  | some ps => s!"(pZ {ps})"

private structure Keys where
  idx : Std.HashMap KK Nat := {}
  list : Array KK := #[]

private def Keys.add (ks : Keys) (k : KK) : Keys :=
  if ks.idx.contains k then ks else { idx := ks.idx.insert k ks.list.size, list := ks.list.push k }

private partial def Keys.addDeep (ks : Keys) (k : KK) : Keys :=
  if ks.idx.contains k then ks else
  match k with
  | .aux b _ => (ks.addDeep b).add k
  | _ => ks.add k

private def kn (ks : Keys) (k : KK) : String := s!"k{(ks.idx[k]?).getD 999999}"

private partial def ppExpr (ks : Keys) : KE → String
  | .bvar i => s!"(bv {i})"
  | .fvar .. => "FVAR"
  | .sort u => s!"(st {ppLevel u})"
  | .const k us => s!"(cn {kn ks k} [{", ".intercalate (us.map ppLevel)}])"
  | .app f a => s!"(ap {ppExpr ks f} {ppExpr ks a})"
  | .lam t b m => s!"(lm {ppPw m.pw} {ppExpr ks t} {ppExpr ks b})"
  | .forallE t b m => s!"(pi {ppPw m.pw} {ppExpr ks t} {ppExpr ks b})"
  | .letE .. => "LETE"
  | .lit (.natVal n) => s!"(Expr.lit (.natVal {n}))"
  | .lit (.strVal s) => s!"(Expr.lit (.strVal {repr s}))"
  | .proj s i e => s!"(Expr.proj {kn ks s} {i} {ppExpr ks e})"

private partial def allKeys (ks : Keys) : KE → Keys
  | .const k _ => ks.addDeep k
  | .app f a => allKeys (allKeys ks f) a
  | .lam t b _ => allKeys (allKeys ks t) b
  | .forallE t b _ => allKeys (allKeys ks t) b
  | .proj s _ e => allKeys (ks.addDeep s) e
  | .fvar _ t => allKeys ks t
  | .letE t v b _ => allKeys (allKeys (allKeys ks t) v) b
  | _ => ks

private def ciAllKeys (ks : Keys) (c : CI) : Keys :=
  let ks := allKeys (ks.addDeep c.name) c.toConstantVal.type
  match c with
  | .defnInfo _ v _ => allKeys ks v
  | .thmInfo _ v => allKeys ks v
  | .indInfo _ caps => (caps.etaCtor.map ks.addDeep).getD ks
  | .recInfo _ _ _ rules => rules.foldl (fun ks r =>
      let ks := allKeys (ks.addDeep r.ctor) r.rhs
      match r.fire with
      | .nested _ pins => pins.foldl allKeys ks
      | _ => ks) ks
  | _ => ks

private def ppDerived (d : Ix.Kernel.Derived) : String := toString (reprPrec d 1024)

private def ppKeyDef (ks : Keys) (k : KK) : String :=
  let body := match k with
    | .role r => s!"Key.role {toString (reprPrec r 1024)}"
    | .id a => s!"Key.id (adr {a.hash.data.toList})"
    | .aux b d => s!"Key.aux {kn ks b} {ppDerived d}"
  s!"def {kn ks k} : KKey := {body}"

private def ppCV (ks : Keys) (c : Ix.Kernel.ConstantVal .anon) : String :=
  s!"(cv {kn ks c.name} {c.levelParams} {ppExpr ks c.type})"

private def ppHint : Ix.Kernel.ReducibilityHint → String
  | .opaque => "ReducibilityHint.opaque"
  | .abbrev => "ReducibilityHint.abbrev"
  | .regular n => s!"(ReducibilityHint.regular {n})"

private def ppFire (ks : Keys) : Ix.Kernel.RecRuleFire .anon → String
  | .inert => "RecRuleFire.inert"
  | .plain => "RecRuleFire.plain"
  | .nested lvls pins =>
    s!"(RecRuleFire.nested [{", ".intercalate (lvls.map ppLevel)}] [{", ".intercalate (pins.map (ppExpr ks))}])"

private def ppRule (ks : Keys) (r : Ix.Kernel.RecRule .anon) : String :=
  s!"(RecRule.mk {kn ks r.ctor} {r.nfields} {r.ctorParams} {ppFire ks r.fire} {ppExpr ks r.rhs} {r.k} {r.eta} {r.paramsBlind})"

private def ppCaps (ks : Keys) (c : Ix.Kernel.IndCaps .anon) : String :=
  let ec := match c.etaCtor with
    | some k => s!"(some {kn ks k})"
    | none => "none"
  "{ eta := " ++ toString c.eta ++ ", etaCtor := " ++ ec ++ ", etaParams := " ++
    toString c.etaParams ++ ", etaFields := " ++ toString c.etaFields ++ ", unitlike := " ++
    toString c.unitlike ++ ", unitParams := " ++ toString c.unitParams ++ ", ruleK := " ++
    toString c.ruleK ++ ", sortZ := " ++ ppPw c.sortZ ++ " }"

private def ppCI (ks : Keys) : CI → Option String
  | .axiomInfo c => some s!"ConstantInfo.axiomInfo {ppCV ks c}"
  | .defnInfo c v h => some s!"ConstantInfo.defnInfo {ppCV ks c} {ppExpr ks v} {ppHint h}"
  | .thmInfo c v => some s!"ConstantInfo.thmInfo {ppCV ks c} {ppExpr ks v}"
  | .indInfo c caps => some s!"ConstantInfo.indInfo {ppCV ks c} {ppCaps ks caps}"
  | .ctorInfo c nP nF => some s!"ConstantInfo.ctorInfo {ppCV ks c} {nP} {nF}"
  | .recInfo c mI rP rules =>
    some s!"ConstantInfo.recInfo {ppCV ks c} {mI} {rP} [{", ".intercalate (rules.map (ppRule ks))}]"
  | .projInfo _ => none

private def ppList (ks : Keys) (name pfx : String) (cs : List CI) : String × Bool := Id.run do
  let mut out := ""
  let mut names : List String := []
  let mut ok := true
  for (c, i) in cs.zipIdx do
    match ppCI ks c with
    | some s =>
      out := out ++ s!"def {pfx}{i} : ConstantInfo .anon :=\n  {s}\n\n"
      names := names ++ [s!"{pfx}{i}"]
    | none => ok := false
  return (out ++ s!"def {name} : List (ConstantInfo .anon) :=\n  [{", ".intercalate names}]\n", ok)

private def fixtureModule (fuel : Nat) (env : Ix.Kernel.Env .anon) (blk : List CI)
    (summary : String) : String × Bool := Id.run do
  let mut ks : Keys := {}
  for c in env.consts do ks := ciAllKeys ks c
  for c in blk do ks := ciAllKeys ks c
  let keyDefs := "\n".intercalate (ks.list.toList.map (ppKeyDef ks))
  let (envS, ok1) := ppList ks "env" "e" env.consts
  let (blkS, ok2) := ppList ks "blk" "b" blk
  let body := "import IxVMRefinement.TwinFamily.CheckInstance\n" ++
    "import IxVMRefinement.FamilyAlias.Fixtures.Terms\n\n" ++
    "/-! # A second recursor record of `Lean.Compiler.LCNF.Alt`'s family, at its compiled keys\n\n" ++
    summary ++ " -/\n\n" ++
    "namespace IxVM.Refinement.Typing.TwinFamily.Fixtures.LcnfAltPair\n\n" ++
    "open IxVM.Refinement.Core\n" ++
    "open IxVM.Refinement.Decl.FamilyAlias.Fixtures\n" ++
    "open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule RecRuleFire ReducibilityHint)\n\n" ++
    "set_option maxRecDepth 100000\n\n" ++
    keyDefs ++ "\n\n" ++ envS ++ "\n" ++ blkS ++ "\n" ++
    "set_option maxHeartbeats 0 in\n" ++
    "/-- **IxC's twin check accepts the second record against the stored canonical one, and after\n" ++
    "it each member is stored as a constant that stores it, with a model companion** (evaluated). -/\n" ++
    s!"theorem check_ok : twinStepCheck {fuel} ⟨env⟩ blk = true := by\n  decide +kernel\n\n" ++
    "/-- **The twin step's record at this pair**: IxC's twin record at the positional package, each\n" ++
    "member stored after the step as a constant that stores its reading, and a model companion at each\n" ++
    "member. -/\n" ++
    "theorem inhabited :\n" ++
    "    ∃ env₂, Ix.Kernel.Semantics.DeclRecTwinRunJ IxVM.Refinement.Decl.twinPosRulesJ ⟨env⟩ blk env₂ ∧\n" ++
    "      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ IxVM.Consistency.StoredAs c ci) ∧\n" ++
    "      (∀ ci ∈ blk, Ix.Kernel.Model.HasModel env₂ ci.name) :=\n" ++
    "  twinStep_of_check check_ok\n\n" ++
    "end IxVM.Refinement.Typing.TwinFamily.Fixtures.LcnfAltPair\n"
  return (body, ok1 && ok2)

/-! ## The suite -/

private def runOrientation (fuel : Nat) (canon twin : Variant) (out? : Option System.FilePath) :
    IO Bool := do
  let pfx := s!"[ixvm-twin-pair] canonical {canon.label}, second {twin.label}"
  let k ← IO.ofExcept (kernelEnvOf canon)
  let env := k.fe.env
  IO.println s!"{pfx}: IxC's environment: {env.consts.length} constants, {k.installed} \
    declarations installed, {k.failures.size} records refused"
  for (a, why) in k.failures.extract 0 6 do
    IO.println s!"{pfx}:   refused {a}: {(why.replace "\n" " ").take 160}"
  let canonAddrs := memberAddrs canon.store canon.rb
  let twinAddrs := memberAddrs twin.store twin.rb
  let canonKeys := canonAddrs.map (IxVM.Consistency.keyOf canon.table)
  IO.println s!"{pfx}: members {canonAddrs.length} and {twinAddrs.length}; same table \
    {canon.table.toBytes == twin.table.toBytes}"
  let mut blk : List CI := []
  for a in twinAddrs do
    match readRecMember twin.table twin.store twin.blob a with
    | .ok ci => blk := blk ++ [ci]
    | .error e => throw (IO.userError s!"{pfx}: the reading of {a}: {e}")
  let fresh := blk.all fun ci => (env.find? ci.name).isNone
  IO.println s!"{pfx}: the second record read, {blk.length} members, keys fresh in IxC's \
    environment {fresh}"
  let (evals, _) := evalMembers fuel env blk canonKeys
  for m in evals do IO.println s!"{pfx}: member {m.render}"
  let ops : Ix.Kernel.CheckerOps .anon (Ix.Kernel.CheckM .anon) := Ix.Kernel.fueledOps .verified fuel
  let run := Ix.Kernel.NativeTwin.check ops env blk
  IO.println s!"{pfx}: IxC's twin check: {if okOf run then "accepted" else "declined: " ++ errOf run}"
  if let some dir := out? then
    if okOf run then
      -- the part of the environment the check reads
      let mut seed : Array KK := #[]
      for c in blk do
        for k' in ciRefs true true c do
          unless seed.contains k' do seed := seed.push k'
      for k in canonKeys do
        seed := seed.push k
        seed := seed.push (Ix.Kernel.auxKey k .model)
        if let some (.recInfo cvC _ _ rulesC) := env.find? k then
          let ks := rulesC.foldl (fun acc r => exprKeys acc r.rhs) (exprKeys #[] cvC.type)
          for k' in ks do
            if let some c := env.find? k' then
              if wrapperLike c then seed := seed.push k'
      let mut chosen : Option (Ix.Kernel.Env .anon) := none
      for values in [false, true] do
        if chosen.isSome then continue
        let envR := restrict env (closeKeys env values seed)
        let runR := Ix.Kernel.NativeTwin.check ops envR blk
        let verdict := if okOf runR then "accepted" else "declined: " ++ errOf runR
        IO.println s!"{pfx}: restricted environment (definition values {values}): \
          {envR.consts.length} constants; IxC's twin check {verdict}"
        if okOf runR then chosen := some envR
      match chosen with
      | none => IO.println s!"{pfx}: no restricted environment accepted; no fixture written"
      | some envR =>
        let summary :=
          "The family of `Lean.Compiler.LCNF.Alt` compiled twice by the certified compile: with the\n" ++
          "`autoParam`s of its constructors' fields kept at the recursors (the canonical record, stored\n" ++
          "first) and as Lean has it (the second record, `blk`). `blk` is the statement's reading\n" ++
          "(`IxVM.Consistency.RecReads`) of the second record's recursor projection records, at the keys\n" ++
          "of their addresses. `env` is IxC's own environment over the canonical variant's records and\n" ++
          "model advice (its reader and phase A of its fold), restricted to the constants the check\n" ++
          "reads: those the second record names, the canonical recursors with their model companions, the\n" ++
          "wrappers the canonical terms use, and what their types (and definitions' values) name, in the\n" ++
          "environment's order. That these data are what the records store was executed, not proved."
        let (text, ok) := fixtureModule fuel envR blk summary
        let path := dir / "LcnfAltPair.lean"
        IO.FS.writeFile path text
        IO.println s!"{pfx}: wrote {path} ({text.length} characters, all constants printed {ok})"
  return okOf run

/-- The two compiled records of `Lean.Compiler.LCNF.Alt`'s family, each as the canonical one. -/
def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let first : Lean.Name := `Lean.Compiler.LCNF.Alt
  let some (.inductInfo iv) := leanEnv.find? first
    | do IO.eprintln s!"[ixvm-twin-pair] {first} is not an inductive"; return 1
  let recNames : List Lean.Name := iv.all.map Lean.mkRecName ++
    (List.range iv.numNested).map fun i => Lean.Name.mkStr (iv.all.headD first) s!"rec_{i + 1}"
  let names := #[first] ++ recNames.toArray
  let edit : Lean.Name × Lean.ConstantInfo → Lean.Name × Lean.ConstantInfo := fun (n, ci) =>
    match ci with
    | .recInfo rv => if recNames.contains n then (n, .recInfo (wrapRecursor leanEnv rv)) else (n, ci)
    | _ => (n, ci)
  IO.println s!"[ixvm-twin-pair] types {iv.all}, recursors {recNames}"
  let (envL, blockL, rbL) ← familyOf (← compileWith leanEnv names id) first
  let (envK, blockK, rbK) ← familyOf (← compileWith leanEnv names edit) first
  IO.println s!"[ixvm-twin-pair] as Lean has it: block {blockL}, recursor family {rbL}"
  IO.println s!"[ixvm-twin-pair] autoParams kept: block {blockK}, recursor family {rbK}"
  unless blockL == blockK && rbL != rbK do
    IO.eprintln "[ixvm-twin-pair] expected one block and two recursor family records"
    return 1
  let lean ← variantOf "as Lean has it" envL rbL
  let kept ← variantOf "autoParams kept" envK rbK
  let fuel := 1000000
  let out? := (← IO.getEnv "IX_TWIN_PAIR_OUT").map System.FilePath.mk
  let keptCanon ← runOrientation fuel kept lean out?
  let leanCanon ← runOrientation fuel lean kept none
  IO.println s!"[ixvm-twin-pair] IxC's twin check: Lean's record as the second of the kept one \
    {keptCanon}; the kept one as the second of Lean's {leanCanon}"
  return if keptCanon then 0 else 1

end Tests.Ix.IxVM.TwinPairRecords
