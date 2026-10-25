import Ix.Cert.AdmittedTargetFronts
import Ix.Cert.RecursorSupport
import Ix.Cert.DefinitionSnapshots
import Ix.Cert.CandidateValueFront
import Ix.Cert.TheoremSnapshots
import Ix.Cert.ProjectionMembers
import Ix.Ixon.CheckOrder
import Tests.Ix.Compile.Harness.Units
import Tests.Ix.Kernel.Authentication
import Tests.Ix.Kernel.EntryCaseDefs

namespace Tests.Ix.Compile.SelectedAdmission
open _root_.Ix.Kernel _root_.Ix.Kernel.Reader _root_.Ix.Kernel.Admission
open _root_.Ix.Cert

private def need (b : Bool) (msg : String) : IO Unit := unless b do throw (IO.userError msg)
private def limits : Limits := Tests.Ix.Kernel.Reader.limits
private def kind : Ixon.ConstantInfo → String
  | .defn d => reprStr d.kind
  | .muts _ => "mutual"
  | .dPrj _ => "definition-projection"
  | .iPrj _ => "inductive-projection"
  | .cPrj _ => "constructor-projection"
  | .rPrj _ => "recursor-projection"
  | .recr _ => "recursor"
  | .axio _ => "axiom"
  | .quot _ => "quotient"

-- Diagnostic candidate only: literal RecordEdge closure, with no full-store
-- fallback. Missing implicit support is reported, never inserted here.
private def candidate (ixe : Ixon.Env) (t : RoleTable) (pre : Prelude .anon) (root : Address) :
    Except String (List Address × Nat) := do
  let mut seen : Std.HashSet Address := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let a := todo.head!
    todo := todo.tail
    if seen.contains a then continue
    let some c := recordAt ixe a | throw s!"missing record {a}"
    seen := seen.insert a
    let owner := ownerOf a c
    if owner != a then todo := owner :: todo
    for r in c.refs do
      if ixe.consts.contains r then todo := r :: todo
  let records := seen.toArray.filterMap fun a => (recordAt ixe a).map (a, ·)
  let order := Ixon.CheckOrder.wholeEnv t pre records
  unless order.contains root && order.size == seen.size && order.all seen.contains do
    throw "candidate order omitted a literal reached record"
  let all := ixe.consts.toArray.filterMap fun (a, lc) => lc.get?.map (a, ·)
  let cx := streamContext Address.admissionHash t pre all.toList ixe.blobs.toList (hintsOf ixe)
  let extra := Ixon.CheckOrder.mergeEdges (Ixon.CheckOrder.groundEdges cx.roles.names)
    (literalEdges cx.roles.names all)
  let missing := records.foldl (init := ({} : Std.HashSet Address)) fun bad (a, _) =>
    (extra.getD a #[]).foldl (fun bad b =>
      if seen.contains b || pre.records.any (·.1 == b) then bad else bad.insert b) bad
  return (order.toList, missing.size)

-- Inspect the exact preparation after ONE public check; this replay adds no
-- declaration, prefix, per-rewrite or inner-header checker invocation.
private def fronts (binding : Binding) (t : RoleTable) (pre : Prelude .anon)
    (ixe : Ixon.Env) (order : List Address) (root : Address) (envA : Env .anon)
    (receipt? : Option DefinitionSnapshots.Receipt := none)
    (theorems? : Option (IO.Ref (Array String) × String) := none) : IO (Nat × Nat) := do
  let records := recordsOf ixe order
  let blobs := blobsOf ixe order
  let hint := hintsOf ixe
  let constants ← IO.ofExcept ((decodeRecords limits records).mapError reprStr)
  let (_, ds) ← match receipt? with
    | some r => pure (r.ev, r.ds)
    | none => IO.ofExcept ((prepareWith Address.admissionHash binding pre limits records blobs hint).mapError toString)
  let cx := streamContext Address.admissionHash t pre constants blobs hint
  let mut st := pre.state
  let mut decls : Array (Declaration .anon) := #[]
  let mut selected : Array (Nat × Declaration .anon) := #[]
  for ((a, c), j) in constants.zipIdx do
    let r : Read .anon ← IO.ofExcept ((readRecord cx st a c).mapError reprStr)
    if a == root then
      if let .defn d := c.info then
        if d.kind == .defn || (d.kind == .thm && theorems?.isSome) then
          let key ← IO.ofExcept ((cx.memberKey (.member a 0)).mapError reprStr)
          let ty ← IO.ofExcept (((definitionReader cx a c d).read d.typ).mapError reprStr)
          let value ← IO.ofExcept (((definitionReader cx a c d).read d.value).mapError reprStr)
          let cv : _root_.Ix.Kernel.ConstantVal .anon := ⟨key, singletonLps d.lvls, ty⟩
          let rewritten := projRewrite st cv value
          let raw := rewritten.getD value
          if d.kind == .thm then
            let some receipt := receipt? | throw (IO.userError "theorem receipt absent")
            let some (rows, label) := theorems? | throw (IO.userError "theorem census absent")
            if label == "projection-control" then
              let owner := match ty with | .forallE (.const n _) _ _ => some n | _ => none
              IO.println s!"projection diagnostic: kind={repr d.kind} wire={repr d.value} body={repr (Frontend.lamBody value)} reader-owner={(owner.bind st.projOwners.get?).isSome} reader-level={(owner.bind fun n => st.projLevels[Frontend.projIotaName n 0]?).isSome}"
              need ((owner.bind st.projOwners.get?).isSome &&
                (owner.bind fun n => st.projLevels[Frontend.projIotaName n 0]?).isSome) "projection owner/level control is vacuous"
            need (r.decls == #[.thmDecl cv raw]) "theorem wire/projection body changed"
            let some i := ds.findIdx? (· == .thmDecl cv raw) | throw (IO.userError "prepared theorem missing")
            let s ← IO.ofExcept (TheoremSnapshots.snapshot receipt i)
            let some (.thmInfo got storedRaw) := envA.find? cv.name | throw (IO.userError "raw theorem missing")
            need (s.position == i && s.cv == cv && s.raw == raw && storedRaw == raw &&
              got.name == cv.name && got.levelParams == cv.levelParams && s.expected == got.type) "theorem identity/header/raw storage changed"
            need (s.before.consts.length == s.counter && s.view.env.consts == envA.consts &&
              s.before.find? cv.name == none && s.view.find? cv.name == none &&
              s.before.consts.all (fun c => s.view.find? c.name == s.before.find? c.name)) "theorem prefix view changed"
            rows.modify (·.push s!"theorem {label} record={j} prepared={i} counter={s.counter} key={cv.name} levels={cv.levelParams.length} projection={rewritten.isSome}")
          else
            let some (.defnDecl got body h) := (r.decls[0]? : Option (Declaration .anon))
              | throw (IO.userError "standalone read did not emit a definition")
            need (got == cv && body == raw && r.decls == #[.defnDecl cv raw h]) "wire key/levels/projection body changed"
            selected := selected.push (j, .defnDecl cv raw h)
    decls := decls ++ r.decls
    st := st.commit r
  need (Frontend.preparePrelude pre.ix decls == ds) "reader replay differs from the actual preparation"
  let mut moved := 0
  for (j, decl) in selected do
    let some i := ds.findIdx? (· == decl) | throw (IO.userError "prepared declaration missing")
    let .defnDecl cv raw h := decl | throw (IO.userError "wrong front kind")
    let some (.defnInfo got checked storedHint) := envA.find? cv.name | throw (IO.userError "checked definition missing")
    need (got.name == cv.name && got.levelParams == cv.levelParams && storedHint == h) "checked identity/levels/hint changed"
    if let some r := receipt? then
      let s ← IO.ofExcept (r.snapshot i)
      need (s.position == i && s.cv == cv && s.raw == raw && s.hint == h &&
        s.expected == got.type && s.checked == checked) "snapshot changed its declaration/header/body association"
      need (s.before.consts.length == s.counter && s.view.env.consts == envA.consts &&
        s.view.find? cv.name == none && s.before.find? cv.name == none &&
        (s.view.env.find? cv.name).isSome) "snapshot confused final environment with the logical prefix"
      need (s.before.consts.all (fun c => s.view.find? c.name == s.before.find? c.name)) "prefix lookup changed"
      IO.println s!"  snapshot prepared={i} counter={s.counter} key={cv.name}"
    if i != j then moved := moved + 1
    IO.println s!"  front record={j} prepared={i} key={cv.name} levels={cv.levelParams.length}"
  return (selected.size, moved)

private def census (label : String) (out : _root_.Ix.CompileM.LeanPipelineOut)
    (binding : Binding) (t : RoleTable) (pre : Prelude .anon) : IO (Nat × Nat) := do
  let some nodes := out.sourceNodes? | throw (IO.userError "missing original source facts")
  let cs := _root_.Ix.Compile.ChangedSet.ofCompile out.cenv.env out.blocks out.cenv.auxReport.table out.env
  let roots := SourcePublication.selectOriginal nodes cs out.env
  let mut counts : Std.HashMap String Nat := {}
  let mut kinds : Std.HashMap String Nat := {}
  let mut witnessed := 0
  let mut moved := 0
  IO.println s!"selected input {label}: originals={nodes.size} failures={out.cenv.ungrounded.size}"
  for (r, occurrence) in roots.zipIdx do
    let tag := (recordAt out.env r.address).map (kind ·.info) |>.getD "missing"
    let scope := if (recordAt out.env r.address).any (fun c => match c.info with
      | .defn d => d.kind == .defn | _ => false) then "standalone" else "open"
    kinds := kinds.insert tag (kinds.getD tag 0 + 1)
    let site := s!"{label}[{occurrence}] {r.source.pretty} reason={repr r.reason} kind={tag} front-scope={scope} address={r.address}"
    match candidate out.env t pre r.address with
    | .error why =>
      counts := counts.insert "candidate-error" (counts.getD "candidate-error" 0 + 1)
      IO.println s!"{site} outcome=candidate-error {why}"
    | .ok (order, support) =>
      let result := Ixon.Authenticated.checkBytes binding limits (recordsOf out.env order)
        (blobsOf out.env order) (hintsOf out.env)
      match result with
      | .error e =>
        let outcome := reprStr e.outcome
        counts := counts.insert outcome (counts.getD outcome 0 + 1)
        IO.println s!"{site} records={order.length} missing-support={support} outcome={outcome} {e}"
      | .ok envA =>
        counts := counts.insert "accepted" (counts.getD "accepted" 0 + 1)
        IO.println s!"{site} records={order.length} missing-support={support} outcome=accepted"
        let (n, shifts) ← fronts binding t pre out.env order r.address envA
        witnessed := witnessed + n
        moved := moved + shifts
  need (counts.toList.foldl (fun n p => n + p.2) 0 == roots.length) "selected occurrence disappeared"
  IO.println s!"selected census {label}: roots={roots.length} outcomes={repr counts.toList} kinds={repr kinds.toList} standalone-fronts={witnessed} moved={moved}"
  return (witnessed, moved)

private def controls (out : _root_.Ix.CompileM.LeanPipelineOut) (binding : Binding)
    (t : RoleTable) (pre : Prelude .anon) : IO Unit := do
  let store := out.env.consts.fold (init := ({} : Ixon.CheckOrder.RecordStore)) fun m a lc =>
    match lc.get? with | some c => m.insert a c | none => m
  let some (p, c) := store.toList.find? (fun (a, c) => ownerOf a c != a)
    | throw (IO.userError "projection control is vacuous")
  let owner := ownerOf p c
  let ownerOrder := Ixon.CheckOrder.closure store {} #[p]
  need (!ownerOrder.contains p && ownerOrder.contains owner) "owner closure unexpectedly retained literal projection"
  for target in [p, owner] do
    need (!(candidate { out.env with consts := out.env.consts.erase target } t pre p).isOk)
      "missing seed/owner was silently discarded"
  let rs := (Tests.Ix.Kernel.Reader.rekeyed Tests.Ix.Kernel.Reader.definitions).encoded
  let check := fun b l records => Ixon.Authenticated.checkBytes b l records []
  need ((check binding limits rs).isOk) "authenticated definition control failed"
  need (match check binding limits (rs ++ [rs.head!]) with | .error (.duplicate ..) => true | _ => false) "duplicate accepted"
  need (match check binding { limits with maxRecords := 0 } rs with | .error (.limit _) => true | _ => false) "limit accepted"
  need (match check { binding with bytes := binding.bytes.push 0 } limits rs with | .error (.binding _) => true | _ => false) "bad binding accepted"
  let bad := rs.zipIdx.map fun ((a, bytes), i) => (a, if i == 0 then bytes.push 0 else bytes)
  need (match check binding limits bad with | .error (.mismatch ..) => true | _ => false) "bad payload accepted"
  let ill := Tests.Ix.Kernel.Reader.defn .defn (Tests.Ix.Kernel.Reader.ref 0)
    (Tests.Ix.Kernel.Reader.var 0) [Tests.Ix.Kernel.Reader.nat]
  let rejected := (Tests.Ix.Kernel.Reader.rekeyed [(Tests.Ix.Kernel.Reader.address 900, ill)]).encoded
  need (match check binding limits rejected with | .error e@(.kernel ..) => e.outcome == .declined | _ => false) "kernel decline changed"
  let .defn d := ill.info | throw (IO.userError "decline fixture is not a definition")
  let unsafeRecords := (Tests.Ix.Kernel.Reader.rekeyed
    [(Tests.Ix.Kernel.Reader.address 900, { ill with info := .defn { d with safety := .unsaf } })]).encoded
  need (match check binding limits unsafeRecords with | .error (.read _ (.declined _)) => true | _ => false) "unsafe reader decline changed"
  need (!(Ixon.Authenticated.checkBytes binding limits Tests.Ix.Kernel.CertifiedEntry.omitted []).isOk)
    "omitted projection control unexpectedly passed the bare entry"
  IO.println "selected controls: projection/owner distinction, missing seed/owner, byte/binding/duplicate/limit and checker refusal preserved"

-- Family edges add existing input records; they are not ordering prerequisites.
private def referenceText : ConstRef Address → String
  | .member b i => s!"member({b},{i})"
  | .ctor b i k => s!"ctor({b},{i},{k})"

private def supportedCandidate {ixe : Ixon.Env} (p : RecursorSupport.Catalogue ixe limits)
    (t : RoleTable) (pre : Prelude .anon) (root : Address) (literal : List Address) :
    Except String (List Address × Array (Address × String × Bool) × Nat) := do
  let cx := p.context t pre
  let store := recordMap p.constants.toArray
  let mut seen : Std.HashSet Address := {}
  let mut todo := [(root, "root")]
  let mut additions := #[]
  while !todo.isEmpty do
    let (a, why) := todo.head!
    todo := todo.tail
    if seen.contains a then continue
    let some c := store[a]? | throw s!"missing catalogue record {a}: {why}"
    seen := seen.insert a
    if !literal.contains a then additions := additions.push (a, why, true)
    let owner := ownerOf a c
    if owner != a then todo := (owner, s!"projection owner of {a}") :: todo
    for r in c.refs do
      if store.contains r then todo := (r, s!"reference of {a}") :: todo
    if let .muts ms := c.info then
      if ms.any (fun | .indc _ => true | _ => false) then
        let some shape := cx.index.blocks[a]? | throw s!"missing full-catalogue family {a}"
        for recOwner in Ixon.CheckOrder.recursorRecords cx.index a do
          let some ref := shape.recs.find? (·.block == recOwner) | throw "support owner has no selected reference"
          if store.contains recOwner then
            todo := (recOwner, s!"family {a}, selected {referenceText ref}, catalogue input") :: todo
          else
            unless (pre.records ++ pre.evidence).any (·.1 == recOwner) do throw s!"missing fallback recursor {recOwner}"
            additions := additions.push (recOwner, s!"family {a}, selected {referenceText ref}, unshadowed fallback", false)
  let chosen := p.constants.toArray.filter (fun pair => seen.contains pair.1)
  let order := Ixon.CheckOrder.wholeEnv t pre chosen
  unless order.contains root && order.size == seen.size && order.all seen.contains && literal.all order.contains do
    throw "supported candidate dropped an original/literal record"
  let extra := Ixon.CheckOrder.mergeEdges (Ixon.CheckOrder.groundEdges cx.roles.names) (literalEdges cx.roles.names chosen)
  let missing := chosen.foldl (init := ({} : Std.HashSet Address)) fun bad (a, _) =>
    (extra.getD a #[]).foldl (fun bad b =>
      if seen.contains b || pre.records.any (·.1 == b) then bad else bad.insert b) bad
  return (order.toList, additions, missing.size)

private def needError {α : Type} (result : Except String α) (message : String) : IO Unit :=
  need (match result with | .error e => e == message | _ => false) message
open _root_.Ix.Cert.ProjectionRoots in
private def projectionCase (ixe : Ixon.Env) (order : List Address) (root : Address)
    (r : DefinitionSnapshots.Receipt) (label : String) (rows : IO.Ref (Array String)) (wantOrder := false) : IO Unit := do
  let records := recordsOf ixe order
  let some j := records.findIdx? (fun p => p.1 == root) | throw (IO.userError "projection root bytes missing")
  let packet ← IO.ofExcept (locateBytes limits records j)
  let l := packet.location
  let cx := streamContext Address.admissionHash r.table r.pre packet.constants (blobsOf ixe order) (hintsOf ixe)
  let ⟨_, tr⟩ ← IO.ofExcept ((scanOwner cx r.pre.state l).mapError toString)
  let xs := (tr.shape.order.filterMap (_root_.Ix.CompileCert.InductiveReading.indcAt l.members)).toList
  let g ← IO.ofExcept (checkMember cx root l.reference xs tr.rb r.ds)
  let q := g.choice
  need (root != l.reference.block) "projection root/owner distinction is vacuous"
  needError (locate packet.constants packet.constants.length) "projection: input root is unavailable"
  let missing := packet.constants.filter (fun p => p.1 != l.reference.block)
  let some j' := missing.findIdx? (fun p => p.1 == root) | throw (IO.userError "deleted-owner control lost root")
  needError (locate missing j') "projection: input owner is unavailable"
  needError (checkMember cx root l.reference [] tr.rb r.ds) "projection member: motive is unavailable"
  let empty := match l.reference with | .member .. => { tr.rb with types := #[] } | .ctor .. => { tr.rb with ctors := #[] }
  needError (checkMember cx root l.reference xs empty r.ds) "projection member: emitted row is unavailable"
  needError (checkMember cx root l.reference xs tr.rb #[]) "projection member: complete prepared family is unavailable"
  let badRef := match l.reference with | .member b i => .member b (i + 1000000) | .ctor b i k => .ctor b i (k + 1000000)
  need (!(checkMember cx root badRef xs tr.rb r.ds).isOk && !(checkMember cx l.reference.block l.reference xs tr.rb r.ds).isOk) "bad reference/root accepted"
  let header := fun (f : CVal .anon → CVal .anon) => match l.reference with
    | .member .. => { tr.rb with types := tr.rb.types.modify q.rowIndex fun (v, p, n) => (f v, p, n) }
    | .ctor .. => { tr.rb with ctors := tr.rb.ctors.modify q.rowIndex fun (v, p, n) => (f v, p, n) }
  let count := match l.reference with
    | .member .. => { tr.rb with numParams := tr.rb.numParams + 1 }
    | .ctor .. => { tr.rb with ctors := tr.rb.ctors.modify q.rowIndex fun (v, p, n) => (v, p, n + 1) }
  for bad in [header (fun v => { v with type := .forallE (.sort .zero) v.type { pw := .never } }),
      header (fun v => { v with levelParams := v.levelParams ++ [999999] }), count] do
    need (decide (CtxAgree.indDeclOf bad ≠ CtxAgree.indDeclOf tr.rb)) "payload mutation is vacuous"
    needError (checkMember cx root l.reference xs bad r.ds) "projection member: complete prepared family is unavailable"
  for d in [.indDecl (familyList tr.rb) (tr.rb.numParams + 1), .indDecl (familyList tr.rb).reverse tr.rb.numParams] do
    need (decide (d ≠ CtxAgree.indDeclOf tr.rb)) "prepared mutation is vacuous"
    needError (checkMember cx root l.reference xs tr.rb (r.ds.modify q.prepared fun _ => d)) "projection member: complete prepared family is unavailable"
  need (!decide (Matches l.reference xs tr.rb r.ds { q with prepared := r.ds.size })) "wrong prepared index accepted"
  -- Deliberately untrusted raw context: keys agree, only address correspondence fails.
  let fake : Ctx .anon := { cx with
    roles := { names := cx.roles.names.insert l.reference q.row.1.name }
    keys := {}
    reconstruct := fun _ => some l.reference.block }
  need ((fake.keyAt root).toOption == some q.row.1.name && (fake.memberKey l.reference).toOption == some q.row.1.name &&
    (fake.addressOf l.reference).toOption == some l.reference.block) "address-only control is vacuous"
  needError (checkMember fake root l.reference xs tr.rb r.ds) "projection member: key or address correspondence failed"
  let ctorOrder := match l.reference with | .ctor .. => decide (tr.rb.ctors.size > 1) | _ => false
  if ctorOrder then
    let swapped := { tr.rb with ctors := tr.rb.ctors.swapIfInBounds q.rowIndex ((q.rowIndex + 1) % tr.rb.ctors.size) }
    need (decide (CtxAgree.indDeclOf swapped ≠ CtxAgree.indDeclOf tr.rb) && !(checkMember cx root l.reference xs swapped r.ds).isOk) "constructor order control failed"
  if wantOrder then
    need (xs.length > 1) "nested multi-motive witness missing"
    let other := (q.motive + 1) % xs.length
    need (xs[q.motive]?.map Prod.fst != xs[other]?.map Prod.fst) "motive witness has duplicate indices"
    need (!(checkMember cx root l.reference (xs.toArray.swapIfInBounds q.motive other).toList tr.rb r.ds).isOk) "motive order mutation accepted"
    need (!(checkMember cx root l.reference xs { tr.rb with types := tr.rb.types.swapIfInBounds q.motive other } r.ds).isOk) "type order mutation accepted"
    let some (pa, pc) := (r.pre.records ++ r.pre.evidence).find? (fun p => p.2.info matches .iPrj _) | throw (IO.userError "prelude projection witness missing")
    let fallback := streamContext Address.admissionHash r.table r.pre [(pa, pc)] [] (fun _ => none)
    need ((resolveSource fallback.store pa pc).isSome) "prelude-only owner does not resolve"
    needError (locate [(pa, pc)] 0) "projection: input owner is unavailable"
  let nonzero := match l.reference with | .ctor _ _ k => decide (k > 0) | _ => false
  let line := s!"projection {label} root={root} record={j} owner={l.reference.block} owner-record={l.ownerPosition} raw={referenceText l.reference}"
  rows.modify (·.push (line ++ s!" motive={q.motive} flat={q.rowIndex} family-slot={q.position} prepared={q.prepared} key={q.row.1.name}" ++
    s!" order={repr tr.shape.order} types={tr.rb.types.size}:{repr (tr.rb.types.map fun x => toString x.1.name)}" ++
    s!" nonzero-ctor={nonzero} ctor-order={ctorOrder} motive-order={wantOrder}"))

private def supportedCensus (out : _root_.Ix.CompileM.LeanPipelineOut) (binding : Binding)
    (t : RoleTable) (pre : Prelude .anon) (theorems projections : IO.Ref (Array String)) : IO Unit := do
  let p ← IO.ofExcept ((RecursorSupport.catalogue out.env limits).mapError reprStr)
  let some nodes := out.sourceNodes? | throw (IO.userError "missing original facts")
  let cs := _root_.Ix.Compile.ChangedSet.ofCompile out.cenv.env out.blocks out.cenv.auxReport.table out.env
  let roots := SourcePublication.selectOriginal nodes cs out.env
  let mut counts : Std.HashMap String Nat := {}
  let mut witnessed := 0
  let mut familyAgreed := 0
  let mut missingExtras := 0
  for (r, occurrence) in roots.zipIdx do
    let site := s!"supported[{occurrence}] {r.source.pretty} reason={repr r.reason} address={r.address}"
    let (literal, _) ← IO.ofExcept (candidate out.env t pre r.address)
    let mut outcome := "candidate-error"
    match supportedCandidate p t pre r.address literal with
    | .error why => IO.println s!"{site} outcome={outcome} {why}"
    | .ok (order, additions, missing) =>
      missingExtras := missingExtras + missing
      for (a, why, artifact) in additions do IO.println s!"  {site} support={a} artifact={artifact} {why}"
      let same ← IO.ofExcept ((p.checkBatch t pre order).mapError reprStr)
      if !same then
        outcome := "family-conflict"
        IO.println s!"{site} literal={literal.length} supported={order.length} missing-extra={missing} outcome={outcome}"
      else
        familyAgreed := familyAgreed + 1
        match DefinitionSnapshots.checkReceipt binding limits (recordsOf out.env order)
            (blobsOf out.env order) (hintsOf out.env) with
        | .error e =>
          outcome := reprStr e.outcome
          IO.println s!"{site} literal={literal.length} supported={order.length} missing-extra={missing} family-agreement=true outcome={outcome} {e}"
        | .ok receipt =>
          outcome := "accepted"
          IO.println s!"{site} literal={literal.length} supported={order.length} missing-extra={missing} family-agreement=true outcome=accepted"
          let n ← if (recordAt out.env r.address).any (fun c => match c.info with | .iPrj _ | .cPrj _ => true | _ => false) then do
              projectionCase out.env order r.address receipt site projections
              pure 0
            else Prod.fst <$> fronts binding receipt.table receipt.pre out.env order r.address receipt.env (some receipt) (some (theorems, site))
          witnessed := witnessed + n
    counts := counts.insert outcome (counts.getD outcome 0 + 1)
  need (counts.toList.foldl (fun n p => n + p.2) 0 == roots.length) "supported occurrence disappeared"
  IO.println s!"supported census: roots={roots.length} outcomes={repr counts.toList} family-agreements={familyAgreed} missing-extra={missingExtras} new-batch-standalone-fronts={witnessed}"
  need (roots.length == 68 && counts.getD "accepted" 0 == 68 && familyAgreed == 68 &&
    witnessed == 47 && missingExtras == 0) "O2Split supported admission regression changed"

private def supportControls (binding : Binding) (t : RoleTable) (pre : Prelude .anon) : IO Unit := do
  let fixture := Tests.Ix.Kernel.Reader.rekeyed Tests.Ix.Kernel.Reader.twoFixture
  let asEnv := fun (xs : Ingress.Constants) => xs.foldl (fun e (a, c) => e.storeConst a c) ({} : Ixon.Env)
  let ixe := asEnv fixture.records
  let p ← IO.ofExcept ((RecursorSupport.catalogue ixe limits).mapError reprStr)
  let block := fixture.rename (Tests.Ix.Kernel.Reader.address 20)
  let root := fixture.rename (Tests.Ix.Kernel.Reader.address 21)
  let recAddr := fixture.rename (Tests.Ix.Kernel.Reader.address 24)
  let (literal, _) ← IO.ofExcept (candidate ixe t pre root)
  need (!(Ixon.Authenticated.checkBytes binding limits (recordsOf ixe literal) (blobsOf ixe literal) (hintsOf ixe)).isOk)
    "Two literal batch unexpectedly admitted without recursor support"
  let (order, additions, _) ← IO.ofExcept (supportedCandidate p t pre root literal)
  need (order.contains recAddr && additions.any (fun (a, _, artifact) => a == recAddr && artifact)) "recursor support not recorded"
  need (match p.checkBatch t pre order with | .ok true => true | _ => false) "Two family agreement failed"
  need ((Ixon.Authenticated.checkBytes binding limits (recordsOf ixe order) (blobsOf ixe order) (hintsOf ixe)).isOk)
    "Two supported batch did not admit"
  let missing := { ixe with consts := ixe.consts.erase recAddr }
  let missingP ← IO.ofExcept ((RecursorSupport.catalogue missing limits).mapError reprStr)
  need (!(supportedCandidate missingP t pre root literal).isOk) "missing support payload was synthesized"
  let some original := p.constants.lookup recAddr | throw (IO.userError "Two recursor missing")
  let alternative := { original with sharing := original.sharing.push (.sort 0) }
  let altAddr := Address.admissionHash (Ixon.serConstant alternative)
  need (altAddr != recAddr) "competing recursor is not distinct"
  let conflictEnv := ixe.storeConst altAddr alternative
  let competing ← IO.ofExcept ((RecursorSupport.catalogue conflictEnv limits).mapError reprStr)
  let full := (competing.context t pre).index
  let some shape := full.blocks[block]? | throw (IO.userError "competing family missing")
  let some selected := shape.recs[0]? | throw (IO.userError "competing family empty")
  let loser := if selected.block == recAddr then altAddr else recAddr
  let originalOrder := competing.constants.map Prod.fst
  let changedOrder := loser :: originalOrder.filter (· != loser)
  need (match competing.checkBatch t pre originalOrder with | .ok true => true | _ => false) "unchanged family guard failed"
  need (match competing.checkBatch t pre changedOrder with | .ok false => true | _ => false) "first-winner conflict was hidden"
  let some entry := full.recs[selected]? | throw (IO.userError "selected entry missing")
  for altered in [{ entry with block := recAddr }, { entry with motive := entry.motive + 1 },
      { entry with major := .ctor block 0 0 }, { entry with large := !entry.large }] do
    need (!RecursorSupport.familyEq full { full with recs := full.recs.insert selected altered } block) "entry field conflict hidden"
  let empty : RecIndex := { blocks := ({} : Std.HashMap Address BlockShape).insert block default }
  need (!RecursorSupport.familyEq {} {} block && !RecursorSupport.familyEq empty {} block &&
    RecursorSupport.familyEq empty empty block) "missing and computed empty shape confused"
  let shadow := contextOf (md := .anon) t #[(recAddr, alternative)] [] #[(recAddr, original)]
  need (shadow.store recAddr == some alternative &&
    !(ReaderClosureKeys.scanned #[(recAddr, alternative)] #[(recAddr, original)]).contains (recAddr, original)) "fallback shadowing changed"
  let .recr r := original.info | throw (IO.userError "Two recursor is not standalone")
  let mutualRecord := { original with info := .muts #[.recr r] }
  let mutualAddr := Address.admissionHash (Ixon.serConstant mutualRecord)
  let mutualEnv := (asEnv (fixture.records.filter (fun row => row.1 != recAddr))).storeConst mutualAddr mutualRecord
  let mutualP ← IO.ofExcept ((RecursorSupport.catalogue mutualEnv limits).mapError reprStr)
  need ((Ixon.CheckOrder.recursorRecords (mutualP.context t pre).index block).contains mutualAddr) "mutual recursor origin lost"
  IO.println "support controls: Two supplied family, absent payload, exact first winner, all entry fields, missing/empty, fallback shadow and mutual record passed"

private def snapshotControls (binding : Binding) (t : RoleTable) (pre : Prelude .anon) : IO Unit := do
  let env ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let raw := Tests.Ix.Compile.Harness.closureOf env [`Tests.Ix.Kernel.EntryCaseDefs.natAdd]
  let out ← IO.ofExcept (← _root_.Ix.CompileM.compileLeanConsts raw (numWorkers := 1))
  let some named := out.env.named.get? (_root_.Ix.Name.fromLeanName `Tests.Ix.Kernel.EntryCaseDefs.natAdd)
    | throw (IO.userError "native operation control root not published")
  let p ← IO.ofExcept ((RecursorSupport.catalogue out.env limits).mapError reprStr)
  let (literal, _) ← IO.ofExcept (candidate out.env t pre named.addr)
  let (order, _, _) ← IO.ofExcept (supportedCandidate p t pre named.addr literal)
  let records := recordsOf out.env order
  let blobs := blobsOf out.env order
  let r ← IO.ofExcept ((DefinitionSnapshots.checkReceipt binding limits records blobs (hintsOf out.env)).mapError toString)
  let native := r.ds.zipIdx.filterMap fun (d, i) => match d with
    | .defnDecl cv _ _ => if natOpNames.contains cv.name || natDivModNames.contains cv.name then some i else none
    | _ => none
  need (!native.isEmpty) "native full-install definition control is vacuous"
  for i in native do
    let s ← IO.ofExcept (r.snapshot i)
    need (s.view.find? s.cv.name == none && (r.env.find? s.cv.name).isSome) "native snapshot exposed itself"
    IO.println s!"native snapshot prepared={i} counter={s.counter} key={s.cv.name}"
  let some first := r.ds.findIdx? (fun | .defnDecl .. => true | _ => false) | throw (IO.userError "definition control absent")
  let s ← IO.ofExcept (r.snapshot first)
  need (s.counter != first) "declaration position incorrectly used as constant counter"
  let some later := r.env.consts.head? | throw (IO.userError "checked environment empty")
  need (later.name != s.cv.name && s.view.find? later.name == none) "later-key hiding control is vacuous or wrong"
  need (!(r.snapshot r.ds.size).isOk) "out-of-range snapshot accepted"
  let some other := r.ds.findIdx? (fun | .defnDecl .. => false | _ => true) | throw (IO.userError "mixed declaration control absent")
  need (!(r.snapshot other).isOk) "non-definition snapshot accepted"
  need (!({ r with index := { r.index with idx := r.index.idx.erase s.cv.name } }.snapshot first).isOk) "missing lookup accepted"
  let wrong := { r with index := { r.index with idx := r.index.idx.insert s.cv.name (s.counter, .axiomInfo s.cv) } }
  need (!(wrong.snapshot first).isOk) "wrong indexed kind accepted"
  let badRecords := records.map fun (a, bytes) => (a, bytes.push 0)
  let check := fun b l => DefinitionSnapshots.checkReceipt b l badRecords blobs (hintsOf out.env)
  need (match check { binding with bytes := binding.bytes.push 0 } { limits with maxRecords := 0 } with
    | .error (.binding _) => true | _ => false) "receipt changed binding error precedence"
  need (match check binding { limits with maxRecords := 0 } with
    | .error (.limit _) => true | _ => false) "receipt changed limit error precedence"
  need (match check binding limits with | .error (.mismatch ..) => true | _ => false) "receipt changed byte error precedence"
  IO.println "snapshot controls: native full-install, constant/declaration offsets, later-key hiding, missing/kind indices and exact error precedence passed"

def candidateTarget : Nat := 7

-- Synthetic candidate controls only: zero is not the source form of seven.
private def candidateControls (binding : Binding) (t : RoleTable) (pre : Prelude .anon) : IO Unit := do
  let env ← getCompileEnv #[`Tests.Ix.Compile.SelectedAdmission]
  let raw := Tests.Ix.Compile.Harness.closureOf env [``candidateTarget]
  let out ← IO.ofExcept (← _root_.Ix.CompileM.compileLeanConsts raw (numWorkers := 1))
  let some named := out.env.named.get? (_root_.Ix.Name.fromLeanName ``candidateTarget)
    | throw (IO.userError "candidate target missing")
  let p ← IO.ofExcept ((RecursorSupport.catalogue out.env limits).mapError reprStr)
  let (literal, _) ← IO.ofExcept (candidate out.env t pre named.addr)
  let (order, _, _) ← IO.ofExcept (supportedCandidate p t pre named.addr literal)
  let records := recordsOf out.env order
  let blobs := blobsOf out.env order
  let r ← IO.ofExcept ((DefinitionSnapshots.checkReceipt binding limits records blobs (hintsOf out.env)).mapError toString)
  let constants ← IO.ofExcept ((decodeRecords limits records).mapError reprStr)
  let cx := streamContext Address.admissionHash r.table r.pre constants blobs (hintsOf out.env)
  let key ← IO.ofExcept ((cx.memberKey (.member named.addr 0)).mapError reprStr)
  let some i := r.ds.findIdx? (fun | .defnDecl cv .. => cv.name == key | _ => false)
    | throw (IO.userError "candidate definition index missing")
  let s ← IO.ofExcept (r.snapshot i)
  need (s.cv.levelParams.isEmpty && !natOpNames.contains key && !natDivModNames.contains key)
    "candidate control is not an ordinary monomorphic definition"
  let natTy : _root_.Ix.Kernel.Expr .anon := .const natName []
  let good : _root_.Ix.Kernel.Expr .anon := .const natZeroName []
  need (good != s.raw) "candidate control copied the target body"
  let .ok checked := CandidateValueFront.checkAt r i good | throw (IO.userError "distinct well-typed candidate refused")
  need (!checked.hasFvar && checked != s.checked) "candidate result was confused with the target value"
  let missing : Key .anon := .id (Tests.Ix.Kernel.Reader.address 999)
  need (s.view.find? key == none && s.view.find? missing == none) "negative lookup controls are vacuous"
  let bad : List (String × _root_.Ix.Kernel.Expr .anon) :=
    [("wrong type", .sort .zero), ("loose variable", .bvar 0), ("free variable", .fvar 0 natTy),
     ("current self", .const key []), ("unresolved", .const missing []), ("undeclared level", .sort (.param 999))]
  for (label, value) in bad do
    need (match CandidateValueFront.checkAt r i value with | .error (.value _) => true | _ => false)
      s!"candidate {label} did not preserve a value error"
  let .error expectedContext := r.snapshot r.ds.size | throw (IO.userError "missing-index control accepted")
  need (match CandidateValueFront.checkAt r r.ds.size good with
    | .error (.context got) => got == expectedContext | _ => false) "candidate context error changed"
  let same ← IO.ofExcept (r.snapshot i)
  need (same.checked == s.checked && same.expected == s.expected) "temporary candidate push changed the target receipt"
  IO.println "candidate controls: distinct typed value only; wrong type, loose/free variables, self, unresolved and level errors; context error and target receipt preserved"

structure TheoremBox where
  witness : True
  kids : List TheoremBox
run_cmd do
  let some (.thmInfo d) := (← Lean.getEnv).find? `Tests.Ix.Compile.SelectedAdmission.TheoremBox.witness
    | throwError "primitive projection theorem missing"
  Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl
    { name := `Tests.Ix.Compile.SelectedAdmission.theoremProjection,
      levelParams := d.levelParams, type := d.type, value := d.value })

open Tests.Ix.Kernel.Reader in
private def theoremControls (binding : Binding) (t : RoleTable) (pre : Prelude .anon) (projections : IO.Ref (Array String)) : IO Unit := do
  let env ← getCompileEnv #[`Tests.Ix.Compile.SelectedAdmission]
  let input := Tests.Ix.Compile.Harness.closureOf env [`Tests.Ix.Compile.SelectedAdmission.theoremProjection]
  let out ← IO.ofExcept (← _root_.Ix.CompileM.compileLeanConsts input (numWorkers := 1))
  let some named := out.env.named.get? (_root_.Ix.Name.fromLeanName `Tests.Ix.Compile.SelectedAdmission.theoremProjection)
    | throw (IO.userError "theorem projection control not published")
  let p ← IO.ofExcept ((RecursorSupport.catalogue out.env limits).mapError reprStr)
  let (literal, _) ← candidate out.env t pre named.addr |> IO.ofExcept
  let (order, _, _) ← supportedCandidate p t pre named.addr literal |> IO.ofExcept
  let r ← IO.ofExcept ((DefinitionSnapshots.checkReceipt binding limits (recordsOf out.env order)
    (blobsOf out.env order) (hintsOf out.env)).mapError toString)
  let rows ← IO.mkRef #[]
  let _ ← fronts binding r.table r.pre out.env order named.addr r.env (some r) (some (rows, "projection-control"))
  let observed ← rows.get
  for row in observed do IO.println row
  let some i := r.ds.findIdx? (fun | .thmDecl .. => true | _ => false) | throw (IO.userError "theorem control absent")
  let s ← IO.ofExcept (TheoremSnapshots.snapshot r i)
  let failure := fun r i msg => need (match TheoremSnapshots.snapshot r i with | .error e => e == msg | _ => false) msg
  failure r r.ds.size "theorem snapshot: declaration index is unavailable"
  let some other := r.ds.findIdx? (fun | .thmDecl .. => false | _ => true) | throw (IO.userError "other kind absent")
  failure r other "theorem snapshot: declaration is not a theorem"
  failure { r with index := { r.index with idx := r.index.idx.erase s.cv.name } } i
    "theorem snapshot: theorem index entry is unavailable"
  failure { r with index := { r.index with idx := r.index.idx.insert s.cv.name (s.counter, .axiomInfo s.cv) } } i
    "theorem snapshot: indexed constant is not a theorem"
  let bads := [(defn .thm (ref 0) (var 0) [nat], "type of theorem "),
    (defn .thm (apps (ref 0 [0]) [ref 1, ref 2, ref 2]) (ref 2) [eq, nat, natZero] [one], "type mismatch in theorem ")]
  for (bad, message) in bads do
    let batch := (rekeyed [(address 230, bad)]).encoded
    need (match DefinitionSnapshots.checkReceipt binding limits batch [] (fun _ => none) with
      | .error (.kernel (.invalid m) _) => (Msg.render toString m).startsWith message
      | _ => false) "theorem proposition-before-body or value error changed"
  IO.println "theorem error controls: four context errors, proposition-before-body and theorem value refusal passed"
  need (observed.size == 1 && observed.all (·.endsWith "projection=true")) "theorem projection rewrite control is vacuous"
  IO.println "theorem controls: actual projection rewrite, raw storage, four context errors, proposition-before-body and theorem value refusal passed"
  let some typeRoot := out.env.named.get? (_root_.Ix.Name.fromLeanName `Tests.Ix.Compile.SelectedAdmission.TheoremBox)
    | throw (IO.userError "nested type projection missing")
  projectionCase out.env order typeRoot.addr r "nested-projection-control" projections

private def mutualProjectionControl (binding : Binding) (t : RoleTable) (pre : Prelude .anon)
    (projections : IO.Ref (Array String)) : IO Unit := do
  let env ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let input := Tests.Ix.Compile.Harness.closureOf env
    [`Tests.Ix.Kernel.EntryCaseDefs.Tm, `Tests.Ix.Kernel.EntryCaseDefs.Args]
  let out ← IO.ofExcept (← _root_.Ix.CompileM.compileLeanConsts input (numWorkers := 1))
  need out.cenv.ungrounded.isEmpty "mutual projection control has compile failures"
  let some named := out.env.named.get? (_root_.Ix.Name.fromLeanName `Tests.Ix.Kernel.EntryCaseDefs.Tm)
    | throw (IO.userError "mutual projection root missing")
  let p ← IO.ofExcept ((RecursorSupport.catalogue out.env limits).mapError reprStr)
  let (literal, _) ← IO.ofExcept (candidate out.env t pre named.addr)
  let (order, _, _) ← IO.ofExcept (supportedCandidate p t pre named.addr literal)
  need (← IO.ofExcept ((p.checkBatch t pre order).mapError reprStr)) "mutual family agreement failed"
  let r ← IO.ofExcept ((DefinitionSnapshots.checkReceipt binding limits (recordsOf out.env order)
    (blobsOf out.env order) (hintsOf out.env)).mapError toString)
  projectionCase out.env order named.addr r "mutual-order-control" projections true

def runSupported : IO Unit := do
  let binding ← IO.ofExcept defaultBinding
  let t ← IO.ofExcept ((admitBinding Address.admissionHash binding).mapError (toString ∘ Error.binding))
  let pre : Prelude .anon ← IO.ofExcept (preludeFor t)
  let unit ← Tests.Ix.Compile.Harness.unitOfFile "Tests/Ix/Compile/Pass/O2Split.lean"
  let out ← Tests.Ix.Compile.Harness.compileUnit unit 1
  let (witnessed, moved) ← census "O2Split" out binding t pre
  need (witnessed == 11 && moved == 11) "frozen literal-batch front baseline changed"
  controls out binding t pre
  let theorems ← IO.mkRef #[]
  let projections ← IO.mkRef #[]
  supportedCensus out binding t pre theorems projections
  supportControls binding t pre
  snapshotControls binding t pre
  candidateControls binding t pre
  let rows ← theorems.get
  need (rows.size == 15 && (rows.filter (·.contains "Reason.cascade")).size == 11) "15 theorem occurrences or reasons changed"
  for row in rows do IO.println row
  theoremControls binding t pre projections
  mutualProjectionControl binding t pre projections
  let projectionRows ← projections.get
  let selected := projectionRows.filter (·.startsWith "projection supported[")
  need (projectionRows.size == 8 && selected.size == 6 && (selected.filter (·.contains "raw=member(")).size == 2 &&
    (selected.filter (·.contains "raw=ctor(")).size == 4 && selected.any (·.contains "nonzero-ctor=true") &&
    selected.any (·.contains "ctor-order=true") && projectionRows.any (fun s => s.startsWith "projection mutual-order-control" && s.contains "motive-order=true")) "projection census/order coverage changed"
  for row in projectionRows do IO.println row
  IO.println "projection census: six original roots (two types/four constructors), two extra control rows, one extra admission; actual order, prelude-only, unavailable, key/address, payload and prepared-family controls passed"

def run : IO Unit := do
  let binding ← IO.ofExcept defaultBinding
  let t ← IO.ofExcept ((admitBinding Address.admissionHash binding).mapError (toString ∘ Error.binding))
  let pre : Prelude .anon ← IO.ofExcept (preludeFor t)
  let name := `SelectedAdmission.tiny
  let tiny : Lean.ConstantInfo := .defnInfo
    { name, levelParams := [], type := .sort (.succ .zero),
      value := .sort .zero, hints := .abbrev, safety := .safe, all := [name] }
  let normal ← IO.ofExcept (← _root_.Ix.CompileM.compileLeanConsts [(name, tiny)] (numWorkers := 1))
  let _ ← census "ordinary" normal binding t pre
  let unit ← Tests.Ix.Compile.Harness.unitOfFile "Tests/Ix/Compile/Pass/O2Split.lean"
  let changed ← Tests.Ix.Compile.Harness.compileUnit unit 1
  let (witnessed, moved) ← census "O2Split" changed binding t pre
  need (witnessed > 0 && moved > 0) "no admitted selected standalone definition with a real prepared-index shift"
  controls changed binding t pre

/-- info: 'Ix.Cert.AdmittedTargetFronts.prepared_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.AdmittedTargetFronts.prepared_of_check
/-- info: 'Ix.Cert.AdmittedTargetFronts.decoded_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.AdmittedTargetFronts.decoded_at
/-- info: 'Ix.Cert.AdmittedTargetFronts.stream_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.AdmittedTargetFronts.stream_at
/-- info: 'Ix.Cert.AdmittedTargetFronts.Prepared.singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.AdmittedTargetFronts.Prepared.singleton
/-- info: 'Ix.Cert.AdmittedTargetFronts.selected_fronts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.AdmittedTargetFronts.selected_fronts
/-- info: 'Ix.Cert.RecursorSupport.Catalogue.origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.RecursorSupport.Catalogue.origin
/-- info: 'Ix.Cert.RecursorSupport.recursorRecords_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.RecursorSupport.recursorRecords_mem
/-- info: 'Ix.Cert.RecursorSupport.Catalogue.support_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.RecursorSupport.Catalogue.support_origin
/-- info: 'Ix.Cert.RecursorSupport.familyEq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.RecursorSupport.familyEq_iff
/-- info: 'Ix.Cert.RecursorSupport.Catalogue.checkBatch_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.RecursorSupport.Catalogue.checkBatch_iff
/-- info: 'Ix.Cert.DefinitionSnapshots.checkReceipt_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.DefinitionSnapshots.checkReceipt_env
/-- info: 'Ix.Cert.DefinitionSnapshots.checkReceipt_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.DefinitionSnapshots.checkReceipt_ok
/-- info: 'Ix.Cert.DefinitionSnapshots.snapshot_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.DefinitionSnapshots.snapshot_of_check
/-- info: 'Ix.Cert.CandidateValueFront.checkAt_front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.CandidateValueFront.checkAt_front
/-- info: 'Ix.Cert.TheoremSnapshots.selected_theorem_fronts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.TheoremSnapshots.selected_theorem_fronts
/-- info: 'Ix.Cert.TheoremSnapshots.snapshot_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.TheoremSnapshots.snapshot_of_check
end Tests.Ix.Compile.SelectedAdmission
