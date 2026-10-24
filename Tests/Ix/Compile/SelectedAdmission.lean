import Ix.Cert.AdmittedTargetFronts
import Ix.Cert.RecursorSupport
import Ix.Cert.DefinitionSnapshots
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
    (receipt? : Option DefinitionSnapshots.Receipt := none) : IO (Nat × Nat) := do
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
        if d.kind == .defn then
          let key ← IO.ofExcept ((cx.memberKey (.member a 0)).mapError reprStr)
          let ty ← IO.ofExcept (((definitionReader cx a c d).read d.typ).mapError reprStr)
          let value ← IO.ofExcept (((definitionReader cx a c d).read d.value).mapError reprStr)
          let cv : _root_.Ix.Kernel.ConstantVal .anon := ⟨key, singletonLps d.lvls, ty⟩
          let raw := (projRewrite st cv value).getD value
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

private def supportedCensus (out : _root_.Ix.CompileM.LeanPipelineOut) (binding : Binding)
    (t : RoleTable) (pre : Prelude .anon) : IO Unit := do
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
          let (n, _) ← fronts binding receipt.table receipt.pre out.env order r.address receipt.env (some receipt)
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

def runSupported : IO Unit := do
  let binding ← IO.ofExcept defaultBinding
  let t ← IO.ofExcept ((admitBinding Address.admissionHash binding).mapError (toString ∘ Error.binding))
  let pre : Prelude .anon ← IO.ofExcept (preludeFor t)
  let unit ← Tests.Ix.Compile.Harness.unitOfFile "Tests/Ix/Compile/Pass/O2Split.lean"
  let out ← Tests.Ix.Compile.Harness.compileUnit unit 1
  let (witnessed, moved) ← census "O2Split" out binding t pre
  need (witnessed == 11 && moved == 11) "frozen literal-batch front baseline changed"
  controls out binding t pre
  supportedCensus out binding t pre
  supportControls binding t pre
  snapshotControls binding t pre

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
end Tests.Ix.Compile.SelectedAdmission
