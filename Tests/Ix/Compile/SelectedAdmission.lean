import Ix.Cert.AdmittedTargetFronts
import Ix.Ixon.CheckOrder
import Tests.Ix.Compile.Harness.Units
import Tests.Ix.Kernel.Authentication

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
    (ixe : Ixon.Env) (order : List Address) (root : Address) (envA : Env .anon) : IO (Nat × Nat) := do
  let records := recordsOf ixe order
  let blobs := blobsOf ixe order
  let hint := hintsOf ixe
  let constants ← IO.ofExcept ((decodeRecords limits records).mapError reprStr)
  let (_, ds) ← IO.ofExcept ((prepareWith Address.admissionHash binding pre limits records blobs hint).mapError toString)
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
    let .defnDecl cv _ h := decl | throw (IO.userError "wrong front kind")
    let some (.defnInfo got _ storedHint) := envA.find? cv.name | throw (IO.userError "checked definition missing")
    need (got.name == cv.name && got.levelParams == cv.levelParams && storedHint == h) "checked identity/levels/hint changed"
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
end Tests.Ix.Compile.SelectedAdmission
