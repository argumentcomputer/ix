import Lean

/-!
# Proof closure under suggested premises

`lean --run Closure.lean SRC MODULE TASKS OUT HEARTBEATS TIMEOUT-MS`

Elaborates the module source `SRC` (whose module name is `MODULE`) command by command with the
frontend, keeping the command state from before each command. When a command adds one of the
target theorems listed in `TASKS`, the theorem's type is read from the environment after the
command and every premise condition for it is attempted on a fresh goal of that type, in the
command state from *before* the command: later declarations and attributes, and the theorem
itself, are absent. Theorems whose type mentions a constant that the same command created are
skipped.

`TASKS` has lines `THEOREM<TAB>CONDITION<TAB>P1,P2,…`; each premise may list alternative names
separated by `|`, the first present in the pre-command environment being used. Names are compared
in the form `Name.toString` prints them.

Each condition runs the portfolio `simp_all [Ps]`, `aesop (add unsafe 20% P)…`, `grind [Ps]`
in order, after `intros`, each under `HEARTBEATS` (thousands, as `maxHeartbeats`) and a wall-clock
limit of `TIMEOUT-MS`. Before an attempt, each premise is tried alone with that tactic on the goal
`True`; a premise whose elaboration raises or logs an error is dropped for that tactic only. An
attempt closes the goal when it raises nothing, logs no error, leaves no goal, and the instantiated
proof has no metavariable or `sorry` and is accepted by the kernel as a theorem of the target type.
For a closing attempt, the premises it was handed are split into those occurring in the proof
term, those reached only through declarations the attempt added, those reached only through
internal declarations that already existed, and those reached only through one of their equation
lemmas (`used`, `usedViaAux`, `usedViaInternal`, `usedViaEq`).

One JSON object per line is written to `OUT`, per theorem and condition.
-/

open Lean Elab Meta

structure Cond where
  name : String
  premises : Array (Array String)

structure Target where
  thm : String
  conds : Array Cond

def tacticNames : Array String := #["simp_all", "aesop", "grind"]

/-- Placeholder identifiers stand in for premise names in tactic text and are then replaced by
`_root_`-qualified identifiers, so any constant name (private, numeric components, escapes)
reaches the elaborator unchanged. -/
def placeholder (i : Nat) : Name := Name.mkSimple s!"ixclosurePremise{i}"

def tacticText (tac : String) (n : Nat) : String :=
  let ps := (List.range n).map fun i => (placeholder i).toString
  match tac with
  | "simp_all" => if n == 0 then "simp_all" else s!"simp_all [{", ".intercalate ps}]"
  | "aesop" => "aesop" ++ String.join (ps.map fun p => s!" (add unsafe 20% {p})")
  | _ => if n == 0 then "grind" else s!"grind [{", ".intercalate ps}]"

def substPremises (stx : Syntax) (ps : Array Name) : Syntax :=
  Id.run <| stx.replaceM (m := Id) fun s =>
    if s.isIdent then
      match s.getId with
      | .str .anonymous str =>
        if str.startsWith "ixclosurePremise" then
          match (str.drop 16).toString.toNat? with
          | some i => if h : i < ps.size then some (mkIdent (`_root_ ++ ps[i])) else none
          | none => none
        else none
      | _ => none
    else none

def jsonStr (s : String) : String := (Json.str s).compress

def names (ns : Array Name) : String := s!"[{",".intercalate (ns.toList.map (jsonStr ·.toString))}]"

/-- Wall-clock limit shared by all attempts: a single watchdog thread sets the current token once
its deadline passes. -/
structure Watchdog where
  slot : IO.Ref (Option (Nat × IO.CancelToken))

def Watchdog.start : IO Watchdog := do
  let slot ← IO.mkRef none
  let rec loop : Nat → IO Unit
    | 0 => pure ()
    | k + 1 => do
      IO.sleep 20
      if let some (deadline, tk) ← slot.get then
        if (← IO.monoMsNow) ≥ deadline then tk.set
      loop k
  let _ ← IO.asTask (prio := .dedicated) (loop 1000000000)
  return { slot }

structure Outcome where
  closed : Bool
  err : String := ""
  remaining : Nat := 0
  /-- Premises occurring in the closing proof term itself. -/
  used : Array Name := #[]
  /-- Premises reached only through declarations the attempt added. -/
  usedViaAux : Array Name := #[]
  /-- Premises reached only through pre-existing internal declarations. -/
  usedViaInternal : Array Name := #[]
  /-- Premises reached only through one of their equation lemmas (`p.eq_1`, `p.eq_def`, …). -/
  usedViaEq : Array Name := #[]

def isEqLemmaOf (p c : Name) : Bool :=
  match c with
  | .str q s => q == p && (s.startsWith "eq_" || s == "eq_def" || s == "eq_unfold")
  | _ => false

/-- Constants reachable from `roots` through the bodies of the constants that `expand` admits. -/
def reach (env : Environment) (roots : NameSet) (expand : Name → Bool) : NameSet := Id.run do
  let mut seen := roots
  let mut work := roots.toList.filter expand
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => break
    | c :: rest =>
      work := rest
      let some ci := env.find? c | continue
      let body := ci.value? (allowOpaque := true) |>.getD ci.type
      for d in body.getUsedConstants do
        if !seen.contains d then
          seen := seen.insert d
          if expand d then work := d :: work
  return seen

structure PremiseUse where
  used : Array Name
  viaAux : Array Name
  viaInternal : Array Name
  viaEq : Array Name

/-- Which of `ps` a proof `val` uses: in the term itself; through declarations added during the
attempt (absent from `env0`, such as simp's `_auxLemma.N` or grind's abstracted proofs); through
internal declarations that already existed (`_proof_N`, `_auxLemma.N` made by earlier commands),
whose bodies may also mention premises the tactic did not choose; or through one of their equation
lemmas (`p.eq_1`, `p.eq_def`, …). Pure, so it consumes no heartbeats and cannot be interrupted. -/
def premiseUse (env env0 : Environment) (val : Expr) (ps : Array Name) : PremiseUse :=
  let direct : NameSet := val.getUsedConstants.foldl (·.insert ·) {}
  let viaNew := reach env direct (!env0.contains ·)
  let viaAll := reach env direct fun c => !env0.contains c || c.isInternalDetail
  { used := ps.filter direct.contains
    viaAux := ps.filter fun p => !direct.contains p && viaNew.contains p
    viaInternal := ps.filter fun p => !viaNew.contains p && viaAll.contains p
    viaEq := ps.filter fun p => !viaAll.contains p && viaAll.toList.any (isEqLemmaOf p) }

/-- Runs `x` in the saved command state `s0`, discarding every effect on that state. -/
def inState (s0 : Command.State) (src : FileMap) (fileName : String) (tk : IO.CancelToken)
    (x : TermElabM α) : IO (Except String α) := do
  let ctx : Command.Context := {
    fileName, fileMap := src, cmdPos := 0, snap? := none, cancelTk? := some tk }
  let s0 := { s0 with messages := {} }
  match ← (EIO.toIO' ((Command.liftTermElabM x) ctx |>.run s0)) with
  | .ok (a, _) => return .ok a
  | .error e => return .error (← e.toMessageData.toString)

def errorsOf (log : MessageLog) : IO String := do
  for m in log.toList do
    if m.severity == .error then return (← m.data.toString).take 200 |>.toString
  return ""

/-- Elaborates and runs `tac` on goal `type`; see the module docstring for what counts. -/
def attempt (type : Expr) (lps : List Name) (tacStx : Syntax) (hb : Nat) (intro : Bool)
    (ps : Array Name := #[]) : TermElabM Outcome := do
  let env0 ← getEnv
  let goal ← mkFreshExprMVar type .syntheticOpaque
  let saved ← Core.getMessageLog
  Core.resetMessageLog
  let run : TermElabM Outcome := do
    let tac : Tactic.TacticM Unit := do
      if intro then Tactic.evalTactic (← `(tactic| intros))
      Tactic.evalTactic tacStx
    let rest ← Term.withoutErrToSorry <| Tactic.run goal.mvarId! tac
    Term.synthesizeSyntheticMVarsNoPostponing
    let errs ← errorsOf (← Core.getMessageLog)
    if errs != "" then return { closed := false, err := errs }
    if !rest.isEmpty then return { closed := false, err := "goals remain", remaining := rest.length }
    let val ← instantiateMVars goal
    if val.hasSorry then return { closed := false, err := "sorry" }
    if val.hasExprMVar || val.hasLevelMVar then return { closed := false, err := "metavariables" }
    let n := (← getEnv).mainModule ++ `_closure_check
    addDecl (.thmDecl { name := n, levelParams := lps, type, value := val })
    let errs ← errorsOf (← Core.getMessageLog)
    if errs != "" then return { closed := false, err := s!"kernel: {errs}" }
    let u := premiseUse (← getEnv) env0 val ps
    return { closed := true, used := u.used, usedViaAux := u.viaAux,
             usedViaInternal := u.viaInternal, usedViaEq := u.viaEq }
  let r ← withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) <|
    Core.withCurrHeartbeats <|
      tryCatchRuntimeEx run fun e => do
        return { closed := false, err := ((← e.toMessageData.toString).take 200).toString }
  Core.setMessageLog saved
  return r

def main (args : List String) : IO UInt32 := do
  let [srcPath, modName, tasksPath, outPath, hbStr, toStr] := args
    | IO.eprintln "usage: Closure SRC MODULE TASKS OUT HEARTBEATS TIMEOUT-MS"; return 2
  let hb := hbStr.toNat!
  let timeoutMs := toStr.toNat!
  -- Targets, in file order.
  let mut targets : Std.HashMap String Target := {}
  for line in (← IO.FS.lines tasksPath) do
    let fs := line.splitOn "\t"
    if fs.length < 2 then continue
    let thm := fs[0]!
    let ps := (fs.getD 2 "").splitOn "," |>.filter (· ≠ "") |>.map (·.splitOn "|" |>.toArray)
    let t := targets.getD thm { thm, conds := #[] }
    targets := targets.insert thm { t with conds := t.conds.push { name := fs[1]!, premises := ps.toArray } }
  let out ← IO.FS.Handle.mk outPath .write
  let emit (s : String) : IO Unit := do out.putStrLn s; out.flush
  let wd ← Watchdog.start
  unsafe Lean.enableInitializersExecution
  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile srcPath
  let inputCtx := Parser.mkInputContext input srcPath
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let mainModule := modName.toName
  let opts : Options := ({} : Options)
    |>.set `autoImplicit false |>.set `maxSynthPendingDepth (3 : Nat)
    |>.set `pp.unicode.fun true |>.set `Elab.async false
  let t0 ← IO.monoMsNow
  let (env, messages) ← Elab.processHeader header opts messages inputCtx (mainModule := mainModule)
  if messages.hasErrors then
    IO.eprintln s!"header errors: {← errorsOf messages}"
    return 1
  IO.eprintln s!"imported in {(← IO.monoMsNow) - t0} ms"
  let cmdState := Command.mkState env messages opts
  let fileMap := inputCtx.fileMap
  -- Resolves a printed name against an environment; private and escaped names fall back to a
  -- scan of the module's own constants.
  let resolve (env : Environment) (s : String) : IO (Option Name) := do
    let n := s.toName
    if !n.isAnonymous && n.toString == s && env.contains n then return some n
    let hit := env.constants.map₂.foldl (init := none) fun acc k _ =>
      if acc.isNone && k.toString == s then some k else acc
    return hit
  -- Imported constants with names that do not round-trip through `String.toName`.
  let importIndex : Std.HashMap String Name := env.constants.map₁.fold (init := {}) fun m k _ =>
    if k.toString.toName == k then m else m.insert k.toString k
  let resolveP (env : Environment) (s : String) : IO (Option Name) := do
    if let some n ← resolve env s then return some n
    if let some n := importIndex.get? s then if env.contains n then return some n
    return none
  let mut st : Elab.Frontend.State := { commandState := cmdState, parserState, cmdPos := parserState.pos }
  let mut remaining := targets
  let mut commands := 0
  let mut elabMs := 0
  let mut attemptMs := 0
  let mut done := false
  while !done && !remaining.isEmpty do
    let pre := st.commandState
    let c0 ← IO.monoMsNow
    let (isEnd, st') ← (Elab.Frontend.processCommand { inputCtx }).run st
    elabMs := elabMs + ((← IO.monoMsNow) - c0)
    st := st'
    done := isEnd
    commands := commands + 1
    let post := st.commandState.env
    let preEnv := pre.env
    -- Targets declared by this command.
    let mut found : Array (Target × Name) := #[]
    for (s, t) in remaining.toList do
      if let some n ← resolve post s then
        if !preEnv.contains n then found := found.push (t, n)
    for (t, n) in found do
      remaining := remaining.erase t.thm
      let some ci := post.find? n | continue
      let type := ci.type
      let fresh := type.getUsedConstants.filter (!preEnv.contains ·)
      if !fresh.isEmpty then
        for c in t.conds do
          emit s!"\{\"thm\":{jsonStr t.thm},\"cond\":{jsonStr c.name},\"status\":\"skipped\",\"reason\":\"type uses constants of the same command\",\"fresh\":{jsonStr (toString fresh.toList)}}"
        continue
      let a0 ← IO.monoMsNow
      -- Premise usability per tactic, memoized across conditions of this theorem.
      let mut usable : Std.HashMap (String × Name) Bool := {}
      -- Results memoized by the exact premise list each tactic receives.
      let mut memo : Std.HashMap (String × List Name) (Outcome × Nat) := {}
      for c in t.conds do
        let mut present : Array Name := #[]
        let mut missing := 0
        for alts in c.premises do
          let mut hit : Option Name := none
          for a in alts do
            if hit.isNone then
              if let some p ← resolveP preEnv a then hit := some p
          match hit with
          | some p => if !present.contains p && p != n then present := present.push p
          | none => missing := missing + 1
        let mut closedBy := ""
        let mut closing : Outcome := { closed := false }
        let mut tried : Array String := #[]
        let mut totalMs := 0
        for tac in tacticNames do
          let mut ps : Array Name := #[]
          for p in present do
            let key := (tac, p)
            let ok ← match usable.get? key with
              | some b => pure b
              | none => do
                let txt := tacticText tac 1
                let ok ← match Parser.runParserCategory preEnv `tactic txt with
                  | .error _ => pure false
                  | .ok stx =>
                    let tk ← IO.CancelToken.new
                    wd.slot.set (some ((← IO.monoMsNow) + timeoutMs, tk))
                    let r ← inState pre fileMap srcPath tk
                      (attempt (mkConst ``True) [] (substPremises stx #[p]) hb false)
                    wd.slot.set none
                    pure <| match r with
                      | .ok o => o.closed
                      | .error _ => false
                pure ok
            usable := usable.insert key ok
            if ok then ps := ps.push p
          let mkey := (tac, ps.toList)
          let (o, ms) ← match memo.get? mkey with
            | some r => pure r
            | none => do
              let r ← match Parser.runParserCategory preEnv `tactic (tacticText tac ps.size) with
                | .error e => pure ({ closed := false, err := s!"parse: {e}" }, 0)
                | .ok stx => do
                  let tk ← IO.CancelToken.new
                  let s0 ← IO.monoMsNow
                  wd.slot.set (some (s0 + timeoutMs, tk))
                  let r ← inState pre fileMap srcPath tk
                    (attempt type ci.levelParams (substPremises stx ps) hb true ps)
                  wd.slot.set none
                  let ms := (← IO.monoMsNow) - s0
                  let o := match r with
                    | .ok o => o
                    | .error e => { closed := false, err := e.take 200 |>.toString }
                  let o := if (← tk.isSet) && !o.closed then { o with err := s!"timeout: {o.err}" } else o
                  pure (o, ms)
              memo := memo.insert mkey r
              pure r
          totalMs := totalMs + ms
          let useJson := if o.closed then
              s!",\"used\":{names o.used},\"usedViaAux\":{names o.usedViaAux},\"usedViaInternal\":{names o.usedViaInternal},\"usedViaEq\":{names o.usedViaEq}"
            else ""
          tried := tried.push s!"\{\"tactic\":\"{tac}\",\"premises\":{ps.size},\"closed\":{o.closed},\"ms\":{ms},\"err\":{jsonStr o.err}{useJson}}"
          if o.closed then
            closedBy := tac
            closing := o
            break
        let status := if closedBy != "" then "closed" else "failed"
        emit s!"\{\"thm\":{jsonStr t.thm},\"cond\":{jsonStr c.name},\"status\":\"{status}\",\"tactic\":{jsonStr closedBy},\"ms\":{totalMs},\"given\":{c.premises.size},\"accessible\":{present.size},\"missing\":{missing},\"used\":{names closing.used},\"usedViaAux\":{names closing.usedViaAux},\"usedViaInternal\":{names closing.usedViaInternal},\"usedViaEq\":{names closing.usedViaEq},\"attempts\":[{",".intercalate tried.toList}]}"
      attemptMs := attemptMs + ((← IO.monoMsNow) - a0)
  for (s, t) in remaining.toList do
    for c in t.conds do
      emit s!"\{\"thm\":{jsonStr s},\"cond\":{jsonStr c.name},\"status\":\"skipped\",\"reason\":\"not declared by any command\"}"
  IO.eprintln s!"commands {commands} elab {elabMs} ms attempts {attemptMs} ms errors {st.commandState.messages.hasErrors}"
  -- The watchdog thread would otherwise keep the process alive.
  IO.Process.exit 0
