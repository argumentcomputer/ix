import IxCC.Anf.Defun.Narrow

/-! # Untrusted 0-CFA closure flow analysis (P9 oracle)

`Flow.analyse P maxArms` computes a closed-world monovariant closure-flow
summary (`Narrow.Cert`) over a `FirstOrder` post-P8 Anf program:

* Each global parameter, global return, constructor field, join parameter, and
  narrowed dispatch-site return carries an abstract closure-key set (`Abs`,
  indices into `P.ctors`), widened to `none` (⊤) past `maxSet` keys.
* At a dispatch site `call (dispatch m) (f :: as)` whose callee flow has
  `≤ maxArms` keys (and fewer than the dispatcher's alternatives), the solver
  abstractly evaluates ONLY those reachable dispatcher arms, preserving
  site-specific argument and return precision without mega-dispatcher pollution.
* Unnarrowed dispatch sites mark their dispatcher as active so its full body is
  included in the fixpoint.

**Untrusted (outside TCB):** `Flow.lean` carries zero proofs. Its output is
validated by `Narrow.run` (which is proved sound for *any* certificate in
`Anf/Proof/Defun/Narrow.lean`). Pure and deterministic (no `HashMap` iteration
order dependence), so producer and replay see identical certificates. -/

namespace IxCC.Anf.Defun.Flow

open Narrow (Abs Cert)

/-- Maximum closure keys tracked per abstract value before widening to ⊤. -/
def maxFlowSet : Nat := 16

/-- Maximum fixpoint iterations. -/
def maxIters : Nat := 32

def absBot : Abs := some []

def absJoin (a b : Abs) : Abs :=
  match a, b with
  | none, _ | _, none => none
  | some xs, some ys =>
    let u := ys.foldl (fun acc y => if acc.contains y then acc else acc ++ [y]) xs
    if u.length ≤ maxFlowSet then some u else none

def absEq : Abs → Abs → Bool
  | none, none => true
  | some xs, some ys => xs.length == ys.length && xs.all (ys.contains ·)
  | _, _ => false

def absListEq : List Abs → List Abs → Bool
  | [], [] => true
  | a :: as, b :: bs => absEq a b && absListEq as bs
  | _, _ => false

def absListJoin : List Abs → List Abs → List Abs
  | [], [] => []
  | a :: as, b :: bs => absJoin a b :: absListJoin as bs
  | as, [] => as
  | [], bs => bs

def findCtorIdx (ctors : Array Lam.CtorInfo) (k : Key.CtorKey) : Option Nat :=
  ctors.findIdx? fun info => decide (info.key = k)

def dedupNatsAux (seen : List Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
    if seen.contains x then dedupNatsAux seen xs
    else x :: dedupNatsAux (x :: seen) xs

def dedupNats (xs : List Nat) : List Nat := dedupNatsAux [] xs

/-- Solver state threaded across fixpoint iterations. -/
structure St where
  params : Src.NatMap (List Abs) := .leaf
  rets : Src.NatMap Abs := .leaf
  fields : Src.NatMap (List Abs) := .leaf
  /-- Per global, array of join parameter flow lists indexed by pre-order join id. -/
  joins : Src.NatMap (Array (List Abs)) := .leaf
  /-- Per global, array of narrowed-site return flows indexed by pre-order site id. -/
  siteRets : Src.NatMap (Array Abs) := .leaf
  usedDisps : Src.NatSet := .leaf
  changed : Bool := false

def getParamFlows (st : St) (g : GlobalId) (n : Nat) : List Abs :=
  match st.params.get? g with
  | some ps => if ps.length == n then ps else List.replicate n absBot
  | none => List.replicate n absBot

def getRetFlow (st : St) (g : GlobalId) : Abs :=
  (st.rets.get? g).getD absBot

def getFieldFlow (st : St) (ci : Option Nat) (i : Nat) : Abs :=
  match ci with
  | none => absBot
  | some idx => ((st.fields.get? idx).getD []).getD i absBot

def getFieldFlows (st : St) (ci : Option Nat) (n : Nat) : List Abs :=
  (List.range n).map (getFieldFlow st ci)

def joinParams (st : St) (g : GlobalId) (afs : List Abs) : St :=
  let old := getParamFlows st g afs.length
  let nw := absListJoin old afs
  if absListEq old nw then st
  else { st with params := st.params.insert g nw, changed := true }

def joinRet (st : St) (g : GlobalId) (r : Abs) : St :=
  let old := getRetFlow st g
  let nw := absJoin old r
  if absEq old nw then st
  else { st with rets := st.rets.insert g nw, changed := true }

def joinFields (st : St) (ci : Nat) (afs : List Abs) : St :=
  let old := (st.fields.get? ci).getD (List.replicate afs.length absBot)
  let old' := if old.length < afs.length then old ++ List.replicate (afs.length - old.length) absBot else old
  let nw := absListJoin old' afs
  if absListEq old' nw && old.length ≥ afs.length then st
  else { st with fields := st.fields.insert ci nw, changed := true }

def markDisp (st : St) (d : GlobalId) : St :=
  if st.usedDisps.contains d then st
  else { st with usedDisps := st.usedDisps.insert d, changed := true }

def getJoinFlow (st : St) (g : GlobalId) (jid n : Nat) : List Abs :=
  let arr := (st.joins.get? g).getD #[]
  match arr[jid]? with
  | some ps => if ps.length == n then ps else List.replicate n absBot
  | none => List.replicate n absBot

def joinJoinFlow (st : St) (g : GlobalId) (jid : Nat) (afs : List Abs) : St :=
  let arr := (st.joins.get? g).getD #[]
  let arr := if jid < arr.size then arr else arr ++ Array.replicate (jid + 1 - arr.size) (List.replicate afs.length absBot)
  let old := arr[jid]!
  let old := if old.length == afs.length then old else List.replicate afs.length absBot
  let nw := absListJoin old afs
  if absListEq old nw then st
  else { st with joins := st.joins.insert g (arr.set! jid nw), changed := true }

def getSiteRet (st : St) (g : GlobalId) (sid : Nat) : Abs :=
  ((st.siteRets.get? g).getD #[]).getD sid absBot

def joinSiteRet (st : St) (g : GlobalId) (sid : Nat) (r : Abs) : St :=
  let arr := (st.siteRets.get? g).getD #[]
  let arr := if sid < arr.size then arr else arr ++ Array.replicate (sid + 1 - arr.size) absBot
  let old := arr[sid]!
  let nw := absJoin old r
  if absEq old nw then st
  else { st with siteRets := st.siteRets.insert g (arr.set! sid nw), changed := true }

def atomAbs (env : List Abs) : Atom → Abs
  | .var i => (env[i]?).getD none
  | .lit _ => absBot
  | .box => absBot

def atomsAbs (env : List Abs) : List Atom → List Abs
  | [] => []
  | a :: as => atomAbs env a :: atomsAbs env as

/-- Abstractly evaluate a plain binding, updating `st` and returning its result flow. -/
def stepBindPlain (P : Program) (ctors : Array Lam.CtorInfo) (env : List Abs) (b : Bind) (st : St) :
    Abs × St :=
  match b with
  | .atom a => (atomAbs env a, st)
  | .con c as =>
    let afs := atomsAbs env as
    let ci := findCtorIdx ctors c
    let st := match ci with
      | some idx => joinFields st idx afs
      | none => st
    let rf := match c, ci with
      | .clo .., some idx => some [idx]
      | .clo .., none => none
      | .src _, _ => absBot
    (rf, st)
  | .proj c i _ => (getFieldFlow st (findCtorIdx ctors c) i, st)
  | .prim _ _ => (absBot, st)
  | .glob g =>
    match P.global? g with
    | some gd =>
      if gd.ps.isEmpty then
        let st := if Walk.isDispatchKey gd.key then markDisp st g else st
        (getRetFlow st g, st)
      else (none, st)
    | none => (absBot, st)
  | .call g as =>
    match P.global? g with
    | some gd =>
      if as.length == gd.ps.length then
        let st := joinParams st g (atomsAbs env as)
        let st := if Walk.isDispatchKey gd.key then markDisp st g else st
        (getRetFlow st g, st)
      else (absBot, st)
    | none => (absBot, st)
  | .app .. | .fn .. => (none, st)

mutual

/-- Abstractly evaluate a plain expression (dispatcher body or narrowed arm),
joining return values via `onRet`. -/
def stepExpPlain (P : Program) (ctors : Array Lam.CtorInfo) (onRet : St → Abs → St)
    (env : List Abs) (jenv : List (List Abs)) (st : St) : Exp → St
  | .bind _ b e =>
    let (bf, st) := stepBindPlain P ctors env b st
    stepExpPlain P ctors onRet (bf :: env) jenv st e
  | .join n r b e =>
    let ps := List.replicate n (none : Abs)
    let st := stepExpPlain P ctors onRet (ps.reverse ++ env) (if r then ps :: jenv else jenv) st b
    stepExpPlain P ctors onRet env (ps :: jenv) st e
  | .jump _ _ => st
  | .case _ alts dflt =>
    let st := stepAltsPlain P ctors onRet env jenv st alts
    stepOptPlain P ctors onRet env jenv st dflt
  | .ret a => onRet st (atomAbs env a)
  | .tick e => stepExpPlain P ctors onRet env jenv st e
  | .trap => st

def stepAltsPlain (P : Program) (ctors : Array Lam.CtorInfo) (onRet : St → Abs → St)
    (env : List Abs) (jenv : List (List Abs)) (st : St) : List Alt → St
  | [] => st
  | .mk c n b :: rest =>
    let ffs := getFieldFlows st (findCtorIdx ctors c) n
    let st := stepExpPlain P ctors onRet (ffs.reverse ++ env) jenv st b
    stepAltsPlain P ctors onRet env jenv st rest

def stepOptPlain (P : Program) (ctors : Array Lam.CtorInfo) (onRet : St → Abs → St)
    (env : List Abs) (jenv : List (List Abs)) (st : St) : Option Exp → St
  | none => st
  | some e => stepExpPlain P ctors onRet env jenv st e

end

/-- Check whether every key in `ks` yields an instantiable arm in `dispAlts`. -/
def canNarrowArms (ctors : Array Lam.CtorInfo) (dispAlts : List Alt) (args : List Atom)
    (contJump : Bool) : List Nat → Bool
  | [] => true
  | ci :: rest =>
    match ctors[ci]? with
    | none => false
    | some info =>
      match dispAlts.filter fun a => decide (a.key = info.key) with
      | [] => canNarrowArms ctors dispAlts args contJump rest
      | [.mk _ nf altBody] =>
        (Narrow.instExp args nf contJump 0 0 altBody).isSome &&
          canNarrowArms ctors dispAlts args contJump rest
      | _ :: _ :: _ => false

mutual

/-- Abstractly evaluate a non-dispatcher global's body, tracking pre-order join
indices (`jid`) and dispatch-site indices (`sid`), and evaluating only reachable
arms at narrowable dispatch sites. -/
def stepExp (P : Program) (ctors : Array Lam.CtorInfo) (maxArms : Nat) (curG : GlobalId)
    (env : List Abs) (jenv : List (Nat × Nat)) (jid sid : Nat) (st : St) :
    Exp → Nat × Nat × St
  | .bind _ b body =>
    match b with
    | .call d (f :: as) =>
      let narrowInfo : Option (List Alt × List Nat × Bool) :=
        match P.global? d with
        | some gd =>
          if Walk.isDispatchKey gd.key && gd.ps.length == as.length + 1 then
            match gd.body with
            | .case (.var m) dispAlts none =>
              if m == as.length && Narrow.allCloAlts dispAlts then
                match atomAbs env f with
                | some ks =>
                  let ks' := dedupNats ks
                  let tail := Narrow.isTailRet body
                  if ks'.length ≤ maxArms && ks'.length < dispAlts.length &&
                      canNarrowArms ctors dispAlts (f :: as) (!tail) ks' then
                    some (dispAlts, ks', tail)
                  else none
                | none => none
              else none
            | _ => none
          else none
        | none => none
      match narrowInfo with
      | some (dispAlts, ks', tail) =>
        let argFlows := atomAbs env f :: atomsAbs env as
        let st := ks'.foldl (fun st ci =>
          match ctors[ci]? with
          | none => st
          | some info =>
            match dispAlts.find? fun a => decide (a.key = info.key) with
            | none => st
            | some (.mk _ nf altBody) =>
              let ffs := getFieldFlows st (some ci) nf
              stepExpPlain P ctors (fun st r => joinSiteRet st curG sid r)
                (ffs.reverse ++ argFlows.reverse) [] st altBody) st
        let sret := getSiteRet st curG sid
        let st := if tail then joinRet st curG sret else st
        if tail then (jid, sid + 1, st)
        else stepExp P ctors maxArms curG (sret :: env) jenv jid (sid + 1) st body
      | none =>
        let (bf, st) := stepBindPlain P ctors env (.call d (f :: as)) st
        stepExp P ctors maxArms curG (bf :: env) jenv jid (sid + 1) st body
    | _ =>
      let (bf, st) := stepBindPlain P ctors env b st
      stepExp P ctors maxArms curG (bf :: env) jenv jid sid st body
  | .join n r b body =>
    let ps := getJoinFlow st curG jid n
    let (jid1, sid1, st1) := stepExp P ctors maxArms curG (ps.reverse ++ env)
      (if r then (jid, n) :: jenv else jenv) (jid + 1) sid st b
    stepExp P ctors maxArms curG env ((jid, n) :: jenv) jid1 sid1 st1 body
  | .jump j as =>
    let st := match jenv[j]? with
      | some (origJid, n) =>
        if as.length == n then joinJoinFlow st curG origJid (atomsAbs env as) else st
      | none => st
    (jid, sid, st)
  | .case _ alts dflt =>
    let (jid1, sid1, st1) := stepAlts P ctors maxArms curG env jenv jid sid st alts
    stepOpt P ctors maxArms curG env jenv jid1 sid1 st1 dflt
  | .ret a => (jid, sid, joinRet st curG (atomAbs env a))
  | .tick e => stepExp P ctors maxArms curG env jenv jid sid st e
  | .trap => (jid, sid, st)

def stepAlts (P : Program) (ctors : Array Lam.CtorInfo) (maxArms : Nat) (curG : GlobalId)
    (env : List Abs) (jenv : List (Nat × Nat)) (jid sid : Nat) (st : St) :
    List Alt → Nat × Nat × St
  | [] => (jid, sid, st)
  | .mk c n b :: rest =>
    let ffs := getFieldFlows st (findCtorIdx ctors c) n
    let (jid1, sid1, st1) := stepExp P ctors maxArms curG (ffs.reverse ++ env) jenv jid sid st b
    stepAlts P ctors maxArms curG env jenv jid1 sid1 st1 rest

def stepOpt (P : Program) (ctors : Array Lam.CtorInfo) (maxArms : Nat) (curG : GlobalId)
    (env : List Abs) (jenv : List (Nat × Nat)) (jid sid : Nat) (st : St) :
    Option Exp → Nat × Nat × St
  | none => (jid, sid, st)
  | some e => stepExp P ctors maxArms curG env jenv jid sid st e

end

/-- One full iteration over all non-dispatcher globals and active dispatchers. -/
def iterOnce (P : Program) (ctors : Array Lam.CtorInfo) (maxArms : Nat) (st : St) : St :=
  let st := { st with changed := false }
  let st := P.roots.foldl (fun st r =>
    match P.global? r with
    | some gd => if Walk.isDispatchKey gd.key then markDisp st r else st
    | none => st) st
  P.globalList.foldl (fun st (g, gd) =>
    if Walk.isDispatchKey gd.key then
      if st.usedDisps.contains g then
        let pfs := getParamFlows st g gd.ps.length
        stepExpPlain P ctors (fun st r => joinRet st g r) pfs.reverse [] st gd.body
      else st
    else
      let pfs := getParamFlows st g gd.ps.length
      (stepExp P ctors maxArms g pfs.reverse [] 0 0 st gd.body).2.2) st

/-- Run the fixpoint solver up to `fuel` iterations. -/
def solve (P : Program) (ctors : Array Lam.CtorInfo) (maxArms : Nat) : Nat → St → St
  | 0, st => st
  | fuel + 1, st =>
    let st' := iterOnce P ctors maxArms st
    if st'.changed then solve P ctors maxArms fuel st' else st'

mutual

/-- Extract the exact `joins` and `siteRets` queues for global `g` in the exact
order `Narrow.checkRewriteExp` consumes them. -/
def extractExp (P : Program) (ctors : Array Lam.CtorInfo) (maxArms : Nat) (st : St)
    (curG : GlobalId) (env : List Abs) (jid sid : Nat) (jsAcc : List (List Abs))
    (srAcc : List Abs) : Exp → Nat × Nat × List (List Abs) × List Abs
  | .bind _ b body =>
    match b with
    | .call d (f :: as) =>
      let narrowInfo : Option (List Nat × Bool) :=
        match P.global? d with
        | some gd =>
          if Walk.isDispatchKey gd.key && gd.ps.length == as.length + 1 then
            match gd.body with
            | .case (.var m) dispAlts none =>
              if m == as.length && Narrow.allCloAlts dispAlts then
                match atomAbs env f with
                | some ks =>
                  let ks' := dedupNats ks
                  let tail := Narrow.isTailRet body
                  if ks'.length ≤ maxArms && ks'.length < dispAlts.length &&
                      canNarrowArms ctors dispAlts (f :: as) (!tail) ks' then
                    some (ks', tail)
                  else none
                | none => none
              else none
            | _ => none
          else none
        | none => none
      match narrowInfo with
      | some (_, tail) =>
        let sret := getSiteRet st curG sid
        let srAcc := srAcc ++ [sret]
        if tail then (jid, sid + 1, jsAcc, srAcc)
        else extractExp P ctors maxArms st curG (sret :: env) jid (sid + 1) jsAcc srAcc body
      | none =>
        let (bf, _) := stepBindPlain P ctors env (.call d (f :: as)) st
        extractExp P ctors maxArms st curG (bf :: env) jid (sid + 1) jsAcc srAcc body
    | _ =>
      let (bf, _) := stepBindPlain P ctors env b st
      extractExp P ctors maxArms st curG (bf :: env) jid sid jsAcc srAcc body
  | .join n _ b body =>
    let ps := getJoinFlow st curG jid n
    let (jid1, sid1, js1, sr1) :=
      extractExp P ctors maxArms st curG (ps.reverse ++ env) (jid + 1) sid (jsAcc ++ [ps]) srAcc b
    extractExp P ctors maxArms st curG env jid1 sid1 js1 sr1 body
  | .case _ alts dflt =>
    let (jid1, sid1, js1, sr1) := extractAlts P ctors maxArms st curG env jid sid jsAcc srAcc alts
    extractOpt P ctors maxArms st curG env jid1 sid1 js1 sr1 dflt
  | .tick e => extractExp P ctors maxArms st curG env jid sid jsAcc srAcc e
  | .jump .. | .ret _ | .trap => (jid, sid, jsAcc, srAcc)

def extractAlts (P : Program) (ctors : Array Lam.CtorInfo) (maxArms : Nat) (st : St)
    (curG : GlobalId) (env : List Abs) (jid sid : Nat) (jsAcc : List (List Abs))
    (srAcc : List Abs) : List Alt → Nat × Nat × List (List Abs) × List Abs
  | [] => (jid, sid, jsAcc, srAcc)
  | .mk c n b :: rest =>
    let ffs := getFieldFlows st (findCtorIdx ctors c) n
    let (jid1, sid1, js1, sr1) :=
      extractExp P ctors maxArms st curG (ffs.reverse ++ env) jid sid jsAcc srAcc b
    extractAlts P ctors maxArms st curG env jid1 sid1 js1 sr1 rest

def extractOpt (P : Program) (ctors : Array Lam.CtorInfo) (maxArms : Nat) (st : St)
    (curG : GlobalId) (env : List Abs) (jid sid : Nat) (jsAcc : List (List Abs))
    (srAcc : List Abs) : Option Exp → Nat × Nat × List (List Abs) × List Abs
  | none => (jid, sid, jsAcc, srAcc)
  | some e => extractExp P ctors maxArms st curG env jid sid jsAcc srAcc e

end

/-- **Untrusted flow analysis**: compute a compact `Narrow.Cert` for `P`
reporting `≤ maxArms` (default 4) reachable closure keys per narrowable
dispatch site. Returns `none` if no dispatch site can be narrowed or if the
solver exceeds certificate bounds. -/
def analyse (P : Program) (maxArms : Nat := 4) : Option Cert :=
  if !firstOrder P || Defun.knownClosure P.known then none
  else if !P.globalList.any (fun (_, gd) => Walk.isDispatchKey gd.key) then none
  else
    let ctors := P.ctors.toArray
    let st := solve P ctors maxArms maxIters {}
    let params := P.globalList.filterMap fun (g, gd) =>
      let ps := getParamFlows st g gd.ps.length
      if P.roots.contains g then
        if ps.all (absEq · absBot) then none else some (g, ps)
      else if ps.all (·.isNone) then none else some (g, ps)
    let rets := P.globalList.filterMap fun (g, _) =>
      let r := getRetFlow st g
      if r.isNone then none else some (g, r)
    let fields := (List.range ctors.size).filterMap fun ci =>
      match st.fields.get? ci with
      | some fs => if fs.all (absEq · absBot) then none else some (ci, fs)
      | none => none
    let (joins, siteRets, anyNarrow) := P.globalList.foldl (init := ([], [], false))
      fun (jsOut, srOut, any) (g, gd) =>
        if Walk.isDispatchKey gd.key then (jsOut, srOut, any)
        else
          let pfs := getParamFlows st g gd.ps.length
          let (_, _, js, srs) := extractExp P ctors maxArms st g pfs.reverse 0 0 [] [] gd.body
          let jsOut := if js.isEmpty then jsOut else jsOut ++ [(g, js)]
          let srOut := if srs.isEmpty then srOut else srOut ++ [(g, srs)]
          (jsOut, srOut, any || !srs.isEmpty)
    if !anyNarrow then none
    else
      let cert : Cert := { maxArms, params, rets, fields, joins, siteRets }
      if Narrow.checkCert cert then some cert else none

end IxCC.Anf.Defun.Flow
