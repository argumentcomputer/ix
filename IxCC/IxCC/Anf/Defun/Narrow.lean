import IxCC.Anf.Defun
import IxCC.Anf.Walk
import IxCC.Anf.WellFormed

/-! # P9: flow-directed dispatch narrowing

`Narrow.run` validates a compact closed-world closure-flow summary (`Cert`,
produced by the untrusted solver `Anf.Defun.Flow.analyse`) in one linear pass
over a `FirstOrder` program, and rewrites every dispatch call
`call (dispatch m) (f :: as)` whose checked closure-key set `ks` has
`ks.length ≤ maxArms` (default 4) and strictly fewer alternatives than the
dispatcher into a short `case f [...] none` (no default arm, so
`Rt.checkSwitches` and `Own.Plain` accept it unchanged).

Because the flow summary is validated before narrowing (and `Narrow.run` leaves
the program unchanged if validation fails), **soundness holds for ANY
certificate** (`Narrow.Proof.run_refines`): a dishonest or stale flow oracle
can cost speed only, never correctness, and `Flow.lean` stays outside the TCB.

Kernel-evaluable: lists, `Src.NatMap`, structural recursion. -/

namespace IxCC.Anf.Defun.Narrow

/-- Abstract closure-key upper bound in certificate form: `none` is ⊤
(unconstrained), `some idxs` restricts closure keys to `P.ctors[i].key` for
`i ∈ idxs`. -/
abbrev Abs := Option (List Nat)

/-- Decoded abstract closure-key upper bound over constructor keys. -/
abbrev KAbs := Option (List Key.CtorKey)

/-- Untrusted flow summary certificate for P9 dispatch narrowing. All keys are
encoded as indices into `P.ctors` (plain `Nat`s). -/
structure Cert where
  /-- Maximum narrowed arms per dispatch site (`D`, default 4). -/
  maxArms : Nat := 4
  /-- Parameter flows per global id (roots default to `some []`, others to `none`). -/
  params : List (GlobalId × List Abs) := []
  /-- Return flows per global id (omitted defaults to `none`). -/
  rets : List (GlobalId × Abs) := []
  /-- Constructor field flows per `P.ctors` index (omitted defaults to `some []`). -/
  fields : List (Nat × List Abs) := []
  /-- Join-point parameter flows per global id, in pre-order of `join` nodes. -/
  joins : List (GlobalId × List (List Abs)) := []
  /-- Site return flows per global id, in pre-order of narrowed dispatch sites. -/
  siteRets : List (GlobalId × List Abs) := []
  deriving Inhabited

/-- Resource bounds on a P9 certificate (checked by `CertJson` and `checkMidCert`). -/
def maxCertGlobals : Nat := 100000
def maxCertFields : Nat := 4096
def maxCertKeys : Nat := 32
def maxCertArms : Nat := 16
def maxCertList : Nat := 4096

def checkAbs (a : Abs) : Bool :=
  match a with
  | none => true
  | some ks => ks.length ≤ maxCertKeys

def checkCert (c : Cert) : Bool :=
  c.maxArms ≤ maxCertArms &&
  c.params.length ≤ maxCertGlobals &&
  c.params.all (fun (_, ps) => ps.length ≤ 256 && ps.all checkAbs) &&
  c.rets.length ≤ maxCertGlobals &&
  c.rets.all (fun (_, r) => checkAbs r) &&
  c.fields.length ≤ maxCertFields &&
  c.fields.all (fun (_, fs) => fs.length ≤ 256 && fs.all checkAbs) &&
  c.joins.length ≤ maxCertGlobals &&
  c.joins.all (fun (_, js) => js.length ≤ maxCertList && js.all fun ps => ps.length ≤ 256 && ps.all checkAbs) &&
  c.siteRets.length ≤ maxCertGlobals &&
  c.siteRets.all (fun (_, rs) => rs.length ≤ maxCertList && rs.all checkAbs)

/-! ## Decoded flow summary -/

def decodeAbs (ctors : List Lam.CtorInfo) : Abs → KAbs
  | none => none
  | some idxs =>
    if idxs.all (· < ctors.length) then
      some (idxs.filterMap fun i => (ctors[i]?).map (·.key))
    else none

/-- Decoded certificate over constructor keys. -/
structure DecCert where
  maxArms : Nat
  params : Src.NatMap (List KAbs)
  rets : Src.NatMap KAbs
  fields : List (Key.CtorKey × List KAbs)
  joins : Src.NatMap (List (List KAbs))
  siteRets : Src.NatMap (List KAbs)

def decode (P : Program) (c : Cert) : DecCert :=
  let d := decodeAbs P.ctors
  { maxArms := c.maxArms
    params := Src.NatMap.ofList (c.params.map fun (g, ps) => (g, ps.map d))
    rets := Src.NatMap.ofList (c.rets.map fun (g, r) => (g, d r))
    fields := c.fields.filterMap fun (idx, fs) => (P.ctors[idx]?).map fun info => (info.key, fs.map d)
    joins := Src.NatMap.ofList (c.joins.map fun (g, js) => (g, js.map (·.map d)))
    siteRets := Src.NatMap.ofList (c.siteRets.map fun (g, rs) => (g, rs.map d)) }

/-- Subset test on closure-key upper bounds. -/
def kabsSub : KAbs → KAbs → Bool
  | _, none => true
  | none, some _ => false
  | some xs, some ys => xs.all fun x => ys.any fun y => decide (x = y)

def kabsListSub : List KAbs → List KAbs → Bool
  | [], [] => true
  | a :: as, b :: bs => kabsSub a b && kabsListSub as bs
  | _, _ => false

/-- Parameter flows of global `g` of arity `n`: roots default to `some []`
(callers pass `Nat` literals, never closures); non-roots default to `none`. -/
def paramFlows (P : Program) (dc : DecCert) (g : GlobalId) (n : Nat) : List KAbs :=
  match dc.params.get? g with
  | some ps => if ps.length == n then ps else List.replicate n (if P.roots.contains g then some [] else none)
  | none => List.replicate n (if P.roots.contains g then some [] else none)

def retFlow (dc : DecCert) (g : GlobalId) : KAbs :=
  (dc.rets.get? g).getD none

def fieldFlow (dc : DecCert) (k : Key.CtorKey) (i : Nat) : KAbs :=
  match dc.fields.find? fun p => decide (p.1 = k) with
  | some (_, fs) => fs.getD i (some [])
  | none => some []

def fieldFlows (dc : DecCert) (k : Key.CtorKey) (n : Nat) : List KAbs :=
  (List.range n).map (fieldFlow dc k)

def atomFlow (env : List KAbs) : Atom → KAbs
  | .var i => (env[i]?).getD none
  | .lit _ => some []
  | .box => some []

def atomsFlow (env : List KAbs) : List Atom → List KAbs
  | [] => []
  | a :: as => atomFlow env a :: atomsFlow env as

/-! ## Instantiating a dispatcher arm at a call site -/

def shiftAtom (k : Nat) : Atom → Atom
  | .var i => .var (i + k)
  | a => a

/-- Substitute dispatcher parameter list `args` (of length `m + 1`) into an
atom inside a dispatcher alternative with `nf` fields and `depth` local
binders. Returns `none` if an out-of-scope variable is encountered. -/
def instAtom (args : List Atom) (nf depth : Nat) : Atom → Option Atom
  | .lit l => some (.lit l)
  | .box => some .box
  | .var i =>
    if i < depth + nf then some (.var i)
    else
      let k := i - (depth + nf)
      if k < args.length then
        (args[args.length - 1 - k]?).map (shiftAtom (depth + nf))
      else none

def instAtoms (args : List Atom) (nf depth : Nat) : List Atom → Option (List Atom)
  | [] => some []
  | a :: as => do
    let a' ← instAtom args nf depth a
    let as' ← instAtoms args nf depth as
    some (a' :: as')

mutual

/-- Instantiate a first-order dispatcher arm body at a call site with arguments
`args`. When `contJump` is `true`, every `ret a` becomes `jump jdepth [a']`
jumping to the outer continuation join point; when `false` (tail position), it
stays `ret a'`. -/
def instExp (args : List Atom) (nf : Nat) (contJump : Bool) (depth jdepth : Nat) : Exp → Option Exp
  | .bind c b e => do
    let b' ← instBind args nf depth b
    let e' ← instExp args nf contJump (depth + 1) jdepth e
    some (.bind c b' e')
  | .join ar r b e => do
    let b' ← instExp args nf contJump (depth + ar) (if r then jdepth + 1 else jdepth) b
    let e' ← instExp args nf contJump depth (jdepth + 1) e
    some (.join ar r b' e')
  | .jump j as =>
    if j < jdepth then do
      let as' ← instAtoms args nf depth as
      some (.jump j as')
    else none
  | .case x alts dflt => do
    let x' ← instAtom args nf depth x
    let alts' ← instAlts args nf contJump depth jdepth alts
    let dflt' ← instOpt args nf contJump depth jdepth dflt
    some (.case x' alts' dflt')
  | .ret a => do
    let a' ← instAtom args nf depth a
    if contJump then some (.jump jdepth [a']) else some (.ret a')
  | .tick e => do
    let e' ← instExp args nf contJump depth jdepth e
    some (.tick e')
  | .trap => some .trap

def instBind (args : List Atom) (nf depth : Nat) : Bind → Option Bind
  | .atom a => .atom <$> instAtom args nf depth a
  | .con c as => .con c <$> instAtoms args nf depth as
  | .proj c i x => .proj c i <$> instAtom args nf depth x
  | .prim p as => .prim p <$> instAtoms args nf depth as
  | .glob g => some (.glob g)
  | .call g as => .call g <$> instAtoms args nf depth as
  | .app .. | .fn .. => none

def instAlts (args : List Atom) (nf : Nat) (contJump : Bool) (depth jdepth : Nat) :
    List Alt → Option (List Alt)
  | [] => some []
  | .mk k n b :: rest => do
    let b' ← instExp args nf contJump (depth + n) jdepth b
    let rest' ← instAlts args nf contJump depth jdepth rest
    some (.mk k n b' :: rest')

def instOpt (args : List Atom) (nf : Nat) (contJump : Bool) (depth jdepth : Nat) :
    Option Exp → Option (Option Exp)
  | none => some none
  | some e => some <$> instExp args nf contJump depth jdepth e

end

/-! ## Checking a plain (unnarrowed) expression / dispatcher arm -/

/-- Whether every alternative in `alts` matches a closure constructor. -/
def allCloAlts : List Alt → Bool
  | [] => true
  | .mk (.clo ..) _ _ :: rest => allCloAlts rest
  | .mk (.src _) _ _ :: _ => false

/-- Deduplicate constructor keys, keeping first occurrence order (structurally recursive). -/
def dedupKeysAux (seen : List Key.CtorKey) : List Key.CtorKey → List Key.CtorKey
  | [] => []
  | k :: ks =>
    if seen.any fun s => decide (s = k) then dedupKeysAux seen ks
    else k :: dedupKeysAux (k :: seen) ks

def dedupKeys (ks : List Key.CtorKey) : List Key.CtorKey := dedupKeysAux [] ks

/-- Check a single binding's flow against `dc`, returning its result flow (and
whether a dispatcher call `d` was made unnarrowed, recorded in `used`). -/
def checkBindPlain (P : Program) (dc : DecCert) (env : List KAbs) (b : Bind) :
    Option (KAbs × List GlobalId) :=
  match b with
  | .atom a => some (atomFlow env a, [])
  | .con c as =>
    let afs := atomsFlow env as
    if kabsListSub afs (fieldFlows dc c as.length) then
      match c with
      | .clo .. => some (some [c], [])
      | .src _ => some (some [], [])
    else none
  | .proj c i _ => some (fieldFlow dc c i, [])
  | .prim _ _ => some (some [], [])
  | .glob g =>
    match P.global? g with
    | some gd => if gd.ps.isEmpty then some (retFlow dc g, [g]) else none
    | none => some (some [], [])
  | .call g as =>
    match P.global? g with
    | some gd =>
      if as.length == gd.ps.length then
        if kabsListSub (atomsFlow env as) (paramFlows P dc g gd.ps.length) then
          some (retFlow dc g, [g])
        else none
      else some (some [], [])
    | none => some (some [], [])
  | .app .. | .fn .. => none

mutual

/-- Flow-check a plain (non-narrowing) expression against `dc` and target return
flow `rflow`, returning the list of globals called/referenced by it. -/
def checkExpPlain (P : Program) (dc : DecCert) (rflow : KAbs) (env : List KAbs)
    (jenv : List (List KAbs)) : Exp → Option (List GlobalId)
  | .bind _ b e => do
    let (bf, u1) ← checkBindPlain P dc env b
    let u2 ← checkExpPlain P dc rflow (bf :: env) jenv e
    some (u1 ++ u2)
  | .join n r b e => do
    let ps := List.replicate n (none : KAbs)
    let u1 ← checkExpPlain P dc rflow (ps.reverse ++ env) (if r then ps :: jenv else jenv) b
    let u2 ← checkExpPlain P dc rflow env (ps :: jenv) e
    some (u1 ++ u2)
  | .jump j as =>
    match jenv[j]? with
    | some ps =>
      if as.length == ps.length && kabsListSub (atomsFlow env as) ps then some []
      else none
    | none => some []
  | .case _ alts dflt => do
    let u1 ← checkAltsPlain P dc rflow env jenv alts
    let u2 ← checkOptPlain P dc rflow env jenv dflt
    some (u1 ++ u2)
  | .ret a => if kabsSub (atomFlow env a) rflow then some [] else none
  | .tick e => checkExpPlain P dc rflow env jenv e
  | .trap => some []

def checkAltsPlain (P : Program) (dc : DecCert) (rflow : KAbs) (env : List KAbs)
    (jenv : List (List KAbs)) : List Alt → Option (List GlobalId)
  | [] => some []
  | .mk c n b :: rest => do
    let u1 ← checkExpPlain P dc rflow ((fieldFlows dc c n).reverse ++ env) jenv b
    let u2 ← checkAltsPlain P dc rflow env jenv rest
    some (u1 ++ u2)

def checkOptPlain (P : Program) (dc : DecCert) (rflow : KAbs) (env : List KAbs)
    (jenv : List (List KAbs)) : Option Exp → Option (List GlobalId)
  | none => some []
  | some e => checkExpPlain P dc rflow env jenv e

end

/-! ## Checking and narrowing a global's body in one synchronized pass -/

/-- Build and flow-check the narrowed alternatives for keys `ks` against
dispatcher `dispAlts`, site arguments `f :: as` (with flows `argFlows`), and
target site return flow `siteRet`. -/
def narrowArms (P : Program) (dc : DecCert) (dispAlts : List Alt) (args : List Atom)
    (argFlows : List KAbs) (contJump : Bool) (siteRet : KAbs) :
    List Key.CtorKey → Option (List Alt × List GlobalId)
  | [] => some ([], [])
  | ck :: rest =>
    match dispAlts.filter fun a => decide (a.key = ck) with
    | [] =>
      -- Key `ck` is not handled by `dispAlts` (so `dispAlts` is stuck on `ck`);
      -- omitting it from the narrowed case keeps `ck` stuck too!
      narrowArms P dc dispAlts args argFlows contJump siteRet rest
    | [.mk key nf altBody] => do
      let u1 ← checkExpPlain P dc siteRet ((fieldFlows dc key nf).reverse ++ argFlows.reverse) [] altBody
      let armBody ← instExp args nf contJump 0 0 altBody
      let (restAlts, u2) ← narrowArms P dc dispAlts args argFlows contJump siteRet rest
      some (.mk key nf armBody :: restAlts, u1 ++ u2)
    | _ :: _ :: _ => none

/-- Whether `body` is a simple tail return `ret (var 0)`. -/
def isTailRet : Exp → Bool
  | .ret (.var 0) => true
  | _ => false

/-- State threaded through `checkRewriteExp`: join-flow queue, site-return
queue, and globals called unnarrowed. -/
structure RwSt where
  joins : List (List KAbs)
  siteRets : List KAbs
  used : List GlobalId

mutual

/-- Flow-check and narrow an expression in one pass, returning the rewritten
expression and updated queues/used-globals. -/
def checkRewriteExp (P : Program) (dc : DecCert) (rflow : KAbs) (env : List KAbs)
    (jenv : List (List KAbs)) (st : RwSt) : Exp → Option (Exp × RwSt)
  | .bind c b body =>
    match b with
    | .call d (f :: as) =>
      let tried : Option (Exp × RwSt) :=
        match P.global? d with
        | some gd =>
          if Walk.isDispatchKey gd.key && gd.ps.length == as.length + 1 then
            match gd.body with
            | .case (.var m) dispAlts none =>
              if m == as.length && allCloAlts dispAlts then
                match atomFlow env f with
                | some ks =>
                  let ks' := dedupKeys ks
                  if ks'.length ≤ dc.maxArms && ks'.length < dispAlts.length then
                    let (siteRet, sRest) := match st.siteRets with
                      | r :: rs => (r, rs)
                      | [] => (none, [])
                    let tail := isTailRet body
                    let argFlows := atomFlow env f :: atomsFlow env as
                    match narrowArms P dc dispAlts (f :: as) argFlows (!tail) siteRet ks' with
                    | some (nAlts, uArms) =>
                      let st1 : RwSt := { st with siteRets := sRest, used := uArms ++ st.used }
                      if tail then
                        if kabsSub siteRet rflow then
                          some (.tick (.case f nAlts none), st1)
                        else none
                      else
                        match checkRewriteExp P dc rflow (siteRet :: env) jenv st1 body with
                        | some (body', st2) =>
                          some (.join 1 false body' (.tick (.case f nAlts none)), st2)
                        | none => none
                    | none => none
                  else none
                | none => none
              else none
            | _ => none
          else none
        | none => none
      match tried with
      | some res => some res
      | none => do
        let (bf, u1) ← checkBindPlain P dc env (.call d (f :: as))
        let (body', st') ← checkRewriteExp P dc rflow (bf :: env) jenv { st with used := u1 ++ st.used } body
        some (.bind c (.call d (f :: as)) body', st')
    | _ => do
      let (bf, u1) ← checkBindPlain P dc env b
      let (body', st') ← checkRewriteExp P dc rflow (bf :: env) jenv { st with used := u1 ++ st.used } body
      some (.bind c b body', st')
  | .join n r b body => do
    let (ps, jRest) := match st.joins with
      | p :: ps' => if p.length == n then (p, ps') else (List.replicate n none, ps')
      | [] => (List.replicate n none, [])
    let st1 := { st with joins := jRest }
    let (b', st2) ← checkRewriteExp P dc rflow (ps.reverse ++ env) (if r then ps :: jenv else jenv) st1 b
    let (body', st3) ← checkRewriteExp P dc rflow env (ps :: jenv) st2 body
    some (.join n r b' body', st3)
  | .jump j as =>
    match jenv[j]? with
    | some ps =>
      if as.length == ps.length && kabsListSub (atomsFlow env as) ps then some (.jump j as, st)
      else none
    | none => some (.jump j as, st)
  | .case x alts dflt => do
    let (alts', st1) ← checkRewriteAlts P dc rflow env jenv st alts
    let (dflt', st2) ← checkRewriteOpt P dc rflow env jenv st1 dflt
    some (.case x alts' dflt', st2)
  | .ret a =>
    if kabsSub (atomFlow env a) rflow then some (.ret a, st) else none
  | .tick e => do
    let (e', st') ← checkRewriteExp P dc rflow env jenv st e
    some (.tick e', st')
  | .trap => some (.trap, st)

def checkRewriteAlts (P : Program) (dc : DecCert) (rflow : KAbs) (env : List KAbs)
    (jenv : List (List KAbs)) (st : RwSt) : List Alt → Option (List Alt × RwSt)
  | [] => some ([], st)
  | .mk c n b :: rest => do
    let (b', st1) ← checkRewriteExp P dc rflow ((fieldFlows dc c n).reverse ++ env) jenv st b
    let (rest', st2) ← checkRewriteAlts P dc rflow env jenv st1 rest
    some (.mk c n b' :: rest', st2)

def checkRewriteOpt (P : Program) (dc : DecCert) (rflow : KAbs) (env : List KAbs)
    (jenv : List (List KAbs)) (st : RwSt) : Option Exp → Option (Option Exp × RwSt)
  | none => some (none, st)
  | some e => do
    let (e', st') ← checkRewriteExp P dc rflow env jenv st e
    some (some e', st')

end

/-! ## Checking and narrowing the whole program -/

/-- Check dispatcher globals reachable from `todo` (fuelled worklist). Every
dispatcher still referenced by an unnarrowed call (or a root) must pass
`checkExpPlain`. -/
def checkDisps (P : Program) (dc : DecCert) :
    Nat → List GlobalId → Src.NatSet → Bool
  | 0, [], _ => true
  | 0, _ :: _, _ => false
  | _, [], _ => true
  | fuel + 1, g :: todo, seen =>
    if seen.contains g then checkDisps P dc fuel todo seen
    else
      match P.global? g with
      | some gd =>
        if Walk.isDispatchKey gd.key then
          let pfs := paramFlows P dc g gd.ps.length
          let rfl := retFlow dc g
          match checkExpPlain P dc rfl pfs.reverse [] gd.body with
          | some more => checkDisps P dc fuel (more ++ todo) (seen.insert g)
          | none => false
        else checkDisps P dc fuel todo (seen.insert g)
      | none => checkDisps P dc fuel todo (seen.insert g)

/-- Rewrite all non-dispatcher globals and collect globals they reference. -/
def rewriteGlobals (P : Program) (dc : DecCert) :
    List (GlobalId × GDef) → List GlobalId → Option (List (GlobalId × GDef) × List GlobalId)
  | [], used => some ([], used)
  | (g, gd) :: rest, used =>
    if Walk.isDispatchKey gd.key then do
      let (gs, used') ← rewriteGlobals P dc rest used
      some ((g, gd) :: gs, used')
    else
      let pfs := paramFlows P dc g gd.ps.length
      let rfl := retFlow dc g
      let st0 : RwSt := { joins := (dc.joins.get? g).getD [], siteRets := (dc.siteRets.get? g).getD [], used := [] }
      match checkRewriteExp P dc rfl pfs.reverse [] st0 gd.body with
      | some (body', st') => do
        let (gs, used') ← rewriteGlobals P dc rest (st'.used ++ used)
        some ((g, { gd with body := body' }) :: gs, used')
      | none => none

/-- **P9**: flow-directed dispatch narrowing. Validates the flow certificate `c`
and narrows dispatch sites with `≤ c.maxArms` reachable closure keys; if `P` is
not first-order, has closure-keyed pinned constructors, or `c` fails validation,
returns `P` unchanged (so narrowing is unconditionally sound for any `c`). -/
def run (c : Cert) (P : Program) : Program :=
  if !firstOrder P || Defun.knownClosure P.known then P
  else
    let dc := decode P c
    match rewriteGlobals P dc P.globalList P.roots with
    | none => P
    | some (gs, used) =>
      let fuel := P.size + used.length + P.globalList.foldl (fun n (_, gd) => n + gd.body.refs.length) 0 + 1
      if checkDisps P dc fuel used .leaf then
        { P with globals := Src.NatMap.ofList gs }
      else P

end IxCC.Anf.Defun.Narrow
