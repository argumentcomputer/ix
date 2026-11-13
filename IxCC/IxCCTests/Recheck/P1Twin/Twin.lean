import IxCCTests.Recheck.P1Twin.Exec

/-! SrcEval's twin (engineers RN, RO and PD): `Src/Semantics.lean`'s control flow in `IO`, checking P1's
`SortAgree` events (a), (c)-(f) and executable forms of `Live` and of what a call reads, with a
visit hook at every call (`TCx.visit`, the mutant pass), the enclosing spine's arguments at an
evaluation (`more`, for `Frame`'s prefix disjunct), a mode that checks the `SortAgree` events only
(`sortOnly`, the pass's sub-runs), and (f) as `SortCoherent` states it (whether or not the projection
succeeds). -/

namespace IxCCTests.Recheck.P1Twin

open IxCC IxCC.Src IxCC.Src.Relevance IxCC.Src.Relevance.Check IxCC.Src.Relevance.Check.Canonical
open IxCC.Sem (Result)

structure TCx where
  p : Program
  ann : Ann
  ch : Checked
  counts : IO.Ref (List (String × Nat))
  notes : IO.Ref (List String)
  /-- Called at every call the twin makes (with the spine arguments past an evaluated term). -/
  visit : Call → List Term.Arg → IO Unit := fun _ _ => pure ()
  /-- Check the `SortAgree` events only (no `Live`/reads checks). -/
  sortOnly : Bool := false

/-- Add `n` to the count of `key`. -/
def TCx.add (x : TCx) (key : String) (n : Nat) : IO Unit :=
  x.counts.modify fun cs =>
    match cs.find? (·.1 == key) with
    | some _ => cs.map fun (k, m) => if k == key then (k, m + n) else (k, m)
    | none => cs ++ [(key, n)]

def TCx.bump (x : TCx) (key : String) (note : String := "") : IO Unit := do
  x.counts.modify fun cs =>
    match cs.find? (·.1 == key) with
    | some _ => cs.map fun (k, n) => if k == key then (k, n + 1) else (k, n)
    | none => cs ++ [(key, 1)]
  if note != "" then
    let ns ← x.notes.get
    if ns.length < 40 then x.notes.set (ns ++ [s!"{key}: {note}"])

/-! ## RN's approximate `Live` (kept for the real-run checks RO reported) -/

/-- Variables (indices into the environment) used at positions relevant at `ls`. -/
def relUses (ls : Levels) : Nat → Term → List Nat
  | d, .var i => if i ≥ d then [i - d] else []
  | d, .app f a _ r => relUses ls d f ++ (if r.irrAt ls then [] else relUses ls d a)
  | d, .lam b _ t => if b.propWhen.holds ls then [] else relUses ls (d + 1) t
  | d, .letE _ r _ v b => (if r.irrAt ls then [] else relUses ls d v) ++ relUses ls (d + 1) b
  | d, .proj _ _ e => relUses ls d e
  | _, _ => []

mutual
partial def liveB (x : TCx) (n : Nat) : Value → Bool
  | .lit _ | .str _ => true
  | .irr .. => false
  | .con c ls _ fs => (List.range fs.length).all fun i =>
      match fs[i]? with
      | some v => if readsFieldB x.p x.ann x.ch c ls i || !v.isIrr then liveB x n v else true
      | none => true
  | .clo b d body ρ ls => envB x n ls ρ (.lam b d body)
  | .pap h ls args =>
      ((List.range args.length).all fun j => match args[j]? with
        | some s => (headIgnoresB x.ann h ls j && markerB s) || liveSlotB x n s
        | none => true) && minorsIgnoreB x.p x.ann h args && decide (args.length < x.p.headArity h)
partial def liveSlotB (x : TCx) (n : Nat) : Slot → Bool
  | .val v => liveB x n v
  | .name t ρ ls => envB x n ls ρ t
partial def envB (x : TCx) (n : Nat) (ls : Levels) (ρ : Env) (t : Term) : Bool :=
  if n == 0 then true else
  (relUses ls 0 t).eraseDups.all fun i =>
    match ρ[i]? with
    | some s => shieldedB i ρ t || liveSlotB x (n - 1) s
    | none => true
end

def lamBinders : Term → List Binder
  | .lam b _ t => b :: lamBinders t
  | _ => []

/-- (a)'s exemption: the last argument of the spine is at a position written erased. -/
def writtenErasedArgB (p : Program) (t : Term) : Bool :=
  match t.spineL with
  | (.const c _, args) => match p.decl? c with
    | some d => (erasedParams d.type).contains (args.length - 1)
    | none => false
  | (.lam b d body, args) =>
    ((lamBinders (.lam b d body))[args.length - 1]?.map (·.contract.uses == .erased)).getD false
  | _ => false

def depth : Nat := 3

/-! ## The twin -/

mutual

partial def tEval (x : TCx) (k : Nat) (ls : Levels) (ρ : Env) (t : Term) (shielded : Bool)
    (more : List Term.Arg := []) : IO (Result Value) := do
  x.visit (.eval k ls ρ t) more
  let r ← tEval' x k ls ρ t more
  if !x.sortOnly then
    if let .ok v := r then
      if v.isIrr then
        if shielded then x.bump "eval: marker from a shielded variable (expected)"
        else x.bump "VIOLATION eval: marker at a read position" s!"{termShort t}"
  return r

partial def tEval' (x : TCx) (k : Nat) (ls : Levels) (ρ : Env) (t : Term) (more : List Term.Arg) :
    IO (Result Value) := do
  let p := x.p
  match t with
  | .var i =>
    match ρ[i]? with
    | some s => tForce x k s
    | none => pure .stuck
  | .sort _ | .pi .. =>
    x.bump "E2: a sort or Π evaluated (C7 refuses one at a relevant position)"
    pure (.ok (.irr (some t) ρ ls))
  | .natLit n => pure (.ok (.lit n))
  | .strLit s => pure (.ok (.str s))
  | .lam b d body => pure (.ok (.clo b d body ρ ls))
  | .letE _ r _ v body =>
    if r.irrAt ls then tEval x k ls (.val (.irr (some v) ρ ls) :: ρ) body false
    else
      match ← tEval x k ls ρ v false with
      | .ok w => tEval x k ls (.val w :: ρ) body false
      | .timeout => pure .timeout
      | .resource r => pure (.resource r)
      | .trap => pure .trap
      | .stuck => pure .stuck
  | .proj s i e =>
    match ← tEval x k ls ρ e false with
    | .ok v =>
      let res := p.projectField s i v
      x.bump "E6 projection"
      -- (f), as `SortCoherent` states it: a constructor value's field `i` is a marker only where written erased
      match v with
      | .con c _ _ fs =>
        if (fs[i]?.map (·.isIrr)).getD false then
          if fieldWrittenErased p c i then x.bump "E6: marker field written erased (exempt)"
          else x.bump "VIOLATION (f) E6: projection yields a marker" s!"field {i} of {c}"
      | _ => pure ()
      if !x.sortOnly then
        if let .ok _ := res then
          if !liveB x depth v then x.bump "VIOLATION reads: projected structure not Live"
      pure res
    | .timeout => pure .timeout
    | .resource r => pure (.resource r)
    | .trap => pure .trap
    | .stuck => pure .stuck
  | .app f a m r =>
    match ← tEval x k ls ρ f false ((a, m, r) :: more) with
    | .ok fv =>
      if r.irrAt ls then
        x.bump "E7 irrelevant argument"
        if writtenErasedArgB p t then x.bump "E7 irrelevant argument at a position written erased (exempt)"
        else if !ignoresNextB x.ann fv then
          x.bump "VIOLATION (a) E7: a sort marker meets a receiver that reads it" s!"{fv.shape}"
        tApply x k fv (.val (.irr (some a) ρ ls))
      else
        match m with
        | .strict =>
          let sh := match a with
            | .var y => shieldedB y ρ t
            | _ => false
          match ← tEval x k ls ρ a sh with
          | .ok w => tApply x k fv (.val w)
          | .timeout => pure .timeout
          | .resource r => pure (.resource r)
          | .trap => pure .trap
          | .stuck => pure .stuck
        | .byName => tApply x k fv (.name a ρ ls)
    | .timeout => pure .timeout
    | .resource r => pure (.resource r)
    | .trap => pure .trap
    | .stuck => pure .stuck
  | .const c us => tEvalConst x k (us.map (evalUniv ls)) c

partial def tEvalConst (x : TCx) (k : Nat) (ls : Levels) (c : CId) : IO (Result Value) := do
  x.visit (.evalConst k ls c) []
  let p := x.p
  match p.table.resolveOf c with
  | some (.prim op) => tHeadValue x k ls (.prim op)
  | some (.word w op _) => tHeadValue x k ls (.word w op)
  | some (.csimp g vs _) =>
    match k with
    | 0 => pure .timeout
    | k + 1 => tEval x k ls [] (.const g vs) false
  | some (.eqn _ body) =>
    match k with
    | 0 => pure .timeout
    | k + 1 => tEval x k ls [] body false
  | some (.case _) => tHeadValue x k ls (.cases c)
  | none =>
    match p.decl? c with
    | some (.ctor ..) => tHeadValue x k ls (.ctor c)
    | some (.recr ..) => tHeadValue x k ls (.recr c)
    | some (.quot .ctor ..) => tHeadValue x k ls (.quotMk c)
    | some (.quot .lift ..) => tHeadValue x k ls (.quotLift c)
    | some (.defn .defn .safe _ _ v) =>
      match k with
      | 0 => pure .timeout
      | k + 1 => tEval x k ls [] v false
    | some (.defn .opaq .safe _ _ v) =>
      if p.table.isOpaqueByValue c then
        match k with
        | 0 => pure .timeout
        | k + 1 => tEval x k ls [] v false
      else pure .stuck
    | _ => pure .stuck

partial def tHeadValue (x : TCx) (k : Nat) (ls : Levels) (h : Head) : IO (Result Value) := do
  x.visit (.headValue k ls h) []
  if x.p.headArity h == 0 then tFire x k h ls [] else pure (.ok (.pap h ls []))

partial def tApply (x : TCx) (k : Nat) (f : Value) (s : Slot) : IO (Result Value) := do
  x.visit (.apply k f s) []
  let r ← tApply' x k f s
  if !x.sortOnly then
    if let .ok _ := r then
      if !liveB x depth f then x.bump "VIOLATION reads: applied function not Live" s!"{f.shape}"
  return r

partial def tApply' (x : TCx) (k : Nat) (f : Value) (s : Slot) : IO (Result Value) := do
  match f with
  | .clo b _ body ρ ls =>
    if b.propWhen.allowsBeta ls then
      match k with
      | 0 => pure .timeout
      | k + 1 => tEval x k ls (s :: ρ) body false
    else pure .stuck
  | .pap h ls args =>
    let args := args ++ [s]
    let arity := x.p.headArity h
    if args.length == arity then tFire x k h ls args
    else if args.length < arity then pure (.ok (.pap h ls args))
    else pure .stuck
  | _ => pure .stuck

partial def tApplyAll (x : TCx) (k : Nat) (f : Value) (ss : List Slot) : IO (Result Value) := do
  x.visit (.applyAll k f ss) []
  match ss with
  | [] => pure (.ok f)
  | s :: rest =>
    match ← tApply x k f s with
    | .ok v => tApplyAll x k v rest
    | .timeout => pure .timeout
    | .resource r => pure (.resource r)
    | .trap => pure .trap
    | .stuck => pure .stuck

/-- F5's `applyAll`, checking (c) before each application. -/
partial def tApplyFields (x : TCx) (k : Nat) (exempt : Nat → Bool) (i : Nat) (f : Value) (ss : List Slot) :
    IO (Result Value) := do
  x.visit (.applyAll k f ss) []
  match ss with
  | [] => pure (.ok f)
  | s :: rest =>
    if markerB s then
      x.bump "F5 marker field"
      if exempt i then x.bump "F5 marker field written erased (exempt)"
      else if !ignoresNextB x.ann f then x.bump "VIOLATION (c) F5: a marker field meets a receiver that reads it"
    match ← tApply x k f s with
    | .ok v => tApplyFields x k exempt (i + 1) v rest
    | .timeout => pure .timeout
    | .resource r => pure (.resource r)
    | .trap => pure .trap
    | .stuck => pure .stuck

partial def tFire (x : TCx) (k : Nat) (h : Head) (ls : Levels) (args : List Slot) : IO (Result Value) := do
  x.visit (.fire k h ls args) []
  let p := x.p
  match h with
  | .ctor c =>
    match p.decl? c with
    | some (.ctor _ _ _ _ np _ _) =>
      match ← tForceAll x k (args.drop np) with
      | .ok fields =>
        if some c == p.known.natZero then pure (.ok (.lit 0))
        else if some c == p.known.natSucc then
          match fields with
          | [.lit n] => pure (.ok (.lit (n + 1)))
          | _ => pure .stuck
        else pure (.ok (.con c ls (args.take np) fields))
      | .timeout => pure .timeout
      | .resource r => pure (.resource r)
      | .trap => pure .trap
      | .stuck => pure .stuck
    | _ => pure .stuck
  | .quotMk c =>
    match args with
    | [α, r, a] =>
      match ← tForce x k a with
      | .ok v => pure (.ok (.con c ls [α, r] [v]))
      | .timeout => pure .timeout
      | .resource r => pure (.resource r)
      | .trap => pure .trap
      | .stuck => pure .stuck
    | _ => pure .stuck
  | .quotLift _ =>
    match k with
    | 0 => pure .timeout
    | k + 1 =>
      match args with
      | [_, _, _, f, _, q] =>
        match ← tForce x k q with
        | .ok (.con c' l' ps [a]) =>
          if p.isQuotCtor c' then
            if !x.sortOnly && !liveB x depth (.con c' l' ps [a]) then x.bump "VIOLATION reads: lifted quotient not Live"
            match ← tForce x k f with
            | .ok fv =>
              if a.isIrr then
                x.bump "F8 marker element"
                let qErased := match p.decl? c' with
                  | some d => (erasedParams d.type).contains 2
                  | none => false
                if qErased then x.bump "F8 marker element written erased (exempt)"
                else if !ignoresNextB x.ann fv then x.bump "VIOLATION (e) F8: a marker element meets a function that reads it"
              tApply x k fv (.val a)
            | .timeout => pure .timeout
            | .resource r => pure (.resource r)
            | .trap => pure .trap
            | .stuck => pure .stuck
          else pure .stuck
        | .ok _ => pure .stuck
        | .timeout => pure .timeout
        | .resource r => pure (.resource r)
        | .trap => pure .trap
        | .stuck => pure .stuck
      | _ => pure .stuck
  | .recr r =>
    match k with
    | 0 => pure .timeout
    | k + 1 =>
      match p.decl? r, (p.table.recKindOf r).map (·.atLevels ls) with
      | some (.recr _ _ _ np nmot nmin ni ind rules _), some kind =>
        let pre := args.take (np + nmot + nmin)
        let chosen : Result (Nat × List Slot) ← match kind with
          | .empty => pure .trap
          | .ordinary =>
            match ← tForce x k (args.getD (np + nmot + nmin + ni) default) with
            | .ok major =>
              let sel := p.selectRule ind np major
              if !x.sortOnly && sel.isSome && !liveB x depth major then x.bump "VIOLATION reads: F2 major not Live"
              pure (Result.ofOption sel)
            | .timeout => pure .timeout
            | .resource r => pure (.resource r)
            | .trap => pure .trap
            | .stuck => pure .stuck
          | .subsingleton _ srcs =>
            let indices := (args.drop (np + nmot + nmin)).take ni
            pure (.ok (0, srcs.map fun
              | .index i => indices.getD i (Slot.irrNone ls)
              | .proof => Slot.irrNone ls))
        match chosen with
        | .ok (j, fields) =>
          match rules[j]? with
          | some rule =>
            let slots := pre ++ fields
            -- (d): marker slots meet irrelevant rule λs, unless from a position written erased
            x.bump "F2 activation"
            let lams := lamRels rule.rhs
            for n in List.range slots.length do
              if (slots[n]?.map markerB).getD false then
                let rty := ((p.decl? r).map (·.type)).getD (.sort .zero)
                let idxErased := match kind with
                  | .subsingleton _ srcs => match srcs[n - pre.length]? with
                    | some (.index i) => pre.length ≤ n && (erasedParams rty).contains (pre.length + i)
                    | _ => false
                  | _ => false
                let fieldErased := (n < pre.length && (erasedParams rty).contains n) ||
                  (pre.length ≤ n && fieldWrittenErased p rule.ctor (n - pre.length)) || idxErased
                if fieldErased then x.bump "F2 marker slot from a position written erased (exempt)"
                else if !((lams[n]?.map (·.irrAt ls)).getD false) then
                  x.bump "VIOLATION (d) F2: a marker slot meets a relevant rule λ" s!"slot {n} of rule {j} of {r}"
            match peelLams slots.length rule.rhs with
            | some body => tEval x k ls slots.reverse body false
            | none => pure .stuck
          | none => pure .stuck
        | .timeout => pure .timeout
        | .resource r => pure (.resource r)
        | .trap => pure .trap
        | .stuck => pure .stuck
      | _, _ => pure .stuck
  | .cases c =>
    match k with
    | 0 => pure .timeout
    | k + 1 =>
      match p.table.resolveOf c with
      | some (.case r) =>
        match p.decl? r, (p.table.recKindOf r).map (·.atLevels ls) with
        | some (.recr _ _ _ np _ _ ni ind rules _), some kind =>
          let chosen : Result (Nat × List Slot) ← match kind with
            | .empty => pure .trap
            | .ordinary =>
              match ← tForce x k (args.getD (np + 1 + ni) default) with
              | .ok major =>
                let sel := p.selectRule ind np major
                if !x.sortOnly && sel.isSome && !liveB x depth major then x.bump "VIOLATION reads: F5 major not Live"
                pure (Result.ofOption sel)
              | .timeout => pure .timeout
              | .resource r => pure (.resource r)
              | .trap => pure .trap
              | .stuck => pure .stuck
            | .subsingleton _ srcs =>
              pure (.ok (0, srcs.map fun
                | .index i => args.getD (np + 1 + i) (Slot.irrNone ls)
                | .proof => Slot.irrNone ls))
          match chosen with
          | .ok (j, fields) =>
            match ← tForce x k (args.getD (np + 1 + ni + 1 + j) default) with
            | .ok minor =>
              let cty := ((p.decl? c).map (·.type)).getD (.sort .zero)
              let exempt := fun i => ((rules[j]?).map fun rule => fieldWrittenErased p rule.ctor i).getD false ||
                (match kind with
                  | .subsingleton _ srcs => match srcs[i]? with
                    | some (.index i') => (erasedParams cty).contains (np + 1 + i')
                    | _ => false
                  | _ => false)
              tApplyFields x k exempt 0 minor fields
            | .timeout => pure .timeout
            | .resource r => pure (.resource r)
            | .trap => pure .trap
            | .stuck => pure .stuck
          | .timeout => pure .timeout
          | .resource r => pure (.resource r)
          | .trap => pure .trap
          | .stuck => pure .stuck
        | _, _ => pure .stuck
      | _ => pure .stuck
  | .prim op =>
    match ← tForceAll x k args with
    | .ok vs =>
      match litArgs vs with
      | some ns =>
        match op.evalLits ns with
        | some (.nat n) => pure (.ok (.lit n))
        | some (.bool b) => pure (p.boolValue b)
        | none => pure .stuck
      | none => pure .stuck
    | .timeout => pure .timeout
    | .resource r => pure (.resource r)
    | .trap => pure .trap
    | .stuck => pure .stuck
  | .word w op =>
    match ← tForceAll x k args with
    | .ok vs => pure (p.wordValue w op vs)
    | .timeout => pure .timeout
    | .resource r => pure (.resource r)
    | .trap => pure .trap
    | .stuck => pure .stuck

partial def tForce (x : TCx) (k : Nat) (s : Slot) : IO (Result Value) := do
  x.visit (.force k s) []
  match s with
  | .val v => pure (.ok v)
  | .name t ρ ls =>
    match k with
    | 0 => pure .timeout
    | k + 1 => tEval x k ls ρ t false

partial def tForceAll (x : TCx) (k : Nat) (ss : List Slot) : IO (Result (List Value)) := do
  x.visit (.forceAll k ss) []
  match ss with
  | [] => pure (.ok [])
  | s :: rest =>
    match ← tForce x k s with
    | .ok v =>
      match ← tForceAll x k rest with
      | .ok vs => pure (.ok (v :: vs))
      | .timeout => pure .timeout
      | .resource r => pure (.resource r)
      | .trap => pure .trap
      | .stuck => pure .stuck
    | .timeout => pure .timeout
    | .resource r => pure (.resource r)
    | .trap => pure .trap
    | .stuck => pure .stuck

end

/-- Any call through the twin (its result's shape). -/
def tCall (x : TCx) (more : List Term.Arg) : Call → IO String
  | .eval k ls ρ t => do pure (resShape (← tEval x k ls ρ t false more))
  | .evalConst k ls c => do pure (resShape (← tEvalConst x k ls c))
  | .headValue k ls h => do pure (resShape (← tHeadValue x k ls h))
  | .apply k f s => do pure (resShape (← tApply x k f s))
  | .applyAll k f ss => do pure (resShape (← tApplyAll x k f ss))
  | .fire k h ls args => do pure (resShape (← tFire x k h ls args))
  | .force k s => do pure (resShape (← tForce x k s))
  | .forceAll k ss => do
    match ← tForceAll x k ss with
    | .ok vs => pure s!"[{vs.length} values]"
    | .stuck => pure "stuck" | .trap => pure "trap" | .timeout => pure "timeout" | .resource _ => pure "resource"
where resShape : Result Value → String
  | .ok v => v.shape
  | .stuck => "stuck"
  | .trap => "trap"
  | .timeout => "timeout"
  | .resource _ => "resource"

def resultShape : Result Value → String
  | .ok v => v.shape
  | .stuck => "stuck"
  | .trap => "trap"
  | .timeout => "timeout"
  | .resource _ => "resource"

/-- `Src.run` through the twin; compared with `Src.run`; the root result checked `Live` (RN's
approximation and PD's exact one). -/
def twinRun (x : TCx) (k : Nat) (root : CId) (xs : List Value) : IO Unit := do
  let r ← match ← tEvalConst x k [] root with
    | .ok f => tApplyAll x k f (xs.map .val)
    | r => pure r
  let s := Src.run x.p k root xs
  if resultShape r != resultShape s then x.bump "MISMATCH twin vs SrcEval" s!"{resultShape r} / {resultShape s}"
  else x.bump s!"run {resultShape s |>.takeWhile (· != ' ')}"
  if let .ok v := s then
    if liveB x 50 v then x.bump "root result Live" else x.bump "VIOLATION root result not Live" s!"{v.shape}"
    let (ok, cutp) := runEM (liveM (ECx.make x.p x.ann x.ch) 40 v)
    if !ok then x.bump "VIOLATION root result not Live (exact)" s!"{valShort 3 v}"
    else if cutp then x.bump "root result Live (exact, depth cut)"

def newCx (p : Program) (ann : Ann) (ch : Checked) : IO TCx := do
  return { p, ann, ch, counts := ← IO.mkRef [], notes := ← IO.mkRef [] }

def report (label : String) (x : TCx) : IO Unit := do
  let cs ← x.counts.get
  IO.println s!"TWIN {label}: {cs.map fun (k, n) => s!"{k}={n}"}"
  for n in ← x.notes.get do IO.println s!"  NOTE {n}"

/-- The checked record SrcEval's `Live` reads (its records), for a program no check accepted. -/
def looseChecked (ann : Ann) : Checked :=
  { keys := [], reached := [], instances := [], consts := ann.consts, ctors := ann.ctors }

end IxCCTests.Recheck.P1Twin
