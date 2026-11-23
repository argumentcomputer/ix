import Ix.Cert.IxccAiur.Gadgets
import Aiur.HeapMono
import Aiur.Optimized.Depth.Grouped

/-! # Full Backward Simulation Proof for `IxCC Fir → Formal Aiur`

Proves complete backward simulation from `Aiur.Generic.SourceSemantics.EvalFn`
on any program lowered by `Lower.lowerProgram` (covering `.src` and `.clo`
constructors, `Lit.str` byte lists, non-recursive & recursive join points
`.jp`/`.jmp`, and all 12 `Nat` primitives) back to `Fir.run`, and composes it
with `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound` (and its
Goldilocks specialization) for full end-to-end certified compilation from
accepted Aiur circuit rows to `Fir.run`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only. -/

namespace Ix.Cert.IxccAiur.Backward

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open Ix.Cert.IxccAiur.Fir Ix.Cert.IxccAiur.Lower Ix.Cert.IxccAiur.Gadgets

/-! ## Section 1: Value Relations (`BytesRep`, `VR`, `VRs`) -/

section ValueRel

variable {F : Type} [Field F]

/-- Representation of a UTF-8 byte list in `Prog::Bytes` on heap `h`. -/
inductive BytesRep (be : String) (h : Heap F) : List UInt8 → SourceValue F → Prop where
  | nil : BytesRep be h [] (.construct be "Nil" [])
  | cons {b : UInt8} {bs : List UInt8} {addr : Nat} {rw : SourceValue F}
      (atAddr : h[addr]? = some rw) (tail : BytesRep be h bs rw) :
      BytesRep be h (b :: bs) (.construct be "Cons" [.field (b.toNat : F), .ptr (.enum be) addr])

theorem BytesRep.extend {be : String} {h h' : Heap F} (ext : Heap.Extends h h')
    {bs : List UInt8} {w : SourceValue F} (hr : BytesRep be h bs w) :
    BytesRep be h' bs w := by
  induction hr with
  | nil => exact .nil
  | cons atAddr _ ih => exact .cons (ext.getElem?_eq atAddr) ih

theorem BytesRep.extend_append {be : String} {h t : Heap F}
    {bs : List UInt8} {w : SourceValue F} (hr : BytesRep be h bs w) :
    BytesRep be (h ++ t) bs w :=
  hr.extend (Heap.Extends.append_right h t)

theorem BytesRep.type_eq {be : String} {h : Heap F} {bs : List UInt8} {w : SourceValue F}
    (hr : BytesRep be h bs w) : w.type = .enum be := by
  cases hr <;> simp [Value.type]

mutual

/-- Value relation connecting a Fir runtime value `v` to its `Prog::Obj`
representation `w` on heap `h`. Covers small `Nat` literals, `.erased`,
`Lit.str` byte lists, and BOTH `.src` and `.clo` constructors. -/
inductive VR (P : Fir.Program) (e be : String) (h : Heap F) :
    Fir.Val → SourceValue F → Prop where
  | nat {n : Nat} (small : n < natLimit) :
      VR P e be h (.lit (.nat n)) (.construct e "N" [.field (n : F)])
  | erased :
      VR P e be h .erased (.construct e "E" [])
  | str {s : String} {bw : SourceValue F} (bytes : BytesRep be h s.toUTF8.toList bw) :
      VR P e be h (.lit (.str s)) (.construct e "S" [bw])
  | ctor {c : CtorInfo} {idx : Nat} {entry : CtorTableEntry}
      {fs : List Fir.Val} {ps : List (SourceValue F)}
      (atIdx : P.ctors[idx]? = some entry) (keyEq : entry.key = c.key)
      (arityEq : fs.length = entry.arity) (fields : VRs P e be h fs ps) :
      VR P e be h (.ctor c fs) (.construct e (ctorNameOf idx c.key) ps)

/-- Heap-boxed field list relation for `Obj` constructor payloads. -/
inductive VRs (P : Fir.Program) (e be : String) (h : Heap F) :
    List Fir.Val → List (SourceValue F) → Prop where
  | nil : VRs P e be h [] []
  | cons {v : Fir.Val} {vs : List Fir.Val} {addr : Nat} {w : SourceValue F}
      {ps : List (SourceValue F)}
      (atAddr : h[addr]? = some w) (head : VR P e be h v w) (tail : VRs P e be h vs ps) :
      VRs P e be h (v :: vs) (.ptr (.enum e) addr :: ps)

end

mutual

theorem VR.extend {P : Fir.Program} {e be : String} {h h' : Heap F} (ext : Heap.Extends h h') :
    ∀ {v : Fir.Val} {w : SourceValue F}, VR P e be h v w → VR P e be h' v w
  | _, _, .nat small => .nat small
  | _, _, .erased => .erased
  | _, _, .str bytes => .str (bytes.extend ext)
  | _, _, .ctor atIdx keyEq arityEq fields =>
    .ctor atIdx keyEq arityEq (VRs.extend ext fields)

theorem VRs.extend {P : Fir.Program} {e be : String} {h h' : Heap F} (ext : Heap.Extends h h') :
    ∀ {vs : List Fir.Val} {ps : List (SourceValue F)}, VRs P e be h vs ps → VRs P e be h' vs ps
  | _, _, .nil => .nil
  | _, _, .cons atAddr hd tl => .cons (ext.getElem?_eq atAddr) (VR.extend ext hd) (VRs.extend ext tl)

end

theorem VR.extend_append {P : Fir.Program} {e be : String} {h t : Heap F}
    {v : Fir.Val} {w : SourceValue F} (hr : VR P e be h v w) :
    VR P e be (h ++ t) v w :=
  hr.extend (Heap.Extends.append_right h t)

theorem VRs.extend_append {P : Fir.Program} {e be : String} {h t : Heap F}
    {vs : List Fir.Val} {ps : List (SourceValue F)} (hr : VRs P e be h vs ps) :
    VRs P e be (h ++ t) vs ps :=
  hr.extend (Heap.Extends.append_right h t)

theorem VR.type_eq {P : Fir.Program} {e be : String} {h : Heap F}
    {v : Fir.Val} {w : SourceValue F} (hr : VR P e be h v w) :
    w.type = .enum e := by
  cases hr <;> simp [Value.type]

theorem VRs.length_eq {P : Fir.Program} {e be : String} {h : Heap F} :
    ∀ {vs : List Fir.Val} {ps : List (SourceValue F)},
      VRs P e be h vs ps → vs.length = ps.length
  | _, _, .nil => rfl
  | _, _, .cons _ _ tl => congrArg Nat.succ tl.length_eq

theorem VRs.getElem?_some {P : Fir.Program} {e be : String} {h : Heap F} :
    ∀ {i : Nat} {vs : List Fir.Val} {ps : List (SourceValue F)},
      VRs P e be h vs ps → i < vs.length →
      ∃ v addr w, vs[i]? = some v ∧ ps[i]? = some (.ptr (.enum e) addr) ∧
        h[addr]? = some w ∧ VR P e be h v w
  | i, vs, ps, hvs, hi => by
    induction i generalizing vs ps with
    | zero =>
      cases hvs with
      | nil => simp at hi
      | cons atAddr hd _ => exact ⟨_, _, _, rfl, rfl, atAddr, hd⟩
    | succ i ih =>
      cases hvs with
      | nil => simp at hi
      | cons _ _ tl => exact ih _ _ tl (by simp at hi; omega)

theorem VR_N_inv {P : Fir.Program} {e be : String} {h : Heap F} {v : Fir.Val}
    {x : SourceValue F} (hr : VR P e be h v (.construct e "N" [x])) :
    ∃ n : Nat, n < natLimit ∧ v = .lit (.nat n) ∧ x = .field (n : F) := by
  generalize hw : (Value.construct e "N" [x] : SourceValue F) = w at hr
  cases hr with
  | nat small =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hw
    exact ⟨_, small, rfl, hw.2.2⟩
  | erased => simp at hw
  | str _ => simp at hw
  | @ctor c idx _ _ _ _ _ _ _ =>
    simp only [Value.construct.injEq] at hw
    exact False.elim (ctorNameOf_ne_N idx c.key hw.2.1.symm)

theorem VR_E_inv {P : Fir.Program} {e be : String} {h : Heap F} {v : Fir.Val}
    (hr : VR P e be h v (.construct e "E" [])) :
    v = .erased := by
  generalize hw : (Value.construct e "E" [] : SourceValue F) = w at hr
  cases hr with
  | nat _ => simp at hw
  | erased => rfl
  | str _ => simp at hw
  | @ctor c idx _ _ _ _ _ _ _ =>
    simp only [Value.construct.injEq] at hw
    exact False.elim (ctorNameOf_ne_E idx c.key hw.2.1.symm)

theorem VR_S_inv {P : Fir.Program} {e be : String} {h : Heap F} {v : Fir.Val}
    {bw : SourceValue F} (hr : VR P e be h v (.construct e "S" [bw])) :
    ∃ s, v = .lit (.str s) ∧ BytesRep be h s.toUTF8.toList bw := by
  generalize hw : (Value.construct e "S" [bw] : SourceValue F) = w at hr
  cases hr with
  | nat _ => simp at hw
  | erased => simp at hw
  | str bytes =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hw
    exact ⟨_, rfl, hw.2.2 ▸ bytes⟩
  | @ctor c idx _ _ _ _ _ _ _ =>
    simp only [Value.construct.injEq] at hw
    exact False.elim (ctorNameOf_ne_S idx c.key hw.2.1.symm)

theorem VR_ctor_inv {P : Fir.Program} {e be : String} {h : Heap F}
    (hnd : (objCtorNames P).Nodup)
    {idx : Nat} {entry : CtorTableEntry} (hget : P.ctors[idx]? = some entry)
    {v : Fir.Val} {ps : List (SourceValue F)}
    (hr : VR P e be h v (.construct e (ctorNameOf idx entry.key) ps)) :
    ∃ c fs, v = .ctor c fs ∧ c.key = entry.key ∧ fs.length = entry.arity ∧ VRs P e be h fs ps := by
  generalize hw : (Value.construct e (ctorNameOf idx entry.key) ps : SourceValue F) = w at hr
  cases hr with
  | nat _ =>
    simp only [Value.construct.injEq] at hw
    exact False.elim (ctorNameOf_ne_N idx entry.key hw.2.1)
  | erased =>
    simp only [Value.construct.injEq] at hw
    exact False.elim (ctorNameOf_ne_E idx entry.key hw.2.1)
  | str _ =>
    simp only [Value.construct.injEq] at hw
    exact False.elim (ctorNameOf_ne_S idx entry.key hw.2.1)
  | @ctor c idx' entry' fs ps' atIdx keyEq arityEq fields =>
    simp only [Value.construct.injEq] at hw
    obtain ⟨_, hname, hps⟩ := hw
    rw [← keyEq] at hname
    obtain ⟨rfl, rfl⟩ := ctorNameOf_inj_of_nodup hnd atIdx hget hname.symm
    exact ⟨c, fs, rfl, keyEq.symm, arityEq, hps ▸ fields⟩

theorem Forall₂_VR_extend {P : Fir.Program} {e be : String} {h h' : Heap F}
    (ext : Heap.Extends h h') {vs : List Fir.Val} {ws : List (SourceValue F)}
    (hrel : List.Forall₂ (VR P e be h) vs ws) :
    List.Forall₂ (VR P e be h') vs ws :=
  hrel.imp fun _ _ hr => hr.extend ext

end ValueRel

/-! ## Section 2: `trap_no_derivation` & Call-Depth-Indexed `EvalFnN` -/

section EvalDepth

variable {F : Type} [Field F] [DecidableEq F]

/-- `trapE msg` (`assert_eq(0, 1)`) admits no `EvalExpr` derivation. -/
theorem trap_no_derivation {world : World F} {types : Types} {locals : Environment F Nat}
    {msg : String} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (qualifyExprF F (trapE msg)) h r h') : False := by
  simp only [trapE, seqE, litE, erasedE, mk, qualifyExprF, qualifyExpr, qualifyPat,
    qualifyName_obj, Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map,
    List.map] at ev
  obtain ⟨_, _, hass, _⟩ := evalExpr_let_wildcard_inv ev
  obtain ⟨vl, vr, _, ev0, ev1, heq, _⟩ := evalExpr_assertEq_inv hass
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
  exact (zero_ne_one (α := F)) (by simpa using Value.field.inj heq)

mutual

/-- Call-depth-indexed mirror of `SourceSemantics.EvalExpr`, where `d : Nat`
strictly decreases across `.call` invocations and stays unchanged everywhere else. -/
inductive EvalExprN (world : World F) :
    Nat → Types → Environment F Nat → Aiur.Generic.Expr F → Heap F → SourceValue F → Heap F → Prop where
  | literal : EvalExprN world d types locals (.literal x) heap (.field x) heap
  | var (found : locals.find? (·.1 == name) = some (name, value)) :
      EvalExprN world d types locals (.var name) heap value heap
  | global (lookup : world.constant name (type.subst types) = .ok pattern)
      (interpreted : Consts.toExpr pattern = .ok body)
      (value : EvalExprN world d [] [] body before result after) :
      EvalExprN world d types locals (.global name (some type)) before result after
  | tuple (items : EvalArgsN world d types locals exprs before values after) :
      EvalExprN world d types locals (.tuple exprs) before (.tuple values) after
  | array (items : EvalArgsN world d types locals exprs before values after) :
      EvalExprN world d types locals (.array exprs) before (.tuple values) after
  | repeat (item : EvalExprN world d types locals expr before value after) :
      EvalExprN world d types locals (.repeat expr length) before (.tuple (List.replicate length value)) after
  | index (tuple : EvalExprN world d types locals expr before value after)
      (projected : projectValue value index = .ok result) :
      EvalExprN world d types locals (.index expr index) before result after
  | slice (tuple : EvalExprN world d types locals expr before value after)
      (sliced : sliceValue value start stop = .ok result) :
      EvalExprN world d types locals (.slice expr start stop) before result after
  | builtin (items : EvalArgsN world d types locals exprs before values after)
      (applied : operation.apply values = .ok result) :
      EvalExprN world d types locals (.builtin operation exprs) before result after
  | update (items : EvalArgsN world d types locals exprs before values after)
      (updated : Update.value types paths values = .ok result) :
      EvalExprN world d types locals (.update paths exprs) before result after
  | record (items : EvalArgsN world d types locals exprs before values after) :
      EvalExprN world d types locals (.record head exprs) before
        (.construct (constructorName types head.type) structConstructor
          (head.order values (.tuple []))) after
  | member (record : EvalExprN world d types locals expr before value after)
      (projected : memberValue types field value = .ok result) :
      EvalExprN world d types locals (.member expr field) before result after
  | construct (items : EvalArgsN world d types locals exprs before values after) :
      EvalExprN world d types locals (.construct name typeArgs ctor exprs) before
        (.construct (instanceName types name typeArgs) ctor values) after
  | constructAs (items : EvalArgsN world d types locals exprs before values after) :
      EvalExprN world d types locals (.constructAs params t ctor exprs) before
        (.construct (constructorName types t) ctor values) after
  | project (tuple : EvalExprN world d types locals expr before value after)
      (projected : projectValue value index = .ok result) :
      EvalExprN world d types locals (.project expr index) before result after
  | letValue (value : EvalExprN world d types locals expr before input middle)
      (matched : world.matchPattern types middle pattern input = .ok (some bindings))
      (body : EvalExprN world d types (bindings ++ locals) rest middle result after) :
      EvalExprN world d types locals (.letValue pattern expr rest) before result after
  | store (value : EvalExprN world d types locals expr before input middle) :
      EvalExprN world d types locals (.store expr) before (.ptr input.type middle.length) (middle ++ [input])
  | load (pointer : EvalExprN world d types locals expr before value after)
      (loaded : loadValue after value = .ok result) :
      EvalExprN world d types locals (.load expr) before result after
  | hint (key : EvalExprN world d types locals expr before input after)
      (typed : world.typed (t.subst types).toCore witness = true) :
      EvalExprN world d types locals (.hint t expr channel) before witness.toValue after
  | neg (value : EvalExprN world d types locals expr before input after)
      (operation : evalNeg input = .ok result) :
      EvalExprN world d types locals (.neg expr) before result after
  | binary (left : EvalExprN world d types locals lhs before x middle)
      (right : EvalExprN world d types locals rhs middle y after)
      (applied : evalBinOp op x y = .ok result) :
      EvalExprN world d types locals (.binary op lhs rhs) before result after
  | call {d d' : Nat} (hlt : d' < d)
      (arguments : EvalArgsN world d types locals args before inputs middle)
      (callee : EvalFnN world d' (instanceName types name typeArgs) inputs middle result after) :
      EvalExprN world d types locals (.call name typeArgs args) before result after
  | matchValue (value : EvalExprN world d types locals expr before input middle)
      (selected : SourceSemantics.selectArm world types middle input arms = .ok (some (bindings, body)))
      (branch : EvalExprN world d types (bindings ++ locals) body middle result after) :
      EvalExprN world d types locals (.matchValue expr arms) before result after
  | block (body : EvalExprN world d types locals expr before result after) :
      EvalExprN world d types locals (.control (.block label) expr) before result after
  | blockExit (body : EvalExitN world d types locals expr before (.block label) result after) :
      EvalExprN world d types locals (.control (.block label) expr) before result after

inductive EvalArgsN (world : World F) :
    Nat → Types → Environment F Nat → List (Aiur.Generic.Expr F) → Heap F → List (SourceValue F) → Heap F → Prop where
  | nil : EvalArgsN world d types locals [] heap [] heap
  | cons (head : EvalExprN world d types locals expr before value middle)
      (tail : EvalArgsN world d types locals rest middle values after) :
      EvalArgsN world d types locals (expr :: rest) before (value :: values) after

inductive EvalFnN (world : World F) :
    Nat → String → List (SourceValue F) → Heap F → SourceValue F → Heap F → Prop where
  | intro (prepared : world.prepare name args = .ok (types, locals, expr))
      (body : EvalExprN world d types locals expr before result after) :
      EvalFnN world d name args before result after
  | returned (prepared : world.prepare name args = .ok (types, locals, expr))
      (body : EvalExitN world d types locals expr before .function result after) :
      EvalFnN world d name args before result after

inductive EvalExitN (world : World F) :
    Nat → Types → Environment F Nat → Aiur.Generic.Expr F → Heap F → ExitTarget → SourceValue F → Heap F → Prop where
  | exit (value : EvalExprN world d types locals expr before result after) :
      EvalExitN world d types locals (.control (.exit target) expr) before target result after
  | exitPayload (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.control (.exit outer) expr) before target result after
  | fromBlock (different : target ≠ .block label)
      (body : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.control (.block label) expr) before target result after
  | fromGlobal (lookup : world.constant name (type.subst types) = .ok pattern)
      (interpreted : Consts.toExpr pattern = .ok body)
      (value : EvalExitN world d [] [] body before target result after) :
      EvalExitN world d types locals (.global name (some type)) before target result after
  | fromTuple (items : EvalArgsExitN world d types locals exprs before target result after) :
      EvalExitN world d types locals (.tuple exprs) before target result after
  | fromArray (items : EvalArgsExitN world d types locals exprs before target result after) :
      EvalExitN world d types locals (.array exprs) before target result after
  | fromRepeat (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.repeat expr length) before target result after
  | fromIndex (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.index expr index) before target result after
  | fromSlice (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.slice expr start stop) before target result after
  | fromBuiltin (items : EvalArgsExitN world d types locals exprs before target result after) :
      EvalExitN world d types locals (.builtin operation exprs) before target result after
  | fromUpdate (items : EvalArgsExitN world d types locals exprs before target result after) :
      EvalExitN world d types locals (.update paths exprs) before target result after
  | fromRecord (items : EvalArgsExitN world d types locals exprs before target result after) :
      EvalExitN world d types locals (.record head exprs) before target result after
  | fromMember (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.member expr field) before target result after
  | fromConstruct (items : EvalArgsExitN world d types locals exprs before target result after) :
      EvalExitN world d types locals (.construct name args ctor exprs) before target result after
  | fromConstructAs (items : EvalArgsExitN world d types locals exprs before target result after) :
      EvalExitN world d types locals (.constructAs params t ctor exprs) before target result after
  | fromProject (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.project expr index) before target result after
  | fromLetValue (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.letValue pattern expr rest) before target result after
  | letBody (value : EvalExprN world d types locals expr before input middle)
      (matched : world.matchPattern types middle pattern input = .ok (some bindings))
      (body : EvalExitN world d types (bindings ++ locals) rest middle target result after) :
      EvalExitN world d types locals (.letValue pattern expr rest) before target result after
  | fromStore (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.store expr) before target result after
  | fromLoad (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.load expr) before target result after
  | fromHint (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.hint t expr channel) before target result after
  | fromNeg (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.neg expr) before target result after
  | binaryLeft (value : EvalExitN world d types locals left before target result after) :
      EvalExitN world d types locals (.binary op left right) before target result after
  | binaryRight (left : EvalExprN world d types locals lhs before input middle)
      (right : EvalExitN world d types locals rhs middle target result after) :
      EvalExitN world d types locals (.binary op lhs rhs) before target result after
  | fromCall (arguments : EvalArgsExitN world d types locals args before target result after) :
      EvalExitN world d types locals (.call name typeArgs args) before target result after
  | fromMatchValue (value : EvalExitN world d types locals expr before target result after) :
      EvalExitN world d types locals (.matchValue expr arms) before target result after
  | matchBody (value : EvalExprN world d types locals expr before input middle)
      (selected : SourceSemantics.selectArm world types middle input arms = .ok (some (bindings, body)))
      (branch : EvalExitN world d types (bindings ++ locals) body middle target result after) :
      EvalExitN world d types locals (.matchValue expr arms) before target result after

inductive EvalArgsExitN (world : World F) :
    Nat → Types → Environment F Nat → List (Aiur.Generic.Expr F) → Heap F → ExitTarget → SourceValue F → Heap F → Prop where
  | head (value : EvalExitN world d types locals expr before target result after) :
      EvalArgsExitN world d types locals (expr :: rest) before target result after
  | tail (head : EvalExprN world d types locals expr before value middle)
      (tail : EvalArgsExitN world d types locals rest middle target result after) :
      EvalArgsExitN world d types locals (expr :: rest) before target result after

end

mutual

theorem EvalExprN.toEvalExpr {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {e : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F} :
    EvalExprN world d types locals e h r h' → EvalExpr world types locals e h r h'
  | .literal => .literal
  | .var h => .var h
  | .global hl hi v => .global hl hi v.toEvalExpr
  | .tuple xs => .tuple xs.toEvalArgs
  | .array xs => .array xs.toEvalArgs
  | .repeat x => .repeat x.toEvalExpr
  | .index x hp => .index x.toEvalExpr hp
  | .slice x hs => .slice x.toEvalExpr hs
  | .builtin xs ha => .builtin xs.toEvalArgs ha
  | .update xs ha => .update xs.toEvalArgs ha
  | .record xs => .record xs.toEvalArgs
  | .member x hp => .member x.toEvalExpr hp
  | .construct xs => .construct xs.toEvalArgs
  | .constructAs xs => .constructAs xs.toEvalArgs
  | .project x hp => .project x.toEvalExpr hp
  | .letValue v hm b => .letValue v.toEvalExpr hm b.toEvalExpr
  | .store v => .store v.toEvalExpr
  | .load v hl => .load v.toEvalExpr hl
  | .hint k ht => .hint k.toEvalExpr ht
  | .neg v hop => .neg v.toEvalExpr hop
  | .binary l r ha => .binary l.toEvalExpr r.toEvalExpr ha
  | .call _ xs c => .call xs.toEvalArgs c.toEvalFn
  | .matchValue v hs b => .matchValue v.toEvalExpr hs b.toEvalExpr
  | .block b => .block b.toEvalExpr
  | .blockExit b => .blockExit b.toEvalExit

theorem EvalArgsN.toEvalArgs {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
    {h h' : Heap F} {vs : List (SourceValue F)} :
    EvalArgsN world d types locals es h vs h' → EvalArgs world types locals es h vs h'
  | .nil => .nil
  | .cons hd tl => .cons hd.toEvalExpr tl.toEvalArgs

theorem EvalFnN.toEvalFn {world : World F} {d : Nat} {name : String}
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} :
    EvalFnN world d name args h r h' → EvalFn world name args h r h'
  | .intro hp b => .intro hp b.toEvalExpr
  | .returned hp b => .returned hp b.toEvalExit

theorem EvalExitN.toEvalExit {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {e : Aiur.Generic.Expr F}
    {h h' : Heap F} {t : ExitTarget} {r : SourceValue F} :
    EvalExitN world d types locals e h t r h' → EvalExit world types locals e h t r h'
  | .exit v => .exit v.toEvalExpr
  | .exitPayload v => .exitPayload v.toEvalExit
  | .fromBlock hd b => .fromBlock hd b.toEvalExit
  | .fromGlobal hl hi v => .fromGlobal hl hi v.toEvalExit
  | .fromTuple xs => .fromTuple xs.toEvalArgsExit
  | .fromArray xs => .fromArray xs.toEvalArgsExit
  | .fromRepeat v => .fromRepeat v.toEvalExit
  | .fromIndex v => .fromIndex v.toEvalExit
  | .fromSlice v => .fromSlice v.toEvalExit
  | .fromBuiltin xs => .fromBuiltin xs.toEvalArgsExit
  | .fromUpdate xs => .fromUpdate xs.toEvalArgsExit
  | .fromRecord xs => .fromRecord xs.toEvalArgsExit
  | .fromMember v => .fromMember v.toEvalExit
  | .fromConstruct xs => .fromConstruct xs.toEvalArgsExit
  | .fromConstructAs xs => .fromConstructAs xs.toEvalArgsExit
  | .fromProject v => .fromProject v.toEvalExit
  | .fromLetValue v => .fromLetValue v.toEvalExit
  | .letBody v hm b => .letBody v.toEvalExpr hm b.toEvalExit
  | .fromStore v => .fromStore v.toEvalExit
  | .fromLoad v => .fromLoad v.toEvalExit
  | .fromHint v => .fromHint v.toEvalExit
  | .fromNeg v => .fromNeg v.toEvalExit
  | .binaryLeft v => .binaryLeft v.toEvalExit
  | .binaryRight l r => .binaryRight l.toEvalExpr r.toEvalExit
  | .fromCall xs => .fromCall xs.toEvalArgsExit
  | .fromMatchValue v => .fromMatchValue v.toEvalExit
  | .matchBody v hs b => .matchBody v.toEvalExpr hs b.toEvalExit

theorem EvalArgsExitN.toEvalArgsExit {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
    {h h' : Heap F} {t : ExitTarget} {r : SourceValue F} :
    EvalArgsExitN world d types locals es h t r h' → EvalArgsExit world types locals es h t r h'
  | .head v => .head v.toEvalExit
  | .tail hd tl => .tail hd.toEvalExpr tl.toEvalArgsExit

end

theorem EvalExprN.heap_extends {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {e : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals e h r h') : Heap.Extends h h' :=
  ev.toEvalExpr.heap_extends

theorem EvalArgsN.heap_extends {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
    {h h' : Heap F} {vs : List (SourceValue F)}
    (ev : EvalArgsN world d types locals es h vs h') : Heap.Extends h h' :=
  ev.toEvalArgs.heap_extends

theorem EvalFnN.heap_extends {world : World F} {d : Nat} {name : String}
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFnN world d name args h r h') : Heap.Extends h h' :=
  ev.toEvalFn.heap_extends

mutual

theorem EvalExprN.mono {world : World F} :
    ∀ {d₁ d₂ : Nat} {types : Types} {locals : Environment F Nat} {e : Aiur.Generic.Expr F}
      {h h' : Heap F} {r : SourceValue F},
      d₁ ≤ d₂ → EvalExprN world d₁ types locals e h r h' → EvalExprN world d₂ types locals e h r h'
  | _, _, _, _, _, _, _, _, _, .literal => .literal
  | _, _, _, _, _, _, _, _, _, .var h => .var h
  | _, _, _, _, _, _, _, _, hle, .global hl hi v => .global hl hi (v.mono hle)
  | _, _, _, _, _, _, _, _, hle, .tuple xs => .tuple (xs.mono hle)
  | _, _, _, _, _, _, _, _, hle, .array xs => .array (xs.mono hle)
  | _, _, _, _, _, _, _, _, hle, .repeat x => .repeat (x.mono hle)
  | _, _, _, _, _, _, _, _, hle, .index x hp => .index (x.mono hle) hp
  | _, _, _, _, _, _, _, _, hle, .slice x hs => .slice (x.mono hle) hs
  | _, _, _, _, _, _, _, _, hle, .builtin xs ha => .builtin (xs.mono hle) ha
  | _, _, _, _, _, _, _, _, hle, .update xs ha => .update (xs.mono hle) ha
  | _, _, _, _, _, _, _, _, hle, .record xs => .record (xs.mono hle)
  | _, _, _, _, _, _, _, _, hle, .member x hp => .member (x.mono hle) hp
  | _, _, _, _, _, _, _, _, hle, .construct xs => .construct (xs.mono hle)
  | _, _, _, _, _, _, _, _, hle, .constructAs xs => .constructAs (xs.mono hle)
  | _, _, _, _, _, _, _, _, hle, .project x hp => .project (x.mono hle) hp
  | _, _, _, _, _, _, _, _, hle, .letValue v hm b => .letValue (v.mono hle) hm (b.mono hle)
  | _, _, _, _, _, _, _, _, hle, .store v => .store (v.mono hle)
  | _, _, _, _, _, _, _, _, hle, .load v hl => .load (v.mono hle) hl
  | _, _, _, _, _, _, _, _, hle, .hint k ht => .hint (k.mono hle) ht
  | _, _, _, _, _, _, _, _, hle, .neg v hop => .neg (v.mono hle) hop
  | _, _, _, _, _, _, _, _, hle, .binary l r ha => .binary (l.mono hle) (r.mono hle) ha
  | _, _, _, _, _, _, _, _, hle, .call hlt xs c => .call (Nat.lt_of_lt_of_le hlt hle) (xs.mono hle) c
  | _, _, _, _, _, _, _, _, hle, .matchValue v hs b => .matchValue (v.mono hle) hs (b.mono hle)
  | _, _, _, _, _, _, _, _, hle, .block b => .block (b.mono hle)
  | _, _, _, _, _, _, _, _, hle, .blockExit b => .blockExit (b.mono hle)

theorem EvalArgsN.mono {world : World F} :
    ∀ {d₁ d₂ : Nat} {types : Types} {locals : Environment F Nat}
      {es : List (Aiur.Generic.Expr F)} {h h' : Heap F} {vs : List (SourceValue F)},
      d₁ ≤ d₂ → EvalArgsN world d₁ types locals es h vs h' → EvalArgsN world d₂ types locals es h vs h'
  | _, _, _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, _, hle, .cons hd tl => .cons (hd.mono hle) (tl.mono hle)

theorem EvalFnN.mono {world : World F} :
    ∀ {d₁ d₂ : Nat} {name : String} {args : List (SourceValue F)}
      {h h' : Heap F} {r : SourceValue F},
      d₁ ≤ d₂ → EvalFnN world d₁ name args h r h' → EvalFnN world d₂ name args h r h'
  | _, _, _, _, _, _, _, hle, .intro hp b => .intro hp (b.mono hle)
  | _, _, _, _, _, _, _, hle, .returned hp b => .returned hp (b.mono hle)

theorem EvalExitN.mono {world : World F} :
    ∀ {d₁ d₂ : Nat} {types : Types} {locals : Environment F Nat} {e : Aiur.Generic.Expr F}
      {h h' : Heap F} {t : ExitTarget} {r : SourceValue F},
      d₁ ≤ d₂ → EvalExitN world d₁ types locals e h t r h' → EvalExitN world d₂ types locals e h t r h'
  | _, _, _, _, _, _, _, _, _, hle, .exit v => .exit (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .exitPayload v => .exitPayload (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromBlock hd b => .fromBlock hd (b.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromGlobal hl hi v => .fromGlobal hl hi (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromTuple xs => .fromTuple (xs.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromArray xs => .fromArray (xs.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromRepeat v => .fromRepeat (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromIndex v => .fromIndex (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromSlice v => .fromSlice (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromBuiltin xs => .fromBuiltin (xs.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromUpdate xs => .fromUpdate (xs.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromRecord xs => .fromRecord (xs.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromMember v => .fromMember (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromConstruct xs => .fromConstruct (xs.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromConstructAs xs => .fromConstructAs (xs.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromProject v => .fromProject (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromLetValue v => .fromLetValue (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .letBody v hm b => .letBody (v.mono hle) hm (b.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromStore v => .fromStore (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromLoad v => .fromLoad (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromHint v => .fromHint (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromNeg v => .fromNeg (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .binaryLeft v => .binaryLeft (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .binaryRight l r => .binaryRight (l.mono hle) (r.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromCall xs => .fromCall (xs.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .fromMatchValue v => .fromMatchValue (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .matchBody v hs b => .matchBody (v.mono hle) hs (b.mono hle)

theorem EvalArgsExitN.mono {world : World F} :
    ∀ {d₁ d₂ : Nat} {types : Types} {locals : Environment F Nat}
      {es : List (Aiur.Generic.Expr F)} {h h' : Heap F} {t : ExitTarget} {r : SourceValue F},
      d₁ ≤ d₂ → EvalArgsExitN world d₁ types locals es h t r h' →
      EvalArgsExitN world d₂ types locals es h t r h'
  | _, _, _, _, _, _, _, _, _, hle, .head v => .head (v.mono hle)
  | _, _, _, _, _, _, _, _, _, hle, .tail hd tl => .tail (hd.mono hle) (tl.mono hle)

end

mutual

theorem EvalExprN.ofEvalExpr {world : World F} :
    ∀ {types : Types} {locals : Environment F Nat} {e : Aiur.Generic.Expr F}
      {h h' : Heap F} {r : SourceValue F},
      EvalExpr world types locals e h r h' → ∃ d, EvalExprN world d types locals e h r h'
  | _, _, _, _, _, _, .literal => ⟨0, .literal⟩
  | _, _, _, _, _, _, .var h => ⟨0, .var h⟩
  | _, _, _, _, _, _, .global hl hi v =>
    let ⟨d, hv⟩ := EvalExprN.ofEvalExpr v; ⟨d, .global hl hi hv⟩
  | _, _, _, _, _, _, .tuple xs =>
    let ⟨d, hxs⟩ := EvalArgsN.ofEvalArgs xs; ⟨d, .tuple hxs⟩
  | _, _, _, _, _, _, .array xs =>
    let ⟨d, hxs⟩ := EvalArgsN.ofEvalArgs xs; ⟨d, .array hxs⟩
  | _, _, _, _, _, _, .repeat x =>
    let ⟨d, hx⟩ := EvalExprN.ofEvalExpr x; ⟨d, .repeat hx⟩
  | _, _, _, _, _, _, .index x hp =>
    let ⟨d, hx⟩ := EvalExprN.ofEvalExpr x; ⟨d, .index hx hp⟩
  | _, _, _, _, _, _, .slice x hs =>
    let ⟨d, hx⟩ := EvalExprN.ofEvalExpr x; ⟨d, .slice hx hs⟩
  | _, _, _, _, _, _, .builtin xs ha =>
    let ⟨d, hxs⟩ := EvalArgsN.ofEvalArgs xs; ⟨d, .builtin hxs ha⟩
  | _, _, _, _, _, _, .update xs ha =>
    let ⟨d, hxs⟩ := EvalArgsN.ofEvalArgs xs; ⟨d, .update hxs ha⟩
  | _, _, _, _, _, _, .record xs =>
    let ⟨d, hxs⟩ := EvalArgsN.ofEvalArgs xs; ⟨d, .record hxs⟩
  | _, _, _, _, _, _, .member x hp =>
    let ⟨d, hx⟩ := EvalExprN.ofEvalExpr x; ⟨d, .member hx hp⟩
  | _, _, _, _, _, _, .construct xs =>
    let ⟨d, hxs⟩ := EvalArgsN.ofEvalArgs xs; ⟨d, .construct hxs⟩
  | _, _, _, _, _, _, .constructAs xs =>
    let ⟨d, hxs⟩ := EvalArgsN.ofEvalArgs xs; ⟨d, .constructAs hxs⟩
  | _, _, _, _, _, _, .project x hp =>
    let ⟨d, hx⟩ := EvalExprN.ofEvalExpr x; ⟨d, .project hx hp⟩
  | _, _, _, _, _, _, .letValue v hm b =>
    let ⟨d1, hv⟩ := EvalExprN.ofEvalExpr v
    let ⟨d2, hb⟩ := EvalExprN.ofEvalExpr b
    ⟨max d1 d2, .letValue (hv.mono (Nat.le_max_left _ _)) hm (hb.mono (Nat.le_max_right _ _))⟩
  | _, _, _, _, _, _, .store v =>
    let ⟨d, hv⟩ := EvalExprN.ofEvalExpr v; ⟨d, .store hv⟩
  | _, _, _, _, _, _, .load v hl =>
    let ⟨d, hv⟩ := EvalExprN.ofEvalExpr v; ⟨d, .load hv hl⟩
  | _, _, _, _, _, _, .hint k ht =>
    let ⟨d, hk⟩ := EvalExprN.ofEvalExpr k; ⟨d, .hint hk ht⟩
  | _, _, _, _, _, _, .neg v hop =>
    let ⟨d, hv⟩ := EvalExprN.ofEvalExpr v; ⟨d, .neg hv hop⟩
  | _, _, _, _, _, _, .binary l r ha =>
    let ⟨d1, hl⟩ := EvalExprN.ofEvalExpr l
    let ⟨d2, hr⟩ := EvalExprN.ofEvalExpr r
    ⟨max d1 d2, .binary (hl.mono (Nat.le_max_left _ _)) (hr.mono (Nat.le_max_right _ _)) ha⟩
  | _, _, _, _, _, _, .call xs c =>
    let ⟨d1, hxs⟩ := EvalArgsN.ofEvalArgs xs
    let ⟨d2, hc⟩ := EvalFnN.ofEvalFn c
    ⟨max d1 (d2 + 1), .call (Nat.lt_of_lt_of_le (Nat.lt_succ_self d2) (Nat.le_max_right _ _))
      (hxs.mono (Nat.le_max_left _ _)) hc⟩
  | _, _, _, _, _, _, .matchValue v hs b =>
    let ⟨d1, hv⟩ := EvalExprN.ofEvalExpr v
    let ⟨d2, hb⟩ := EvalExprN.ofEvalExpr b
    ⟨max d1 d2, .matchValue (hv.mono (Nat.le_max_left _ _)) hs (hb.mono (Nat.le_max_right _ _))⟩
  | _, _, _, _, _, _, .block b =>
    let ⟨d, hb⟩ := EvalExprN.ofEvalExpr b; ⟨d, .block hb⟩
  | _, _, _, _, _, _, .blockExit b =>
    let ⟨d, hb⟩ := EvalExitN.ofEvalExit b; ⟨d, .blockExit hb⟩

theorem EvalArgsN.ofEvalArgs {world : World F} :
    ∀ {types : Types} {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {h h' : Heap F} {vs : List (SourceValue F)},
      EvalArgs world types locals es h vs h' → ∃ d, EvalArgsN world d types locals es h vs h'
  | _, _, _, _, _, _, .nil => ⟨0, .nil⟩
  | _, _, _, _, _, _, .cons hd tl =>
    let ⟨d1, hhd⟩ := EvalExprN.ofEvalExpr hd
    let ⟨d2, htl⟩ := EvalArgsN.ofEvalArgs tl
    ⟨max d1 d2, .cons (hhd.mono (Nat.le_max_left _ _)) (htl.mono (Nat.le_max_right _ _))⟩

theorem EvalFnN.ofEvalFn {world : World F} :
    ∀ {name : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F},
      EvalFn world name args h r h' → ∃ d, EvalFnN world d name args h r h'
  | _, _, _, _, _, .intro hp b =>
    let ⟨d, hb⟩ := EvalExprN.ofEvalExpr b; ⟨d, .intro hp hb⟩
  | _, _, _, _, _, .returned hp b =>
    let ⟨d, hb⟩ := EvalExitN.ofEvalExit b; ⟨d, .returned hp hb⟩

theorem EvalExitN.ofEvalExit {world : World F} :
    ∀ {types : Types} {locals : Environment F Nat} {e : Aiur.Generic.Expr F}
      {h h' : Heap F} {t : ExitTarget} {r : SourceValue F},
      EvalExit world types locals e h t r h' → ∃ d, EvalExitN world d types locals e h t r h'
  | _, _, _, _, _, _, _, .exit v =>
    let ⟨d, hv⟩ := EvalExprN.ofEvalExpr v; ⟨d, .exit hv⟩
  | _, _, _, _, _, _, _, .exitPayload v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .exitPayload hv⟩
  | _, _, _, _, _, _, _, .fromBlock hd b =>
    let ⟨d, hb⟩ := EvalExitN.ofEvalExit b; ⟨d, .fromBlock hd hb⟩
  | _, _, _, _, _, _, _, .fromGlobal hl hi v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromGlobal hl hi hv⟩
  | _, _, _, _, _, _, _, .fromTuple xs =>
    let ⟨d, hxs⟩ := EvalArgsExitN.ofEvalArgsExit xs; ⟨d, .fromTuple hxs⟩
  | _, _, _, _, _, _, _, .fromArray xs =>
    let ⟨d, hxs⟩ := EvalArgsExitN.ofEvalArgsExit xs; ⟨d, .fromArray hxs⟩
  | _, _, _, _, _, _, _, .fromRepeat v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromRepeat hv⟩
  | _, _, _, _, _, _, _, .fromIndex v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromIndex hv⟩
  | _, _, _, _, _, _, _, .fromSlice v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromSlice hv⟩
  | _, _, _, _, _, _, _, .fromBuiltin xs =>
    let ⟨d, hxs⟩ := EvalArgsExitN.ofEvalArgsExit xs; ⟨d, .fromBuiltin hxs⟩
  | _, _, _, _, _, _, _, .fromUpdate xs =>
    let ⟨d, hxs⟩ := EvalArgsExitN.ofEvalArgsExit xs; ⟨d, .fromUpdate hxs⟩
  | _, _, _, _, _, _, _, .fromRecord xs =>
    let ⟨d, hxs⟩ := EvalArgsExitN.ofEvalArgsExit xs; ⟨d, .fromRecord hxs⟩
  | _, _, _, _, _, _, _, .fromMember v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromMember hv⟩
  | _, _, _, _, _, _, _, .fromConstruct xs =>
    let ⟨d, hxs⟩ := EvalArgsExitN.ofEvalArgsExit xs; ⟨d, .fromConstruct hxs⟩
  | _, _, _, _, _, _, _, .fromConstructAs xs =>
    let ⟨d, hxs⟩ := EvalArgsExitN.ofEvalArgsExit xs; ⟨d, .fromConstructAs hxs⟩
  | _, _, _, _, _, _, _, .fromProject v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromProject hv⟩
  | _, _, _, _, _, _, _, .fromLetValue v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromLetValue hv⟩
  | _, _, _, _, _, _, _, .letBody v hm b =>
    let ⟨d1, hv⟩ := EvalExprN.ofEvalExpr v
    let ⟨d2, hb⟩ := EvalExitN.ofEvalExit b
    ⟨max d1 d2, .letBody (hv.mono (Nat.le_max_left _ _)) hm (hb.mono (Nat.le_max_right _ _))⟩
  | _, _, _, _, _, _, _, .fromStore v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromStore hv⟩
  | _, _, _, _, _, _, _, .fromLoad v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromLoad hv⟩
  | _, _, _, _, _, _, _, .fromHint v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromHint hv⟩
  | _, _, _, _, _, _, _, .fromNeg v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromNeg hv⟩
  | _, _, _, _, _, _, _, .binaryLeft v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .binaryLeft hv⟩
  | _, _, _, _, _, _, _, .binaryRight l r =>
    let ⟨d1, hl⟩ := EvalExprN.ofEvalExpr l
    let ⟨d2, hr⟩ := EvalExitN.ofEvalExit r
    ⟨max d1 d2, .binaryRight (hl.mono (Nat.le_max_left _ _)) (hr.mono (Nat.le_max_right _ _))⟩
  | _, _, _, _, _, _, _, .fromCall xs =>
    let ⟨d, hxs⟩ := EvalArgsExitN.ofEvalArgsExit xs; ⟨d, .fromCall hxs⟩
  | _, _, _, _, _, _, _, .fromMatchValue v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .fromMatchValue hv⟩
  | _, _, _, _, _, _, _, .matchBody v hs b =>
    let ⟨d1, hv⟩ := EvalExprN.ofEvalExpr v
    let ⟨d2, hb⟩ := EvalExitN.ofEvalExit b
    ⟨max d1 d2, .matchBody (hv.mono (Nat.le_max_left _ _)) hs (hb.mono (Nat.le_max_right _ _))⟩

theorem EvalArgsExitN.ofEvalArgsExit {world : World F} :
    ∀ {types : Types} {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {h h' : Heap F} {t : ExitTarget} {r : SourceValue F},
      EvalArgsExit world types locals es h t r h' →
      ∃ d, EvalArgsExitN world d types locals es h t r h'
  | _, _, _, _, _, _, _, .head v =>
    let ⟨d, hv⟩ := EvalExitN.ofEvalExit v; ⟨d, .head hv⟩
  | _, _, _, _, _, _, _, .tail hd tl =>
    let ⟨d1, hhd⟩ := EvalExprN.ofEvalExpr hd
    let ⟨d2, htl⟩ := EvalArgsExitN.ofEvalArgsExit tl
    ⟨max d1 d2, .tail (hhd.mono (Nat.le_max_left _ _)) (htl.mono (Nat.le_max_right _ _))⟩

end

/-! ### Straight-Line `EvalExprN` Inversion Helpers -/

theorem evalFnN_plain_inv {world : World F} {d : Nat} {name : String} {paramNames : List String}
    {body : Aiur.Generic.Expr F} {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F}
    (hfn : WorldHasFn world name paramNames body) (hplain : isPlainExpr body = true)
    (ev : EvalFnN world d name args h r h') :
    args.length = paramNames.length ∧
    EvalExprN world d [] (paramNames.zip args) body h r h' := by
  cases ev with
  | intro prep b =>
    obtain ⟨rfl, hlen, rfl, rfl⟩ := hfn _ _ _ _ prep
    exact ⟨hlen, b⟩
  | returned prep b =>
    obtain ⟨rfl, _, rfl, rfl⟩ := hfn _ _ _ _ prep
    exact False.elim (no_evalExit_of_plain hplain b.toEvalExit)

theorem evalExprN_literal_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {x : F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.literal x) h r h') :
    r = .field x ∧ h' = h := by
  cases ev; exact ⟨rfl, rfl⟩

theorem evalExprN_var_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {name : String} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.var name) h r h') :
    locals.find? (·.1 == name) = some (name, r) ∧ h' = h := by
  cases ev with | var hlook => exact ⟨hlook, rfl⟩

theorem evalExprN_let_bind_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {x : String} {e b : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.letValue (.bind x) e b) h r h') :
    ∃ v hm,
      EvalExprN world d types locals e h v hm ∧
      EvalExprN world d types ((x, v) :: locals) b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    simp [World.matchPattern, matchPatternWith] at hm
    subst hm
    exact ⟨_, _, hv, hb⟩

theorem evalExprN_let_wildcard_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {e b : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.letValue .wildcard e b) h r h') :
    ∃ v hm,
      EvalExprN world d types locals e h v hm ∧
      EvalExprN world d types locals b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    simp [World.matchPattern, matchPatternWith] at hm
    subst hm
    exact ⟨_, _, hv, hb⟩

theorem evalExprN_call_inv {world : World F} {d : Nat} {locals : Environment F Nat}
    {name : String} {args : List (Aiur.Generic.Expr F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals (.call name (some []) args) h r h') :
    ∃ d' vs hm, d' < d ∧
      EvalArgsN world d [] locals args h vs hm ∧
      EvalFnN world d' name vs hm r h' := by
  cases ev with
  | call hlt hargs hcal =>
    simp only [instanceName, Option.getD_some, List.map_nil, Instance.symbol, List.isEmpty_nil,
      ↓reduceIte] at hcal
    exact ⟨_, _, _, hlt, hargs, hcal⟩

theorem evalExprN_construct_inv {world : World F} {d : Nat} {locals : Environment F Nat}
    {en ctor : String} {args : List (Aiur.Generic.Expr F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals (.construct en (some []) ctor args) h r h') :
    ∃ vs, EvalArgsN world d [] locals args h vs h' ∧ r = .construct en ctor vs := by
  cases ev with
  | construct hargs =>
    exact ⟨_, hargs, by simp [instanceName, Instance.symbol]⟩

theorem evalExprN_store_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {e : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.store e) h r h') :
    ∃ v hm, EvalExprN world d types locals e h v hm ∧
      r = .ptr v.type hm.length ∧ h' = hm ++ [v] := by
  cases ev with | store hv => exact ⟨_, _, hv, rfl, rfl⟩

theorem evalExprN_load_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {e : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.load e) h r h') :
    ∃ vp, EvalExprN world d types locals e h vp h' ∧ loadValue h' vp = .ok r := by
  cases ev with | load hv hl => exact ⟨_, hv, hl⟩

theorem evalExprN_binary_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {op : BinOp} {lhs rhs : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.binary op lhs rhs) h r h') :
    ∃ x y hm, EvalExprN world d types locals lhs h x hm ∧
      EvalExprN world d types locals rhs hm y h' ∧ evalBinOp op x y = .ok r := by
  cases ev with | binary hl hr hop => exact ⟨_, _, _, hl, hr, hop⟩

theorem evalExprN_trap_elim {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {msg : String} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (qualifyExprF F (trapE msg)) h r h') : False :=
  trap_no_derivation ev.toEvalExpr

end EvalDepth

/-! ## Section 3: `LoweredWorld` and Program Extraction -/

section LoweredWorldSec

variable {F : Type} [Field F] [DecidableEq F]

/-- World hypothesis for a lowered `Fir.Program`: `lowerProgram P = .ok prog`,
`world` satisfies the `UInt64` library contracts, and every function in
`prog.functions` is bound in `world` under `Prog::<name>` with its qualified body. -/
structure LoweredWorld (P : Fir.Program) (prog : Aiur.Generic.Program Nat) (world : World F) : Prop where
  lowered : lowerProgram P = .ok prog
  u64 : U64Contracts world
  hasFn : ∀ g ∈ prog.functions,
    WorldHasFn world (qualified g.name) (g.params.map Prod.fst) (qualifyExprF F g.body)

/-- Build `LoweredWorld` directly from a prepared `Generic.Source F` whose functions
match `prog.functions` under `Prog::` qualification. -/
theorem LoweredWorld.ofSource {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    (hlow : lowerProgram P = .ok prog) (s : Generic.Source F)
    (hu64 : U64Contracts s.world)
    (hmatch : ∀ g ∈ prog.functions, ∃ f,
      s.program.findFunction? (qualified g.name) = some f ∧
      f.typeParams = [] ∧
      f.params.map Prod.fst = g.params.map Prod.fst ∧
      f.body = qualifyExprF F g.body) :
    LoweredWorld P prog s.world where
  lowered := hlow
  u64 := hu64
  hasFn := by
    intro g hg
    obtain ⟨f, hfind, htp, hparams, hbody⟩ := hmatch g hg
    have hnoDollar : (qualified g.name).toList.head? ≠ some '$' := by
      simp [qualified, moduleName]
    have hwf := worldHasFn_of_findFunction? s hnoDollar hfind htp
    rwa [hparams, hbody] at hwf

/-- Helper: extracting membership from `List.mapM` over `Except`. -/
private theorem mem_mapM_except {α β : Type*} {f : α → Except String β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      ∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y
  | [], ys, h, _, hx => by cases hx
  | a :: as, ys, h, x, hx => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases ha : f a with
    | error _ => simp [ha] at h
    | ok b =>
      simp only [ha] at h
      cases has : as.mapM f with
      | error _ => simp [has] at h
      | ok bs =>
        simp only [has, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact ⟨b, List.mem_cons_self, ha⟩
        · obtain ⟨y, hy, hfy⟩ := mem_mapM_except has x hmem
          exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- Helper: unpacking `lowerProgram P = .ok prog`. -/
theorem lowerProgram_inv {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    (h : lowerProgram P = .ok prog) :
    (P.ctors.map (·.key)).Nodup ∧
    (objCtorNames P).Nodup ∧
    ∃ fnGroups entries,
      P.funList.mapM (fun (f, fd) => funE ⟨P⟩ f fd) = .ok fnGroups ∧
      ((List.range P.exports.length).zip P.exports).mapM (fun (i, f) => entryE P i f) = .ok entries ∧
      prog.functions = entries ++ fnGroups.flatten ++ helpers ⟨P⟩ := by
  unfold lowerProgram at h
  by_cases hk : allDistinct (P.ctors.map (·.key)) = true
  · simp only [hk, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
    by_cases hn : allDistinct (objCtorNames P) = true
    · simp only [hn, ↓reduceIte] at h
      cases hfg : P.funList.mapM (fun (f, fd) => funE ⟨P⟩ f fd) with
      | error _ => simp [hfg] at h
      | ok fnGroups =>
        simp only [hfg] at h
        cases hen : ((List.range P.exports.length).zip P.exports).mapM (fun (i, f) => entryE P i f) with
        | error _ => simp [hen] at h
        | ok entries =>
          simp only [hen, Except.ok.injEq] at h
          subst h
          exact ⟨(allDistinct_iff_nodup _).mp hk, (allDistinct_iff_nodup _).mp hn,
            fnGroups, entries, rfl, rfl, rfl⟩
    · have hnf : allDistinct (objCtorNames P) = false := Bool.eq_false_iff.mpr hn
      simp [hnf, throw, throwThe, MonadExceptOf.throw] at h
  · have hkf : allDistinct (P.ctors.map (·.key)) = false := Bool.eq_false_iff.mpr hk
    simp [hkf, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

theorem LoweredWorld.ctors_keys_nodup {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    {world : World F} (lw : LoweredWorld P prog world) : (P.ctors.map (·.key)).Nodup :=
  (lowerProgram_inv lw.lowered).1

theorem LoweredWorld.ctors_names_nodup {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    {world : World F} (lw : LoweredWorld P prog world) : (objCtorNames P).Nodup :=
  (lowerProgram_inv lw.lowered).2.1

theorem LoweredWorld.primHelpers {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    {world : World F} (lw : LoweredWorld P prog world) : PrimHelpersWorld P world := by
  obtain ⟨_, _, _, _, _, _, hfuncs⟩ := lowerProgram_inv lw.lowered
  exact PrimHelpersWorld.ofFunctions lw.u64 fun g hg =>
    lw.hasFn g (by rw [hfuncs]; exact List.mem_append_right _ hg)

theorem LoweredWorld.hasFun {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    {world : World F} (lw : LoweredWorld P prog world)
    {f : FunId} {fd : Fir.Fun} (hfun : P.fun? f = some fd) (hsz : f < P.size) :
    let pns := (List.range fd.params.length).map localName
    ∃ body st,
      codeE ⟨P⟩ f (bindVm [] (fd.params.map Prod.fst) pns) [] fd.body
        { nextLocal := fd.params.length } = .ok (body, st) ∧
      WorldHasFn world (qualified (funName f)) pns (qualifyExprF F body) ∧
      (∀ g ∈ st.lifted, WorldHasFn world (qualified g.name) (g.params.map Prod.fst)
        (qualifyExprF F g.body)) := by
  obtain ⟨_, _, fnGroups, entries, hfg, _, hfuncs⟩ := lowerProgram_inv lw.lowered
  have hmemFL : (f, fd) ∈ P.funList := by
    simp only [Fir.Program.funList, List.mem_filterMap, List.mem_range]
    exact ⟨f, hsz, by simp [hfun]⟩
  obtain ⟨fns, hfnsMem, hfunE⟩ := mem_mapM_except hfg (f, fd) hmemFL
  obtain ⟨body, st, hcode, hfnsEq⟩ := funE_inv hfunE
  refine ⟨body, st, hcode, ?_, ?_⟩
  · let mainFn : Lower.Fn := {
      name := funName f
      params := ((List.range fd.params.length).map localName).map (·, objTy)
      result := objTy
      body := body
    }
    have hmemMain : mainFn ∈ prog.functions := by
      rw [hfuncs]
      apply List.mem_append_left
      apply List.mem_append_right
      rw [List.mem_flatten]
      exact ⟨fns, hfnsMem, by rw [hfnsEq]; exact List.mem_cons_self⟩
    have hwf := lw.hasFn mainFn hmemMain
    simpa [mainFn, List.map_map, Function.comp_def] using hwf
  · intro g hg
    have hmemG : g ∈ prog.functions := by
      rw [hfuncs]
      apply List.mem_append_left
      apply List.mem_append_right
      rw [List.mem_flatten]
      exact ⟨fns, hfnsMem, by rw [hfnsEq]; exact List.mem_cons_of_mem _ hg⟩
    exact lw.hasFn g hmemG

theorem LoweredWorld.hasEntry {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    {world : World F} (lw : LoweredWorld P prog world)
    {i : Nat} {f : FunId} (hexp : P.exports[i]? = some f) :
    ∃ fd, P.fun? f = some fd ∧ f < P.size ∧
      WorldHasFn world (qualified (entryName i))
        ((List.range fd.params.length).map entryParamName)
        (qualifyExprF F (callE (funName f) ((List.range fd.params.length).map fun j =>
          seqE (wordE (vE (entryParamName j))) (natE (vE (entryParamName j)))))) := by
  obtain ⟨_, _, fnGroups, entries, _, hen, hfuncs⟩ := lowerProgram_inv lw.lowered
  have hiLt : i < P.exports.length := (List.getElem?_eq_some_iff.mp hexp).1
  have hget : P.exports[i] = f := (List.getElem?_eq_some_iff.mp hexp).2
  have hmemZip : (i, f) ∈ (List.range P.exports.length).zip P.exports := by
    rw [List.mem_iff_getElem]
    refine ⟨i, by simp [hiLt], ?_⟩
    simp [hget]
  obtain ⟨ef, hefMem, hentryE⟩ := mem_mapM_except hen (i, f) hmemZip
  unfold entryE at hentryE
  cases hfd : P.fun? f with
  | none => simp [hfd, throw, throwThe, MonadExceptOf.throw] at hentryE
  | some fd =>
    simp only [hfd] at hentryE
    by_cases hsz : f < P.size
    · simp only [hsz, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hentryE
      subst hentryE
      let entFn : Lower.Fn := {
        name := entryName i
        params := (List.range fd.params.length).map fun j => (entryParamName j, (.field : Lower.Ty))
        result := objTy
        body := callE (funName f) ((List.range fd.params.length).map fun j =>
          seqE (wordE (vE (entryParamName j))) (natE (vE (entryParamName j))))
      }
      have hmemP : entFn ∈ prog.functions := by
        rw [hfuncs]
        exact List.mem_append_left _ (List.mem_append_left _ hefMem)
      have hwf := lw.hasFn entFn hmemP
      refine ⟨fd, rfl, hsz, ?_⟩
      simpa [entFn, List.map_map, Function.comp_def] using hwf
    · simp [hsz, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hentryE

end LoweredWorldSec

/-! ## Section 4: Lexical Environments, Captured Variables, and Join-Point Invariant -/

section EnvRelSec

variable {F : Type} [Field F]

/-- Lexical environment relation: every variable mapped in `vm` evaluates in `ρ` and
`locals` to `VR`-related values at heap `h`, and every Aiur name recorded in `vm`
(including shadowed names captured by `liveNames`) is bound in `locals`. -/
structure EnvRel (P : Fir.Program) (h : Heap F) (vm : VarMap) (ρ : Fir.Env)
    (locals : Environment F Nat) : Prop where
  rel : ∀ x nm, vm.lookup x = some nm →
    ∃ v w, ρ.get? x = some v ∧ locals.find? (·.1 == nm) = some (nm, w) ∧
      VR P objQName bytesQName h v w
  bound : ∀ nm ∈ vm.map Prod.snd, ∃ w, locals.find? (·.1 == nm) = some (nm, w)

theorem EnvRel.extend {P : Fir.Program} {h h' : Heap F} (ext : Heap.Extends h h')
    {vm : VarMap} {ρ : Fir.Env} {locals : Environment F Nat}
    (hr : EnvRel P h vm ρ locals) : EnvRel P h' vm ρ locals where
  rel x nm hlook := by
    obtain ⟨v, w, hρ, hloc, hvr⟩ := hr.rel x nm hlook
    exact ⟨v, w, hρ, hloc, hvr.extend ext⟩
  bound := hr.bound

private theorem lookup_mem_map_snd {vm : VarMap} {x : Var} {nm : String}
    (hlook : vm.lookup x = some nm) : nm ∈ vm.map Prod.snd := by
  induction vm with
  | nil => cases hlook
  | cons hd tl ih =>
    simp only [List.lookup] at hlook
    split at hlook
    · simp only [Option.some.injEq] at hlook; subst hlook; simp
    · exact List.mem_cons_of_mem _ (ih hlook)

theorem EnvRel.cons_fresh {P : Fir.Program} {h : Heap F} {vm : VarMap} {ρ : Fir.Env}
    {locals : Environment F Nat} {x : Var} {nx : String} {v : Fir.Val} {w : SourceValue F}
    (hr : EnvRel P h vm ρ locals) (hfresh : nx ∉ vm.map Prod.snd)
    (hvr : VR P objQName bytesQName h v w) :
    EnvRel P h ((x, nx) :: vm) (ρ.insert x v) ((nx, w) :: locals) where
  rel y ny hlook := by
    by_cases hyx : y = x
    · subst hyx
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hlook
      subst hlook
      exact ⟨v, w, NatMap.get?_insert_self ρ y v, by simp, hvr⟩
    · have hbeq : (y == x) = false := beq_false_of_ne hyx
      simp only [List.lookup, hbeq] at hlook
      obtain ⟨vy, wy, hρ, hloc, hvry⟩ := hr.rel y ny hlook
      have hne : nx ≠ ny := fun heq => hfresh (heq ▸ lookup_mem_map_snd hlook)
      have hneB : (nx == ny) = false := beq_false_of_ne hne
      exact ⟨vy, wy, by rw [NatMap.get?_insert_ne ρ v (Ne.symm hyx)]; exact hρ,
        by simp [hneB, hloc], hvry⟩
  bound nm hmem := by
    simp only [List.map_cons, List.mem_cons] at hmem
    rcases hmem with rfl | htl
    · exact ⟨w, by simp⟩
    · obtain ⟨wm, hloc⟩ := hr.bound nm htl
      have hne : nx ≠ nm := fun heq => hfresh (heq ▸ htl)
      have hneB : (nx == nm) = false := beq_false_of_ne hne
      exact ⟨wm, by simp [hneB, hloc]⟩

theorem EnvRel.cons_unused {P : Fir.Program} {h : Heap F} {vm : VarMap} {ρ : Fir.Env}
    {locals : Environment F Nat} {nm : String} {w : SourceValue F}
    (hr : EnvRel P h vm ρ locals) (hfresh : nm ∉ vm.map Prod.snd) :
    EnvRel P h vm ρ ((nm, w) :: locals) where
  rel y ny hlook := by
    obtain ⟨vy, wy, hρ, hloc, hvry⟩ := hr.rel y ny hlook
    have hne : nm ≠ ny := fun heq => hfresh (heq ▸ lookup_mem_map_snd hlook)
    have hneB : (nm == ny) = false := beq_false_of_ne hne
    exact ⟨vy, wy, hρ, by simp [hneB, hloc], hvry⟩
  bound s hs := by
    obtain ⟨ws, hloc⟩ := hr.bound s hs
    have hne : nm ≠ s := fun heq => hfresh (heq ▸ hs)
    have hneB : (nm == s) = false := beq_false_of_ne hne
    exact ⟨ws, by simp [hneB, hloc]⟩

/-- Every name in `names` looks up in `locals` to the corresponding value in `vals`. -/
def EvalCapArgs {F : Type} (locals : Environment F Nat) : List String → List (SourceValue F) → Prop
  | [], [] => True
  | nm :: nms, w :: ws => locals.find? (·.1 == nm) = some (nm, w) ∧ EvalCapArgs locals nms ws
  | _, _ => False

omit [Field F] in
theorem EvalCapArgs.length_eq {locals : Environment F Nat} :
    ∀ {nms : List String} {ws : List (SourceValue F)},
      EvalCapArgs locals nms ws → ws.length = nms.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, tl⟩ => congrArg Nat.succ tl.length_eq
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

omit [Field F] in
theorem EvalCapArgs.mem_bound {locals : Environment F Nat} :
    ∀ {nms : List String} {ws : List (SourceValue F)},
      EvalCapArgs locals nms ws → ∀ nm ∈ nms, ∃ w, locals.find? (·.1 == nm) = some (nm, w)
  | [], [], _, _, hm => by cases hm
  | a :: as, w :: ws, ⟨hd, tl⟩, nm, hm => by
    rcases List.mem_cons.mp hm with rfl | htl
    · exact ⟨w, hd⟩
    · exact tl.mem_bound nm htl
  | [], _ :: _, h, _, _ => False.elim h
  | _ :: _, [], h, _, _ => False.elim h

omit [Field F] in
theorem EvalCapArgs.cons_unused {locals : Environment F Nat} {nx : String} {wx : SourceValue F} :
    ∀ {nms : List String} {ws : List (SourceValue F)},
      nx ∉ nms → EvalCapArgs locals nms ws → EvalCapArgs ((nx, wx) :: locals) nms ws
  | [], [], _, _ => trivial
  | nm :: nms, w :: ws, hni, ⟨hd, tl⟩ => by
    have hne : nx ≠ nm := fun heq => hni (heq ▸ List.mem_cons_self)
    have hneB : (nx == nm) = false := beq_false_of_ne hne
    exact ⟨by simp [hneB, hd],
      tl.cons_unused (fun hm => hni (List.mem_cons_of_mem _ hm))⟩
  | [], _ :: _, _, h => False.elim h
  | _ :: _, [], _, h => False.elim h

omit [Field F] in
theorem EvalCapArgs.of_zip_nodup :
    ∀ {nms : List String} {ws : List (SourceValue F)} {extra : Environment F Nat},
      nms.Nodup → ws.length = nms.length →
      EvalCapArgs (nms.zip ws ++ extra) nms ws
  | [], [], _, _, _ => trivial
  | nm :: nms, w :: ws, extra, hnd, hlen => by
    rw [List.nodup_cons] at hnd
    have hlen' : ws.length = nms.length := by simpa using hlen
    have htl := EvalCapArgs.of_zip_nodup (extra := extra) hnd.2 hlen'
    exact ⟨by simp, htl.cons_unused hnd.1⟩
  | [], _ :: _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, hlen => by simp at hlen

omit [Field F] in
theorem find?_eq_of_evalCapArgs {locals : Environment F Nat} :
    ∀ {nms : List String} {ws : List (SourceValue F)} {nm : String},
      nms.Nodup → EvalCapArgs locals nms ws → nm ∈ nms →
      (nms.zip ws).find? (·.1 == nm) = locals.find? (·.1 == nm)
  | [], [], _, _, _, hm => by cases hm
  | a :: as, w :: ws, nm, hnd, ⟨hd, tl⟩, hm => by
    rw [List.nodup_cons] at hnd
    simp only [List.zip_cons_cons, List.find?_cons]
    by_cases hEq : a = nm
    · subst hEq; simp [hd]
    · have hbeq : (a == nm) = false := beq_false_of_ne hEq
      simp only [hbeq]
      rcases List.mem_cons.mp hm with rfl | hmem
      · exact False.elim (hEq rfl)
      · exact find?_eq_of_evalCapArgs hnd.2 tl hmem
  | [], _ :: _, _, _, h, _ => False.elim h
  | _ :: _, [], _, _, h, _ => False.elim h

omit [Field F] in
theorem evalCapArgs_of_subset {locals : Environment F Nat}
    {capNames : List String} {capVals : List (SourceValue F)}
    (hnd : capNames.Nodup) (hcap : EvalCapArgs locals capNames capVals) :
    ∀ {nms : List String} {ws : List (SourceValue F)},
      (∀ x ∈ nms, x ∈ capNames) → EvalCapArgs locals nms ws →
      EvalCapArgs (capNames.zip capVals) nms ws
  | [], [], _, _ => trivial
  | nm :: nms, w :: ws, hsub, ⟨hd, tl⟩ => by
    have hmem : nm ∈ capNames := hsub nm List.mem_cons_self
    have heq := find?_eq_of_evalCapArgs hnd hcap hmem
    exact ⟨by rw [heq]; exact hd,
      evalCapArgs_of_subset hnd hcap (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) tl⟩
  | [], _ :: _, _, h => False.elim h
  | _ :: _, [], _, h => False.elim h

omit [Field F] in
theorem EvalCapArgs.append_right {base extra : Environment F Nat} :
    ∀ {nms : List String} {ws : List (SourceValue F)},
      EvalCapArgs base nms ws → EvalCapArgs (base ++ extra) nms ws
  | [], [], _ => trivial
  | nm :: nms, w :: ws, ⟨hd, tl⟩ => ⟨by rw [List.find?_append, hd]; rfl, tl.append_right⟩
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

theorem EnvRel.of_capZip {P : Fir.Program} {h : Heap F} {vm : VarMap} {ρ : Fir.Env}
    {locals : Environment F Nat} {capNames : List String} {capVals : List (SourceValue F)}
    (hr : EnvRel P h vm ρ locals) (hnd : capNames.Nodup)
    (hcap : EvalCapArgs locals capNames capVals)
    (hsub : ∀ s ∈ vm.map Prod.snd, s ∈ capNames) :
    EnvRel P h vm ρ (capNames.zip capVals) where
  rel x nm hlook := by
    obtain ⟨v, w, hρ, hloc, hvr⟩ := hr.rel x nm hlook
    have heq := find?_eq_of_evalCapArgs hnd hcap (hsub nm (lookup_mem_map_snd hlook))
    exact ⟨v, w, hρ, by rw [heq]; exact hloc, hvr⟩
  bound nm hmem := by
    obtain ⟨w, hloc⟩ := hr.bound nm hmem
    have heq := find?_eq_of_evalCapArgs hnd hcap (hsub nm hmem)
    exact ⟨w, by rw [heq]; exact hloc⟩

theorem EnvRel.bindAll_append {P : Fir.Program} {h : Heap F} :
    ∀ {ps : List Var} {pns : List String} {vs : List Fir.Val} {ws : List (SourceValue F)}
      {vm : VarMap} {ρ : Fir.Env} {base : Environment F Nat},
      ps.length = pns.length →
      pns.Nodup →
      (∀ p ∈ pns, p ∉ base.map Prod.fst) →
      EnvRel P h vm ρ base →
      List.Forall₂ (VR P objQName bytesQName h) vs ws →
      vs.length = ps.length →
      EnvRel P h (bindVm vm ps pns) (bindAll ρ ps vs) (base ++ pns.zip ws) := by
  intro ps
  induction ps with
  | nil =>
    intro pns vs ws vm ρ base hlen _ _ henv hrel hvlen
    cases pns <;> cases vs <;> cases ws <;> simp_all [bindVm, bindAll]
  | cons x xs ih =>
    intro pns vs ws vm ρ base hlen hnd hdisj henv hrel hvlen
    cases pns with
    | nil => simp at hlen
    | cons pn pnt =>
      cases hrel with
      | nil => simp at hvlen
      | @cons v w vs' ws' hvr htl =>
        rw [List.nodup_cons] at hnd
        simp only [bindVm, bindAll, List.zip_cons_cons]
        have hlen' : xs.length = pnt.length := by simpa using hlen
        have hvlen' : vs'.length = xs.length := by simpa using hvlen
        have hpnDisj : pn ∉ base.map Prod.fst := hdisj pn List.mem_cons_self
        have hnoneBase : base.find? (·.1 == pn) = none := by
          rw [List.find?_eq_none]
          intro p hp
          simp only [beq_iff_eq]
          intro heq
          exact hpnDisj (List.mem_map.mpr ⟨p, hp, heq⟩)
        have henv1 : EnvRel P h ((x, pn) :: vm) (ρ.insert x v) (base ++ [(pn, w)]) :=
          { rel := fun y ny hlook => by
              by_cases hyx : y = x
              · subst hyx
                simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hlook
                subst hlook
                exact ⟨v, w, NatMap.get?_insert_self ρ y v,
                  by rw [List.find?_append, hnoneBase]; simp, hvr⟩
              · have hbeq : (y == x) = false := beq_false_of_ne hyx
                simp only [List.lookup, hbeq] at hlook
                obtain ⟨vy, wy, hρ, hloc, hvry⟩ := henv.rel y ny hlook
                exact ⟨vy, wy, by rw [NatMap.get?_insert_ne ρ v (Ne.symm hyx)]; exact hρ,
                  by rw [List.find?_append, hloc]; rfl, hvry⟩
            bound := fun nm hmem => by
              simp only [List.map_cons, List.mem_cons] at hmem
              rcases hmem with rfl | htl'
              · exact ⟨w, by rw [List.find?_append, hnoneBase]; simp⟩
              · obtain ⟨wm, hloc⟩ := henv.bound nm htl'
                exact ⟨wm, by rw [List.find?_append, hloc]; rfl⟩ }
        have hdisj' : ∀ p ∈ pnt, p ∉ (base ++ [(pn, w)]).map Prod.fst := by
          intro p hp hmem
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_singleton] at hmem
          rcases hmem with hb | rfl
          · exact hdisj p (List.mem_cons_of_mem _ hp) hb
          · exact hnd.1 hp
        have hres := ih (base := base ++ [(pn, w)]) hlen' hnd.2 hdisj' henv1 htl hvlen'
        simpa [List.append_assoc] using hres

end EnvRelSec

section JEnvRelSec

variable {F : Type} [Field F] [DecidableEq F]

/-- Depth-indexed join-point stack relation between static `jenv` and dynamic `J`
evaluated in `locals` at heap `h`. -/
inductive JEnvRel (P : Fir.Program) (world : World F) :
    Nat → Heap F → List JEntryL → List Fir.JEntry → Environment F Nat → Prop where
  | nil : JEnvRel P world d h [] [] locals
  | cons {d : Nat} {h : Heap F} {ji : JEntryL} {jrest : List JEntryL}
      {je : Fir.JEntry} {Jrest : List Fir.JEntry} {locals : Environment F Nat}
      {capVals : List (SourceValue F)}
      (idEq : ji.id = je.id)
      (fnQual : qualifyName ji.fnName = qualified ji.fnName)
      (arityEq : ji.paramCount = je.params.length)
      (capEval : EvalCapArgs locals ji.capNames capVals)
      (sound : ∀ d' < d, ∀ h1, Heap.Extends h h1 →
        ∀ vs ws r h2,
          List.Forall₂ (VR P objQName bytesQName h1) vs ws →
          vs.length = je.params.length →
          EvalFnN world d' (qualified ji.fnName) (capVals ++ ws) h1 r h2 →
          ∃ k v, Fir.eval P k (Fir.bindAll je.env je.params vs) (je.after Jrest) je.body = .ok v ∧
            VR P objQName bytesQName h2 v r)
      (tail : JEnvRel P world d h jrest Jrest locals) :
      JEnvRel P world d h (ji :: jrest) (je :: Jrest) locals

theorem JEnvRel.extend {P : Fir.Program} {world : World F} {d : Nat} {h h' : Heap F}
    (ext : Heap.Extends h h') {jenv : List JEntryL} {J : List Fir.JEntry}
    {locals : Environment F Nat} (hr : JEnvRel P world d h jenv J locals) :
    JEnvRel P world d h' jenv J locals := by
  induction hr with
  | nil => exact .nil
  | cons idEq fnQual arityEq capEval sound _ ih =>
    exact .cons idEq fnQual arityEq capEval
      (fun d' hd' h1 ext1 vs ws r h2 hrel hlen ev =>
        sound d' hd' h1 (ext.trans ext1) vs ws r h2 hrel hlen ev) ih

theorem JEnvRel.mono_depth {P : Fir.Program} {world : World F} {d₁ d₂ : Nat} (hle : d₁ ≤ d₂)
    {h : Heap F} {jenv : List JEntryL} {J : List Fir.JEntry} {locals : Environment F Nat}
    (hr : JEnvRel P world d₂ h jenv J locals) :
    JEnvRel P world d₁ h jenv J locals := by
  induction hr with
  | nil => exact .nil
  | cons idEq fnQual arityEq capEval sound _ ih =>
    exact .cons idEq fnQual arityEq capEval
      (fun d' hd' => sound d' (Nat.lt_of_lt_of_le hd' hle)) ih

theorem JEnvRel.cons_unused {P : Fir.Program} {world : World F} {d : Nat} {h : Heap F}
    {jenv : List JEntryL} {J : List Fir.JEntry} {locals : Environment F Nat}
    {nx : String} {wx : SourceValue F}
    (hfresh : nx ∉ jenv.flatMap (·.capNames))
    (hr : JEnvRel P world d h jenv J locals) :
    JEnvRel P world d h jenv J ((nx, wx) :: locals) := by
  induction hr with
  | nil => exact .nil
  | cons idEq fnQual arityEq capEval sound _ ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hfresh
    exact .cons idEq fnQual arityEq (capEval.cons_unused hfresh.1) sound (ih hfresh.2)

theorem JEnvRel.append_right {P : Fir.Program} {world : World F} {d : Nat} {h : Heap F}
    {jenv : List JEntryL} {J : List Fir.JEntry} {base extra : Environment F Nat}
    (hr : JEnvRel P world d h jenv J base) :
    JEnvRel P world d h jenv J (base ++ extra) := by
  induction hr with
  | nil => exact .nil
  | cons idEq fnQual arityEq capEval sound _ ih =>
    exact .cons idEq fnQual arityEq capEval.append_right sound ih

theorem JEnvRel.of_capZip {P : Fir.Program} {world : World F} {d : Nat} {h : Heap F}
    {jenv : List JEntryL} {J : List Fir.JEntry} {locals : Environment F Nat}
    {capNames : List String} {capVals : List (SourceValue F)}
    (hnd : capNames.Nodup) (hcap : EvalCapArgs locals capNames capVals)
    (hsub : ∀ s ∈ jenv.flatMap (·.capNames), s ∈ capNames)
    (hr : JEnvRel P world d h jenv J locals) :
    JEnvRel P world d h jenv J (capNames.zip capVals) := by
  induction hr with
  | nil => exact .nil
  | cons idEq fnQual arityEq capEval sound _ ih =>
    simp only [List.flatMap_cons, List.mem_append] at hsub
    exact .cons idEq fnQual arityEq
      (evalCapArgs_of_subset hnd hcap (fun x hx => hsub x (Or.inl hx)) capEval)
      sound
      (ih hcap fun x hx => hsub x (Or.inr hx))

theorem JEnvRel.cap_bound {P : Fir.Program} {world : World F} {d : Nat} {h : Heap F}
    {jenv : List JEntryL} {J : List Fir.JEntry} {locals : Environment F Nat}
    (hr : JEnvRel P world d h jenv J locals) :
    ∀ s ∈ jenv.flatMap (·.capNames), ∃ w, locals.find? (·.1 == s) = some (s, w) := by
  induction hr with
  | nil => intro s hs; simp at hs
  | cons _ _ _ capEval _ _ ih =>
    intro s hs
    simp only [List.flatMap_cons, List.mem_append] at hs
    rcases hs with h1 | h2
    · exact capEval.mem_bound s h1
    · exact ih s h2

theorem JEnvRel.find_lookup {P : Fir.Program} {world : World F} {d : Nat} {h : Heap F}
    {jenv : List JEntryL} {J : List Fir.JEntry} {locals : Environment F Nat}
    (hr : JEnvRel P world d h jenv J locals) {j : JoinId} {ji : JEntryL}
    (hfind : jenv.find? (·.id == j) = some ji) :
    ∃ je Jrest capVals,
      lookupJ j J = some (je, Jrest) ∧
      qualifyName ji.fnName = qualified ji.fnName ∧
      ji.paramCount = je.params.length ∧
      EvalCapArgs locals ji.capNames capVals ∧
      (∀ d' < d, ∀ h1, Heap.Extends h h1 →
        ∀ vs ws r h2,
          List.Forall₂ (VR P objQName bytesQName h1) vs ws →
          vs.length = je.params.length →
          EvalFnN world d' (qualified ji.fnName) (capVals ++ ws) h1 r h2 →
          ∃ k v, Fir.eval P k (Fir.bindAll je.env je.params vs) (je.after Jrest) je.body = .ok v ∧
            VR P objQName bytesQName h2 v r) := by
  induction hr with
  | nil => simp at hfind
  | cons idEq fnQual arityEq capEval sound tail ih =>
    rename_i ji' jrest je' Jrest loc' capVals'
    simp only [List.find?_cons] at hfind
    by_cases hEq : ji'.id = j
    · have hbeq : (ji'.id == j) = true := beq_iff_eq.mpr hEq
      rw [hbeq] at hfind
      simp only [Option.some.injEq] at hfind
      subst hfind
      have hje : je'.id = j := idEq ▸ hEq
      exact ⟨je', Jrest, capVals', by simp [lookupJ, hje], fnQual, arityEq, capEval, sound⟩
    · have hbeq : (ji'.id == j) = false := beq_false_of_ne hEq
      rw [hbeq] at hfind
      have hneJe : je'.id ≠ j := idEq ▸ hEq
      obtain ⟨je, Jrest', capVals'', hlook, hq, har, hcap, hsnd⟩ := ih hfind
      exact ⟨je, Jrest', capVals'', by simp [lookupJ, hneJe, hlook], hq, har, hcap, hsnd⟩

/-- Every name in `liveNames vm jenv` is bound in `locals`, so `EvalCapArgs` holds. -/
theorem exists_evalCapArgs_liveNames {P : Fir.Program} {world : World F} {d : Nat} {h : Heap F}
    {vm : VarMap} {ρ : Fir.Env} {jenv : List JEntryL} {J : List Fir.JEntry}
    {locals : Environment F Nat}
    (hvm : EnvRel P h vm ρ locals) (hjenv : JEnvRel P world d h jenv J locals) :
    ∃ capVals, EvalCapArgs locals (liveNames vm jenv) capVals := by
  have hall : ∀ s ∈ liveNames vm jenv, ∃ w, locals.find? (·.1 == s) = some (s, w) := by
    intro s hs
    have hmem : s ∈ vm.map Prod.snd ++ jenv.flatMap (·.capNames) :=
      List.mem_eraseDups.mp hs
    rw [List.mem_append] at hmem
    rcases hmem with h1 | h2
    · exact hvm.bound s h1
    · exact hjenv.cap_bound s h2
  have build : ∀ (nms : List String),
      (∀ s ∈ nms, ∃ w, locals.find? (·.1 == s) = some (s, w)) →
      ∃ ws, EvalCapArgs locals nms ws := by
    intro nms
    induction nms with
    | nil => intro _; exact ⟨[], trivial⟩
    | cons nm t ih =>
      intro hall'
      obtain ⟨w, hw⟩ := hall' nm List.mem_cons_self
      obtain ⟨wt, hwt⟩ := ih fun s hs => hall' s (List.mem_cons_of_mem _ hs)
      exact ⟨w :: wt, hw, hwt⟩
  exact build (liveNames vm jenv) hall

private theorem nodup_eraseDupsBy_loop {α : Type*} (r : α → α → Bool)
    (hrefl : ∀ a, r a a = true) :
    ∀ (l acc : List α), acc.Nodup → (List.eraseDupsBy.loop r l acc).Nodup
  | [], acc, hacc => by simpa [List.eraseDupsBy.loop] using List.nodup_reverse.mpr hacc
  | a :: l, acc, hacc => by
    simp only [List.eraseDupsBy.loop]
    split
    · exact nodup_eraseDupsBy_loop r hrefl l acc hacc
    · rename_i hne
      have hnotmem : a ∉ acc := by
        intro hmem
        have htrue : acc.any (r a) = true := List.any_eq_true.mpr ⟨a, hmem, hrefl a⟩
        rw [htrue] at hne
        exact Bool.noConfusion hne
      exact nodup_eraseDupsBy_loop r hrefl l (a :: acc) (List.nodup_cons.mpr ⟨hnotmem, hacc⟩)

theorem liveNames_nodup (vm : VarMap) (jenv : List JEntryL) :
    (liveNames vm jenv).Nodup := by
  unfold liveNames List.eraseDups List.eraseDupsBy
  exact nodup_eraseDupsBy_loop (· == ·) (fun _ => beq_self_eq_true _) _ [] List.nodup_nil

theorem mem_liveNames_of_vm {vm : VarMap} {jenv : List JEntryL} {s : String}
    (h : s ∈ vm.map Prod.snd) : s ∈ liveNames vm jenv :=
  List.mem_eraseDups.mpr (List.mem_append_left _ h)

theorem mem_liveNames_of_jenv {vm : VarMap} {jenv : List JEntryL} {s : String}
    (h : s ∈ jenv.flatMap (·.capNames)) : s ∈ liveNames vm jenv :=
  List.mem_eraseDups.mpr (List.mem_append_right _ h)

theorem AllLocalLt_liveNames {n : Nat} {vm : VarMap} {jenv : List JEntryL}
    (hvm : AllLocalLt n (vm.map Prod.snd)) (hj : AllLocalLt n (jenv.flatMap (·.capNames))) :
    AllLocalLt n (liveNames vm jenv) := by
  intro s hs
  have hmem := List.mem_eraseDups.mp hs
  rw [List.mem_append] at hmem
  rcases hmem with h1 | h2
  · exact hvm s h1
  · exact hj s h2

theorem AllLocalLt_bindVm {n m : Nat} :
    ∀ {vm : VarMap} {ps : List Var} {pns : List String},
      AllLocalLt n (vm.map Prod.snd) →
      (∀ p ∈ pns, ∃ k, k < m ∧ p = localName k) →
      n ≤ m →
      AllLocalLt m ((bindVm vm ps pns).map Prod.snd)
  | vm, [], _, hvm, _, hle => hvm.mono hle
  | vm, _ :: _, [], hvm, _, hle => hvm.mono hle
  | vm, x :: xs, pn :: pnt, hvm, hpns, hle => by
    simp only [bindVm]
    apply AllLocalLt_bindVm (n := m) (m := m) _ (fun p hp => hpns p (List.mem_cons_of_mem _ hp)) (Nat.le_refl m)
    intro s hs
    simp only [List.map_cons, List.mem_cons] at hs
    rcases hs with rfl | htl
    · exact hpns s List.mem_cons_self
    · exact hvm.mono hle s htl

end JEnvRelSec

/-! ## Section 5: Expressions, Projections, and Primitives over `EvalExprN` -/

section ExprSound

variable {F : Type} [Field F] [DecidableEq F]

theorem evalArgsN_append_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} :
    ∀ {xs ys : List (Aiur.Generic.Expr F)} {h h' : Heap F} {ws : List (SourceValue F)},
      EvalArgsN world d types locals (xs ++ ys) h ws h' →
      ∃ wxs wys hm, ws = wxs ++ wys ∧
        EvalArgsN world d types locals xs h wxs hm ∧
        EvalArgsN world d types locals ys hm wys h'
  | [], _, _, _, _, ev => ⟨[], _, _, rfl, .nil, ev⟩
  | _ :: _, _, _, _, _, .cons hd tl => by
    obtain ⟨wxs, wys, hm, rfl, hxs, hys⟩ := evalArgsN_append_inv tl
    exact ⟨_ :: wxs, wys, hm, rfl, .cons hd hxs, hys⟩

theorem eval_bytesE {world : World F} {d : Nat} {locals : Environment F Nat} :
    ∀ {bs : List UInt8} {h h' : Heap F} {r : SourceValue F},
      EvalExprN world d [] locals (qualifyExprF F (bytesE bs)) h r h' →
      BytesRep bytesQName h' bs r ∧ Heap.Extends h h'
  | [], h, h', r, ev => by
    simp only [bytesE, bytesNilE, qualifyExprF, qualifyExpr, qualifyName_bytes, Option.map_some,
      Aiur.Generic.Expr.map, List.map] at ev
    obtain ⟨vs, hargs, rfl⟩ := evalExprN_construct_inv ev
    cases hargs
    exact ⟨.nil, Heap.Extends.refl h⟩
  | b :: bs, h, h', r, ev => by
    simp only [bytesE, bytesConsE, qualifyExprF, qualifyExpr, qualifyName_bytes,
      Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
    obtain ⟨vs, hargs, rfl⟩ := evalExprN_construct_inv ev
    cases hargs with
    | cons h1 hrest =>
      cases hrest with
      | cons h2 hnil =>
        cases hnil
        obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv h1
        obtain ⟨bw, hm, evBs, rfl, rfl⟩ := evalExprN_store_inv h2
        obtain ⟨hrep, hext⟩ := eval_bytesE evBs
        have hty : bw.type = .enum bytesQName := hrep.type_eq
        rw [hty]
        have hat : (hm ++ [bw])[hm.length]? = some bw := by simp
        exact ⟨.cons hat (hrep.extend_append), hext.trans (Heap.Extends.snoc hm bw)⟩

theorem eval_argE {P : Fir.Program} {world : World F} {d : Nat}
    {vm : VarMap} {ρ : Fir.Env} {locals : Environment F Nat}
    {a : Arg} {e : Lower.Expr} {h h' : Heap F} {r : SourceValue F}
    (ha : argE vm a = .ok e) (henv : EnvRel P h vm ρ locals)
    (ev : EvalExprN world d [] locals (qualifyExprF F e) h r h') :
    ∃ v, a.eval ρ = some v ∧ VR P objQName bytesQName h' v r ∧ Heap.Extends h h' := by
  cases a with
  | var x =>
    simp only [argE] at ha
    cases hlook : vm.lookup x with
    | none => simp [hlook, throw, throwThe, MonadExceptOf.throw] at ha
    | some nx =>
      simp only [hlook, pure, Except.pure, Except.ok.injEq] at ha
      subst ha
      simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
      obtain ⟨hloc, rfl⟩ := evalExprN_var_inv ev
      obtain ⟨v, w, hρ, hloc', hvr⟩ := henv.rel x nx hlook
      rw [hloc', Option.some.injEq, Prod.mk.injEq] at hloc
      obtain ⟨_, rfl⟩ := hloc
      exact ⟨v, hρ, hvr, Heap.Extends.refl _⟩
  | lit l =>
    cases l with
    | nat n =>
      simp only [argE] at ha
      by_cases hlt : n < natLimit
      · simp only [hlt, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at ha
        subst ha
        simp only [natE, mk, litE, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
          Aiur.Generic.Expr.map, List.map] at ev
        obtain ⟨vs, hargs, rfl⟩ := evalExprN_construct_inv ev
        cases hargs with
        | cons h1 hnil =>
          cases hnil
          obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv h1
          exact ⟨.lit (.nat n), rfl, .nat hlt, Heap.Extends.refl _⟩
      · simp [hlt, throw, throwThe, MonadExceptOf.throw] at ha
    | str s =>
      simp only [argE, pure, Except.pure, Except.ok.injEq] at ha
      subst ha
      simp only [strE, mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
        Aiur.Generic.Expr.map, List.map] at ev
      obtain ⟨vs, hargs, rfl⟩ := evalExprN_construct_inv ev
      cases hargs with
      | cons h1 hnil =>
        cases hnil
        obtain ⟨hrep, hext⟩ := eval_bytesE h1
        exact ⟨.lit (.str s), rfl, .str hrep, hext⟩
  | erased =>
    simp only [argE, pure, Except.pure, Except.ok.injEq] at ha
    subst ha
    simp only [erasedE, mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
      Aiur.Generic.Expr.map, List.map] at ev
    obtain ⟨vs, hargs, rfl⟩ := evalExprN_construct_inv ev
    cases hargs
    exact ⟨.erased, rfl, .erased, Heap.Extends.refl h⟩

theorem eval_argsE {P : Fir.Program} {world : World F} {d : Nat}
    {vm : VarMap} {ρ : Fir.Env} {locals : Environment F Nat} :
    ∀ {as : List Arg} {es : List Lower.Expr} {h h' : Heap F} {ws : List (SourceValue F)},
      argsE vm as = .ok es → EnvRel P h vm ρ locals →
      EvalArgsN world d [] locals (es.map (qualifyExprF F)) h ws h' →
      ∃ vs, evalArgs ρ as = some vs ∧ List.Forall₂ (VR P objQName bytesQName h') vs ws ∧
        Heap.Extends h h'
  | [], es, h, h', ws, ha, _, ev => by
    simp only [argsE, List.mapM_nil, pure, Except.pure, Except.ok.injEq] at ha
    subst ha
    cases ev
    exact ⟨[], rfl, .nil, Heap.Extends.refl h⟩
  | a :: as, es, h, h', ws, ha, henv, ev => by
    simp only [argsE, List.mapM_cons, bind, Except.bind, pure, Except.pure] at ha
    cases ha1 : argE vm a with
    | error _ => simp [ha1] at ha
    | ok e1 =>
      simp only [ha1] at ha
      cases has : as.mapM (argE vm) with
      | error _ => simp [has] at ha
      | ok es' =>
        simp only [has, Except.ok.injEq] at ha
        subst ha
        simp only [List.map_cons] at ev
        cases ev with
        | cons hhd htl =>
          obtain ⟨v1, hv1, hvr1, ext1⟩ := eval_argE ha1 henv hhd
          obtain ⟨vs, hvs, hrel, ext2⟩ := eval_argsE has (henv.extend ext1) htl
          exact ⟨v1 :: vs, by simp [evalArgs, hv1, hvs],
            .cons (hvr1.extend ext2) hrel, ext1.trans ext2⟩

theorem eval_argsE_store {P : Fir.Program} {world : World F} {d : Nat}
    {vm : VarMap} {ρ : Fir.Env} {locals : Environment F Nat} :
    ∀ {as : List Arg} {es : List Lower.Expr} {h h' : Heap F} {ps : List (SourceValue F)},
      argsE vm as = .ok es → EnvRel P h vm ρ locals →
      EvalArgsN world d [] locals (es.map fun e => .store (qualifyExprF F e)) h ps h' →
      ∃ vs, evalArgs ρ as = some vs ∧ VRs P objQName bytesQName h' vs ps ∧ Heap.Extends h h'
  | [], es, h, h', ps, ha, _, ev => by
    simp only [argsE, List.mapM_nil, pure, Except.pure, Except.ok.injEq] at ha
    subst ha
    cases ev
    exact ⟨[], rfl, .nil, Heap.Extends.refl h⟩
  | a :: as, es, h, h', ps, ha, henv, ev => by
    simp only [argsE, List.mapM_cons, bind, Except.bind, pure, Except.pure] at ha
    cases ha1 : argE vm a with
    | error _ => simp [ha1] at ha
    | ok e1 =>
      simp only [ha1] at ha
      cases has : as.mapM (argE vm) with
      | error _ => simp [has] at ha
      | ok es' =>
        simp only [has, Except.ok.injEq] at ha
        subst ha
        simp only [List.map_cons] at ev
        cases ev with
        | cons hhd htl =>
          obtain ⟨w1, hm1, ev1, rfl, rfl⟩ := evalExprN_store_inv hhd
          obtain ⟨v1, hv1, hvr1, ext1⟩ := eval_argE ha1 henv ev1
          have hty : w1.type = .enum objQName := hvr1.type_eq
          rw [hty]
          have ext12 : Heap.Extends h (hm1 ++ [w1]) := ext1.trans (Heap.Extends.snoc hm1 w1)
          obtain ⟨vs, hvs, hvrs, ext3⟩ := eval_argsE_store has (henv.extend ext12) htl
          have hat1 : (hm1 ++ [w1])[hm1.length]? = some w1 := by simp
          have hat : h'[hm1.length]? = some w1 := ext3.getElem?_eq hat1
          have hvr1' : VR P objQName bytesQName h' v1 w1 :=
            hvr1.extend ((Heap.Extends.snoc hm1 w1).trans ext3)
          exact ⟨v1 :: vs, by simp [evalArgs, hv1, hvs], .cons hat hvr1' hvrs, ext12.trans ext3⟩

theorem eval_capNames {world : World F} {d : Nat} {locals : Environment F Nat} :
    ∀ {nms : List String} {capVals ws : List (SourceValue F)} {h h' : Heap F},
      EvalCapArgs locals nms capVals →
      EvalArgsN world d [] locals (nms.map fun nm => qualifyExprF F (vE nm)) h ws h' →
      ws = capVals ∧ h' = h
  | [], [], _, _, _, _, ev => by cases ev; exact ⟨rfl, rfl⟩
  | [], _ :: _, _, _, _, hcap, _ => False.elim hcap
  | _ :: _, [], _, _, _, hcap, _ => False.elim hcap
  | nm :: nms, c :: cs, _, _, _, ⟨hd, tl⟩, .cons h1 hrest => by
    simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at h1
    obtain ⟨hlook, rfl⟩ := evalExprN_var_inv h1
    rw [hd, Option.some.injEq, Prod.mk.injEq] at hlook
    obtain ⟨_, rfl⟩ := hlook
    obtain ⟨rfl, rfl⟩ := eval_capNames tl hrest
    exact ⟨rfl, rfl⟩

/-! ### Pattern-Matching Helpers for Projections and `case` -/

omit [Field F] [DecidableEq F] in
private theorem matchListWith_map {α β : Type}
    {matchOne : β → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {f : α → β} :
    ∀ (xs : List α) (vals : List (SourceValue F)),
      matchListWith matchOne (xs.map f) vals =
      matchListWith (fun a v => matchOne (f a) v) xs vals
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, v :: vs => by
    simp only [List.map_cons, matchListWith, bind, Except.bind]
    cases matchOne (f x) v with
    | error e => rfl
    | ok res =>
      cases res with
      | none => rfl
      | some b => simp only [matchListWith_map xs vs]

omit [Field F] in
private theorem matchListWith_attach_eq {world : World F} {h : Heap F} :
    ∀ (pats : List (Aiur.Generic.Pattern F)) (vals : List (SourceValue F)),
      matchListWith (fun pat val => matchPatternWith world.constant world.constDepth [] h pat.val val)
        pats.attach vals =
      matchListWith (World.matchPattern world [] h) pats vals
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, v :: vs => by
    simp only [List.attach_cons, matchListWith, World.matchPattern, bind, Except.bind]
    cases matchPatternWith world.constant world.constDepth [] h p v with
    | error e => rfl
    | ok res =>
      cases res with
      | none => rfl
      | some b =>
        rw [matchListWith_map]
        simp only [matchListWith_attach_eq ps vs, World.matchPattern]

omit [Field F] in
private theorem matchListWith_replicate_wildcard {world : World F} {h : Heap F} :
    ∀ (n : Nat) (ps : List (SourceValue F)),
      ps.length = n →
      matchListWith (World.matchPattern world [] h) (List.replicate n .wildcard) ps = .ok (some [])
  | 0, [], _ => rfl
  | 0, _ :: _, hlen => by simp at hlen
  | _ + 1, [], hlen => by simp at hlen
  | n + 1, _ :: ps, hlen => by
    have hlen' : ps.length = n := by simpa using hlen
    simp only [List.replicate_succ, matchListWith, bind, Except.bind, pure, Except.pure]
    have hw : world.matchPattern [] h .wildcard ‹_› = .ok (some []) := by
      simp [World.matchPattern, matchPatternWith, pure, Except.pure]
    rw [hw, matchListWith_replicate_wildcard n ps hlen']
    rfl

omit [Field F] in
private theorem matchListWith_projPats {world : World F} {h : Heap F} :
    ∀ (len start i : Nat) (ps : List (SourceValue F)),
      ps.length = len →
      matchListWith (World.matchPattern world [] h)
        ((List.range len).map fun j =>
          if start + j = i then (Aiur.Generic.Pattern.bind "q" : Aiur.Generic.Pattern F)
          else .wildcard) ps =
      .ok (some (if start ≤ i ∧ i < start + len then
        match ps[i - start]? with
        | some p => [("q", p)]
        | none => []
      else []))
  | 0, start, i, [], _ => by
    simp [matchListWith, pure, Except.pure]
  | 0, _, _, _ :: _, hlen => by simp at hlen
  | _ + 1, _, _, [], hlen => by simp at hlen
  | len + 1, start, i, p :: pt, hlen => by
    have hlen' : pt.length = len := by simpa using hlen
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have htailEq :
        (List.range len).map ((fun j => if start + j = i then
          (Aiur.Generic.Pattern.bind "q" : Aiur.Generic.Pattern F) else .wildcard) ∘ (· + 1)) =
        (List.range len).map (fun j => if (start + 1) + j = i then
          (Aiur.Generic.Pattern.bind "q" : Aiur.Generic.Pattern F) else .wildcard) := by
      apply List.map_congr_left
      intro j _
      have hadd : start + (j + 1) = (start + 1) + j := by omega
      simp [Function.comp, hadd]
    rw [htailEq]
    have ih := matchListWith_projPats (world := world) (h := h) len (start + 1) i pt hlen'
    by_cases hsi : start = i
    · subst hsi
      have hnot : ¬ (start + 1 ≤ start ∧ start < start + 1 + len) := by omega
      have hcond : start ≤ start ∧ start < start + (len + 1) := by omega
      have hbind : world.matchPattern [] h (.bind "q") p = .ok (some [("q", p)]) := by
        simp [World.matchPattern, matchPatternWith, pure, Except.pure]
      simp only [Nat.add_zero, ↓reduceIte, matchListWith, hbind, ih, hnot, hcond, Nat.sub_self,
        List.getElem?_cons_zero, List.append_nil, bind, Except.bind, pure, Except.pure, and_self]
    · have hne0 : start + 0 ≠ i := by omega
      have hiff : (start ≤ i ∧ i < start + (len + 1)) ↔ (start + 1 ≤ i ∧ i < start + 1 + len) := by
        omega
      have hwild : world.matchPattern [] h .wildcard p = .ok (some []) := by
        simp [World.matchPattern, matchPatternWith, pure, Except.pure]
      simp only [hne0, ↓reduceIte, matchListWith, hwild, ih, List.nil_append,
        bind, Except.bind, pure, Except.pure]
      by_cases hc : start + 1 ≤ i ∧ i < start + 1 + len
      · have hc' : start ≤ i ∧ i < start + (len + 1) := hiff.mpr hc
        have hsub : i - start = (i - (start + 1)) + 1 := by omega
        simp [hc, hc', hsub]
      · have hc' : ¬ (start ≤ i ∧ i < start + (len + 1)) := fun h => hc (hiff.mp h)
        simp only [hc, hc', ↓reduceIte]

omit [Field F] in
private theorem selectArm_append_inv {world : World F} {h : Heap F} {v : SourceValue F}
    {l1 l2 : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
    {b : Environment F Nat} {body : Aiur.Generic.Expr F}
    (hsel : SourceSemantics.selectArm world [] h v (l1 ++ l2) = .ok (some (b, body))) :
    SourceSemantics.selectArm world [] h v l1 = .ok (some (b, body)) ∨
    (SourceSemantics.selectArm world [] h v l1 = .ok none ∧
     SourceSemantics.selectArm world [] h v l2 = .ok (some (b, body))) := by
  induction l1 with
  | nil => exact Or.inr ⟨rfl, hsel⟩
  | cons arm rest ih =>
    rcases arm with ⟨pat, armBody⟩
    simp only [List.cons_append, SourceSemantics.selectArm, bind, Except.bind] at hsel ⊢
    cases hm : world.matchPattern [] h pat v with
    | error e => simp [hm] at hsel
    | ok res =>
      cases res with
      | some bs =>
        simp only [hm, pure, Except.pure] at hsel ⊢
        exact Or.inl hsel
      | none =>
        simp only [hm] at hsel ⊢
        exact ih hsel

theorem eval_projE {P : Fir.Program} {world : World F} {d : Nat}
    (fc : FieldCompatible F) (hnd : (objCtorNames P).Nodup)
    {locals : Environment F Nat} {nx : String} {c : CtorKey} {i : Nat}
    {v : Fir.Val} {w r : SourceValue F} {h h' : Heap F}
    (hloc : locals.find? (·.1 == nx) = some (nx, w))
    (hvr : VR P objQName bytesQName h v w)
    (ev : EvalExprN world d [] locals (qualifyExprF F (projE ⟨P⟩ nx c i)) h r h') :
    ∃ v', projVal P c i v = .ok v' ∧ VR P objQName bytesQName h' v' r ∧ Heap.Extends h h' := by
  let tableArm : List (Lower.Pat × Lower.Expr) := match (Cx.mk P).ctorEntry? c with
    | some (idx, entry) =>
      if i < entry.arity then
        [(pC (ctorNameOf idx entry.key)
          ((List.range entry.arity).map fun j => if j = i then .bind "q" else .wildcard),
          .load (vE "q"))]
      else []
    | none => []
  let natArm : List (Lower.Pat × Lower.Expr) :=
    if P.known.natSucc == some c && i == 0 then
      [(pN (.bind "q"), matchE (vE "q")
        [(.literal 0, trapE "Nat.zero has no field"),
         (.wildcard, natE (subE (vE "q") (litE 1)))])]
    else []
  change EvalExprN world d [] locals (qualifyExprF F
    (if (tableArm ++ natArm).isEmpty then trapE "projection of a missing field"
     else matchE (vE nx) (tableArm ++ natArm))) h r h' at ev
  cases hemp : (tableArm ++ natArm).isEmpty
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte, matchE, vE, qualifyExprF, qualifyExpr,
      Aiur.Generic.Expr.map] at ev
    cases ev with
    | matchValue evx hsel hbr =>
      obtain ⟨hlx, hmEq⟩ := evalExprN_var_inv evx
      rw [hmEq] at hsel hbr
      rw [hloc, Option.some.injEq, Prod.mk.injEq] at hlx
      obtain ⟨_, rfl⟩ := hlx
      rw [List.map_append, List.map_append] at hsel
      rcases selectArm_append_inv hsel with h1 | ⟨_, h2⟩
      · -- Matched `tableArm`
        dsimp only [tableArm] at h1
        cases hc : (Cx.mk P).ctorEntry? c with
        | none =>
          simp [hc, SourceSemantics.selectArm] at h1
        | some p =>
          rcases p with ⟨idx, entry⟩
          simp only [hc] at h1
          by_cases hi : i < entry.arity
          · simp only [hi, ↓reduceIte] at h1
            obtain ⟨hget, hkey⟩ := ctorEntry?_sound hc
            simp only [pC, vE, List.map_cons, List.map_nil, SourceSemantics.selectArm,
              qualifyPat, qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map,
              World.matchPattern, bind, Except.bind, pure, Except.pure] at h1
            cases w with
            | field _ | tuple _ | ptr _ _ => simp [matchPatternWith, pure, Except.pure] at h1
            | construct ew cw ps =>
              simp only [matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
                List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_map, List.length_range,
                bind, Except.bind, pure, Except.pure] at h1
              by_cases htest : (ew != objQName || cw != ctorNameOf idx entry.key ||
                  (entry.arity != ps.length)) = true
              · simp [htest] at h1
              · simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_ne_iff] at htest
                obtain ⟨⟨rfl, rfl⟩, hlen⟩ := htest
                have hpsLen : ps.length = entry.arity := hlen.symm
                have hpatMap :
                    List.map (Aiur.Generic.Pattern.map Nat.cast)
                      (List.map qualifyPat (List.map (fun j =>
                        if j = i then (Aiur.Generic.Pattern.bind "q" : Lower.Pat) else .wildcard)
                        (List.range entry.arity))) =
                    (List.range entry.arity).map (fun j =>
                      if 0 + j = i then (Aiur.Generic.Pattern.bind "q" : Aiur.Generic.Pattern F)
                      else .wildcard) := by
                  simp only [List.map_map]
                  apply List.map_congr_left
                  intro j _
                  by_cases hji : j = i <;>
                    simp [Function.comp, hji, qualifyPat, Aiur.Generic.Pattern.map]
                simp only [hpsLen, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at h1
                rw [matchListWith_attach_eq, hpatMap, matchListWith_projPats entry.arity 0 i ps hpsLen] at h1
                obtain ⟨ci, fs, rfl, hckey, hflen, hvrs⟩ := VR_ctor_inv hnd hget hvr
                obtain ⟨vi, addr, wi, hfsi, hpsi, hatAddr, hvrWi⟩ :=
                  VRs.getElem?_some (i := i) hvrs (by omega)
                simp [hi, hpsi] at h1
                obtain ⟨rfl, rfl⟩ := h1
                simp only [qualifyExpr, Aiur.Generic.Expr.map] at hbr
                obtain ⟨vp, evp, hload⟩ := evalExprN_load_inv hbr
                obtain ⟨hlq, rfl⟩ := evalExprN_var_inv evp
                simp only [List.cons_append, List.nil_append, List.find?_cons, beq_self_eq_true,
                  Option.some.injEq, Prod.mk.injEq, true_and] at hlq
                subst hlq
                simp [loadValue, hatAddr, hvrWi.type_eq] at hload
                subst hload
                refine ⟨vi, ?_, hvrWi, Heap.Extends.refl _⟩
                simp [projVal, Val.asCtor, hckey, hkey, hfsi, Result.ofOption]
          · simp [hi, SourceSemantics.selectArm] at h1
      · -- Matched `natArm`
        dsimp only [natArm] at h2
        by_cases hns : (P.known.natSucc == some c && i == 0) = true
        · simp only [hns, ↓reduceIte] at h2
          simp only [Bool.and_eq_true, beq_iff_eq] at hns
          obtain ⟨hsucc, rfl⟩ := hns
          simp only [pN, List.map_cons, List.map_nil, SourceSemantics.selectArm,
            qualifyPat, qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map,
            World.matchPattern, bind, Except.bind, pure, Except.pure] at h2
          cases w with
          | field _ | tuple _ | ptr _ _ => simp [matchPatternWith, pure, Except.pure] at h2
          | construct ew cw ps =>
            simp only [matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
              List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_cons, List.length_nil,
              bind, Except.bind, pure, Except.pure] at h2
            by_cases htest : (ew != objQName || cw != "N" || (1 != ps.length)) = true
            · simp [htest] at h2
            · simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_ne_iff] at htest
              obtain ⟨⟨rfl, rfl⟩, hlen⟩ := htest
              rcases ps with _ | ⟨xq, _ | _⟩ <;> simp at hlen
              simp only [bne_self_eq_false, Bool.or_self,
                List.attach_cons, List.attach_nil, List.map_nil, matchListWith, matchPatternWith,
                List.append_nil, bind, Except.bind, pure, Except.pure] at h2
              obtain ⟨rfl, rfl⟩ := h2
              obtain ⟨n, hn, rfl, rfl⟩ := VR_N_inv hvr
              simp only [matchE, vE, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
                Aiur.Generic.Pattern.map, List.map] at hbr
              cases hbr with
              | matchValue evq hsel2 hbr2 =>
                obtain ⟨hlq, hmqEq⟩ := evalExprN_var_inv evq
                rw [hmqEq] at hsel2 hbr2
                simp only [List.cons_append, List.nil_append, List.find?_cons, beq_self_eq_true,
                  Option.some.injEq, Prod.mk.injEq, true_and] at hlq
                subst hlq
                cases n with
                | zero =>
                  simp only [Nat.cast_zero, SourceSemantics.selectArm, World.matchPattern,
                    matchPatternWith, Aiur.Pattern.bindings, ↓reduceIte,
                    bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                    Prod.mk.injEq] at hsel2
                  obtain ⟨rfl, rfl⟩ := hsel2
                  exact False.elim (evalExprN_trap_elim hbr2)
                | succ m =>
                  have hne : (0 : F) ≠ ((m + 1 : Nat) : F) :=
                    Ne.symm (fc.ne_zero_of_pos (Nat.succ_pos m)
                      (lt_trans hn (by unfold natLimit; omega)))
                  simp only [Nat.cast_zero, SourceSemantics.selectArm, World.matchPattern,
                    matchPatternWith, Aiur.Pattern.bindings, hne, ↓reduceIte,
                    bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                    Prod.mk.injEq] at hsel2
                  obtain ⟨rfl, rfl⟩ := hsel2
                  simp only [natE, mk, subE, litE, qualifyExpr, qualifyName_obj, Option.map_some,
                    Aiur.Generic.Expr.map, List.map] at hbr2
                  obtain ⟨vs, hargs, rfl⟩ := evalExprN_construct_inv hbr2
                  cases hargs with
                  | cons evsub hnil =>
                    cases hnil
                    obtain ⟨v1, v2, _, ev1, ev2, hsub⟩ := evalExprN_binary_inv evsub
                    obtain ⟨hl1, rfl⟩ := evalExprN_var_inv ev1
                    obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv ev2
                    simp only [List.nil_append, List.cons_append, List.find?_cons, beq_self_eq_true,
                      Option.some.injEq, Prod.mk.injEq, true_and] at hl1
                    subst hl1
                    simp only [evalBinOp, Nat.cast_one, Nat.cast_add, add_sub_cancel_right,
                      Except.ok.injEq] at hsub
                    subst hsub
                    refine ⟨.lit (.nat m), ?_, .nat (by omega), Heap.Extends.refl _⟩
                    simp [projVal, Val.asCtor, hsucc, Result.ofOption]
        · simp [hns, SourceSemantics.selectArm] at h2
  · simp only [hemp, ↓reduceIte] at ev
    exact False.elim (evalExprN_trap_elim ev)

/-! ### Primitive Operations Soundness -/

omit [DecidableEq F] in
private theorem eval_boolPrim_vr {P : Fir.Program} (hkeys : (P.ctors.map (·.key)).Nodup)
    {tt ff : String} (hb : (Cx.mk P).boolNames = some (tt, ff)) (b : Bool) (h : Heap F) :
    ∃ v, boolVal P b = some v ∧
      VR P objQName bytesQName h v (.construct objQName (if b then tt else ff) []) := by
  unfold Cx.boolNames at hb
  cases hbt : P.known.boolTrue with
  | none => simp [hbt, bind, Option.bind] at hb
  | some kt =>
    cases hbf : P.known.boolFalse with
    | none => simp [hbt, hbf, bind, Option.bind] at hb
    | some kf =>
      cases hct : (Cx.mk P).ctorEntry? kt with
      | none => simp [hbt, hbf, hct, bind, Option.bind] at hb
      | some pt =>
        rcases pt with ⟨it, et⟩
        cases hcf : (Cx.mk P).ctorEntry? kf with
        | none => simp [hbt, hbf, hct, hcf, bind, Option.bind] at hb
        | some pf =>
          rcases pf with ⟨if_, ef⟩
          simp only [hbt, hbf, hct, hcf, bind, Option.bind] at hb
          by_cases har : (et.arity == 0 && ef.arity == 0) = true
          · simp only [har, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl⟩ := hb
            simp only [Bool.and_eq_true, beq_iff_eq] at har
            obtain ⟨hart, harf⟩ := har
            cases b with
            | true =>
              obtain ⟨hget, hkey⟩ := ctorEntry?_sound hct
              have hfind := ctorEntry?_find? hkeys hct
              let ci : CtorInfo := ⟨kt, et.tag, et.arity, 0, List.replicate et.arity .shared⟩
              refine ⟨.ctor ci [], ?_, ?_⟩
              · simp [boolVal, hbt, Program.ctorInfo?, CtorInfo.ofKey, hfind, ci]
              · simp only [↓reduceIte, hkey]
                exact .ctor hget hkey (by simp [hart]) .nil
            | false =>
              obtain ⟨hget, hkey⟩ := ctorEntry?_sound hcf
              have hfind := ctorEntry?_find? hkeys hcf
              let ci : CtorInfo := ⟨kf, ef.tag, ef.arity, 0, List.replicate ef.arity .shared⟩
              refine ⟨.ctor ci [], ?_, ?_⟩
              · simp [boolVal, hbf, Program.ctorInfo?, CtorInfo.ofKey, hfind, ci]
              · simp only [Bool.false_eq_true, ↓reduceIte, hkey]
                exact .ctor hget hkey (by simp [harf]) .nil
          · simp [har] at hb

theorem eval_prim {P : Fir.Program} {prog : Aiur.Generic.Program Nat} {world : World F} {d : Nat}
    (fc : FieldCompatible F) (lw : LoweredWorld P prog world)
    {vm : VarMap} {ρ : Fir.Env} {locals : Environment F Nat}
    {op : Prim} {fnName : String} {arity : Nat} {as : List Arg} {argEs : List Lower.Expr}
    {h h' : Heap F} {r : SourceValue F}
    (hprim : primFun op = .ok (fnName, arity))
    (hlen : as.length = arity)
    (hbool : isBoolPrim op = true → (Cx.mk P).boolNames.isSome = true)
    (hargs : argsE vm as = .ok argEs)
    (henv : EnvRel P h vm ρ locals)
    (ev : EvalExprN world d [] locals (qualifyExprF F (callE fnName argEs)) h r h') :
    ∃ v, evalRhs P ρ (.prim op as) = .ok v ∧ VR P objQName bytesQName h' v r ∧ Heap.Extends h h' := by
  simp only [callE, qualifyExprF, qualifyExpr, qualifyName_primFun hprim, Option.map_some,
    Aiur.Generic.Expr.map, List.map_map] at ev
  obtain ⟨_, ws, hm, _, hargsEv, hcal⟩ := evalExprN_call_inv ev
  have hargsEv' : EvalArgsN world d [] locals (argEs.map (qualifyExprF F)) h ws hm := hargsEv
  obtain ⟨vs, hvs, hrel, ext1⟩ := eval_argsE hargs henv hargsEv'
  have pw := lw.primHelpers
  have evFn := hcal.toEvalFn
  have hvslen : vs.length = arity := by
    have h1 : ∀ {as : List Arg} {vs : List Fir.Val}, evalArgs ρ as = some vs → vs.length = as.length := by
      intro as
      induction as with
      | nil => intro vs h; simp [evalArgs] at h; subst h; rfl
      | cons a tl ih =>
        intro vs h
        simp only [evalArgs] at h
        cases ha : a.eval ρ with
        | none => simp [ha] at h
        | some v =>
          cases htl : evalArgs ρ tl with
          | none => simp [ha, htl] at h
          | some vst =>
            simp only [ha, htl, Option.some.injEq] at h
            subst h
            exact congrArg Nat.succ (ih htl)
    rw [h1 hvs, hlen]
  cases op with
  | natAdd =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hvslen
    cases hrel with
    | cons hvr1 hrel2 =>
      cases hrel2 with
      | cons hvr2 hnil =>
        cases hnil
        obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ := pAdd_only_nat pw evFn
        obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
        obtain ⟨n2, hn2, rfl, rfl⟩ := VR_N_inv hvr2
        obtain ⟨hsum, rfl, rfl⟩ := pAdd_sound fc pw hn1 hn2 evFn
        exact ⟨.lit (.nat (n1 + n2)), by simp [evalRhs, hvs, primResult, natArgs, Prim.sem],
          .nat hsum, ext1⟩
  | natSub =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hvslen
    cases hrel with
    | cons hvr1 hrel2 =>
      cases hrel2 with
      | cons hvr2 hnil =>
        cases hnil
        obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ := pSub_only_nat pw evFn
        obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
        obtain ⟨n2, hn2, rfl, rfl⟩ := VR_N_inv hvr2
        obtain ⟨hres, rfl, rfl⟩ := pSub_sound fc pw hn1 hn2 evFn
        exact ⟨.lit (.nat (n1 - n2)), by simp [evalRhs, hvs, primResult, natArgs, Prim.sem],
          .nat hres, ext1⟩
  | natMul =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hvslen
    cases hrel with
    | cons hvr1 hrel2 =>
      cases hrel2 with
      | cons hvr2 hnil =>
        cases hnil
        obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ := pMul_only_nat pw evFn
        obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
        obtain ⟨n2, hn2, rfl, rfl⟩ := VR_N_inv hvr2
        obtain ⟨hres, rfl, rfl⟩ := pMul_sound fc pw hn1 hn2 evFn
        exact ⟨.lit (.nat (n1 * n2)), by simp [evalRhs, hvs, primResult, natArgs, Prim.sem],
          .nat hres, ext1⟩
  | natDiv =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hvslen
    cases hrel with
    | cons hvr1 hrel2 =>
      cases hrel2 with
      | cons hvr2 hnil =>
        cases hnil
        obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ := pDiv_only_nat pw evFn
        obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
        obtain ⟨n2, hn2, rfl, rfl⟩ := VR_N_inv hvr2
        obtain ⟨hres, rfl, rfl⟩ := pDiv_sound fc pw hn1 hn2 evFn
        exact ⟨.lit (.nat (if n2 == 0 then 0 else n1 / n2)),
          by simp [evalRhs, hvs, primResult, natArgs, Prim.sem], .nat hres, ext1⟩
  | natMod =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hvslen
    cases hrel with
    | cons hvr1 hrel2 =>
      cases hrel2 with
      | cons hvr2 hnil =>
        cases hnil
        obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ := pMod_only_nat pw evFn
        obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
        obtain ⟨n2, hn2, rfl, rfl⟩ := VR_N_inv hvr2
        obtain ⟨hres, rfl, rfl⟩ := pMod_sound fc pw hn1 hn2 evFn
        exact ⟨.lit (.nat (if n2 == 0 then n1 else n1 % n2)),
          by simp [evalRhs, hvs, primResult, natArgs, Prim.sem], .nat hres, ext1⟩
  | natPred =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | _⟩ <;> simp at hvslen
    cases hrel with
    | cons hvr1 hnil =>
      cases hnil
      obtain ⟨x1, rfl⟩ := pPred_only_nat pw evFn
      obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
      obtain ⟨hres, rfl, rfl⟩ := pPred_sound fc pw hn1 evFn
      exact ⟨.lit (.nat (n1 - 1)), by simp [evalRhs, hvs, primResult, natArgs, Prim.sem],
        .nat hres, ext1⟩
  | natLand =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hvslen
    cases hrel with
    | cons hvr1 hrel2 =>
      cases hrel2 with
      | cons hvr2 hnil =>
        cases hnil
        obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ := pLand_only_nat pw evFn
        obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
        obtain ⟨n2, hn2, rfl, rfl⟩ := VR_N_inv hvr2
        obtain ⟨hres, rfl, rfl⟩ := pLand_sound fc pw hn1 hn2 evFn
        exact ⟨.lit (.nat (n1 &&& n2)), by simp [evalRhs, hvs, primResult, natArgs, Prim.sem],
          .nat hres, ext1⟩
  | natLor =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hvslen
    cases hrel with
    | cons hvr1 hrel2 =>
      cases hrel2 with
      | cons hvr2 hnil =>
        cases hnil
        obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ := pLor_only_nat pw evFn
        obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
        obtain ⟨n2, hn2, rfl, rfl⟩ := VR_N_inv hvr2
        obtain ⟨hres, rfl, rfl⟩ := pLor_sound fc pw hn1 hn2 evFn
        exact ⟨.lit (.nat (n1 ||| n2)), by simp [evalRhs, hvs, primResult, natArgs, Prim.sem],
          .nat hres, ext1⟩
  | natXor =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hvslen
    cases hrel with
    | cons hvr1 hrel2 =>
      cases hrel2 with
      | cons hvr2 hnil =>
        cases hnil
        obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ := pXor_only_nat pw evFn
        obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
        obtain ⟨n2, hn2, rfl, rfl⟩ := VR_N_inv hvr2
        obtain ⟨hres, rfl, rfl⟩ := pXor_sound fc pw hn1 hn2 evFn
        exact ⟨.lit (.nat (n1 ^^^ n2)), by simp [evalRhs, hvs, primResult, natArgs, Prim.sem],
          .nat hres, ext1⟩
  | natBeq =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hvslen
    have hbn := hbool rfl
    cases hb : (Cx.mk P).boolNames with
    | none => simp [hb] at hbn
    | some tf =>
      rcases tf with ⟨tt, ff⟩
      cases hrel with
      | cons hvr1 hrel2 =>
        cases hrel2 with
        | cons hvr2 hnil =>
          cases hnil
          obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ := pBeq_only_nat pw hb evFn
          obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
          obtain ⟨n2, hn2, rfl, rfl⟩ := VR_N_inv hvr2
          obtain ⟨rfl, rfl⟩ := pBeq_sound fc pw hb hn1 hn2 evFn
          obtain ⟨vb, hvb, hvrB⟩ := eval_boolPrim_vr lw.ctors_keys_nodup hb (n1 == n2) h'
          exact ⟨vb, by simp [evalRhs, hvs, primResult, natArgs, Prim.sem, hvb, Result.ofOption],
            hvrB, ext1⟩
  | natBle =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hvslen
    have hbn := hbool rfl
    cases hb : (Cx.mk P).boolNames with
    | none => simp [hb] at hbn
    | some tf =>
      rcases tf with ⟨tt, ff⟩
      cases hrel with
      | cons hvr1 hrel2 =>
        cases hrel2 with
        | cons hvr2 hnil =>
          cases hnil
          obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ := pBle_only_nat pw hb evFn
          obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
          obtain ⟨n2, hn2, rfl, rfl⟩ := VR_N_inv hvr2
          obtain ⟨rfl, rfl⟩ := pBle_sound fc pw hb hn1 hn2 evFn
          obtain ⟨vb, hvb, hvrB⟩ := eval_boolPrim_vr lw.ctors_keys_nodup hb (decide (n1 ≤ n2)) h'
          exact ⟨vb, by simp [evalRhs, hvs, primResult, natArgs, Prim.sem, hvb, Result.ofOption],
            hvrB, ext1⟩
  | natBlt =>
    simp only [primFun, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprim
    obtain ⟨rfl, rfl⟩ := hprim
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hvslen
    have hbn := hbool rfl
    cases hb : (Cx.mk P).boolNames with
    | none => simp [hb] at hbn
    | some tf =>
      rcases tf with ⟨tt, ff⟩
      cases hrel with
      | cons hvr1 hrel2 =>
        cases hrel2 with
        | cons hvr2 hnil =>
          cases hnil
          obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ := pBlt_only_nat pw hb evFn
          obtain ⟨n1, hn1, rfl, rfl⟩ := VR_N_inv hvr1
          obtain ⟨n2, hn2, rfl, rfl⟩ := VR_N_inv hvr2
          obtain ⟨rfl, rfl⟩ := pBlt_sound fc pw hb hn1 hn2 evFn
          obtain ⟨vb, hvb, hvrB⟩ := eval_boolPrim_vr lw.ctors_keys_nodup hb (decide (n1 < n2)) h'
          exact ⟨vb, by simp [evalRhs, hvs, primResult, natArgs, Prim.sem, hvb, Result.ofOption],
            hvrB, ext1⟩
  | natPow | natGcd | natShl | natShr =>
    simp [primFun, throw, throwThe, MonadExceptOf.throw] at hprim

end ExprSound

/-! ## Section 6: `firstPerKey`, `ctorArms`, and `eval_caseE` -/

section CaseSound

variable {F : Type} [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem firstPerKey_find?_eq :
    ∀ (acc alts : List (CtorKey × Lower.Expr)) (k : CtorKey),
      (firstPerKey acc alts).find? (·.1 == k) =
      (acc.reverse.find? (·.1 == k)).or (alts.find? (·.1 == k))
  | acc, [], k => by simp [firstPerKey]
  | acc, (k', e) :: rest, k => by
    unfold firstPerKey
    by_cases hany : acc.any (·.1 == k') = true
    · simp only [hany, ↓reduceIte]
      rw [firstPerKey_find?_eq acc rest k]
      by_cases hkk : k' = k
      · subst hkk
        obtain ⟨p, hp, hpk⟩ := List.any_eq_true.mp hany
        have hpRev : p ∈ acc.reverse := List.mem_reverse.mpr hp
        cases hf : acc.reverse.find? (·.1 == p.1) with
        | none =>
          have := (List.find?_eq_none.mp hf) p hpRev
          simp at this
        | some q =>
          have hpk' : p.1 = k' := beq_iff_eq.mp hpk
          rw [hpk'] at hf
          simp [hf]
      · have hbeq : (k' == k) = false := beq_false_of_ne hkk
        simp [hbeq]
    · simp only [hany, Bool.false_eq_true, ↓reduceIte]
      rw [firstPerKey_find?_eq ((k', e) :: acc) rest k]
      simp only [List.reverse_cons, List.find?_append]
      rw [Option.or_assoc, ← List.find?_append]
      rfl

omit [Field F] [DecidableEq F] in
theorem firstPerKey_nil_find? (alts : List (CtorKey × Lower.Expr)) (k : CtorKey) :
    (firstPerKey [] alts).find? (·.1 == k) = alts.find? (·.1 == k) := by
  simpa using firstPerKey_find?_eq [] alts k

private theorem selectArm_ctorArms_miss {P : Fir.Program} {world : World F} {h : Heap F}
    {cname : String} {ps : List (SourceValue F)}
    (hmiss : ∀ idx k, ctorNameOf idx k ≠ cname) :
    ∀ (xs : List (CtorKey × Lower.Expr)),
      SourceSemantics.selectArm world [] h (.construct objQName cname ps)
        ((ctorArms ⟨P⟩ xs).map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok none
  | [] => rfl
  | (k, body) :: rest => by
    unfold ctorArms
    cases hc : (Cx.mk P).ctorEntry? k with
    | none => exact selectArm_ctorArms_miss hmiss rest
    | some p =>
      rcases p with ⟨idx, entry⟩
      have hne : cname ≠ ctorNameOf idx entry.key := Ne.symm (hmiss idx entry.key)
      have hbne : (cname != ctorNameOf idx entry.key) = true := bne_iff_ne.mpr hne
      simp only [List.map_cons, pC, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
        qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol, hbne,
        Bool.or_true, Bool.true_or, ↓reduceIte, bind, Except.bind, pure, Except.pure]
      exact selectArm_ctorArms_miss hmiss rest

private theorem selectArm_ctorArms_ctor {P : Fir.Program} {world : World F} {h : Heap F}
    (hnd : (objCtorNames P).Nodup) (hkeys : (P.ctors.map (·.key)).Nodup)
    {idx : Nat} {entry : CtorTableEntry} {ps : List (SourceValue F)}
    (atIdx : P.ctors[idx]? = some entry) (hlen : ps.length = entry.arity) :
    ∀ (xs : List (CtorKey × Lower.Expr)),
      SourceSemantics.selectArm world [] h (.construct objQName (ctorNameOf idx entry.key) ps)
        ((ctorArms ⟨P⟩ xs).map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) =
      .ok ((xs.find? (·.1 == entry.key)).map fun p => ([], qualifyExprF F p.2))
  | [] => rfl
  | (k, body) :: rest => by
    unfold ctorArms
    by_cases hk : k = entry.key
    · subst hk
      have hc : (Cx.mk P).ctorEntry? entry.key = some (idx, entry) :=
        ctorEntry?_complete hkeys atIdx
      simp only [hc, List.map_cons, List.find?_cons, beq_self_eq_true, Option.map_some]
      have hrepMap :
          List.map (Aiur.Generic.Pattern.map Nat.cast)
            (List.map qualifyPat (List.replicate entry.arity (Aiur.Generic.Pattern.wildcard : Lower.Pat))) =
          List.replicate entry.arity (Aiur.Generic.Pattern.wildcard : Aiur.Generic.Pattern F) := by
        simp [List.map_replicate, qualifyPat, Aiur.Generic.Pattern.map]
      simp only [pC, SourceSemantics.selectArm, qualifyPatF, qualifyPat, qualifyTy, objTy,
        qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith,
        constructorName, Ty.subst, Ty.toCore, Instance.symbol, List.map_nil, List.isEmpty_nil,
        ↓reduceIte, hrepMap, List.length_replicate, hlen, bne_self_eq_false, Bool.or_self,
        Bool.false_eq_true, bind, Except.bind, pure, Except.pure]
      rw [matchListWith_attach_eq, matchListWith_replicate_wildcard entry.arity ps hlen]
    · have hbeq : (k == entry.key) = false := beq_false_of_ne hk
      simp only [List.find?_cons, hbeq]
      cases hc : (Cx.mk P).ctorEntry? k with
      | none => exact selectArm_ctorArms_ctor hnd hkeys atIdx hlen rest
      | some p =>
        rcases p with ⟨idx', entry'⟩
        obtain ⟨hget', hkey'⟩ := ctorEntry?_sound hc
        have hneName : ctorNameOf idx entry.key ≠ ctorNameOf idx' entry'.key := by
          intro heq
          obtain ⟨_, hentryEq⟩ := ctorNameOf_inj_of_nodup hnd atIdx hget' heq
          exact hk (hkey'.symm.trans (congrArg CtorTableEntry.key hentryEq.symm))
        have hbne : (ctorNameOf idx entry.key != ctorNameOf idx' entry'.key) = true :=
          bne_iff_ne.mpr hneName
        simp only [List.map_cons, pC, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
          qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol, hbne,
          Bool.or_true, Bool.true_or, ↓reduceIte, bind, Except.bind, pure, Except.pure]
        exact selectArm_ctorArms_ctor hnd hkeys atIdx hlen rest

omit [Field F] [DecidableEq F] in
private theorem altsE_find_sound {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL} :
    ∀ {alts : List Alt} {st st1 : LowerState} {altEs : List (CtorKey × Lower.Expr)} {k : CtorKey},
      altsE cx fid vm jenv alts st = .ok (altEs, st1) →
      (∀ p, altEs.find? (·.1 == k) = some p →
        ∃ b stA stB,
          b.size ≤ Code.altsSize alts ∧
          codeE cx fid vm jenv b stA = .ok (p.2, stB) ∧
          st.nextLocal ≤ stA.nextLocal ∧
          (∀ g ∈ stB.lifted, g ∈ st1.lifted) ∧
          ∀ kc ρ J d, Fir.evalAlts cx.P kc ρ J k alts d = Fir.eval cx.P kc ρ J b) ∧
      (altEs.find? (·.1 == k) = none →
        ∀ kc ρ J d, Fir.evalAlts cx.P kc ρ J k alts d =
          match d with | some dc => Fir.eval cx.P kc ρ J dc | none => .stuck)
  | [], st, st1, altEs, k, h => by
    obtain ⟨rfl, rfl⟩ := altsE_nil_inv h
    exact ⟨fun _ hp => by simp at hp, fun _ kc ρ J d => Fir.evalAlts_nil cx.P kc ρ J k d⟩
  | .mk k' b :: rest, st, st1, altEs, k, h => by
    obtain ⟨be, stMid, re, hb, hr, rfl⟩ := altsE_cons_inv h
    obtain ⟨hle1, t1, hlif1⟩ := codeE_state_mono cx fid vm jenv b st stMid be hb
    obtain ⟨_, t2, hlif2⟩ := altsE_state_mono cx fid vm jenv rest stMid st1 re hr
    obtain ⟨ihSome, ihNone⟩ := altsE_find_sound (k := k) hr
    constructor
    · intro p hp
      simp only [List.find?_cons] at hp
      by_cases hk : k' = k
      · have hbeq : (k' == k) = true := beq_iff_eq.mpr hk
        simp only [hbeq, Option.some.injEq] at hp
        subst hp
        refine ⟨b, st, stMid, by simp [Code.altsSize], hb, Nat.le_refl _, ?_, ?_⟩
        · intro g hg; rw [hlif2]; exact List.mem_append_left _ hg
        · intro kc ρ J d; rw [Fir.evalAlts_cons]; simp [hk]
      · have hbeq : (k' == k) = false := beq_false_of_ne hk
        simp only [hbeq] at hp
        obtain ⟨b', stA, stB, hsz, hcode, hleA, hlifB, hev⟩ := ihSome p hp
        refine ⟨b', stA, stB, by simp only [Code.altsSize]; omega, hcode,
          Nat.le_trans hle1 hleA, hlifB, ?_⟩
        intro kc ρ J d
        rw [Fir.evalAlts_cons]
        simp only [hk, ↓reduceIte]
        exact hev kc ρ J d
    · intro hnone kc ρ J d
      simp only [List.find?_cons] at hnone
      by_cases hk : k' = k
      · have hbeq : (k' == k) = true := beq_iff_eq.mpr hk
        simp [hbeq] at hnone
      · have hbeq : (k' == k) = false := beq_false_of_ne hk
        simp only [hbeq] at hnone
        rw [Fir.evalAlts_cons]
        simp only [hk, ↓reduceIte]
        exact ihNone hnone kc ρ J d

theorem eval_caseE {P : Fir.Program} {world : World F} {dDepth : Nat}
    (fc : FieldCompatible F) (hnd : (objCtorNames P).Nodup)
    (hkeys : (P.ctors.map (·.key)).Nodup)
    {fid : FunId} {vm : VarMap} {jenv : List JEntryL} {x : Var} {nx : String}
    {alts : List Alt} {d : Option Code}
    {st st1 st' : LowerState} {altEs : List (CtorKey × Lower.Expr)} {dE : Option Lower.Expr}
    {ρ : Fir.Env} {J : List Fir.JEntry} {locals : Environment F Nat}
    {h h' : Heap F} {r : SourceValue F}
    (hlook : vm.lookup x = some nx)
    (halts : altsE ⟨P⟩ fid vm jenv alts st = .ok (altEs, st1))
    (hd : optE ⟨P⟩ fid vm jenv d st1 = .ok (dE, st'))
    (hlocVm : AllLocalLt st.nextLocal (vm.map Prod.snd))
    (hlocJ : AllLocalLt st.nextLocal (jenv.flatMap (·.capNames)))
    (henv : EnvRel P h vm ρ locals)
    (hjenv : JEnvRel P world dDepth h jenv J locals)
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F (caseE ⟨P⟩ nx altEs dE)) h r h') :
    ∃ b stA stB be locals',
      b.size < (Code.case x alts d).size ∧
      codeE ⟨P⟩ fid vm jenv b stA = .ok (be, stB) ∧
      st.nextLocal ≤ stA.nextLocal ∧
      (∀ g ∈ stB.lifted, g ∈ st'.lifted) ∧
      EnvRel P h vm ρ locals' ∧
      JEnvRel P world dDepth h jenv J locals' ∧
      EvalExprN world dDepth [] locals' (qualifyExprF F be) h r h' ∧
      (∀ kc, Fir.eval P kc ρ J (.case x alts d) = Fir.eval P kc ρ J b) := by
  obtain ⟨v, w, hρx, hlocx, hvr⟩ := henv.rel x nx hlook
  obtain ⟨hle1, _, hlif1⟩ := altsE_state_mono ⟨P⟩ fid vm jenv alts st st1 altEs halts
  obtain ⟨_, t2, hlif2⟩ := optE_state_mono ⟨P⟩ fid vm jenv d st1 st' dE hd
  have hlifAlts : ∀ g ∈ st1.lifted, g ∈ st'.lifted := fun g hg => by
    rw [hlif2]; exact List.mem_append_left _ hg
  have hqVm : "q" ∉ vm.map Prod.snd := fun hm => hlocVm.ne_q "q" hm rfl
  have hqJ : "q" ∉ jenv.flatMap (·.capNames) := fun hm => hlocJ.ne_q "q" hm rfl
  -- Helper: reducing `pick (some k)` or fallback for a given `k` with `v.asCtor P.known = some (k, fs)`
  have finishKey : ∀ (k : CtorKey) (fs : List Fir.Val) (locals' : Environment F Nat)
      (be : Lower.Expr),
      v.asCtor P.known = some (k, fs) →
      be = (((firstPerKey [] altEs).find? (·.1 == k)).map (·.2)).getD (dE.getD (trapE "no alternative")) →
      EnvRel P h vm ρ locals' →
      JEnvRel P world dDepth h jenv J locals' →
      EvalExprN world dDepth [] locals' (qualifyExprF F be) h r h' →
      ∃ b stA stB be' locals'',
        b.size < (Code.case x alts d).size ∧
        codeE ⟨P⟩ fid vm jenv b stA = .ok (be', stB) ∧
        st.nextLocal ≤ stA.nextLocal ∧
        (∀ g ∈ stB.lifted, g ∈ st'.lifted) ∧
        EnvRel P h vm ρ locals'' ∧
        JEnvRel P world dDepth h jenv J locals'' ∧
        EvalExprN world dDepth [] locals'' (qualifyExprF F be') h r h' ∧
        (∀ kc, Fir.eval P kc ρ J (.case x alts d) = Fir.eval P kc ρ J b) := by
    intro k fs locals' be hasCtor hbe henv' hjenv' evBe
    rw [firstPerKey_nil_find?] at hbe
    obtain ⟨hSome, hNone⟩ := altsE_find_sound (k := k) halts
    cases hf : altEs.find? (·.1 == k) with
    | some p =>
      rw [hf] at hbe
      simp only [Option.map_some, Option.getD_some] at hbe
      subst hbe
      obtain ⟨b, stA, stB, hsz, hcode, hleA, hlifB, hevAlts⟩ := hSome p hf
      refine ⟨b, stA, stB, p.2, locals', by simp only [Code.size]; omega, hcode, hleA,
        fun g hg => hlifAlts g (hlifB g hg), henv', hjenv', evBe, ?_⟩
      intro kc
      rw [Fir.eval_case, hρx]
      simp only [Result.ofOption, Result.bind_ok, hasCtor]
      exact hevAlts kc ρ J d
    | none =>
      rw [hf] at hbe
      simp only [Option.map_none, Option.getD_none] at hbe
      cases d with
      | none =>
        obtain ⟨rfl, _⟩ := optE_none_inv hd
        simp only [Option.getD_none] at hbe
        subst hbe
        exact False.elim (evalExprN_trap_elim evBe)
      | some dc =>
        obtain ⟨de, hcodeD, rfl⟩ := optE_some_inv hd
        simp only [Option.getD_some] at hbe
        rw [hbe] at evBe
        refine ⟨dc, st1, st', de, locals', by simp only [Code.size, Code.optSize]; omega,
          hcodeD, hle1, fun _ hg => hg, henv', hjenv', evBe, ?_⟩
        intro kc
        rw [Fir.eval_case, hρx]
        simp only [Result.ofOption, Result.bind_ok, hasCtor]
        exact hNone hf kc ρ J (some dc)
  -- Unfold `caseE` and invert outer `matchValue`
  unfold caseE at ev
  simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
  cases ev with
  | matchValue evx hsel hbr =>
    obtain ⟨hlx, hmEq⟩ := evalExprN_var_inv evx
    rw [hmEq] at hsel hbr
    rw [hlocx, Option.some.injEq, Prod.mk.injEq] at hlx
    obtain ⟨_, rfl⟩ := hlx
    rw [List.map_append, List.map_append, List.map_append, List.map_append] at hsel
    cases hvr with
    | @nat n hn =>
      have hmiss : SourceSemantics.selectArm world [] h (.construct objQName "N" [.field (n : F)])
          (List.map (fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2))
            (ctorArms ⟨P⟩ (firstPerKey [] altEs))) = .ok none := by
        simpa [qualifyPatF, qualifyExprF] using
          selectArm_ctorArms_miss (P := P) (world := world) (h := h) (cname := "N")
            (ps := [.field (n : F)]) ctorNameOf_ne_N (firstPerKey [] altEs)
      rcases selectArm_append_inv hsel with h12 | ⟨h12none, h3⟩
      · rcases selectArm_append_inv h12 with h1 | ⟨_, h2⟩
        · simp only [List.map_map, Function.comp_def] at h1
          have h1' : SourceSemantics.selectArm world [] h (.construct objQName "N" [.field (n : F)])
              (List.map (fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2))
                (ctorArms ⟨P⟩ (firstPerKey [] altEs))) = _ := h1
          rw [hmiss] at h1'; simp at h1'
        · -- `natArm` matches
          simp only [List.map_cons, List.map_nil, pN, SourceSemantics.selectArm,
            qualifyPat, qualifyTy, objTy, qualifyName_obj,
            Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith, constructorName,
            Ty.subst, Ty.toCore, Instance.symbol, List.isEmpty_nil,
            bne_self_eq_false, List.attach_cons, List.attach_nil,
            matchListWith, List.append_nil, bind, Except.bind, pure, Except.pure,
            ↓reduceIte, Bool.or_self] at h2
          obtain ⟨rfl, rfl⟩ := h2
          simp only [qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
            Aiur.Generic.Pattern.map, List.map] at hbr
          cases hbr with
          | matchValue evq hsel2 hbr2 =>
            obtain ⟨hlq, hmqEq⟩ := evalExprN_var_inv evq
            rw [hmqEq] at hsel2 hbr2
            simp only [List.cons_append, List.nil_append, List.find?_cons, beq_self_eq_true,
              Option.some.injEq, Prod.mk.injEq, true_and] at hlq
            subst hlq
            cases n with
            | zero =>
              simp only [Nat.cast_zero, SourceSemantics.selectArm, World.matchPattern,
                matchPatternWith, Aiur.Pattern.bindings, ↓reduceIte,
                bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                Prod.mk.injEq] at hsel2
              obtain ⟨rfl, rfl⟩ := hsel2
              cases hnz : P.known.natZero with
              | none =>
                simp only [hnz] at hbr2
                exact False.elim (evalExprN_trap_elim hbr2)
              | some kz =>
                simp only [hnz, List.nil_append, List.cons_append, Nat.cast_zero] at hbr2
                exact finishKey kz [] (("q", .field (0 : F)) :: locals) _
                  (by simp [Val.asCtor, hnz]) rfl (henv.cons_unused hqVm) (hjenv.cons_unused hqJ) hbr2
            | succ m =>
              have hne : (0 : F) ≠ ((m + 1 : Nat) : F) :=
                Ne.symm (fc.ne_zero_of_pos (Nat.succ_pos m)
                  (lt_trans hn (by unfold natLimit; omega)))
              simp only [Nat.cast_zero, SourceSemantics.selectArm, World.matchPattern,
                matchPatternWith, Aiur.Pattern.bindings, hne, ↓reduceIte,
                bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                Prod.mk.injEq] at hsel2
              obtain ⟨rfl, rfl⟩ := hsel2
              cases hns : P.known.natSucc with
              | none =>
                simp only [hns] at hbr2
                exact False.elim (evalExprN_trap_elim hbr2)
              | some ks =>
                simp only [hns, List.nil_append, List.cons_append] at hbr2
                exact finishKey ks [.lit (.nat m)] (("q", .field (((m + 1 : Nat) : F))) :: locals) _
                  (by simp [Val.asCtor, hns]) rfl (henv.cons_unused hqVm) (hjenv.cons_unused hqJ) hbr2
      · -- `h12none` is impossible because `natArm` matches `N(_)`!
        exfalso
        have hstep : ∀ {l1 l2 : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)},
            SourceSemantics.selectArm world [] h (.construct objQName "N" [.field (n : F)]) l1 = .ok none →
            SourceSemantics.selectArm world [] h (.construct objQName "N" [.field (n : F)]) (l1 ++ l2) =
              SourceSemantics.selectArm world [] h (.construct objQName "N" [.field (n : F)]) l2 := by
          intro l1 l2 hl1
          induction l1 with
          | nil => rfl
          | cons a rest ih =>
            simp only [List.cons_append, SourceSemantics.selectArm, bind, Except.bind] at hl1 ⊢
            cases hm : world.matchPattern [] h a.1 (.construct objQName "N" [.field (n : F)]) with
            | error _ => simp [hm] at hl1
            | ok o =>
              cases o with
              | some _ => simp [hm, pure, Except.pure] at hl1
              | none => simp only [hm] at hl1 ⊢; exact ih hl1
        have hmiss' : SourceSemantics.selectArm world [] h (.construct objQName "N" [.field (n : F)])
            (List.map (fun arm => (Aiur.Generic.Pattern.map Nat.cast arm.1, Aiur.Generic.Expr.map Nat.cast arm.2))
              (List.map (fun arm => (qualifyPat arm.1, qualifyExpr arm.2))
                (ctorArms ⟨P⟩ (firstPerKey [] altEs)))) = .ok none := by
          simpa [qualifyPatF, qualifyExprF, List.map_map, Function.comp_def] using hmiss
        rw [hstep hmiss'] at h12none
        simp [pN, SourceSemantics.selectArm, qualifyPat, qualifyTy, objTy,
          qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith,
          constructorName, Ty.toCore, Instance.symbol, matchListWith,
          bind, Except.bind, pure, Except.pure] at h12none
    | erased =>
      have hmiss : SourceSemantics.selectArm world [] h (.construct objQName "E" [])
          (List.map (fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2))
            (ctorArms ⟨P⟩ (firstPerKey [] altEs))) = .ok none := by
        simpa [qualifyPatF, qualifyExprF] using
          selectArm_ctorArms_miss (P := P) (world := world) (h := h) (cname := "E")
            (ps := []) ctorNameOf_ne_E (firstPerKey [] altEs)
      have hstep : ∀ {l1 l2 : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)},
          SourceSemantics.selectArm world [] h (.construct objQName "E" []) l1 = .ok none →
          SourceSemantics.selectArm world [] h (.construct objQName "E" []) (l1 ++ l2) =
            SourceSemantics.selectArm world [] h (.construct objQName "E" []) l2 := by
        intro l1 l2 hl1
        induction l1 with
        | nil => rfl
        | cons a rest ih =>
          simp only [List.cons_append, SourceSemantics.selectArm, bind, Except.bind] at hl1 ⊢
          cases hm : world.matchPattern [] h a.1 (.construct objQName "E" []) with
          | error _ => simp [hm] at hl1
          | ok o =>
            cases o with
            | some _ => simp [hm, pure, Except.pure] at hl1
            | none => simp only [hm] at hl1 ⊢; exact ih hl1
      have hmiss' : SourceSemantics.selectArm world [] h (.construct objQName "E" [])
          (List.map (fun arm => (Aiur.Generic.Pattern.map Nat.cast arm.1, Aiur.Generic.Expr.map Nat.cast arm.2))
            (List.map (fun arm => (qualifyPat arm.1, qualifyExpr arm.2))
              (ctorArms ⟨P⟩ (firstPerKey [] altEs)))) = .ok none := by
        simpa [qualifyPatF, qualifyExprF, List.map_map, Function.comp_def] using hmiss
      rcases selectArm_append_inv hsel with h12 | ⟨h12none, _⟩
      · rw [hstep hmiss'] at h12
        simp [pN, pC, SourceSemantics.selectArm, qualifyPat, qualifyTy, objTy,
          qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith,
          constructorName, Ty.toCore, Instance.symbol, matchListWith,
          bind, Except.bind, pure, Except.pure] at h12
        obtain ⟨rfl, rfl⟩ := h12
        exact False.elim (evalExprN_trap_elim hbr)
      · exfalso
        rw [hstep hmiss'] at h12none
        simp [pN, pC, SourceSemantics.selectArm, qualifyPat, qualifyTy, objTy,
          qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith,
          constructorName, Ty.toCore, Instance.symbol, matchListWith,
          bind, Except.bind, pure, Except.pure] at h12none
    | @str s bw _ =>
      have hmiss : SourceSemantics.selectArm world [] h (.construct objQName "S" [bw])
          (List.map (fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2))
            (ctorArms ⟨P⟩ (firstPerKey [] altEs))) = .ok none := by
        simpa [qualifyPatF, qualifyExprF] using
          selectArm_ctorArms_miss (P := P) (world := world) (h := h) (cname := "S")
            (ps := [bw]) ctorNameOf_ne_S (firstPerKey [] altEs)
      have hstep : ∀ {l1 l2 : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)},
          SourceSemantics.selectArm world [] h (.construct objQName "S" [bw]) l1 = .ok none →
          SourceSemantics.selectArm world [] h (.construct objQName "S" [bw]) (l1 ++ l2) =
            SourceSemantics.selectArm world [] h (.construct objQName "S" [bw]) l2 := by
        intro l1 l2 hl1
        induction l1 with
        | nil => rfl
        | cons a rest ih =>
          simp only [List.cons_append, SourceSemantics.selectArm, bind, Except.bind] at hl1 ⊢
          cases hm : world.matchPattern [] h a.1 (.construct objQName "S" [bw]) with
          | error _ => simp [hm] at hl1
          | ok o =>
            cases o with
            | some _ => simp [hm, pure, Except.pure] at hl1
            | none => simp only [hm] at hl1 ⊢; exact ih hl1
      have hmiss' : SourceSemantics.selectArm world [] h (.construct objQName "S" [bw])
          (List.map (fun arm => (Aiur.Generic.Pattern.map Nat.cast arm.1, Aiur.Generic.Expr.map Nat.cast arm.2))
            (List.map (fun arm => (qualifyPat arm.1, qualifyExpr arm.2))
              (ctorArms ⟨P⟩ (firstPerKey [] altEs)))) = .ok none := by
        simpa [qualifyPatF, qualifyExprF, List.map_map, Function.comp_def] using hmiss
      rcases selectArm_append_inv hsel with h12 | ⟨h12none, _⟩
      · rw [hstep hmiss'] at h12
        simp [pN, pC, SourceSemantics.selectArm, qualifyPat, qualifyTy, objTy,
          qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith,
          constructorName, Ty.toCore, Instance.symbol, matchListWith,
          bind, Except.bind, pure, Except.pure] at h12
        obtain ⟨rfl, rfl⟩ := h12
        exact False.elim (evalExprN_trap_elim hbr)
      · exfalso
        rw [hstep hmiss'] at h12none
        simp [pN, pC, SourceSemantics.selectArm, qualifyPat, qualifyTy, objTy,
          qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith,
          constructorName, Ty.toCore, Instance.symbol, matchListWith,
          bind, Except.bind, pure, Except.pure] at h12none
    | @ctor ci idx entry fs ps atIdx keyEq arityEq fields =>
      have hpsLen : ps.length = entry.arity := by rw [← fields.length_eq, arityEq]
      have hctorSel := selectArm_ctorArms_ctor (P := P) (world := world) (h := h)
        hnd hkeys atIdx hpsLen (firstPerKey [] altEs)
      rw [firstPerKey_nil_find?, keyEq] at hctorSel
      have hctorSel' : SourceSemantics.selectArm world [] h
          (.construct objQName (ctorNameOf idx ci.key) ps)
          (List.map (fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2))
            (ctorArms ⟨P⟩ (firstPerKey [] altEs))) =
          .ok ((altEs.find? (·.1 == ci.key)).map fun p => ([], qualifyExprF F p.2)) := by
        simpa [keyEq, qualifyPatF, qualifyExprF] using hctorSel
      have hneN : (ctorNameOf idx ci.key != "N") = true := bne_iff_ne.mpr (ctorNameOf_ne_N idx ci.key)
      have hneE : (ctorNameOf idx ci.key != "E") = true := bne_iff_ne.mpr (ctorNameOf_ne_E idx ci.key)
      have hneS : (ctorNameOf idx ci.key != "S") = true := bne_iff_ne.mpr (ctorNameOf_ne_S idx ci.key)
      rcases selectArm_append_inv hsel with h12 | ⟨h12none, h3⟩
      · rcases selectArm_append_inv h12 with h1 | ⟨_, h2⟩
        · simp only [List.map_map, Function.comp_def] at h1
          have h1' : SourceSemantics.selectArm world [] h
              (.construct objQName (ctorNameOf idx ci.key) ps)
              (List.map (fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2))
                (ctorArms ⟨P⟩ (firstPerKey [] altEs))) = _ := h1
          rw [hctorSel'] at h1'
          cases hf : altEs.find? (·.1 == ci.key) with
          | none => simp [hf] at h1'
          | some p =>
            simp only [hf, Option.map_some, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h1'
            obtain ⟨rfl, rfl⟩ := h1'
            simp only [List.nil_append] at hbr
            have hbe : p.2 = (((firstPerKey [] altEs).find? (·.1 == ci.key)).map (·.2)).getD
                (dE.getD (trapE "no alternative")) := by
              rw [firstPerKey_nil_find?, hf]; rfl
            exact finishKey ci.key fs locals p.2 (by simp [Val.asCtor]) hbe henv hjenv hbr
        · exfalso
          simp [pN, pC, SourceSemantics.selectArm, qualifyPat, qualifyTy, objTy,
            qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith,
            constructorName, Ty.toCore, Instance.symbol, hneN, hneE, hneS,
            bind, Except.bind, pure, Except.pure] at h2
      · -- Default arm matched: first ensure `altEs.find? (·.1 == ci.key) = none`!
        have hfindNone : altEs.find? (·.1 == ci.key) = none := by
          cases hf : altEs.find? (·.1 == ci.key) with
          | none => rfl
          | some p =>
            exfalso
            have hstep : ∀ {l1 l2 : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
                {res : Environment F Nat × Aiur.Generic.Expr F},
                SourceSemantics.selectArm world [] h (.construct objQName (ctorNameOf idx ci.key) ps) l1 =
                  .ok (some res) →
                SourceSemantics.selectArm world [] h (.construct objQName (ctorNameOf idx ci.key) ps) (l1 ++ l2) =
                  .ok (some res) := by
              intro l1 l2 res hl1
              induction l1 with
              | nil => simp [SourceSemantics.selectArm] at hl1
              | cons a rest ih =>
                simp only [List.cons_append, SourceSemantics.selectArm, bind, Except.bind] at hl1 ⊢
                cases hm : world.matchPattern [] h a.1 (.construct objQName (ctorNameOf idx ci.key) ps) with
                | error _ => simp [hm] at hl1
                | ok o =>
                  cases o with
                  | some bs => simp only [hm, pure, Except.pure] at hl1 ⊢; exact hl1
                  | none => simp only [hm] at hl1 ⊢; exact ih hl1
            rw [hf] at hctorSel'
            have hctorSel'' : SourceSemantics.selectArm world [] h
                (.construct objQName (ctorNameOf idx ci.key) ps)
                (List.map (fun arm => (Aiur.Generic.Pattern.map Nat.cast arm.1, Aiur.Generic.Expr.map Nat.cast arm.2))
                  (List.map (fun arm => (qualifyPat arm.1, qualifyExpr arm.2))
                    (ctorArms ⟨P⟩ (firstPerKey [] altEs)))) =
                .ok (some ([], qualifyExprF F p.2)) := by
              simpa [qualifyPatF, qualifyExprF, List.map_map, Function.comp_def] using hctorSel'
            rw [hstep hctorSel''] at h12none
            simp at h12none
        cases d with
        | none =>
          obtain ⟨rfl, _⟩ := optE_none_inv hd
          simp [SourceSemantics.selectArm] at h3
        | some dc =>
          obtain ⟨de, _, rfl⟩ := optE_some_inv hd
          simp only [List.map_cons, List.map_nil, SourceSemantics.selectArm,
            qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith,
            bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
            Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          simp only [List.nil_append] at hbr
          have hbe : de = (((firstPerKey [] altEs).find? (·.1 == ci.key)).map (·.2)).getD
              ((some de).getD (trapE "no alternative")) := by
            rw [firstPerKey_nil_find?, hfindNone]; rfl
          exact finishKey ci.key fs locals de (by simp [Val.asCtor]) hbe henv hjenv hbr

end CaseSound

/-! ## Section 7: Main Backward Simulation Theorem (`eval_codeE_sound_N`) -/

section MainProof

variable {F : Type} [Field F] [DecidableEq F]

mutual

private theorem isPlainExpr_codeE_only (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    ∀ (c : Code) (st st' : LowerState) (e : Lower.Expr),
      codeE cx fid vm jenv c st = .ok (e, st') → isPlainExpr e = true
  | .bind _ _ k, _, _, _, h => by
    obtain ⟨re, ke, hr, hk, rfl⟩ := codeE_bind_inv h
    simp [letE, isPlainExpr, isPlainExpr_rhsE hr, isPlainExpr_codeE_only cx fid _ jenv k _ _ _ hk]
  | .jp _ _ _ _ k, _, _, _, h => by
    obtain ⟨_, _, _, hk⟩ := codeE_jp_inv h
    exact isPlainExpr_codeE_only cx fid _ _ k _ _ _ hk
  | .jmp _ _, _, _, _, h => by
    obtain ⟨ji, argEs, _, _, ha, rfl, rfl⟩ := codeE_jmp_inv h
    simp only [callE, isPlainExpr, isPlainList_iff]
    intro x hx
    rcases List.mem_append.mp hx with h1 | h2
    · rw [List.mem_map] at h1; obtain ⟨nm, _, rfl⟩ := h1; simp [vE, isPlainExpr]
    · exact isPlainExpr_argsE ha x h2
  | .case _ alts d, _, _, _, h => by
    obtain ⟨nx, altEs, st1, dE, _, halts, hd, rfl⟩ := codeE_case_inv h
    exact isPlainExpr_caseE cx nx (isPlainExpr_altsE_only cx fid vm jenv alts _ st1 altEs halts)
      (isPlainExpr_optE_only cx fid vm jenv d st1 _ dE hd)
  | .ret _, _, _, _, h => by
    obtain ⟨ha, rfl⟩ := codeE_ret_inv h
    exact isPlainExpr_argE ha
  | .tcall _ _, _, _, _, h => by
    obtain ⟨_, argEs, _, _, _, ha, rfl, rfl⟩ := codeE_tcall_inv h
    simp only [callE, isPlainExpr, isPlainList_iff]
    exact isPlainExpr_argsE ha
  | .trap, _, _, _, h => by
    obtain ⟨rfl, rfl⟩ := codeE_trap_inv h
    exact isPlainExpr_trapE _

private theorem isPlainExpr_altsE_only (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    ∀ (alts : List Alt) (st st' : LowerState) (res : List (CtorKey × Lower.Expr)),
      altsE cx fid vm jenv alts st = .ok (res, st') → ∀ p ∈ res, isPlainExpr p.2 = true
  | [], _, _, _, h => by
    obtain ⟨rfl, rfl⟩ := altsE_nil_inv h; simp
  | .mk _ b :: rest, _, _, _, h => by
    obtain ⟨be, st1, re, hb, hr, rfl⟩ := altsE_cons_inv h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | htl
    · exact isPlainExpr_codeE_only cx fid vm jenv b _ st1 be hb
    · exact isPlainExpr_altsE_only cx fid vm jenv rest st1 _ re hr p htl

private theorem isPlainExpr_optE_only (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    ∀ (o : Option Code) (st st' : LowerState) (res : Option Lower.Expr),
      optE cx fid vm jenv o st = .ok (res, st') → ∀ e, res = some e → isPlainExpr e = true
  | none, _, _, _, h => by
    obtain ⟨rfl, rfl⟩ := optE_none_inv h; intro _ he; cases he
  | some c, _, _, _, h => by
    obtain ⟨ce, hc, rfl⟩ := optE_some_inv h
    intro e he; cases he
    exact isPlainExpr_codeE_only cx fid vm jenv c _ _ ce hc

end

/-- Inductive hypothesis for all lowered Fir functions at call depths strictly below `d`. -/
def FunSoundN (P : Fir.Program) (world : World F) (d : Nat) : Prop :=
  ∀ d' < d, ∀ f fd, P.fun? f = some fd → f < P.size →
    ∀ vs ws h r h',
      List.Forall₂ (VR P objQName bytesQName h) vs ws →
      EvalFnN world d' (qualified (funName f)) ws h r h' →
      ∃ k v, Fir.run P k f vs = .ok v ∧ VR P objQName bytesQName h' v r

/-- Inductive invariant for lowering arbitrary `Fir.Code` at call depth `d`. -/
def CodeSoundAt (P : Fir.Program) (world : World F) (d : Nat) : Prop :=
  ∀ fid vm jenv c st st' e ρ J locals h r h',
    codeE ⟨P⟩ fid vm jenv c st = .ok (e, st') →
    AllLocalLt st.nextLocal (vm.map Prod.snd) →
    AllLocalLt st.nextLocal (jenv.flatMap (·.capNames)) →
    (∀ g ∈ st'.lifted, WorldHasFn world (qualified g.name) (g.params.map Prod.fst)
      (qualifyExprF F g.body)) →
    EnvRel P h vm ρ locals →
    JEnvRel P world d h jenv J locals →
    EvalExprN world d [] locals (qualifyExprF F e) h r h' →
    ∃ k v, Fir.eval P k ρ J c = .ok v ∧ VR P objQName bytesQName h' v r

/-- Derive `FunSoundN P world d` from `∀ d' < d, CodeSoundAt P world d'`. -/
theorem funSoundN_of_codeSound {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    {world : World F} (lw : LoweredWorld P prog world) {d : Nat}
    (hCode : ∀ d' < d, CodeSoundAt P world d') :
    FunSoundN P world d := by
  intro d' hd' f fd hfun hsz vs ws h r h' hrel evFn
  obtain ⟨body, st, hcode, hwfMain, hwfLifted⟩ := lw.hasFun hfun hsz
  have hplain : isPlainExpr (qualifyExprF F body) = true := by
    rw [isPlainExpr_qualifyExprF]
    exact (isPlainExpr_codeE ⟨P⟩ f _ [] fd.body _ _ _ hcode (by simp)).1
  obtain ⟨hwslen, evBody⟩ := evalFnN_plain_inv hwfMain hplain evFn
  have hvslen : vs.length = fd.params.length := by
    have := hrel.length_eq
    simp only [List.length_map, List.length_range] at hwslen
    omega
  set pns := (List.range fd.params.length).map localName
  have hpnsLen : (fd.params.map Prod.fst).length = pns.length := by simp [pns]
  have hpnsNodup : pns.Nodup :=
    List.Nodup.map (fun _ _ heq => localName_inj heq) List.nodup_range
  have henv0 : EnvRel P h [] .leaf [] :=
    { rel := fun _ _ h => (by cases h), bound := fun _ h => (by cases h) }
  have henv : EnvRel P h (bindVm [] (fd.params.map Prod.fst) pns)
      (bindAll .leaf (fd.params.map Prod.fst) vs) (pns.zip ws) := by
    simpa using EnvRel.bindAll_append hpnsLen hpnsNodup (by simp) henv0 hrel (by simp [hvslen])
  have hlocVm : AllLocalLt fd.params.length ((bindVm [] (fd.params.map Prod.fst) pns).map Prod.snd) := by
    apply AllLocalLt_bindVm (n := 0) (m := fd.params.length) (by intro s hs; cases hs) _ (Nat.zero_le _)
    intro p hp
    simp only [pns, List.mem_map, List.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    exact ⟨k, hk, rfl⟩
  have hlocJ : AllLocalLt fd.params.length (([] : List JEntryL).flatMap (·.capNames)) := by
    intro s hs; simp at hs
  obtain ⟨k, v, heval, hvr⟩ := hCode d' hd' f _ [] fd.body _ st body _ [] (pns.zip ws) h r h'
    hcode hlocVm hlocJ hwfLifted henv .nil evBody
  refine ⟨k + 1, v, ?_, hvr⟩
  rw [Fir.run_eq, Fir.evalCall_of P (k + 1) hfun]
  simp [Fir.callFun, hvslen, Fir.later, heval]

/-- Master induction: `CodeSoundAt P world d` holds for every call depth `d : Nat`. -/
theorem eval_codeE_sound_N {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    {world : World F} (fc : FieldCompatible F) (lw : LoweredWorld P prog world) :
    ∀ d : Nat, CodeSoundAt P world d := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ihD =>
    have hFunSound : FunSoundN P world d := funSoundN_of_codeSound lw ihD
    -- Inner strong induction on `c.size`
    have bySize : ∀ (n : Nat) (c : Code), c.size = n →
        ∀ fid vm jenv st st' e ρ J locals h r h',
          codeE ⟨P⟩ fid vm jenv c st = .ok (e, st') →
          AllLocalLt st.nextLocal (vm.map Prod.snd) →
          AllLocalLt st.nextLocal (jenv.flatMap (·.capNames)) →
          (∀ g ∈ st'.lifted, WorldHasFn world (qualified g.name) (g.params.map Prod.fst)
            (qualifyExprF F g.body)) →
          EnvRel P h vm ρ locals →
          JEnvRel P world d h jenv J locals →
          EvalExprN world d [] locals (qualifyExprF F e) h r h' →
          ∃ k v, Fir.eval P k ρ J c = .ok v ∧ VR P objQName bytesQName h' v r := by
      intro n
      induction n using Nat.strongRecOn with
      | _ n ihS =>
        intro c hcsz fid vm jenv st st' e ρ J locals h r h' hcode hlocVm hlocJ hLifted henv hjenv ev
        cases c with
        | bind x rhs k =>
          obtain ⟨re, ke, hrhs, hk, rfl⟩ := codeE_bind_inv hcode
          simp only [letE, qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
            Aiur.Generic.Pattern.map] at ev
          obtain ⟨w1, hm, evRhs, evK⟩ := evalExprN_let_bind_inv ev
          have hfreshVm : localName st.nextLocal ∉ vm.map Prod.snd :=
            hlocVm.not_mem (Nat.le_refl _)
          have hfreshJ : localName st.nextLocal ∉ jenv.flatMap (·.capNames) :=
            hlocJ.not_mem (Nat.le_refl _)
          have hlocVm' : AllLocalLt (st.nextLocal + 1) (((x, localName st.nextLocal) :: vm).map Prod.snd) := by
            intro s hs
            simp only [List.map_cons, List.mem_cons] at hs
            rcases hs with rfl | htl
            · exact ⟨st.nextLocal, by omega, rfl⟩
            · exact hlocVm.mono (by omega) s htl
          have hlocJ' : AllLocalLt (st.nextLocal + 1) (jenv.flatMap (·.capNames)) :=
            hlocJ.mono (by omega)
          have hkSize : k.size < n := by rw [← hcsz]; simp [Code.size]
          cases rhs with
          | call f as =>
            unfold rhsE at hrhs
            cases hfun : P.fun? f with
            | none => simp [hfun, throw, throwThe, MonadExceptOf.throw] at hrhs
            | some fd =>
              simp only [hfun] at hrhs
              by_cases hsz : f < P.size
              · simp only [hsz, ↓reduceIte] at hrhs
                by_cases hlen : as.length = fd.params.length
                · simp only [hlen, beq_self_eq_true, ↓reduceIte, bind, Except.bind, pure,
                    Except.pure] at hrhs
                  cases hargs : argsE vm as with
                  | error _ => simp [hargs] at hrhs
                  | ok argEs =>
                    simp only [hargs, Except.ok.injEq] at hrhs
                    subst hrhs
                    simp only [callE, qualifyExpr, qualifyName_funName, Option.map_some,
                      Aiur.Generic.Expr.map, List.map_map] at evRhs
                    obtain ⟨d', ws, hm1, hd', hargsEv, hcal⟩ := evalExprN_call_inv evRhs
                    have hargsEv' : EvalArgsN world d [] locals (argEs.map (qualifyExprF F)) h ws hm1 := hargsEv
                    obtain ⟨vs, hvs, hrel, ext1⟩ := eval_argsE hargs henv hargsEv'
                    obtain ⟨k1, v1, hrun1, hvr1⟩ := hFunSound d' hd' f fd hfun hsz vs ws hm1 w1 hm hrel hcal
                    have ext2 : Heap.Extends h hm := ext1.trans hcal.heap_extends
                    have henv' := (henv.extend ext2).cons_fresh (x := x) hfreshVm hvr1
                    have hjenv' := (hjenv.extend ext2).cons_unused (wx := w1) hfreshJ
                    obtain ⟨k2, v2, heval2, hvr2⟩ := ihS k.size hkSize k rfl fid _ jenv _ st' ke
                      (ρ.insert x v1) J ((localName st.nextLocal, w1) :: locals) hm r h'
                      hk hlocVm' hlocJ' hLifted henv' hjenv' evK
                    refine ⟨max k1 k2, v2, ?_, hvr2⟩
                    rw [Fir.eval_bindCall, hvs]
                    simp only [Result.ofOption, Result.bind_ok]
                    rw [Fir.evalCall_mono P hrun1 (Nat.le_max_left k1 k2)]
                    simp only [Result.bind_ok]
                    exact Fir.eval_mono P heval2 (Nat.le_max_right k1 k2)
                · have hbeq : (as.length == fd.params.length) = false := beq_false_of_ne hlen
                  simp [hbeq, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hrhs
              · simp [hsz, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hrhs
          | arg a =>
            obtain ⟨v1, hv1, hvr1, ext1⟩ := eval_argE hrhs henv evRhs
            have henv' := (henv.extend ext1).cons_fresh (x := x) hfreshVm hvr1
            have hjenv' := (hjenv.extend ext1).cons_unused (wx := w1) hfreshJ
            obtain ⟨k2, v2, heval2, hvr2⟩ := ihS k.size hkSize k rfl fid _ jenv _ st' ke
              (ρ.insert x v1) J ((localName st.nextLocal, w1) :: locals) hm r h'
              hk hlocVm' hlocJ' hLifted henv' hjenv' evK
            refine ⟨k2, v2, ?_, hvr2⟩
            rw [Fir.eval_bindRhs P k2 ρ J x (.arg a) k (by intro _ _ h; cases h)]
            simp [Fir.evalRhs, hv1, Result.ofOption, heval2]
          | ctor ci as =>
            unfold rhsE at hrhs
            cases hc : (Cx.mk P).ctorEntry? ci.key with
            | none => simp [hc] at hrhs
            | some p =>
              rcases p with ⟨idx, entry⟩
              simp only [hc] at hrhs
              by_cases har : (as.length == entry.arity && ci.arity == entry.arity) = true
              · simp only [har, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hrhs
                cases hargs : argsE vm as with
                | error _ => simp [hargs] at hrhs
                | ok argEs =>
                  simp only [hargs, Except.ok.injEq] at hrhs
                  subst hrhs
                  simp only [Bool.and_eq_true, beq_iff_eq] at har
                  obtain ⟨hasLen, hciAr⟩ := har
                  obtain ⟨hget, hkey⟩ := ctorEntry?_sound hc
                  simp only [mk, qualifyExpr, qualifyName_obj, Option.map_some,
                    Aiur.Generic.Expr.map, List.map_map] at evRhs
                  obtain ⟨ps, hargsEv, rfl⟩ := evalExprN_construct_inv evRhs
                  have hargsEv' : EvalArgsN world d [] locals
                      (argEs.map fun e => .store (qualifyExprF F e)) h ps hm := by
                    simpa [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map_map,
                      Function.comp_def] using hargsEv
                  obtain ⟨vs, hvs, hvrs, ext1⟩ := eval_argsE_store hargs henv hargsEv'
                  have hvslen : vs.length = entry.arity := by
                    have hlenEq : ∀ {as : List Arg} {vs : List Fir.Val},
                        evalArgs ρ as = some vs → vs.length = as.length := by
                      intro as
                      induction as with
                      | nil => intro vs h; simp [evalArgs] at h; subst h; rfl
                      | cons a tl ih =>
                        intro vs h; simp only [evalArgs] at h
                        cases ha : a.eval ρ with
                        | none => simp [ha] at h
                        | some v =>
                          cases htl : evalArgs ρ tl with
                          | none => simp [ha, htl] at h
                          | some vst =>
                            simp only [ha, htl, Option.some.injEq] at h; subst h
                            exact congrArg Nat.succ (ih htl)
                    rw [hlenEq hvs, hasLen]
                  have hvr1 : VR P objQName bytesQName hm (.ctor ci vs)
                      (.construct objQName (ctorNameOf idx entry.key) ps) := by
                    rw [hkey]
                    exact .ctor hget hkey hvslen hvrs
                  have henv' := (henv.extend ext1).cons_fresh (x := x) hfreshVm hvr1
                  have hjenv' := (hjenv.extend ext1).cons_unused (wx := .construct objQName (ctorNameOf idx entry.key) ps) hfreshJ
                  obtain ⟨k2, v2, heval2, hvr2⟩ := ihS k.size hkSize k rfl fid _ jenv _ st' ke
                    (ρ.insert x (.ctor ci vs)) J _ hm r h'
                    hk hlocVm' hlocJ' hLifted henv' hjenv' evK
                  refine ⟨k2, v2, ?_, hvr2⟩
                  rw [Fir.eval_bindRhs P k2 ρ J x (.ctor ci as) k (by intro _ _ h; cases h)]
                  simp [Fir.evalRhs, hvs, hvslen, hciAr, heval2]
              · simp [har, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hrhs
          | proj y ck idx =>
            unfold rhsE at hrhs
            cases hlook : vm.lookup y with
            | none => simp [hlook, throw, throwThe, MonadExceptOf.throw] at hrhs
            | some ny =>
              simp only [hlook, pure, Except.pure, Except.ok.injEq] at hrhs
              subst hrhs
              obtain ⟨vy, wy, hρy, hlocy, hvrY⟩ := henv.rel y ny hlook
              obtain ⟨v1, hproj, hvr1, ext1⟩ :=
                eval_projE fc lw.ctors_names_nodup hlocy hvrY evRhs
              have henv' := (henv.extend ext1).cons_fresh (x := x) hfreshVm hvr1
              have hjenv' := (hjenv.extend ext1).cons_unused (wx := w1) hfreshJ
              obtain ⟨k2, v2, heval2, hvr2⟩ := ihS k.size hkSize k rfl fid _ jenv _ st' ke
                (ρ.insert x v1) J ((localName st.nextLocal, w1) :: locals) hm r h'
                hk hlocVm' hlocJ' hLifted henv' hjenv' evK
              refine ⟨k2, v2, ?_, hvr2⟩
              rw [Fir.eval_bindRhs P k2 ρ J x (.proj y ck idx) k (by intro _ _ h; cases h)]
              simp [Fir.evalRhs, hρy, hproj, heval2]
          | prim op as =>
            unfold rhsE at hrhs
            cases hpf : primFun op with
            | error _ => simp [hpf, bind, Except.bind] at hrhs
            | ok pfn =>
              rcases pfn with ⟨fnName, arity⟩
              simp only [hpf, bind, Except.bind] at hrhs
              by_cases hlen : as.length = arity
              · simp only [hlen, beq_self_eq_true, ↓reduceIte] at hrhs
                by_cases hbadBool : (isBoolPrim op && (Cx.mk P).boolNames.isNone) = true
                · simp [hbadBool, throw, throwThe, MonadExceptOf.throw] at hrhs
                · simp only [hbadBool, Bool.false_eq_true, ↓reduceIte] at hrhs
                  cases hargs : argsE vm as with
                  | error _ => simp [hargs] at hrhs
                  | ok argEs =>
                    simp only [hargs, pure, Except.pure, Except.ok.injEq] at hrhs
                    subst hrhs
                    have hbool : isBoolPrim op = true → (Cx.mk P).boolNames.isSome = true := by
                      intro hbp
                      cases hb : (Cx.mk P).boolNames with
                      | none => simp [hbp, hb] at hbadBool
                      | some _ => rfl
                    obtain ⟨v1, hprimOk, hvr1, ext1⟩ :=
                      eval_prim fc lw hpf hlen hbool hargs henv evRhs
                    have henv' := (henv.extend ext1).cons_fresh (x := x) hfreshVm hvr1
                    have hjenv' := (hjenv.extend ext1).cons_unused (wx := w1) hfreshJ
                    obtain ⟨k2, v2, heval2, hvr2⟩ := ihS k.size hkSize k rfl fid _ jenv _ st' ke
                      (ρ.insert x v1) J ((localName st.nextLocal, w1) :: locals) hm r h'
                      hk hlocVm' hlocJ' hLifted henv' hjenv' evK
                    refine ⟨k2, v2, ?_, hvr2⟩
                    rw [Fir.eval_bindRhs P k2 ρ J x (.prim op as) k (by intro _ _ h; cases h)]
                    simp [hprimOk, heval2]
              · have hbeq : (as.length == arity) = false := beq_false_of_ne hlen
                simp [hbeq, throw, throwThe, MonadExceptOf.throw] at hrhs
        | jp j ps isRec body k =>
          obtain ⟨bodyExpr, st2, hbody, hk⟩ := codeE_jp_inv hcode
          set capNames := liveNames vm jenv
          set jpName := jpFunName fid st.nextJp
          set pns := (List.range ps.length).map (fun i => localName (st.nextLocal + i))
          set ji : JEntryL := ⟨j, jpName, capNames, ps.length⟩
          set je : Fir.JEntry := { id := j, charged := false, env := ρ, params := ps, body := body, isRec := isRec }
          set liftedFn : Lower.Fn := ⟨jpName, [], (capNames ++ pns).map (·, objTy), objTy, bodyExpr, false⟩
          obtain ⟨capVals, hcapEval⟩ := exists_evalCapArgs_liveNames henv hjenv
          have hcapNodup : capNames.Nodup := liveNames_nodup vm jenv
          have hcapLen : capVals.length = capNames.length := hcapEval.length_eq
          have hpnsLen : pns.length = ps.length := by simp [pns]
          have hpnsNodup : pns.Nodup :=
            List.Nodup.map (fun _ _ heq => by have := localName_inj heq; omega) List.nodup_range
          have hlocCap : AllLocalLt st.nextLocal capNames := AllLocalLt_liveNames hlocVm hlocJ
          have hpnsDisj : ∀ p ∈ pns, p ∉ (capNames.zip capVals).map Prod.fst := by
            intro p hp hmem
            simp only [pns, List.mem_map, List.mem_range] at hp
            obtain ⟨idx, _, rfl⟩ := hp
            rw [List.map_fst_zip (by omega)] at hmem
            exact hlocCap.not_mem (by omega) hmem
          have hwfLiftedBody : ∀ g ∈ st2.lifted,
              WorldHasFn world (qualified g.name) (g.params.map Prod.fst) (qualifyExprF F g.body) := by
            obtain ⟨_, tK, hlifK⟩ := codeE_state_mono ⟨P⟩ fid vm (ji :: jenv) k _ st' e hk
            intro g hg
            apply hLifted g
            rw [hlifK]
            exact List.mem_append_left _ (List.mem_append_left _ hg)
          have hwfJp : WorldHasFn world (qualified jpName) (capNames ++ pns) (qualifyExprF F bodyExpr) := by
            obtain ⟨_, tK, hlifK⟩ := codeE_state_mono ⟨P⟩ fid vm (ji :: jenv) k _ st' e hk
            have hmem : liftedFn ∈ st'.lifted := by
              rw [hlifK]
              exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
            have hwf := hLifted liftedFn hmem
            simpa [liftedFn, List.map_map, Function.comp_def] using hwf
          have hplainBody : isPlainExpr (qualifyExprF F bodyExpr) = true := by
            rw [isPlainExpr_qualifyExprF]
            exact isPlainExpr_codeE_only ⟨P⟩ fid _ _ body _ _ _ hbody
          -- Let's prove `jiSound` for all `m < d` by inner `Nat.strongRecOn` on `m`!
          have hlocVmBody : AllLocalLt (st.nextLocal + ps.length) ((bindVm vm ps pns).map Prod.snd) := by
            apply AllLocalLt_bindVm hlocVm _ (by omega)
            intro p hp
            simp only [pns, List.mem_map, List.mem_range] at hp
            obtain ⟨idx, hidx, rfl⟩ := hp
            exact ⟨st.nextLocal + idx, by omega, rfl⟩
          have hlocJBody : AllLocalLt (st.nextLocal + ps.length)
              ((if isRec then ji :: jenv else jenv).flatMap (·.capNames)) := by
            cases isRec
            · exact hlocJ.mono (by omega)
            · intro s hs
              rcases List.mem_append.mp hs with h1 | h2
              · exact hlocCap.mono (by omega) s h1
              · exact hlocJ.mono (by omega) s h2
          have jiSound : ∀ m < d, ∀ h1, Heap.Extends h h1 →
              ∀ vs ws r1 h2,
                List.Forall₂ (VR P objQName bytesQName h1) vs ws →
                vs.length = ps.length →
                EvalFnN world m (qualified jpName) (capVals ++ ws) h1 r1 h2 →
                ∃ k' v', Fir.eval P k' (Fir.bindAll ρ ps vs) (je.after J) body = .ok v' ∧
                  VR P objQName bytesQName h2 v' r1 := by
            intro m
            induction m using Nat.strongRecOn with
            | _ m ihM =>
              intro hmLt h1 ext1 vs ws r1 h2 hrel hvslen evJp
              obtain ⟨_, evBody⟩ := evalFnN_plain_inv hwfJp hplainBody evJp
              have hzipEq : (capNames ++ pns).zip (capVals ++ ws) =
                  capNames.zip capVals ++ pns.zip ws :=
                List.zip_append (by omega)
              rw [hzipEq] at evBody
              have henvCap : EnvRel P h1 vm ρ (capNames.zip capVals) :=
                (henv.extend ext1).of_capZip hcapNodup hcapEval (fun s hs => mem_liveNames_of_vm hs)
              have henvBody : EnvRel P h1 (bindVm vm ps pns) (Fir.bindAll ρ ps vs)
                  (capNames.zip capVals ++ pns.zip ws) :=
                EnvRel.bindAll_append hpnsLen.symm hpnsNodup hpnsDisj henvCap hrel hvslen
              have hjenvBase : JEnvRel P world m h1 jenv J (capNames.zip capVals ++ pns.zip ws) :=
                (((hjenv.extend ext1).mono_depth (Nat.le_of_lt hmLt)).of_capZip hcapNodup hcapEval
                  (fun s hs => mem_liveNames_of_jenv hs)).append_right
              have hjenvBody : JEnvRel P world m h1 (if isRec then ji :: jenv else jenv)
                  (je.after J) (capNames.zip capVals ++ pns.zip ws) := by
                cases hrec : isRec with
                | false =>
                  simpa [je, Fir.JEntry.after, hrec] using hjenvBase
                | true =>
                  simp only [je, Fir.JEntry.after, hrec, ↓reduceIte]
                  refine .cons rfl (qualifyName_jpFunName fid st.nextJp) rfl
                    (EvalCapArgs.of_zip_nodup hcapNodup hcapLen) ?_ hjenvBase
                  intro m' hm' h1' ext1' vs' ws' r1' h2' hrel' hvslen' evRec
                  have hres := ihM m' hm' (Nat.lt_trans hm' hmLt) h1' (ext1.trans ext1')
                    vs' ws' r1' h2' hrel' hvslen' evRec
                  simpa [je, Fir.JEntry.after, hrec] using hres
              exact ihD m hmLt fid _ _ body _ st2 bodyExpr _ _ _ h1 r1 h2
                hbody hlocVmBody hlocJBody hwfLiftedBody henvBody hjenvBody evBody
          -- Now step into continuation `k` with `ji :: jenv` and `je :: J`!
          obtain ⟨hleBody, _, _⟩ := codeE_state_mono ⟨P⟩ fid _ _ body _ st2 bodyExpr hbody
          have hst2Ge : st.nextLocal ≤ st2.nextLocal := Nat.le_trans (Nat.le_add_right _ _) hleBody
          have hlocVmK : AllLocalLt st2.nextLocal (vm.map Prod.snd) := hlocVm.mono hst2Ge
          have hlocJK : AllLocalLt st2.nextLocal ((ji :: jenv).flatMap (·.capNames)) := by
            simp only [List.flatMap_cons]
            intro s hs
            rcases List.mem_append.mp hs with h1 | h2
            · exact hlocCap.mono hst2Ge s h1
            · exact hlocJ.mono hst2Ge s h2
          have hjenvK : JEnvRel P world d h (ji :: jenv) (je :: J) locals :=
            .cons rfl (qualifyName_jpFunName fid st.nextJp) rfl hcapEval jiSound hjenv
          have hkSize : k.size < n := by rw [← hcsz]; simp [Code.size]
          obtain ⟨kOut, vOut, hevalK, hvrOut⟩ := ihS k.size hkSize k rfl fid vm (ji :: jenv) _ st' e
            ρ (je :: J) locals h r h' hk hlocVmK hlocJK hLifted henv hjenvK ev
          refine ⟨kOut, vOut, ?_, hvrOut⟩
          rw [Fir.eval_jp]
          exact hevalK
        | jmp j as =>
          obtain ⟨ji, argEs, hfind, harity, hargs, rfl, rfl⟩ := codeE_jmp_inv hcode
          obtain ⟨je, Jrest, capVals, hlookJ, hqual, hparamEq, hcapEval, hjsound⟩ :=
            hjenv.find_lookup hfind
          simp only [callE, qualifyExprF, qualifyExpr, hqual, Option.map_some,
            Aiur.Generic.Expr.map, List.map_append, List.map_map] at ev
          obtain ⟨d', allWs, hm, hd', hargsEv, hcal⟩ := evalExprN_call_inv ev
          obtain ⟨capWs, argWs, hm1, rfl, hcapEv, hargEv⟩ := evalArgsN_append_inv hargsEv
          have hcapEv' : EvalArgsN world d [] locals (ji.capNames.map fun nm => qualifyExprF F (vE nm))
              h capWs hm1 := by
            simpa [qualifyExprF, List.map_map, Function.comp_def] using hcapEv
          obtain ⟨rfl, hm1Eq⟩ := eval_capNames hcapEval hcapEv'
          rw [hm1Eq] at hargEv
          have hargEv' : EvalArgsN world d [] locals (argEs.map (qualifyExprF F)) h argWs hm := hargEv
          obtain ⟨vs, hvs, hrel, ext1⟩ := eval_argsE hargs henv hargEv'
          have hvslen : vs.length = je.params.length := by
            have h1 : ∀ {as : List Arg} {vs : List Fir.Val},
                evalArgs ρ as = some vs → vs.length = as.length := by
              intro as
              induction as with
              | nil => intro vs h; simp [evalArgs] at h; subst h; rfl
              | cons a tl ih =>
                intro vs h; simp only [evalArgs] at h
                cases ha : a.eval ρ with
                | none => simp [ha] at h
                | some v =>
                  cases htl : evalArgs ρ tl with
                  | none => simp [ha, htl] at h
                  | some vst =>
                    simp only [ha, htl, Option.some.injEq] at h; subst h
                    exact congrArg Nat.succ (ih htl)
            rw [h1 hvs, harity, hparamEq]
          obtain ⟨k1, v1, heval1, hvr1⟩ :=
            hjsound d' hd' hm ext1 vs argWs r h' hrel hvslen hcal
          refine ⟨k1 + 1, v1, ?_, hvr1⟩
          rw [Fir.eval_jmp, hlookJ, hvs]
          simp only [Result.ofOption, Result.bind_ok, Fir.jumpTo, hvslen, ↓reduceIte]
          cases je.charged
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact Fir.eval_mono P heval1 (Nat.le_succ k1)
          · simp [Fir.later, heval1]
        | case x alts dOpt =>
          obtain ⟨nx, altEs, st1, dE, hlook, halts, hdOpt, rfl⟩ := codeE_case_inv hcode
          obtain ⟨b, stA, stB, be, locals', hbSize, hbCode, hleA, hlifB, henv', hjenv', evBe, hcaseEq⟩ :=
            eval_caseE fc lw.ctors_names_nodup lw.ctors_keys_nodup
              hlook halts hdOpt hlocVm hlocJ henv hjenv ev
          have hbLt : b.size < n := by rw [← hcsz]; exact hbSize
          obtain ⟨k1, v1, hevalB, hvr1⟩ := ihS b.size hbLt b rfl fid vm jenv stA stB be
            ρ J locals' h r h' hbCode (hlocVm.mono hleA) (hlocJ.mono hleA)
            (fun g hg => hLifted g (hlifB g hg)) henv' hjenv' evBe
          exact ⟨k1, v1, by rw [hcaseEq k1]; exact hevalB, hvr1⟩
        | ret a =>
          obtain ⟨ha, rfl⟩ := codeE_ret_inv hcode
          obtain ⟨v1, hv1, hvr1, _⟩ := eval_argE ha henv ev
          exact ⟨0, v1, by simp [Fir.eval_ret, hv1, Result.ofOption], hvr1⟩
        | tcall f as =>
          obtain ⟨fd, argEs, hfun, hsz, hlen, hargs, rfl, rfl⟩ := codeE_tcall_inv hcode
          simp only [callE, qualifyExprF, qualifyExpr, qualifyName_funName, Option.map_some,
            Aiur.Generic.Expr.map, List.map_map] at ev
          obtain ⟨d', ws, hm, hd', hargsEv, hcal⟩ := evalExprN_call_inv ev
          have hargsEv' : EvalArgsN world d [] locals (argEs.map (qualifyExprF F)) h ws hm := hargsEv
          obtain ⟨vs, hvs, hrel, _⟩ := eval_argsE hargs henv hargsEv'
          obtain ⟨k1, v1, hrun1, hvr1⟩ := hFunSound d' hd' f fd hfun hsz vs ws hm r h' hrel hcal
          refine ⟨k1, v1, ?_, hvr1⟩
          rw [Fir.eval_tcall, hvs]
          exact hrun1
        | trap =>
          obtain ⟨rfl, rfl⟩ := codeE_trap_inv hcode
          exact False.elim (evalExprN_trap_elim ev)
    intro fid vm jenv c st st' e ρ J locals h r h'
    exact bySize c.size c rfl fid vm jenv st st' e ρ J locals h r h'

end MainProof

/-! ## Section 8: Headline Backward Simulation & End-to-End Circuit Soundness -/

section Headline

variable {F : Type} [Field F] [DecidableEq F]

/-- **Full Backward Simulation Theorem (Internal Fir Functions):**
Every `Aiur.Generic.SourceSemantics.EvalFn` derivation of a lowered Fir function
`Prog::f<f>` on `VR`-related arguments yields a terminating `Fir.run P k f vs = .ok v`
whose result `v` is `VR`-related to `r` on the resulting heap `h'`. -/
theorem backward_sound {P : Fir.Program} {prog : Aiur.Generic.Program Nat} {world : World F}
    (fc : FieldCompatible F) (lw : LoweredWorld P prog world)
    {f : FunId} {fd : Fir.Fun} (hfun : P.fun? f = some fd) (hsz : f < P.size)
    {vs : List Fir.Val} {ws : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hrel : List.Forall₂ (VR P objQName bytesQName h) vs ws)
    (ev : EvalFn world (qualified (funName f)) ws h r h') :
    ∃ k v, Fir.run P k f vs = .ok v ∧ VR P objQName bytesQName h' v r := by
  obtain ⟨d, evN⟩ := EvalFnN.ofEvalFn ev
  exact funSoundN_of_codeSound lw (fun d' _ => eval_codeE_sound_N fc lw d')
    d (Nat.lt_succ_self d) f fd hfun hsz vs ws h r h' hrel evN

/-- Helper: inverting `entryE`'s argument wrappers `seqE (wordE (vE nm)) (natE (vE nm))`. -/
private theorem eval_entry_args {world : World F} (u64 : U64Contracts world) :
    ∀ {nms : List String} {args ws : List (SourceValue F)} {extra : Environment F Nat}
      {h h' : Heap F},
      nms.Nodup → args.length = nms.length →
      EvalArgs world [] (nms.zip args ++ extra)
        (nms.map fun nm => qualifyExprF F (seqE (wordE (vE nm)) (natE (vE nm)))) h ws h' →
      ∃ ns : List Nat,
        (∀ n ∈ ns, n < natLimit) ∧
        args = ns.map (fun n => .field (n : F)) ∧
        ws = ns.map (fun n => .construct objQName "N" [.field (n : F)]) ∧
        h' = h
  | [], [], _, _, _, _, _, _, ev => by
    cases ev; exact ⟨[], by simp, rfl, rfl, rfl⟩
  | [], _ :: _, _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, hlen, _ => by simp at hlen
  | nm :: nms, a :: as, ws, extra, h, h', hnd, hlen, ev => by
    rw [List.nodup_cons] at hnd
    have hlen' : as.length = nms.length := by simpa using hlen
    cases ev with
    | cons hhd htl =>
      simp only [seqE, wordE, natE, mk, callE, vE, qualifyExprF, qualifyExpr, qualifyPat,
        qualifyName_u64_from_field, qualifyName_obj, Option.map_some,
        Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at hhd
      obtain ⟨_, _, evWord, evNat⟩ := evalExpr_let_wildcard_inv hhd
      obtain ⟨va, _, eva, hcal⟩ := evalExpr_call1_inv evWord
      obtain ⟨hla, rfl⟩ := evalExpr_var_inv eva
      simp only [List.zip_cons_cons, List.cons_append, List.find?_cons, beq_self_eq_true,
        Option.some.injEq, Prod.mk.injEq, true_and] at hla
      subst hla
      obtain ⟨n, hn, rfl, _, rfl⟩ := u64.from_field _ _ _ _ hcal
      obtain ⟨vn, evn, rfl⟩ := evalExpr_construct1_inv evNat
      obtain ⟨hln, rfl⟩ := evalExpr_var_inv evn
      simp only [List.zip_cons_cons, List.cons_append, List.find?_cons, beq_self_eq_true,
        Option.some.injEq, Prod.mk.injEq, true_and] at hln
      subst hln
      -- Shift `(nm, .field n)` from head of `locals` out of the tail lookup (since `nm ∉ nms`)
      -- Easier: prove a tiny lemma that `EvalArgs` on `seqE (wordE (vE _)) (natE (vE _))` only depends on lookups in `nms`!
      have hlookupRest : ∀ {xs : List String} {vals : List (SourceValue F)} {h1 h2 : Heap F},
          nm ∉ xs →
          EvalArgs world [] ((nm, .field (n : F)) :: (nms.zip as ++ extra))
            (xs.map fun x => qualifyExprF F (seqE (wordE (vE x)) (natE (vE x)))) h1 vals h2 →
          EvalArgs world [] (nms.zip as ++ extra)
            (xs.map fun x => qualifyExprF F (seqE (wordE (vE x)) (natE (vE x)))) h1 vals h2 := by
        intro xs
        induction xs with
        | nil => intro vals _ _ _ e; cases e; exact .nil
        | cons x xt ih =>
          intro vals h1 h2 hni e
          simp only [List.mem_cons, not_or] at hni
          cases e with
          | cons e1 e2 =>
            rename_i val1 mid1 vals2
            have hneB : (nm == x) = false := beq_false_of_ne hni.1
            simp only [seqE, wordE, natE, mk, callE, vE, qualifyExprF, qualifyExpr, qualifyPat,
              qualifyName_u64_from_field, qualifyName_obj, Option.map_some,
              Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at e1
            obtain ⟨vw, hm1, eW, eN⟩ := evalExpr_let_wildcard_inv e1
            obtain ⟨vx1, hm0, evx1, cal1⟩ := evalExpr_call1_inv eW
            obtain ⟨hl1, hm0Eq⟩ := evalExpr_var_inv evx1
            rw [hm0Eq] at cal1
            simp only [List.find?_cons, hneB] at hl1
            obtain ⟨vx2, evx2, rfl⟩ := evalExpr_construct1_inv eN
            obtain ⟨hl2, hm1Eq⟩ := evalExpr_var_inv evx2
            rw [← hm1Eq] at cal1
            simp only [List.find?_cons, hneB] at hl2
            have e1' : EvalExpr world [] (nms.zip as ++ extra)
                (qualifyExprF F (seqE (wordE (vE x)) (natE (vE x)))) h1
                (.construct objQName "N" [vx2]) mid1 := by
              simp only [seqE, wordE, natE, mk, callE, vE, qualifyExprF, qualifyExpr, qualifyPat,
                qualifyName_u64_from_field, qualifyName_obj, Option.map_some,
                Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map]
              exact .letValue (bindings := []) (.call (.cons (.var hl1) .nil) cal1)
                (by simp [World.matchPattern, matchPatternWith])
                (.construct (.cons (.var hl2) .nil))
            exact .cons e1' (ih hni.2 e2)
      have htl' := hlookupRest hnd.1 (by simpa [List.zip_cons_cons, List.cons_append] using htl)
      obtain ⟨ns, hns, rfl, rfl, rfl⟩ := eval_entry_args u64 hnd.2 hlen' htl'
      refine ⟨n :: ns, ?_, rfl, rfl, rfl⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hn
      · exact hns x hmem

/-- **Entrypoint Backward Simulation Theorem (`Prog::main<i>`):**
Every `EvalFn` derivation of an exported entry wrapper `Prog::main<i>` on raw `Field`
arguments proves that all arguments are `< 2^56` field casts and yields a terminating
`Fir.run P k f (ns.map (.lit ∘ .nat)) = .ok v` with `VR P objQName bytesQName h' v r`. -/
theorem entry_backward_sound {P : Fir.Program} {prog : Aiur.Generic.Program Nat} {world : World F}
    (fc : FieldCompatible F) (lw : LoweredWorld P prog world)
    {i : Nat} {f : FunId} (hexp : P.exports[i]? = some f)
    {args : List (SourceValue F)} {h' : Heap F} {r : SourceValue F}
    (ev : EvalFn world (qualified (entryName i)) args [] r h') :
    ∃ (ns : List Nat) (k : Nat) (v : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      Fir.run P k f (ns.map fun n => .lit (.nat n)) = .ok v ∧
      VR P objQName bytesQName h' v r := by
  obtain ⟨fd, hfun, hsz, hwfEnt⟩ := lw.hasEntry hexp
  have hplain : isPlainExpr (qualifyExprF F (callE (funName f) ((List.range fd.params.length).map
      fun j => seqE (wordE (vE (entryParamName j))) (natE (vE (entryParamName j)))))) = true := by
    rw [isPlainExpr_qualifyExprF]
    simp only [callE, isPlainExpr, isPlainList_iff, List.mem_map]
    rintro _ ⟨j, _, rfl⟩
    simp [seqE, wordE, callE, natE, mk, vE, isPlainExpr, isPlainList]
  obtain ⟨hlen, evBody⟩ := evalFn_plain_inv hwfEnt hplain ev
  simp only [callE, qualifyExprF, qualifyExpr, qualifyName_funName, Option.map_some,
    Aiur.Generic.Expr.map, List.map_map] at evBody
  cases evBody with
  | call hargsEv hcal =>
    rename_i ws hm
    simp only [instanceName, Option.getD_some, List.map_nil, Instance.symbol, List.isEmpty_nil,
      ↓reduceIte] at hcal
    set nms := (List.range fd.params.length).map entryParamName
    have hnd : nms.Nodup :=
      List.Nodup.map (fun _ _ heq => entryParamName_inj heq) List.nodup_range
    have hargsEv' : EvalArgs world [] (nms.zip args ++ [])
        (nms.map fun nm => qualifyExprF F (seqE (wordE (vE nm)) (natE (vE nm)))) [] ws hm := by
      simpa [nms, qualifyExprF, List.map_map, Function.comp_def] using hargsEv
    obtain ⟨ns, hns, rfl, rfl, rfl⟩ := eval_entry_args lw.u64 hnd hlen hargsEv'
    have hrel : List.Forall₂ (VR P objQName bytesQName [])
        (ns.map fun n => .lit (.nat n))
        (ns.map fun (n : Nat) => .construct objQName "N" [.field (n : F)]) := by
      clear hcal hargsEv' hargsEv hlen hnd hplain hwfEnt hexp hsz hfun ev
      induction ns with
      | nil => exact .nil
      | cons n nt ih =>
        exact .cons (.nat (hns n List.mem_cons_self))
          (ih fun x hx => hns x (List.mem_cons_of_mem _ hx))
    obtain ⟨k, v, hrun, hvr⟩ := backward_sound fc lw hfun hsz hrel hcal
    exact ⟨ns, k, v, hns, rfl, hrun, hvr⟩

/-- **End-to-End Certified Compilation Soundness (General `FieldCompatible F`):**
Composes `entry_backward_sound` with `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound`.
Any batch of at most `2^39` rows accepted by `plan.checkMemo` over the grouped, activated
certified depth pass of the physical Aiur circuits for an exported Fir entrypoint
`Prog::main<i>` yields a terminating `Fir.run P k f` evaluation on the decoded `< 2^56`
natural-number inputs, whose Fir result `v` corresponds via `VR` to the Aiur source value
and via `Represents` to the decoded circuit output `result`. -/
theorem lowered_circuit_sound {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    {moduleProg : Aiur.Modules.Program F}
    {id : String → Except String Nat}
    (fc : FieldCompatible F)
    (prepared : Aiur.Modules.Prepared moduleProg)
    (lw : LoweredWorld P prog prepared.environment.source.world)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical cfg)
    (bits : cfg.bits ≤ 24)
    (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String}
    {entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {i : Nat} {f : FunId}
    (hname : entry.resolved.name = qualified (entryName i))
    (hexp : P.exports[i]? = some f)
    {rom : Aiur.WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Aiur.Value F}
    {wires : List (Aiur.WireValue F)} {output : Aiur.WireValue F}
    (signed : Aiur.Circuit.Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message F}
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Aiur.Circuit.Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Aiur.Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    (checked : plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ (value : SourceValue F) (heap : Heap F) (ns : List Nat) (k : Nat) (v : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      Fir.run P k f (ns.map fun n => .lit (.nat n)) = .ok v ∧
      VR P objQName bytesQName heap v value ∧
      Aiur.Represents ((Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result := by
  obtain ⟨value, heap, hevalMod, hrep⟩ :=
    prepared.depth_grouped_activated_heap_sound compiled physical certified bits plan activated
      selected valid signed rooted outside bound characteristic checked arguments decoded
  obtain ⟨entry', hsel', hevalFn⟩ := hevalMod
  rw [selected, Option.some.injEq] at hsel'
  subst hsel'
  rw [hname] at hevalFn
  obtain ⟨ns, k, v, hns, hargs, hrun, hvr⟩ := entry_backward_sound fc lw hexp hevalFn
  exact ⟨value, heap, ns, k, v, hns, hargs, hrun, hvr, hrep⟩

/-- **End-to-End Certified Compilation Soundness over Goldilocks (`U32.Goldilocks.F`):**
Discharges BOTH `FieldCompatible` (via `goldilocks_fieldCompatible`) and the depth-pass
characteristic bound (via `Depth.goldilocks_characteristic`). -/
theorem lowered_circuit_sound_goldilocks {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    {moduleProg : Aiur.Modules.Program Aiur.Library.U32.Goldilocks.F}
    {id : String → Except String Nat}
    (prepared : Aiur.Modules.Prepared moduleProg)
    (lw : LoweredWorld P prog prepared.environment.source.world)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical cfg)
    (bits : cfg.bits ≤ 24)
    (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String}
    {entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {i : Nat} {f : FunId}
    (hname : entry.resolved.name = qualified (entryName i))
    (hexp : P.exports[i]? = some f)
    {rom : Aiur.WidthROM Aiur.Library.U32.Goldilocks.F} (valid : rom.Valid)
    {args : List (SourceValue Aiur.Library.U32.Goldilocks.F)}
    {result : Aiur.Value Aiur.Library.U32.Goldilocks.F}
    {wires : List (Aiur.WireValue Aiur.Library.U32.Goldilocks.F)}
    {output : Aiur.WireValue Aiur.Library.U32.Goldilocks.F}
    (signed : Aiur.Circuit.Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.U32.Goldilocks.F}
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Aiur.Circuit.Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.U32.Goldilocks.F)}
    (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ (value : SourceValue Aiur.Library.U32.Goldilocks.F) (heap : Heap Aiur.Library.U32.Goldilocks.F)
      (ns : List Nat) (k : Nat) (v : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : Aiur.Library.U32.Goldilocks.F)) ∧
      Fir.run P k f (ns.map fun n => .lit (.nat n)) = .ok v ∧
      VR P objQName bytesQName heap v value ∧
      Aiur.Represents ((Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result :=
  lowered_circuit_sound goldilocks_fieldCompatible prepared lw compiled physical certified bits plan
    activated selected hname hexp valid signed rooted outside bound
    Aiur.Optimized.Depth.goldilocks_characteristic checked arguments decoded

end Headline

end Ix.Cert.IxccAiur.Backward
