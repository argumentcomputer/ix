module
public import Ix.Aiur.Semantics.ConcreteEval

/-!
Per-arm equational unfolders for `Concrete.Eval.interp`.

Each lemma rewrites `interp … (.<ctor> …) …` into its explicit case body.
These are the mechanical step that every `Lower` preservation arm needs when
it unwinds `interp` on the corresponding term constructor.

All proofs are `simp [interp]`. Relies on `@[expose] def interp`.
-/

@[expose] public section

namespace Aiur
namespace Concrete.Eval

/-- `.unit` arm. -/
theorem interp_unit
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (st : EvalState) :
    interp decls fuel env (.unit t e) st = .ok (.unit, st) := by
  simp only [interp]
  try rfl

/-- `.var` arm. -/
theorem interp_var
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (l : Local) (st : EvalState) :
    interp decls fuel env (.var t e l) st =
      match env.find? (·.1 == l) with
      | some (_, v) => .ok (v, st)
      | none        => .error (.unboundVar l) := by
  simp only [interp]
  try rfl

/-- `.field` arm. -/
theorem interp_field
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (g : G) (st : EvalState) :
    interp decls fuel env (.field t e g) st = .ok (.field g, st) := by
  simp only [interp]
  try rfl

/-- `.ref` arm. -/
theorem interp_ref
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (g : Global) (st : EvalState) :
    interp decls fuel env (.ref t e g) st =
      match decls.getByKey g with
      | some (.function _)          => .ok (.fn g, st)
      | some (.constructor _ ctor)  =>
          if ctor.argTypes.isEmpty then .ok (.ctor g #[], st)
          else .error (.notCallable g)
      | some (.dataType _)          => .error (.notCallable g)
      | none                        => .error (.unboundGlobal g) := by
  simp only [interp]
  try rfl

/-- `.ret` arm. -/
theorem interp_ret
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (r : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.ret t e r) st = interp decls fuel env r st := by
  simp only [interp]
  try rfl

/-- `.tuple` arm. -/
theorem interp_tuple
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (ts : Array Concrete.Term) (st : EvalState) :
    interp decls fuel env (.tuple t e ts) st =
      match evalList decls fuel env ts.toList st with
      | .error e => .error e
      | .ok (vs, st') => .ok (.tuple vs, st') := by
  simp only [interp]
  try rfl

/-- `.array` arm. -/
theorem interp_array
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (ts : Array Concrete.Term) (st : EvalState) :
    interp decls fuel env (.array t e ts) st =
      match evalList decls fuel env ts.toList st with
      | .error e => .error e
      | .ok (vs, st') => .ok (.array vs, st') := by
  simp only [interp]
  try rfl

/-- `.add` arm. Unfolds via `evalBinField`. -/
theorem interp_add
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a b : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.add t e a b) st =
      evalBinField decls fuel env a b st (fun x y => .field (x + y)) := by
  simp only [interp]
  try rfl

/-- `.sub` arm. -/
theorem interp_sub
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a b : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.sub t e a b) st =
      evalBinField decls fuel env a b st (fun x y => .field (x - y)) := by
  simp only [interp]
  try rfl

/-- `.mul` arm. -/
theorem interp_mul
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a b : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.mul t e a b) st =
      evalBinField decls fuel env a b st (fun x y => .field (x * y)) := by
  simp only [interp]
  try rfl

/-- `.eqZero` arm. -/
theorem interp_eqZero
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.eqZero t e a) st =
      match interp decls fuel env a st with
      | .error err => .error err
      | .ok (.field g, st') => .ok (.field (if g.val == 0 then 1 else 0), st')
      | .ok _ => .error (.typeMismatch "eqZero") := by
  simp only [interp]
  try rfl

/-- `.u8ShiftLeft` arm. -/
theorem interp_u8ShiftLeft
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.u8ShiftLeft t e a) st =
      match interp decls fuel env a st with
      | .error err => .error err
      | .ok (.field g, st') => .ok (.field (G.ofUInt8 (g.val.toUInt8 <<< 1)), st')
      | .ok _ => .error (.typeMismatch "u8ShiftLeft") := by
  simp only [interp]
  try rfl

/-- `.u8ShiftRight` arm. -/
theorem interp_u8ShiftRight
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.u8ShiftRight t e a) st =
      match interp decls fuel env a st with
      | .error err => .error err
      | .ok (.field g, st') => .ok (.field (G.ofUInt8 (g.val.toUInt8 >>> 1)), st')
      | .ok _ => .error (.typeMismatch "u8ShiftRight") := by
  simp only [interp]
  try rfl

/-- `.u8BitDecomposition` arm. -/
theorem interp_u8BitDecomposition
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.u8BitDecomposition t e a) st =
      match interp decls fuel env a st with
      | .error err => .error err
      | .ok (.field g, st') =>
        let byte := g.val.toUInt8
        .ok (.array (Array.ofFn fun (i : Fin 8) =>
          .field (G.ofUInt8 ((byte >>> i.val.toUInt8) &&& 1))), st')
      | .ok _ => .error (.typeMismatch "u8BitDecomposition") := by
  simp only [interp]
  try rfl

/-- `.u8Xor` arm. -/
theorem interp_u8Xor
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a b : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.u8Xor t e a b) st =
      evalBinField decls fuel env a b st (fun x y =>
        .field (G.ofUInt8 (x.val.toUInt8 ^^^ y.val.toUInt8))) := by
  simp only [interp]
  try rfl

/-- `.u8Add` arm. -/
theorem interp_u8Add
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a b : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.u8Add t e a b) st =
      evalBinField decls fuel env a b st (fun x y =>
        let sum := x.val.toUInt8.toNat + y.val.toUInt8.toNat
        .tuple #[.field (G.ofUInt8 sum.toUInt8),
                 .field (if sum ≥ 256 then 1 else 0)]) := by
  simp only [interp]
  try rfl

/-- `.u8Sub` arm. -/
theorem interp_u8Sub
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a b : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.u8Sub t e a b) st =
      evalBinField decls fuel env a b st (fun x y =>
        let i := x.val.toUInt8; let j := y.val.toUInt8
        .tuple #[.field (G.ofUInt8 (i - j)), .field (if j > i then 1 else 0)]) := by
  simp only [interp]
  try rfl

/-- `.u8And` arm. -/
theorem interp_u8And
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a b : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.u8And t e a b) st =
      evalBinField decls fuel env a b st (fun x y =>
        .field (G.ofUInt8 (x.val.toUInt8 &&& y.val.toUInt8))) := by
  simp only [interp]
  try rfl

/-- `.u8Or` arm. -/
theorem interp_u8Or
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a b : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.u8Or t e a b) st =
      evalBinField decls fuel env a b st (fun x y =>
        .field (G.ofUInt8 (x.val.toUInt8 ||| y.val.toUInt8))) := by
  simp only [interp]
  try rfl

/-- `.u8LessThan` arm. -/
theorem interp_u8LessThan
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a b : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.u8LessThan t e a b) st =
      evalBinField decls fuel env a b st (fun x y =>
        .field (if x.val.toUInt8 < y.val.toUInt8 then 1 else 0)) := by
  simp only [interp]
  try rfl

/-- `.u32LessThan` arm. -/
theorem interp_u32LessThan
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a b : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.u32LessThan t e a b) st =
      evalBinField decls fuel env a b st (fun x y =>
        .field (if x.val.toUInt32 < y.val.toUInt32 then 1 else 0)) := by
  simp only [interp]
  try rfl

/-- `.store` arm. -/
theorem interp_store
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.store t e a) st =
      match interp decls fuel env a st with
      | .error err => .error err
      | .ok (v, st') =>
        let gs := flattenForStore v
        let w := gs.size
        let (st'', idx) := storeInsert st' gs
        .ok (.pointer w idx, st'') := by
  simp only [interp]
  try rfl

/-- `.load` arm. -/
theorem interp_load
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (a : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.load t e a) st =
      match interp decls fuel env a st with
      | .error err => .error err
      | .ok (.pointer w i, st') =>
        match storeLookup st' w i with
        | some gs =>
          let srcTyp : Aiur.Typ := concreteTypToSource a.typ
          let eltTyp : Aiur.Typ := match srcTyp with
            | Aiur.Typ.pointer inner => inner
            | t' => t'
          let (v, _) := unflattenValue (default : Source.Decls) gs 0 eltTyp
          .ok (v, st')
        | none => .error (.invalidPointer i)
      | .ok _ => .error (.typeMismatch "load") := by
  simp only [interp]
  try rfl



/-- `.array` arm output: existence of evalList result. -/
theorem interp_array_ok
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (ts : Array Concrete.Term)
    (st : EvalState) (interp_v : Value) (st' : EvalState)
    (h : interp decls fuel env (.array t e ts) st = .ok (interp_v, st')) :
    ∃ vs, evalList decls fuel env ts.toList st = .ok (vs, st') ∧
          interp_v = .array vs := by
  rw [interp_array] at h
  cases hres : evalList decls fuel env ts.toList st with
  | error e => rw [hres] at h; cases h
  | ok p =>
    obtain ⟨vs, st''⟩ := p
    rw [hres] at h
    simp only at h
    have hpair : (.array vs, st'') = (interp_v, st') := Except.ok.inj h
    have hv : interp_v = .array vs := (congrArg Prod.fst hpair).symm
    have hst : st'' = st' := congrArg Prod.snd hpair
    subst hst
    exact ⟨vs, rfl, hv⟩

/-- `.proj` arm. -/
theorem interp_proj
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (sub : Concrete.Term) (n : Nat) (st : EvalState) :
    interp decls fuel env (.proj t e sub n) st =
      match interp decls fuel env sub st with
      | .error err => .error err
      | .ok (.tuple vs, st') =>
        if h : n < vs.size then .ok (vs[n], st')
        else .error (.indexOoB n)
      | .ok _ => .error (.typeMismatch "proj") := by
  simp only [interp]
  try rfl

/-- `.get` arm. -/
theorem interp_get
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (sub : Concrete.Term) (n : Nat) (st : EvalState) :
    interp decls fuel env (.get t e sub n) st =
      match interp decls fuel env sub st with
      | .error err => .error err
      | .ok (.array vs, st') =>
        if h : n < vs.size then .ok (vs[n], st')
        else .error (.indexOoB n)
      | .ok _ => .error (.typeMismatch "get") := by
  simp only [interp]
  try rfl

/-- `.slice` arm. -/
theorem interp_slice
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (sub : Concrete.Term) (i j : Nat) (st : EvalState) :
    interp decls fuel env (.slice t e sub i j) st =
      match interp decls fuel env sub st with
      | .error err => .error err
      | .ok (.array vs, st') => .ok (.array (vs.extract i j), st')
      | .ok _ => .error (.typeMismatch "slice") := by
  simp only [interp]
  try rfl

/-- `.set` arm. -/
theorem interp_set
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (sub : Concrete.Term) (n : Nat)
    (vT : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.set t e sub n vT) st =
      match interp decls fuel env vT st with
      | .error err => .error err
      | .ok (val, st1) =>
        match interp decls fuel env sub st1 with
        | .error err => .error err
        | .ok (.array vs, st2) =>
          if n < vs.size then .ok (.array (vs.set! n val), st2)
          else .error (.indexOoB n)
        | .ok _ => .error (.typeMismatch "set") := by
  simp only [interp]
  try rfl

/-- `.letLoad` arm. -/
theorem interp_letLoad
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (dst : Local) (dstTyp : Concrete.Typ)
    (src : Local) (b : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.letLoad t e dst dstTyp src b) st =
      match env.find? (·.1 == src) with
      | none => .error (.unboundVar src)
      | some (_, .pointer w i) =>
        match storeLookup st w i with
        | some gs =>
          let srcTyp := concreteTypToSource dstTyp
          let (stored, _) := unflattenValue (default : Source.Decls) gs 0 srcTyp
          interp decls fuel ((dst, stored) :: env) b st
        | none => .error (.invalidPointer i)
      | some _ => .error (.typeMismatch "letLoad src is not a pointer") := by
  simp only [interp]
  try rfl

/-- `.ioSetInfo` arm. -/
theorem interp_ioSetInfo
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (key idx len r : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.ioSetInfo t e key idx len r) st =
      match interp decls fuel env key st with
      | .error err => .error err
      | .ok (vk, stk) =>
      match interp decls fuel env idx stk with
      | .error err => .error err
      | .ok (vi, sti) =>
      match interp decls fuel env len sti with
      | .error err => .error err
      | .ok (vl, stl) =>
        match vk, vi, vl with
        | .array vs, .field iG, .field lG =>
          match expectFieldArray vs with
          | none       => .error (.typeMismatch "ioSetInfo key")
          | some keyGs =>
            if stl.ioBuffer.map.contains keyGs then .error .ioKeyAlreadySet
            else
              let info : IOKeyInfo := ⟨iG.val.toNat, lG.val.toNat⟩
              let st' := { stl with ioBuffer :=
                { stl.ioBuffer with map := stl.ioBuffer.map.insert keyGs info } }
              interp decls fuel env r st'
        | _, _, _ => .error (.typeMismatch "ioSetInfo") := by
  simp only [interp]
  try rfl

/-- `.ioRead` arm. -/
theorem interp_ioRead
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (idx : Concrete.Term) (len : Nat) (st : EvalState) :
    interp decls fuel env (.ioRead t e idx len) st =
      match interp decls fuel env idx st with
      | .error err => .error err
      | .ok (.field g, st') =>
        let start := g.val.toNat
        if start + len > st'.ioBuffer.data.size then .error .ioReadOoB
        else .ok (.array (st'.ioBuffer.data.extract start (start + len) |>.map .field), st')
      | .ok _ => .error (.typeMismatch "ioRead") := by
  simp only [interp]
  try rfl

/-- `.ioWrite` arm. -/
theorem interp_ioWrite
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (data r : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.ioWrite t e data r) st =
      match interp decls fuel env data st with
      | .error err => .error err
      | .ok (.array vs, st') =>
        match expectFieldArray vs with
        | none       => .error (.typeMismatch "ioWrite")
        | some dataGs =>
          let st'' := { st' with ioBuffer :=
            { st'.ioBuffer with data := st'.ioBuffer.data ++ dataGs } }
          interp decls fuel env r st''
      | .ok _ => .error (.typeMismatch "ioWrite") := by
  simp only [interp]
  try rfl

/-- `.ioGetInfo` arm. -/
theorem interp_ioGetInfo
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (k : Concrete.Term) (st : EvalState) :
    interp decls fuel env (.ioGetInfo t e k) st =
      match interp decls fuel env k st with
      | .error err => .error err
      | .ok (.array vs, st') =>
        match expectFieldArray vs with
        | none       => .error (.typeMismatch "ioGetInfo key")
        | some keyGs =>
          match st'.ioBuffer.map[keyGs]? with
          | some info =>
            .ok (.tuple #[.field (.ofNat info.idx), .field (.ofNat info.len)], st')
          | none => .error .ioKeyNotFound
      | .ok _ => .error (.typeMismatch "ioGetInfo") := by
  simp only [interp]
  try rfl

/-- `.app` arm. -/
theorem interp_app
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (g : Global)
    (args : List Concrete.Term) (u : Bool) (st : EvalState) :
    interp decls fuel env (.app t e g args u) st =
      match evalList decls fuel env args st with
      | .error err => .error err
      | .ok (vs, st') =>
        match tryLocalLookup g env with
        | some v => applyLocal decls fuel v vs.toList st'
        | none   => applyGlobal decls fuel g vs.toList st' := by
  simp only [interp]
  try rfl

/-- `evalBinField` unfolds to its match cascade. -/
theorem evalBinField_unfold
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t1 t2 : Concrete.Term) (st : EvalState) (k : G → G → Value) :
    evalBinField decls fuel env t1 t2 st k =
      match interp decls fuel env t1 st with
      | .error err => .error err
      | .ok (v1, st1) =>
        match interp decls fuel env t2 st1 with
        | .error err => .error err
        | .ok (v2, st2) =>
          match v1, v2 with
          | .field a, .field b => .ok (k a b, st2)
          | _, _ => .error (.typeMismatch "bin field") := by
  simp only [evalBinField]
  try rfl



end Concrete.Eval
end Aiur

end -- @[expose] public section
