/-
  Kernel Equal: Definitional equality checking.

  Handles proof irrelevance, unit types, eta expansion.
  In NbE, all non-partial definitions are eagerly unfolded by `eval`, so there
  is no lazy delta reduction here — different const-headed values are genuinely
  unequal (they are stuck constructors, recursors, axioms, or partial defs).
  Adapted from Yatima.Typechecker.Equal, parameterized over MetaMode.
-/
import Ix.Kernel.Eval

namespace Ix.Kernel

/-- Pointer equality on thunks: if two thunks share the same pointer, they must
    produce the same value. Returns false conservatively when pointers differ. -/
@[inline] private def susValuePtrEq (a b : SusValue m) : Bool :=
  unsafe ptrAddrUnsafe a.body == ptrAddrUnsafe b.body

/-- Compare two arrays of levels for equality. -/
private def equalUnivArrays (us us' : Array (Level m)) : Bool :=
  us.size == us'.size && Id.run do
    let mut i := 0
    while i < us.size do
      if !Level.equalLevel us[i]! us'[i]! then return false
      i := i + 1
    return true

/-- Construct a canonicalized cache key for two SusValues using their pointer addresses.
    The smaller pointer always comes first, making the key symmetric: key(a,b) == key(b,a). -/
@[inline] private def susValueCacheKey (a b : SusValue m) : USize × USize :=
  let pa := unsafe ptrAddrUnsafe a.body
  let pb := unsafe ptrAddrUnsafe b.body
  if pa ≤ pb then (pa, pb) else (pb, pa)

mutual
  /-- Try eta expansion for structure-like types. -/
  partial def tryEtaStruct (lvl : Nat) (term term' : SusValue m) : TypecheckM m Bool := do
    match term'.get with
    | .app (.const k _ _) args _ =>
      match (← get).typedConsts.get? k with
      | some (.constructor type ..) =>
        match ← applyType (← eval type) args with
        | .app (.const tk _ _) targs _ =>
          match (← get).typedConsts.get? tk with
          | some (.inductive _ struct ..) =>
            -- Skip struct eta for Prop types (proof irrelevance handles them)
            let isProp := match term'.info with | .proof => true | _ => false
            if struct && !isProp then
              targs.zipIdx.foldlM (init := true) fun acc (arg, i) => do
                match arg.get with
                | .app (.proj _ idx val _) _ _ =>
                  pure (acc && i == idx && (← equal lvl term val.sus))
                | _ => pure false
            else pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false

  /-- Check if two suspended values are definitionally equal at the given level.
      Assumes both have the same type and live in the same context. -/
  partial def equal (lvl : Nat) (term term' : SusValue m) : TypecheckM m Bool :=
    match term.info, term'.info with
    | .unit, .unit => pure true
    | .proof, .proof => pure true
    | _, _ => withFuelCheck do
      if (← read).trace then dbg_trace s!"equal: {term.get.ctorName} vs {term'.get.ctorName}"
      -- Fast path: pointer equality on thunks
      if susValuePtrEq term term' then return true
      -- Check equality cache
      let key := susValueCacheKey term term'
      if let some true := (← get).equalCache.get? key then return true
      let tv := term.get
      let tv' := term'.get
      let result ← match tv, tv' with
      | .lit lit, .lit lit' => pure (lit == lit')
      | .sort u, .sort u' => pure (Level.equalLevel u u')
      | .pi dom img env _ _, .pi dom' img' env' _ _ => do
        let res ← equal lvl dom dom'
        let ctx ← read
        let stt ← get
        let img  := suspend img  { ctx with env := env.extendWith  (mkSusVar dom.info  lvl) } stt
        let img' := suspend img' { ctx with env := env'.extendWith (mkSusVar dom'.info lvl) } stt
        let res' ← equal (lvl + 1) img img'
        if !res' then
          dbg_trace s!"equal Pi images FAILED at lvl={lvl}: lhs={img.get.dump} rhs={img'.get.dump}"
        pure (res && res')
      | .lam dom bod env _ _, .lam dom' bod' env' _ _ => do
        let res ← equal lvl dom dom'
        let ctx ← read
        let stt ← get
        let bod  := suspend bod  { ctx with env := env.extendWith  (mkSusVar dom.info  lvl) } stt
        let bod' := suspend bod' { ctx with env := env'.extendWith (mkSusVar dom'.info lvl) } stt
        let res' ← equal (lvl + 1) bod bod'
        pure (res && res')
      | .lam dom bod env _ _, .app neu' args' infos' => do
        let var := mkSusVar dom.info lvl
        let ctx ← read
        let stt ← get
        let bod := suspend bod { ctx with env := env.extendWith var } stt
        let app := Value.app neu' (var :: args') (term'.info :: infos')
        equal (lvl + 1) bod (.mk bod.info app)
      | .app neu args infos, .lam dom bod env _ _ => do
        let var := mkSusVar dom.info lvl
        let ctx ← read
        let stt ← get
        let bod := suspend bod { ctx with env := env.extendWith var } stt
        let app := Value.app neu (var :: args) (term.info :: infos)
        equal (lvl + 1) (.mk bod.info app) bod
      | .app (.fvar idx _) args _, .app (.fvar idx' _) args' _ =>
        if idx == idx' then equalThunks lvl args args'
        else pure false
      | .app (.const k us _) args _, .app (.const k' us' _) args' _ =>
        if k == k' && equalUnivArrays us us' then
          equalThunks lvl args args'
        else
          -- In NbE, eval eagerly unfolds all non-partial definitions.
          -- Different const heads here are stuck terms that can't reduce further.
          pure false
      -- Nat literal vs constructor expansion
      | .lit (.natVal _), .app (.const _ _ _) _ _ => do
        let prims := (← read).prims
        let expanded ← toCtorIfLit prims tv
        equal lvl (.mk term.info (.mk fun _ => expanded)) term'
      | .app (.const _ _ _) _ _, .lit (.natVal _) => do
        let prims := (← read).prims
        let expanded ← toCtorIfLit prims tv'
        equal lvl term (.mk term'.info (.mk fun _ => expanded))
      -- String literal vs constructor expansion
      | .lit (.strVal _), .app (.const _ _ _) _ _ => do
        let prims := (← read).prims
        let expanded ← strLitToCtorVal prims (match tv with | .lit (.strVal s) => s | _ => "")
        equal lvl (.mk term.info (.mk fun _ => expanded)) term'
      | .app (.const _ _ _) _ _, .lit (.strVal _) => do
        let prims := (← read).prims
        let expanded ← strLitToCtorVal prims (match tv' with | .lit (.strVal s) => s | _ => "")
        equal lvl term (.mk term'.info (.mk fun _ => expanded))
      | _, .app (.const _ _ _) _ _ =>
        tryEtaStruct lvl term term'
      | .app (.const _ _ _) _ _, _ =>
        tryEtaStruct lvl term' term
      | .app (.proj ind idx val _) args _, .app (.proj ind' idx' val' _) args' _ =>
        if ind == ind' && idx == idx' then do
          let eqVal ← equal lvl val.sus val'.sus
          let eqThunks ← equalThunks lvl args args'
          pure (eqVal && eqThunks)
        else pure false
      | .exception e, _ | _, .exception e =>
        throw s!"exception in equal: {e}"
      | _, _ =>
        dbg_trace s!"equal FALLTHROUGH at lvl={lvl}: lhs={tv.dump} rhs={tv'.dump}"
        pure false
      if result then
        modify fun stt => { stt with equalCache := stt.equalCache.insert key true }
      return result

  /-- Check if two lists of suspended values are pointwise equal. -/
  partial def equalThunks (lvl : Nat) (vals vals' : List (SusValue m)) : TypecheckM m Bool :=
    match vals, vals' with
    | val :: vals, val' :: vals' => do
      let eq ← equal lvl val val'
      let eq' ← equalThunks lvl vals vals'
      pure (eq && eq')
    | [], [] => pure true
    | _, _ => pure false
end

end Ix.Kernel
