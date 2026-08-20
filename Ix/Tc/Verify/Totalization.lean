import Ix.Tc.Verify.Monad
import Ix.Tc.CanonicalCheck
import Ix.Tc.Check

/-!
# K0: equations for the total recursive-methods knot

These equations expose the production definitions needed by the later
`Methods.WF` induction. They also pin the runtime boundary precisely:
`methodsOut` throws `.maxRecFuel` without changing state, while a successor
table runs the selected kernel method under the predecessor table.
-/

namespace Ix.Tc

variable {m : Mode}

/-! ## Tier A/B: canonical-block comparison and refinement -/

@[simp] theorem compareKUniv_succ_equation (x y : KUniv m)
    (xi yi : Address) :
    compareKUniv (.succ x xi) (.succ y yi) = compareKUniv x y := rfl

@[simp] theorem compareKUniv_max_equation (xl xr yl yr : KUniv m)
    (xi yi : Address) :
    compareKUniv (.max xl xr xi) (.max yl yr yi) =
      (compareKUniv xl yl).andThen (compareKUniv xr yr) := rfl

@[simp] theorem mergeSorted_equation (ctx : KMutCtx)
    (resolveCtor : ResolveCtor m)
    (left right : Array (KId m × KConst m)) :
    mergeSorted ctx resolveCtor left right =
      mergeSorted.go ctx resolveCtor left right 0 0
        (Array.mkEmpty (left.size + right.size))
        (left.size + right.size) := rfl

@[simp] theorem mergeSorted_go_zero (ctx : KMutCtx)
    (resolveCtor : ResolveCtor m)
    (left right : Array (KId m × KConst m)) (li ri : Nat)
    (result : Array (KId m × KConst m)) :
    mergeSorted.go ctx resolveCtor left right li ri result 0 =
      .ok (result ++ left.extract li left.size ++
        right.extract ri right.size) := rfl

@[simp] theorem sortByCompare_equation (ctx : KMutCtx)
    (resolveCtor : ResolveCtor m)
    (items : Array (KId m × KConst m)) :
    sortByCompare ctx resolveCtor items =
      sortByCompareFuel ctx resolveCtor items.size items := rfl

@[simp] theorem sortByCompareFuel_zero (ctx : KMutCtx)
    (resolveCtor : ResolveCtor m)
    (items : Array (KId m × KConst m)) :
    sortByCompareFuel ctx resolveCtor 0 items = .ok items := rfl

@[simp] theorem sortKConstsRefineFuel_zero (resolveCtor : ResolveCtor m)
    (classes : Array (Array (KId m × KConst m))) :
    sortKConstsRefineFuel resolveCtor 0 classes = .ok classes := rfl

/-! ## Tier B: bounded diagnostic rendering -/

@[simp] theorem KExpr.render_equation (e : KExpr m) (depth : Nat) :
    e.render depth = KExpr.renderFuel (21 - depth) e depth := rfl

@[simp] theorem KExpr.renderFuel_zero (e : KExpr m) (depth : Nat) :
    KExpr.renderFuel 0 e depth = "..." := rfl

/-! ## Tier A: expression occurrence worklist -/

@[simp] theorem exprMentionsAddr_equation (e : KExpr m) (addr : Address) :
    exprMentionsAddr e addr = exprMentionsAddr.go addr [e] := rfl

@[simp] theorem exprMentionsAddr_go_nil (addr : Address) :
    exprMentionsAddr.go (m := m) addr [] = false := by
  rw [exprMentionsAddr.go]

@[simp] theorem exprMentionsAddr_go_app (addr : Address)
    (f a : KExpr m) (info : ExprInfo m) (stack : List (KExpr m)) :
    exprMentionsAddr.go addr (.app f a info :: stack) =
      exprMentionsAddr.go addr (a :: f :: stack) := by
  rw [exprMentionsAddr.go]

@[simp] theorem exprMentionsAddr_go_const (addr : Address)
    (id : KId m) (us : Array (KUniv m)) (info : ExprInfo m)
    (stack : List (KExpr m)) :
    exprMentionsAddr.go addr (.const id us info :: stack) =
      if id.addr == addr then true else exprMentionsAddr.go addr stack := by
  rw [exprMentionsAddr.go]

/-! ## Tier B: bounded context-pop loops -/

@[simp] theorem EquivManager.find_equation
    (em : EquivManager) (node : Nat) :
    em.find node =
      let (root, parent) :=
        EquivManager.find.go em.parent node em.parent.size
      (root, { em with parent }) := rfl

@[simp] theorem EquivManager.find_go_zero
    (parent : Array Nat) (node : Nat) :
    EquivManager.find.go parent node 0 = (node, parent) := rfl

@[simp] theorem EquivManager.find_go_succ
    (parent : Array Nat) (node fuel : Nat) :
    EquivManager.find.go parent node (fuel + 1) =
      if parent[node]! != node then
        let parent := parent.set! node parent[parent[node]!]!
        let node := parent[node]!
        EquivManager.find.go parent node fuel
      else
        (node, parent) := rfl

@[simp] theorem LocalContext.truncate_equation
    (lctx : LocalContext m) (len : Nat) :
    lctx.truncate len =
      LocalContext.truncate.go len lctx.decls lctx.index
        (lctx.decls.size - len) := rfl

@[simp] theorem LocalContext.truncate_go_zero
    (len : Nat) (decls : Array (FVarId × LocalDecl m))
    (index : Std.HashMap FVarId Nat) :
    LocalContext.truncate.go len decls index 0 = { decls, index } := rfl

@[simp] theorem LocalContext.truncate_go_succ
    (len fuel : Nat) (decls : Array (FVarId × LocalDecl m))
    (index : Std.HashMap FVarId Nat) :
    LocalContext.truncate.go len decls index (fuel + 1) =
      if decls.size > len then
        let (id, _) := decls.back!
        LocalContext.truncate.go len decls.pop (index.erase id) fuel
      else
        { decls, index } := rfl

/-- `restoreDepth` derives its total pop count from the current, not an
earlier, state. This is the exact replacement equation for the old `while`.
-/
@[simp] theorem TcM.restoreDepth_apply (saved : Nat) (s : TcState m) :
    TcM.restoreDepth saved s =
      TcM.restoreDepth.go saved (s.ctx.size - saved) s := rfl

@[simp] theorem TcM.restoreDepth_go_zero (saved : Nat) (s : TcState m) :
    TcM.restoreDepth.go saved 0 s = .ok () s := rfl

@[simp] theorem TcM.ctxSuffixNeed_zero (s : TcState m) (need : Nat) :
    TcM.ctxSuffixNeed s 0 need = need := rfl

@[simp] theorem TcM.ctxSuffixNeed_succ
    (s : TcState m) (fuel need : Nat) :
    TcM.ctxSuffixNeed s (fuel + 1) need =
      let nextNeed := TcM.ctxSuffixNeedStep s need
      if nextNeed == need then need
      else TcM.ctxSuffixNeed s fuel nextNeed := rfl

/-- Once the suffix closure step is stable, every positive remaining bound
returns immediately with the same suffix. -/
theorem TcM.ctxSuffixNeed_of_fixed (s : TcState m) (fuel need : Nat)
    (hfixed : TcM.ctxSuffixNeedStep s need = need) :
    TcM.ctxSuffixNeed s (fuel + 1) need = need := by
  simp [TcM.ctxSuffixNeed, hfixed]

/-! ## Tier A: pure WHNF helpers -/

/-- Exact recursive-branch equation for the structurally recursive
constructor-numeral walker. An application with a constant head has exactly
one spine argument, matching the former `collectSpine`/size test. -/
@[simp] theorem extractNatValue_app_const_equation
    (id : KId m) (us : Array (KUniv m)) (constInfo : ExprInfo m)
    (arg : KExpr m) (appInfo : ExprInfo m) (prims : Primitives m) :
    extractNatValue (.app (.const id us constInfo) arg appInfo) prims =
      if id.addr == prims.natSucc.addr then
        (extractNatValue arg prims).map (· + 1)
      else none := rfl

@[simp] theorem extractNatValue_nat_equation
    (n : Nat) (blob : Address) (info : ExprInfo m)
    (prims : Primitives m) :
    extractNatValue (.nat n blob info) prims = some n := rfl

@[simp] theorem RecM.natOffset_equation (e : KExpr m) (depth : Nat) :
    RecM.natOffset e depth = RecM.natOffsetFuel (256 - depth) e := rfl

@[simp] theorem RecM.natOffsetOrZero_equation
    (e : KExpr m) (depth : Nat) :
    RecM.natOffsetOrZero e depth = do
      return (← RecM.natOffset e depth).getD (e, 0) := rfl

@[simp] theorem RecM.evalNatOffsetLiteral_equation
    (e : KExpr m) (depth : Nat) :
    RecM.evalNatOffsetLiteral e depth =
      RecM.evalNatOffsetLiteralFuel (256 - depth) e := rfl

@[simp] theorem RecM.natOffsetFuel_zero
    (e : KExpr m) (methods : Methods m) (s : TcState m) :
    (RecM.natOffsetFuel 0 e).run methods s = .ok none s := rfl

@[simp] theorem RecM.evalNatOffsetLiteralFuel_zero
    (e : KExpr m) (methods : Methods m) (s : TcState m) :
    (RecM.evalNatOffsetLiteralFuel 0 e).run methods s = .ok none s := rfl

@[simp] theorem RecM.tryEvalNatValueForPred_equation
    (e : KExpr m) (depth : Nat) :
    RecM.tryEvalNatValueForPred e depth =
      RecM.tryEvalNatValueForPredFuel (64 - depth) e := rfl

@[simp] theorem RecM.tryEvalNatValueForPredFuel_zero
    (e : KExpr m) (methods : Methods m) (s : TcState m) :
    (RecM.tryEvalNatValueForPredFuel 0 e).run methods s = .ok none s := rfl

/-! ## Tier B: explicitly bounded kernel-loop driver -/

@[simp] theorem RecM.runBounded_zero
    (step : σ → RecM m (RecM.BoundedStep σ α))
    (state : σ) (methods : Methods m) (s : TcState m) :
    (RecM.runBounded step 0 state).run methods s =
      .error .maxRecDepth s := rfl

theorem RecM.runBounded_succ
    (step : σ → RecM m (RecM.BoundedStep σ α))
    (fuel : Nat) (state : σ) :
    RecM.runBounded step (fuel + 1) state = (do
      match ← step state with
      | .next state => RecM.runBounded step fuel state
      | .done result => return result) := rfl

@[simp] theorem RecM.consumeBetaLams_equation
    (body : KExpr m) (args : Array (KExpr m)) :
    RecM.consumeBetaLams body args =
      RecM.consumeBetaLamsFuel args.size body args
        (Array.mkEmpty args.size) := rfl

@[simp] theorem RecM.consumeBetaLamsFuel_zero
    (body : KExpr m) (args consumed : Array (KExpr m)) :
    RecM.consumeBetaLamsFuel 0 body args consumed =
      (body, consumed) := rfl

theorem RecM.consumeBetaLamsFuel_succ
    (fuel : Nat) (body : KExpr m)
    (args consumed : Array (KExpr m)) :
    RecM.consumeBetaLamsFuel (fuel + 1) body args consumed =
      if consumed.size ≥ args.size then
        (body, consumed)
      else
        match body with
        | .lam _ _ _ inner _ =>
          RecM.consumeBetaLamsFuel fuel inner args
            (consumed.push args[consumed.size]!)
        | _ => (body, consumed) := rfl

/-- Exact unfolding equation for the structurally recursive
projection-wrapper telescope walk. -/
theorem projectionDefinitionInfo_go_equation (cur : KExpr m) (arity : Nat) :
    projectionDefinitionInfo.go cur arity =
      match cur with
      | .lam _ _ _ body _ => projectionDefinitionInfo.go body (arity + 1)
      | .prj structId field projected _ =>
        match projected with
        | .var idx _ _ =>
          if idx.toNat ≥ arity then none
          else some (arity, structId, field, arity - 1 - idx.toNat)
        | _ => none
      | _ => none := by
  cases cur <;> rfl

/-! ## Tier A: extracted non-recursive WHNF helpers -/

theorem RecM.unfoldConstValue_equation (headExpr val : KExpr m)
    (us : Array (KUniv m)) :
    RecM.unfoldConstValue headExpr val us = do
      let key := headExpr.addr
      if let some cached := (← get).env.unfoldCache[key]? then
        return cached
      let result ← TcM.instantiateUnivParams val us
      modify fun s => { s with env := { s.env with
        unfoldCache := s.env.unfoldCache.insert key result } }
      return result := rfl

theorem RecM.tryDeltaUnfold_equation (e : KExpr m) :
    RecM.tryDeltaUnfold e = do
      let (head, args) := e.collectSpine
      let .const id us _ := head | return none
      let val ← match (← TcM.tryGetConst id) with
        | some (.defn (kind := kind) (val := val) ..) =>
          match kind with
          | .defn | .thm => pure val
          | .opaq => return none
        | _ => return none
      let val ← RecM.unfoldConstValue head val us
      let mut result := val
      for arg in args do
        result ← TcM.intern (KExpr.mkApp result arg)
      return some result := rfl

theorem RecM.deltaUnfoldOne_equation (e : KExpr m) :
    RecM.deltaUnfoldOne e = do
      if let some unfolded ← RecM.tryDeltaUnfold e then
        return some unfolded
      if let .const id us _ := e then
        match (← TcM.tryGetConst id) with
        | some (.defn (kind := kind) (val := val) ..) =>
          match kind with
          | .defn | .thm =>
            return some (← RecM.unfoldConstValue e val us)
          | .opaq => return none
        | _ => return none
      return none := rfl

@[simp] theorem RecM.applyIotaArg_false (result arg : KExpr m) :
    RecM.applyIotaArg result arg false =
      TcM.intern (KExpr.mkApp result arg) := rfl

@[simp] theorem RecM.applyIotaArg_true_lam
    (name : m.F Name) (bi : m.F Lean.BinderInfo)
    (dom body arg : KExpr m) (info : ExprInfo m) :
    RecM.applyIotaArg (.lam name bi dom body info) arg true =
      pure (substNoIntern body arg 0) := rfl

theorem RecM.isNatLiteralRecursorApp_equation (e : KExpr m) :
    RecM.isNatLiteralRecursorApp e = do
      let (head, spine) := e.collectSpine
      let .const id _ _ := head | return false
      let p ← RecM.prims
      if id.addr != p.natRec.addr && id.addr != p.natCasesOn.addr then
        return false
      let some (.recr (params := params) (motives := motives)
          (minors := minors) (indices := indices) ..) ←
          TcM.tryGetConst id | return false
      let majorIdx := (params + motives + minors + indices).toNat
      match spine[majorIdx]? with
      | some (.nat ..) => return true
      | _ => return false := rfl

theorem RecM.isTransientNatLiteralWork_equation (e : KExpr m) :
    RecM.isTransientNatLiteralWork e = do
      if (← RecM.isNatLiteralRecursorApp e) then
        return true
      let (head, args) := e.collectSpine
      let .const id _ _ := head | return false
      if id.addr == (← RecM.prims).natSucc.addr && args.size == 1 then
        RecM.isNatLiteralRecursorApp args[0]!
      else
        return false := rfl

theorem RecM.cleanupNatOffsetMajor_equation (e : KExpr m) :
    RecM.cleanupNatOffsetMajor e = do
      if (← RecM.evalNatOffsetLiteral e 0).isSome then
        return none
      let some (base, offset) ← RecM.natOffset e 0 | return none
      if offset == 0 then
        return none
      let predOffset := offset - 1
      let pred ← if predOffset == 0 then pure base
        else do RecM.mkNatAdd base (RecM.natExprFromValue predOffset)
      return some (← RecM.mkNatSucc pred) := rfl

theorem RecM.projectDecidableFinValMinor_equation
    (id : KId m) (field : UInt64) (minor : KExpr m) :
    RecM.projectDecidableFinValMinor id field minor = do
      let .lam name bi dom body _ := minor | return none
      let proj ← TcM.intern (KExpr.mkPrj id field body)
      return some (← TcM.intern (KExpr.mkLam name bi dom proj)) := rfl

theorem RecM.tryReduceFinValDecidableRec_equation
    (id : KId m) (field : UInt64) (head : KExpr m)
    (args : Array (KExpr m)) :
    RecM.tryReduceFinValDecidableRec id field head args = do
      if (← get).noAccel then return none
      let p ← RecM.prims
      if id.addr != p.fin.addr || field != 0 then
        return none
      let .const recId recUs _ := head | return none
      if recId.addr != p.decidableRec.addr || args.size < 5 then
        return none
      let .lam motiveName motiveBi motiveDom _ _ := args[1]!
        | return none
      let some falseMinor ←
          RecM.projectDecidableFinValMinor id field args[2]!
        | return none
      let some trueMinor ←
          RecM.projectDecidableFinValMinor id field args[3]!
        | return none
      let natTy ← TcM.intern (.mkConst p.nat #[])
      let motive ←
        TcM.intern (KExpr.mkLam motiveName motiveBi motiveDom natTy)
      let mut result ← TcM.intern (KExpr.mkConst recId recUs)
      result ← TcM.intern (KExpr.mkApp result args[0]!)
      result ← TcM.intern (KExpr.mkApp result motive)
      result ← TcM.intern (KExpr.mkApp result falseMinor)
      result ← TcM.intern (KExpr.mkApp result trueMinor)
      result ← TcM.intern (KExpr.mkApp result args[4]!)
      for arg in args.extract 5 args.size do
        result ← TcM.intern (KExpr.mkApp result arg)
      return some result := rfl

theorem RecM.tryReduceProjectionDefinition_equation (e : KExpr m) :
    RecM.tryReduceProjectionDefinition e = do
      let (head, args) := e.collectSpine
      let .const id _ _ := head | return none
      let val ← match (← TcM.tryGetConst id) with
        | some (.defn (kind := .defn) (val := val) ..) => pure val
        | _ => return none
      let some (arity, structId, field, structArgIdx) :=
        projectionDefinitionInfo val | return none
      if args.size < arity then
        return none
      let mut result ←
        TcM.intern (KExpr.mkPrj structId field args[structArgIdx]!)
      for arg in args.extract arity args.size do
        result ← TcM.intern (KExpr.mkApp result arg)
      return some result := rfl

theorem RecM.natRecLiteralParts_equation (e : KExpr m) :
    RecM.natRecLiteralParts e = do
      let (head, spine) := e.collectSpine
      let .const id _ _ := head | return none
      if id.addr != (← RecM.prims).natRec.addr then
        return none
      let some (.recr (params := params) (motives := motives)
          (minors := minors) (indices := indices) ..) ←
          TcM.tryGetConst id | return none
      if minors.toNat < 2 then
        return none
      let baseIdx := params.toNat + motives.toNat
      let stepIdx := baseIdx + 1
      let majorIdx :=
        params.toNat + motives.toNat + minors.toNat + indices.toNat
      let some (.nat major _ _) := spine[majorIdx]? | return none
      return some { spine, major, baseIdx, stepIdx, majorIdx } := rfl

theorem RecM.isNatStuckRecursorAddr_equation (addr : Address) :
    RecM.isNatStuckRecursorAddr (m := m) addr = do
      let p ← RecM.prims
      return addr == p.natRec.addr || addr == p.natCasesOn.addr
        || addr == p.bitVecToNat.addr := rfl

theorem RecM.isStuckNatPredicateProbe_equation (e : KExpr m) :
    RecM.isStuckNatPredicateProbe e = do
      let (head, _) := e.collectSpine
      match head with
      | .const id _ _ =>
        return (← RecM.isNatBinPredAddr id.addr) ||
          (← RecM.isNatStuckRecursorAddr id.addr)
      | .prj id _ val _ =>
        if id.addr == (← RecM.prims).fin.addr then
          return true
        let (valHead, _) := val.collectSpine
        match valHead with
        | .const valId _ _ => RecM.isNatStuckRecursorAddr valId.addr
        | _ => return false
      | _ => return false := rfl

theorem RecM.bitvecOfNatArgs_equation (e : KExpr m) :
    RecM.bitvecOfNatArgs e = do
      let p ← RecM.prims
      let (head, args) := e.collectSpine
      let .const id _ _ := head | return none
      if id.addr == p.bitVecOfNat.addr && args.size == 2 then
        return some (args[0]!, args[1]!)
      if id.addr != p.ofNatOfNat.addr || args.size < 2 then
        return none
      let (typeHead, typeArgs) := args[0]!.collectSpine
      let .const typeId _ _ := typeHead | return none
      if typeId.addr == p.bitVec.addr && typeArgs.size == 1 then
        return some (typeArgs[0]!, args[1]!)
      return none := rfl

theorem RecM.charOfNatExpr_equation (n : Nat) :
    RecM.charOfNatExpr (m := m) n = do
      let charOfNat ← TcM.intern (.mkConst (← RecM.prims).charOfNat #[])
      let natLit ← TcM.intern (RecM.natExprFromValue n : KExpr m)
      return some (← TcM.intern (KExpr.mkApp charOfNat natLit)) := rfl

theorem RecM.tryReduceStringLiteral_equation (p : Primitives m)
    (id : KId m) (s : String) :
    RecM.tryReduceStringLiteral p id s = (do
      let isUtf8ByteSize := id.addr == p.stringUtf8ByteSize.addr
      let isToByteArray := id.addr == p.stringToByteArray.addr
      if isUtf8ByteSize then
        return some (← TcM.intern
          (RecM.natExprFromValue s.utf8ByteSize : KExpr m))
      if isToByteArray then
        if s.isEmpty then
          return some (← TcM.intern (.mkConst p.byteArrayEmpty #[]))
        return none
      let codepoint := (s.toList.getLast?.map (·.toNat)).getD 65
      RecM.charOfNatExpr codepoint) := rfl

theorem RecM.tryReduceString_equation (e : KExpr m) :
    RecM.tryReduceString e = (do
      let (head, args) := e.collectSpine
      if args.size != 1 then
        return none
      let .const id _ _ := head | return none
      let p ← RecM.prims
      let isBack := id.addr == p.stringBack.addr ||
        id.addr == p.stringLegacyBack.addr
      let isUtf8ByteSize := id.addr == p.stringUtf8ByteSize.addr
      let isToByteArray := id.addr == p.stringToByteArray.addr
      if !isBack && !isUtf8ByteSize && !isToByteArray then
        return none
      let .str s _ _ := args[0]! | return none
      if isUtf8ByteSize then
        return some (← TcM.intern
          (RecM.natExprFromValue s.utf8ByteSize : KExpr m))
      if isToByteArray then
        if s.isEmpty then
          return some (← TcM.intern (.mkConst p.byteArrayEmpty #[]))
        return none
      let codepoint := (s.toList.getLast?.map (·.toNat)).getD 65
      RecM.charOfNatExpr codepoint) := rfl

theorem RecM.discoverBlockInductives_equation (blockId : KId m) :
    RecM.discoverBlockInductives blockId = do
      let some members ← TcM.tryGetBlock blockId | return #[]
      let mut inds : Array (KId m) := #[]
      for id in members do
        if let some (.indc ..) ← TcM.tryGetConst id then
          inds := inds.push id
      return inds := rfl

/-! ## Tier A: extracted non-recursive def-eq helpers -/

@[simp] theorem RecM.compareRank_equation (a b : Nat × Nat) :
    RecM.compareRank a b =
      match compare a.1 b.1 with
      | .eq => compare a.2 b.2
      | o => o := rfl

theorem RecM.isNatLike_equation (e : KExpr m) :
    RecM.isNatLike e = do
      let p ← RecM.prims
      match e with
      | .nat .. => return true
      | .const id _ _ => return id.addr == p.natZero.addr
      | .app f _ _ =>
        match f with
        | .const id _ _ => return id.addr == p.natSucc.addr
        | _ => return false
      | _ => return false := rfl

theorem RecM.isNatZero_equation (e : KExpr m) :
    RecM.isNatZero e = do
      let p ← RecM.prims
      match e with
      | .nat v _ _ => return v == 0
      | .const id _ _ => return id.addr == p.natZero.addr
      | _ => return false := rfl

theorem RecM.natSuccOf_equation (e : KExpr m) :
    RecM.natSuccOf e = do
      let p ← RecM.prims
      match e with
      | .nat v _ _ =>
        if v == 0 then
          return none
        return some (← TcM.intern
          (RecM.natExprFromValue (v - 1) : KExpr m))
      | .app f arg _ =>
        match f with
        | .const id _ _ =>
          if id.addr == p.natSucc.addr then
            return some arg
          return none
        | _ => return none
      | _ => return none := rfl

theorem RecM.isBoolTrue_equation (e : KExpr m) :
    RecM.isBoolTrue e = do
      match e with
      | .const id us _ =>
        return us.isEmpty && id.addr == (← RecM.prims).boolTrue.addr
      | _ => return false := rfl

theorem RecM.isDelta_equation (id : KId m) :
    RecM.isDelta id = do
      match (← TcM.tryGetConst id) with
      | some (.defn (kind := kind) ..) =>
        match kind with
        | .defn | .thm => return true
        | .opaq => return false
      | _ => return false := rfl

theorem RecM.isRegular_equation (id : KId m) :
    RecM.isRegular id = do
      match (← TcM.tryGetConst id) with
      | some (.defn (hints := .regular _) ..) => return true
      | _ => return false := rfl

theorem RecM.defRankId_equation (id : KId m) :
    RecM.defRankId id = do
      match (← TcM.tryGetConst id) with
      | some (.defn (kind := kind) (hints := hints) ..) =>
        match kind with
        | .opaq | .thm => return (0, 0)
        | .defn =>
          match hints with
          | .opaque => return (0, 0)
          | .regular h => return (1, h.toNat)
          | .abbrev => return (2, 0)
      | _ => return (0, 0) := rfl

/-! ## Tier C: Infer's method-indexed structural recursion -/

@[simp] theorem RecM.infer_eq_inferWith (e : KExpr m) :
    RecM.infer e = RecM.inferWith RecM.inferCall e := rfl

@[simp] theorem RecM.inferCall_run (e : KExpr m)
    (methods : Methods m) (s : TcState m) :
    (RecM.inferCall e).run methods s = methods.infer e s := rfl

@[simp] theorem RecM.inferOnlyCall_run (e : KExpr m)
    (methods : Methods m) (s : TcState m) :
    (RecM.inferOnlyCall e).run methods s =
      TcM.withInferOnly (methods.infer e) s := rfl

@[simp] theorem RecM.isDefEqCall_run (a b : KExpr m)
    (methods : Methods m) (s : TcState m) :
    (RecM.isDefEqCall a b).run methods s = methods.isDefEq a b s := rfl

@[simp] theorem RecM.whnfRec_run (e : KExpr m)
    (methods : Methods m) (s : TcState m) :
    (RecM.whnfRec e).run methods s = methods.whnf e s := rfl

@[simp] theorem RecM.whnfModeRec_run (e : KExpr m) (mode : NatSuccMode)
    (methods : Methods m) (s : TcState m) :
    (RecM.whnfModeRec e mode).run methods s =
      methods.whnfMode e mode s := rfl

@[simp] theorem RecM.whnfCoreFlagsRec_run
    (e : KExpr m) (flags : WhnfFlags)
    (methods : Methods m) (s : TcState m) :
    (RecM.whnfCoreFlagsRec e flags).run methods s =
      methods.whnfCoreFlags e flags s := rfl

@[simp] theorem RecM.whnf_eq_whnfWithNatSuccMode (e : KExpr m) :
    RecM.whnf e = RecM.whnfWithNatSuccMode e .collapse := rfl

@[simp] theorem RecM.whnfCore_eq_whnfCoreWithFlags (e : KExpr m) :
    RecM.whnfCore e = RecM.whnfCoreWithFlags e .FULL := rfl

@[simp] theorem RecM.whnfNoDelta_eq_whnfNoDeltaImpl (e : KExpr m) :
    RecM.whnfNoDelta e =
      RecM.whnfNoDeltaImpl e .FULL .collapse := rfl

theorem RecM.ensureSortDirect_equation (e : KExpr m) :
    RecM.ensureSortDirect e = (do
      if let .sort u _ := e then
        return u
      match (← RecM.whnf e) with
      | .sort u _ => return u
      | _ => throw .typeExpected) := rfl

theorem RecM.ensureForallDirect_equation (e : KExpr m) :
    RecM.ensureForallDirect e = (do
      if let .all _ _ a b _ := e then
        return (a, b)
      let w ← RecM.whnf e
      match w with
      | .all _ _ a b _ => return (a, b)
      | _ => throw (.funExpected e w)) := rfl

theorem RecM.peelProjForall_equation (e : KExpr m) (err : String) :
    RecM.peelProjForall e err = (do
      if let .all _ _ dom body _ := e then
        return (dom, body)
      match (← RecM.whnf e) with
      | .all _ _ dom body _ => return (dom, body)
      | _ => throw (.other err)) := rfl

/-! ## Tier A: total safety-reference worklist -/

@[simp] theorem RecM.checkNoUnsafeRefs_equation
    (root : KExpr m) (callerSafety : Ix.DefinitionSafety) :
    RecM.checkNoUnsafeRefs root callerSafety =
      RecM.checkNoUnsafeRefs.go callerSafety [root] {} {} := rfl

@[simp] theorem RecM.checkNoUnsafeRefs_go_nil
    (callerSafety : Ix.DefinitionSafety)
    (seenExprs seenConsts : Std.HashSet Address) :
    RecM.checkNoUnsafeRefs.go (m := m) callerSafety []
      seenExprs seenConsts = pure () := by
  rw [RecM.checkNoUnsafeRefs.go]

theorem RecM.checkNoUnsafeRefs_go_app
    (callerSafety : Ix.DefinitionSafety) (f a : KExpr m)
    (info : ExprInfo m) (stack : List (KExpr m))
    (seenExprs seenConsts : Std.HashSet Address) :
    RecM.checkNoUnsafeRefs.go callerSafety (.app f a info :: stack)
        seenExprs seenConsts =
      if seenExprs.contains (.app f a info : KExpr m).addr then
        RecM.checkNoUnsafeRefs.go callerSafety stack seenExprs seenConsts
      else
        RecM.checkNoUnsafeRefs.go callerSafety (a :: f :: stack)
          (seenExprs.insert (.app f a info : KExpr m).addr) seenConsts := by
  rw [RecM.checkNoUnsafeRefs.go]

/-! ## Tier A/B: total inductive validation and telescope scans -/

@[simp] theorem RecM.validateUnivParamsSeen_equation
    (root : KUniv m) (bound : Nat) (seen : Std.HashSet Address) :
    RecM.validateUnivParamsSeen root bound seen =
      RecM.validateUnivParamsSeen.go bound [root] seen := rfl

@[simp] theorem RecM.validateUnivParamsSeen_go_nil
    (bound : Nat) (seen : Std.HashSet Address) :
    RecM.validateUnivParamsSeen.go (m := m) bound [] seen = pure seen := by
  rw [RecM.validateUnivParamsSeen.go]

theorem RecM.validateUnivParamsSeen_go_max
    (bound : Nat) (a b : KUniv m) (addr : Address)
    (stack : List (KUniv m)) (seen : Std.HashSet Address) :
    RecM.validateUnivParamsSeen.go bound (.max a b addr :: stack) seen =
      if seen.contains addr then
        RecM.validateUnivParamsSeen.go bound stack seen
      else
        RecM.validateUnivParamsSeen.go bound (b :: a :: stack)
          (seen.insert addr) := by
  rw [RecM.validateUnivParamsSeen.go]
  simp [KUniv.addr]

@[simp] theorem RecM.validateExprWellScoped_equation
    (root : KExpr m) (rootDepth : UInt64) (lvlBound : Nat) :
    RecM.validateExprWellScoped root rootDepth lvlBound =
      RecM.validateExprWellScoped.go lvlBound [(root, rootDepth)] {} {} := rfl

@[simp] theorem RecM.validateExprWellScoped_go_nil
    (lvlBound : Nat) (seenExprs : Std.HashSet (Address × UInt64))
    (seenUnivs : Std.HashSet Address) :
    RecM.validateExprWellScoped.go (m := m) lvlBound []
      seenExprs seenUnivs = pure () := by
  rw [RecM.validateExprWellScoped.go]

theorem RecM.validateExprWellScoped_go_app
    (lvlBound : Nat) (f a : KExpr m) (info : ExprInfo m) (depth : UInt64)
    (stack : List (KExpr m × UInt64))
    (seenExprs : Std.HashSet (Address × UInt64))
    (seenUnivs : Std.HashSet Address) :
    RecM.validateExprWellScoped.go lvlBound
        ((.app f a info, depth) :: stack) seenExprs seenUnivs =
      if seenExprs.contains ((.app f a info : KExpr m).addr, depth) then
        RecM.validateExprWellScoped.go lvlBound stack seenExprs seenUnivs
      else
        RecM.validateExprWellScoped.go lvlBound
          ((a, depth) :: (f, depth) :: stack)
          (seenExprs.insert ((.app f a info : KExpr m).addr, depth))
          seenUnivs := by
  rw [RecM.validateExprWellScoped.go]

@[simp] theorem RecM.peelRuleIhForalls_equation
    (root : KExpr m) (flat : Array (FlatBlockMember m)) :
    RecM.peelRuleIhForalls root flat =
      RecM.peelRuleIhForalls.go flat root #[] := rfl

@[simp] theorem RecM.checkPositivityDomain_equation
    (dom : KExpr m) (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) :
    RecM.checkPositivityDomain dom groups activeAddrs =
      RecM.checkPositivityDomainFuel maxWhnfFuel.toNat dom groups
        activeAddrs := rfl

@[simp] theorem RecM.checkPositivityDomainFuel_zero
    (dom : KExpr m) (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) :
    RecM.checkPositivityDomainFuel 0 dom groups activeAddrs =
      throw .maxRecDepth := rfl

@[simp] theorem RecM.checkNestedCtorFieldsFuel_zero
    (ctorTy : KExpr m) (nParams : Nat) (paramArgs : Array (KExpr m))
    (us : Array (KUniv m)) (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) :
    RecM.checkNestedCtorFieldsFuel 0 ctorTy nParams paramArgs us
      groups activeAddrs = throw .maxRecDepth := rfl

@[simp] theorem RecM.checkNestedCtorFieldsLoopFuel_zero
    (ty : KExpr m) (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) :
    RecM.checkNestedCtorFieldsLoopFuel 0 ty groups activeAddrs =
      throw .maxRecDepth := rfl

theorem RecM.countForalls_equation (ty : KExpr m) :
    RecM.countForalls ty = (do
      let saved := (← get).lctx.size
      RecM.runBounded (fun (cur, n) => do
        let w ← RecM.whnf cur
        match w with
        | .all name bi dom body _ =>
          let fvId ← TcM.freshFVarId (m := m)
          let fv ← TcM.intern (.mkFVar fvId name)
          modify fun s =>
            { s with lctx := s.lctx.push fvId (.cdecl name bi dom) }
          let cur ← TcM.runIntern (instantiateRev body #[fv])
          return .next (cur, n + 1)
        | _ =>
          modify fun s => { s with lctx := s.lctx.truncate saved }
          return .done n) maxWhnfFuel.toNat (ty, 0)) := rfl

/-! ## Tier C: total recursive-methods knot -/

@[simp] theorem methodsN_zero : methodsN (m := m) 0 = methodsOut := rfl

@[simp] theorem methodsN_succ_whnf (n : Nat) (e : KExpr m) :
    (methodsN (m := m) (n + 1)).whnf e =
      (RecM.whnf e).run (methodsN n) := rfl

@[simp] theorem methodsN_succ_whnfCore (n : Nat) (e : KExpr m) :
    (methodsN (m := m) (n + 1)).whnfCore e =
      (RecM.whnfCore e).run (methodsN n) := rfl

@[simp] theorem methodsN_succ_whnfMode
    (n : Nat) (e : KExpr m) (mode : NatSuccMode) :
    (methodsN (m := m) (n + 1)).whnfMode e mode =
      (RecM.whnfWithNatSuccMode e mode).run (methodsN n) := rfl

@[simp] theorem methodsN_succ_whnfCoreFlags
    (n : Nat) (e : KExpr m) (flags : WhnfFlags) :
    (methodsN (m := m) (n + 1)).whnfCoreFlags e flags =
      (RecM.whnfCoreWithFlags e flags).run (methodsN n) := rfl

@[simp] theorem methodsN_succ_infer (n : Nat) (e : KExpr m) :
    (methodsN (m := m) (n + 1)).infer e =
      (RecM.infer e).run (methodsN n) := rfl

@[simp] theorem methodsN_succ_isDefEq (n : Nat) (a b : KExpr m) :
    (methodsN (m := m) (n + 1)).isDefEq a b =
      (RecM.isDefEq a b).run (methodsN n) := rfl

@[simp] theorem methodsOut_whnf (e : KExpr m) (s : TcState m) :
    methodsOut.whnf e s = .error .maxRecFuel s := rfl

@[simp] theorem methodsOut_whnfCore (e : KExpr m) (s : TcState m) :
    methodsOut.whnfCore e s = .error .maxRecFuel s := rfl

@[simp] theorem methodsOut_whnfMode
    (e : KExpr m) (mode : NatSuccMode) (s : TcState m) :
    methodsOut.whnfMode e mode s = .error .maxRecFuel s := rfl

@[simp] theorem methodsOut_whnfCoreFlags
    (e : KExpr m) (flags : WhnfFlags) (s : TcState m) :
    methodsOut.whnfCoreFlags e flags s = .error .maxRecFuel s := rfl

@[simp] theorem methodsOut_infer (e : KExpr m) (s : TcState m) :
    methodsOut.infer e s = .error .maxRecFuel s := rfl

@[simp] theorem methodsOut_isDefEq (a b : KExpr m) (s : TcState m) :
    methodsOut.isDefEq a b s = .error .maxRecFuel s := rfl

/-- Public recursive computations select their table from the current
`recFuel`; `fuelBudget` does not participate in this equation. -/
@[simp] theorem TcM.runRec_apply (x : RecM m α) (s : TcState m) :
    TcM.runRec x s = x.run (methodsN s.recFuel.toNat) s := rfl

/-- At zero current fuel, the first direct `infer` table back-edge has the
same error and unchanged error state as `methodsOut`. The top-level `x`
itself is still allowed to run if it never takes a back-edge. -/
theorem TcM.runRec_directInfer_zero (e : KExpr m) (s : TcState m)
    (hzero : s.recFuel = 0) :
    TcM.runRec (fun methods => methods.infer e) s =
      .error .maxRecFuel s := by
  unfold TcM.runRec
  rw [hzero]
  rfl

@[simp] theorem TcM.whnf_eq_runRec (e : KExpr m) :
    TcM.whnf e = TcM.runRec (RecM.whnf e) := rfl

@[simp] theorem TcM.whnfCore_eq_runRec (e : KExpr m) :
    TcM.whnfCore e = TcM.runRec (RecM.whnfCore e) := rfl

@[simp] theorem TcM.whnfNoDelta_eq_runRec (e : KExpr m) :
    TcM.whnfNoDelta e = TcM.runRec (RecM.whnfNoDelta e) := rfl

@[simp] theorem TcM.infer_eq_runRec (e : KExpr m) :
    TcM.infer e = TcM.runRec (RecM.infer e) := rfl

@[simp] theorem TcM.isDefEq_eq_runRec (a b : KExpr m) :
    TcM.isDefEq a b = TcM.runRec (RecM.isDefEq a b) := rfl

@[simp] theorem TcM.ensureSort_eq_runRec (e : KExpr m) :
    TcM.ensureSort e = TcM.runRec (RecM.ensureSortDirect e) := rfl

@[simp] theorem TcM.ensureForall_eq_runRec (e : KExpr m) :
    TcM.ensureForall e = TcM.runRec (RecM.ensureForallDirect e) := rfl

end Ix.Tc
