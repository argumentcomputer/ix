import Ix.Compile.Verify.ExprCodec
import Ix.Compile.Verify.Catalog

/-!
# Arbitrary canonical expression-spine codec

The first expression-codec slice covered singleton application, lambda, and
forall spines.  Production expression compilation deliberately constructs
arbitrary flattened spines, while the production codec writes each whole
spine behind one wire-sized count.  This module establishes the telescope
algebra needed to lift the codec proof to that production domain.
-/

namespace Ix.Compile.Verify.Codec.Ixon.Expr

/-! ## Application telescopes -/

theorem collectAppArgs_length (expr : Ixon.Expr) :
    expr.collectAppArgs.1.length = expr.appCount := by
  induction expr with
  | app fn arg ihFn _ =>
    simp [Ixon.Expr.collectAppArgs, Ixon.Expr.appCount, ihFn]
  | sort | var | ref | recur | prj | str | nat | lam | all | letE | share =>
    rfl

theorem collectAppArgs_base_notApp (expr : Ixon.Expr) :
    notApp expr.collectAppArgs.2 := by
  induction expr with
  | app fn arg ihFn _ =>
    simpa [Ixon.Expr.collectAppArgs] using ihFn
  | sort | var | ref | recur | prj | str | nat | lam | all | letE | share =>
    trivial

theorem collectAppArgs_reconstruct (expr : Ixon.Expr) :
    expr.collectAppArgs.1.foldl Ixon.Expr.app expr.collectAppArgs.2 = expr := by
  induction expr with
  | app fn arg ihFn _ =>
    simp [Ixon.Expr.collectAppArgs, List.foldl_append, ihFn]
  | sort | var | ref | recur | prj | str | nat | lam | all | letE | share =>
    rfl

theorem collectAppArgs_base_wireWF {expr : Ixon.Expr}
    (h : expr.wireWF) : expr.collectAppArgs.2.wireWF := by
  induction expr with
  | app fn arg ihFn _ =>
    exact ihFn h.1
  | sort | var | ref | recur | prj | str | nat | lam | all | letE | share =>
    simpa [Ixon.Expr.collectAppArgs] using h

theorem collectAppArgs_mem_wireWF {expr arg : Ixon.Expr}
    (h : expr.wireWF) (hmem : arg ∈ expr.collectAppArgs.1) : arg.wireWF := by
  induction expr with
  | app fn actual ihFn _ =>
    simp only [Ixon.Expr.collectAppArgs] at hmem
    rcases List.mem_append.mp hmem with hfn | hactual
    · exact ihFn h.1 hfn
    · have : arg = actual := by simpa using hactual
      subst arg
      exact h.2.1
  | sort | var | ref | recur | prj | str | nat | lam | all | letE | share =>
    exact nomatch hmem

/-! ## Lambda telescopes -/

theorem collectLamBinders_length (expr : Ixon.Expr) :
    expr.collectLamBinders.1.length = expr.lamCount := by
  induction expr with
  | lam uses ty body _ ihBody =>
    simp [Ixon.Expr.collectLamBinders, Ixon.Expr.lamCount, ihBody]
  | sort | var | ref | recur | prj | str | nat | app | all | letE | share =>
    rfl

theorem collectLamBinders_base_notLam (expr : Ixon.Expr) :
    notLam expr.collectLamBinders.2 := by
  induction expr with
  | lam uses ty body _ ihBody =>
    simpa [Ixon.Expr.collectLamBinders] using ihBody
  | sort | var | ref | recur | prj | str | nat | app | all | letE | share =>
    trivial

theorem collectLamBinders_reconstruct (expr : Ixon.Expr) :
    expr.collectLamBinders.1.foldr
        (fun binder body => .lam binder.1 binder.2 body)
        expr.collectLamBinders.2 = expr := by
  induction expr with
  | lam uses ty body _ ihBody =>
    simp [Ixon.Expr.collectLamBinders, ihBody]
  | sort | var | ref | recur | prj | str | nat | app | all | letE | share =>
    rfl

theorem collectLamBinders_base_wireWF {expr : Ixon.Expr}
    (h : expr.wireWF) : expr.collectLamBinders.2.wireWF := by
  induction expr with
  | lam uses ty body _ ihBody =>
    exact ihBody h.2.1
  | sort | var | ref | recur | prj | str | nat | app | all | letE | share =>
    simpa [Ixon.Expr.collectLamBinders] using h

theorem collectLamBinders_mem_wireWF {expr ty : Ixon.Expr}
    (h : expr.wireWF)
    (hmem : ∃ uses, (uses, ty) ∈ expr.collectLamBinders.1) : ty.wireWF := by
  induction expr with
  | lam uses binder body _ ihBody =>
    rcases hmem with ⟨foundUses, hmem⟩
    simp only [Ixon.Expr.collectLamBinders] at hmem
    rcases List.mem_cons.mp hmem with hhead | htail
    · have : ty = binder := congrArg Prod.snd hhead
      subst ty
      exact h.1
    · exact ihBody h.2.1 ⟨foundUses, htail⟩
  | sort | var | ref | recur | prj | str | nat | app | all | letE | share =>
    rcases hmem with ⟨_, hmem⟩
    exact nomatch hmem

/-! ## Forall telescopes -/

theorem collectAllBinders_length (expr : Ixon.Expr) :
    expr.collectAllBinders.1.length = expr.allCount := by
  induction expr with
  | all uses owned ty body _ ihBody =>
    simp [Ixon.Expr.collectAllBinders, Ixon.Expr.allCount, ihBody]
  | sort | var | ref | recur | prj | str | nat | app | lam | letE | share =>
    rfl

theorem collectAllBinders_base_notAll (expr : Ixon.Expr) :
    notAll expr.collectAllBinders.2 := by
  induction expr with
  | all uses owned ty body _ ihBody =>
    simpa [Ixon.Expr.collectAllBinders] using ihBody
  | sort | var | ref | recur | prj | str | nat | app | lam | letE | share =>
    trivial

theorem collectAllBinders_reconstruct (expr : Ixon.Expr) :
    expr.collectAllBinders.1.foldr
        (fun binder body => .all binder.1 binder.2.1 binder.2.2 body)
        expr.collectAllBinders.2 = expr := by
  induction expr with
  | all uses owned ty body _ ihBody =>
    simp [Ixon.Expr.collectAllBinders, ihBody]
  | sort | var | ref | recur | prj | str | nat | app | lam | letE | share =>
    rfl

theorem collectAllBinders_base_wireWF {expr : Ixon.Expr}
    (h : expr.wireWF) : expr.collectAllBinders.2.wireWF := by
  induction expr with
  | all uses owned ty body _ ihBody =>
    exact ihBody h.2.1
  | sort | var | ref | recur | prj | str | nat | app | lam | letE | share =>
    simpa [Ixon.Expr.collectAllBinders] using h

theorem collectAllBinders_mem_wireWF {expr ty : Ixon.Expr}
    (h : expr.wireWF)
    (hmem : ∃ uses owned,
      (uses, owned, ty) ∈ expr.collectAllBinders.1) : ty.wireWF := by
  induction expr with
  | all uses owned binder body _ ihBody =>
    rcases hmem with ⟨foundUses, foundOwned, hmem⟩
    simp only [Ixon.Expr.collectAllBinders] at hmem
    rcases List.mem_cons.mp hmem with hhead | htail
    · have : ty = binder := congrArg (fun entry => entry.2.2) hhead
      subst ty
      exact h.1
    · exact ihBody h.2.1 ⟨foundUses, foundOwned, htail⟩
  | sort | var | ref | recur | prj | str | nat | app | lam | letE | share =>
    rcases hmem with ⟨_, _, hmem⟩
    exact nomatch hmem

/-! ## Canonical whole-spine bytes -/

def exprListBytes (encode : Ixon.Expr → ByteArray) : List Ixon.Expr → ByteArray
  | [] => ByteArray.empty
  | expr :: exprs => encode expr ++ exprListBytes encode exprs

def lamBinderListBytes (encode : Ixon.Expr → ByteArray) :
    List (Ixon.Uses × Ixon.Expr) → ByteArray
  | [] => ByteArray.empty
  | (uses, ty) :: binders =>
      [uses.toBits].toByteArray ++ encode ty ++
        lamBinderListBytes encode binders

def allBinderListBytes (encode : Ixon.Expr → ByteArray) :
    List (Ixon.Uses × Ixon.Owned × Ixon.Expr) → ByteArray
  | [] => ByteArray.empty
  | (uses, owned, ty) :: binders =>
      [uses.toBits ||| (owned.toBits <<< 2)].toByteArray ++ encode ty ++
        allBinderListBytes encode binders

def allBinderMode (uses : Ixon.Uses) (owned : Ixon.Owned) : UInt8 :=
  uses.toBits ||| (owned.toBits <<< 2)

@[simp] theorem allBinderTriple_type
    (uses : Ixon.Uses) (owned : Ixon.Owned) (ty : Ixon.Expr) :
    ((uses, owned, ty) : Ixon.Uses × Ixon.Owned × Ixon.Expr).2.2 = ty := by
  rfl

/-- Exact bytes written by the production codec when complete application
and binder telescopes are compressed behind one count. -/
def spineWireEncode : Ixon.Expr → ByteArray
  | .sort idx => tag4Bytes Ixon.Expr.FLAG_SORT idx
  | .var idx => tag4Bytes Ixon.Expr.FLAG_VAR idx
  | .ref refIdx univs =>
      tag4Bytes Ixon.Expr.FLAG_REF univs.size.toUInt64 ++ tag0Bytes refIdx ++
        tag0ListBytes univs.toList
  | .recur recIdx univs =>
      tag4Bytes Ixon.Expr.FLAG_REC univs.size.toUInt64 ++ tag0Bytes recIdx ++
        tag0ListBytes univs.toList
  | .prj typeRefIdx fieldIdx val =>
      tag4Bytes Ixon.Expr.FLAG_PRJ fieldIdx ++ tag0Bytes typeRefIdx ++
        spineWireEncode val
  | .str refIdx => tag4Bytes Ixon.Expr.FLAG_STR refIdx
  | .nat refIdx => tag4Bytes Ixon.Expr.FLAG_NAT refIdx
  | expr@(.app _ _) =>
      tag4Bytes Ixon.Expr.FLAG_APP
          expr.collectAppArgs.1.length.toUInt64 ++
        spineWireEncode expr.collectAppArgs.2 ++
          expr.collectAppArgs.1.attach.foldl (init := ByteArray.empty)
            (fun bytes arg => bytes ++ spineWireEncode arg.1)
  | expr@(.lam _ _ _) =>
      tag4Bytes Ixon.Expr.FLAG_LAM
          expr.collectLamBinders.1.length.toUInt64 ++
        expr.collectLamBinders.1.attach.foldl (init := ByteArray.empty)
            (fun bytes binder =>
              bytes ++ [binder.1.1.toBits].toByteArray ++
                spineWireEncode binder.1.2) ++
          spineWireEncode expr.collectLamBinders.2
  | expr@(.all _ _ _ _) =>
      tag4Bytes Ixon.Expr.FLAG_ALL
          expr.collectAllBinders.1.length.toUInt64 ++
        expr.collectAllBinders.1.attach.foldl (init := ByteArray.empty)
            (fun bytes binder =>
              bytes ++
                [allBinderMode binder.1.1 binder.1.2.1].toByteArray ++
                  spineWireEncode binder.1.2.2) ++
          spineWireEncode expr.collectAllBinders.2
  | .letE nonDep ty val body =>
      tag4Bytes Ixon.Expr.FLAG_LET (if nonDep then 1 else 0) ++
        spineWireEncode ty ++ spineWireEncode val ++ spineWireEncode body
  | .share idx => tag4Bytes Ixon.Expr.FLAG_SHARE idx
termination_by expr => expr.nodeCount
decreasing_by
  all_goals simp_wf
  all_goals simp only [Ixon.Expr.nodeCount]
  all_goals try omega
  · subst expr
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAppArgs_base_nodeCount_lt _ _
  · subst expr
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAppArgs_mem_nodeCount_lt (.app _ _) arg.1 arg.2
  · subst expr
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectLamBinders_mem_nodeCount_lt
        (.lam _ _ _) binder.1.2 ⟨binder.1.1, binder.2⟩
  · subst expr
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectLamBinders_base_nodeCount_lt _ _ _
  · subst expr
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAllBinders_mem_nodeCount_lt
        (.all _ _ _ _) binder.1.2.2
        ⟨binder.1.1, binder.1.2.1, binder.2⟩
  · subst expr
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAllBinders_base_nodeCount_lt _ _ _ _

theorem spineWireEncode_size_pos (expr : Ixon.Expr) :
    0 < (spineWireEncode expr).size := by
  cases expr with
  | sort idx => simpa [spineWireEncode] using
      tag4Bytes_size_pos Ixon.Expr.FLAG_SORT idx
  | var idx => simpa [spineWireEncode] using
      tag4Bytes_size_pos Ixon.Expr.FLAG_VAR idx
  | ref refIdx univs =>
      have h := tag4Bytes_size_pos Ixon.Expr.FLAG_REF univs.size.toUInt64
      simp only [spineWireEncode, ByteArray.size_append]
      omega
  | recur recIdx univs =>
      have h := tag4Bytes_size_pos Ixon.Expr.FLAG_REC univs.size.toUInt64
      simp only [spineWireEncode, ByteArray.size_append]
      omega
  | prj typeRefIdx fieldIdx val =>
      have h := tag4Bytes_size_pos Ixon.Expr.FLAG_PRJ fieldIdx
      simp only [spineWireEncode, ByteArray.size_append]
      omega
  | str refIdx => simpa [spineWireEncode] using
      tag4Bytes_size_pos Ixon.Expr.FLAG_STR refIdx
  | nat refIdx => simpa [spineWireEncode] using
      tag4Bytes_size_pos Ixon.Expr.FLAG_NAT refIdx
  | app fn arg =>
      have h := tag4Bytes_size_pos Ixon.Expr.FLAG_APP
        (Ixon.Expr.app fn arg).collectAppArgs.1.length.toUInt64
      simp only [spineWireEncode, ByteArray.size_append]
      omega
  | lam uses ty body =>
      have h := tag4Bytes_size_pos Ixon.Expr.FLAG_LAM
        (Ixon.Expr.lam uses ty body).collectLamBinders.1.length.toUInt64
      simp only [spineWireEncode, ByteArray.size_append]
      omega
  | all uses owned ty body =>
      have h := tag4Bytes_size_pos Ixon.Expr.FLAG_ALL
        (Ixon.Expr.all uses owned ty body).collectAllBinders.1.length.toUInt64
      simp only [spineWireEncode, ByteArray.size_append]
      omega
  | letE nonDep ty val body =>
      have h := tag4Bytes_size_pos Ixon.Expr.FLAG_LET
        (if nonDep then 1 else 0)
      simp only [spineWireEncode, ByteArray.size_append]
      omega
  | share idx => simpa [spineWireEncode] using
      tag4Bytes_size_pos Ixon.Expr.FLAG_SHARE idx

theorem attachFold_exprListBytes (encode : Ixon.Expr → ByteArray)
    (exprs : List Ixon.Expr) (initial : ByteArray) :
    exprs.attach.foldl
        (fun bytes expr => bytes ++ encode expr.1) initial =
      initial ++ exprListBytes encode exprs := by
  rw [List.foldl_attach
    (f := fun bytes expr => bytes ++ encode expr)]
  induction exprs generalizing initial with
  | nil => simp [exprListBytes]
  | cons expr exprs ih =>
    simp only [List.foldl_cons]
    simpa [exprListBytes, ByteArray.append_assoc] using
      ih (initial ++ encode expr)

theorem attachFold_lamBinderListBytes (encode : Ixon.Expr → ByteArray)
    (binders : List (Ixon.Uses × Ixon.Expr)) (initial : ByteArray) :
    binders.attach.foldl
        (fun bytes binder =>
          bytes ++ [binder.1.1.toBits].toByteArray ++ encode binder.1.2)
        initial = initial ++ lamBinderListBytes encode binders := by
  change binders.attach.foldl
      (fun bytes binder =>
        (fun bytes (value : Ixon.Uses × Ixon.Expr) =>
          bytes ++ [value.1.toBits].toByteArray ++ encode value.2)
          bytes binder.1) initial = _
  rw [List.foldl_attach
    (f := fun bytes (binder : Ixon.Uses × Ixon.Expr) =>
      bytes ++ [binder.1.toBits].toByteArray ++ encode binder.2)]
  induction binders generalizing initial with
  | nil => simp [lamBinderListBytes]
  | cons binder binders ih =>
    rw [List.foldl_cons, ih]
    simp only [lamBinderListBytes]
    simp only [ByteArray.append_assoc]

theorem attachFold_allBinderListBytes (encode : Ixon.Expr → ByteArray)
    (binders : List (Ixon.Uses × Ixon.Owned × Ixon.Expr))
    (initial : ByteArray) :
    binders.attach.foldl
        (fun bytes binder =>
          bytes ++ [allBinderMode binder.1.1 binder.1.2.1].toByteArray ++
            encode binder.1.2.2) initial =
      initial ++ allBinderListBytes encode binders := by
  change binders.attach.foldl
      (fun bytes binder =>
        (fun bytes (value : Ixon.Uses × Ixon.Owned × Ixon.Expr) =>
          bytes ++ [allBinderMode value.1 value.2.1].toByteArray ++
            encode value.2.2) bytes binder.1) initial = _
  rw [List.foldl_attach
    (f := fun bytes
      (binder : Ixon.Uses × Ixon.Owned × Ixon.Expr) =>
      bytes ++ [allBinderMode binder.1 binder.2.1].toByteArray ++
        encode binder.2.2)]
  induction binders generalizing initial with
  | nil => simp [allBinderListBytes]
  | cons binder binders ih =>
    rw [List.foldl_cons, ih]
    simp only [allBinderListBytes, allBinderMode]
    simp only [ByteArray.append_assoc]

def putExprList (exprs : List Ixon.Expr) : Ixon.PutM Unit :=
  exprs.foldlM (fun _ expr => Ixon.putExpr expr) ()

def putLamBinderList (binders : List (Ixon.Uses × Ixon.Expr)) :
    Ixon.PutM Unit := do
  for binder in binders do
    Ixon.putU8 binder.1.toBits
    Ixon.putExpr binder.2

def putAllBinderList
    (binders : List (Ixon.Uses × Ixon.Owned × Ixon.Expr)) :
    Ixon.PutM Unit := do
  for binder in binders do
    Ixon.putU8 (allBinderMode binder.1 binder.2.1)
    Ixon.putExpr binder.2.2

theorem putExprList_writes (encode : Ixon.Expr → ByteArray)
    (exprs : List Ixon.Expr)
    (h : ∀ expr, expr ∈ exprs → Writes (Ixon.putExpr expr) (encode expr)) :
    Writes (putExprList exprs) (exprListBytes encode exprs) := by
  induction exprs with
  | nil =>
    intro before
    simp only [putExprList, List.foldlM_nil, exprListBytes,
      ByteArray.append_empty]
    change ((), before) = ((), before)
    rfl
  | cons expr exprs ih =>
    have hhead := h expr (by simp)
    have htail : ∀ tail, tail ∈ exprs →
        Writes (Ixon.putExpr tail) (encode tail) := by
      intro tail hmem
      exact h tail (by simp [hmem])
    simpa [putExprList, exprListBytes] using hhead.bind (ih htail)

theorem putLamBinderList_writes (encode : Ixon.Expr → ByteArray)
    (binders : List (Ixon.Uses × Ixon.Expr))
    (h : ∀ binder, binder ∈ binders →
      Writes (Ixon.putExpr binder.2) (encode binder.2)) :
    Writes (putLamBinderList binders)
      (lamBinderListBytes encode binders) := by
  induction binders with
  | nil =>
    intro before
    simp only [putLamBinderList, lamBinderListBytes,
      ByteArray.append_empty]
    change ((), before) = ((), before)
    rfl
  | cons binder binders ih =>
    have hhead := h binder (by simp)
    have htail : ∀ tail, tail ∈ binders →
        Writes (Ixon.putExpr tail.2) (encode tail.2) := by
      intro tail hmem
      exact h tail (by simp [hmem])
    rcases binder with ⟨uses, ty⟩
    simpa [putLamBinderList, lamBinderListBytes,
      ByteArray.append_assoc] using
        (putU8_writes uses.toBits).bind (hhead.bind (ih htail))

theorem putAllBinderList_writes (encode : Ixon.Expr → ByteArray)
    (binders : List (Ixon.Uses × Ixon.Owned × Ixon.Expr))
    (h : ∀ binder, binder ∈ binders →
      Writes (Ixon.putExpr binder.2.2) (encode binder.2.2)) :
    Writes (putAllBinderList binders)
      (allBinderListBytes encode binders) := by
  induction binders with
  | nil =>
    intro before
    simp only [putAllBinderList, allBinderListBytes,
      ByteArray.append_empty]
    change ((), before) = ((), before)
    rfl
  | cons binder binders ih =>
    have hhead := h binder (by simp)
    have htail : ∀ tail, tail ∈ binders →
        Writes (Ixon.putExpr tail.2.2) (encode tail.2.2) := by
      intro tail hmem
      exact h tail (by simp [hmem])
    rcases binder with ⟨uses, owned, ty⟩
    simpa [putAllBinderList, allBinderListBytes, allBinderMode,
      ByteArray.append_assoc] using
        (putU8_writes (allBinderMode uses owned)).bind
          (hhead.bind (ih htail))

theorem listFor_putExpr_eq (exprs : List Ixon.Expr) :
    (do for expr in exprs do Ixon.putExpr expr) = putExprList exprs := by
  simp [putExprList]

theorem listFor_putLamBinders_eq
    (binders : List (Ixon.Uses × Ixon.Expr)) :
    (do
      for binder in binders do
        Ixon.putU8 binder.1.toBits
        Ixon.putExpr binder.2) = putLamBinderList binders := by
  rfl

theorem listFor_putAllBinders_eq
    (binders : List (Ixon.Uses × Ixon.Owned × Ixon.Expr)) :
    (do
      for binder in binders do
        Ixon.putU8 (binder.1.toBits ||| (binder.2.1.toBits <<< 2))
        Ixon.putExpr binder.2.2) = putAllBinderList binders := by
  simp [putAllBinderList, allBinderMode]

theorem putLamBinderList_bind (binders : List (Ixon.Uses × Ixon.Expr))
    (next : Ixon.PutM α) :
    (do
      putLamBinderList binders
      next) =
    (do
      for binder in binders do
        Ixon.putU8 binder.1.toBits
        Ixon.putExpr binder.2
      next) := by
  simp [putLamBinderList]

theorem putAllBinderList_bind
    (binders : List (Ixon.Uses × Ixon.Owned × Ixon.Expr))
    (next : Ixon.PutM α) :
    (do
      putAllBinderList binders
      next) =
    (do
      for binder in binders do
        Ixon.putU8 (binder.1.toBits ||| (binder.2.1.toBits <<< 2))
        Ixon.putExpr binder.2.2
      next) := by
  simp [putAllBinderList, allBinderMode]

@[simp] theorem attachFold_exprListBytes_empty
    (encode : Ixon.Expr → ByteArray) (exprs : List Ixon.Expr) :
    exprs.attach.foldl
        (fun bytes expr => bytes ++ encode expr.1) ByteArray.empty =
      exprListBytes encode exprs := by
  simpa using attachFold_exprListBytes encode exprs ByteArray.empty

@[simp] theorem attachFold_lamBinderListBytes_empty
    (encode : Ixon.Expr → ByteArray)
    (binders : List (Ixon.Uses × Ixon.Expr)) :
    binders.attach.foldl
        (fun bytes binder =>
          bytes ++ [binder.1.1.toBits].toByteArray ++ encode binder.1.2)
        ByteArray.empty = lamBinderListBytes encode binders := by
  simpa using
    attachFold_lamBinderListBytes encode binders ByteArray.empty

@[simp] theorem attachFold_allBinderListBytes_empty
    (encode : Ixon.Expr → ByteArray)
    (binders : List (Ixon.Uses × Ixon.Owned × Ixon.Expr)) :
    binders.attach.foldl
        (fun bytes binder =>
          bytes ++ [allBinderMode binder.1.1 binder.1.2.1].toByteArray ++
            encode binder.1.2.2) ByteArray.empty =
      allBinderListBytes encode binders := by
  simpa using
    attachFold_allBinderListBytes encode binders ByteArray.empty

/-- The production writer emits the canonical whole-telescope encoding for
every expression satisfying the compiler-facing wire invariant. -/
theorem putExpr_writes_spine (expr : Ixon.Expr) (h : expr.wireWF) :
    Writes (Ixon.putExpr expr) (spineWireEncode expr) := by
  cases expr with
  | sort idx =>
    simpa [Ixon.putExpr, spineWireEncode] using
      putTag4_writes Ixon.Expr.FLAG_SORT idx
  | var idx =>
    simpa [Ixon.putExpr, spineWireEncode] using
      putTag4_writes Ixon.Expr.FLAG_VAR idx
  | ref refIdx univs =>
    have hwrite :=
      (putTag4_writes Ixon.Expr.FLAG_REF univs.size.toUInt64).bind
        ((putTag0_writes refIdx).bind (arrayPutTag0_writes univs))
    simpa [Ixon.putExpr, spineWireEncode, ByteArray.append_assoc] using hwrite
  | recur recIdx univs =>
    have hwrite :=
      (putTag4_writes Ixon.Expr.FLAG_REC univs.size.toUInt64).bind
        ((putTag0_writes recIdx).bind (arrayPutTag0_writes univs))
    simpa [Ixon.putExpr, spineWireEncode, ByteArray.append_assoc] using hwrite
  | prj typeRefIdx fieldIdx val =>
    have hval := putExpr_writes_spine val h
    have hwrite := (putTag4_writes Ixon.Expr.FLAG_PRJ fieldIdx).bind
      ((putTag0_writes typeRefIdx).bind hval)
    simpa [Ixon.putExpr, spineWireEncode, ByteArray.append_assoc] using hwrite
  | str refIdx =>
    simpa [Ixon.putExpr, spineWireEncode] using
      putTag4_writes Ixon.Expr.FLAG_STR refIdx
  | nat refIdx =>
    simpa [Ixon.putExpr, spineWireEncode] using
      putTag4_writes Ixon.Expr.FLAG_NAT refIdx
  | app fn arg =>
    let whole := Ixon.Expr.app fn arg
    have hbaseWF : whole.collectAppArgs.2.wireWF :=
      collectAppArgs_base_wireWF h
    have hbase := putExpr_writes_spine whole.collectAppArgs.2 hbaseWF
    have hargs := putExprList_writes spineWireEncode
      whole.collectAppArgs.1 (fun value hmem =>
        putExpr_writes_spine value (collectAppArgs_mem_wireWF h hmem))
    have hwrite :=
      (putTag4_writes Ixon.Expr.FLAG_APP
        whole.collectAppArgs.1.length.toUInt64).bind (hbase.bind hargs)
    simp only [Ixon.putExpr, spineWireEncode]
    rw [listFor_putExpr_eq, attachFold_exprListBytes_empty]
    simpa [ByteArray.append_assoc] using hwrite
  | lam uses ty body =>
    let whole := Ixon.Expr.lam uses ty body
    have hbaseWF : whole.collectLamBinders.2.wireWF :=
      collectLamBinders_base_wireWF h
    have hbinders := putLamBinderList_writes spineWireEncode
      whole.collectLamBinders.1 (fun binder hmem =>
        putExpr_writes_spine binder.2
          (collectLamBinders_mem_wireWF h ⟨binder.1, hmem⟩))
    have hbase := putExpr_writes_spine whole.collectLamBinders.2 hbaseWF
    have hwrite :=
      (putTag4_writes Ixon.Expr.FLAG_LAM
        whole.collectLamBinders.1.length.toUInt64).bind
          (hbinders.bind hbase)
    simp only [Ixon.putExpr, spineWireEncode]
    rw [← putLamBinderList_bind, attachFold_lamBinderListBytes_empty]
    simpa [ByteArray.append_assoc] using hwrite
  | all uses owned ty body =>
    let whole := Ixon.Expr.all uses owned ty body
    have hbaseWF : whole.collectAllBinders.2.wireWF :=
      collectAllBinders_base_wireWF h
    have hbinders := putAllBinderList_writes spineWireEncode
      whole.collectAllBinders.1 (fun binder hmem =>
        putExpr_writes_spine binder.2.2
          (collectAllBinders_mem_wireWF h
            ⟨binder.1, binder.2.1, hmem⟩))
    have hbase := putExpr_writes_spine whole.collectAllBinders.2 hbaseWF
    have hwrite :=
      (putTag4_writes Ixon.Expr.FLAG_ALL
        whole.collectAllBinders.1.length.toUInt64).bind
          (hbinders.bind hbase)
    simp only [Ixon.putExpr, spineWireEncode]
    rw [← putAllBinderList_bind]
    rw [attachFold_allBinderListBytes_empty]
    simpa [ByteArray.append_assoc] using hwrite
  | letE nonDep ty val body =>
    obtain ⟨hty, hval, hbody⟩ := h
    have hwrite :=
      (putTag4_writes Ixon.Expr.FLAG_LET (if nonDep then 1 else 0)).bind
        ((putExpr_writes_spine ty hty).bind
          ((putExpr_writes_spine val hval).bind
            (putExpr_writes_spine body hbody)))
    simpa [Ixon.putExpr, spineWireEncode, ByteArray.append_assoc] using hwrite
  | share idx =>
    simpa [Ixon.putExpr, spineWireEncode] using
      putTag4_writes Ixon.Expr.FLAG_SHARE idx
termination_by expr.nodeCount
decreasing_by
  all_goals simp_wf
  all_goals subst expr
  all_goals simp only [Ixon.Expr.nodeCount]
  all_goals try omega
  · simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAppArgs_base_nodeCount_lt fn arg
  · change value ∈ (Ixon.Expr.app fn arg).collectAppArgs.1 at hmem
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAppArgs_mem_nodeCount_lt (.app fn arg) value hmem
  · change binder ∈
      (Ixon.Expr.lam uses ty body).collectLamBinders.1 at hmem
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectLamBinders_mem_nodeCount_lt (.lam uses ty body)
        binder.2 ⟨binder.1, hmem⟩
  · simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectLamBinders_base_nodeCount_lt uses ty body
  · change binder ∈
      (Ixon.Expr.all uses owned ty body).collectAllBinders.1 at hmem
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAllBinders_mem_nodeCount_lt (.all uses owned ty body)
        binder.2.2 ⟨binder.1, binder.2.1, hmem⟩
  · simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAllBinders_base_nodeCount_lt uses owned ty body

/-! ## Telescope readers -/

theorem spineWireEncode_app (fn arg : Ixon.Expr) :
    spineWireEncode (.app fn arg) =
      tag4Bytes Ixon.Expr.FLAG_APP
          (Ixon.Expr.app fn arg).collectAppArgs.1.length.toUInt64 ++
        spineWireEncode (Ixon.Expr.app fn arg).collectAppArgs.2 ++
          exprListBytes spineWireEncode
            (Ixon.Expr.app fn arg).collectAppArgs.1 := by
  simp only [spineWireEncode]
  rw [attachFold_exprListBytes_empty]

theorem spineWireEncode_lam (uses : Ixon.Uses) (ty body : Ixon.Expr) :
    spineWireEncode (.lam uses ty body) =
      tag4Bytes Ixon.Expr.FLAG_LAM
          (Ixon.Expr.lam uses ty body).collectLamBinders.1.length.toUInt64 ++
        lamBinderListBytes spineWireEncode
            (Ixon.Expr.lam uses ty body).collectLamBinders.1 ++
          spineWireEncode
            (Ixon.Expr.lam uses ty body).collectLamBinders.2 := by
  simp only [spineWireEncode]
  rw [attachFold_lamBinderListBytes_empty]

theorem spineWireEncode_all (uses : Ixon.Uses) (owned : Ixon.Owned)
    (ty body : Ixon.Expr) :
    spineWireEncode (.all uses owned ty body) =
      tag4Bytes Ixon.Expr.FLAG_ALL
          (Ixon.Expr.all uses owned ty body).collectAllBinders.1.length.toUInt64 ++
        allBinderListBytes spineWireEncode
            (Ixon.Expr.all uses owned ty body).collectAllBinders.1 ++
          spineWireEncode
            (Ixon.Expr.all uses owned ty body).collectAllBinders.2 := by
  simp only [spineWireEncode]
  rw [attachFold_allBinderListBytes_empty]

theorem exprListBytes_member_size_le (encode : Ixon.Expr → ByteArray)
    {expr : Ixon.Expr} {exprs : List Ixon.Expr} (hmem : expr ∈ exprs) :
    (encode expr).size ≤ (exprListBytes encode exprs).size := by
  induction exprs with
  | nil => exact nomatch hmem
  | cons head tail ih =>
    simp only [List.mem_cons] at hmem
    simp only [exprListBytes, ByteArray.size_append]
    rcases hmem with rfl | htail
    · omega
    · have := ih htail
      omega

theorem lamBinderListBytes_member_size_le
    (encode : Ixon.Expr → ByteArray)
    {binder : Ixon.Uses × Ixon.Expr}
    {binders : List (Ixon.Uses × Ixon.Expr)} (hmem : binder ∈ binders) :
    (encode binder.2).size ≤
      (lamBinderListBytes encode binders).size := by
  induction binders with
  | nil => exact nomatch hmem
  | cons head tail ih =>
    simp only [List.mem_cons] at hmem
    simp only [lamBinderListBytes, ByteArray.size_append,
      List.size_toByteArray, List.length_cons, List.length_nil]
    rcases hmem with rfl | htail
    · omega
    · have := ih htail
      omega

theorem allBinderListBytes_member_size_le
    (encode : Ixon.Expr → ByteArray)
    {binder : Ixon.Uses × Ixon.Owned × Ixon.Expr}
    {binders : List (Ixon.Uses × Ixon.Owned × Ixon.Expr)}
    (hmem : binder ∈ binders) :
    (encode binder.2.2).size ≤
      (allBinderListBytes encode binders).size := by
  induction binders with
  | nil => exact nomatch hmem
  | cons head tail ih =>
    rcases head with ⟨headUses, headRest⟩
    rcases headRest with ⟨headOwned, headTy⟩
    simp only [List.mem_cons] at hmem
    simp only [allBinderListBytes, ByteArray.size_append,
      List.size_toByteArray, List.length_cons, List.length_nil]
    rcases hmem with heq | htail
    · rw [heq]
      change (encode headTy).size ≤
        1 + (encode headTy).size + (allBinderListBytes encode tail).size
      omega
    · have := ih htail
      omega

theorem getExprAppArgs_reads (getm : Ixon.GetM Ixon.Expr)
    (encode : Ixon.Expr → ByteArray) (exprs : List Ixon.Expr)
    (base : Ixon.Expr)
    (h : ∀ expr, expr ∈ exprs → Reads getm (encode expr) expr) :
    Reads (Ixon.getExprAppArgs getm exprs.length base)
      (exprListBytes encode exprs) (exprs.foldl Ixon.Expr.app base) := by
  induction exprs generalizing base with
  | nil =>
    simpa [Ixon.getExprAppArgs, exprListBytes] using Reads.pure base
  | cons expr exprs ih =>
    have hhead := h expr (by simp)
    have htail : ∀ tail, tail ∈ exprs →
        Reads getm (encode tail) tail := by
      intro tail hmem
      exact h tail (by simp [hmem])
    have hrest := ih (.app base expr) htail
    simpa [Ixon.getExprAppArgs, exprListBytes] using hhead.bind hrest

@[simp] theorem uses_ofBits_toBits (uses : Ixon.Uses) :
    Ixon.Uses.ofBits? uses.toBits = some uses := by
  cases uses <;> rfl

theorem getExprLamBinders_reads (getm : Ixon.GetM Ixon.Expr)
    (encode : Ixon.Expr → ByteArray)
    (binders : List (Ixon.Uses × Ixon.Expr))
    (h : ∀ binder, binder ∈ binders →
      Reads getm (encode binder.2) binder.2) :
    Reads (Ixon.getExprLamBinders getm binders.length)
      (lamBinderListBytes encode binders) binders := by
  induction binders with
  | nil =>
    simpa [Ixon.getExprLamBinders, lamBinderListBytes] using
      (Reads.pure ([] : List (Ixon.Uses × Ixon.Expr)))
  | cons binder binders ih =>
    rcases binder with ⟨uses, ty⟩
    have hty := h (uses, ty) (by simp)
    have htail : ∀ tail, tail ∈ binders →
        Reads getm (encode tail.2) tail.2 := by
      intro tail hmem
      exact h tail (by simp [hmem])
    have hreturn := Reads.pure
      ((uses, ty) :: binders : List (Ixon.Uses × Ixon.Expr))
    have hafterTail := Reads.bind
      (next := fun tail : List (Ixon.Uses × Ixon.Expr) =>
        (pure ((uses, ty) :: tail) :
          Ixon.GetM (List (Ixon.Uses × Ixon.Expr))))
      (ih htail) hreturn
    have hafterTy := Reads.bind
      (next := fun decodedTy : Ixon.Expr => do
        let tail ← Ixon.getExprLamBinders getm binders.length
        return (uses, decodedTy) :: tail)
      hty hafterTail
    have hafterMode : Reads
        (do
          let some decodedUses := Ixon.Uses.ofBits? uses.toBits
            | throw s!"getExpr: invalid lambda mode {uses.toBits}"
          let decodedTy ← getm
          let tail ← Ixon.getExprLamBinders getm binders.length
          return (decodedUses, decodedTy) :: tail)
        (encode ty ++ lamBinderListBytes encode binders)
        ((uses, ty) :: binders) := by
      simpa using hafterTy
    have hall := Reads.bind
      (next := fun mode : UInt8 => do
        let some decodedUses := Ixon.Uses.ofBits? mode
          | throw s!"getExpr: invalid lambda mode {mode}"
        let decodedTy ← getm
        let tail ← Ixon.getExprLamBinders getm binders.length
        return (decodedUses, decodedTy) :: tail)
      (getU8_reads uses.toBits) hafterMode
    rw [Ixon.getExprLamBinders.eq_def, lamBinderListBytes]
    simp only [List.length_cons]
    rw [ByteArray.append_assoc]
    exact hall

theorem getExprAllBinders_reads (getm : Ixon.GetM Ixon.Expr)
    (encode : Ixon.Expr → ByteArray)
    (binders : List (Ixon.Uses × Ixon.Owned × Ixon.Expr))
    (h : ∀ binder, binder ∈ binders →
      Reads getm (encode binder.2.2) binder.2.2) :
    Reads (Ixon.getExprAllBinders getm binders.length)
      (allBinderListBytes encode binders) binders := by
  induction binders with
  | nil =>
    simpa [Ixon.getExprAllBinders, allBinderListBytes] using
      (Reads.pure
        ([] : List (Ixon.Uses × Ixon.Owned × Ixon.Expr)))
  | cons binder binders ih =>
    rcases binder with ⟨uses, owned, ty⟩
    let mode := allBinderMode uses owned
    have hfields := forallMode_fields uses owned
    obtain ⟨hmodeLe, huses, howned⟩ := hfields
    change mode ≤ 7 at hmodeLe
    change Ixon.Uses.ofBits? (mode &&& 0x03) = some uses at huses
    change Ixon.Owned.ofBits? ((mode >>> 2) &&& 0x01) = some owned at howned
    have hmodeNotGt : ¬ mode > 7 := by
      simp only [UInt8.le_iff_toNat_le] at hmodeLe
      simp only [UInt8.lt_iff_toNat_lt]
      omega
    have hty := h (uses, owned, ty) (by simp)
    have htail : ∀ tail, tail ∈ binders →
        Reads getm (encode tail.2.2) tail.2.2 := by
      intro tail hmem
      exact h tail (by simp [hmem])
    have hreturn := Reads.pure
      ((uses, owned, ty) :: binders :
        List (Ixon.Uses × Ixon.Owned × Ixon.Expr))
    have hafterTail := Reads.bind
      (next := fun tail : List (Ixon.Uses × Ixon.Owned × Ixon.Expr) =>
        (pure ((uses, owned, ty) :: tail) :
          Ixon.GetM (List (Ixon.Uses × Ixon.Owned × Ixon.Expr))))
      (ih htail) hreturn
    have hafterTy := Reads.bind
      (next := fun decodedTy : Ixon.Expr => do
        let tail ← Ixon.getExprAllBinders getm binders.length
        return (uses, owned, decodedTy) :: tail)
      hty hafterTail
    have hafterMode : Reads
        (do
          if mode > 7 then
            throw s!"getExpr: invalid forall mode {mode}"
          let some decodedUses := Ixon.Uses.ofBits? (mode &&& 0x03)
            | throw s!"getExpr: invalid forall usage mode {mode}"
          let some decodedOwned :=
              Ixon.Owned.ofBits? ((mode >>> 2) &&& 0x01)
            | throw s!"getExpr: invalid forall ownership mode {mode}"
          let decodedTy ← getm
          let tail ← Ixon.getExprAllBinders getm binders.length
          return (decodedUses, decodedOwned, decodedTy) :: tail)
        (encode ty ++ allBinderListBytes encode binders)
        ((uses, owned, ty) :: binders) := by
      simpa [hmodeNotGt, huses, howned] using hafterTy
    have hall := Reads.bind
      (next := fun decodedMode : UInt8 => do
        if decodedMode > 7 then
          throw s!"getExpr: invalid forall mode {decodedMode}"
        let some decodedUses := Ixon.Uses.ofBits? (decodedMode &&& 0x03)
          | throw s!"getExpr: invalid forall usage mode {decodedMode}"
        let some decodedOwned :=
            Ixon.Owned.ofBits? ((decodedMode >>> 2) &&& 0x01)
          | throw s!"getExpr: invalid forall ownership mode {decodedMode}"
        let decodedTy ← getm
        let tail ← Ixon.getExprAllBinders getm binders.length
        return (decodedUses, decodedOwned, decodedTy) :: tail)
      (getU8_reads mode) hafterMode
    rw [Ixon.getExprAllBinders.eq_def, allBinderListBytes]
    simp only [List.length_cons]
    change Reads _
      ([mode].toByteArray ++ encode ty ++
        allBinderListBytes encode binders) ((uses, owned, ty) :: binders)
    rw [ByteArray.append_assoc]
    exact hall

theorem natCount_decode (count : Nat) (h : count < UInt64.size) :
    count.toUInt64.toNat = count := by
  change (UInt64.ofNat count).toNat = count
  exact UInt64.toNat_ofNat_of_lt h

theorem canonicalAppContinuation_reads (getm : Ixon.GetM Ixon.Expr)
    (count : Nat) (base result : Ixon.Expr) (bytes : ByteArray)
    (hbase : notApp base)
    (hread : Reads (Ixon.getExprAppArgs getm count base) bytes result) :
    Reads
      (do
        match base with
        | .app .. => throw "getExpr: non-canonical app base"
        | _ => pure ()
        Ixon.getExprAppArgs getm count base)
      bytes result := by
  cases base <;> simp_all [notApp]

theorem canonicalLamFinish_reads
    (binders : List (Ixon.Uses × Ixon.Expr))
    (base result : Ixon.Expr) (hbase : notLam base)
    (hreconstruct : binders.foldr
      (fun binder body => .lam binder.1 binder.2 body) base = result) :
    Reads
      (do
        match base with
        | .lam .. => throw "getExpr: non-canonical lam telescope"
        | _ => pure ()
        return binders.foldr
          (fun binder body => .lam binder.1 binder.2 body) base)
      ByteArray.empty result := by
  cases base <;> simp_all [notLam] <;> apply Reads.pure

theorem canonicalAllFinish_reads
    (binders : List (Ixon.Uses × Ixon.Owned × Ixon.Expr))
    (base result : Ixon.Expr) (hbase : notAll base)
    (hreconstruct : binders.foldr
      (fun binder body => .all binder.1 binder.2.1 binder.2.2 body)
      base = result) :
    Reads
      (do
        match base with
        | .all .. => throw "getExpr: non-canonical all telescope"
        | _ => pure ()
        return binders.foldr
          (fun binder body => .all binder.1 binder.2.1 binder.2.2 body)
          base)
      ByteArray.empty result := by
  cases base <;> simp_all [notAll] <;> apply Reads.pure

/-- The fuel-bounded production reader consumes the whole-spine encoding.
The same fixed recursive fuel is shared by every child of one telescope; the
leading tag byte makes each child budget strictly smaller than its parent. -/
theorem getExprFuel_reads_spine (expr : Ixon.Expr) (h : expr.wireWF)
    (fuel : Nat) (hfuel : (spineWireEncode expr).size ≤ fuel) :
    Reads (Ixon.getExprFuel fuel) (spineWireEncode expr) expr := by
  cases fuel with
  | zero =>
    have hpos := spineWireEncode_size_pos expr
    omega
  | succ fuel =>
    cases expr with
    | sort idx =>
      have htag := getTag4_reads Ixon.Expr.FLAG_SORT idx (by decide)
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_SORT, idx⟩)
          ByteArray.empty (.sort idx) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_SORT] using
          Reads.pure (Ixon.Expr.sort idx)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, spineWireEncode] using hall
    | var idx =>
      have htag := getTag4_reads Ixon.Expr.FLAG_VAR idx (by decide)
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_VAR, idx⟩)
          ByteArray.empty (.var idx) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_VAR] using
          Reads.pure (Ixon.Expr.var idx)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, spineWireEncode] using hall
    | ref refIdx univs =>
      have hcount := natCount_decode univs.size h
      have htag := getTag4_reads Ixon.Expr.FLAG_REF univs.size.toUInt64
        (by decide)
      have hidx := getTag0_reads refIdx
      have hunivs := getTag0Sizes_reads univs.toList
      have hreturn : Reads
          (pure (Ixon.Expr.ref refIdx univs.toList.toArray) :
            Ixon.GetM Ixon.Expr)
          ByteArray.empty (.ref refIdx univs) := by
        simpa using Reads.pure (Ixon.Expr.ref refIdx univs)
      have hafterUnivs := Reads.bind
        (next := fun decoded : List UInt64 =>
          (pure (Ixon.Expr.ref refIdx decoded.toArray) :
            Ixon.GetM Ixon.Expr)) hunivs hreturn
      have htail0 := Reads.bind
        (next := fun decoded : Ixon.Tag0 => do
          let decodedUnivs ← Ixon.getTag0Sizes univs.toList.length
          return Ixon.Expr.ref decoded.size decodedUnivs.toArray)
        hidx hafterUnivs
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_REF, univs.size.toUInt64⟩)
          (tag0Bytes refIdx ++ tag0ListBytes univs.toList)
          (.ref refIdx univs) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_REF, hcount,
          ByteArray.append_assoc] using htail0
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag hparsed
      simpa [Ixon.getExprFuel, spineWireEncode,
        ByteArray.append_assoc] using hall
    | recur recIdx univs =>
      have hcount := natCount_decode univs.size h
      have htag := getTag4_reads Ixon.Expr.FLAG_REC univs.size.toUInt64
        (by decide)
      have hidx := getTag0_reads recIdx
      have hunivs := getTag0Sizes_reads univs.toList
      have hreturn : Reads
          (pure (Ixon.Expr.recur recIdx univs.toList.toArray) :
            Ixon.GetM Ixon.Expr)
          ByteArray.empty (.recur recIdx univs) := by
        simpa using Reads.pure (Ixon.Expr.recur recIdx univs)
      have hafterUnivs := Reads.bind
        (next := fun decoded : List UInt64 =>
          (pure (Ixon.Expr.recur recIdx decoded.toArray) :
            Ixon.GetM Ixon.Expr)) hunivs hreturn
      have htail0 := Reads.bind
        (next := fun decoded : Ixon.Tag0 => do
          let decodedUnivs ← Ixon.getTag0Sizes univs.toList.length
          return Ixon.Expr.recur decoded.size decodedUnivs.toArray)
        hidx hafterUnivs
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_REC, univs.size.toUInt64⟩)
          (tag0Bytes recIdx ++ tag0ListBytes univs.toList)
          (.recur recIdx univs) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_REC, hcount,
          ByteArray.append_assoc] using htail0
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag hparsed
      simpa [Ixon.getExprFuel, spineWireEncode,
        ByteArray.append_assoc] using hall
    | prj typeRefIdx fieldIdx val =>
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_PRJ fieldIdx).size +
              (tag0Bytes typeRefIdx).size + (spineWireEncode val).size ≤
            fuel + 1 := by
        simpa only [spineWireEncode, ByteArray.size_append] using hfuel
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_PRJ fieldIdx
      have hval := getExprFuel_reads_spine val h fuel (by omega)
      have htag := getTag4_reads Ixon.Expr.FLAG_PRJ fieldIdx (by decide)
      have hidx := getTag0_reads typeRefIdx
      have hreturn := Reads.pure (Ixon.Expr.prj typeRefIdx fieldIdx val)
      have hafterVal := Reads.bind
        (next := fun decodedVal : Ixon.Expr =>
          (pure (Ixon.Expr.prj typeRefIdx fieldIdx decodedVal) :
            Ixon.GetM Ixon.Expr)) hval hreturn
      have htail0 := Reads.bind
        (next := fun decodedIdx : Ixon.Tag0 => do
          let decodedVal ← Ixon.getExprFuel fuel
          return Ixon.Expr.prj decodedIdx.size fieldIdx decodedVal)
        hidx hafterVal
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_PRJ, fieldIdx⟩)
          (tag0Bytes typeRefIdx ++ spineWireEncode val)
          (.prj typeRefIdx fieldIdx val) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_PRJ,
          ByteArray.append_assoc] using htail0
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag hparsed
      simpa [Ixon.getExprFuel, spineWireEncode,
        ByteArray.append_assoc] using hall
    | str refIdx =>
      have htag := getTag4_reads Ixon.Expr.FLAG_STR refIdx (by decide)
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_STR, refIdx⟩)
          ByteArray.empty (.str refIdx) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_STR] using
          Reads.pure (Ixon.Expr.str refIdx)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, spineWireEncode] using hall
    | nat refIdx =>
      have htag := getTag4_reads Ixon.Expr.FLAG_NAT refIdx (by decide)
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_NAT, refIdx⟩)
          ByteArray.empty (.nat refIdx) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_NAT] using
          Reads.pure (Ixon.Expr.nat refIdx)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, spineWireEncode] using hall
    | app fn arg =>
      let whole := Ixon.Expr.app fn arg
      let args := whole.collectAppArgs.1
      let base := whole.collectAppArgs.2
      have hbaseWF : base.wireWF := collectAppArgs_base_wireWF h
      have hbound : args.length < UInt64.size := by
        simpa [args, whole, collectAppArgs_length,
          Ixon.Expr.appCount] using h.2.2
      have hcount := natCount_decode args.length hbound
      have hcountPos : 0 < args.length := by
        simp [args, whole, collectAppArgs_length, Ixon.Expr.appCount]
      have hcountNe : args.length.toUInt64 ≠ 0 := by
        intro heq
        have hz : args.length = 0 := by
          calc
            args.length = args.length.toUInt64.toNat := hcount.symm
            _ = (0 : UInt64).toNat := congrArg UInt64.toNat heq
            _ = 0 := rfl
        exact (Nat.ne_of_gt hcountPos) hz
      have hcountBeq : (args.length.toUInt64 == 0) = false := by
        simp [hcountNe]
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_APP args.length.toUInt64).size +
              (spineWireEncode base).size +
                (exprListBytes spineWireEncode args).size ≤ fuel + 1 := by
        simpa only [whole, args, base, spineWireEncode_app,
          ByteArray.size_append] using hfuel
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_APP
        args.length.toUInt64
      have hbaseRead := getExprFuel_reads_spine base hbaseWF fuel (by omega)
      have hargsRead := getExprAppArgs_reads (Ixon.getExprFuel fuel)
        spineWireEncode args base (fun value hmem =>
          getExprFuel_reads_spine value
            (collectAppArgs_mem_wireWF h (by simpa [args, whole] using hmem))
            fuel (by
              have hle := exprListBytes_member_size_le spineWireEncode hmem
              omega))
      have hreconstruct : args.foldl Ixon.Expr.app base = whole := by
        simpa [args, base, whole] using collectAppArgs_reconstruct whole
      rw [hreconstruct] at hargsRead
      have hafterBase : Reads
          (do
            match base with
            | .app .. => throw "getExpr: non-canonical app base"
            | _ => pure ()
            Ixon.getExprAppArgs (Ixon.getExprFuel fuel)
              args.length base)
          (exprListBytes spineWireEncode args) whole := by
        exact canonicalAppContinuation_reads
          (Ixon.getExprFuel fuel) args.length base whole
          (exprListBytes spineWireEncode args)
          (by simpa [base, whole] using collectAppArgs_base_notApp whole)
          hargsRead
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_APP, args.length.toUInt64⟩)
          (spineWireEncode base ++ exprListBytes spineWireEncode args)
          whole := by
        simp only [Ixon.getExprFromTag, Ixon.Expr.FLAG_APP, hcountBeq,
          Bool.false_eq_true, if_false]
        rw [hcount]
        exact Reads.bind
          (next := fun decodedBase : Ixon.Expr => do
            match decodedBase with
            | .app .. => throw "getExpr: non-canonical app base"
            | _ => pure ()
            Ixon.getExprAppArgs (Ixon.getExprFuel fuel)
              args.length decodedBase)
          hbaseRead hafterBase
      have htag := getTag4_reads Ixon.Expr.FLAG_APP args.length.toUInt64
        (by decide)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag hparsed
      simpa [Ixon.getExprFuel, whole, args, base, spineWireEncode_app,
        ByteArray.append_assoc] using hall
    | lam uses ty body =>
      let whole := Ixon.Expr.lam uses ty body
      let binders := whole.collectLamBinders.1
      let base := whole.collectLamBinders.2
      have hbaseWF : base.wireWF := collectLamBinders_base_wireWF h
      have hbound : binders.length < UInt64.size := by
        simpa [binders, whole, collectLamBinders_length,
          Ixon.Expr.lamCount] using h.2.2
      have hcount := natCount_decode binders.length hbound
      have hcountPos : 0 < binders.length := by
        simp [binders, whole, collectLamBinders_length, Ixon.Expr.lamCount]
      have hcountNe : binders.length.toUInt64 ≠ 0 := by
        intro heq
        have hz : binders.length = 0 := by
          calc
            binders.length = binders.length.toUInt64.toNat := hcount.symm
            _ = (0 : UInt64).toNat := congrArg UInt64.toNat heq
            _ = 0 := rfl
        exact (Nat.ne_of_gt hcountPos) hz
      have hcountBeq : (binders.length.toUInt64 == 0) = false := by
        simp [hcountNe]
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_LAM binders.length.toUInt64).size +
              (lamBinderListBytes spineWireEncode binders).size +
                (spineWireEncode base).size ≤ fuel + 1 := by
        simpa only [whole, binders, base, spineWireEncode_lam,
          ByteArray.size_append] using hfuel
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_LAM
        binders.length.toUInt64
      have hbindersRead := getExprLamBinders_reads
        (Ixon.getExprFuel fuel) spineWireEncode binders
        (fun binder hmem =>
          getExprFuel_reads_spine binder.2
            (collectLamBinders_mem_wireWF h
              ⟨binder.1, by simpa [binders, whole] using hmem⟩)
            fuel (by
              have hle := lamBinderListBytes_member_size_le
                spineWireEncode hmem
              omega))
      have hbaseRead := getExprFuel_reads_spine base hbaseWF fuel (by omega)
      have hreconstruct : binders.foldr
          (fun binder body => .lam binder.1 binder.2 body) base = whole := by
        simpa [binders, base, whole] using collectLamBinders_reconstruct whole
      have hfinish : Reads
          (do
            match base with
            | .lam .. => throw "getExpr: non-canonical lam telescope"
            | _ => pure ()
            return binders.foldr
              (fun (uses, ty) result => .lam uses ty result) base)
          ByteArray.empty whole := by
        exact canonicalLamFinish_reads binders base whole
          (by simpa [base, whole] using collectLamBinders_base_notLam whole)
          hreconstruct
      have hafterBase : Reads
          (do
            let body ← Ixon.getExprFuel fuel
            match body with
            | .lam .. => throw "getExpr: non-canonical lam telescope"
            | _ => pure ()
            return binders.foldr
              (fun (uses, ty) result => .lam uses ty result) body)
          (spineWireEncode base) whole := by
        simpa using Reads.bind
          (next := fun body : Ixon.Expr => do
            match body with
            | .lam .. => throw "getExpr: non-canonical lam telescope"
            | _ => pure ()
            return binders.foldr
              (fun (uses, ty) result => Ixon.Expr.lam uses ty result) body)
          hbaseRead hfinish
      have hparsed0 : Reads
          (do
            let decodedBinders ←
              Ixon.getExprLamBinders (Ixon.getExprFuel fuel) binders.length
            let decodedBase ← Ixon.getExprFuel fuel
            match decodedBase with
            | .lam .. => throw "getExpr: non-canonical lam telescope"
            | _ => pure ()
            return decodedBinders.foldr
              (fun (uses, ty) result => .lam uses ty result) decodedBase)
          (lamBinderListBytes spineWireEncode binders ++
            spineWireEncode base) whole := by
        exact Reads.bind
          (next := fun decodedBinders : List (Ixon.Uses × Ixon.Expr) => do
            let decodedBase ← Ixon.getExprFuel fuel
            match decodedBase with
            | .lam .. => throw "getExpr: non-canonical lam telescope"
            | _ => pure ()
            return decodedBinders.foldr
              (fun (uses, ty) result => .lam uses ty result) decodedBase)
          hbindersRead hafterBase
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_LAM, binders.length.toUInt64⟩)
          (lamBinderListBytes spineWireEncode binders ++
            spineWireEncode base) whole := by
        simp only [Ixon.getExprFromTag, Ixon.Expr.FLAG_LAM, hcountBeq,
          Bool.false_eq_true, if_false]
        rw [hcount]
        exact hparsed0
      have htag := getTag4_reads Ixon.Expr.FLAG_LAM binders.length.toUInt64
        (by decide)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag hparsed
      simpa [Ixon.getExprFuel, whole, binders, base, spineWireEncode_lam,
        ByteArray.append_assoc] using hall
    | all uses owned ty body =>
      let whole := Ixon.Expr.all uses owned ty body
      let binders := whole.collectAllBinders.1
      let base := whole.collectAllBinders.2
      have hbaseWF : base.wireWF := collectAllBinders_base_wireWF h
      have hbound : binders.length < UInt64.size := by
        simpa [binders, whole, collectAllBinders_length,
          Ixon.Expr.allCount] using h.2.2
      have hcount := natCount_decode binders.length hbound
      have hcountPos : 0 < binders.length := by
        simp [binders, whole, collectAllBinders_length, Ixon.Expr.allCount]
      have hcountNe : binders.length.toUInt64 ≠ 0 := by
        intro heq
        have hz : binders.length = 0 := by
          calc
            binders.length = binders.length.toUInt64.toNat := hcount.symm
            _ = (0 : UInt64).toNat := congrArg UInt64.toNat heq
            _ = 0 := rfl
        exact (Nat.ne_of_gt hcountPos) hz
      have hcountBeq : (binders.length.toUInt64 == 0) = false := by
        simp [hcountNe]
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_ALL binders.length.toUInt64).size +
              (allBinderListBytes spineWireEncode binders).size +
                (spineWireEncode base).size ≤ fuel + 1 := by
        simpa only [whole, binders, base, spineWireEncode_all,
          ByteArray.size_append] using hfuel
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_ALL
        binders.length.toUInt64
      have hbindersRead := getExprAllBinders_reads
        (Ixon.getExprFuel fuel) spineWireEncode binders
        (fun binder hmem =>
          getExprFuel_reads_spine binder.2.2
            (collectAllBinders_mem_wireWF h
              ⟨binder.1, binder.2.1,
                by simpa [binders, whole] using hmem⟩)
            fuel (by
              have hle := allBinderListBytes_member_size_le
                spineWireEncode hmem
              omega))
      have hbaseRead := getExprFuel_reads_spine base hbaseWF fuel (by omega)
      have hreconstruct : binders.foldr
          (fun binder body => .all binder.1 binder.2.1 binder.2.2 body)
          base = whole := by
        simpa [binders, base, whole] using collectAllBinders_reconstruct whole
      have hfinish : Reads
          (do
            match base with
            | .all .. => throw "getExpr: non-canonical all telescope"
            | _ => pure ()
            return binders.foldr
              (fun (uses, owned, ty) result =>
                .all uses owned ty result) base)
          ByteArray.empty whole := by
        exact canonicalAllFinish_reads binders base whole
          (by simpa [base, whole] using collectAllBinders_base_notAll whole)
          hreconstruct
      have hafterBase : Reads
          (do
            let body ← Ixon.getExprFuel fuel
            match body with
            | .all .. => throw "getExpr: non-canonical all telescope"
            | _ => pure ()
            return binders.foldr
              (fun (uses, owned, ty) result =>
                .all uses owned ty result) body)
          (spineWireEncode base) whole := by
        simpa using Reads.bind
          (next := fun body : Ixon.Expr => do
            match body with
            | .all .. => throw "getExpr: non-canonical all telescope"
            | _ => pure ()
            return binders.foldr
              (fun (uses, owned, ty) result =>
                Ixon.Expr.all uses owned ty result) body)
          hbaseRead hfinish
      have hparsed0 : Reads
          (do
            let decodedBinders ←
              Ixon.getExprAllBinders (Ixon.getExprFuel fuel) binders.length
            let decodedBase ← Ixon.getExprFuel fuel
            match decodedBase with
            | .all .. => throw "getExpr: non-canonical all telescope"
            | _ => pure ()
            return decodedBinders.foldr
              (fun (uses, owned, ty) result =>
                .all uses owned ty result) decodedBase)
          (allBinderListBytes spineWireEncode binders ++
            spineWireEncode base) whole := by
        exact Reads.bind
          (next := fun decodedBinders :
              List (Ixon.Uses × Ixon.Owned × Ixon.Expr) => do
            let decodedBase ← Ixon.getExprFuel fuel
            match decodedBase with
            | .all .. => throw "getExpr: non-canonical all telescope"
            | _ => pure ()
            return decodedBinders.foldr
              (fun (uses, owned, ty) result =>
                .all uses owned ty result) decodedBase)
          hbindersRead hafterBase
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_ALL, binders.length.toUInt64⟩)
          (allBinderListBytes spineWireEncode binders ++
            spineWireEncode base) whole := by
        simp only [Ixon.getExprFromTag, Ixon.Expr.FLAG_ALL, hcountBeq,
          Bool.false_eq_true, if_false]
        rw [hcount]
        exact hparsed0
      have htag := getTag4_reads Ixon.Expr.FLAG_ALL binders.length.toUInt64
        (by decide)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag hparsed
      simpa [Ixon.getExprFuel, whole, binders, base, spineWireEncode_all,
        ByteArray.append_assoc] using hall
    | letE nonDep ty val body =>
      obtain ⟨hty, hval, hbody⟩ := h
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_LET (if nonDep then 1 else 0)).size +
              (spineWireEncode ty).size + (spineWireEncode val).size +
                (spineWireEncode body).size ≤ fuel + 1 := by
        simpa only [spineWireEncode, ByteArray.size_append] using hfuel
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_LET
        (if nonDep then 1 else 0)
      have htyRead := getExprFuel_reads_spine ty hty fuel (by omega)
      have hvalRead := getExprFuel_reads_spine val hval fuel (by omega)
      have hbodyRead := getExprFuel_reads_spine body hbody fuel (by omega)
      have htag := getTag4_reads Ixon.Expr.FLAG_LET
        (if nonDep then 1 else 0) (by decide)
      have hreturn := Reads.pure (Ixon.Expr.letE nonDep ty val body)
      have hafterBody := Reads.bind
        (next := fun decodedBody : Ixon.Expr =>
          (pure (Ixon.Expr.letE nonDep ty val decodedBody) :
            Ixon.GetM Ixon.Expr)) hbodyRead hreturn
      have hafterVal := Reads.bind
        (next := fun decodedVal : Ixon.Expr => do
          let decodedBody ← Ixon.getExprFuel fuel
          return Ixon.Expr.letE nonDep ty decodedVal decodedBody)
        hvalRead hafterBody
      have hchildren := Reads.bind
        (next := fun decodedTy : Ixon.Expr => do
          let decodedVal ← Ixon.getExprFuel fuel
          let decodedBody ← Ixon.getExprFuel fuel
          return Ixon.Expr.letE nonDep decodedTy decodedVal decodedBody)
        htyRead hafterVal
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_LET, if nonDep then 1 else 0⟩)
          (spineWireEncode ty ++ spineWireEncode val ++
            spineWireEncode body) (.letE nonDep ty val body) := by
        cases nonDep <;> simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_LET,
          ByteArray.append_assoc] using hchildren
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag hparsed
      simpa [Ixon.getExprFuel, spineWireEncode,
        ByteArray.append_assoc] using hall
    | share idx =>
      have htag := getTag4_reads Ixon.Expr.FLAG_SHARE idx (by decide)
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_SHARE, idx⟩)
          ByteArray.empty (.share idx) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_SHARE] using
          Reads.pure (Ixon.Expr.share idx)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, spineWireEncode] using hall
termination_by expr.nodeCount
decreasing_by
  all_goals simp_wf
  all_goals subst expr
  all_goals try simp only [Ixon.Expr.nodeCount]
  all_goals try omega
  · simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAppArgs_base_nodeCount_lt fn arg
  · change value ∈ (Ixon.Expr.app fn arg).collectAppArgs.1 at hmem
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAppArgs_mem_nodeCount_lt (.app fn arg) value hmem
  · change binder ∈
      (Ixon.Expr.lam uses ty body).collectLamBinders.1 at hmem
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectLamBinders_mem_nodeCount_lt (.lam uses ty body)
        binder.2 ⟨binder.1, hmem⟩
  · simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectLamBinders_base_nodeCount_lt uses ty body
  · change binder ∈
      (Ixon.Expr.all uses owned ty body).collectAllBinders.1 at hmem
    simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAllBinders_mem_nodeCount_lt (.all uses owned ty body)
        binder.2.2 ⟨binder.1, binder.2.1, hmem⟩
  · simpa only [Ixon.Expr.nodeCount] using
      Ixon.Expr.collectAllBinders_base_nodeCount_lt uses owned ty body

theorem serExpr_eq_spineWireEncode (expr : Ixon.Expr) (h : expr.wireWF) :
    Ixon.serExpr expr = spineWireEncode expr := by
  exact (putExpr_writes_spine expr h).runPut

theorem getExpr_reads_spine (expr : Ixon.Expr) (h : expr.wireWF) :
    Reads Ixon.getExpr (spineWireEncode expr) expr := by
  intro before after
  unfold Ixon.getExpr
  change (EStateM.bind EStateM.get _) _ = _
  simp only [EStateM.bind, EStateM.get]
  have hfuel : (spineWireEncode expr).size ≤
      (before ++ spineWireEncode expr ++ after).size - before.size + 1 := by
    simp only [ByteArray.size_append]
    omega
  have hread := getExprFuel_reads_spine expr h _ hfuel before after
  exact hread

/-- Exact full-buffer expression round trip for every expression satisfying
the production compiler's wire-representability invariant, including
arbitrary canonical application, lambda, and forall spines. -/
theorem deExpr_serExpr (expr : Ixon.Expr) (h : expr.wireWF) :
    Ixon.deExpr (Ixon.serExpr expr) = .ok expr := by
  rw [serExpr_eq_spineWireEncode expr h]
  unfold Ixon.deExpr Ixon.runGetExact
  have hread := getExpr_reads_spine expr h ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getExpr { bytes := spineWireEncode expr } = _ at hread
  rw [hread]
  simp

end Ix.Compile.Verify.Codec.Ixon.Expr

namespace Ix.Compile.Verify

abbrev ExprWireWF : Ixon.Expr → Prop := Ixon.Expr.wireWF

theorem deExpr_serExpr (expr : Ixon.Expr) (h : ExprWireWF expr) :
    Ixon.deExpr (Ixon.serExpr expr) = .ok expr :=
  Codec.Ixon.Expr.deExpr_serExpr expr h

end Ix.Compile.Verify
