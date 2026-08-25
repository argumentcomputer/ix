import Ix.Compile.Verify.Codec

/-!
# Proof-visible v2 expression codec

This first expression slice proves the production writer/reader inverse for
all constructors with empty universe-instantiation vectors and canonical
singleton application/lambda/forall spines. Numeric fields use the complete
`Tag0`/`Tag4` laws, so they are not artificially restricted to one-byte tags.
-/

namespace Ix.Compile.Verify.Codec.Ixon.Expr

theorem byteArray_append_singleton (bytes : ByteArray) (byte : UInt8) :
    bytes ++ [byte].toByteArray = bytes.push byte := by
  exact ByteArray.append_toByteArray_singleton

def notApp : Ixon.Expr → Prop
  | .app .. => False
  | _ => True

def notLam : Ixon.Expr → Prop
  | .lam .. => False
  | _ => True

def notAll : Ixon.Expr → Prop
  | .all .. => False
  | _ => True

/-- First expression-codec domain: all constructors, empty universe-index
    vectors, and singleton canonical app/binder spines. -/
def SingleWireWF : Ixon.Expr → Prop
  | .sort _ | .var _ | .str _ | .nat _ | .share _ => True
  | .ref _ univs | .recur _ univs => univs = #[]
  | .prj _ _ val => SingleWireWF val
  | .app fn arg => SingleWireWF fn ∧ SingleWireWF arg ∧ notApp fn
  | .lam _ ty body => SingleWireWF ty ∧ SingleWireWF body ∧ notLam body
  | .all _ _ ty body => SingleWireWF ty ∧ SingleWireWF body ∧ notAll body
  | .letE _ ty val body =>
      SingleWireWF ty ∧ SingleWireWF val ∧ SingleWireWF body

theorem collectAppArgs_eq_of_notApp (e : Ixon.Expr) (h : notApp e) :
    e.collectAppArgs = ([], e) := by
  cases e <;> simp_all [notApp, Ixon.Expr.collectAppArgs]

theorem collectLamBinders_eq_of_notLam (e : Ixon.Expr) (h : notLam e) :
    e.collectLamBinders = ([], e) := by
  cases e <;> simp_all [notLam, Ixon.Expr.collectLamBinders]

theorem collectAllBinders_eq_of_notAll (e : Ixon.Expr) (h : notAll e) :
    e.collectAllBinders = ([], e) := by
  cases e <;> simp_all [notAll, Ixon.Expr.collectAllBinders]

def wireEncode : Ixon.Expr → ByteArray
  | .sort idx => tag4Bytes Ixon.Expr.FLAG_SORT idx
  | .var idx => tag4Bytes Ixon.Expr.FLAG_VAR idx
  | .ref refIdx _ =>
      tag4Bytes Ixon.Expr.FLAG_REF 0 ++ tag0Bytes refIdx
  | .recur recIdx _ =>
      tag4Bytes Ixon.Expr.FLAG_REC 0 ++ tag0Bytes recIdx
  | .prj typeRefIdx fieldIdx val =>
      tag4Bytes Ixon.Expr.FLAG_PRJ fieldIdx ++ tag0Bytes typeRefIdx ++
        wireEncode val
  | .str refIdx => tag4Bytes Ixon.Expr.FLAG_STR refIdx
  | .nat refIdx => tag4Bytes Ixon.Expr.FLAG_NAT refIdx
  | .app fn arg =>
      tag4Bytes Ixon.Expr.FLAG_APP 1 ++ wireEncode fn ++ wireEncode arg
  | .lam uses ty body =>
      tag4Bytes Ixon.Expr.FLAG_LAM 1 ++
        ([uses.toBits].toByteArray ++ (wireEncode ty ++ wireEncode body))
  | .all uses owned ty body =>
      tag4Bytes Ixon.Expr.FLAG_ALL 1 ++
        ([uses.toBits ||| (owned.toBits <<< 2)].toByteArray ++
          (wireEncode ty ++ wireEncode body))
  | .letE nonDep ty val body =>
      tag4Bytes Ixon.Expr.FLAG_LET (if nonDep then 1 else 0) ++
        wireEncode ty ++ wireEncode val ++ wireEncode body
  | .share idx => tag4Bytes Ixon.Expr.FLAG_SHARE idx

theorem tag0Bytes_size_pos (size : UInt64) : 0 < (tag0Bytes size).size := by
  unfold tag0Bytes
  split <;> simp <;> omega

theorem tag4Bytes_size_pos (flag : UInt8) (size : UInt64) :
    0 < (tag4Bytes flag size).size := by
  unfold tag4Bytes
  split <;> simp <;> omega

theorem wireEncode_size_pos (e : Ixon.Expr) : 0 < (wireEncode e).size := by
  cases e with
  | sort idx => simpa [wireEncode] using tag4Bytes_size_pos Ixon.Expr.FLAG_SORT idx
  | var idx => simpa [wireEncode] using tag4Bytes_size_pos Ixon.Expr.FLAG_VAR idx
  | ref idx univs =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_REF 0
    simp only [wireEncode, ByteArray.size_append]
    omega
  | recur idx univs =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_REC 0
    simp only [wireEncode, ByteArray.size_append]
    omega
  | prj typeIdx fieldIdx val =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_PRJ fieldIdx
    simp only [wireEncode, ByteArray.size_append]
    omega
  | str idx => simpa [wireEncode] using tag4Bytes_size_pos Ixon.Expr.FLAG_STR idx
  | nat idx => simpa [wireEncode] using tag4Bytes_size_pos Ixon.Expr.FLAG_NAT idx
  | app fn arg =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_APP 1
    simp only [wireEncode, ByteArray.size_append]
    omega
  | lam uses ty body =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_LAM 1
    simp only [wireEncode, ByteArray.size_append]
    omega
  | all uses owned ty body =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_ALL 1
    simp only [wireEncode, ByteArray.size_append]
    omega
  | letE nonDep ty val body =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_LET
      (if nonDep then 1 else 0)
    simp only [wireEncode, ByteArray.size_append]
    omega
  | share idx =>
    simpa [wireEncode] using tag4Bytes_size_pos Ixon.Expr.FLAG_SHARE idx

theorem forallMode_fields (uses : Ixon.Uses) (owned : Ixon.Owned) :
    let mode := uses.toBits ||| (owned.toBits <<< 2)
    mode ≤ 7 ∧ Ixon.Uses.ofBits? (mode &&& 0x03) = some uses ∧
      Ixon.Owned.ofBits? ((mode >>> 2) &&& 0x01) = some owned := by
  cases uses <;> cases owned <;> decide

end Ix.Compile.Verify.Codec.Ixon.Expr

namespace Ix.Compile.Verify.Codec.Ixon.Expr

theorem putExpr_writes_single (e : Ixon.Expr) (h : SingleWireWF e) :
    Writes (Ixon.putExpr e) (wireEncode e) := by
  induction e with
  | sort idx =>
    simpa [Ixon.putExpr, wireEncode] using
      putTag4_writes Ixon.Expr.FLAG_SORT idx
  | var idx =>
    simpa [Ixon.putExpr, wireEncode] using
      putTag4_writes Ixon.Expr.FLAG_VAR idx
  | ref refIdx univs =>
    simp only [SingleWireWF] at h
    subst univs
    simpa [Ixon.putExpr, wireEncode] using
      (putTag4_writes Ixon.Expr.FLAG_REF 0).bind (putTag0_writes refIdx)
  | recur recIdx univs =>
    simp only [SingleWireWF] at h
    subst univs
    simpa [Ixon.putExpr, wireEncode] using
      (putTag4_writes Ixon.Expr.FLAG_REC 0).bind (putTag0_writes recIdx)
  | prj typeRefIdx fieldIdx val ih =>
    have hwrite := (putTag4_writes Ixon.Expr.FLAG_PRJ fieldIdx).bind
      ((putTag0_writes typeRefIdx).bind (ih h))
    simpa [Ixon.putExpr, wireEncode, ByteArray.append_assoc] using hwrite
  | str refIdx =>
    simpa [Ixon.putExpr, wireEncode] using
      putTag4_writes Ixon.Expr.FLAG_STR refIdx
  | nat refIdx =>
    simpa [Ixon.putExpr, wireEncode] using
      putTag4_writes Ixon.Expr.FLAG_NAT refIdx
  | app fn arg ihFn ihArg =>
    obtain ⟨hfn, harg, hnot⟩ := h
    have hcollect := collectAppArgs_eq_of_notApp fn hnot
    have hspine : (Ixon.Expr.app fn arg).collectAppArgs = ([arg], fn) := by
      simp [Ixon.Expr.collectAppArgs, hcollect]
    have hwrite := (putTag4_writes Ixon.Expr.FLAG_APP 1).bind
      ((ihFn hfn).bind (ihArg harg))
    simpa [Ixon.putExpr, wireEncode, hspine,
      ByteArray.append_assoc] using hwrite
  | lam uses ty body ihTy ihBody =>
    obtain ⟨hty, hbody, hnot⟩ := h
    have hcollect := collectLamBinders_eq_of_notLam body hnot
    have hspine : (Ixon.Expr.lam uses ty body).collectLamBinders =
        ([(uses, ty)], body) := by
      simp [Ixon.Expr.collectLamBinders, hcollect]
    have hwrite := (putTag4_writes Ixon.Expr.FLAG_LAM 1).bind
      ((putU8_writes uses.toBits).bind ((ihTy hty).bind (ihBody hbody)))
    simpa [Ixon.putExpr, wireEncode, hspine, byteArray_append_singleton,
      ByteArray.append_assoc] using hwrite
  | all uses owned ty body ihTy ihBody =>
    obtain ⟨hty, hbody, hnot⟩ := h
    have hcollect := collectAllBinders_eq_of_notAll body hnot
    have hspine : (Ixon.Expr.all uses owned ty body).collectAllBinders =
        ([(uses, owned, ty)], body) := by
      simp [Ixon.Expr.collectAllBinders, hcollect]
    have hwrite := (putTag4_writes Ixon.Expr.FLAG_ALL 1).bind
      ((putU8_writes (uses.toBits ||| (owned.toBits <<< 2))).bind
        ((ihTy hty).bind (ihBody hbody)))
    simpa [Ixon.putExpr, wireEncode, hspine, byteArray_append_singleton,
      ByteArray.append_assoc] using hwrite
  | letE nonDep ty val body ihTy ihVal ihBody =>
    obtain ⟨hty, hval, hbody⟩ := h
    have hwrite :=
      (putTag4_writes Ixon.Expr.FLAG_LET (if nonDep then 1 else 0)).bind
        ((ihTy hty).bind ((ihVal hval).bind (ihBody hbody)))
    simpa [Ixon.putExpr, wireEncode, ByteArray.append_assoc] using hwrite
  | share idx =>
    simpa [Ixon.putExpr, wireEncode] using
      putTag4_writes Ixon.Expr.FLAG_SHARE idx

end Ix.Compile.Verify.Codec.Ixon.Expr

namespace Ix.Compile.Verify.Codec.Ixon.Expr

theorem getExprFuel_reads_single (e : Ixon.Expr) (h : SingleWireWF e)
    (fuel : Nat) (hfuel : (wireEncode e).size ≤ fuel) :
    Reads (Ixon.getExprFuel fuel) (wireEncode e) e := by
  revert h fuel
  induction e with
  | sort idx =>
    intro h fuel hfuel
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.sort idx); omega
    | succ fuel =>
      have htag := getTag4_reads Ixon.Expr.FLAG_SORT idx (by decide)
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_SORT, idx⟩)
          ByteArray.empty (.sort idx) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_SORT] using
          Reads.pure (Ixon.Expr.sort idx)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode] using hall
  | var idx =>
    intro h fuel hfuel
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.var idx); omega
    | succ fuel =>
      have htag := getTag4_reads Ixon.Expr.FLAG_VAR idx (by decide)
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_VAR, idx⟩)
          ByteArray.empty (.var idx) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_VAR] using
          Reads.pure (Ixon.Expr.var idx)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode] using hall
  | ref refIdx univs =>
    intro h fuel hfuel
    simp only [SingleWireWF] at h
    subst univs
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.ref refIdx #[]); omega
    | succ fuel =>
      have htag := getTag4_reads Ixon.Expr.FLAG_REF 0 (by decide)
      have hidx := getTag0_reads refIdx
      have hreturn := Reads.pure (Ixon.Expr.ref refIdx #[])
      have htail := Reads.bind
        (next := fun decoded : Ixon.Tag0 =>
          (pure (Ixon.Expr.ref decoded.size #[]) : Ixon.GetM Ixon.Expr))
        hidx hreturn
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_REF, 0⟩)
          (tag0Bytes refIdx) (.ref refIdx #[]) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_REF,
          Ixon.getTag0Sizes] using htail
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag hparsed
      simpa [Ixon.getExprFuel, wireEncode, ByteArray.append_assoc] using hall
  | recur recIdx univs =>
    intro h fuel hfuel
    simp only [SingleWireWF] at h
    subst univs
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.recur recIdx #[]); omega
    | succ fuel =>
      have htag := getTag4_reads Ixon.Expr.FLAG_REC 0 (by decide)
      have hidx := getTag0_reads recIdx
      have hreturn := Reads.pure (Ixon.Expr.recur recIdx #[])
      have htail := Reads.bind
        (next := fun decoded : Ixon.Tag0 =>
          (pure (Ixon.Expr.recur decoded.size #[]) : Ixon.GetM Ixon.Expr))
        hidx hreturn
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_REC, 0⟩)
          (tag0Bytes recIdx) (.recur recIdx #[]) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_REC,
          Ixon.getTag0Sizes] using htail
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag hparsed
      simpa [Ixon.getExprFuel, wireEncode, ByteArray.append_assoc] using hall
  | prj typeRefIdx fieldIdx val ih =>
    intro h fuel hfuel
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.prj typeRefIdx fieldIdx val); omega
    | succ fuel =>
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_PRJ fieldIdx).size +
              (tag0Bytes typeRefIdx).size + (wireEncode val).size ≤
            fuel + 1 := by
        simpa only [wireEncode, ByteArray.size_append] using hfuel
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_PRJ fieldIdx
      have hval := ih h fuel (by omega)
      have htag := getTag4_reads Ixon.Expr.FLAG_PRJ fieldIdx (by decide)
      have hidx := getTag0_reads typeRefIdx
      have hreturn := Reads.pure (Ixon.Expr.prj typeRefIdx fieldIdx val)
      have hafterVal := Reads.bind
        (next := fun decodedVal : Ixon.Expr =>
          (pure (Ixon.Expr.prj typeRefIdx fieldIdx decodedVal) :
            Ixon.GetM Ixon.Expr))
        hval hreturn
      have htail := Reads.bind
        (next := fun decodedIdx : Ixon.Tag0 => do
          let decodedVal ← Ixon.getExprFuel fuel
          return Ixon.Expr.prj decodedIdx.size fieldIdx decodedVal)
        hidx hafterVal
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_PRJ, fieldIdx⟩)
          (tag0Bytes typeRefIdx ++ wireEncode val)
          (.prj typeRefIdx fieldIdx val) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_PRJ,
          ByteArray.append_assoc] using htail
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag hparsed
      simpa [Ixon.getExprFuel, wireEncode, ByteArray.append_assoc] using hall
  | str refIdx =>
    intro h fuel hfuel
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.str refIdx); omega
    | succ fuel =>
      have htag := getTag4_reads Ixon.Expr.FLAG_STR refIdx (by decide)
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_STR, refIdx⟩)
          ByteArray.empty (.str refIdx) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_STR] using
          Reads.pure (Ixon.Expr.str refIdx)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode] using hall
  | nat refIdx =>
    intro h fuel hfuel
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.nat refIdx); omega
    | succ fuel =>
      have htag := getTag4_reads Ixon.Expr.FLAG_NAT refIdx (by decide)
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_NAT, refIdx⟩)
          ByteArray.empty (.nat refIdx) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_NAT] using
          Reads.pure (Ixon.Expr.nat refIdx)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode] using hall
  | app fn arg ihFn ihArg =>
    intro h fuel hfuel
    obtain ⟨hfn, harg, hnot⟩ := h
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.app fn arg); omega
    | succ fuel =>
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_APP 1).size +
              (wireEncode fn).size + (wireEncode arg).size ≤ fuel + 1 := by
        simpa only [wireEncode, ByteArray.size_append] using hfuel
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_APP 1
      have hfnRead := ihFn hfn fuel (by omega)
      have hargRead := ihArg harg fuel (by omega)
      have htag := getTag4_reads Ixon.Expr.FLAG_APP 1 (by decide)
      have hreturn := Reads.pure (Ixon.Expr.app fn arg)
      have hafterArg := Reads.bind
        (next := fun decodedArg : Ixon.Expr =>
          (pure (Ixon.Expr.app fn decodedArg) : Ixon.GetM Ixon.Expr))
        hargRead hreturn
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_APP, 1⟩)
          (wireEncode fn ++ wireEncode arg) (.app fn arg) := by
        change Reads
          (do
            let base ← Ixon.getExprFuel fuel
            match base with
            | .app .. => throw "getExpr: non-canonical app base"
            | _ => pure ()
            Ixon.getExprAppArgs (Ixon.getExprFuel fuel) 1 base)
          (wireEncode fn ++ wireEncode arg) (.app fn arg)
        apply Reads.bind hfnRead
        cases fn <;> simp_all [notApp, Ixon.getExprAppArgs] <;>
          simpa [Ixon.getExprAppArgs] using hafterArg
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode, ByteArray.append_assoc] using hall
  | lam uses ty body ihTy ihBody =>
    intro h fuel hfuel
    obtain ⟨hty, hbody, hnot⟩ := h
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.lam uses ty body); omega
    | succ fuel =>
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_LAM 1).size + 1 +
              (wireEncode ty).size + (wireEncode body).size ≤ fuel + 1 := by
        simp only [wireEncode, ByteArray.size_append,
          List.size_toByteArray, List.length_cons, List.length_nil] at hfuel
        omega
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_LAM 1
      have htyRead := ihTy hty fuel (by omega)
      have hbodyRead := ihBody hbody fuel (by omega)
      have htag := getTag4_reads Ixon.Expr.FLAG_LAM 1 (by decide)
      have hmode := getU8_reads uses.toBits
      have hempty : Reads
          (Ixon.getExprLamBinders (Ixon.getExprFuel fuel) 0)
          ByteArray.empty [] := by
        simpa [Ixon.getExprLamBinders] using
          (Reads.pure ([] : List (Ixon.Uses × Ixon.Expr)))
      have hlistReturn :=
        Reads.pure ([(uses, ty)] : List (Ixon.Uses × Ixon.Expr))
      have hafterEmpty := Reads.bind
        (next := fun tail : List (Ixon.Uses × Ixon.Expr) =>
          (pure ((uses, ty) :: tail) :
            Ixon.GetM (List (Ixon.Uses × Ixon.Expr))))
        hempty hlistReturn
      have hafterTy := Reads.bind
        (next := fun decodedTy : Ixon.Expr => do
          let tail ← Ixon.getExprLamBinders (Ixon.getExprFuel fuel) 0
          return (uses, decodedTy) :: tail)
        htyRead hafterEmpty
      have hbinders : Reads
          (Ixon.getExprLamBinders (Ixon.getExprFuel fuel) 1)
          ([uses.toBits].toByteArray ++ wireEncode ty) [(uses, ty)] := by
        rw [Ixon.getExprLamBinders]
        apply Reads.bind hmode
        simpa using hafterTy
      have hfinish : Reads
          (do
            match body with
            | .lam .. => throw "getExpr: non-canonical lam telescope"
            | _ => pure ()
            return [(uses, ty)].foldr
              (fun (u, t) result => Ixon.Expr.lam u t result) body)
          ByteArray.empty (.lam uses ty body) := by
        cases body <;> simp_all [notLam] <;> apply Reads.pure
      have hbodyParsed := Reads.bind
        (next := fun decodedBody : Ixon.Expr => do
          match decodedBody with
          | .lam .. => throw "getExpr: non-canonical lam telescope"
          | _ => pure ()
          return [(uses, ty)].foldr
            (fun (u, t) result => Ixon.Expr.lam u t result) decodedBody)
        hbodyRead hfinish
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_LAM, 1⟩)
          ([uses.toBits].toByteArray ++ wireEncode ty ++ wireEncode body)
          (.lam uses ty body) := by
        change Reads
          (do
            let binders ← Ixon.getExprLamBinders
              (Ixon.getExprFuel fuel) 1
            let decodedBody ← Ixon.getExprFuel fuel
            match decodedBody with
            | .lam .. => throw "getExpr: non-canonical lam telescope"
            | _ => pure ()
            return binders.foldr
              (fun (u, t) result => Ixon.Expr.lam u t result) decodedBody)
          ([uses.toBits].toByteArray ++ wireEncode ty ++ wireEncode body)
          (.lam uses ty body)
        apply Reads.bind hbinders
        simpa using hbodyParsed
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode, ByteArray.append_assoc] using hall
  | all uses owned ty body ihTy ihBody =>
    intro h fuel hfuel
    obtain ⟨hty, hbody, hnot⟩ := h
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.all uses owned ty body); omega
    | succ fuel =>
      let mode := uses.toBits ||| (owned.toBits <<< 2)
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_ALL 1).size + 1 +
              (wireEncode ty).size + (wireEncode body).size ≤ fuel + 1 := by
        simp only [wireEncode, ByteArray.size_append,
          List.size_toByteArray, List.length_cons, List.length_nil] at hfuel
        omega
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_ALL 1
      have htyRead := ihTy hty fuel (by omega)
      have hbodyRead := ihBody hbody fuel (by omega)
      have htag := getTag4_reads Ixon.Expr.FLAG_ALL 1 (by decide)
      have hmode := getU8_reads mode
      have hfields := forallMode_fields uses owned
      obtain ⟨hmodeLe, huses, howned⟩ := hfields
      change mode ≤ 7 at hmodeLe
      change Ixon.Uses.ofBits? (mode &&& 0x03) = some uses at huses
      change Ixon.Owned.ofBits? ((mode >>> 2) &&& 0x01) = some owned at howned
      have hmodeNotGt : ¬ mode > 7 := by
        simp only [UInt8.le_iff_toNat_le] at hmodeLe
        simp only [UInt8.lt_iff_toNat_lt]
        omega
      have hempty : Reads
          (Ixon.getExprAllBinders (Ixon.getExprFuel fuel) 0)
          ByteArray.empty [] := by
        simpa [Ixon.getExprAllBinders] using
          (Reads.pure ([] : List (Ixon.Uses × Ixon.Owned × Ixon.Expr)))
      have hlistReturn := Reads.pure
        ([(uses, owned, ty)] : List (Ixon.Uses × Ixon.Owned × Ixon.Expr))
      have hafterEmpty := Reads.bind
        (next := fun tail : List (Ixon.Uses × Ixon.Owned × Ixon.Expr) =>
          (pure ((uses, owned, ty) :: tail) :
            Ixon.GetM (List (Ixon.Uses × Ixon.Owned × Ixon.Expr))))
        hempty hlistReturn
      have hafterTy := Reads.bind
        (next := fun decodedTy : Ixon.Expr => do
          let tail ← Ixon.getExprAllBinders (Ixon.getExprFuel fuel) 0
          return (uses, owned, decodedTy) :: tail)
        htyRead hafterEmpty
      have hbinders : Reads
          (Ixon.getExprAllBinders (Ixon.getExprFuel fuel) 1)
          ([mode].toByteArray ++ wireEncode ty) [(uses, owned, ty)] := by
        rw [Ixon.getExprAllBinders]
        apply Reads.bind hmode
        simp only [if_neg hmodeNotGt, huses, howned]
        simpa using hafterTy
      have hfinish : Reads
          (do
            match body with
            | .all .. => throw "getExpr: non-canonical all telescope"
            | _ => pure ()
            return [(uses, owned, ty)].foldr
              (fun (u, o, t) result => Ixon.Expr.all u o t result) body)
          ByteArray.empty (.all uses owned ty body) := by
        cases body <;> simp_all [notAll] <;> apply Reads.pure
      have hbodyParsed := Reads.bind
        (next := fun decodedBody : Ixon.Expr => do
          match decodedBody with
          | .all .. => throw "getExpr: non-canonical all telescope"
          | _ => pure ()
          return [(uses, owned, ty)].foldr
            (fun (u, o, t) result => Ixon.Expr.all u o t result) decodedBody)
        hbodyRead hfinish
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_ALL, 1⟩)
          ([mode].toByteArray ++ wireEncode ty ++ wireEncode body)
          (.all uses owned ty body) := by
        change Reads
          (do
            let binders ← Ixon.getExprAllBinders
              (Ixon.getExprFuel fuel) 1
            let decodedBody ← Ixon.getExprFuel fuel
            match decodedBody with
            | .all .. => throw "getExpr: non-canonical all telescope"
            | _ => pure ()
            return binders.foldr
              (fun (u, o, t) result => Ixon.Expr.all u o t result)
              decodedBody)
          ([mode].toByteArray ++ wireEncode ty ++ wireEncode body)
          (.all uses owned ty body)
        apply Reads.bind hbinders
        simpa using hbodyParsed
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode, mode,
        ByteArray.append_assoc] using hall
  | letE nonDep ty val body ihTy ihVal ihBody =>
    intro h fuel hfuel
    obtain ⟨hty, hval, hbody⟩ := h
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.letE nonDep ty val body); omega
    | succ fuel =>
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_LET (if nonDep then 1 else 0)).size +
              (wireEncode ty).size + (wireEncode val).size +
                (wireEncode body).size ≤ fuel + 1 := by
        simpa only [wireEncode, ByteArray.size_append] using hfuel
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_LET
        (if nonDep then 1 else 0)
      have htyRead := ihTy hty fuel (by omega)
      have hvalRead := ihVal hval fuel (by omega)
      have hbodyRead := ihBody hbody fuel (by omega)
      have htag := getTag4_reads Ixon.Expr.FLAG_LET
        (if nonDep then 1 else 0) (by decide)
      have hreturn := Reads.pure (Ixon.Expr.letE nonDep ty val body)
      have hafterBody := Reads.bind
        (next := fun decodedBody : Ixon.Expr =>
          (pure (Ixon.Expr.letE nonDep ty val decodedBody) :
            Ixon.GetM Ixon.Expr))
        hbodyRead hreturn
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
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_LET, if nonDep then 1 else 0⟩)
          (wireEncode ty ++ wireEncode val ++ wireEncode body)
          (.letE nonDep ty val body) := by
        cases nonDep <;> simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_LET,
          ByteArray.append_assoc] using hchildren
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode, ByteArray.append_assoc] using hall
  | share idx =>
    intro h fuel hfuel
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.share idx); omega
    | succ fuel =>
      have htag := getTag4_reads Ixon.Expr.FLAG_SHARE idx (by decide)
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_SHARE, idx⟩)
          ByteArray.empty (.share idx) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_SHARE] using
          Reads.pure (Ixon.Expr.share idx)
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode] using hall

theorem serExpr_eq_wireEncode_single (e : Ixon.Expr) (h : SingleWireWF e) :
    Ixon.serExpr e = wireEncode e := by
  exact (putExpr_writes_single e h).runPut

theorem getExpr_reads_single (e : Ixon.Expr) (h : SingleWireWF e) :
    Reads Ixon.getExpr (wireEncode e) e := by
  intro before after
  unfold Ixon.getExpr
  change (EStateM.bind EStateM.get _) _ = _
  simp only [EStateM.bind, EStateM.get]
  have hfuel : (wireEncode e).size ≤
      (before ++ wireEncode e ++ after).size - before.size + 1 := by
    simp only [ByteArray.size_append]
    omega
  have hread := getExprFuel_reads_single e h _ hfuel before after
  exact hread

/-- Exact full-buffer expression round trip for the first canonical
    singleton-spine domain. -/
theorem deExpr_serExpr_single (e : Ixon.Expr) (h : SingleWireWF e) :
    Ixon.deExpr (Ixon.serExpr e) = .ok e := by
  rw [serExpr_eq_wireEncode_single e h]
  unfold Ixon.deExpr Ixon.runGetExact
  have hread := getExpr_reads_single e h ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getExpr { bytes := wireEncode e } = _ at hread
  rw [hread]
  simp

end Ix.Compile.Verify.Codec.Ixon.Expr

namespace Ix.Compile.Verify

abbrev ExprSingleWireWF : Ixon.Expr → Prop :=
  Codec.Ixon.Expr.SingleWireWF

theorem deExpr_serExpr_single (e : Ixon.Expr) (h : ExprSingleWireWF e) :
    Ixon.deExpr (Ixon.serExpr e) = .ok e :=
  Codec.Ixon.Expr.deExpr_serExpr_single e h

theorem sortExpr_singleWireWF (univIdx : UInt64) :
    ExprSingleWireWF (.sort univIdx) := by
  trivial

theorem idAType_singleWireWF (aRef : UInt64) :
    ExprSingleWireWF
      (.all .many .shared (.ref aRef #[]) (.ref aRef #[])) := by
  simp [ExprSingleWireWF, Codec.Ixon.Expr.SingleWireWF,
    Codec.Ixon.Expr.notAll]

theorem idAValue_singleWireWF (aRef : UInt64) :
    ExprSingleWireWF (.lam .many (.ref aRef #[]) (.var 0)) := by
  simp [ExprSingleWireWF, Codec.Ixon.Expr.SingleWireWF,
    Codec.Ixon.Expr.notLam]

end Ix.Compile.Verify
