/-
Extracted from Ix/Compile/Verify/ExprCodec.lean at Ix revision
b067697b9d97552c6f52b2f72c892f84e4c7170f, with the Ixon v3 changes to that
file at Ix revision b413cd93a43d75a37c358491ca65cd79f1a2a42c,
and the Ixon v4 (TagN) changes to that file at Ix revision
22afee6d9245bd5f974ad59019affed034d84615.
-/

import IxC.Ixon.Verify.Basic

/-!
# Proof-visible Ixon expression codec

This expression slice proves the production writer/reader inverse for all
constructors with wire-sized universe-instantiation vectors and canonical
singleton application/lambda/forall spines. Numeric fields use the complete
TagN laws (`f = 0` and `f = 4`), so they are not artificially restricted to one-byte tags.
-/

namespace Ixon.Verify.Codec.Expr

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

/-- The array length must survive the production `Nat → UInt64 → Nat`
    wire-count conversion. -/
def IndexVectorWF (idxs : Array UInt64) : Prop :=
  idxs.size < UInt64.size

/-- Expression-codec domain: all constructors, wire-sized universe-index
    vectors, and singleton canonical app/binder spines. -/
def SingleWireWF : Ixon.Expr → Prop
  | .sort _ | .var _ | .str _ | .nat _ | .share _ => True
  | .ref _ univs | .recur _ univs => IndexVectorWF univs
  | .prj _ _ val => SingleWireWF val
  | .app fn arg => SingleWireWF fn ∧ SingleWireWF arg ∧ notApp fn
  | .lam ty body => SingleWireWF ty ∧ SingleWireWF body ∧ notLam body
  | .all ty body => SingleWireWF ty ∧ SingleWireWF body ∧ notAll body
  | .letE _ _ ty val body =>
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

/-- Concatenated TagN (`f = 0`) encodings in list order. -/
def tag0ListBytes : List UInt64 → ByteArray
  | [] => ByteArray.empty
  | idx :: idxs => tag0Bytes idx ++ tag0ListBytes idxs

def wireEncode : Ixon.Expr → ByteArray
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
        wireEncode val
  | .str refIdx => tag4Bytes Ixon.Expr.FLAG_STR refIdx
  | .nat refIdx => tag4Bytes Ixon.Expr.FLAG_NAT refIdx
  | .app fn arg =>
      tag4Bytes Ixon.Expr.FLAG_APP 1 ++ wireEncode fn ++ wireEncode arg
  | .lam ty body =>
      tag4Bytes Ixon.Expr.FLAG_LAM 1 ++ (wireEncode ty ++ wireEncode body)
  | .all ty body =>
      tag4Bytes Ixon.Expr.FLAG_ALL 1 ++ (wireEncode ty ++ wireEncode body)
  | .letE nonDep mode ty val body =>
      tag4Bytes Ixon.Expr.FLAG_LET (Ixon.LetMode.header nonDep mode) ++
        (wireEncode ty ++ (wireEncode val ++ wireEncode body))
  | .share idx => tag4Bytes Ixon.Expr.FLAG_SHARE idx

theorem tag0Bytes_size_pos (size : UInt64) : 0 < (tag0Bytes size).size := 
  tagNBytes_size_pos 0 0 size

theorem tag0ListBytes_size_ge_length (idxs : List UInt64) :
    idxs.length ≤ (tag0ListBytes idxs).size := by
  induction idxs with
  | nil => simp [tag0ListBytes]
  | cons idx idxs ih =>
    have hpos := tag0Bytes_size_pos idx
    simp only [tag0ListBytes, ByteArray.size_append, List.length_cons]
    omega

theorem tag4Bytes_size_pos (flag : UInt8) (size : UInt64) :
    0 < (tag4Bytes flag size).size := 
  tagNBytes_size_pos 4 flag size

theorem wireEncode_size_pos (e : Ixon.Expr) : 0 < (wireEncode e).size := by
  cases e with
  | sort idx => simpa [wireEncode] using tag4Bytes_size_pos Ixon.Expr.FLAG_SORT idx
  | var idx => simpa [wireEncode] using tag4Bytes_size_pos Ixon.Expr.FLAG_VAR idx
  | ref idx univs =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_REF univs.size.toUInt64
    simp only [wireEncode, ByteArray.size_append]
    omega
  | recur idx univs =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_REC univs.size.toUInt64
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
  | lam ty body =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_LAM 1
    simp only [wireEncode, ByteArray.size_append]
    omega
  | all ty body =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_ALL 1
    simp only [wireEncode, ByteArray.size_append]
    omega
  | letE nonDep mode ty val body =>
    have h := tag4Bytes_size_pos Ixon.Expr.FLAG_LET
      (Ixon.LetMode.header nonDep mode)
    simp only [wireEncode, ByteArray.size_append]
    omega
  | share idx =>
    simpa [wireEncode] using tag4Bytes_size_pos Ixon.Expr.FLAG_SHARE idx

theorem indexVectorWF_count (idxs : Array UInt64) (h : IndexVectorWF idxs) :
    idxs.size.toUInt64.toNat = idxs.size := by
  unfold IndexVectorWF at h
  change (UInt64.ofNat idxs.size).toNat = idxs.size
  exact UInt64.toNat_ofNat_of_lt h

def putTag0List (idxs : List UInt64) : Ixon.PutM Unit :=
  idxs.foldlM (fun _ idx => Ixon.putTagN 0 0 idx) ()

theorem putTag0List_writes (idxs : List UInt64) :
    Writes (putTag0List idxs) (tag0ListBytes idxs) := by
  induction idxs with
  | nil =>
    intro before
    simp only [putTag0List, List.foldlM_nil, tag0ListBytes,
      ByteArray.append_empty]
    rfl
  | cons idx idxs ih =>
    simpa only [putTag0List, List.foldlM_cons, tag0ListBytes] using
      (putTag0_writes idx).bind ih

theorem arrayPutTag0_eq_putTag0List (idxs : Array UInt64) :
    (do for idx in idxs do Ixon.putTagN 0 0 idx) =
      putTag0List idxs.toList := by
  rw [← Array.forIn_toList]
  simp [putTag0List]

theorem arrayPutTag0_writes (idxs : Array UInt64) :
    Writes (do for idx in idxs do Ixon.putTagN 0 0 idx)
      (tag0ListBytes idxs.toList) := by
  rw [arrayPutTag0_eq_putTag0List]
  exact putTag0List_writes idxs.toList

theorem getTagN0Values_reads (idxs : List UInt64) :
    Reads (Ixon.getTagN0Values idxs.length) (tag0ListBytes idxs) idxs := by
  induction idxs with
  | nil =>
    simpa [Ixon.getTagN0Values, tag0ListBytes] using
      (Reads.pure ([] : List UInt64))
  | cons idx idxs ih =>
    have hhead := getTag0_reads idx
    have hreturn := Reads.pure (idx :: idxs)
    have htail := Reads.bind
      (next := fun tail : List UInt64 =>
        (pure (idx :: tail) : Ixon.GetM (List UInt64)))
      ih hreturn
    have hall := Reads.bind
      (next := fun decoded : Ixon.TagN => do
        let tail ← Ixon.getTagN0Values idxs.length
        return decoded.value :: tail)
      hhead htail
    simpa [Ixon.getTagN0Values, tag0ListBytes] using hall

end Ixon.Verify.Codec.Expr

namespace Ixon.Verify.Codec.Expr

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
    have hwrite :=
      (putTag4_writes Ixon.Expr.FLAG_REF univs.size.toUInt64).bind
        ((putTag0_writes refIdx).bind (arrayPutTag0_writes univs))
    simpa [Ixon.putExpr, wireEncode, ByteArray.append_assoc] using hwrite
  | recur recIdx univs =>
    have hwrite :=
      (putTag4_writes Ixon.Expr.FLAG_REC univs.size.toUInt64).bind
        ((putTag0_writes recIdx).bind (arrayPutTag0_writes univs))
    simpa [Ixon.putExpr, wireEncode, ByteArray.append_assoc] using hwrite
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
  | lam ty body ihTy ihBody =>
    obtain ⟨hty, hbody, hnot⟩ := h
    have hcollect := collectLamBinders_eq_of_notLam body hnot
    have hspine : (Ixon.Expr.lam ty body).collectLamBinders = ([ty], body) := by
      simp [Ixon.Expr.collectLamBinders, hcollect]
    have hwrite := (putTag4_writes Ixon.Expr.FLAG_LAM 1).bind
      ((ihTy hty).bind (ihBody hbody))
    simpa [Ixon.putExpr, wireEncode, hspine, ByteArray.append_assoc] using hwrite
  | all ty body ihTy ihBody =>
    obtain ⟨hty, hbody, hnot⟩ := h
    have hcollect := collectAllBinders_eq_of_notAll body hnot
    have hspine : (Ixon.Expr.all ty body).collectAllBinders = ([ty], body) := by
      simp [Ixon.Expr.collectAllBinders, hcollect]
    have hwrite := (putTag4_writes Ixon.Expr.FLAG_ALL 1).bind
      ((ihTy hty).bind (ihBody hbody))
    simpa [Ixon.putExpr, wireEncode, hspine, ByteArray.append_assoc] using hwrite
  | letE nonDep mode ty val body ihTy ihVal ihBody =>
    obtain ⟨hty, hval, hbody⟩ := h
    have hwrite :=
      (putTag4_writes Ixon.Expr.FLAG_LET (Ixon.LetMode.header nonDep mode)).bind
        ((ihTy hty).bind ((ihVal hval).bind (ihBody hbody)))
    simpa [Ixon.putExpr, wireEncode, ByteArray.append_assoc] using hwrite
  | share idx =>
    simpa [Ixon.putExpr, wireEncode] using
      putTag4_writes Ixon.Expr.FLAG_SHARE idx

end Ixon.Verify.Codec.Expr

namespace Ixon.Verify.Codec.Expr

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
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.ref refIdx univs); omega
    | succ fuel =>
      have hcount := indexVectorWF_count univs h
      have htag := getTag4_reads Ixon.Expr.FLAG_REF univs.size.toUInt64
        (by decide)
      have hidx := getTag0_reads refIdx
      have hunivs := getTagN0Values_reads univs.toList
      have hreturn : Reads
          (pure (Ixon.Expr.ref refIdx univs.toList.toArray) :
            Ixon.GetM Ixon.Expr)
          ByteArray.empty (.ref refIdx univs) := by
        simpa using Reads.pure (Ixon.Expr.ref refIdx univs)
      have hafterUnivs := Reads.bind
        (next := fun decoded : List UInt64 =>
          (pure (Ixon.Expr.ref refIdx decoded.toArray) :
            Ixon.GetM Ixon.Expr))
        hunivs hreturn
      have hcheckedUnivs := Reads.checkCount univs.size.toUInt64 1
        (by simpa [hcount] using tag0ListBytes_size_ge_length univs.toList)
        hafterUnivs
      have htail := Reads.bind
        (next := fun decoded : Ixon.TagN =>
          (do
            Ixon.checkCount univs.size.toUInt64
            let decodedUnivs ← Ixon.getTagN0Values univs.toList.length
            return Ixon.Expr.ref decoded.value decodedUnivs.toArray))
        hidx hcheckedUnivs
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_REF, univs.size.toUInt64⟩)
          (tag0Bytes refIdx ++ tag0ListBytes univs.toList)
          (.ref refIdx univs) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_REF,
          hcount, ByteArray.append_assoc] using htail
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag hparsed
      simpa [Ixon.getExprFuel, wireEncode, ByteArray.append_assoc] using hall
  | recur recIdx univs =>
    intro h fuel hfuel
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.recur recIdx univs); omega
    | succ fuel =>
      have hcount := indexVectorWF_count univs h
      have htag := getTag4_reads Ixon.Expr.FLAG_REC univs.size.toUInt64
        (by decide)
      have hidx := getTag0_reads recIdx
      have hunivs := getTagN0Values_reads univs.toList
      have hreturn : Reads
          (pure (Ixon.Expr.recur recIdx univs.toList.toArray) :
            Ixon.GetM Ixon.Expr)
          ByteArray.empty (.recur recIdx univs) := by
        simpa using Reads.pure (Ixon.Expr.recur recIdx univs)
      have hafterUnivs := Reads.bind
        (next := fun decoded : List UInt64 =>
          (pure (Ixon.Expr.recur recIdx decoded.toArray) :
            Ixon.GetM Ixon.Expr))
        hunivs hreturn
      have hcheckedUnivs := Reads.checkCount univs.size.toUInt64 1
        (by simpa [hcount] using tag0ListBytes_size_ge_length univs.toList)
        hafterUnivs
      have htail := Reads.bind
        (next := fun decoded : Ixon.TagN =>
          (do
            Ixon.checkCount univs.size.toUInt64
            let decodedUnivs ← Ixon.getTagN0Values univs.toList.length
            return Ixon.Expr.recur decoded.value decodedUnivs.toArray))
        hidx hcheckedUnivs
      have hparsed : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_REC, univs.size.toUInt64⟩)
          (tag0Bytes recIdx ++ tag0ListBytes univs.toList)
          (.recur recIdx univs) := by
        simpa [Ixon.getExprFromTag, Ixon.Expr.FLAG_REC,
          hcount, ByteArray.append_assoc] using htail
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
        (next := fun decodedIdx : Ixon.TagN => do
          let decodedVal ← Ixon.getExprFuel fuel
          return Ixon.Expr.prj decodedIdx.value fieldIdx decodedVal)
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
            Ixon.checkCount 1 1
            let base ← Ixon.getExprFuel fuel
            match base with
            | .app .. => throw "getExpr: non-canonical app base"
            | _ => pure ()
            Ixon.getExprAppArgs (Ixon.getExprFuel fuel) 1 base)
          (wireEncode fn ++ wireEncode arg) (.app fn arg)
        apply Reads.checkCount 1 1
          (by
            have hpos := wireEncode_size_pos fn
            simp only [ByteArray.size_append, UInt64.reduceToNat, Nat.one_mul]
            omega)
        apply Reads.bind hfnRead
        cases fn <;> simp_all [notApp, Ixon.getExprAppArgs] <;>
          simpa [Ixon.getExprAppArgs] using hafterArg
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode, ByteArray.append_assoc] using hall
  | lam ty body ihTy ihBody =>
    intro h fuel hfuel
    obtain ⟨hty, hbody, hnot⟩ := h
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.lam ty body); omega
    | succ fuel =>
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_LAM 1).size +
              (wireEncode ty).size + (wireEncode body).size ≤ fuel + 1 := by
        simp only [wireEncode, ByteArray.size_append] at hfuel
        omega
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_LAM 1
      have htyRead := ihTy hty fuel (by omega)
      have hbodyRead := ihBody hbody fuel (by omega)
      have htag := getTag4_reads Ixon.Expr.FLAG_LAM 1 (by decide)
      have hempty : Reads
          (Ixon.getExprLamBinders (Ixon.getExprFuel fuel) 0)
          ByteArray.empty ([] : List Ixon.Expr) := by
        simpa [Ixon.getExprLamBinders] using (Reads.pure ([] : List Ixon.Expr))
      have hlistReturn := Reads.pure ([ty] : List Ixon.Expr)
      have hafterEmpty := Reads.bind
        (next := fun tail : List Ixon.Expr =>
          (pure (ty :: tail) : Ixon.GetM (List Ixon.Expr)))
        hempty hlistReturn
      have hafterTy := Reads.bind
        (next := fun decodedTy : Ixon.Expr => do
          let tail ← Ixon.getExprLamBinders (Ixon.getExprFuel fuel) 0
          return decodedTy :: tail)
        htyRead hafterEmpty
      have hbinders : Reads
          (Ixon.getExprLamBinders (Ixon.getExprFuel fuel) 1)
          (wireEncode ty) [ty] := by
        rw [Ixon.getExprLamBinders]
        simpa using hafterTy
      have hfinish : Reads
          (do
            match body with
            | .lam .. => throw "getExpr: non-canonical lam telescope"
            | _ => pure ()
            return [ty].foldr (fun t result => Ixon.Expr.lam t result) body)
          ByteArray.empty (.lam ty body) := by
        cases body <;> simp_all [notLam] <;> apply Reads.pure
      have hbodyParsed := Reads.bind
        (next := fun decodedBody : Ixon.Expr => do
          match decodedBody with
          | .lam .. => throw "getExpr: non-canonical lam telescope"
          | _ => pure ()
          return [ty].foldr (fun t result => Ixon.Expr.lam t result) decodedBody)
        hbodyRead hfinish
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_LAM, 1⟩)
          (wireEncode ty ++ wireEncode body)
          (.lam ty body) := by
        change Reads
          (do
            Ixon.checkCount 1 1
            let binders ← Ixon.getExprLamBinders
              (Ixon.getExprFuel fuel) 1
            let decodedBody ← Ixon.getExprFuel fuel
            match decodedBody with
            | .lam .. => throw "getExpr: non-canonical lam telescope"
            | _ => pure ()
            return binders.foldr
              (fun t result => Ixon.Expr.lam t result) decodedBody)
          (wireEncode ty ++ wireEncode body)
          (.lam ty body)
        apply Reads.checkCount 1 1
          (by
            have hpos := wireEncode_size_pos ty
            simp only [ByteArray.size_append, UInt64.reduceToNat, Nat.one_mul]
            omega)
        apply Reads.bind hbinders
        simpa using hbodyParsed
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode, ByteArray.append_assoc] using hall
  | all ty body ihTy ihBody =>
    intro h fuel hfuel
    obtain ⟨hty, hbody, hnot⟩ := h
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.all ty body); omega
    | succ fuel =>
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_ALL 1).size +
              (wireEncode ty).size + (wireEncode body).size ≤ fuel + 1 := by
        simp only [wireEncode, ByteArray.size_append] at hfuel
        omega
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_ALL 1
      have htyRead := ihTy hty fuel (by omega)
      have hbodyRead := ihBody hbody fuel (by omega)
      have htag := getTag4_reads Ixon.Expr.FLAG_ALL 1 (by decide)
      have hempty : Reads
          (Ixon.getExprAllBinders (Ixon.getExprFuel fuel) 0)
          ByteArray.empty ([] : List Ixon.Expr) := by
        simpa [Ixon.getExprAllBinders] using (Reads.pure ([] : List Ixon.Expr))
      have hlistReturn := Reads.pure ([ty] : List Ixon.Expr)
      have hafterEmpty := Reads.bind
        (next := fun tail : List Ixon.Expr =>
          (pure (ty :: tail) : Ixon.GetM (List Ixon.Expr)))
        hempty hlistReturn
      have hafterTy := Reads.bind
        (next := fun decodedTy : Ixon.Expr => do
          let tail ← Ixon.getExprAllBinders (Ixon.getExprFuel fuel) 0
          return decodedTy :: tail)
        htyRead hafterEmpty
      have hbinders : Reads
          (Ixon.getExprAllBinders (Ixon.getExprFuel fuel) 1)
          (wireEncode ty) [ty] := by
        rw [Ixon.getExprAllBinders]
        simpa using hafterTy
      have hfinish : Reads
          (do
            match body with
            | .all .. => throw "getExpr: non-canonical all telescope"
            | _ => pure ()
            return [ty].foldr (fun t result => Ixon.Expr.all t result) body)
          ByteArray.empty (.all ty body) := by
        cases body <;> simp_all [notAll] <;> apply Reads.pure
      have hbodyParsed := Reads.bind
        (next := fun decodedBody : Ixon.Expr => do
          match decodedBody with
          | .all .. => throw "getExpr: non-canonical all telescope"
          | _ => pure ()
          return [ty].foldr (fun t result => Ixon.Expr.all t result) decodedBody)
        hbodyRead hfinish
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_ALL, 1⟩)
          (wireEncode ty ++ wireEncode body)
          (.all ty body) := by
        change Reads
          (do
            Ixon.checkCount 1 1
            let binders ← Ixon.getExprAllBinders
              (Ixon.getExprFuel fuel) 1
            let decodedBody ← Ixon.getExprFuel fuel
            match decodedBody with
            | .all .. => throw "getExpr: non-canonical all telescope"
            | _ => pure ()
            return binders.foldr
              (fun t result => Ixon.Expr.all t result) decodedBody)
          (wireEncode ty ++ wireEncode body)
          (.all ty body)
        apply Reads.checkCount 1 1
          (by
            have hpos := wireEncode_size_pos ty
            simp only [ByteArray.size_append, UInt64.reduceToNat, Nat.one_mul]
            omega)
        apply Reads.bind hbinders
        simpa using hbodyParsed
      have hall := Reads.bind
        (next := Ixon.getExprFromTag (Ixon.getExprFuel fuel)) htag htail
      simpa [Ixon.getExprFuel, wireEncode, ByteArray.append_assoc] using hall
  | letE nonDep mode ty val body ihTy ihVal ihBody =>
    intro h fuel hfuel
    obtain ⟨hty, hval, hbody⟩ := h
    cases fuel with
    | zero => have hpos := wireEncode_size_pos (.letE nonDep mode ty val body); omega
    | succ fuel =>
      have hsizes :
          (tag4Bytes Ixon.Expr.FLAG_LET (Ixon.LetMode.header nonDep mode)).size +
              (wireEncode ty).size + (wireEncode val).size +
                (wireEncode body).size ≤ fuel + 1 := by
        simp only [wireEncode, ByteArray.size_append] at hfuel
        omega
      have htagPos := tag4Bytes_size_pos Ixon.Expr.FLAG_LET
        (Ixon.LetMode.header nonDep mode)
      have htyRead := ihTy hty fuel (by omega)
      have hvalRead := ihVal hval fuel (by omega)
      have hbodyRead := ihBody hbody fuel (by omega)
      have htag := getTag4_reads Ixon.Expr.FLAG_LET
        (Ixon.LetMode.header nonDep mode) (by decide)
      have hreturn := Reads.pure (Ixon.Expr.letE nonDep mode ty val body)
      have hafterBody := Reads.bind
        (next := fun decodedBody : Ixon.Expr =>
          (pure (Ixon.Expr.letE nonDep mode ty val decodedBody) :
            Ixon.GetM Ixon.Expr))
        hbodyRead hreturn
      have hafterVal := Reads.bind
        (next := fun decodedVal : Ixon.Expr => do
          let decodedBody ← Ixon.getExprFuel fuel
          return Ixon.Expr.letE nonDep mode ty decodedVal decodedBody)
        hvalRead hafterBody
      have hchildren := Reads.bind
        (next := fun decodedTy : Ixon.Expr => do
          let decodedVal ← Ixon.getExprFuel fuel
          let decodedBody ← Ixon.getExprFuel fuel
          return Ixon.Expr.letE nonDep mode decodedTy decodedVal decodedBody)
        htyRead hafterVal
      have htail : Reads
          (Ixon.getExprFromTag (Ixon.getExprFuel fuel)
            ⟨Ixon.Expr.FLAG_LET, Ixon.LetMode.header nonDep mode⟩)
          (wireEncode ty ++ wireEncode val ++ wireEncode body)
          (.letE nonDep mode ty val body) := by
        simp only [Ixon.getExprFromTag, Ixon.Expr.FLAG_LET, Ixon.LetMode.ofHeader?_header]
        simpa only [ByteArray.append_assoc, ByteArray.append_empty] using hchildren
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

end Ixon.Verify.Codec.Expr

namespace Ixon.Verify

abbrev ExprSingleWireWF : Ixon.Expr → Prop :=
  Codec.Expr.SingleWireWF

theorem deExpr_serExpr_single (e : Ixon.Expr) (h : ExprSingleWireWF e) :
    Ixon.deExpr (Ixon.serExpr e) = .ok e :=
  Codec.Expr.deExpr_serExpr_single e h

theorem sortExpr_singleWireWF (univIdx : UInt64) :
    ExprSingleWireWF (.sort univIdx) := by
  trivial

theorem idAType_singleWireWF (aRef : UInt64) :
    ExprSingleWireWF
      (.all (.ref aRef #[]) (.ref aRef #[])) := by
  simp [ExprSingleWireWF, Codec.Expr.SingleWireWF,
    Codec.Expr.IndexVectorWF, Codec.Expr.notAll]

theorem idAValue_singleWireWF (aRef : UInt64) :
    ExprSingleWireWF (.lam (.ref aRef #[]) (.var 0)) := by
  simp [ExprSingleWireWF, Codec.Expr.SingleWireWF,
    Codec.Expr.IndexVectorWF, Codec.Expr.notLam]

end Ixon.Verify
