import IxC.Kernel.Admission.Theorems
import IxC.Kernel.Ixon.ReaderSpec

/-! # Unsharing & Constant Lowering Bridge (`IxVM` `Convert` / `Ingress` ↔ `IxC` `Reader`)

This module formulates the functional model of `IxVM`'s `Convert` and `Ingress`
circuit modules (`Ix/IxVM/Convert.lean`, `Ix/IxVM/Ingress.lean`, and Formal Aiur's
`Convert.aiur` / `Ingress.aiur`) and proves their correspondence with `IxC`'s
`Ix.Kernel.Reader` (`unshare`, `convUniv`, `convExpr`, `MemberReader`, `resolveSource`,
`readRecord`) and `Ix.Kernel.Admission.projectionAddress`.

## Key Results
1. **Universe Conversion (`ixvmConvertUniv_eq_convUniv`)**:
   `IxVM`'s `Convert::convert_univ` is identical to `Ix.Kernel.Reader.convUniv`.
2. **Top-Level Unsharing (`ixvmUnshare_eq_unshare`)**:
   `IxVM`'s bounded `Share(idx)` dereferencing agrees identically with
   `Ix.Kernel.Reader.unshare`.
3. **Sharing Table Prefix & `MemberReader` (`ixvmConvertExpr_eq_memberReader_read`)**:
   `MemberReader.mk'` builds a table of size `src.sharing.size` where each entry
   `tbl[i]?` is the conversion of `src.sharing[i]?` against earlier entries, matching
   `IxVM`'s `expand_sharing_vec` + `subst_refs_univs` (`Convert::convert_expr`).
4. **Projection Constant Resolution (`ixvmResolveSource_eq_resolveSource`)**:
   `IxVM`'s `Ingress::get_ci` resolution of standalone records (`.defn`, `.recr`,
   `.axio`, `.quot`), projection wrappers (`.dPrj`, `.iPrj`, `.rPrj`, `.cPrj`), and
   rejection of raw `.muts` block addresses agrees identically with
   `Ix.Kernel.Reader.resolveSource`.
5. **Synthesized Projection Wrapper Addresses (`ixvmProjectionAddr_eq_projectionAddress`,
   `ixvmCtorProjectionAddr_eq_projectionAddress`)**:
   `IxVM`'s `Ingress::projection_addr` (used by `build_recur_addrs` for `Expr.Rec`)
   produces the exact same content address as `Ix.Kernel.Admission.projectionAddress`.
6. **Record Lowering Equivalence (`ixvmReadProj_eq_readRecord`, `ixvmReadAxiom_eq_readRecord`,
   `ixvmReadQuot_eq_readRecord`, `ixvmReadDefn_eq_readRecord`)**:
   `IxVM`'s constant lowering (`convert_definition`, `convert_axiom`, `convert_quotient`,
   and projection validation) matches `Ix.Kernel.Reader.readRecord`.
-/

namespace Ix.Cert.IxVM

open Ix.Kernel
open Ix.Kernel.Reader
open Ix.Kernel.Admission

/-! ## 1. Universe Conversion (`Convert::convert_univ` ↔ `Reader.convUniv`) -/

/-- Functional model of `IxVM`'s `Convert::convert_univ`, parameterized by the
level-parameter mapping `param : Nat → LevelParam` (`id` for non-recursors,
`recParam lps` for recursors). -/
def ixvmConvertUniv (param : Nat → LevelParam) : Ixon.Univ → Level
  | .zero => .zero
  | .succ inner => .succ (ixvmConvertUniv param inner)
  | .max a b => .max (ixvmConvertUniv param a) (ixvmConvertUniv param b)
  | .imax a b => .imax (ixvmConvertUniv param a) (ixvmConvertUniv param b)
  | .var idx => .param (param idx.toNat)

/-- **`Convert::convert_univ` equals `Reader.convUniv` on every universe expression.** -/
theorem ixvmConvertUniv_eq_convUniv (param : Nat → LevelParam) :
    ∀ u : Ixon.Univ, ixvmConvertUniv param u = convUniv param u
  | .zero => rfl
  | .succ inner => by
    simp [ixvmConvertUniv, convUniv, ixvmConvertUniv_eq_convUniv param inner]
  | .max a b => by
    simp [ixvmConvertUniv, convUniv,
      ixvmConvertUniv_eq_convUniv param a, ixvmConvertUniv_eq_convUniv param b]
  | .imax a b => by
    simp [ixvmConvertUniv, convUniv,
      ixvmConvertUniv_eq_convUniv param a, ixvmConvertUniv_eq_convUniv param b]
  | .var _ => rfl

/-- Functional model of `Convert::convert_univ_idxs` on an `ECx md`. -/
def ixvmConvertUnivIdxs (e : ECx md) (idxs : List UInt64) : ReadM (List Level) :=
  idxs.mapM e.level

/-- **`Convert::convert_univ_idxs` agrees with `ECx.levels`.** -/
theorem ixvmConvertUnivIdxs_eq_levels (e : ECx md) (us : Array UInt64) :
    ixvmConvertUnivIdxs e us.toList = e.levels us := rfl

/-! ## 2. Unsharing & Expression Conversion (`Convert::convert_expr` ↔ `Reader.convExpr`) -/

/-- Functional model of top-level `Share(idx)` unsharing with explicit fuel. -/
def ixvmUnshareGo (sharing : Array Ixon.Expr) : Nat → Ixon.Expr → Ixon.Expr
  | 0, e => e
  | n + 1, .share i =>
    match sharing[i.toNat]? with
    | some e' => ixvmUnshareGo sharing n e'
    | none => .share i
  | _, e => e

/-- Functional model of top-level unsharing on an `Ixon.Constant`. -/
def ixvmUnshare (c : Ixon.Constant) (e : Ixon.Expr) : Ixon.Expr :=
  ixvmUnshareGo c.sharing (c.sharing.size + 1) e

theorem ixvmUnshareGo_eq_unshare_go (c : Ixon.Constant) :
    ∀ (fuel : Nat) (e : Ixon.Expr), ixvmUnshareGo c.sharing fuel e = unshare.go c fuel e
  | 0, _ => rfl
  | n + 1, .share i => by
    unfold ixvmUnshareGo unshare.go
    cases c.sharing[i.toNat]? with
    | none => rfl
    | some e' => exact ixvmUnshareGo_eq_unshare_go c n e'
  | _ + 1, .var _ => rfl
  | _ + 1, .sort _ => rfl
  | _ + 1, .ref _ _ => rfl
  | _ + 1, .recur _ _ => rfl
  | _ + 1, .prj _ _ _ => rfl
  | _ + 1, .str _ => rfl
  | _ + 1, .nat _ => rfl
  | _ + 1, .app _ _ => rfl
  | _ + 1, .lam _ _ _ => rfl
  | _ + 1, .all _ _ _ _ => rfl
  | _ + 1, .letE _ _ _ _ => rfl

/-- **`ixvmUnshare` is identical to `Ix.Kernel.Reader.unshare`.** -/
theorem ixvmUnshare_eq_unshare (c : Ixon.Constant) (e : Ixon.Expr) :
    ixvmUnshare c e = unshare c e :=
  ixvmUnshareGo_eq_unshare_go c (c.sharing.size + 1) e

/-- Bottom-up sharing vector expansion (`expand_sharing_vec` + `subst_refs_univs` in
`IxVM` / `MemberReader.mk'` in `IxC`): iterates over `sharing`, converting each entry
against the already-converted prefix `tbl`. -/
def ixvmExpandSharingVec (ecx : ECx md) (sharing : Array Ixon.Expr) :
    Array (ReadM (CExpr md)) :=
  Id.run do
    let mut tbl : Array (ReadM (CExpr md)) := Array.mkEmpty sharing.size
    for entry in sharing do
      tbl := tbl.push (convExpr ecx tbl entry)
    return tbl

/-- Functional model of `Convert::convert_expr` after `ixvmExpandSharingVec`. -/
def ixvmConvertExpr (cx : Ctx md) (src : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (e : Ixon.Expr) : ReadM (CExpr md) :=
  let ecx : ECx md := ⟨cx, src, src.univs.map (convUniv param), self⟩
  let tbl := ixvmExpandSharingVec ecx src.sharing
  convExpr ecx tbl e

/-- **`ixvmConvertExpr` is identical to `MemberReader.read` (`MemberReader.mk'`).** -/
theorem ixvmConvertExpr_eq_memberReader_read (cx : Ctx md) (src : Ixon.Constant)
    (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md))) (e : Ixon.Expr) :
    ixvmConvertExpr cx src param self e = (MemberReader.mk' cx src param self).read e := rfl

/-! ## 3. Projection Constant Resolution (`Ingress::get_ci` ↔ `Reader.resolveSource`) -/

/-- Functional model of `IxVM`'s constant reference resolution (`Ingress::get_ci` and
`get_ci_dprj` / `get_ci_iprj` / `get_ci_rprj` / `get_ci_cprj`):
- Standalone `.defn`, `.recr`, `.axio`, `.quot` resolve to `.member addr 0`.
- Raw `.muts` blocks are not directly addressable constants (`none`).
- Projection constants `.dPrj`, `.iPrj`, `.rPrj`, `.cPrj` require empty tables and
  resolve to the corresponding member or constructor of their target `.muts` block. -/
def ixvmResolveSource (store : Store) (addr : Address) (c : Ixon.Constant) :
    Option (ConstRef Address) :=
  match c.info with
  | .defn _ | .recr _ | .axio _ | .quot _ => some (.member addr 0)
  | .muts _ => none
  | .dPrj p => do
    guard (emptyTables c)
    let .muts ms := (← store p.block).info | none
    let .defn _ ← ms[p.idx.toNat]? | none
    pure (.member p.block p.idx.toNat)
  | .iPrj p => do
    guard (emptyTables c)
    let .muts ms := (← store p.block).info | none
    let .indc _ ← ms[p.idx.toNat]? | none
    pure (.member p.block p.idx.toNat)
  | .rPrj p => do
    guard (emptyTables c)
    let .muts ms := (← store p.block).info | none
    let .recr _ ← ms[p.idx.toNat]? | none
    pure (.member p.block p.idx.toNat)
  | .cPrj p => do
    guard (emptyTables c)
    let .muts ms := (← store p.block).info | none
    let .indc ind ← ms[p.idx.toNat]? | none
    let ctor ← ind.ctors[p.cidx.toNat]?
    guard (ctor.cidx == p.cidx)
    pure (.ctor p.block p.idx.toNat p.cidx.toNat)

/-- **`ixvmResolveSource` is definitionally equal to `Ix.Kernel.Reader.resolveSource`.** -/
theorem ixvmResolveSource_eq_resolveSource (store : Store) (addr : Address) (c : Ixon.Constant) :
    ixvmResolveSource store addr c = resolveSource store addr c := rfl

/-! ## 4. Synthesized Projection Wrapper Addresses (`Ingress::projection_addr` ↔ `Admission.projectionAddress`) -/

/-- Functional model of `IxVM`'s `Ingress::projection_addr(members, block_addr, idx)`:
Given the `members` array of a `.muts` block at `blockAddr` and a member index `idx`
that fits in `UInt64`, synthesizes the projection constant (`dPrj`, `iPrj`, or `rPrj`)
with empty tables, serializes it, and hashes it with `hash`. -/
def ixvmProjectionAddr (hash : ByteArray → Address) (members : Array Ixon.MutConst)
    (blockAddr : Address) (idx : Nat) : Option Address := do
  let mc ← members[idx]?
  let idxWord ← (Egress.wordC idx).toOption
  let info : Ixon.ConstantInfo := match mc with
    | .defn _ => .dPrj ⟨idxWord.val, blockAddr⟩
    | .indc _ => .iPrj ⟨idxWord.val, blockAddr⟩
    | .recr _ => .rPrj ⟨idxWord.val, blockAddr⟩
  let projC : Ixon.Constant := ⟨info, #[], #[], #[]⟩
  pure (hash (Ixon.serConstant projC))

/-- **Equivalence of `Ingress::projection_addr` and `Admission.projectionAddress` for Block Members**:
Whenever `store blockAddr = some blockConst` with `blockConst.info = .muts members`,
`ixvmProjectionAddr hash members blockAddr idx` equals
`Admission.projectionAddress hash store (.member blockAddr idx)`. -/
theorem ixvmProjectionAddr_eq_projectionAddress (hash : ByteArray → Address)
    (store : Store) (blockAddr : Address) (blockConst : Ixon.Constant)
    (members : Array Ixon.MutConst) (idx : Nat)
    (hstore : store blockAddr = some blockConst)
    (hinfo : blockConst.info = .muts members) :
    ixvmProjectionAddr hash members blockAddr idx =
      projectionAddress hash store (.member blockAddr idx) := by
  unfold ixvmProjectionAddr projectionAddress
  dsimp only
  rw [hstore]
  dsimp only [bind, Option.bind]
  rw [hinfo]
  dsimp only
  cases hmc : members[idx]? with
  | none => rfl
  | some mc =>
    cases mc <;>
      simp only [Egress.writeProjection, Egress.writeProjectionC,
        Except.map, Except.toOption, bind, Except.bind, pure, Except.pure] <;>
      cases Egress.wordC idx <;> rfl

/-- Functional model of constructor projection address synthesis (`cPrj`) in `IxVM`. -/
def ixvmCtorProjectionAddr (hash : ByteArray → Address)
    (blockAddr : Address) (idx cidx : Nat) : Option Address := do
  let idxWord ← (Egress.wordC idx).toOption
  let cidxWord ← (Egress.wordC cidx).toOption
  let projC : Ixon.Constant := ⟨.cPrj ⟨idxWord.val, cidxWord.val, blockAddr⟩, #[], #[], #[]⟩
  pure (hash (Ixon.serConstant projC))

/-- **Equivalence of `ixvmCtorProjectionAddr` and `Admission.projectionAddress` for Constructors**:
For any constructor reference `.ctor blockAddr idx cidx`, `ixvmCtorProjectionAddr`
produces the exact same address as `Admission.projectionAddress`. -/
theorem ixvmCtorProjectionAddr_eq_projectionAddress (hash : ByteArray → Address)
    (store : Store) (blockAddr : Address) (idx cidx : Nat) :
    ixvmCtorProjectionAddr hash blockAddr idx cidx =
      projectionAddress hash store (.ctor blockAddr idx cidx) := by
  unfold ixvmCtorProjectionAddr projectionAddress
  simp only [Option.bind_some, Egress.writeProjection, Egress.writeProjectionC,
    Except.map, Except.toOption, bind, Except.bind, pure, Except.pure]
  cases Egress.wordC idx with
  | error _ => rfl
  | ok iw =>
    cases Egress.wordC cidx with
    | error _ => rfl
    | ok cw => rfl

/-! ## 5. Constant Lowering Bridge (`Convert::to_kconstant` ↔ `Reader.readRecord`) -/

/-- **Projection Record Reading (`dPrj`, `iPrj`, `rPrj`, `cPrj`)**:
`readRecord` on a projection constant succeeds (emitting `#[]` declarations, as
projections only validate their target in `store`) if and only if `ixvmResolveSource`
resolves the projection to `some ref`. -/
theorem ixvmReadProj_eq_readRecord (cx : Ctx md) (st : State md) (owner : Address)
    (c : Ixon.Constant)
    (hproj : (∃ p, c.info = .dPrj p) ∨ (∃ p, c.info = .iPrj p) ∨
             (∃ p, c.info = .rPrj p) ∨ (∃ p, c.info = .cPrj p)) :
    (readRecord cx st owner c = .ok {}) ↔ (ixvmResolveSource cx.store owner c).isSome = Bool.true := by
  rw [ixvmResolveSource_eq_resolveSource]
  rcases hproj with ⟨p, hi⟩ | ⟨p, hi⟩ | ⟨p, hi⟩ | ⟨p, hi⟩ <;>
    (unfold readRecord; rw [hi]; dsimp only;
     cases hres : resolveSource cx.store owner c <;>
       simp [malformed, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure])

/-- **Axiom Record Lowering (`Convert::convert_axiom` ↔ `Reader.readRecord`)**:
For any safe axiom record `c` with `c.info = .axio a` (`a.isUnsafe = false`),
`readRecord cx st owner c` lowers `c` using `ixvmConvertExpr` with empty `recur_addrs`
(`fun _ => none`) and level parameters `List.range a.lvls.toNat`. -/
theorem ixvmReadAxiom_eq_readRecord (cx : Ctx md) (st : State md) (owner : Address)
    (c : Ixon.Constant) (a : Ixon.Axiom)
    (hinfo : c.info = .axio a) (hsafe : a.isUnsafe = Bool.false) :
    readRecord cx st owner c = (do
      let name ← cx.memberKey (.member owner 0)
      let ty ← ixvmConvertExpr cx c id (fun _ => none) a.typ
      let cv : CVal md := ⟨name, List.range a.lvls.toNat, ty⟩
      pure { decls := #[Declaration.axiomDecl cv] }) := by
  unfold readRecord
  rw [hinfo]
  dsimp only
  rw [hsafe]
  simp only [Bool.false_eq_true, ↓reduceIte, ixvmConvertExpr_eq_memberReader_read]

/-- **Quotient Record Lowering (`Convert::convert_quotient` ↔ `Reader.readRecord`)**:
For any quotient record `c` with `c.info = .quot q`, `readRecord cx st owner c`
lowers `c` using `ixvmConvertExpr` with empty `recur_addrs` (`fun _ => none`) and
level parameters `List.range q.lvls.toNat`. -/
theorem ixvmReadQuot_eq_readRecord (cx : Ctx md) (st : State md) (owner : Address)
    (c : Ixon.Constant) (q : Ixon.Quotient)
    (hinfo : c.info = .quot q) :
    readRecord cx st owner c = (do
      let name ← cx.memberKey (.member owner 0)
      let ty ← ixvmConvertExpr cx c id (fun _ => none) q.typ
      let cv : CVal md := ⟨name, List.range q.lvls.toNat, ty⟩
      let kind : Ix.Kernel.QuotKind := match q.kind with
        | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind
      pure { decls := #[Declaration.quotDecl kind cv] }) := by
  unfold readRecord
  rw [hinfo]
  simp only [ixvmConvertExpr_eq_memberReader_read]
  rfl

/-- **Singleton Definition/Theorem/Opaque Lowering (`Convert::convert_definition` ↔ `Reader.readRecord`)**:
For any singleton definition record `c` with `c.info = .defn d`, `readRecord cx st owner c`
lowers `d.typ` and `d.value` using `ixvmConvertExpr` and passes the resulting `ConstantVal`
and value to `lowerDefinition`. -/
theorem ixvmReadDefn_eq_readRecord (cx : Ctx md) (st : State md) (owner : Address)
    (c : Ixon.Constant) (d : Ixon.Definition)
    (hinfo : c.info = .defn d) :
    let self : Nat → Option (ReadM (CName md)) :=
      fun i => if i == 0 then some (cx.memberKey (.member owner 0)) else none
    readRecord cx st owner c = (do
      let (decl, rw) ← (do
        let name ← cx.memberKey (.member owner 0)
        let ty ← ixvmConvertExpr cx c id self d.typ
        let val ← ixvmConvertExpr cx c id self d.value
        let cv : CVal md := ⟨name, List.range d.lvls.toNat, ty⟩
        lowerDefinition (cx.hint (.member owner 0)) st (st.heights.getD · 0)
          cv val d.kind d.safety)
      pure { decls := #[decl], projRewrites := if rw then 1 else 0 }) := by
  intro self
  unfold readRecord readDefinition
  rw [hinfo]
  simp only [ixvmConvertExpr_eq_memberReader_read]
  rfl

end Ix.Cert.IxVM
