import IxCC.Rt.Proof.Diagram
import IxCC.Cfg.Proof.Fuel

/-!
# DR4 String Hoisting & `strLitProc` Simulation (`Rt.Proof.StrHoist`)

Proves end-to-end simulation for `Rt.lower` on `Cfg.Program`s containing string literals:

1. **`strLitProc_sim`**: calling `Rt.Rc.Array.strLitProc idx s` from any `HeapInv` memory
   either fails with `.resource .heap` or returns in 0 charges with an 8-byte-aligned non-zero
   address `w` (`ValRelStr T Pw (.lit (.str s)) w`) while preserving `HeapInv` for the exact
   same abstract heap `H` and placement `Pw`.
2. **`strDiagram_sel`**: lifts `Rt.Proof.diagram_sel` from `Cfg.step .immortal P'` to
   `strStep P P'` (which intercepts calls to `P.size + 3 + i` as zero-charge oracle string
   materializations), reusing `step_instr`, `step_call_instr`, `step_term_sel`, `step_return`,
   and `step_enter` verbatim.
3. **`hoist_forward`**: pure `Cfg`-to-`Cfg` forward diagram from `Cfg.step .immortal P` to
   `strStep P (lowerCfg P)` with exact equality on final `(RVal × Heap)` and identity clock map,
   preserving `SwitchSel` 1-to-1 (including fused Boolean switches).
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Rt.LowerStr
open IxCC.Src (NatMap)

/-! ## 1. `strLitProc` simulation -/

/-- Little-endian 64-bit stores emitted by `strLitProc` starting at word index `k`. -/
def storeWords (m : X86.Memory) (base : Word) : Nat → List Word → X86.Memory
  | _, [] => m
  | k, w :: ws => storeWords (m.write .w64 (base + UInt64.ofNat (8 * k)) w) base (k + 1) ws

@[simp] theorem storeWords_readable (m : X86.Memory) (base : Word) :
    ∀ (k : Nat) (ws : List Word), (storeWords m base k ws).readable = m.readable
  | _, [] => rfl
  | k, _ :: ws => by simp [storeWords, storeWords_readable _ base (k + 1) ws, X86.Memory.write]

@[simp] theorem storeWords_writable (m : X86.Memory) (base : Word) :
    ∀ (k : Nat) (ws : List Word), (storeWords m base k ws).writable = m.writable
  | _, [] => rfl
  | k, _ :: ws => by simp [storeWords, storeWords_writable _ base (k + 1) ws, X86.Memory.write]

theorem storeWords_keeps {m : X86.Memory} {base b v : Word} (hb : b.toNat + 8 ≤ 2 ^ 64) :
    ∀ (k : Nat) (ws : List Word), base.toNat + 8 * (k + ws.length) ≤ 2 ^ 64 →
      (b.toNat + 8 ≤ base.toNat + 8 * k ∨ base.toNat + 8 * (k + ws.length) ≤ b.toNat) →
      WordAt m b v → WordAt (storeWords m base k ws) b v
  | _, [], _, _, h => h
  | k, w :: ws, hfit, hd, h => by
    simp only [storeWords]
    apply storeWords_keeps hb (k + 1) ws (by simp at hfit ⊢; omega) (by simp at hd ⊢; omega)
    apply h.write_disjoint
    · rw [addr_toNat (by simp at hfit; omega)]; simp [X86.Width.bytes] at hfit ⊢; omega
    · exact hb
    · rw [addr_toNat (by simp at hfit; omega)]; simp [X86.Width.bytes] at hd ⊢; omega

/-- Helper: displacement word of a small non-negative `Nat`. -/
theorem dispWord_ofNat (n : Nat) (hn : n < 2 ^ 63) :
    Lir.dispWord (Int.ofNat n) = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  simp only [Lir.dispWord, UInt64.toNat_ofBitVec, BitVec.toNat_ofInt, UInt64.toNat_ofNat',
    Int.ofNat_eq_natCast]
  have h1 : (n : Int) % ((2 ^ 64 : Nat) : Int) = (n : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg n) (by omega)
  rw [h1, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]

/-- The statement sequence emitted by `strLitProc` for `ws` starting at word index `k`. -/
def strStoreStmts : Nat → List Word → List Lir.Stmt
  | _, [] => []
  | k, w :: ws =>
    Lir.Stmt.assign (3 + k) (.arg (.imm w)) ::
    Lir.Stmt.store .w64 (Rt.Rc.Procs.cellAddr 0 (8 * k)) (.v (3 + k)) ::
    strStoreStmts (k + 1) ws

theorem zipIdx_flatMap_eq_strStoreStmts :
    ∀ (k : Nat) (ws : List Word),
      (ws.zipIdx k).flatMap (fun (w, j) =>
        let reg := 3 + j
        [Lir.Stmt.assign reg (.arg (.imm w)),
         Lir.Stmt.store .w64 (Rt.Rc.Procs.cellAddr 0 (8 * j)) (.v reg)]) =
      strStoreStmts k ws
  | _, [] => rfl
  | k, w :: ws => by
    simp only [List.zipIdx_cons, List.flatMap_cons, strStoreStmts, List.cons_append, List.nil_append]
    rw [zipIdx_flatMap_eq_strStoreStmts (k + 1) ws]

theorem execList_strStoreStmts {base ctx : Word} :
    ∀ (k : Nat) (ws : List Word) (ρ : Lir.Env) (m : X86.Memory),
      ρ[0]? = some base →
      base.toNat + 8 * (k + ws.length) < 2 ^ 63 →
      8 * (k + ws.length) < 2 ^ 63 →
      (∀ addr : Nat, base.toNat + 8 * k ≤ addr → addr < base.toNat + 8 * (k + ws.length) →
        m.writable (UInt64.ofNat addr) = true) →
      ∃ ρ', Lir.execList ρ m ctx (strStoreStmts k ws) = some (ρ', storeWords m base k ws) ∧
        ρ'[0]? = some base
  | _, [], ρ, m, h0, _, _, _ => ⟨ρ, rfl, h0⟩
  | k, w :: ws, ρ, m, h0, hfit, h8, hwr => by
    have hk8 : 8 * k < 2 ^ 63 := by simp at h8; omega
    have hdisp : Lir.dispWord ((8 : Int) * (k : Int)) = UInt64.ofNat (8 * k) := by
      have hi : ((8 : Int) * (k : Int)) = Int.ofNat (8 * k) := by
        rw [Int.ofNat_eq_natCast]; omega
      rw [hi]; exact dispWord_ofNat (8 * k) hk8
    have hne : (3 + k : Nat) ≠ 0 := by omega
    have hρ1 : (ρ.insert (3 + k) w)[0]? = some base := by
      rw [Lir.env_insert_ne _ _ hne]; exact h0
    have hρ1k : (ρ.insert (3 + k) w)[3 + k]? = some w := Lir.env_insert_self _ _ _
    have haddr : Lir.Addr.eval (ρ.insert (3 + k) w) ctx (Rt.Rc.Procs.cellAddr 0 (8 * k)) =
        some (base + UInt64.ofNat (8 * k)) := by
      simp only [Lir.Addr.eval, Rt.Rc.Procs.cellAddr, hρ1, bind, Option.bind, hdisp, UInt64.add_zero]
    have hwrite : m.write? .w64 (base + UInt64.ofNat (8 * k)) w =
        .ok (m.write .w64 (base + UInt64.ofNat (8 * k)) w) := by
      apply write?_ok
      intro i hi
      simp only [X86.Width.bytes] at hi
      have heq : base + UInt64.ofNat (8 * k) + UInt64.ofNat i =
          UInt64.ofNat (base.toNat + 8 * k + i) := by
        apply UInt64.toNat_inj.mp
        rw [addr_toNat (by rw [addr_toNat (by simp at hfit; omega)]; simp at hfit; omega),
            addr_toNat (by simp at hfit; omega), UInt64.toNat_ofNat',
            Nat.mod_eq_of_lt (by simp at hfit; omega)]
      rw [heq]
      exact hwr _ (by omega) (by simp at hfit ⊢; omega)
    have hstep1 : Lir.Stmt.exec ρ m ctx (.assign (3 + k) (.arg (.imm w))) =
        some (ρ.insert (3 + k) w, m) := by
      simp [Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval]
    have hstep2 : Lir.Stmt.exec (ρ.insert (3 + k) w) m ctx
        (.store .w64 (Rt.Rc.Procs.cellAddr 0 (8 * k)) (.v (3 + k))) =
        some (ρ.insert (3 + k) w, m.write .w64 (base + UInt64.ofNat (8 * k)) w) := by
      simp only [Lir.Stmt.exec, haddr, Lir.Arg.eval, hρ1k, bind, Option.bind, hwrite]
    obtain ⟨ρ', hex, h0'⟩ := execList_strStoreStmts (k + 1) ws (ρ.insert (3 + k) w)
      (m.write .w64 (base + UInt64.ofNat (8 * k)) w) hρ1
      (by simp at hfit ⊢; omega) (by simp at h8 ⊢; omega)
      (fun addr ha1 ha2 => by
        simp only [X86.Memory.write, writeLittle_writable]
        exact hwr addr (by omega) (by simp at ha2 ⊢; omega))
    refine ⟨ρ', ?_, h0'⟩
    simp only [strStoreStmts, Lir.execList, hstep1, hstep2, storeWords]
    exact hex

/-- Storing `nBytes` static string words into `[bump, bump + nBytes)` preserves `HeapAt`
for the exact same abstract heap `H` and placement `Pw`. -/
theorem strLit_heapAt {T : Tables} {Pw : List Word} {H : Own.Heap} {ctx bump limit : Word}
    {m : X86.Memory} (h : HeapAt T Pw H ctx m bump limit) {ws : List Word} {nBytes : Nat}
    (hsz : 8 * ws.length = nBytes) (hfit : bump.toNat + nBytes ≤ limit.toNat) :
    let bump' := bump + UInt64.ofNat nBytes
    let m1 := m.write .w64 (ctx - 40) bump'
    let m2 := storeWords m1 bump 0 ws
    HeapAt T Pw H ctx m2 bump' limit := by
  intro bump' m1 m2
  have hctx := h.ctxLo
  have h40 := ctx40_toNat hctx
  have h32 := ctx32_toNat hctx
  have hstart := h.start
  have hlim := h.limitLt
  have hbump' : bump'.toNat = bump.toNat + nBytes :=
    addr_toNat (by omega)
  have halign : bump'.toNat % 8 = 0 := by
    have := h.bumpAligned
    omega
  refine {
    len := h.len
    ctxLo := hctx
    bumpWord := ?_
    bumpWritable := fun i hi => by
      simp only [m2, m1, storeWords_writable, X86.Memory.write, writeLittle_writable]
      exact h.bumpWritable i hi
    limitWord := ?_
    start := by rw [hbump']; omega
    bumpLe := by rw [hbump']; omega
    limitLt := hlim
    bumpAligned := halign
    free := fun k hk hk' => by
      simp only [m2, m1, storeWords_readable, storeWords_writable, X86.Memory.write,
        writeLittle_readable, writeLittle_writable]
      exact h.free k (by rw [hbump'] at hk; omega) hk'
    cells := ?_
    ordered := h.ordered }
  · apply storeWords_keeps (by rw [h40]; omega) 0 ws (by simp; omega) (.inl (by rw [h40]; omega))
    exact wordAt_write64 h.bumpWord.readable
  · apply storeWords_keeps (by rw [h32]; omega) 0 ws (by simp; omega) (.inl (by rw [h32]; omega))
    exact h.limitWord.write_disjoint (by rw [h40]; simp [X86.Width.bytes]; omega)
      (by rw [h32]; omega) (.inr (by rw [h40, h32]; simp [X86.Width.bytes]; omega))
  · intro ℓ hℓ
    obtain ⟨a, rc, b, hP, hH, hcell, hlo, hhi⟩ := h.cells ℓ hℓ
    refine ⟨a, rc, b, hP, hH, ?_, hlo, by rw [hbump']; omega⟩
    have ha_hi : a.toNat + cellSize b.fields.length ≤ bump.toNat := hhi
    have hcell_sz : cellSize b.fields.length = 8 + 8 * b.fields.length := by
      simp [cellSize]; omega
    refine {
      ctor := hcell.ctor
      fieldless := hcell.fieldless
      arity := hcell.arity
      small := hcell.small
      aligned := hcell.aligned
      header := ?_
      fields := ?_ }
    · apply storeWords_keeps (by omega) 0 ws (by simp; omega) (.inl (by omega))
      exact hcell.header.write_disjoint (by rw [h40]; simp [X86.Width.bytes]; omega)
        (by omega) (.inr (by rw [h40]; simp [X86.Width.bytes]; omega))
    · intro i v hv
      obtain ⟨w, hw, hvw⟩ := hcell.fields i v hv
      have hi : i < b.fields.length := (List.getElem?_eq_some_iff.1 hv).1
      have hfi : (a + UInt64.ofNat (8 + 8 * i)).toNat = a.toNat + (8 + 8 * i) :=
        addr_toNat (by omega)
      refine ⟨w, ?_, hvw⟩
      apply storeWords_keeps (by rw [hfi]; omega) 0 ws (by simp; omega) (.inl (by rw [hfi]; omega))
      exact hw.write_disjoint (by rw [h40]; simp [X86.Width.bytes]; omega)
        (by rw [hfi]; omega) (.inr (by rw [h40, hfi]; simp [X86.Width.bytes]; omega))

/-- Stepping through a list of non-call statements inside a Lir block (`0` charges). -/
theorem lir_exec_block {lp : Lir.Program} {fn L : Nat} {F : Lir.Func} {B : Lir.Block}
    (hF : lp.funcs[fn]? = some F) (hB : F.blocks[L]? = some B)
    {mem mem' : X86.Memory} {ctx : Word} {rest : List Lir.Frame}
    {pre ss : List Lir.Stmt} (hbody : B.body.toList = pre ++ ss)
    (hnc : ∀ s ∈ ss, s.isCall = false)
    {ρ ρ' : Lir.Env} (hex : Lir.execList ρ mem ctx ss = some (ρ', mem')) :
    Sem.Star (Lir.semStep lp)
      (Lir.atState mem ctx fn L pre.length ρ rest) 0
      (Lir.atState mem' ctx fn L (pre.length + ss.length) ρ' rest) := by
  induction ss generalizing pre ρ mem with
  | nil =>
    simp only [Lir.execList, Option.some.injEq, Prod.mk.injEq] at hex
    obtain ⟨rfl, rfl⟩ := hex
    simpa using Sem.Star.refl _
  | cons s ss ih =>
    simp only [Lir.execList] at hex
    cases hs : Lir.Stmt.exec ρ mem ctx s with
    | none => simp [hs] at hex
    | some p =>
      obtain ⟨ρ1, m1⟩ := p
      simp only [hs] at hex
      have hlt : pre.length < B.body.size := by
        rw [← Array.length_toList, hbody]; simp
      have hget : B.body[pre.length] = s := by
        rw [← Array.getElem_toList (h := hlt)]
        simp [hbody]
      have h1 := Lir.step_stmt (fr := { fn, label := L, pos := pre.length, env := ρ }) (rest := rest)
        hF hB hlt hget (hnc s (by simp)) hs
      have hstar1 : Sem.Star (Lir.semStep lp)
          (Lir.atState mem ctx fn L pre.length ρ rest) 0
          (Lir.atState m1 ctx fn L (pre.length + 1) ρ1 rest) := by
        simpa [Lir.atState] using Lir.star_of_step h1
      have h2 := ih (pre := pre ++ [s]) (by simpa [List.append_assoc] using hbody)
        (fun s' hs' => hnc s' (by simp [hs'])) hex
      have hlen : (pre ++ [s]).length = pre.length + 1 := by simp
      have hlen2 : pre.length + 1 + ss.length = pre.length + (s :: ss).length := by
        simp; omega
      rw [hlen, hlen2] at h2
      simpa using hstar1.trans h2

theorem strStoreStmts_noCall : ∀ (k : Nat) (ws : List Word) (s : Lir.Stmt),
    s ∈ strStoreStmts k ws → s.isCall = false
  | _, [], _, h => nomatch h
  | k, _ :: ws, s, h => by
    simp only [strStoreStmts, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · rfl
    · rfl
    · exact strStoreStmts_noCall (k + 1) ws s h

/-- **Simulation of `Rt.Rc.Array.strLitProc`**: from any `HeapInv` memory, entering `strLitProc idx s`
either fails with `.heap` or returns in 0 charges with an 8-aligned non-zero address `w` satisfying
`ValRelStr T Pw (.lit (.str s)) w` and preserving `HeapInv` for the same `(H, Pw)`. -/
theorem strLitProc_sim {T : Tables} {Pw : List Word} {H : Own.Heap} {ctx : Word} {mem : X86.Memory}
    {lp : Lir.Program} {g idx : Nat} {s : String} {rest : List Lir.Frame}
    (hstr : lp.funcs[g]? = some (Rt.Rc.Array.strLitProc idx s))
    (hheap : HeapInv T Pw H ctx mem) :
    ∃ callee, Lir.enter lp g [] = some callee ∧
      ((∃ mem' w lfr,
          Sem.Star (Lir.semStep lp) { mem, ctx, stack := callee :: rest } 0
            { mem := mem', ctx, stack := lfr :: rest } ∧
          RetAt lp lfr w ∧ ValRelStr T Pw (.lit (.str s)) w ∧ HeapInv T Pw H ctx mem') ∨
       Sem.Fails (Lir.semStep lp) { mem, ctx, stack := callee :: rest }) := by
  let cell := X86.ELFRodata.encodeStaticString s
  let nBytes := cell.size
  have hcellK : (⟨⟨X86.ELFRodata.encodeStaticStringK s⟩⟩ : ByteArray) = cell :=
    X86.ELFRodata.encodeStaticStringK_eq s
  have hparams : (Rt.Rc.Array.strLitProc idx s).params = [] := by
    unfold Rt.Rc.Array.strLitProc; dsimp only; split <;> rfl
  have henter : Lir.enter lp g [] = some { fn := g, label := 0, pos := 0, env := {} } := by
    simp [Lir.enter, hstr, hparams, Lir.bindParams]
  refine ⟨_, henter, ?_⟩
  by_cases hbig : nBytes ≥ 2 ^ 31
  · right
    have hB0 : (Rt.Rc.Array.strLitProc idx s).blocks[0]? = some { term := .fail .heap, cold := true } := by
      unfold Rt.Rc.Array.strLitProc; dsimp only; rw [hcellK]
      rw [ite_eq_left (show (X86.ELFRodata.encodeStaticString s).size ≥ 2 ^ 31 from hbig)]; rfl
    exact ⟨0, _, .heap, .refl _, Lir.semStep_fail.2 (Lir.fail_at hstr hB0 rfl rfl)⟩
  · have hlt31 : nBytes < 2 ^ 31 := by omega
    have hnb : ¬ ((X86.ELFRodata.encodeStaticString s).size ≥ 2 ^ 31) := hbig
    obtain ⟨bump, limit, hA⟩ := hheap
    have hctx := hA.ctxLo
    have h40 := ctx40_toNat hctx
    have h32 := ctx32_toNat hctx
    have hdisp40 : Lir.dispWord Rt.bumpOff = (0 : Word) - 40 := by decide
    have hdisp32 : Lir.dispWord Rt.limitOff = (0 : Word) - 32 := by decide
    have hctx40 : ctx + Lir.dispWord Rt.bumpOff = ctx - 40 := by
      rw [hdisp40]; apply UInt64.toNat_inj.mp; simp [UInt64.sub_eq_add_neg]
    have hctx32 : ctx + Lir.dispWord Rt.limitOff = ctx - 32 := by
      rw [hdisp32]; apply UInt64.toNat_inj.mp; simp [UInt64.sub_eq_add_neg]
    have hB0 : (Rt.Rc.Array.strLitProc idx s).blocks[0]? = some
        { body := #[.assign 0 (.load .w64 .zero (Rt.Rc.Procs.ctx Rt.bumpOff)),
                    .assign 1 (.load .w64 .zero (Rt.Rc.Procs.ctx Rt.limitOff))]
          term := .brOvf .addC 2 (.v 0) (.imm (UInt64.ofNat nBytes))
            (Rt.Rc.Procs.to 1) (Rt.Rc.Procs.to 3) } := by
      unfold Rt.Rc.Array.strLitProc; dsimp only; rw [hcellK, ite_eq_right hnb]; rfl
    have hB1 : (Rt.Rc.Array.strLitProc idx s).blocks[1]? = some
        { term := .br .ule .w64 (.v 2) (.v 1) (Rt.Rc.Procs.to 2) (Rt.Rc.Procs.to 4) } := by
      unfold Rt.Rc.Array.strLitProc; dsimp only; rw [hcellK, ite_eq_right hnb]; rfl
    let ws := Rt.Rc.Array.bytesToWords64 cell
    have hB2 : (Rt.Rc.Array.strLitProc idx s).blocks[2]? = some
        { body := (#[.store .w64 (Rt.Rc.Procs.ctx Rt.bumpOff) (.v 2)] ++
            (strStoreStmts 0 ws).toArray)
          term := .ret [.v 0] } := by
      unfold Rt.Rc.Array.strLitProc; dsimp only; rw [hcellK, ite_eq_right hnb]
      have hzip := zipIdx_flatMap_eq_strStoreStmts 0 (Rt.Rc.Array.bytesToWords64 cell)
      change some ({ body := #[.store .w64 (Rt.Rc.Procs.ctx Rt.bumpOff) (.v 2)] ++
          ((Rt.Rc.Array.bytesToWords64 cell).zipIdx.flatMap fun (w, j) =>
            let reg := 3 + j
            [.assign reg (.arg (.imm w)), .store .w64 (Rt.Rc.Procs.cellAddr 0 (8 * j)) (.v reg)]).toArray,
                     term := .ret [.v 0] } : Lir.Block) = _
      rw [hzip]
    have hB4 : (Rt.Rc.Array.strLitProc idx s).blocks[4]? = some { term := .fail .heap, cold := true } := by
      unfold Rt.Rc.Array.strLitProc; dsimp only; rw [hcellK, ite_eq_right hnb]; rfl
    -- Block 0: load bump and limit, brOvf addC (no overflow since bump < 2^63, nBytes < 2^31)
    let ρ1 : Lir.Env := (({} : Lir.Env).insert 0 bump).insert 1 limit
    have hρ1_0 : ρ1[0]? = some bump := by
      rw [Lir.env_insert_ne _ _ (by decide), Lir.env_insert_self]
    have hρ1_1 : ρ1[1]? = some limit := Lir.env_insert_self _ _ _
    have hex0 : Lir.execList {} mem ctx
        [.assign 0 (.load .w64 .zero (Rt.Rc.Procs.ctx Rt.bumpOff)),
         .assign 1 (.load .w64 .zero (Rt.Rc.Procs.ctx Rt.limitOff))] = some (ρ1, mem) := by
      simp [Lir.execList, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.ctx,
        hctx40, hctx32, hA.bumpWord.read64, hA.limitWord.read64, ρ1]
    have hstar0 : Sem.Star (Lir.semStep lp)
        (Lir.atState mem ctx g 0 0 {} rest) 0 (Lir.atState mem ctx g 0 2 ρ1 rest) :=
      lir_exec_block hstr hB0 (pre := []) (by simp) (by simp [Lir.Stmt.isCall]) hex0
    have hbump_lt : bump.toNat < 2 ^ 63 := Nat.lt_of_le_of_lt hA.bumpLe hA.limitLt
    have hadd_toNat : (bump + UInt64.ofNat nBytes).toNat = bump.toNat + nBytes :=
      addr_toNat (by omega)
    have hno_ovf : ¬ (bump + UInt64.ofNat nBytes < bump) := by
      intro hlt
      have : (bump + UInt64.ofNat nBytes).toNat < bump.toNat := hlt
      omega
    have hovf_eval : Lir.Ovf.eval .addC bump (UInt64.ofNat nBytes) = (bump + UInt64.ofNat nBytes, false) := by
      simp [Lir.Ovf.eval, hno_ovf]
    let ρ2 : Lir.Env := ρ1.insert 2 (bump + UInt64.ofNat nBytes)
    have hρ2_0 : ρ2[0]? = some bump := by
      rw [Lir.env_insert_ne _ _ (by decide)]; exact hρ1_0
    have hρ2_1 : ρ2[1]? = some limit := by
      rw [Lir.env_insert_ne _ _ (by decide)]; exact hρ1_1
    have hρ2_2 : ρ2[2]? = some (bump + UInt64.ofNat nBytes) := Lir.env_insert_self _ _ _
    have hstep01 : Lir.step lp (Lir.atState mem ctx g 0 2 ρ1 rest) =
        .next (Lir.atState mem ctx g 1 0 ρ2 rest) false := by
      have hsz0 : (#[Lir.Stmt.assign 0 (.load .w64 .zero (Rt.Rc.Procs.ctx Rt.bumpOff)),
                     Lir.Stmt.assign 1 (.load .w64 .zero (Rt.Rc.Procs.ctx Rt.limitOff))]).size = 2 := rfl
      simp only [Lir.step, Lir.atState, hstr, hB0, hsz0, Nat.lt_irrefl, ↓reduceDIte,
        Lir.Arg.eval, hρ1_0, hovf_eval, Bool.false_eq_true, ↓reduceIte,
        Lir.takeEdge, Rt.Rc.Procs.to, hB1, Lir.evalArgs, List.mapM_nil, pure, Lir.bindParams, ρ2]
      rfl
    have hstar01 : Sem.Star (Lir.semStep lp)
        (Lir.atState mem ctx g 0 0 {} rest) 0 (Lir.atState mem ctx g 1 0 ρ2 rest) := by
      simpa using hstar0.trans (Lir.star_of_step hstep01)
    have hmask64 : ∀ x : Word, X86.Width.truncate .w64 x = x := by
      intro x; apply UInt64.toNat_inj.mp
      rw [X86.Width.truncate, X86.Width.mask, UInt64.toNat_and,
        show (UInt64.toNat 0xffffffffffffffff) = 2 ^ 64 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt x.toNat_lt]
    by_cases hfit : bump.toNat + nBytes ≤ limit.toNat
    · -- Fits in [bump, limit): jump to block 2, store bump' and all static words, return bump
      left
      have hule : Lir.Cond.holds .ule .w64 (bump + UInt64.ofNat nBytes) limit = true := by
        simp only [Lir.Cond.holds, hmask64, decide_eq_true_eq, UInt64.le_iff_toNat_le, hadd_toNat]
        exact hfit
      have hstep12 : Lir.step lp (Lir.atState mem ctx g 1 0 ρ2 rest) =
          .next (Lir.atState mem ctx g 2 0 ρ2 rest) false := by
        simp only [Lir.step, Lir.atState, hstr, hB1, Array.size_empty, Nat.not_lt_zero, ↓reduceDIte,
          Lir.Arg.eval, hρ2_2, hρ2_1, hule, ↓reduceIte, Lir.takeEdge, Rt.Rc.Procs.to, hB2,
          Lir.evalArgs, List.mapM_nil, pure, Lir.bindParams]
        rfl
      have hstar02 : Sem.Star (Lir.semStep lp)
          (Lir.atState mem ctx g 0 0 {} rest) 0 (Lir.atState mem ctx g 2 0 ρ2 rest) := by
        simpa using hstar01.trans (Lir.star_of_step hstep12)
      -- Block 2: store bump' at [ctx - 40], then storeWords
      let m1 := mem.write .w64 (ctx - 40) (bump + UInt64.ofNat nBytes)
      have hwBump : mem.write? .w64 (ctx - 40) (bump + UInt64.ofNat nBytes) = .ok m1 :=
        write?_ok (fun i hi => hA.bumpWritable i (by simpa [X86.Width.bytes] using hi))
      have hstBump : Lir.Stmt.exec ρ2 mem ctx (.store .w64 (Rt.Rc.Procs.ctx Rt.bumpOff) (.v 2)) =
          some (ρ2, m1) := by
        simp only [Lir.Stmt.exec, Lir.Addr.eval, Rt.Rc.Procs.ctx, bind, Option.bind,
          UInt64.add_zero, hctx40, Lir.Arg.eval, hρ2_2, hwBump]
      have hws_len : 8 * ws.length = nBytes := by
        have hal := X86.ELFRodata.encodeStaticByteArray_aligned s.toUTF8
        change 8 * (Rt.Rc.Array.bytesToWords64 (X86.ELFRodata.encodeStaticByteArray s.toUTF8)).length =
          (X86.ELFRodata.encodeStaticByteArray s.toUTF8).size
        rw [Rt.Rc.Array.bytesToWords64_length]
        omega
      have hlim_lt := hA.limitLt
      obtain ⟨ρ', hexWs, h0'⟩ := execList_strStoreStmts (base := bump) (ctx := ctx) 0 ws ρ2 m1 hρ2_0
        (by simp; omega) (by simp; omega)
        (fun addr ha1 ha2 => by
          simp only [m1, X86.Memory.write, writeLittle_writable]
          exact (hA.free addr (by omega) (by omega)).2)
      have hex2 : Lir.execList ρ2 mem ctx
          (.store .w64 (Rt.Rc.Procs.ctx Rt.bumpOff) (.v 2) :: strStoreStmts 0 ws) =
          some (ρ', storeWords m1 bump 0 ws) := by
        simp only [Lir.execList, hstBump]; exact hexWs
      have hstar2 : Sem.Star (Lir.semStep lp)
          (Lir.atState mem ctx g 2 0 ρ2 rest) 0
          (Lir.atState (storeWords m1 bump 0 ws) ctx g 2 (1 + (strStoreStmts 0 ws).length) ρ' rest) := by
        have h := lir_exec_block hstr hB2 (rest := rest) (pre := [])
          (by simp)
          (fun st hst => by
            simp only [List.mem_cons] at hst
            rcases hst with rfl | hst
            · rfl
            · exact strStoreStmts_noCall 0 ws st hst)
          hex2
        simpa [Nat.add_comm] using h
      have hstarAll := hstar02.trans hstar2
      have hbump_ne : bump ≠ 0 := by
        intro hz
        have : bump.toNat = 0 := by rw [hz]; rfl
        have := hA.start
        omega
      refine ⟨storeWords m1 bump 0 ws, bump,
        { fn := g, label := 2, pos := 1 + (strStoreStmts 0 ws).length, env := ρ' },
        by simpa [Lir.atState] using hstarAll, ?_, ⟨hA.bumpAligned, hbump_ne⟩,
        ⟨bump + UInt64.ofNat nBytes, limit, strLit_heapAt hA hws_len hfit⟩⟩
      refine ⟨rfl, Rt.Rc.Array.strLitProc idx s, _, .v 0, hstr, hB2, by simp [Nat.add_comm], rfl, h0'⟩
    · -- Does not fit in [bump, limit): jump to block 4 and fail .heap
      right
      have hule : Lir.Cond.holds .ule .w64 (bump + UInt64.ofNat nBytes) limit = false := by
        simp only [Lir.Cond.holds, hmask64, decide_eq_false_iff_not, UInt64.le_iff_toNat_le, hadd_toNat]
        exact hfit
      have hstep14 : Lir.step lp (Lir.atState mem ctx g 1 0 ρ2 rest) =
          .next (Lir.atState mem ctx g 4 0 ρ2 rest) false := by
        simp only [Lir.step, Lir.atState, hstr, hB1, Array.size_empty, Nat.not_lt_zero, ↓reduceDIte,
          Lir.Arg.eval, hρ2_2, hρ2_1, hule, Bool.false_eq_true, ↓reduceIte, Lir.takeEdge,
          Rt.Rc.Procs.to, hB4, Lir.evalArgs, List.mapM_nil, pure, Lir.bindParams]
        rfl
      have hstar04 : Sem.Star (Lir.semStep lp)
          (Lir.atState mem ctx g 0 0 {} rest) 0 (Lir.atState mem ctx g 4 0 ρ2 rest) := by
        simpa using hstar01.trans (Lir.star_of_step hstep14)
      exact ⟨0, _, .heap, by simpa [Lir.atState] using hstar04,
        Lir.semStep_fail.2 (Lir.fail_at hstr hB4 rfl rfl)⟩

/-! ## 2. Oracle string step (`strStep`) and lifted LIR diagram (`strDiagram_sel`) -/

/-- The string literal assigned to `FunId` `f`, if `f` is one of `P`'s appended `strLitProc`s. -/
def strOfProg (P : Cfg.Program) (f : Fir.FunId) : Option String :=
  if P.size + 3 ≤ f then (Rt.lowerStrs P)[f - (P.size + 3)]? else none

/-- `Cfg.step .immortal P'` extended with zero-charge oracle calls for `P`'s string procedures. -/
def strStep (P P' : Cfg.Program) : Cfg.State → Sem.Step Cfg.State (Own.RVal × Own.Heap)
  | .call f [] stk H =>
    match strOfProg P f with
    | some s => .next (.ret (.lit (.str s)) stk H) false
    | none => Cfg.step .immortal P' (.call f [] stk H)
  | s => Cfg.step .immortal P' s

/-- LIR target layout for `P'` plus `P`'s appended `strLitProc`s at `P.size + 3 + i`. -/
structure TargetStr (P P' : Cfg.Program) (lp : Lir.Program) : Prop where
  base : Target P' lp
  strs : ∀ i s, (Rt.lowerStrs P)[i]? = some s →
    lp.funcs[P.size + 3 + i]? = some (Rt.Rc.Array.strLitProc i s)

/-- **Single-step simulation from `strStep P P'` to LIR**, reusing all of `Rt.Proof.Diagram`. -/
theorem strStep_sim_one {P P' : Cfg.Program} {lp : Lir.Program} {ctx : Word}
    (ht : TargetStr P P' lp) {s₁ s₁' : Cfg.State} {s₂ : Lir.State} {b : Bool}
    (hrel : Rel P' lp ctx s₁ s₂) (hsafe : SwitchSel P' s₁)
    (hs : strStep P P' s₁ = .next s₁' b) :
    (∃ c s₂', Sem.Star (Lir.semStep lp) s₂ c s₂' ∧ b.toNat ≤ c ∧ Rel P' lp ctx s₁' s₂') ∨
      Sem.Fails (Lir.semStep lp) s₂ := by
  match s₁, hrel, hs with
  | .call g [] stk H, hrel, hs =>
    simp only [strStep] at hs
    cases hso : strOfProg P g with
    | some s =>
      simp only [hso, Sem.Step.next.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      have hge : P.size + 3 ≤ g := by
        unfold strOfProg at hso
        split at hso
        · assumption
        · cases hso
      have hidx : (Rt.lowerStrs P)[g - (P.size + 3)]? = some s := by
        unfold strOfProg at hso; simpa [hge] using hso
      have hg_eq : P.size + 3 + (g - (P.size + 3)) = g := by omega
      have hstr : lp.funcs[g]? = some (Rt.Rc.Array.strLitProc (g - (P.size + 3)) s) := by
        simpa [hg_eq] using ht.strs (g - (P.size + 3)) s hidx
      obtain ⟨hctx, Pw, hheap, ws, lrest, hws, hstk, hstep⟩ := hrel
      cases hws with
      | nil =>
        obtain ⟨callee, henter, hsim⟩ := strLitProc_sim (rest := lrest) hstr hheap
        have hcallStep : Lir.step lp s₂ = .next { s₂ with stack := callee :: lrest } true :=
          hstep callee henter
        have hstarCall : Sem.Star (Lir.semStep lp) s₂ 1
            { mem := s₂.mem, ctx, stack := callee :: lrest } := by
          have h1 := Lir.star_of_step hcallStep
          simpa [hctx] using h1
        rcases hsim with ⟨mem', w, lfr, hstarBody, hret, hval, hheap'⟩ | hfail
        · refine .inl ⟨1 + 0, { mem := mem', ctx, stack := lfr :: lrest },
            hstarCall.trans hstarBody, by simp, ?_⟩
          exact ⟨rfl, Pw, hheap', lfr, lrest, w, rfl, hval, hret, hstk⟩
        · exact .inr (fails_prepend hstarCall hfail)
    | none =>
      simp only [hso] at hs
      have hb : b = true := by
        simp only [Cfg.step] at hs
        split at hs
        · split at hs
          · split at hs
            · simp only [Sem.Step.next.injEq] at hs; exact hs.2.symm
            · cases hs
          · cases hs
        · cases hs
      subst hb
      obtain ⟨c, s₂', hst, hc, hrel'⟩ := step_enter ht.base hrel hs
      exact .inl ⟨c, s₂', hst, hc, hrel'⟩
  | .call g (a :: as) stk H, hrel, hs =>
    simp only [strStep] at hs
    have hb : b = true := by
      simp only [Cfg.step] at hs
      split at hs
      · split at hs
        · split at hs
          · simp only [Sem.Step.next.injEq] at hs; exact hs.2.symm
          · cases hs
        · cases hs
      · cases hs
    subst hb
    obtain ⟨c, s₂', hst, hc, hrel'⟩ := step_enter ht.base hrel hs
    exact .inl ⟨c, s₂', hst, hc, hrel'⟩
  | .ret v [] H, _, hs => simp [strStep, Cfg.step] at hs
  | .ret v ((fr, x) :: stk) H, hrel, hs =>
    simp only [strStep, Cfg.step, Sem.Step.next.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨s₂', h₁, hrel'⟩ := step_return hrel
    exact .inl ⟨0, s₂', by simpa using Lir.star_of_step h₁, Nat.le_refl _, hrel'⟩
  | .run fr stk H, hrel, hs =>
    simp only [strStep] at hs
    cases hfr : fr.rest with
    | nil =>
      exact step_term_sel ht.base hrel hfr
        (fun fd b x alts d v key fs e Pw w ctx' m h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
          hsafe fd b x alts d v key fs e Pw w ctx' m h1 h2 hfr h3 h4 h5 h6 h7 h8 h9)
        hs
    | cons i is =>
      obtain ⟨x, r⟩ := i
      by_cases hcall : ∃ g as, r = .fir (.call g as)
      · obtain ⟨g, as, rfl⟩ := hcall
        simp only [Cfg.step, hfr] at hs
        cases hvs : Own.evalArgs fr.env as with
        | none => simp [hvs] at hs
        | some vs =>
          simp only [hvs, Sem.Step.next.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          rcases step_call_instr hrel hfr hvs with hrel' | hfail
          · exact .inl ⟨0, s₂, .refl _, Nat.le_refl _, hrel'⟩
          · exact .inr hfail
      · have hnc : ∀ g as, r ≠ .fir (.call g as) := fun g as h => hcall ⟨g, as, h⟩
        rw [step_bind hfr hnc] at hs
        cases hev : Own.evalRhs .immortal P'.tables fr.env H r with
        | ok p =>
          obtain ⟨v, H'⟩ := p
          simp only [hev, Sem.Step.next.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          exact (step_instr ht.base hrel hfr hnc hev).imp
            (fun ⟨c, s₂', hst, hrel'⟩ => ⟨c, s₂', hst, Nat.zero_le _, hrel'⟩) id
        | resource _ | trap | timeout | stuck => simp [hev] at hs

/-- **Final-step simulation from `strStep P P'` to LIR**, mirroring `Diagram.diagram_sel.final`. -/
theorem strStep_sim_final {P P' : Cfg.Program} {lp : Lir.Program} {ctx : Word}
    {s₁ : Cfg.State} {s₂ : Lir.State} {r : Sem.Result (Own.RVal × Own.Heap)}
    (hrel : Rel P' lp ctx s₁ s₂) (hf : Sem.Final (strStep P P' s₁) r) (hr : r ≠ .stuck) :
    (∃ c s₂' r₂, Sem.Star (Lir.semStep lp) s₂ c s₂' ∧ Sem.Final (Lir.semStep lp s₂') r₂ ∧
        Sem.Result.Refines (Res P' ctx) r r₂) ∨ Sem.Fails (Lir.semStep lp) s₂ := by
  match s₁, hrel, hf with
  | .call g [] stk H, _, hf =>
    exfalso
    simp only [strStep] at hf
    split at hf
    · cases hf
    · simp only [Cfg.step] at hf
      split at hf
      · split at hf
        · split at hf
          · cases hf
          · cases hf; exact hr rfl
        · cases hf; exact hr rfl
      · cases hf; exact hr rfl
  | .call g (_ :: _) stk H, _, hf =>
    exfalso
    simp only [strStep, Cfg.step] at hf
    split at hf
    · split at hf
      · split at hf
        · cases hf
        · cases hf; exact hr rfl
      · cases hf; exact hr rfl
    · cases hf; exact hr rfl
  | .ret v [] H, hrel, hf =>
    simp only [strStep, Cfg.step] at hf
    cases hf
    obtain ⟨w, h₁, hres⟩ := final_return hrel
    exact .inl ⟨0, s₂, .ok ([w], s₂.mem), .refl _, by rw [Lir.semStep, h₁]; exact .done, .ok hres⟩
  | .ret v ((fr, x) :: stk) H, _, hf => simp only [strStep, Cfg.step] at hf; cases hf
  | .run fr stk H, hrel, hf =>
    simp only [strStep] at hf
    cases hfr : fr.rest with
    | nil =>
      cases hst : Cfg.step .immortal P' (.run fr stk H) with
      | trap =>
        rw [hst] at hf
        cases hf
        exact .inl ⟨0, s₂, .trap, .refl _, by rw [Lir.semStep, final_trap hrel hfr hst]; exact .trap, .trap⟩
      | stuck => rw [hst] at hf; cases hf; exact absurd rfl hr
      | next _ _ => rw [hst] at hf; cases hf
      | done _ =>
        exfalso
        simp only [Cfg.step, hfr] at hst
        split at hst
        · split at hst
          · split at hst
            · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
            · split at hst
              · split at hst
                · split at hst
                  · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
                  · cases hst
                · cases hst
              · cases hst
            · split at hst <;> cases hst
            · split at hst <;> cases hst
            · cases hst
          · cases hst
        · cases hst
      | fail _ =>
        exfalso
        simp only [Cfg.step, hfr] at hst
        split at hst
        · split at hst
          · split at hst
            · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
            · split at hst
              · split at hst
                · split at hst
                  · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
                  · cases hst
                · cases hst
              · cases hst
            · split at hst <;> cases hst
            · split at hst <;> cases hst
            · cases hst
          · cases hst
        · cases hst
    | cons i is =>
      exfalso
      obtain ⟨x, r'⟩ := i
      by_cases hcall : ∃ g as, r' = .fir (.call g as)
      · obtain ⟨g, as, rfl⟩ := hcall
        simp only [Cfg.step, hfr] at hf
        split at hf
        · cases hf
        · cases hf; exact hr rfl
      · rw [step_bind hfr (fun g as h => hcall ⟨g, as, h⟩)] at hf
        rcases evalRhs_ok_or_stuck (T := P'.tables) (ρ := fr.env) (H := H) r' with ⟨p, hp⟩ | hp
        · rw [hp] at hf; cases hf
        · rw [hp] at hf; cases hf; exact hr rfl

/-! ## 3. Pure Cfg-to-Cfg `hoistStrings` simulation (`Cfg.step .immortal P` → `strStep P P'`) -/

/-- Collect completeness: `addStr` keeps existing elements and adds `s`. -/
theorem mem_addStr_iff (acc : List String) (s t : String) :
    t ∈ addStr acc s ↔ t ∈ acc ∨ t = s := by
  unfold addStr
  by_cases h : s ∈ acc
  · have hc : acc.contains s = true := List.elem_eq_true_of_mem h
    simp only [hc, ↓reduceIte, iff_self_or]
    intro rfl; exact h
  · have _hc : acc.contains s = false := by
      cases he : acc.contains s with
      | false => rfl
      | true => exact absurd (List.mem_of_elem_eq_true he) h
    simp [h]

theorem mem_collectArg (acc : List String) (a : Fir.Arg) :
    (∀ t ∈ acc, t ∈ collectArg acc a) ∧
    (∀ s, a = .lit (.str s) → s ∈ collectArg acc a) := by
  cases a with
  | lit l =>
    cases l with
    | str s =>
      refine ⟨fun t ht => (mem_addStr_iff acc s t).2 (.inl ht), fun s' hs' => ?_⟩
      cases hs'; exact (mem_addStr_iff acc s s).2 (.inr rfl)
    | nat _ => exact ⟨fun _ h => h, fun _ h => nomatch h⟩
  | var _ | erased => exact ⟨fun _ h => h, fun _ h => nomatch h⟩

theorem mem_collectArgs (acc : List String) (as : List Fir.Arg) :
    (∀ t ∈ acc, t ∈ collectArgs acc as) ∧
    (∀ s, .lit (.str s) ∈ as → s ∈ collectArgs acc as) := by
  induction as generalizing acc with
  | nil => exact ⟨fun _ h => h, fun _ h => nomatch h⟩
  | cons a as ih =>
    simp only [collectArgs, List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (collectArg acc a)
    obtain ⟨ha1, ha2⟩ := mem_collectArg acc a
    refine ⟨fun t ht => h1 t (ha1 t ht), fun s hs => ?_⟩
    rcases List.mem_cons.1 hs with rfl | hs
    · exact h1 s (ha2 s rfl)
    · exact h2 s hs

theorem mem_collectRhs (acc : List String) (r : Own.Rhs) :
    ∀ t ∈ acc, t ∈ collectRhs acc r := by
  cases r with
  | fir e =>
    cases e with
    | arg a => exact (mem_collectArg acc a).1
    | ctor _ as | prim _ as | call _ as => exact (mem_collectArgs acc as).1
    | proj _ _ _ => exact fun _ h => h
  | alloc _ as _ => exact (mem_collectArgs acc as).1
  | proj _ _ _ => exact fun _ h => h

theorem mem_collectInstr (acc : List String) (i : Cfg.Instr) :
    ∀ t ∈ acc, t ∈ collectInstr acc i := by
  cases i with
  | bind _ r => exact mem_collectRhs acc r

theorem mem_collectInstrs (acc : List String) (is : List Cfg.Instr) :
    ∀ t ∈ acc, t ∈ is.foldl collectInstr acc := by
  induction is generalizing acc with
  | nil => exact fun _ h => h
  | cons i is ih =>
    intro t ht
    exact ih (collectInstr acc i) t (mem_collectInstr acc i t ht)

theorem mem_collectEdge (acc : List String) (e : Cfg.Edge) :
    ∀ t ∈ acc, t ∈ collectEdge acc e :=
  (mem_collectArgs acc e.args).1

theorem mem_collectAlts (acc : List String) (alts : List (Key.CtorKey × Cfg.Edge)) :
    ∀ t ∈ acc, t ∈ alts.foldl (fun s (_, e) => collectEdge s e) acc := by
  induction alts generalizing acc with
  | nil => exact fun _ h => h
  | cons p alts ih =>
    intro t ht
    exact ih (collectEdge acc p.2) t (mem_collectEdge acc p.2 t ht)

theorem mem_collectTerm (acc : List String) (tm : Cfg.Term) :
    ∀ t ∈ acc, t ∈ collectTerm acc tm := by
  cases tm with
  | jump e => exact mem_collectEdge acc e
  | switch _ alts d =>
    intro t ht
    have h1 := mem_collectAlts acc alts t ht
    cases d with
    | none => exact h1
    | some e => exact mem_collectEdge _ e t h1
  | ret a => exact (mem_collectArg acc a).1
  | tcall _ as => exact (mem_collectArgs acc as).1
  | trap => exact fun _ h => h

theorem mem_collectBlock (acc : List String) (b : Cfg.Block) :
    ∀ t ∈ acc, t ∈ collectBlock acc b :=
  fun t ht => mem_collectTerm _ b.term t (mem_collectInstrs acc b.body t ht)

theorem mem_collectFun (acc : List String) (fd : Cfg.Fun) :
    ∀ t ∈ acc, t ∈ collectFun acc fd := by
  intro t ht
  unfold collectFun
  have : ∀ (bs : List Cfg.Block) (a : List String), t ∈ a → t ∈ bs.foldl collectBlock a := by
    intro bs
    induction bs with
    | nil => intro _ h; exact h
    | cons b bs ih => intro a ha; exact ih _ (mem_collectBlock a b t ha)
  exact this fd.blocks acc ht

/-- Every string literal occurring in a function `f < P.size` is in `lowerStrs P`. -/
theorem collectStrings_fun_subset {P : Cfg.Program} {f : Nat} {fd : Cfg.Fun}
    (hf : f < P.size) (hfd : P.fun? f = some fd) :
    ∀ s ∈ collectFun [] fd, s ∈ Rt.lowerStrs P := by
  have mono_step : ∀ (fs : List Nat) (acc : List String) (t : String),
      t ∈ acc → t ∈ fs.foldl (fun a g => match P.fun? g with | some fd => collectFun a fd | none => a) acc := by
    intro fs
    induction fs with
    | nil => intro _ _ h; exact h
    | cons g fs ih =>
      intro a t ht
      simp only [List.foldl_cons]
      apply ih
      cases P.fun? g with
      | none => exact ht
      | some fd' => exact mem_collectFun a fd' t ht
  have mem_range_hit : ∀ (fs : List Nat) (acc : List String) (s : String),
      f ∈ fs → (∀ a, s ∈ collectFun [] fd → s ∈ collectFun a fd) → s ∈ collectFun [] fd →
      s ∈ fs.foldl (fun a g => match P.fun? g with | some fd => collectFun a fd | none => a) acc := by
    intro fs
    induction fs with
    | nil => intro _ _ hm; cases hm
    | cons g fs ih =>
      intro acc s hm hlift hs
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 hm with rfl | hm'
      · simp only [hfd]
        exact mono_step fs _ s (hlift acc hs)
      · exact ih _ s hm' hlift hs
  -- Prove collectFun monotonicity in acc: s ∈ collectFun [] fd → s ∈ collectFun acc fd
  have hlift_add : ∀ (a1 a2 : List String) (x : String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ addStr a1 x, t ∈ addStr a2 x := by
    intro a1 a2 x hsub t ht
    rw [mem_addStr_iff] at ht ⊢
    rcases ht with h | rfl
    · exact .inl (hsub t h)
    · exact .inr rfl
  have hlift_arg : ∀ (a1 a2 : List String) (a : Fir.Arg),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ collectArg a1 a, t ∈ collectArg a2 a := by
    intro a1 a2 a hsub t ht
    cases a with
    | lit l => cases l with
      | str s => exact hlift_add a1 a2 s hsub t ht
      | nat _ => exact hsub t ht
    | var _ | erased => exact hsub t ht
  have hlift_args : ∀ (as : List Fir.Arg) (a1 a2 : List String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ collectArgs a1 as, t ∈ collectArgs a2 as := by
    intro as
    induction as with
    | nil => intro _ _ hsub; exact hsub
    | cons a as ih => intro a1 a2 hsub; exact ih _ _ (hlift_arg a1 a2 a hsub)
  have hlift_rhs : ∀ (r : Own.Rhs) (a1 a2 : List String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ collectRhs a1 r, t ∈ collectRhs a2 r := by
    intro r a1 a2 hsub
    cases r with
    | fir e =>
      cases e with
      | arg a => exact hlift_arg a1 a2 a hsub
      | ctor _ as | prim _ as | call _ as => exact hlift_args as a1 a2 hsub
      | proj _ _ _ => exact hsub
    | alloc _ as _ => exact hlift_args as a1 a2 hsub
    | proj _ _ _ => exact hsub
  have hlift_instrs : ∀ (is : List Cfg.Instr) (a1 a2 : List String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ is.foldl collectInstr a1, t ∈ is.foldl collectInstr a2 := by
    intro is
    induction is with
    | nil => intro _ _ hsub; exact hsub
    | cons i is ih =>
      intro a1 a2 hsub
      cases i with
      | bind _ r => exact ih _ _ (hlift_rhs r a1 a2 hsub)
  have hlift_alts : ∀ (alts : List (Key.CtorKey × Cfg.Edge)) (a1 a2 : List String),
      (∀ t ∈ a1, t ∈ a2) →
      ∀ t ∈ alts.foldl (fun s (_, e) => collectEdge s e) a1,
        t ∈ alts.foldl (fun s (_, e) => collectEdge s e) a2 := by
    intro alts
    induction alts with
    | nil => intro _ _ hsub; exact hsub
    | cons p alts ih => intro a1 a2 hsub; exact ih _ _ (hlift_args p.2.args a1 a2 hsub)
  have hlift_term : ∀ (tm : Cfg.Term) (a1 a2 : List String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ collectTerm a1 tm, t ∈ collectTerm a2 tm := by
    intro tm a1 a2 hsub
    cases tm with
    | jump e => exact hlift_args e.args a1 a2 hsub
    | switch _ alts d =>
      have h1 := hlift_alts alts a1 a2 hsub
      cases d with
      | none => exact h1
      | some e => exact hlift_args e.args _ _ h1
    | ret a => exact hlift_arg a1 a2 a hsub
    | tcall _ as => exact hlift_args as a1 a2 hsub
    | trap => exact hsub
  have hlift_blocks : ∀ (bs : List Cfg.Block) (a1 a2 : List String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ bs.foldl collectBlock a1, t ∈ bs.foldl collectBlock a2 := by
    intro bs
    induction bs with
    | nil => intro _ _ hsub; exact hsub
    | cons b bs ih =>
      intro a1 a2 hsub
      exact ih _ _ (hlift_term b.term _ _ (hlift_instrs b.body a1 a2 hsub))
  intro s hs
  exact mem_range_hit (List.range P.size) [] s (List.mem_range.2 hf)
    (fun a h => hlift_blocks fd.blocks [] a (fun _ h0 => nomatch h0) s h) hs

/-- Lookup in `lowerStrFns P` returns a valid `strOfProg P` index! -/
theorem lowerStrFns_lookup_strOfProg {P : Cfg.Program} {s : String} {fnId : Fir.FunId}
    (h : (Rt.lowerStrFns P).lookup s = some fnId) : strOfProg P fnId = some s := by
  have aux : ∀ (k : Nat) (strs : List String),
      ((strs.zipIdx k).map fun (t, i) => (t, P.size + 3 + i)).lookup s = some fnId →
      P.size + 3 + k ≤ fnId ∧ strs[fnId - (P.size + 3 + k)]? = some s := by
    intro k strs
    induction strs generalizing k with
    | nil => simp
    | cons t ts ih =>
      intro hl
      simp only [List.zipIdx_cons, List.map_cons, List.lookup_cons] at hl
      cases hst : (s == t) with
      | true =>
        simp only [hst, Option.some.injEq] at hl
        subst hl
        have rfl_st : s = t := beq_iff_eq.1 hst
        subst rfl_st
        exact ⟨Nat.le_refl _, by simp⟩
      | false =>
        simp only [hst] at hl
        obtain ⟨hge, hget⟩ := ih (k + 1) hl
        refine ⟨by omega, ?_⟩
        have hpos : fnId - (P.size + 3 + k) = (fnId - (P.size + 3 + (k + 1))) + 1 := by
          have h1 : P.size + 3 + (k + 1) = (P.size + 3 + k) + 1 := (Nat.add_assoc _ _ _).symm
          rw [h1, Nat.sub_add_eq fnId (P.size + 3 + k) 1]
          have h2 : 1 ≤ fnId - (P.size + 3 + k) :=
            Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact h1 ▸ hge)
          exact (Nat.sub_add_cancel h2).symm
        rw [hpos]; simpa using hget
  obtain ⟨hge, hget⟩ := aux 0 (Rt.lowerStrs P) h
  unfold strOfProg
  simp only [Nat.add_zero] at hge hget
  simp [hge, hget]

/-- Every string in `lowerStrs P` has a `some` lookup in `lowerStrFns P`. -/
theorem lowerStrFns_lookup_of_mem {P : Cfg.Program} {s : String} (h : s ∈ Rt.lowerStrs P) :
    ∃ fnId, (Rt.lowerStrFns P).lookup s = some fnId ∧ strOfProg P fnId = some s := by
  have aux : ∀ (k : Nat) (strs : List String), s ∈ strs →
      ∃ fnId, ((strs.zipIdx k).map fun (t, i) => (t, P.size + 3 + i)).lookup s = some fnId := by
    intro k strs
    induction strs generalizing k with
    | nil => intro hm; cases hm
    | cons t ts ih =>
      intro hm
      simp only [List.zipIdx_cons, List.map_cons, List.lookup_cons]
      by_cases hst : s = t
      · subst hst; exact ⟨P.size + 3 + k, by simp⟩
      · have hbeq : (s == t) = false := beq_false_of_ne hst
        simp only [hbeq]
        rcases List.mem_cons.1 hm with rfl | hm'
        · exact absurd rfl hst
        · exact ih (k + 1) hm'
  obtain ⟨fnId, hl⟩ := aux 0 (Rt.lowerStrs P) h
  exact ⟨fnId, hl, lowerStrFns_lookup_strOfProg hl⟩

/-- Hoisted string-call bindings in a block body prefix. -/
inductive StrBinds (P : Cfg.Program) : Nat → Nat → List Cfg.Instr → List (Nat × String) → Prop where
  | nil (lo : Nat) : StrBinds P lo lo [] []
  | cons {lo hi t : Nat} {fnId : Fir.FunId} {s : String} {rest : List Cfg.Instr} {bs : List (Nat × String)} :
      strOfProg P fnId = some s →
      lo ≤ t →
      StrBinds P (t + 1) hi rest bs →
      StrBinds P lo hi (.bind t (.fir (.call fnId [])) :: rest) ((t, s) :: bs)

theorem StrBinds.le {P : Cfg.Program} {lo hi : Nat} {pre : List Cfg.Instr} {bs : List (Nat × String)}
    (h : StrBinds P lo hi pre bs) : lo ≤ hi := by
  induction h with
  | nil _ => exact Nat.le_refl _
  | cons _ hlt _ ih => omega

theorem StrBinds.append {P : Cfg.Program} {a b c : Nat} {p1 p2 : List Cfg.Instr} {b1 b2 : List (Nat × String)}
    (h1 : StrBinds P a b p1 b1) (h2 : StrBinds P b c p2 b2) :
    StrBinds P a c (p1 ++ p2) (b1 ++ b2) := by
  induction h1 with
  | nil _ => exact h2
  | cons hs hlt _ ih => exact .cons hs hlt (ih h2)

/-- Bind hoisted string variables in an `Own.Env`. -/
def bindStrs (ρ : Own.Env) : List (Nat × String) → Own.Env
  | [] => ρ
  | (t, s) :: bs => bindStrs (ρ.insert t (.lit (.str s))) bs

theorem bindStrs_append (ρ : Own.Env) (b1 b2 : List (Nat × String)) :
    bindStrs ρ (b1 ++ b2) = bindStrs (bindStrs ρ b1) b2 := by
  induction b1 generalizing ρ with
  | nil => rfl
  | cons p b1 ih => exact ih _

theorem bindStrs_get_lt {P : Cfg.Program} {lo hi : Nat} {pre : List Cfg.Instr} {bs : List (Nat × String)}
    (h : StrBinds P lo hi pre bs) :
    ∀ (ρ : Own.Env) {y : Nat}, y < lo → (bindStrs ρ bs).get? y = ρ.get? y := by
  induction h with
  | nil _ => intro _ _ _; rfl
  | cons _ hlt _ ih =>
    intro ρ y hy
    rw [bindStrs, ih _ (by omega), Src.NatMap.get?_insert_ne _ _ (by omega)]

theorem bindStrs_get_mem {P : Cfg.Program} {lo hi : Nat} {pre : List Cfg.Instr} {bs : List (Nat × String)}
    (h : StrBinds P lo hi pre bs) :
    ∀ (ρ : Own.Env) {t : Nat} {s : String}, (t, s) ∈ bs → (bindStrs ρ bs).get? t = some (.lit (.str s)) := by
  induction h with
  | nil _ => intro _ _ _ hm; cases hm
  | @cons lo hi t0 fnId s0 rest bs _ _ hrest ih =>
    intro ρ t s hm
    rcases List.mem_cons.1 hm with h0 | hm'
    · cases h0
      rw [bindStrs, bindStrs_get_lt hrest _ (by omega), Src.NatMap.get?_insert_self]
    · exact ih _ hm'

/-- Every binding added by `bindStrs` is a string literal. -/
theorem bindStrs_rev : ∀ (bs : List (Nat × String)) (ρ : Own.Env) {y : Nat} {u : Own.RVal},
    (bindStrs ρ bs).get? y = some u → ρ.get? y = some u ∨ ∃ s, u = .lit (.str s)
  | [], _, _, _, h => .inl h
  | (t, s) :: bs, ρ, y, u, h => by
    rcases bindStrs_rev bs (ρ.insert t (.lit (.str s))) h with h' | hs
    · rw [Src.NatMap.get?_insert] at h'
      split at h'
      · cases h'; exact .inr ⟨s, rfl⟩
      · exact .inl h'
    · exact .inr hs

/-- Running a `StrBinds` prefix directly in LIR via `strStep_sim_one`. -/
theorem run_strBinds_sim {P P' : Cfg.Program} {lp : Lir.Program} {ctx : Word}
    (ht : TargetStr P P' lp) {lo hi : Nat} {pre : List Cfg.Instr} {bs : List (Nat × String)}
    (h : StrBinds P lo hi pre bs) :
    ∀ (fr : Cfg.Frame) (tail : List Cfg.Instr) (stk : List (Cfg.Frame × Nat)) (H : Own.Heap)
      {s₃ : Lir.State},
      Rel P' lp ctx (.run { fr with rest := pre ++ tail } stk H) s₃ →
      (∃ c s₃', Sem.Star (Lir.semStep lp) s₃ c s₃' ∧
        Rel P' lp ctx (.run { fr with rest := tail, env := bindStrs fr.env bs } stk H) s₃') ∨
        Sem.Fails (Lir.semStep lp) s₃ := by
  induction h with
  | nil _ =>
    intro fr tail stk H s₃ hrel
    exact .inl ⟨0, s₃, .refl _, by simpa [bindStrs] using hrel⟩
  | @cons lo hi t fnId s rest bs hstr _ _ ih =>
    intro fr tail stk H s₃ hrel
    have h1 : strStep P P' (.run { fr with rest := .bind t (.fir (.call fnId [])) :: (rest ++ tail) } stk H) =
        .next (.call fnId [] (({ fr with rest := rest ++ tail }, t) :: stk) H) false := by
      simp [strStep, Cfg.step, Own.evalArgs]
    have h2 : strStep P P' (.call fnId [] (({ fr with rest := rest ++ tail }, t) :: stk) H) =
        .next (.ret (.lit (.str s)) (({ fr with rest := rest ++ tail }, t) :: stk) H) false := by
      simp [strStep, hstr]
    have h3 : strStep P P' (.ret (.lit (.str s)) (({ fr with rest := rest ++ tail }, t) :: stk) H) =
        .next (.run { fr with rest := rest ++ tail, env := fr.env.insert t (.lit (.str s)) } stk H) false := by
      simp [strStep, Cfg.step]
    have hsw1 : SwitchSel P' (.run { fr with rest := .bind t (.fir (.call fnId [])) :: (rest ++ tail) } stk H) := by
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnil; cases hnil
    rcases strStep_sim_one ht hrel hsw1 h1 with ⟨c1, s₃_1, hst1, _, hrel1⟩ | hf1
    · rcases strStep_sim_one ht hrel1 trivial h2 with ⟨c2, s₃_2, hst2, _, hrel2⟩ | hf2
      · rcases strStep_sim_one ht hrel2 trivial h3 with ⟨c3, s₃_3, hst3, _, hrel3⟩ | hf3
        · rcases ih { fr with env := fr.env.insert t (.lit (.str s)) } tail stk H hrel3 with
            ⟨c4, s₃_4, hst4, hrel4⟩ | hf4
          · exact .inl ⟨c1 + c2 + c3 + c4, s₃_4, ((hst1.trans hst2).trans hst3).trans hst4,
              by simpa [bindStrs] using hrel4⟩
          · exact .inr (fails_prepend ((hst1.trans hst2).trans hst3) hf4)
        · exact .inr (fails_prepend (hst1.trans hst2) hf3)
      · exact .inr (fails_prepend hst1 hf2)
    · exact .inr hf1

/-- Structural facts about `hoistArg`, `hoistArgs`, `hoistRhs`, `hoistTerm`. -/
theorem hoistArg_spec {P : Cfg.Program} {fresh : Nat} {a : Fir.Arg}
    (hcov : ∀ s, a = .lit (.str s) → s ∈ Rt.lowerStrs P) :
    let r := hoistArg (Rt.lowerStrFns P) fresh a
    ∃ bs, StrBinds P fresh r.2.2 r.1 bs ∧
      ∀ (ρ ρ' : Own.Env) (v : Own.RVal),
        (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
        (∀ t s, (t, s) ∈ bs → ρ'.get? t = some (.lit (.str s))) →
        Own.evalArg ρ a = some v → Own.evalArg ρ' r.2.1 = some v := by
  cases a with
  | var y =>
    exact ⟨[], .nil fresh, fun ρ ρ' v hag _ hev => hag y v hev⟩
  | erased =>
    exact ⟨[], .nil fresh, fun _ _ _ _ _ hev => hev⟩
  | lit l =>
    cases l with
    | nat n => exact ⟨[], .nil fresh, fun _ _ _ _ _ hev => hev⟩
    | str s =>
      obtain ⟨fnId, hlu, hso⟩ := lowerStrFns_lookup_of_mem (hcov s rfl)
      refine ⟨[(fresh, s)], ?_, fun ρ ρ' v _ hbs hev => ?_⟩
      · simp only [hoistArg, hlu]
        exact .cons hso (Nat.le_refl _) (.nil (fresh + 1))
      · simp only [Own.evalArg, Option.some.injEq] at hev
        subst hev
        simp only [hoistArg, hlu, Own.evalArg]
        exact hbs fresh s (by simp)

theorem hoistArgs_spec {P : Cfg.Program} :
    ∀ (fresh : Nat) (as : List Fir.Arg),
      (∀ s, .lit (.str s) ∈ as → s ∈ Rt.lowerStrs P) →
      let r := hoistArgs (Rt.lowerStrFns P) fresh as
      ∃ bs, StrBinds P fresh r.2.2 r.1 bs ∧
        ∀ (ρ ρ' : Own.Env) (vs : List Own.RVal),
          (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
          (∀ t s, (t, s) ∈ bs → ρ'.get? t = some (.lit (.str s))) →
          Own.evalArgs ρ as = some vs → Own.evalArgs ρ' r.2.1 = some vs
  | fresh, [], _ => ⟨[], .nil fresh, fun _ _ _ _ _ hev => hev⟩
  | fresh, a :: as, hcov => by
    obtain ⟨bs1, hb1, hev1⟩ := hoistArg_spec (P := P) (fresh := fresh) (a := a)
      (fun s hs => hcov s (by simp [hs]))
    let r1 := hoistArg (Rt.lowerStrFns P) fresh a
    obtain ⟨bs2, hb2, hev2⟩ := hoistArgs_spec r1.2.2 as (fun s hs => hcov s (by simp [hs]))
    refine ⟨bs1 ++ bs2, ?_, fun ρ ρ' vs hag hbs hev => ?_⟩
    · simpa [hoistArgs, r1] using hb1.append hb2
    · simp only [Own.evalArgs] at hev
      cases ha : Own.evalArg ρ a with
      | none => simp [ha] at hev
      | some v =>
        cases has : Own.evalArgs ρ as with
        | none => simp [ha, has] at hev
        | some vs' =>
          simp only [ha, has, Option.some.injEq] at hev
          subst hev
          have h1 := hev1 ρ ρ' v hag (fun t s hm => hbs t s (List.mem_append_left _ hm)) ha
          have h2 := hev2 ρ ρ' vs' hag (fun t s hm => hbs t s (List.mem_append_right _ hm)) has
          simp [hoistArgs, r1, Own.evalArgs, h1, h2]

theorem hoistRhs_spec {P : Cfg.Program} {fresh : Nat} {r : Own.Rhs}
    (hcov : ∀ s ∈ collectRhs [] r, s ∈ Rt.lowerStrs P) :
    let res := hoistRhs (Rt.lowerStrFns P) fresh r
    ∃ bs, StrBinds P fresh res.2.2 res.1 bs ∧
      (∀ g as, r = .fir (.call g as) →
        ∃ as', res.2.1 = .fir (.call g as') ∧
          ∀ (ρ ρ' : Own.Env) (vs : List Own.RVal),
            (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
            (∀ t s, (t, s) ∈ bs → ρ'.get? t = some (.lit (.str s))) →
            Own.evalArgs ρ as = some vs → Own.evalArgs ρ' as' = some vs) ∧
      ((∀ g as, r ≠ .fir (.call g as)) →
        (∀ g as, res.2.1 ≠ .fir (.call g as)) ∧
        ∀ (T : Own.Tables) (ρ ρ' : Own.Env) (H : Own.Heap),
          (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
          (∀ t s, (t, s) ∈ bs → ρ'.get? t = some (.lit (.str s))) →
          ∀ resOut, Own.evalRhs .immortal T ρ H r = resOut → resOut ≠ .stuck →
            Own.evalRhs .immortal T ρ' H res.2.1 = resOut) := by
  cases r with
  | fir e =>
    cases e with
    | arg a =>
      obtain ⟨bs, hb, hev⟩ := hoistArg_spec (P := P) (fresh := fresh) (a := a)
        (fun s hs => hcov s ((mem_collectArg [] a).2 s hs))
      refine ⟨bs, hb, (fun _ _ h => nomatch h), fun _ => ⟨(fun _ _ h => nomatch h), fun T ρ ρ' H hag hbs resOut hr hns => ?_⟩⟩
      simp only [hoistRhs, Own.evalRhs] at hr ⊢
      cases ha : Own.evalArg ρ a with
      | none => simp [ha] at hr; subst hr; exact absurd rfl hns
      | some v =>
        simp only [ha] at hr
        rw [hev ρ ρ' v hag hbs ha]
        exact hr
    | prim op as =>
      obtain ⟨bs, hb, hev⟩ := hoistArgs_spec (P := P) fresh as
        (fun s hs => hcov s ((mem_collectArgs [] as).2 s hs))
      refine ⟨bs, hb, (fun _ _ h => nomatch h), fun _ => ⟨(fun _ _ h => nomatch h), fun T ρ ρ' H hag hbs resOut hr hns => ?_⟩⟩
      simp only [hoistRhs, Own.evalRhs] at hr ⊢
      cases ha : Own.evalArgs ρ as with
      | none => simp [ha] at hr; subst hr; exact absurd rfl hns
      | some vs =>
        simp only [ha] at hr
        rw [hev ρ ρ' vs hag hbs ha]
        exact hr
    | call g as =>
      obtain ⟨bs, hb, hev⟩ := hoistArgs_spec (P := P) fresh as
        (fun s hs => hcov s ((mem_collectArgs [] as).2 s hs))
      refine ⟨bs, hb, fun g' as' heq => ?_, fun hnc => absurd rfl (hnc g as)⟩
      cases heq
      exact ⟨(hoistArgs (Rt.lowerStrFns P) fresh as).2.1, rfl, hev⟩
    | ctor c as =>
      obtain ⟨bs, hb, _⟩ := hoistArgs_spec (P := P) fresh as
        (fun s hs => hcov s ((mem_collectArgs [] as).2 s hs))
      refine ⟨bs, hb, (fun _ _ h => nomatch h), fun _ => ⟨(fun _ _ h => nomatch h), fun T ρ ρ' H _ _ resOut hr hns => ?_⟩⟩
      simp only [Own.evalRhs] at hr; subst hr; exact absurd rfl hns
    | proj y c i =>
      refine ⟨[], .nil fresh, (fun _ _ h => nomatch h), fun _ => ⟨(fun _ _ h => nomatch h), fun T ρ ρ' H _ _ resOut hr hns => ?_⟩⟩
      simp only [Own.evalRhs] at hr; subst hr; exact absurd rfl hns
  | alloc c as k =>
    obtain ⟨bs, hb, hev⟩ := hoistArgs_spec (P := P) fresh as
      (fun s hs => hcov s ((mem_collectArgs [] as).2 s hs))
    refine ⟨bs, hb, (fun _ _ h => nomatch h), fun _ => ⟨(fun _ _ h => nomatch h), fun T ρ ρ' H hag hbs resOut hr hns => ?_⟩⟩
    simp only [hoistRhs, Own.evalRhs] at hr ⊢
    cases ha : Own.evalArgs ρ as with
    | none => simp [ha] at hr; subst hr; exact absurd rfl hns
    | some vs =>
      simp only [ha] at hr
      rw [hev ρ ρ' vs hag hbs ha]
      exact hr
  | proj y c i =>
    refine ⟨[], .nil fresh, (fun _ _ h => nomatch h), fun _ => ⟨(fun _ _ h => nomatch h), fun T ρ ρ' H hag _ resOut hr hns => ?_⟩⟩
    simp only [hoistRhs, Own.evalRhs] at hr ⊢
    cases hy : ρ.get? y with
    | none => simp [hy] at hr; subst hr; exact absurd rfl hns
    | some v =>
      simp only [hy] at hr
      rw [hag y v hy]
      exact hr

theorem hoistEdge_spec {P : Cfg.Program} {fresh : Nat} {e : Cfg.Edge}
    (hcov : ∀ s ∈ collectEdge [] e, s ∈ Rt.lowerStrs P) :
    let res := hoistEdge (Rt.lowerStrFns P) fresh e
    res.2.1.target = e.target ∧ res.2.1.back = e.back ∧
    ∃ bs, StrBinds P fresh res.2.2 res.1 bs ∧
      ∀ (ρ ρ' : Own.Env) (vs : List Own.RVal),
        (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
        (∀ t s, (t, s) ∈ bs → ρ'.get? t = some (.lit (.str s))) →
        Own.evalArgs ρ e.args = some vs → Own.evalArgs ρ' res.2.1.args = some vs := by
  obtain ⟨bs, hb, hev⟩ := hoistArgs_spec (P := P) fresh e.args
    (fun s hs => hcov s ((mem_collectArgs [] e.args).2 s hs))
  exact ⟨rfl, rfl, bs, hb, hev⟩

theorem hoistAlts_spec {P : Cfg.Program} :
    ∀ (fresh : Nat) (alts : List (Key.CtorKey × Cfg.Edge)),
      (∀ s ∈ alts.foldl (fun a (_, e) => collectEdge a e) [], s ∈ Rt.lowerStrs P) →
      let res := hoistAlts (Rt.lowerStrFns P) fresh alts
      res.2.1.map Prod.fst = alts.map Prod.fst ∧
      (∀ (i : Nat) (e : Key.CtorKey × Cfg.Edge), alts[i]? = some e →
        ∃ (e' : Key.CtorKey × Cfg.Edge), res.2.1[i]? = some e' ∧ e'.1 = e.1 ∧
        e'.2.target = e.2.target ∧ e'.2.back = e.2.back) ∧
      ∃ bs, StrBinds P fresh res.2.2 res.1 bs ∧
        ∀ (key : Key.CtorKey) (d d' : Option Cfg.Edge) (e : Cfg.Edge),
          Cfg.selectEdge key alts d = some e →
          (∃ e', Cfg.selectEdge key res.2.1 d' = some e' ∧ e'.target = e.target ∧ e'.back = e.back ∧
            ∀ (ρ ρ' : Own.Env) (vs : List Own.RVal),
              (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
              (∀ t s, (t, s) ∈ bs → ρ'.get? t = some (.lit (.str s))) →
              Own.evalArgs ρ e.args = some vs → Own.evalArgs ρ' e'.args = some vs) ∨
          (d = some e ∧ Cfg.selectEdge key res.2.1 d' = d')
  | fresh, [], _ => by
    refine ⟨rfl, fun _ _ h => by simp at h, [], .nil fresh, ?_⟩
    intro key d d' e hsel
    simp only [Cfg.selectEdge] at hsel ⊢
    exact .inr ⟨hsel, rfl⟩
  | fresh, (k, e0) :: rest, hcov => by
    have hcov0 : ∀ s ∈ collectEdge [] e0, s ∈ Rt.lowerStrs P := by
      intro s hs
      exact hcov s (mem_collectAlts (collectEdge [] e0) rest s hs)
    have hcovR : ∀ s ∈ rest.foldl (fun a (_, e) => collectEdge a e) [], s ∈ Rt.lowerStrs P := by
      intro s hs
      have hlift : ∀ (al : List (Key.CtorKey × Cfg.Edge)) (a1 a2 : List String),
          (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ al.foldl (fun a (_, e) => collectEdge a e) a1,
            t ∈ al.foldl (fun a (_, e) => collectEdge a e) a2 := by
        intro al
        induction al with
        | nil => intro _ _ hsub; exact hsub
        | cons p al ih =>
          intro a1 a2 hsub
          apply ih
          intro t ht
          have hliftArgs : ∀ (as : List Fir.Arg) (x1 x2 : List String),
              (∀ u ∈ x1, u ∈ x2) → ∀ u ∈ collectArgs x1 as, u ∈ collectArgs x2 as := by
            intro as
            induction as with
            | nil => intro _ _ h; exact h
            | cons a as iha =>
              intro x1 x2 hx
              apply iha
              intro u hu
              cases a with
              | lit l =>
                cases l with
                | str st =>
                  rw [collectArg, mem_addStr_iff] at hu ⊢
                  rcases hu with hu | rfl
                  · exact .inl (hx u hu)
                  · exact .inr rfl
                | nat _ => exact hx u hu
              | var _ | erased => exact hx u hu
          exact hliftArgs p.2.args a1 a2 hsub t ht
      exact hcov s (hlift rest [] (collectEdge [] e0) (fun _ h => nomatch h) s hs)
    obtain ⟨ht0, hb0, bs1, hsb1, hev1⟩ := hoistEdge_spec (P := P) (fresh := fresh) (e := e0) hcov0
    let r1 := hoistEdge (Rt.lowerStrFns P) fresh e0
    obtain ⟨hkeysR, hgetR, bs2, hsb2, hselR⟩ := hoistAlts_spec r1.2.2 rest hcovR
    refine ⟨by simp [hoistAlts, r1, hkeysR], ?_, bs1 ++ bs2, by simpa [hoistAlts, r1] using hsb1.append hsb2, ?_⟩
    · intro i e hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨(k, r1.2.1), by simp [hoistAlts, r1], rfl, ht0, hb0⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        obtain ⟨e', he', hk', ht', hb'⟩ := hgetR i e hi
        exact ⟨e', by simp [hoistAlts, r1, he'], hk', ht', hb'⟩
    · intro key d d' e hsel
      simp only [Cfg.selectEdge] at hsel
      by_cases hk : k = key
      · simp only [hk, ↓reduceIte, Option.some.injEq] at hsel
        subst hsel
        refine .inl ⟨r1.2.1, by simp [hoistAlts, r1, Cfg.selectEdge, hk], ht0, hb0, fun ρ ρ' vs hag hbs ha => ?_⟩
        exact hev1 ρ ρ' vs hag (fun t s hm => hbs t s (List.mem_append_left _ hm)) ha
      · simp only [hk, ↓reduceIte] at hsel
        rcases hselR key d d' e hsel with ⟨e', he', ht', hb', hev'⟩ | ⟨hd, hselD'⟩
        · exact .inl ⟨e', by simp [hoistAlts, r1, Cfg.selectEdge, hk, he'], ht', hb',
            fun ρ ρ' vs hag hbs ha => hev' ρ ρ' vs hag (fun t s hm => hbs t s (List.mem_append_right _ hm)) ha⟩
        · exact .inr ⟨hd, by simp [hoistAlts, r1, Cfg.selectEdge, hk, hselD']⟩

theorem hoistOptEdge_spec {P : Cfg.Program} {fresh : Nat} {d : Option Cfg.Edge}
    (hcov : ∀ e, d = some e → ∀ s ∈ collectEdge [] e, s ∈ Rt.lowerStrs P) :
    let res := hoistOptEdge (Rt.lowerStrFns P) fresh d
    (d = none → res.2.1 = none) ∧
    ∃ bs, StrBinds P fresh res.2.2 res.1 bs ∧
      ∀ e, d = some e → ∃ e', res.2.1 = some e' ∧ e'.target = e.target ∧ e'.back = e.back ∧
        ∀ (ρ ρ' : Own.Env) (vs : List Own.RVal),
          (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
          (∀ t s, (t, s) ∈ bs → ρ'.get? t = some (.lit (.str s))) →
          Own.evalArgs ρ e.args = some vs → Own.evalArgs ρ' e'.args = some vs := by
  cases d with
  | none => exact ⟨fun _ => rfl, [], .nil fresh, fun _ h => nomatch h⟩
  | some e =>
    obtain ⟨ht, hb, bs, hsb, hev⟩ := hoistEdge_spec (P := P) (fresh := fresh) (e := e) (hcov e rfl)
    refine ⟨(fun h => nomatch h), bs, hsb, fun e' he' => ?_⟩
    cases he'
    exact ⟨_, rfl, ht, hb, hev⟩

theorem hoistTerm_spec {P : Cfg.Program} {fresh : Nat} {tm : Cfg.Term}
    (hcov : ∀ s ∈ collectTerm [] tm, s ∈ Rt.lowerStrs P) :
    let res := hoistTerm (Rt.lowerStrFns P) fresh tm
    ∃ bs, StrBinds P fresh res.2.2 res.1 bs ∧
      (∀ e, tm = .jump e → ∃ e', res.2.1 = .jump e' ∧ e'.target = e.target ∧ e'.back = e.back ∧
        ∀ (ρ ρ' : Own.Env) (vs : List Own.RVal),
          (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
          (∀ t s, (t, s) ∈ bs → ρ'.get? t = some (.lit (.str s))) →
          Own.evalArgs ρ e.args = some vs → Own.evalArgs ρ' e'.args = some vs) ∧
      (∀ x alts d, tm = .switch x alts d →
        ∃ alts' d', res.2.1 = .switch x alts' d' ∧ alts'.map Prod.fst = alts.map Prod.fst ∧
          (∀ key e, Cfg.selectEdge key alts d = some e →
            ∃ e', Cfg.selectEdge key alts' d' = some e' ∧ e'.target = e.target ∧ e'.back = e.back ∧
              ∀ (ρ ρ' : Own.Env) (vs : List Own.RVal),
                (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
                (∀ t s, (t, s) ∈ bs → ρ'.get? t = some (.lit (.str s))) →
                Own.evalArgs ρ e.args = some vs → Own.evalArgs ρ' e'.args = some vs)) ∧
      (∀ a, tm = .ret a → ∃ a', res.2.1 = .ret a' ∧
        ∀ (ρ ρ' : Own.Env) (v : Own.RVal),
          (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
          (∀ t s, (t, s) ∈ bs → ρ'.get? t = some (.lit (.str s))) →
          Own.evalArg ρ a = some v → Own.evalArg ρ' a' = some v) ∧
      (∀ g as, tm = .tcall g as → ∃ as', res.2.1 = .tcall g as' ∧
        ∀ (ρ ρ' : Own.Env) (vs : List Own.RVal),
          (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
          (∀ t s, (t, s) ∈ bs → ρ'.get? t = some (.lit (.str s))) →
          Own.evalArgs ρ as = some vs → Own.evalArgs ρ' as' = some vs) ∧
      (tm = .trap → res.2.1 = .trap) := by
  cases tm with
  | jump e =>
    obtain ⟨ht, hb, bs, hsb, hev⟩ := hoistEdge_spec (P := P) (fresh := fresh) (e := e) hcov
    refine ⟨bs, hsb, (fun e' he' => by cases he'; exact ⟨_, rfl, ht, hb, hev⟩),
      (fun _ _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h), (fun h => nomatch h)⟩
  | switch x alts d =>
    have hcovA : ∀ s ∈ alts.foldl (fun a (_, e) => collectEdge a e) [], s ∈ Rt.lowerStrs P := by
      intro s hs
      apply hcov s
      simp only [collectTerm]
      cases d with
      | none => exact hs
      | some e => exact mem_collectEdge _ e s hs
    have hcovD : ∀ e, d = some e → ∀ s ∈ collectEdge [] e, s ∈ Rt.lowerStrs P := by
      intro e hd s hs
      apply hcov s
      simp only [collectTerm, hd]
      have hliftArgs : ∀ (as : List Fir.Arg) (x1 x2 : List String),
          (∀ u ∈ x1, u ∈ x2) → ∀ u ∈ collectArgs x1 as, u ∈ collectArgs x2 as := by
        intro as
        induction as with
        | nil => intro _ _ h; exact h
        | cons a as iha =>
          intro x1 x2 hx
          apply iha
          intro u hu
          cases a with
          | lit l =>
            cases l with
            | str st =>
              rw [collectArg, mem_addStr_iff] at hu ⊢
              rcases hu with hu | rfl
              · exact .inl (hx u hu)
              · exact .inr rfl
            | nat _ => exact hx u hu
          | var _ | erased => exact hx u hu
      exact hliftArgs e.args [] _ (fun _ h => nomatch h) s hs
    obtain ⟨hkeys, _, bs1, hsb1, hselA⟩ := hoistAlts_spec (P := P) fresh alts hcovA
    let r1 := hoistAlts (Rt.lowerStrFns P) fresh alts
    obtain ⟨hdn, bs2, hsb2, hselD⟩ := hoistOptEdge_spec (P := P) (fresh := r1.2.2) (d := d) hcovD
    refine ⟨bs1 ++ bs2, by simpa [hoistTerm, r1] using hsb1.append hsb2,
      (fun _ h => nomatch h), (fun x' alts' d' heq => ?_),
      (fun _ h => nomatch h), (fun _ _ h => nomatch h), (fun h => nomatch h)⟩
    cases heq
    let d1 := (hoistOptEdge (Rt.lowerStrFns P) r1.2.2 d).2.1
    refine ⟨r1.2.1, d1, rfl, hkeys, fun key e hsel => ?_⟩
    rcases hselA key d d1 e hsel with ⟨e', he', ht', hb', hevA⟩ | ⟨hd, hselD'⟩
    · exact ⟨e', he', ht', hb', fun ρ ρ' vs hag hbs ha =>
        hevA ρ ρ' vs hag (fun t s hm => hbs t s (List.mem_append_left _ hm)) ha⟩
    · obtain ⟨e', hd', ht', hb', hevD⟩ := hselD e hd
      exact ⟨e', by rw [hselD']; exact hd', ht', hb', fun ρ ρ' vs hag hbs ha =>
        hevD ρ ρ' vs hag (fun t s hm => hbs t s (List.mem_append_right _ hm)) ha⟩
  | ret a =>
    obtain ⟨bs, hsb, hev⟩ := hoistArg_spec (P := P) (fresh := fresh) (a := a)
      (fun s hs => hcov s ((mem_collectArg [] a).2 s hs))
    refine ⟨bs, hsb, (fun _ h => nomatch h), (fun _ _ _ h => nomatch h),
      (fun a' ha' => by cases ha'; exact ⟨_, rfl, hev⟩),
      (fun _ _ h => nomatch h), (fun h => nomatch h)⟩
  | tcall g as =>
    obtain ⟨bs, hsb, hev⟩ := hoistArgs_spec (P := P) fresh as
      (fun s hs => hcov s ((mem_collectArgs [] as).2 s hs))
    refine ⟨bs, hsb, (fun _ h => nomatch h), (fun _ _ _ h => nomatch h),
      (fun _ h => nomatch h), (fun g' as' heq => by cases heq; exact ⟨_, rfl, hev⟩),
      (fun h => nomatch h)⟩
  | trap =>
    exact ⟨[], .nil fresh, (fun _ h => nomatch h), (fun _ _ _ h => nomatch h),
      (fun _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ => rfl)⟩

/-! ### Structural properties of `hoistFun` & `hoistStrings` -/

theorem hoistArg_fresh_le (strFns : List (String × Fir.FunId)) (fresh : Nat) (a : Fir.Arg) :
    fresh ≤ (hoistArg strFns fresh a).2.2 := by
  cases a with
  | lit l =>
    cases l with
    | str s => unfold hoistArg; cases h : strFns.lookup s <;> simp [h]
    | nat _ => exact Nat.le_refl _
  | var _ | erased => exact Nat.le_refl _

theorem hoistArgs_fresh_le (strFns : List (String × Fir.FunId)) :
    ∀ (fresh : Nat) (as : List Fir.Arg), fresh ≤ (hoistArgs strFns fresh as).2.2
  | _, [] => Nat.le_refl _
  | fresh, a :: as =>
    Nat.le_trans (hoistArg_fresh_le strFns fresh a) (hoistArgs_fresh_le strFns _ as)

theorem hoistRhs_fresh_le (strFns : List (String × Fir.FunId)) (fresh : Nat) (r : Own.Rhs) :
    fresh ≤ (hoistRhs strFns fresh r).2.2 := by
  cases r with
  | fir e =>
    cases e with
    | arg a => exact hoistArg_fresh_le strFns fresh a
    | prim _ as | call _ as | ctor _ as => exact hoistArgs_fresh_le strFns fresh as
    | proj _ _ _ => exact Nat.le_refl _
  | alloc _ as _ => exact hoistArgs_fresh_le strFns fresh as
  | proj _ _ _ => exact Nat.le_refl _

theorem hoistInstr_fresh_le (strFns : List (String × Fir.FunId)) (fresh : Nat) (i : Cfg.Instr) :
    fresh ≤ (hoistInstr strFns fresh i).2 := by
  cases i with | bind _ r => exact hoistRhs_fresh_le strFns fresh r

theorem hoistInstrs_fresh_le (strFns : List (String × Fir.FunId)) :
    ∀ (fresh : Nat) (is : List Cfg.Instr), fresh ≤ (hoistInstrs strFns fresh is).2
  | _, [] => Nat.le_refl _
  | fresh, i :: is =>
    Nat.le_trans (hoistInstr_fresh_le strFns fresh i) (hoistInstrs_fresh_le strFns _ is)

theorem hoistInstrs_append (strFns : List (String × Fir.FunId)) :
    ∀ (fresh : Nat) (is1 is2 : List Cfg.Instr),
      let r1 := hoistInstrs strFns fresh is1
      let r2 := hoistInstrs strFns r1.2 is2
      hoistInstrs strFns fresh (is1 ++ is2) = (r1.1 ++ r2.1, r2.2)
  | fresh, [], is2 => by simp [hoistInstrs]
  | fresh, i :: is1, is2 => by
    simp only [List.cons_append, hoistInstrs]
    have ih := hoistInstrs_append strFns (hoistInstr strFns fresh i).2 is1 is2
    simp only at ih
    rw [ih, List.append_assoc]

theorem hoistEdge_fresh_le (strFns : List (String × Fir.FunId)) (fresh : Nat) (e : Cfg.Edge) :
    fresh ≤ (hoistEdge strFns fresh e).2.2 :=
  hoistArgs_fresh_le strFns fresh e.args

theorem hoistAlts_fresh_le (strFns : List (String × Fir.FunId)) :
    ∀ (fresh : Nat) (alts : List (Key.CtorKey × Cfg.Edge)), fresh ≤ (hoistAlts strFns fresh alts).2.2
  | _, [] => Nat.le_refl _
  | fresh, (_, e) :: rest =>
    Nat.le_trans (hoistEdge_fresh_le strFns fresh e) (hoistAlts_fresh_le strFns _ rest)

theorem hoistOptEdge_fresh_le (strFns : List (String × Fir.FunId)) (fresh : Nat) (d : Option Cfg.Edge) :
    fresh ≤ (hoistOptEdge strFns fresh d).2.2 := by
  cases d with
  | none => exact Nat.le_refl _
  | some e => exact hoistEdge_fresh_le strFns fresh e

theorem hoistTerm_fresh_le (strFns : List (String × Fir.FunId)) (fresh : Nat) (tm : Cfg.Term) :
    fresh ≤ (hoistTerm strFns fresh tm).2.2 := by
  cases tm with
  | jump e => exact hoistEdge_fresh_le strFns fresh e
  | switch _ alts d =>
    exact Nat.le_trans (hoistAlts_fresh_le strFns fresh alts) (hoistOptEdge_fresh_le strFns _ d)
  | ret a => exact hoistArg_fresh_le strFns fresh a
  | tcall _ as => exact hoistArgs_fresh_le strFns fresh as
  | trap => exact Nat.le_refl _

theorem hoistBlock_fresh_le (T : Tables) (uses : NatMap Nat) (strFns : List (String × Fir.FunId))
    (fresh : Nat) (b : Cfg.Block) :
    fresh ≤ (hoistBlock T uses strFns fresh b).2 := by
  unfold hoistBlock
  split
  · exact Nat.le_trans (hoistInstrs_fresh_le strFns fresh _)
      (Nat.le_trans (hoistTerm_fresh_le strFns _ b.term) (hoistInstr_fresh_le strFns _ _))
  · exact Nat.le_trans (hoistInstrs_fresh_le strFns fresh b.body) (hoistTerm_fresh_le strFns _ b.term)

theorem hoistBlocks_length (T : Tables) (uses : NatMap Nat) (strFns : List (String × Fir.FunId)) :
    ∀ (fresh : Nat) (bs : List Cfg.Block),
      (hoistBlocks T uses strFns fresh bs).1.length = bs.length
  | _, [] => rfl
  | fresh, b :: bs => by
    simp [hoistBlocks, hoistBlocks_length T uses strFns _ bs]

theorem hoistBlocks_getElem? (T : Tables) (uses : NatMap Nat) (strFns : List (String × Fir.FunId)) :
    ∀ (fresh : Nat) (bs : List Cfg.Block) (i : Nat) (b : Cfg.Block),
      bs[i]? = some b →
      ∃ f0, fresh ≤ f0 ∧ (hoistBlocks T uses strFns fresh bs).1[i]? = some (hoistBlock T uses strFns f0 b).1
  | _, [], _, _, h => by simp at h
  | fresh, b0 :: bs, 0, b, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨fresh, Nat.le_refl _, rfl⟩
  | fresh, b0 :: bs, i + 1, b, h => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨f0, hle, hget⟩ := hoistBlocks_getElem? T uses strFns (hoistBlock T uses strFns fresh b0).2 bs i b h
    exact ⟨f0, Nat.le_trans (hoistBlock_fresh_le T uses strFns fresh b0) hle, by simpa [hoistBlocks] using hget⟩

theorem hoistBlock_params (T : Tables) (uses : NatMap Nat) (strFns : List (String × Fir.FunId))
    (fresh : Nat) (b : Cfg.Block) :
    (hoistBlock T uses strFns fresh b).1.params = b.params := by
  unfold hoistBlock; split <;> rfl

theorem hoistFun_params (T : Tables) (strFns : List (String × Fir.FunId)) (fd : Cfg.Fun) :
    (hoistFun T strFns fd).params = fd.params := by
  unfold Cfg.Fun.params hoistFun
  cases hb : fd.blocks with
  | nil => simp [hoistBlocks]
  | cons b0 bs => simp [hoistBlocks, hoistBlock_params]

theorem lowerCfg_size (P : Cfg.Program) : (Rt.lowerCfg P).size = P.size := by
  unfold Rt.lowerCfg; split <;> rfl

theorem lowerCfg_tables (P : Cfg.Program) : tables (Rt.lowerCfg P) = tables P := by
  unfold Rt.lowerCfg; split <;> rfl

theorem lowerCfg_known (P : Cfg.Program) : (Rt.lowerCfg P).known = P.known := by
  unfold Rt.lowerCfg; split <;> rfl

theorem lowerCfg_exports (P : Cfg.Program) : (Rt.lowerCfg P).exports = P.exports := by
  unfold Rt.lowerCfg; split <;> rfl

theorem lowerCfg_ctors (P : Cfg.Program) : (Rt.lowerCfg P).ctors = P.ctors := by
  unfold Rt.lowerCfg; split <;> rfl

theorem hoistStrings_fun? {P : Cfg.Program} {strFns : List (String × Fir.FunId)}
    {f : Nat} (hf : f < P.size) :
    (hoistStrings P strFns).fun? f = (P.fun? f).map (hoistFun (tables P) strFns) := by
  unfold hoistStrings Cfg.Program.fun?
  dsimp only
  have aux : ∀ (fs : List Nat) (m : NatMap Cfg.Fun),
      fs.Nodup →
      (fs.foldl (fun acc g => match P.funs.get? g with | some fd => acc.insert g (hoistFun (tables P) strFns fd) | none => acc) m).get? f =
        if f ∈ fs then
          match P.funs.get? f with
          | some fd => some (hoistFun (tables P) strFns fd)
          | none => m.get? f
        else m.get? f := by
    intro fs
    induction fs with
    | nil => intro m _; simp
    | cons g fs ih =>
      intro m hnd
      obtain ⟨hg_not, hnd'⟩ := List.nodup_cons.1 hnd
      simp only [List.foldl_cons]
      rw [ih _ hnd']
      by_cases hfg : f = g
      · subst hfg
        simp only [hg_not, ↓reduceIte, List.mem_cons, true_or]
        cases hpg : P.funs.get? f with
        | none => rfl
        | some fd => simp [NatMap.get?_insert]
      · simp only [List.mem_cons, hfg, false_or]
        by_cases hmem : f ∈ fs
        · simp only [hmem, ↓reduceIte]
          cases P.funs.get? f with
          | some fd => rfl
          | none =>
            cases P.funs.get? g with
            | none => rfl
            | some fd' => exact NatMap.get?_insert_ne _ _ hfg
        · simp only [hmem, ↓reduceIte]
          cases P.funs.get? g with
          | none => rfl
          | some fd' => exact NatMap.get?_insert_ne _ _ hfg
  have h := aux (List.range P.size) P.funs List.nodup_range
  simp only [List.mem_range.2 hf, ↓reduceIte] at h
  change (List.foldl (fun acc g => match P.funs.get? g with | some fd => acc.insert g (hoistFun (tables P) strFns fd) | none => acc) P.funs (List.range P.size)).get? f = _
  rw [h]
  cases hpf : P.funs.get? f with
  | none => rfl
  | some fd => rfl

/-- `hoistStrings` preserves `f < P.size` density. -/
theorem hoistStrings_fun?_none {P : Cfg.Program} {strFns : List (String × Fir.FunId)}
    {f : Nat} (hf : ¬ f < P.size) (hnone : P.fun? f = none) :
    (hoistStrings P strFns).fun? f = none := by
  unfold hoistStrings Cfg.Program.fun?
  have aux : ∀ (fs : List Nat) (m : NatMap Cfg.Fun),
      f ∉ fs → m.get? f = none →
      (fs.foldl (fun acc g => match P.fun? g with | some fd => acc.insert g (hoistFun (tables P) strFns fd) | none => acc) m).get? f = none := by
    intro fs
    induction fs with
    | nil => intro _ _ hm; exact hm
    | cons g fs ih =>
      intro m hnot hm
      simp only [List.foldl_cons]
      have hne : f ≠ g := fun h => hnot (by simp [h])
      apply ih _ (fun h => hnot (by simp [h]))
      cases P.fun? g with
      | none => exact hm
      | some fd' => rw [NatMap.get?_insert_ne _ _ hne]; exact hm
  exact aux (List.range P.size) P.funs (by simp [hf]) hnone

/-- `hoistStrings` preserves `Cfg.Ordered` (edge targets and `back` flags are identical). -/
theorem hoistBlock_edges_eq (T : Tables) (uses : NatMap Nat) (strFns : List (String × Fir.FunId))
    (fresh : Nat) (b : Cfg.Block) :
    ∀ e ∈ b.term.edges, ∃ e' ∈ (hoistBlock T uses strFns fresh b).1.term.edges,
      e'.target = e.target ∧ e'.back = e.back := by
  have hterm : (hoistBlock T uses strFns fresh b).1.term =
      (hoistTerm strFns (match fusable T uses b, unsnoc b.body with
        | some _, some (init, _) => (hoistInstrs strFns fresh init).2
        | _, _ => (hoistInstrs strFns fresh b.body).2) b.term).2.1 := by
    unfold hoistBlock
    cases fusable T uses b <;> cases unsnoc b.body <;> rfl
  rw [hterm]
  generalize (match fusable T uses b, unsnoc b.body with
    | some _, some (init, _) => (hoistInstrs strFns fresh init).2
    | _, _ => (hoistInstrs strFns fresh b.body).2) = f1
  cases htm : b.term with
  | jump e0 =>
    intro e he
    simp only [Cfg.Term.edges, List.mem_singleton] at he
    subst he
    exact ⟨(hoistEdge strFns f1 e).2.1, by simp [hoistTerm, Cfg.Term.edges], rfl, rfl⟩
  | switch x alts d =>
    intro e he
    simp only [Cfg.Term.edges, List.mem_append, List.mem_map, Option.mem_toList] at he
    simp only [hoistTerm, Cfg.Term.edges, List.mem_append, List.mem_map, Option.mem_toList]
    rcases he with ⟨⟨k, e0⟩, hmem, rfl⟩ | hd
    · have aux : ∀ (fr : Nat) (al : List (Key.CtorKey × Cfg.Edge)),
          (k, e0) ∈ al → ∃ e', (k, e') ∈ (hoistAlts strFns fr al).2.1 ∧
            e'.target = e0.target ∧ e'.back = e0.back := by
        intro fr al
        induction al generalizing fr with
        | nil => intro h; cases h
        | cons p al ih =>
          intro h
          rcases List.mem_cons.1 h with rfl | h'
          · exact ⟨(hoistEdge strFns fr e0).2.1, by simp [hoistAlts], rfl, rfl⟩
          · obtain ⟨e', he', ht, hb⟩ := ih (hoistEdge strFns fr p.2).2.2 h'
            exact ⟨e', by simp [hoistAlts, he'], ht, hb⟩
      obtain ⟨e', he', ht, hb⟩ := aux f1 alts hmem
      exact ⟨e', .inl ⟨(k, e'), he', rfl⟩, ht, hb⟩
    · subst hd
      exact ⟨(hoistEdge strFns (hoistAlts strFns f1 alts).2.2 e).2.1, .inr (by simp [hoistOptEdge]), rfl, rfl⟩
  | ret _ | tcall _ _ | trap => intro _ h; simp [Cfg.Term.edges] at h

/-- `hoistArg` preserves occurrences of variables `< fresh` (only replaces `.lit (.str _)` with `≥ fresh`). -/
private theorem argVars_hoistArg_lt (strFns : List (String × Fir.FunId)) (fresh : Nat) (a : Fir.Arg) :
    (Cfg.Check.argVars [(hoistArg strFns fresh a).2.1]).filter (· < fresh) =
      (Cfg.Check.argVars [a]).filter (· < fresh) ∧
    (∀ y ∈ ((hoistArg strFns fresh a).1.flatMap instrUses), fresh ≤ y) := by
  cases a with
  | var y => simp [hoistArg]
  | erased => simp [hoistArg]
  | lit l =>
    cases l with
    | nat _ => simp [hoistArg]
    | str s =>
      unfold hoistArg
      cases hl : strFns.lookup s with
      | none => simp [hl, Cfg.Check.argVars]
      | some fnId => simp [hl, Cfg.Check.argVars, instrUses, Cfg.Check.rhsVars]

private theorem argVars_hoistArgs_lt (strFns : List (String × Fir.FunId)) :
    ∀ (fresh bound : Nat) (as : List Fir.Arg), bound ≤ fresh →
      (Cfg.Check.argVars (hoistArgs strFns fresh as).2.1).filter (· < bound) =
        (Cfg.Check.argVars as).filter (· < bound) ∧
      (∀ y ∈ ((hoistArgs strFns fresh as).1.flatMap instrUses), bound ≤ y)
  | fresh, bound, [], _ => by simp [hoistArgs, Cfg.Check.argVars]
  | fresh, bound, a :: as, hle => by
    have h1 := argVars_hoistArg_lt strFns fresh a
    have hle1 : bound ≤ (hoistArg strFns fresh a).2.2 :=
      Nat.le_trans hle (hoistArg_fresh_le strFns fresh a)
    have h2 := argVars_hoistArgs_lt strFns (hoistArg strFns fresh a).2.2 bound as hle1
    have harg1 : (Cfg.Check.argVars [(hoistArg strFns fresh a).2.1]).filter (· < bound) =
        (Cfg.Check.argVars [a]).filter (· < bound) := by
      cases a with
      | var y => simp [hoistArg, Cfg.Check.argVars]
      | erased => simp [hoistArg, Cfg.Check.argVars]
      | lit l =>
        cases l with
        | nat _ => simp [hoistArg, Cfg.Check.argVars]
        | str s =>
          unfold hoistArg
          cases hl : strFns.lookup s with
          | none => simp [hl, Cfg.Check.argVars]
          | some fnId => simp [hl, Cfg.Check.argVars, show ¬ fresh < bound by omega]
    have hcons : ∀ (x : Fir.Arg) (xs : List Fir.Arg),
        Cfg.Check.argVars (x :: xs) = Cfg.Check.argVars [x] ++ Cfg.Check.argVars xs := by
      intro x xs; cases x <;> simp [Cfg.Check.argVars]
    refine ⟨?_, ?_⟩
    · simp only [hoistArgs]
      rw [hcons _ _, List.filter_append, harg1, h2.1, ← List.filter_append, ← hcons]
    · simp only [hoistArgs, List.flatMap_append, List.mem_append]
      intro y hy
      rcases hy with hy1 | hy2
      · exact Nat.le_trans hle (h1.2 y hy1)
      · exact h2.2 y hy2

private theorem useCount_eq_count {xs : List Nat} {x : Nat} :
    ∀ (m : NatMap Nat),
      (xs.foldl (fun acc y => acc.insert y (acc.getD y 0 + 1)) m).getD x 0 =
        m.getD x 0 + xs.count x := by
  induction xs with
  | nil => intro m; simp
  | cons y ys ih =>
    intro m
    simp only [List.foldl_cons, List.count_cons, ih]
    by_cases hxy : y = x
    · subst hxy
      simp [NatMap.getD, NatMap.get?_insert]
      omega
    · have hne : x ≠ y := Ne.symm hxy
      have hbeq : (y == x) = false := beq_false_of_ne hxy
      simp [NatMap.getD, NatMap.get?_insert_ne _ _ hne, hbeq]

private theorem count_eq_of_filter_lt {xs ys : List Nat} {bound x : Nat}
    (hx : x < bound) (h : xs.filter (· < bound) = ys.filter (· < bound)) :
    xs.count x = ys.count x := by
  have hcnt : ∀ (zs : List Nat), zs.count x = (zs.filter (· < bound)).count x := by
    intro zs
    induction zs with
    | nil => rfl
    | cons a as ih =>
      simp only [List.filter_cons, List.count_cons]
      by_cases ha : a < bound
      · simp only [ha, decide_true, ↓reduceIte, List.count_cons, ih]
      · have hne : (a == x) = false := beq_false_of_ne (by omega)
        simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte, hne, ih, Nat.add_zero]
  rw [hcnt xs, h, ← hcnt ys]

private theorem hoistBlock_uses_lt (T : Tables) (uses : NatMap Nat)
    (strFns : List (String × Fir.FunId)) (fresh bound : Nat) (b : Cfg.Block) (hle : bound ≤ fresh) :
    (blockUses (hoistBlock T uses strFns fresh b).1).filter (· < bound) =
      (blockUses b).filter (· < bound) := by
  have hRhs : ∀ (fr : Nat) (r : Own.Rhs), bound ≤ fr →
      ((hoistRhs strFns fr r).1.flatMap instrUses ++ Cfg.Check.rhsVars (hoistRhs strFns fr r).2.1).filter (· < bound) =
        (Cfg.Check.rhsVars r).filter (· < bound) := by
    intro fr r hfr
    have hpre_nil : ∀ {is : List Cfg.Instr}, (∀ y ∈ is.flatMap instrUses, bound ≤ y) →
        (is.flatMap instrUses).filter (· < bound) = [] := by
      intro is his
      rw [List.filter_eq_nil_iff]
      intro y hy; simp [show ¬ y < bound by have := his y hy; omega]
    cases r with
    | fir e =>
      cases e with
      | arg a =>
        have h := argVars_hoistArgs_lt strFns fr bound [a] hfr
        have harg : (Cfg.Check.argVars [(hoistArg strFns fr a).2.1]).filter (· < bound) =
            (Cfg.Check.argVars [a]).filter (· < bound) := by
          cases a with
          | var y => simp [hoistArg, Cfg.Check.argVars]
          | erased => simp [hoistArg, Cfg.Check.argVars]
          | lit l =>
            cases l with
            | nat _ => simp [hoistArg, Cfg.Check.argVars]
            | str s =>
              unfold hoistArg; cases hl : strFns.lookup s with
              | none => simp [hl, Cfg.Check.argVars]
              | some _ => simp [hl, Cfg.Check.argVars, show ¬ fr < bound by omega]
        have hpre : ((hoistArg strFns fr a).1.flatMap instrUses).filter (· < bound) = [] := by
          apply hpre_nil
          intro y hy
          exact Nat.le_trans hfr ((argVars_hoistArg_lt strFns fr a).2 y hy)
        simp [hoistRhs, Cfg.Check.rhsVars, List.filter_append, hpre, harg]
      | prim _ as | call _ as | ctor _ as =>
        have h := argVars_hoistArgs_lt strFns fr bound as hfr
        simp [hoistRhs, Cfg.Check.rhsVars, List.filter_append, hpre_nil h.2, h.1]
      | proj _ _ _ => simp [hoistRhs]
    | alloc _ as _ =>
      have h := argVars_hoistArgs_lt strFns fr bound as hfr
      simp [hoistRhs, Cfg.Check.rhsVars, List.filter_append, hpre_nil h.2, h.1]
    | proj _ _ _ => simp [hoistRhs]
  have hInstr : ∀ (fr : Nat) (i : Cfg.Instr), bound ≤ fr →
      ((hoistInstr strFns fr i).1.flatMap instrUses).filter (· < bound) =
        (instrUses i).filter (· < bound) := by
    intro fr i hfr
    cases i with
    | bind x r =>
      simpa [hoistInstr, instrUses, List.flatMap_append] using hRhs fr r hfr
  have hInstrs : ∀ (fr : Nat) (is : List Cfg.Instr), bound ≤ fr →
      ((hoistInstrs strFns fr is).1.flatMap instrUses).filter (· < bound) =
        (is.flatMap instrUses).filter (· < bound) := by
    intro fr is
    induction is generalizing fr with
    | nil => intro _; simp [hoistInstrs]
    | cons i is ih =>
      intro hfr
      simp only [hoistInstrs, List.flatMap_append, List.flatMap_cons, List.filter_append]
      rw [hInstr fr i hfr, ih _ (Nat.le_trans hfr (hoistInstr_fresh_le strFns fr i))]
  have hTerm : ∀ (fr : Nat) (tm : Cfg.Term), bound ≤ fr →
      ((hoistTerm strFns fr tm).1.flatMap instrUses).filter (· < bound) = [] ∧
      (Cfg.Check.termVars (hoistTerm strFns fr tm).2.1).filter (· < bound) =
        (Cfg.Check.termVars tm).filter (· < bound) := by
    intro fr tm hfr
    have hpre_nil : ∀ {is : List Cfg.Instr}, (∀ y ∈ is.flatMap instrUses, bound ≤ y) →
        (is.flatMap instrUses).filter (· < bound) = [] := by
      intro is his
      rw [List.filter_eq_nil_iff]
      intro y hy; simp [show ¬ y < bound by have := his y hy; omega]
    cases tm with
    | jump e =>
      have h := argVars_hoistArgs_lt strFns fr bound e.args hfr
      exact ⟨hpre_nil h.2, by simpa [hoistTerm, hoistEdge, Cfg.Check.termVars] using h.1⟩
    | ret a =>
      have harg : (Cfg.Check.argVars [(hoistArg strFns fr a).2.1]).filter (· < bound) =
          (Cfg.Check.argVars [a]).filter (· < bound) := by
        cases a with
        | var y => simp [hoistArg, Cfg.Check.argVars]
        | erased => simp [hoistArg, Cfg.Check.argVars]
        | lit l =>
          cases l with
          | nat _ => simp [hoistArg, Cfg.Check.argVars]
          | str s =>
            unfold hoistArg; cases hl : strFns.lookup s with
            | none => simp [hl, Cfg.Check.argVars]
            | some _ => simp [hl, Cfg.Check.argVars, show ¬ fr < bound by omega]
      exact ⟨hpre_nil (fun y hy => Nat.le_trans hfr ((argVars_hoistArg_lt strFns fr a).2 y hy)),
        by simpa [hoistTerm, Cfg.Check.termVars] using harg⟩
    | tcall _ as =>
      have h := argVars_hoistArgs_lt strFns fr bound as hfr
      exact ⟨hpre_nil h.2, by simpa [hoistTerm, Cfg.Check.termVars] using h.1⟩
    | trap => simp [hoistTerm, Cfg.Check.termVars]
    | switch x alts d =>
      have hAlts : ∀ (fr0 : Nat) (al : List (Key.CtorKey × Cfg.Edge)), bound ≤ fr0 →
          ((hoistAlts strFns fr0 al).1.flatMap instrUses).filter (· < bound) = [] ∧
          (((hoistAlts strFns fr0 al).2.1.map (·.2)).flatMap fun e => Cfg.Check.argVars e.args).filter (· < bound) =
            ((al.map (·.2)).flatMap fun e => Cfg.Check.argVars e.args).filter (· < bound) := by
        intro fr0 al
        induction al generalizing fr0 with
        | nil => intro _; simp [hoistAlts]
        | cons p al ih =>
          intro hfr0
          have h1 := argVars_hoistArgs_lt strFns fr0 bound p.2.args hfr0
          have h2 := ih _ (Nat.le_trans hfr0 (hoistEdge_fresh_le strFns fr0 p.2))
          simp only [hoistEdge] at h2
          refine ⟨by simp [hoistAlts, hoistEdge, List.flatMap_append, List.filter_append, hpre_nil h1.2, h2.1], ?_⟩
          simp [hoistAlts, hoistEdge, List.flatMap_cons, List.filter_append, h1.1, h2.2]
      have hOpt : ∀ (fr0 : Nat) (od : Option Cfg.Edge), bound ≤ fr0 →
          ((hoistOptEdge strFns fr0 od).1.flatMap instrUses).filter (· < bound) = [] ∧
          ((hoistOptEdge strFns fr0 od).2.1.toList.flatMap fun e => Cfg.Check.argVars e.args).filter (· < bound) =
            (od.toList.flatMap fun e => Cfg.Check.argVars e.args).filter (· < bound) := by
        intro fr0 od hfr0
        cases od with
        | none => simp [hoistOptEdge]
        | some e =>
          have h1 := argVars_hoistArgs_lt strFns fr0 bound e.args hfr0
          exact ⟨hpre_nil h1.2, by simpa [hoistOptEdge, hoistEdge] using h1.1⟩
      have hA := hAlts fr alts hfr
      have hO := hOpt (hoistAlts strFns fr alts).2.2 d (Nat.le_trans hfr (hoistAlts_fresh_le strFns fr alts))
      refine ⟨by simp [hoistTerm, List.flatMap_append, List.filter_append, hA.1, hO.1], ?_⟩
      simp only [hoistTerm, Cfg.Check.termVars, List.flatMap_append, List.filter_cons, List.filter_append]
      rw [hA.2, hO.2]
  unfold hoistBlock
  split
  · rename_i _ init cmp _ hunsnoc
    have hbody : b.body = init ++ [cmp] := by
      -- Standard unsnoc characterization
      have aux : ∀ (l : List Cfg.Instr) (i : List Cfg.Instr) (c : Cfg.Instr),
          unsnoc l = some (i, c) → l = i ++ [c] := by
        intro l
        induction l with
        | nil => intro _ _ h; simp [unsnoc] at h
        | cons a l ih =>
          intro i c h
          cases l with
          | nil => simp [unsnoc] at h; obtain ⟨rfl, rfl⟩ := h; rfl
          | cons b1 l1 =>
            simp only [unsnoc, Option.map_eq_some_iff] at h
            obtain ⟨⟨i', c'⟩, hu, heq⟩ := h
            cases heq
            simpa using congrArg (a :: ·) (ih i' c' hu)
      exact aux b.body init cmp hunsnoc
    have h1 := hInstrs fresh init hle
    have hle1 : bound ≤ (hoistInstrs strFns fresh init).2 :=
      Nat.le_trans hle (hoistInstrs_fresh_le strFns fresh init)
    have h2 := hTerm _ b.term hle1
    have hle2 : bound ≤ (hoistTerm strFns (hoistInstrs strFns fresh init).2 b.term).2.2 :=
      Nat.le_trans hle1 (hoistTerm_fresh_le strFns _ b.term)
    have h3 := hInstr _ cmp hle2
    simp only [blockUses, List.flatMap_append, List.filter_append, h1, h2.1, h2.2, h3,
      List.append_nil, hbody, List.flatMap_cons, List.flatMap_nil]
  · have h1 := hInstrs fresh b.body hle
    have hle1 : bound ≤ (hoistInstrs strFns fresh b.body).2 :=
      Nat.le_trans hle (hoistInstrs_fresh_le strFns fresh b.body)
    have h2 := hTerm _ b.term hle1
    simp only [blockUses, List.flatMap_append, List.filter_append, h1, h2.1, h2.2, List.append_nil]

/-- `useCounts` agrees on every original variable `< supOf fd` before and after `hoistFun`. -/
theorem hoistFun_useCounts_lt (T : Tables) (strFns : List (String × Fir.FunId)) (fd : Cfg.Fun)
    {x : Nat} (hx : x < supOf fd) :
    (useCounts (hoistFun T strFns fd)).getD x 0 = (useCounts fd).getD x 0 := by
  unfold useCounts
  rw [useCount_eq_count, useCount_eq_count]
  have hleaf : (NatMap.leaf : NatMap Nat).getD x 0 = 0 := rfl
  simp only [hleaf, Nat.zero_add]
  apply count_eq_of_filter_lt hx
  unfold hoistFun
  have aux : ∀ (fr : Nat) (bs : List Cfg.Block), supOf fd ≤ fr →
      ((hoistBlocks T (useCounts fd) strFns fr bs).1.flatMap blockUses).filter (· < supOf fd) =
        (bs.flatMap blockUses).filter (· < supOf fd) := by
    intro fr bs
    induction bs generalizing fr with
    | nil => intro _; simp [hoistBlocks]
    | cons b bs ih =>
      intro hfr
      simp only [hoistBlocks, List.flatMap_cons, List.filter_append]
      rw [hoistBlock_uses_lt T (useCounts fd) strFns fr (supOf fd) b hfr,
          ih _ (Nat.le_trans hfr (hoistBlock_fresh_le T (useCounts fd) strFns fr b))]
  exact aux (max fd.vars (maxVar fd + 1)) fd.blocks (Nat.le_refl _)

/-- If a block `b'` of `hoistFun` has `fusable = none`, the original block `b` also has `fusable = none`
(modulo string-free comparisons — Wait: if `b` was fusable, `b'` IS fusable too!). -/
theorem hoistBlock_fusable_none (T : Tables) (strFns : List (String × Fir.FunId)) (fd : Cfg.Fun)
    {i : Nat} {b : Cfg.Block} {f0 : Nat} (hb : fd.blocks[i]? = some b) (_hf0 : supOf fd ≤ f0)
    (hn : fusable T (useCounts (hoistFun T strFns fd)) (hoistBlock T (useCounts fd) strFns f0 b).1 = none) :
    fusable T (useCounts fd) b = none := by
  cases hfb : fusable T (useCounts fd) b with
  | none => rfl
  | some p =>
    obtain ⟨init, c, a, a'⟩ := p
    obtain ⟨x, op, alts, d, hbody, hcmp, hterm, huses, hbools⟩ := fusable_some hfb
    have huns : unsnoc b.body = some (init, .bind x (.fir (.prim op [a, a']))) := by
      have aux : ∀ (l : List Cfg.Instr) (z : Cfg.Instr), unsnoc (l ++ [z]) = some (l, z) := by
        intro l z
        induction l with
        | nil => rfl
        | cons a l ih =>
          cases l with
          | nil => rfl
          | cons a' l' => simp only [List.cons_append] at ih; simp only [List.cons_append, unsnoc, ih]; rfl
      rw [hbody]; exact aux init _
    have hx_lt : x < supOf fd := instr_def_lt hb (by simpa using hbody.symm)
    have huses' : (useCounts (hoistFun T strFns fd)).getD x 0 = 1 := by
      rw [hoistFun_useCounts_lt T strFns fd hx_lt]; exact huses
    -- In `hoistBlock`, the fused branch puts `cmp'` = `pre ++ [.bind x (.fir (.prim op [a1, a2]))]` LAST!
    have hblk : hoistBlock T (useCounts fd) strFns f0 b =
        let (init', f1) := hoistInstrs strFns f0 init
        let (termPre, term', f2) := hoistTerm strFns f1 b.term
        let (cmp', f3) := hoistInstr strFns f2 (.bind x (.fir (.prim op [a, a'])))
        ({ b with body := init' ++ termPre ++ cmp', term := term' }, f3) := by
      unfold hoistBlock
      simp [hfb, huns]
    rw [congrArg Prod.fst hblk] at hn
    simp only [hoistInstr, hoistRhs, hterm, hoistTerm] at hn
    have huns' : ∀ (pre : List Cfg.Instr) (z : Cfg.Instr), unsnoc (pre ++ [z]) = some (pre, z) := by
      intro l z
      induction l with
      | nil => rfl
      | cons u l ih =>
        cases l with
        | nil => rfl
        | cons u' l' => simp only [List.cons_append] at ih; simp only [List.cons_append, unsnoc, ih]; rfl
    have hkeys : (hoistAlts strFns (hoistInstrs strFns f0 init).2 alts).2.1.map Prod.fst = alts.map Prod.fst := by
      have aux : ∀ (fr : Nat) (al : List (Key.CtorKey × Cfg.Edge)),
          (hoistAlts strFns fr al).2.1.map Prod.fst = al.map Prod.fst := by
        intro fr al
        induction al generalizing fr with
        | nil => rfl
        | cons p al ih => simp [hoistAlts, ih]
      exact aux _ alts
    have hbools' : ((hoistAlts strFns (hoistInstrs strFns f0 init).2 alts).2.1).all
        (fun x => T.known.boolTrue == some x.1 || T.known.boolFalse == some x.1) = true := by
      rw [List.all_eq_true]
      intro p hp
      have hm : p.1 ∈ alts.map Prod.fst := by
        rw [← hkeys]; exact List.mem_map.2 ⟨p, hp, rfl⟩
      obtain ⟨q, hq, hqp⟩ := List.mem_map.1 hm
      rw [← hqp]
      rcases hbools q hq with ht | hf
      · simp [ht]
      · simp [hf]
    unfold fusable at hn
    simp only [← List.append_assoc, huns', hoistArgs] at hn
    simp only [hcmp, beq_self_eq_true, Bool.true_and, huses', hbools', ↓reduceIte] at hn
    cases hn

/-- Frame correspondence between a frame of `P` and a frame of `P' = hoistStrings P (lowerStrFns P)`. -/
def HoistFrame (P P' : Cfg.Program) (fr fr' : Cfg.Frame) : Prop :=
  P' = hoistStrings P (Rt.lowerStrFns P) ∧
  fr'.fn = fr.fn ∧ fr'.blk = fr.blk ∧
  ∃ fd b f0,
    fr.fn < P.size ∧ P.fun? fr.fn = some fd ∧ fd.blocks[fr.blk]? = some b ∧
    supOf fd ≤ f0 ∧
    (∀ y u, fr.env.get? y = some u → y < supOf fd) ∧
    (∀ y u, fr.env.get? y = some u → fr'.env.get? y = some u) ∧
    (∀ y u, fr'.env.get? y = some u → fr.env.get? y = some u ∨ ∃ s, u = .lit (.str s)) ∧
    (hoistFun (tables P) (Rt.lowerStrFns P) fd).blocks[fr.blk]? =
      some (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1 ∧
    ∃ done f1, b.body = done ++ fr.rest ∧ supOf fd ≤ f1 ∧
      (fusable (tables P) (useCounts fd) b = none →
        let (rest', f2) := hoistInstrs (Rt.lowerStrFns P) f1 fr.rest
        let (termPre, term', _) := hoistTerm (Rt.lowerStrFns P) f2 b.term
        fr'.rest = rest' ++ termPre ∧
        (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1.term = term') ∧
      (∀ init cmp, fusable (tables P) (useCounts fd) b ≠ none → unsnoc b.body = some (init, cmp) →
        (∃ restInit, fr.rest = restInit ++ [cmp] ∧
          let (r1, fa) := hoistInstrs (Rt.lowerStrFns P) f1 restInit
          let (tp, term', fb) := hoistTerm (Rt.lowerStrFns P) fa b.term
          let (c1, _) := hoistInstr (Rt.lowerStrFns P) fb cmp
          fr'.rest = r1 ++ tp ++ c1 ∧
          (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1.term = term') ∨
        (fr.rest = [] ∧ fr'.rest = [] ∧
          ∃ fa bs, supOf fd ≤ fa ∧
            StrBinds P fa (hoistTerm (Rt.lowerStrFns P) fa b.term).2.2
              (hoistTerm (Rt.lowerStrFns P) fa b.term).1 bs ∧
            (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1.term =
              (hoistTerm (Rt.lowerStrFns P) fa b.term).2.1 ∧
            ∀ t s, (t, s) ∈ bs → fr'.env.get? t = some (.lit (.str s))))

/-- Stack entry correspondence (also recording `x < supOf fd` for the return destination). -/
def HoistSusp (P P' : Cfg.Program) (p q : Cfg.Frame × Nat) : Prop :=
  p.2 = q.2 ∧ HoistFrame P P' p.1 q.1 ∧ ∀ fd, P.fun? p.1.fn = some fd → p.2 < supOf fd

/-- State correspondence between `Cfg.step .immortal P` and `strStep P (hoistStrings P (lowerStrFns P))`. -/
def HoistRel (P P' : Cfg.Program) : Cfg.State → Cfg.State → Prop
  | .call g vs stk H, .call g' vs' stk' H' =>
    P' = hoistStrings P (Rt.lowerStrFns P) ∧ g' = g ∧ vs' = vs ∧ H' = H ∧
    ListRel (HoistSusp P P') stk stk'
  | .ret v stk H, .ret v' stk' H' =>
    P' = hoistStrings P (Rt.lowerStrFns P) ∧ v' = v ∧ H' = H ∧
    ListRel (HoistSusp P P') stk stk'
  | .run fr stk H, .run fr' stk' H' =>
    H' = H ∧ HoistFrame P P' fr fr' ∧
    ListRel (HoistSusp P P') stk stk'
  | _, _ => False

/-- Helper: entering block `i` of `fd` establishes `HoistFrame`. -/
private theorem hoistFrame_of_block {P P' : Cfg.Program} (hP' : P' = hoistStrings P (Rt.lowerStrFns P))
    {f i : Nat} {fd : Cfg.Fun} {b : Cfg.Block} (hf : f < P.size) (hfd : P.fun? f = some fd)
    (hb : fd.blocks[i]? = some b) {ρ ρ' : Own.Env}
    (hdom : ∀ y u, ρ.get? y = some u → y < supOf fd)
    (hag : ∀ y u, ρ.get? y = some u → ρ'.get? y = some u)
    (hrev : ∀ y u, ρ'.get? y = some u → ρ.get? y = some u ∨ ∃ s, u = .lit (.str s)) :
    ∃ f0, supOf fd ≤ f0 ∧
      (hoistFun (tables P) (Rt.lowerStrFns P) fd).blocks[i]? =
        some (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1 ∧
      HoistFrame P P'
        { fn := f, blk := i, rest := b.body, env := ρ }
        { fn := f, blk := i, rest := (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1.body, env := ρ' } := by
  obtain ⟨f0, hle, hget⟩ := hoistBlocks_getElem? (tables P) (useCounts fd) (Rt.lowerStrFns P)
    (supOf fd) fd.blocks i b hb
  refine ⟨f0, hle, hget, hP', rfl, rfl, fd, b, f0, hf, hfd, hb, hle, hdom, hag, hrev, hget,
    [], f0, rfl, hle, ?_, ?_⟩
  · intro hnone
    unfold hoistBlock
    simp [hnone]
  · intro init cmp hne huns
    left
    have hbody : b.body = init ++ [cmp] := by
      have aux : ∀ (l : List Cfg.Instr) (i : List Cfg.Instr) (c : Cfg.Instr),
          unsnoc l = some (i, c) → l = i ++ [c] := by
        intro l
        induction l with
        | nil => intro _ _ h; simp [unsnoc] at h
        | cons a l ih =>
          intro i c h
          cases l with
          | nil => simp [unsnoc] at h; obtain ⟨rfl, rfl⟩ := h; rfl
          | cons b1 l1 =>
            simp only [unsnoc, Option.map_eq_some_iff] at h
            obtain ⟨⟨i', c'⟩, hu, heq⟩ := h; cases heq
            simpa using congrArg (a :: ·) (ih i' c' hu)
      exact aux b.body init cmp huns
    refine ⟨init, hbody, ?_⟩
    cases hfb : fusable (tables P) (useCounts fd) b with
    | none => exact absurd hfb hne
    | some p =>
      unfold hoistBlock
      simp [hfb, huns]

/-- Helper: `Own.bindAll` preserves domain `< supOf fd`, forward agreement, and reverse string invariant. -/
private theorem bindAll_dom_ag {sup : Nat} :
    ∀ (ps : List Nat) (vs : List Own.RVal) (ρ ρ' : Own.Env),
      (∀ y ∈ ps, y < sup) →
      (∀ y u, ρ.get? y = some u → y < sup) →
      (∀ y u, ρ.get? y = some u → ρ'.get? y = some u) →
      (∀ y u, ρ'.get? y = some u → ρ.get? y = some u ∨ ∃ s, u = .lit (.str s)) →
      (∀ y u, (Own.bindAll ρ ps vs).get? y = some u → y < sup) ∧
      (∀ y u, (Own.bindAll ρ ps vs).get? y = some u → (Own.bindAll ρ' ps vs).get? y = some u) ∧
      (∀ y u, (Own.bindAll ρ' ps vs).get? y = some u →
        (Own.bindAll ρ ps vs).get? y = some u ∨ ∃ s, u = .lit (.str s))
  | [], _, ρ, ρ', _, hdom, hag, hrev => ⟨hdom, hag, hrev⟩
  | _ :: _, [], ρ, ρ', _, hdom, hag, hrev => ⟨hdom, hag, hrev⟩
  | p :: ps, v :: vs, ρ, ρ', hps, hdom, hag, hrev => by
    apply bindAll_dom_ag ps vs (ρ.insert p v) (ρ'.insert p v)
      (fun y hy => hps y (by simp [hy]))
    · intro y u hy
      by_cases hye : y = p
      · subst hye; exact hps y (by simp)
      · rw [NatMap.get?_insert_ne _ _ hye] at hy; exact hdom y u hy
    · intro y u hy
      by_cases hye : y = p
      · subst hye; simpa [NatMap.get?_insert] using hy
      · rw [NatMap.get?_insert_ne _ _ hye] at hy ⊢; exact hag y u hy
    · intro y u hy
      by_cases hye : y = p
      · subst hye; exact .inl (by simpa [NatMap.get?_insert] using hy)
      · rw [NatMap.get?_insert_ne _ _ hye] at hy ⊢; exact hrev y u hy

/-- Helper: collecting strings from a single instruction inside `b.body` of `fd`. -/
private theorem collect_instr_mem {P : Cfg.Program} {f i : Nat} {fd : Cfg.Fun} {b : Cfg.Block}
    {ins : Cfg.Instr} (hf : f < P.size) (hfd : P.fun? f = some fd) (hb : fd.blocks[i]? = some b)
    (hi : ins ∈ b.body) :
    ∀ s ∈ collectInstr [] ins, s ∈ Rt.lowerStrs P := by
  intro s hs
  apply collectStrings_fun_subset hf hfd
  -- `ins ∈ b.body`, `b ∈ fd.blocks`
  have hlift_add : ∀ (a1 a2 : List String) (x : String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ addStr a1 x, t ∈ addStr a2 x := by
    intro a1 a2 x hsub t ht; rw [mem_addStr_iff] at ht ⊢
    rcases ht with h | rfl; exact .inl (hsub t h); exact .inr rfl
  have hlift_arg : ∀ (a1 a2 : List String) (a : Fir.Arg),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ collectArg a1 a, t ∈ collectArg a2 a := by
    intro a1 a2 a hsub t ht
    cases a with
    | lit l => cases l with | str st => exact hlift_add a1 a2 st hsub t ht | nat _ => exact hsub t ht
    | var _ | erased => exact hsub t ht
  have hlift_args : ∀ (as : List Fir.Arg) (a1 a2 : List String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ collectArgs a1 as, t ∈ collectArgs a2 as := by
    intro as; induction as with
    | nil => intro _ _ h; exact h
    | cons a as ih => intro a1 a2 h; exact ih _ _ (hlift_arg a1 a2 a h)
  have hlift_rhs : ∀ (r : Own.Rhs) (a1 a2 : List String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ collectRhs a1 r, t ∈ collectRhs a2 r := by
    intro r a1 a2 h
    cases r with
    | fir e => cases e with
      | arg a => exact hlift_arg a1 a2 a h
      | ctor _ as | prim _ as | call _ as => exact hlift_args as a1 a2 h
      | proj _ _ _ => exact h
    | alloc _ as _ => exact hlift_args as a1 a2 h
    | proj _ _ _ => exact h
  have hin_body : ∀ (is : List Cfg.Instr) (acc : List String), ins ∈ is →
      s ∈ is.foldl collectInstr acc := by
    intro is
    induction is with
    | nil => intro _ h; cases h
    | cons j is ih =>
      intro acc hj
      rcases List.mem_cons.1 hj with rfl | hj'
      · rw [List.foldl_cons]
        apply mem_collectInstrs
        cases ins with | bind _ r => exact hlift_rhs r [] acc (fun _ h0 => nomatch h0) s hs
      · rw [List.foldl_cons]; exact ih _ hj'
  have hb_mem : b ∈ fd.blocks := List.mem_of_getElem? hb
  have hin_blocks : ∀ (bs : List Cfg.Block) (acc : List String), b ∈ bs →
      s ∈ bs.foldl collectBlock acc := by
    intro bs
    induction bs with
    | nil => intro _ h; cases h
    | cons b0 bs ih =>
      intro acc hbm
      rcases List.mem_cons.1 hbm with rfl | hbm'
      · rw [List.foldl_cons]
        apply mem_collectFun (fd := { fd with blocks := bs })
        exact mem_collectTerm _ b.term s (hin_body b.body acc hi)
      · rw [List.foldl_cons]; exact ih _ hbm'
  exact hin_blocks fd.blocks [] hb_mem

private theorem collect_term_mem {P : Cfg.Program} {f i : Nat} {fd : Cfg.Fun} {b : Cfg.Block}
    (hf : f < P.size) (hfd : P.fun? f = some fd) (hb : fd.blocks[i]? = some b) :
    ∀ s ∈ collectTerm [] b.term, s ∈ Rt.lowerStrs P := by
  intro s hs
  apply collectStrings_fun_subset hf hfd
  have hlift_add : ∀ (a1 a2 : List String) (x : String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ addStr a1 x, t ∈ addStr a2 x := by
    intro a1 a2 x hsub t ht; rw [mem_addStr_iff] at ht ⊢
    rcases ht with h | rfl; exact .inl (hsub t h); exact .inr rfl
  have hlift_arg : ∀ (a1 a2 : List String) (a : Fir.Arg),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ collectArg a1 a, t ∈ collectArg a2 a := by
    intro a1 a2 a hsub t ht
    cases a with
    | lit l => cases l with | str st => exact hlift_add a1 a2 st hsub t ht | nat _ => exact hsub t ht
    | var _ | erased => exact hsub t ht
  have hlift_args : ∀ (as : List Fir.Arg) (a1 a2 : List String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ collectArgs a1 as, t ∈ collectArgs a2 as := by
    intro as; induction as with
    | nil => intro _ _ h; exact h
    | cons a as ih => intro a1 a2 h; exact ih _ _ (hlift_arg a1 a2 a h)
  have hlift_alts : ∀ (al : List (Key.CtorKey × Cfg.Edge)) (a1 a2 : List String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ al.foldl (fun a (_, e) => collectEdge a e) a1,
        t ∈ al.foldl (fun a (_, e) => collectEdge a e) a2 := by
    intro al; induction al with
    | nil => intro _ _ h; exact h
    | cons p al ih => intro a1 a2 h; exact ih _ _ (hlift_args p.2.args a1 a2 h)
  have hlift_term : ∀ (tm : Cfg.Term) (a1 a2 : List String),
      (∀ t ∈ a1, t ∈ a2) → ∀ t ∈ collectTerm a1 tm, t ∈ collectTerm a2 tm := by
    intro tm a1 a2 h
    cases tm with
    | jump e => exact hlift_args e.args a1 a2 h
    | switch _ alts d =>
      have h1 := hlift_alts alts a1 a2 h
      cases d with | none => exact h1 | some e => exact hlift_args e.args _ _ h1
    | ret a => exact hlift_arg a1 a2 a h
    | tcall _ as => exact hlift_args as a1 a2 h
    | trap => exact h
  have hb_mem : b ∈ fd.blocks := List.mem_of_getElem? hb
  have hin_blocks : ∀ (bs : List Cfg.Block) (acc : List String), b ∈ bs →
      s ∈ bs.foldl collectBlock acc := by
    intro bs
    induction bs with
    | nil => intro _ h; cases h
    | cons b0 bs ih =>
      intro acc hbm
      rcases List.mem_cons.1 hbm with rfl | hbm'
      · rw [List.foldl_cons]
        apply mem_collectFun (fd := { fd with blocks := bs })
        exact hlift_term b.term [] _ (fun _ h0 => nomatch h0) s hs
      · rw [List.foldl_cons]; exact ih _ hbm'
  exact hin_blocks fd.blocks [] hb_mem

/-- Every bound variable in a `StrBinds P lo hi pre bs` lies in `[lo, hi)`. -/
theorem StrBinds.mem_bounds {P : Cfg.Program} {lo hi : Nat} {pre : List Cfg.Instr}
    {bs : List (Nat × String)} (h : StrBinds P lo hi pre bs) :
    ∀ {t s}, (t, s) ∈ bs → lo ≤ t ∧ t < hi := by
  induction h with
  | nil _ => intro _ _ hm; cases hm
  | @cons lo hi t0 fnId s0 rest bs _ hlo hrest ih =>
    intro t s hm
    rcases List.mem_cons.1 hm with h0 | hm'
    · cases h0
      have := hrest.le
      omega
    · obtain ⟨h1, h2⟩ := ih hm'
      omega

/-- Helper: `takeEdge` step correspondence between `P` and `P'`. -/
private theorem hoist_takeEdge {P P' : Cfg.Program} (hP' : P' = hoistStrings P (Rt.lowerStrFns P))
    {f : Nat} {fd : Cfg.Fun} (hf : f < P.size) (hfd : P.fun? f = some fd)
    {fr fr' : Cfg.Frame} (hfn : fr'.fn = fr.fn) (hfr_fn : fr.fn = f)
    {stk stk' : List (Cfg.Frame × Nat)} {H : Own.Heap}
    (hstk : ListRel (HoistSusp P P') stk stk')
    (hdom : ∀ y u, fr.env.get? y = some u → y < supOf fd)
    (hag : ∀ y u, fr.env.get? y = some u → fr'.env.get? y = some u)
    (hrev : ∀ y u, fr'.env.get? y = some u → fr.env.get? y = some u ∨ ∃ s, u = .lit (.str s))
    {e e' : Cfg.Edge} (htgt : e'.target = e.target) (hback : e'.back = e.back)
    (hev : ∀ vs, Own.evalArgs fr.env e.args = some vs → Own.evalArgs fr'.env e'.args = some vs)
    {s₁' : Cfg.State} {bb : Bool}
    (hs : Cfg.takeEdge fd fr stk H e = .next s₁' bb) :
    ∃ s₂', Cfg.takeEdge (hoistFun (tables P) (Rt.lowerStrFns P) fd) fr' stk' H e' = .next s₂' bb ∧
      HoistRel P P' s₁' s₂' := by
  simp only [Cfg.takeEdge, Cfg.Fun.block?] at hs ⊢
  cases hbt : fd.blocks[e.target]? with
  | none => simp [hbt] at hs
  | some bt =>
    cases hvs : Own.evalArgs fr.env e.args with
    | none => simp [hbt, hvs] at hs
    | some vs =>
      simp only [hbt, hvs] at hs
      split at hs
      · rename_i hlen
        simp only [Sem.Step.next.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have hba := bindAll_dom_ag (bt.params.map (·.1)) vs fr.env fr'.env (params_lt_sup hbt) hdom hag hrev
        obtain ⟨f0, hle, hget, hframe⟩ := hoistFrame_of_block hP' hf hfd hbt
          (ρ := Own.bindAll fr.env (bt.params.map (·.1)) vs)
          (ρ' := Own.bindAll fr'.env (bt.params.map (·.1)) vs)
          hba.1 hba.2.1 hba.2.2
        have hvs' := hev vs hvs
        have hpar : (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 bt).1.params = bt.params :=
          hoistBlock_params _ _ _ _ _
        refine ⟨.run { fn := fr'.fn, blk := e'.target,
                       rest := (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 bt).1.body,
                       env := Own.bindAll fr'.env ((hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 bt).1.params.map (·.1)) vs } stk' H,
          ?_, rfl, ?_, hstk⟩
        · rw [htgt, hget, hvs']; dsimp only; rw [hpar, ite_eq_left hlen, hback]
        · simpa [hfn, hfr_fn, htgt, hpar] using hframe
      · cases hs

/-- Helper: `insert x v` preserves `HoistFrame` when `x < supOf fd`. -/
private theorem hoistFrame_insert {P P' : Cfg.Program} {fr fr' : Cfg.Frame}
    (hfr : HoistFrame P P' fr fr') {x : Nat} {v : Own.RVal}
    (hx : ∀ fd, P.fun? fr.fn = some fd → x < supOf fd) :
    HoistFrame P P' { fr with env := fr.env.insert x v } { fr' with env := fr'.env.insert x v } := by
  obtain ⟨hP', hfn, hblk, fd, b, f0, hflt, hfd, hb, hf0, hdom, hag, hrev, hget, done, f1, hdone, hf1, hnf, hfus⟩ := hfr
  have hx' : x < supOf fd := hx fd hfd
  refine ⟨hP', hfn, hblk, fd, b, f0, hflt, hfd, hb, hf0, ?_, ?_, ?_, hget, done, f1, hdone, hf1, hnf, ?_⟩
  · intro y u hy
    by_cases hye : y = x
    · subst hye; exact hx'
    · rw [NatMap.get?_insert_ne _ _ hye] at hy; exact hdom y u hy
  · intro y u hy
    by_cases hye : y = x
    · subst hye; simpa [NatMap.get?_insert] using hy
    · rw [NatMap.get?_insert_ne _ _ hye] at hy ⊢; exact hag y u hy
  · intro y u hy
    by_cases hye : y = x
    · subst hye; exact .inl (by simpa [NatMap.get?_insert] using hy)
    · rw [NatMap.get?_insert_ne _ _ hye] at hy ⊢; exact hrev y u hy
  · intro init cmp hne huns
    rcases hfus init cmp hne huns with h1 | ⟨hrest, hrest', fa, bs, hfa, hsb, hterm, hbind⟩
    · exact .inl h1
    · refine .inr ⟨hrest, hrest', fa, bs, hfa, hsb, hterm, fun t s hm => ?_⟩
      obtain ⟨hlo, -⟩ := hsb.mem_bounds hm
      rw [NatMap.get?_insert_ne _ _ (by omega)]
      exact hbind t s hm

/-- Helper: `fusable = some _` implies `unsnoc b.body = some (init, cmp)` with a non-call comparison. -/
private theorem unsnoc_of_fusable {T : Tables} {uses : NatMap Nat} {b : Cfg.Block}
    {p : List Cfg.Instr × Lir.Cond × Fir.Arg × Fir.Arg} (hf : fusable T uses b = some p) :
    ∃ x op a a', unsnoc b.body = some (p.1, .bind x (.fir (.prim op [a, a']))) := by
  obtain ⟨x, op, alts, d, hbody, _, _, _, _⟩ := fusable_some hf
  refine ⟨x, op, p.2.2.1, p.2.2.2, ?_⟩
  have aux : ∀ (l : List Cfg.Instr) (z : Cfg.Instr), unsnoc (l ++ [z]) = some (l, z) := by
    intro l z
    induction l with
    | nil => rfl
    | cons a l ih =>
      cases l with
      | nil => rfl
      | cons a' l' => simp only [List.cons_append] at ih; simp only [List.cons_append, unsnoc, ih]; rfl
  rw [hbody]; exact aux p.1 _

/-- Helper: executing one hoisted instruction `.bind x r'` directly in LIR after running `pre_r`. -/
private theorem hoist_step_instr_sim {P P' : Cfg.Program} {lp : Lir.Program} {ctx : Word}
    (hP' : P' = hoistStrings P (Rt.lowerStrFns P)) (ht : TargetStr P P' lp)
    {fd : Cfg.Fun} {b : Cfg.Block} {f_rhs : Nat}
    {fr fr' : Cfg.Frame} {stk stk' : List (Cfg.Frame × Nat)} {H : Own.Heap} {s₃ : Lir.State}
    (hflt : fr.fn < P.size) (hfd : P.fun? fr.fn = some fd) (hb : fd.blocks[fr.blk]? = some b)
    (hf_rhs : supOf fd ≤ f_rhs)
    (hdom : ∀ y u, fr.env.get? y = some u → y < supOf fd)
    (hag : ∀ y u, fr.env.get? y = some u → fr'.env.get? y = some u)
    {x : Nat} {r : Own.Rhs} {is tail' : List Cfg.Instr}
    (hfr_rest : fr.rest = .bind x r :: is)
    (hmem : .bind x r ∈ b.body)
    (hfr'_rest : fr'.rest = (hoistRhs (Rt.lowerStrFns P) f_rhs r).1 ++ (.bind x (hoistRhs (Rt.lowerStrFns P) f_rhs r).2.1 :: tail'))
    (hrel3 : Rel P' lp ctx (.run fr' stk' H) s₃)
    {s₁' : Cfg.State} {bb : Bool} (hs : Cfg.step .immortal P (.run fr stk H) = .next s₁' bb) :
    ∃ bs_r, StrBinds P f_rhs (hoistRhs (Rt.lowerStrFns P) f_rhs r).2.2 (hoistRhs (Rt.lowerStrFns P) f_rhs r).1 bs_r ∧
      bb = false ∧
      let env1 := bindStrs fr'.env bs_r
      ((∃ g as as' vs, r = .fir (.call g as) ∧ (hoistRhs (Rt.lowerStrFns P) f_rhs r).2.1 = .fir (.call g as') ∧
          s₁' = .call g vs (({ fr with rest := is }, x) :: stk) H ∧
          ((∃ c s₃', Sem.Star (Lir.semStep lp) s₃ c s₃' ∧
              Rel P' lp ctx (.call g vs (({ fr' with rest := tail', env := env1 }, x) :: stk') H) s₃') ∨
            Sem.Fails (Lir.semStep lp) s₃)) ∨
       (∃ v H', (∀ g as, r ≠ .fir (.call g as)) ∧
          s₁' = .run { fr with rest := is, env := fr.env.insert x v } stk H' ∧
          ((∃ c s₃', Sem.Star (Lir.semStep lp) s₃ c s₃' ∧
              Rel P' lp ctx (.run { fr' with rest := tail', env := env1.insert x v } stk' H') s₃') ∨
            Sem.Fails (Lir.semStep lp) s₃))) := by
  have hcov : ∀ s ∈ collectRhs [] r, s ∈ Rt.lowerStrs P :=
    collect_instr_mem hflt hfd hb hmem
  obtain ⟨bs_r, hsb_r, hcall_r, hnc_r⟩ := hoistRhs_spec (P := P) (fresh := f_rhs) (r := r) hcov
  let resR := hoistRhs (Rt.lowerStrFns P) f_rhs r
  let env1 := bindStrs fr'.env bs_r
  have hfr'_eq : { fr' with rest := resR.1 ++ (.bind x resR.2.1 :: tail') } = fr' := by
    cases fr'; simp only [Cfg.Frame.mk.injEq, true_and, and_true]; exact hfr'_rest.symm
  have hrel_pre : Rel P' lp ctx (.run { fr' with rest := resR.1 ++ (.bind x resR.2.1 :: tail') } stk' H) s₃ := by
    rw [hfr'_eq]; exact hrel3
  have hag1 : ∀ y u, fr.env.get? y = some u → env1.get? y = some u := by
    intro y u hy
    have hylt : y < f_rhs := Nat.lt_of_lt_of_le (hdom y u hy) hf_rhs
    rw [bindStrs_get_lt hsb_r fr'.env hylt]
    exact hag y u hy
  have hbs1 : ∀ t s, (t, s) ∈ bs_r → env1.get? t = some (.lit (.str s)) :=
    fun t s hm => bindStrs_get_mem hsb_r fr'.env hm
  have hsw_cons : SwitchSel P' (.run { fr' with rest := .bind x resR.2.1 :: tail', env := env1 } stk' H) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnil; cases hnil
  by_cases hcall : ∃ g as, r = .fir (.call g as)
  · obtain ⟨g, as, rfl⟩ := hcall
    simp only [Cfg.step, hfr_rest] at hs
    cases hvs : Own.evalArgs fr.env as with
    | none => simp [hvs] at hs
    | some vs =>
      simp only [hvs, Sem.Step.next.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨as', has'_eq, hev_as⟩ := hcall_r g as rfl
      have hvs' : Own.evalArgs env1 as' = some vs := hev_as fr.env env1 vs hag1 hbs1 hvs
      have hst : strStep P P' (.run { fr' with rest := .bind x resR.2.1 :: tail', env := env1 } stk' H) =
          .next (.call g vs (({ fr' with rest := tail', env := env1 }, x) :: stk') H) false := by
        simp [strStep, Cfg.step, resR, has'_eq, hvs']
      refine ⟨bs_r, hsb_r, rfl, .inl ⟨g, as, as', vs, rfl, has'_eq, rfl, ?_⟩⟩
      rcases run_strBinds_sim ht hsb_r fr' (.bind x resR.2.1 :: tail') stk' H hrel_pre with
        ⟨c1, s₃_1, hst1, hrel1⟩ | hf1
      · rcases strStep_sim_one ht hrel1 hsw_cons hst with ⟨c2, s₃_2, hst2, _, hrel2⟩ | hf2
        · exact .inl ⟨c1 + c2, s₃_2, hst1.trans hst2, hrel2⟩
        · exact .inr (fails_prepend hst1 hf2)
      · exact .inr hf1
  · have hnc : ∀ g as, r ≠ .fir (.call g as) := fun g as h => hcall ⟨g, as, h⟩
    rw [step_bind hfr_rest hnc] at hs
    cases hev : Own.evalRhs .immortal P.tables fr.env H r with
    | ok p =>
      obtain ⟨v, H'⟩ := p
      simp only [hev, Sem.Step.next.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hnc', hev'⟩ := hnc_r hnc
      have htab : P'.tables = P.tables := by rw [hP']; rfl
      have hev1 : Own.evalRhs .immortal P'.tables env1 H resR.2.1 = .ok (v, H') := by
        rw [htab]; exact hev' P.tables fr.env env1 H hag1 hbs1 (.ok (v, H')) hev (by simp)
      have hst : strStep P P' (.run { fr' with rest := .bind x resR.2.1 :: tail', env := env1 } stk' H) =
          .next (.run { fr' with rest := tail', env := env1.insert x v } stk' H') false := by
        simp only [strStep]
        rw [step_bind (by rfl) hnc', hev1]
      refine ⟨bs_r, hsb_r, rfl, .inr ⟨v, H', hnc, rfl, ?_⟩⟩
      rcases run_strBinds_sim ht hsb_r fr' (.bind x resR.2.1 :: tail') stk' H hrel_pre with
        ⟨c1, s₃_1, hst1, hrel1⟩ | hf1
      · rcases strStep_sim_one ht hrel1 hsw_cons hst with ⟨c2, s₃_2, hst2, _, hrel2⟩ | hf2
        · exact .inl ⟨c1 + c2, s₃_2, hst1.trans hst2, hrel2⟩
        · exact .inr (fails_prepend hst1 hf2)
      · exact .inr hf1
    | resource _ | trap | timeout | stuck => simp [hev] at hs

/-- Helper: executing a hoisted terminator in `strStep` once `fr'.rest = []` and `bs_tm` is bound. -/
private theorem hoist_step_term {P P' : Cfg.Program} (hP' : P' = hoistStrings P (Rt.lowerStrFns P))
    {fd : Cfg.Fun} {b : Cfg.Block} {f0 fa : Nat} {bs_tm : List (Nat × String)}
    {fr fr' : Cfg.Frame} {stk stk' : List (Cfg.Frame × Nat)} {H : Own.Heap}
    (hflt : fr.fn < P.size) (hfd : P.fun? fr.fn = some fd) (hb : fd.blocks[fr.blk]? = some b)
    (hfn : fr'.fn = fr.fn) (hblk : fr'.blk = fr.blk)
    (hget : (hoistFun (tables P) (Rt.lowerStrFns P) fd).blocks[fr.blk]? =
      some (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1)
    (hterm_eq : (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1.term =
      (hoistTerm (Rt.lowerStrFns P) fa b.term).2.1)
    (hsb : StrBinds P fa (hoistTerm (Rt.lowerStrFns P) fa b.term).2.2
      (hoistTerm (Rt.lowerStrFns P) fa b.term).1 bs_tm)
    (hfr_nil : fr.rest = []) (hfr'_nil : fr'.rest = [])
    (hdom : ∀ y u, fr.env.get? y = some u → y < supOf fd)
    (hag : ∀ y u, fr.env.get? y = some u → fr'.env.get? y = some u)
    (hrev : ∀ y u, fr'.env.get? y = some u → fr.env.get? y = some u ∨ ∃ s, u = .lit (.str s))
    (hbs : ∀ t s, (t, s) ∈ bs_tm → fr'.env.get? t = some (.lit (.str s)))
    (hstk : ListRel (HoistSusp P P') stk stk')
    {s₁' : Cfg.State} {bb : Bool} (hs : Cfg.step .immortal P (.run fr stk H) = .next s₁' bb) :
    ∃ s₂', strStep P P' (.run fr' stk' H) = .next s₂' bb ∧ HoistRel P P' s₁' s₂' := by
  have hcov : ∀ s ∈ collectTerm [] b.term, s ∈ Rt.lowerStrs P := collect_term_mem hflt hfd hb
  obtain ⟨bs', hsb', hJ, hS, hR, hT, hTr⟩ := hoistTerm_spec (P := P) (fresh := fa) (tm := b.term) hcov
  have huniq : ∀ {lo hi : Nat} {pre : List Cfg.Instr} {b1 b2 : List (Nat × String)},
      StrBinds P lo hi pre b1 → StrBinds P lo hi pre b2 → b1 = b2 := by
    intro lo hi pre b1 b2 h1
    induction h1 generalizing b2 with
    | nil _ => intro h2; cases h2; rfl
    | cons hs1 _ _ ih =>
      intro h2
      cases h2 with
      | cons hs2 _ hrest2 =>
        rw [hs1] at hs2; cases hs2
        exact congrArg _ (ih hrest2)
  have hbs_eq : bs' = bs_tm := huniq hsb' hsb
  subst hbs_eq
  have hfd' : P'.fun? fr'.fn = some (hoistFun (tables P) (Rt.lowerStrFns P) fd) := by
    rw [hfn, hP', hoistStrings_fun? hflt, hfd]; rfl
  have hblk' : (hoistFun (tables P) (Rt.lowerStrFns P) fd).blocks[fr'.blk]? =
      some (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1 := by
    rw [hblk]; exact hget
  simp only [Cfg.step, hfr_nil, hfd, Cfg.Fun.block?, hb] at hs
  simp only [strStep, Cfg.step, hfr'_nil, hfd', Cfg.Fun.block?, hblk', hterm_eq]
  cases htm : b.term with
  | jump e =>
    rw [htm] at hs
    obtain ⟨e', he'_eq, htgt, hback, hev⟩ := hJ e htm
    rw [htm] at he'_eq
    rw [he'_eq]
    exact hoist_takeEdge hP' hflt hfd hfn rfl hstk hdom hag hrev htgt hback
      (fun vs hvs => hev fr.env fr'.env vs hag hbs hvs) hs
  | switch x alts d =>
    rw [htm] at hs
    obtain ⟨alts', d', hsw_eq, _, hsel_eq⟩ := hS x alts d htm
    rw [htm] at hsw_eq
    rw [hsw_eq]; dsimp only
    cases hx : fr.env.get? x with
    | none => simp [hx] at hs
    | some v =>
      simp only [hx] at hs
      rw [hag x v hx]; dsimp only
      have hkn : P'.known = P.known := by rw [hP']; rfl
      rw [hkn]
      cases hac : v.asCtor P.known H with
      | none => simp [hac] at hs
      | some kf =>
        obtain ⟨key, fs⟩ := kf
        simp only [hac] at hs
        dsimp only
        cases hsel : Cfg.selectEdge key alts d with
        | none => simp [hsel] at hs
        | some e =>
          simp only [hsel] at hs
          obtain ⟨e', he', htgt, hback, hev⟩ := hsel_eq key e hsel
          rw [he']; dsimp only
          exact hoist_takeEdge hP' hflt hfd hfn rfl hstk hdom hag hrev htgt hback
            (fun vs hvs => hev fr.env fr'.env vs hag hbs hvs) hs
  | ret a =>
    rw [htm] at hs
    obtain ⟨a', ha'_eq, hev⟩ := hR a htm
    rw [htm] at ha'_eq
    rw [ha'_eq]; dsimp only
    cases ha : Own.evalArg fr.env a with
    | none => simp [ha] at hs
    | some v =>
      simp only [ha, Sem.Step.next.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rw [hev fr.env fr'.env v hag hbs ha]
      exact ⟨_, rfl, hP', rfl, rfl, hstk⟩
  | tcall g as =>
    rw [htm] at hs
    obtain ⟨as', has'_eq, hev⟩ := hT g as htm
    rw [htm] at has'_eq
    rw [has'_eq]; dsimp only
    cases has : Own.evalArgs fr.env as with
    | none => simp [has] at hs
    | some vs =>
      simp only [has, Sem.Step.next.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rw [hev fr.env fr'.env vs hag hbs has]
      exact ⟨_, rfl, hP', rfl, rfl, rfl, hstk⟩
  | trap => rw [htm] at hs; simp at hs

/-- `Dispatches` depends only on the keys of `alts`. -/
theorem dispatches_of_keys_eq {T : Tables} {H : Own.Heap} {v : Own.RVal}
    {alts alts' : List (Key.CtorKey × Cfg.Edge)} (hkeys : alts'.map Prod.fst = alts.map Prod.fst)
    (h : Dispatches T H v alts) : Dispatches T H v alts' := by
  have hmem : ∀ p' ∈ alts', ∃ p ∈ alts, p'.1 = p.1 := by
    intro p' hp'
    have : p'.1 ∈ alts.map Prod.fst := by rw [← hkeys]; exact List.mem_map.2 ⟨p', hp', rfl⟩
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 this
    exact ⟨p, hp, hpe.symm⟩
  refine ⟨fun p' hp' => ?_, fun p' hp' c fs hac => ?_⟩
  · obtain ⟨p, hp, hpe⟩ := hmem p' hp'
    rw [hpe]; exact h.1 p hp
  · obtain ⟨p, hp, hpe⟩ := hmem p' hp'
    rw [hpe]; exact h.2 p hp c fs hac

/-- `SwitchSel` transfers from `P` to `P' = hoistStrings P (lowerStrFns P)` at a terminator state. -/
private theorem hoist_switchSel_env {P P' : Cfg.Program} (hP' : P' = hoistStrings P (Rt.lowerStrFns P))
    {fd : Cfg.Fun} {b : Cfg.Block} {f0 fa : Nat}
    {fr fr' : Cfg.Frame} {stk stk' : List (Cfg.Frame × Nat)} {H : Own.Heap}
    (hflt : fr.fn < P.size) (hfd : P.fun? fr.fn = some fd) (hb : fd.blocks[fr.blk]? = some b)
    (hf0 : supOf fd ≤ f0) (hfn : fr'.fn = fr.fn) (hblk : fr'.blk = fr.blk)
    (hget : (hoistFun (tables P) (Rt.lowerStrFns P) fd).blocks[fr.blk]? =
      some (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1)
    (hterm_eq : (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1.term =
      (hoistTerm (Rt.lowerStrFns P) fa b.term).2.1)
    (hfr_nil : fr.rest = [])
    (hrev : ∀ y u, fr'.env.get? y = some u → fr.env.get? y = some u ∨ ∃ s, u = .lit (.str s))
    (hsafe : SwitchSel P (.run fr stk H)) :
    SwitchSel P' (.run fr' stk' H) := by
  intro fd' b' x alts' d' v key fs e' Pw w ctx' m hfd' hb' hfr'_nil hfus' hterm' hx' hv hheap hac hsel'
  have hfd'_eq : fd' = hoistFun (tables P) (Rt.lowerStrFns P) fd := by
    have : P'.fun? fr'.fn = some (hoistFun (tables P) (Rt.lowerStrFns P) fd) := by
      rw [hfn, hP', hoistStrings_fun? hflt, hfd]; rfl
    rw [hfd'] at this; exact Option.some.inj this
  subst hfd'_eq
  have hb'_eq : b' = (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1 := by
    rw [hblk] at hb'; rw [hget] at hb'; exact (Option.some.inj hb').symm
  subst hb'_eq
  have htab : tables P' = tables P := by rw [hP']; rfl
  rw [htab] at hfus' hv hheap ⊢
  have hkn : P'.known = P.known := by rw [hP']; rfl
  rw [hkn] at hac
  have hfb_none : fusable (tables P) (useCounts fd) b = none :=
    hoistBlock_fusable_none (tables P) (Rt.lowerStrFns P) fd hb hf0 hfus'
  have hcovT : ∀ s ∈ collectTerm [] b.term, s ∈ Rt.lowerStrs P := collect_term_mem hflt hfd hb
  obtain ⟨_, _, hJ, hS, hR, hT, hTr⟩ := hoistTerm_spec (P := P) (fresh := fa) (tm := b.term) hcovT
  rw [hterm_eq] at hterm'
  cases hbtm : b.term with
  | jump e => obtain ⟨e0, he0, _⟩ := hJ e hbtm; rw [he0] at hterm'; cases hterm'
  | ret a => obtain ⟨a0, ha0, _⟩ := hR a hbtm; rw [ha0] at hterm'; cases hterm'
  | tcall g as => obtain ⟨as0, has0, _⟩ := hT g as hbtm; rw [has0] at hterm'; cases hterm'
  | trap => rw [hTr hbtm] at hterm'; cases hterm'
  | switch x0 alts d =>
    obtain ⟨alts0, d0, hsw0, hkeys0, hsel0⟩ := hS x0 alts d hbtm
    rw [hsw0] at hterm'
    cases hterm'
    rcases hrev x v hx' with hx | ⟨s, rfl⟩
    · -- `Cfg.selectEdge key alts d` must be `some e` because `alts0.map Prod.fst = alts.map Prod.fst`
      -- and `d0.isSome = d.isSome`!
      have hsel_orig : ∃ e, Cfg.selectEdge key alts d = some e := by
        have hfind : ∀ (al : List (Key.CtorKey × Cfg.Edge)) (fr0 : Nat),
            (hoistAlts (Rt.lowerStrFns P) fr0 al).2.1.find? (fun p => p.1 == key) = none →
            al.find? (fun p => p.1 == key) = none := by
          intro al
          induction al with
          | nil => intro _ _; rfl
          | cons p al ih =>
            intro fr0 hf
            simp only [hoistAlts, List.find?_cons] at hf ⊢
            split at hf
            · cases hf
            · exact ih _ hf
        have hfindSome : ∀ (al : List (Key.CtorKey × Cfg.Edge)) (fr0 : Nat) (p' : Key.CtorKey × Cfg.Edge),
            (hoistAlts (Rt.lowerStrFns P) fr0 al).2.1.find? (fun p => p.1 == key) = some p' →
            ∃ p, al.find? (fun p => p.1 == key) = some p := by
          intro al
          induction al with
          | nil => intro _ _ hf; simp [hoistAlts] at hf
          | cons p al ih =>
            intro fr0 p' hf
            simp only [hoistAlts, List.find?_cons] at hf ⊢
            split at hf
            · exact ⟨p, rfl⟩
            · exact ih _ p' hf
        have hd_some : ∀ (opt : Option Cfg.Edge) (fr0 : Nat) (e0 : Cfg.Edge),
            (hoistOptEdge (Rt.lowerStrFns P) fr0 opt).2.1 = some e0 → ∃ e, opt = some e := by
          intro opt fr0 e0 hopt
          cases opt with
          | none => simp [hoistOptEdge] at hopt
          | some e => exact ⟨e, rfl⟩
        -- Unfold `Cfg.selectEdge` via `alts.find?`? Wait: check `Cfg.selectEdge`'s recursive def!
        have aux : ∀ (al : List (Key.CtorKey × Cfg.Edge)) (fr0 : Nat) (opt : Option Cfg.Edge) (e0 : Cfg.Edge),
            Cfg.selectEdge key (hoistAlts (Rt.lowerStrFns P) fr0 al).2.1
              (hoistOptEdge (Rt.lowerStrFns P) (hoistAlts (Rt.lowerStrFns P) fr0 al).2.2 opt).2.1 = some e0 →
            ∃ e, Cfg.selectEdge key al opt = some e := by
          intro al
          induction al with
          | nil =>
            intro fr0 opt e0 hs0
            simp only [hoistAlts, Cfg.selectEdge] at hs0 ⊢
            exact hd_some opt fr0 e0 hs0
          | cons p al ih =>
            intro fr0 opt e0 hs0
            simp only [hoistAlts, Cfg.selectEdge] at hs0 ⊢
            by_cases hk : p.1 = key
            · simp [hk]
            · simp only [hk, ↓reduceIte] at hs0 ⊢
              exact ih _ opt e0 hs0
        -- `alts0` and `d0` are literally `(hoistAlts ...).2.1` and `(hoistOptEdge ...).2.1`!
        have hsw_def : hoistTerm (Rt.lowerStrFns P) fa (.switch x alts d) =
            let (p1, alts1, f2) := hoistAlts (Rt.lowerStrFns P) fa alts
            let (p2, d1, f3) := hoistOptEdge (Rt.lowerStrFns P) f2 d
            (p1 ++ p2, .switch x alts1 d1, f3) := rfl
        rw [hbtm] at hsw0
        rw [hsw_def] at hsw0
        simp only [Cfg.Term.switch.injEq] at hsw0
        obtain ⟨_, rfl, rfl⟩ := hsw0
        exact aux alts fa d e' hsel'
      obtain ⟨e, hsel⟩ := hsel_orig
      have hdisp := hsafe fd b x alts d v key fs e Pw w ctx' m hfd hb hfr_nil hfb_none hbtm hx hv hheap hac hsel
      exact dispatches_of_keys_eq hkeys0 hdisp
    · simp [Own.RVal.asCtor] at hac

/-- **`hoist_to_lir_forward`**: end-to-end forward diagram from `Cfg.step .immortal P` directly
to `Lir.semStep lp` for `P' = hoistStrings P (lowerStrFns P)`, with zero `sorry`! -/
theorem hoist_to_lir_forward {P P' : Cfg.Program} {lp : Lir.Program} {ctx : Word}
    (hP' : P' = hoistStrings P (Rt.lowerStrFns P))
    (hdense : ∀ {f fd}, P.fun? f = some fd → f < P.size)
    (ht : TargetStr P P' lp) (s₀ : Cfg.State)
    (hsafe : ∀ s, Reach P s₀ s → SwitchSel P s) :
    Sem.Forward (Cfg.step .immortal P) (Lir.semStep lp) (Res P ctx)
      (fun s₁ s₃ => ∃ s₂, HoistRel P P' s₁ s₂ ∧ Rel P' lp ctx s₂ s₃ ∧ Reach P s₀ s₁) where
  next := by
    intro s₁ s₁' s₃ bb ⟨s₂, hhoist, hrel3, c₀, hreach⟩ hs
    have hreach' : Reach P s₀ s₁' := ⟨c₀ + bb.toNat, hreach.trans (.single hs)⟩
    match s₁, s₂, hhoist with
    | .call g vs stk H, .call g' vs' stk' H', ⟨_, hg_eq, hvs_eq, hH_eq, hstk⟩ =>
      subst g'; subst vs'; subst H'
      simp only [Cfg.step] at hs
      cases hfd : P.fun? g with
      | none => simp [hfd] at hs
      | some fd =>
        simp only [hfd, Cfg.Fun.block?] at hs
        cases hb0 : fd.blocks[0]? with
        | none => simp [hb0] at hs
        | some b0 =>
          simp only [hb0] at hs
          split at hs
          · rename_i hlen
            simp only [Sem.Step.next.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            have hg : g < P.size := hdense hfd
            have hso : strOfProg P g = none := by
              unfold strOfProg
              exact ite_eq_right (Nat.not_le_of_lt (Nat.lt_of_lt_of_le hg (Nat.le_add_right _ _)))
            have hfd' : P'.fun? g = some (hoistFun (tables P) (Rt.lowerStrFns P) fd) := by
              rw [hP', hoistStrings_fun? hg, hfd]; rfl
            have hba := bindAll_dom_ag (b0.params.map (·.1)) vs .leaf .leaf (params_lt_sup hb0)
              (fun _ _ h => nomatch h) (fun _ _ h => h) (fun _ _ h => .inl h)
            obtain ⟨f0, hle, hget, hframe⟩ := hoistFrame_of_block hP' hg hfd hb0
              (ρ := Own.bindAll .leaf (b0.params.map (·.1)) vs)
              (ρ' := Own.bindAll .leaf (b0.params.map (·.1)) vs)
              hba.1 hba.2.1 hba.2.2
            have hpar : (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b0).1.params = b0.params :=
              hoistBlock_params _ _ _ _ _
            have hstep' : strStep P P' (.call g vs stk' H) =
                .next (.run { fn := g, blk := 0,
                              rest := (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b0).1.body,
                              env := Own.bindAll .leaf (b0.params.map (·.1)) vs } stk' H) true := by
              cases vs with
              | nil => simp [strStep, hso, Cfg.step, hfd', Cfg.Fun.block?, hget, hpar, hlen]
              | cons _ _ => simp [strStep, Cfg.step, hfd', Cfg.Fun.block?, hget, hpar, hlen]
            exact (strStep_sim_one ht hrel3 trivial hstep').imp
              (fun ⟨c, s₃', hst3, hc, hrel3'⟩ =>
                ⟨c, s₃', hst3, hc,
                  .run { fn := g, blk := 0,
                         rest := (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b0).1.body,
                         env := Own.bindAll .leaf (b0.params.map (·.1)) vs } stk' H,
                  ⟨rfl, hframe, hstk⟩, hrel3', hreach'⟩) id
          · cases hs
    | .ret v [] H, .ret v' [] H', _ => simp [Cfg.step] at hs
    | .ret v ((fr, x) :: stk) H, .ret v' ((fr', x') :: stk') H', ⟨_, hv_eq, hH_eq, .cons ⟨hx, hfr, hxlim⟩ hstk⟩ =>
      dsimp only at hx
      subst v'; subst H'; subst x'
      simp only [Cfg.step, Sem.Step.next.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      have hstep' : strStep P P' (.ret v ((fr', x) :: stk') H) =
          .next (.run { fr' with env := fr'.env.insert x v } stk' H) false := rfl
      exact (strStep_sim_one ht hrel3 trivial hstep').imp
        (fun ⟨c, s₃', hst3, hc, hrel3'⟩ =>
          ⟨c, s₃', hst3, hc, .run { fr' with env := fr'.env.insert x v } stk' H,
            ⟨rfl, hoistFrame_insert hfr hxlim, hstk⟩, hrel3', hreach'⟩) id
    | .run fr stk H, .run fr' stk' H', ⟨hH_eq, hfr, hstk⟩ =>
      subst H'
      obtain ⟨_, hfn, hblk, fd, b, f0, hflt, hfd, hb, hf0, hdom, hag, hrev, hget, done, f1, hdone, hf1, hnf, hfus⟩ := hfr
      cases hfb : fusable (tables P) (useCounts fd) b with
      | none =>
        obtain ⟨hrest', hterm_eq⟩ := hnf hfb
        cases hrest : fr.rest with
        | nil =>
          simp only [hrest, hoistInstrs, List.nil_append] at hrest' hterm_eq
          have hcovT : ∀ s ∈ collectTerm [] b.term, s ∈ Rt.lowerStrs P := collect_term_mem hflt hfd hb
          obtain ⟨bs_tm, hsb_tm, _⟩ := hoistTerm_spec (P := P) (fresh := f1) (tm := b.term) hcovT
          have heq : { fr' with rest := (hoistTerm (Rt.lowerStrFns P) f1 b.term).1 ++ [] } = fr' := by
            cases fr'; simp only [Cfg.Frame.mk.injEq, true_and, and_true, List.append_nil]; exact hrest'.symm
          have hrel_pre : Rel P' lp ctx (.run { fr' with rest := (hoistTerm (Rt.lowerStrFns P) f1 b.term).1 ++ [] } stk' H) s₃ := by
            rw [heq]; exact hrel3
          rcases run_strBinds_sim ht hsb_tm fr' [] stk' H hrel_pre with ⟨c1, s₃_1, hst1, hrel1⟩ | hf1_fail
          · have hag1 : ∀ y u, fr.env.get? y = some u → (bindStrs fr'.env bs_tm).get? y = some u := by
              intro y u hy
              rw [bindStrs_get_lt hsb_tm fr'.env (Nat.lt_of_lt_of_le (hdom y u hy) hf1)]
              exact hag y u hy
            have hrev1 : ∀ y u, (bindStrs fr'.env bs_tm).get? y = some u →
                fr.env.get? y = some u ∨ ∃ s, u = .lit (.str s) := by
              intro y u hy
              rcases bindStrs_rev bs_tm fr'.env hy with hy' | hstr
              · exact hrev y u hy'
              · exact .inr hstr
            obtain ⟨s₂', hst', hhoist'⟩ := hoist_step_term (fr' := { fr' with rest := [], env := bindStrs fr'.env bs_tm })
              hP' hflt hfd hb hfn hblk hget hterm_eq
              hsb_tm hrest rfl hdom hag1 hrev1 (fun t s hm => bindStrs_get_mem hsb_tm fr'.env hm) hstk hs
            have hsw_mid := hoist_switchSel_env (fr' := { fr' with rest := [], env := bindStrs fr'.env bs_tm })
              (stk' := stk') hP' hflt hfd hb hf0 hfn hblk hget hterm_eq hrest hrev1
              (hsafe _ ⟨c₀, hreach⟩)
            rcases strStep_sim_one ht hrel1 hsw_mid hst' with ⟨c2, s₃_2, hst2, hc2, hrel2⟩ | hf2_fail
            · exact .inl ⟨c1 + c2, s₃_2, hst1.trans hst2, by omega, s₂', hhoist', hrel2, hreach'⟩
            · exact .inr (fails_prepend hst1 hf2_fail)
          · exact .inr hf1_fail
        | cons ins is =>
          obtain ⟨x, r⟩ := ins
          simp only [hrest, hoistInstrs, hoistInstr, List.append_assoc, List.cons_append, List.nil_append] at hrest' hterm_eq
          have hmem : .bind x r ∈ b.body := by rw [hdone, hrest]; simp
          have hx_lt : x < supOf fd := instr_def_lt hb (by rw [← hrest]; exact hdone.symm)
          obtain ⟨bs_r, hsb_r, rfl, hstep_cases⟩ := hoist_step_instr_sim hP' ht hflt hfd hb hf1
            hdom hag hrest hmem hrest' hrel3 hs
          let f1' := (hoistRhs (Rt.lowerStrFns P) f1 r).2.2
          have hf1' : supOf fd ≤ f1' := Nat.le_trans hf1 (hoistRhs_fresh_le _ f1 r)
          have hdone' : b.body = (done ++ [.bind x r]) ++ is := by simpa [hrest] using hdone
          have hag1 : ∀ y u, fr.env.get? y = some u → (bindStrs fr'.env bs_r).get? y = some u := by
            intro y u hy
            rw [bindStrs_get_lt hsb_r fr'.env (Nat.lt_of_lt_of_le (hdom y u hy) hf1)]
            exact hag y u hy
          have hrev1 : ∀ y u, (bindStrs fr'.env bs_r).get? y = some u →
              fr.env.get? y = some u ∨ ∃ s, u = .lit (.str s) := by
            intro y u hy
            rcases bindStrs_rev bs_r fr'.env hy with hy' | hstr
            · exact hrev y u hy'
            · exact .inr hstr
          rcases hstep_cases with ⟨g, as, as', vs, rfl, _, rfl, hsim3⟩ | ⟨v, H', _, rfl, hsim3⟩
          · exact hsim3.imp (fun ⟨c, s₃', hst3, hrel3'⟩ =>
              ⟨c, s₃', hst3, Nat.zero_le _,
                .call g vs (({ fr' with rest := (hoistInstrs (Rt.lowerStrFns P) f1' is).1 ++ (hoistTerm (Rt.lowerStrFns P) (hoistInstrs (Rt.lowerStrFns P) f1' is).2 b.term).1, env := bindStrs fr'.env bs_r }, x) :: stk') H,
                ⟨hP', rfl, rfl, rfl, .cons ⟨rfl,
                  ⟨hP', hfn, hblk, fd, b, f0, hflt, hfd, hb, hf0, hdom, hag1, hrev1, hget,
                    done ++ [.bind x (.fir (.call g as))], f1', hdone', hf1',
                    fun _ => ⟨rfl, hterm_eq⟩, fun _ _ hne _ => absurd hfb hne⟩,
                  fun fd' hfd' => by rw [hfd] at hfd'; cases hfd'; exact hx_lt⟩ hstk⟩, hrel3', hreach'⟩) id
          · refine hsim3.imp (fun ⟨c, s₃', hst3, hrel3'⟩ =>
              ⟨c, s₃', hst3, Nat.zero_le _,
                .run { fr' with rest := (hoistInstrs (Rt.lowerStrFns P) f1' is).1 ++ (hoistTerm (Rt.lowerStrFns P) (hoistInstrs (Rt.lowerStrFns P) f1' is).2 b.term).1, env := (bindStrs fr'.env bs_r).insert x v } stk' H',
                ⟨rfl, ?_, hstk⟩, hrel3', hreach'⟩) id
            refine ⟨hP', hfn, hblk, fd, b, f0, hflt, hfd, hb, hf0, ?_, ?_, ?_, hget,
              done ++ [.bind x r], f1', hdone', hf1',
              fun _ => ⟨rfl, hterm_eq⟩, fun _ _ hne _ => absurd hfb hne⟩
            · intro y u hy
              by_cases hye : y = x
              · subst hye; exact hx_lt
              · rw [NatMap.get?_insert_ne _ _ hye] at hy; exact hdom y u hy
            · intro y u hy
              by_cases hye : y = x
              · subst hye; simpa [NatMap.get?_insert] using hy
              · rw [NatMap.get?_insert_ne _ _ hye] at hy ⊢; exact hag1 y u hy
            · intro y u hy
              by_cases hye : y = x
              · subst hye; exact .inl (by simpa [NatMap.get?_insert] using hy)
              · rw [NatMap.get?_insert_ne _ _ hye] at hy ⊢; exact hrev1 y u hy
      | some p =>
        obtain ⟨xc, opc, ac, ac', huns⟩ := unsnoc_of_fusable hfb
        have hne : fusable (tables P) (useCounts fd) b ≠ none := by simp [hfb]
        rcases hfus p.1 (.bind xc (.fir (.prim opc [ac, ac']))) hne huns with
          ⟨restInit, hfr_eq, hrest', hterm_eq⟩ | ⟨hrest, hrest', fa, bs_tm, hfa, hsb_tm, hterm_eq, hbind⟩
        · cases restInit with
          | nil =>
            simp only [List.nil_append] at hfr_eq
            have hhi0 : hoistInstrs (Rt.lowerStrFns P) f1 [] = ([], f1) := rfl
            rw [hhi0] at hrest' hterm_eq
            dsimp only at hrest' hterm_eq
            rw [List.nil_append] at hrest'
            have hcovT : ∀ s ∈ collectTerm [] b.term, s ∈ Rt.lowerStrs P := collect_term_mem hflt hfd hb
            obtain ⟨bs_tp, hsb_tp, _⟩ := hoistTerm_spec (P := P) (fresh := f1) (tm := b.term) hcovT
            let resT := hoistTerm (Rt.lowerStrFns P) f1 b.term
            let resC := hoistRhs (Rt.lowerStrFns P) resT.2.2 (.fir (.prim opc [ac, ac']))
            have heq : { fr' with rest := resT.1 ++ (resC.1 ++ [.bind xc resC.2.1]) } = fr' := by
              cases fr'; simp only [Cfg.Frame.mk.injEq, true_and, and_true]
              exact hrest'.symm
            have hrel_pre : Rel P' lp ctx
                (.run { fr' with rest := resT.1 ++ (resC.1 ++ [.bind xc resC.2.1]) } stk' H) s₃ := by
              rw [heq]; exact hrel3
            rcases run_strBinds_sim ht hsb_tp fr' (resC.1 ++ [.bind xc resC.2.1]) stk' H hrel_pre with
              ⟨c1, s₃_1, hst1, hrel1⟩ | hf1_fail
            · have hfb_le : supOf fd ≤ resT.2.2 := Nat.le_trans hf1 hsb_tp.le
              have hag_tp : ∀ y u, fr.env.get? y = some u → (bindStrs fr'.env bs_tp).get? y = some u := by
                intro y u hy
                rw [bindStrs_get_lt hsb_tp fr'.env (Nat.lt_of_lt_of_le (hdom y u hy) hf1)]
                exact hag y u hy
              have hrev_tp : ∀ y u, (bindStrs fr'.env bs_tp).get? y = some u →
                  fr.env.get? y = some u ∨ ∃ s, u = .lit (.str s) := by
                intro y u hy
                rcases bindStrs_rev bs_tp fr'.env hy with hy' | hstr
                · exact hrev y u hy'
                · exact .inr hstr
              have hmem : .bind xc (.fir (.prim opc [ac, ac'])) ∈ b.body := by rw [hdone, hfr_eq]; simp
              have hxc_lt : xc < supOf fd := instr_def_lt hb (by rw [← hfr_eq]; exact hdone.symm)
              obtain ⟨bs_r, hsb_r, rfl, hstep_cases⟩ := hoist_step_instr_sim hP' ht hflt hfd hb hfb_le
                hdom hag_tp hfr_eq hmem (tail' := []) rfl hrel1 hs
              rcases hstep_cases with ⟨g, as, _, _, hcontra, _⟩ | ⟨v, H', _, rfl, hsim3⟩
              · cases hcontra
              · rcases hsim3 with ⟨c2, s₃_2, hst2, hrel2⟩ | hf2_fail
                · refine .inl ⟨c1 + c2, s₃_2, hst1.trans hst2, Nat.zero_le _,
                    .run { fr' with rest := [], env := (bindStrs (bindStrs fr'.env bs_tp) bs_r).insert xc v } stk' H',
                    ⟨rfl, ?_, hstk⟩, hrel2, hreach'⟩
                  refine ⟨hP', hfn, hblk, fd, b, f0, hflt, hfd, hb, hf0, ?_, ?_, ?_, hget,
                    done ++ [.bind xc (.fir (.prim opc [ac, ac']))], resC.2.2,
                    by simpa [hfr_eq] using hdone, Nat.le_trans hfb_le hsb_r.le,
                    fun h0 => absurd h0 hne, fun init' cmp' _ huns' => .inr ⟨rfl, rfl, f1, bs_tp, hf1, hsb_tp, hterm_eq, ?_⟩⟩
                  · intro y u hy
                    by_cases hye : y = xc
                    · subst hye; exact hxc_lt
                    · rw [NatMap.get?_insert_ne _ _ hye] at hy; exact hdom y u hy
                  · intro y u hy
                    by_cases hye : y = xc
                    · subst hye; simpa [NatMap.get?_insert] using hy
                    · rw [NatMap.get?_insert_ne _ _ hye] at hy ⊢
                      rw [bindStrs_get_lt hsb_r _ (Nat.lt_of_lt_of_le (hdom y u hy) hfb_le)]
                      exact hag_tp y u hy
                  · intro y u hy
                    by_cases hye : y = xc
                    · subst hye; exact .inl (by simpa [NatMap.get?_insert] using hy)
                    · rw [NatMap.get?_insert_ne _ _ hye] at hy ⊢
                      rcases bindStrs_rev bs_r _ hy with hy' | hstr
                      · exact hrev_tp y u hy'
                      · exact .inr hstr
                  · intro t s hm
                    obtain ⟨hlo, hhi⟩ := hsb_tp.mem_bounds hm
                    have hne_txc : t ≠ xc := Nat.ne_of_gt (Nat.lt_of_lt_of_le hxc_lt (Nat.le_trans hf1 hlo))
                    rw [NatMap.get?_insert_ne _ _ hne_txc, bindStrs_get_lt hsb_r _ hhi]
                    exact bindStrs_get_mem hsb_tp fr'.env hm
                · exact .inr (fails_prepend hst1 hf2_fail)
            · exact .inr hf1_fail
          | cons ins restInit' =>
            obtain ⟨x, r⟩ := ins
            have hfr_eq' : fr.rest = .bind x r :: (restInit' ++ [.bind xc (.fir (.prim opc [ac, ac']))]) := by
              simpa using hfr_eq
            let f1' := (hoistRhs (Rt.lowerStrFns P) f1 r).2.2
            have hhi : hoistInstrs (Rt.lowerStrFns P) f1 (.bind x r :: restInit') =
                ((hoistRhs (Rt.lowerStrFns P) f1 r).1 ++
                  (.bind x (hoistRhs (Rt.lowerStrFns P) f1 r).2.1 :: (hoistInstrs (Rt.lowerStrFns P) f1' restInit').1),
                 (hoistInstrs (Rt.lowerStrFns P) f1' restInit').2) := by
              simp [hoistInstrs, hoistInstr, f1', List.append_assoc]
            rw [hhi] at hrest' hterm_eq
            dsimp only at hrest' hterm_eq
            rw [List.append_assoc, List.append_assoc, List.cons_append] at hrest'
            have hmem : .bind x r ∈ b.body := by rw [hdone, hfr_eq']; simp
            have hx_lt : x < supOf fd := instr_def_lt hb (by rw [← hfr_eq']; exact hdone.symm)
            obtain ⟨bs_r, hsb_r, rfl, hstep_cases⟩ := hoist_step_instr_sim hP' ht hflt hfd hb hf1
              hdom hag hfr_eq' hmem hrest' hrel3 hs
            have hf1' : supOf fd ≤ f1' := Nat.le_trans hf1 (hoistRhs_fresh_le _ f1 r)
            have hdone' : b.body = (done ++ [.bind x r]) ++ (restInit' ++ [.bind xc (.fir (.prim opc [ac, ac']))]) := by
              simpa [hfr_eq'] using hdone
            have hag1 : ∀ y u, fr.env.get? y = some u → (bindStrs fr'.env bs_r).get? y = some u := by
              intro y u hy
              rw [bindStrs_get_lt hsb_r fr'.env (Nat.lt_of_lt_of_le (hdom y u hy) hf1)]
              exact hag y u hy
            have hrev1 : ∀ y u, (bindStrs fr'.env bs_r).get? y = some u →
                fr.env.get? y = some u ∨ ∃ s, u = .lit (.str s) := by
              intro y u hy
              rcases bindStrs_rev bs_r fr'.env hy with hy' | hstr
              · exact hrev y u hy'
              · exact .inr hstr
            rcases hstep_cases with ⟨g, as, as', vs, rfl, _, rfl, hsim3⟩ | ⟨v, H', _, rfl, hsim3⟩
            · let tailF := (hoistInstrs (Rt.lowerStrFns P) f1' restInit').1 ++
                  ((hoistTerm (Rt.lowerStrFns P) (hoistInstrs (Rt.lowerStrFns P) f1' restInit').2 b.term).1 ++
                   (hoistInstr (Rt.lowerStrFns P) (hoistTerm (Rt.lowerStrFns P) (hoistInstrs (Rt.lowerStrFns P) f1' restInit').2 b.term).2.2
                     (.bind xc (.fir (.prim opc [ac, ac'])))).1)
              refine hsim3.imp (fun ⟨c, s₃', hst3, hrel3'⟩ =>
                ⟨c, s₃', hst3, Nat.zero_le _,
                  .call g vs (({ fr' with rest := tailF, env := bindStrs fr'.env bs_r }, x) :: stk') H,
                  ⟨hP', rfl, rfl, rfl, .cons ⟨rfl, ?_, ?_⟩ hstk⟩, hrel3', hreach'⟩) id
              · refine ⟨hP', hfn, hblk, fd, b, f0, hflt, hfd, hb, hf0, hdom, hag1, hrev1, hget,
                  done ++ [.bind x (.fir (.call g as))], f1', hdone', hf1',
                  fun h0 => absurd h0 hne, fun init' cmp' _ huns' => ?_⟩
                rw [huns] at huns'; cases huns'
                exact .inl ⟨restInit', rfl, ⟨(List.append_assoc _ _ _).symm, hterm_eq⟩⟩
              · intro fd' hfd'; rw [hfd] at hfd'; cases hfd'; exact hx_lt
            · let tailF := (hoistInstrs (Rt.lowerStrFns P) f1' restInit').1 ++
                  ((hoistTerm (Rt.lowerStrFns P) (hoistInstrs (Rt.lowerStrFns P) f1' restInit').2 b.term).1 ++
                   (hoistInstr (Rt.lowerStrFns P) (hoistTerm (Rt.lowerStrFns P) (hoistInstrs (Rt.lowerStrFns P) f1' restInit').2 b.term).2.2
                     (.bind xc (.fir (.prim opc [ac, ac'])))).1)
              refine hsim3.imp (fun ⟨c, s₃', hst3, hrel3'⟩ =>
                ⟨c, s₃', hst3, Nat.zero_le _,
                  .run { fr' with rest := tailF, env := (bindStrs fr'.env bs_r).insert x v } stk' H',
                  ⟨rfl, ?_, hstk⟩, hrel3', hreach'⟩) id
              refine ⟨hP', hfn, hblk, fd, b, f0, hflt, hfd, hb, hf0, ?_, ?_, ?_, hget,
                done ++ [.bind x r], f1', hdone', hf1',
                fun h0 => absurd h0 hne, fun init' cmp' _ huns' => ?_⟩
              · intro y u hy
                by_cases hye : y = x
                · subst hye; exact hx_lt
                · rw [NatMap.get?_insert_ne _ _ hye] at hy; exact hdom y u hy
              · intro y u hy
                by_cases hye : y = x
                · subst hye; simpa [NatMap.get?_insert] using hy
                · rw [NatMap.get?_insert_ne _ _ hye] at hy ⊢; exact hag1 y u hy
              · intro y u hy
                by_cases hye : y = x
                · subst hye; exact .inl (by simpa [NatMap.get?_insert] using hy)
                · rw [NatMap.get?_insert_ne _ _ hye] at hy ⊢; exact hrev1 y u hy
              · rw [huns] at huns'; cases huns'
                exact .inl ⟨restInit', rfl, ⟨(List.append_assoc _ _ _).symm, hterm_eq⟩⟩
        · -- Fused block terminator: `fr.rest = []`, `fr'.rest = []`, `bs_tm` already bound!
          obtain ⟨s₂', hst', hhoist'⟩ := hoist_step_term hP' hflt hfd hb hfn hblk hget hterm_eq
            hsb_tm hrest hrest' hdom hag hrev hbind hstk hs
          have hsw_fus := hoist_switchSel_env (stk' := stk') hP' hflt hfd hb hf0 hfn hblk hget hterm_eq hrest hrev
            (hsafe _ ⟨c₀, hreach⟩)
          exact (strStep_sim_one ht hrel3 hsw_fus hst').imp
            (fun ⟨c, s₃', hst3, hc, hrel3'⟩ => ⟨c, s₃', hst3, hc, s₂', hhoist', hrel3', hreach'⟩) id
    | .call .., .ret .., h | .call .., .run .., h
    | .ret .., .call .., h | .ret .., .run .., h
    | .run .., .call .., h | .run .., .ret .., h => cases h
  final := by
    intro s₁ s₃ r ⟨s₂, hhoist, hrel3, _⟩ hf hr
    have hres_eq : Res P' ctx = Res P ctx := by subst hP'; rfl
    rw [← hres_eq]
    match s₁, s₂, hhoist, hf with
    | .call g vs stk H, .call .., _, hf =>
      exfalso
      simp only [Cfg.step] at hf
      split at hf
      · split at hf
        · split at hf
          · cases hf
          · cases hf; exact hr rfl
        · cases hf; exact hr rfl
      · cases hf; exact hr rfl
    | .ret rv [] H, .ret rv' [] H', ⟨_, hv_eq, hH_eq, .nil⟩, hf =>
      subst rv'; subst H'
      simp only [Cfg.step] at hf
      cases hf
      exact strStep_sim_final (P := P) hrel3 (by simp [strStep, Cfg.step]; exact .done) hr
    | .ret _ (_ :: _) _, .ret .., _, hf => simp only [Cfg.step] at hf; cases hf
    | .run fr stk H, .run fr' stk' H', ⟨hH_eq, hfr, _⟩, hf =>
      subst H'
      obtain ⟨_, hfn, hblk, fd, b, f0, hflt, hfd, hb, hf0, hdom, hag, hrev, hget, done, f1, hdone, hf1, hnf, hfus⟩ := hfr
      cases hrest : fr.rest with
      | nil =>
        cases hst : Cfg.step .immortal P (.run fr stk H) with
        | trap =>
          rw [hst] at hf; cases hf
          simp only [Cfg.step, hrest, hfd, Cfg.Fun.block?, hb] at hst
          have hbt : b.term = .trap := by
            cases htm : b.term with
            | jump e =>
              simp only [htm, Cfg.takeEdge] at hst
              split at hst
              · split at hst <;> cases hst
              · cases hst
            | switch x alts d =>
              simp only [htm] at hst
              split at hst
              · split at hst
                · split at hst
                  · simp only [Cfg.takeEdge] at hst
                    split at hst
                    · split at hst <;> cases hst
                    · cases hst
                  · cases hst
                · cases hst
              · cases hst
            | ret a => simp only [htm] at hst; split at hst <;> cases hst
            | tcall g as => simp only [htm] at hst; split at hst <;> cases hst
            | trap => rfl
          have hfd' : P'.fun? fr'.fn = some (hoistFun (tables P) (Rt.lowerStrFns P) fd) := by
            rw [hfn, hP', hoistStrings_fun? hflt, hfd]; rfl
          have hblk' : (hoistFun (tables P) (Rt.lowerStrFns P) fd).blocks[fr'.blk]? =
              some (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1 := by
            rw [hblk]; exact hget
          have hfb_none : fusable (tables P) (useCounts fd) b = none := by
            unfold fusable; simp [hbt]
          obtain ⟨hrest', hterm_eq⟩ := hnf hfb_none
          simp only [hrest, hoistInstrs, hbt, List.nil_append] at hrest' hterm_eq
          have htr2 : strStep P P' (.run fr' stk' H) = .trap := by
            simp [strStep, Cfg.step, hrest', hfd', Cfg.Fun.block?, hblk', hterm_eq]
          exact strStep_sim_final hrel3 (by rw [htr2]; exact .trap) hr
        | stuck => rw [hst] at hf; cases hf; exact absurd rfl hr
        | next _ _ => rw [hst] at hf; cases hf
        | done _ =>
          exfalso
          simp only [Cfg.step, hrest] at hst
          split at hst
          · split at hst
            · split at hst
              · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
              · split at hst
                · split at hst
                  · split at hst
                    · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
                    · cases hst
                  · cases hst
                · cases hst
              · split at hst <;> cases hst
              · split at hst <;> cases hst
              · cases hst
            · cases hst
          · cases hst
        | fail _ =>
          exfalso
          simp only [Cfg.step, hrest] at hst
          split at hst
          · split at hst
            · split at hst
              · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
              · split at hst
                · split at hst
                  · split at hst
                    · simp [Cfg.takeEdge] at hst; split at hst <;> (try split at hst) <;> cases hst
                    · cases hst
                  · cases hst
                · cases hst
              · split at hst <;> cases hst
              · split at hst <;> cases hst
              · cases hst
            · cases hst
          · cases hst
      | cons ins is =>
        exfalso
        obtain ⟨x, r'⟩ := ins
        by_cases hcall : ∃ g as, r' = .fir (.call g as)
        · obtain ⟨g, as, rfl⟩ := hcall
          simp only [Cfg.step, hrest] at hf
          split at hf
          · cases hf
          · cases hf; exact hr rfl
        · rw [step_bind hrest (fun g as h => hcall ⟨g, as, h⟩)] at hf
          rcases evalRhs_ok_or_stuck (T := P.tables) (ρ := fr.env) (H := H) r' with ⟨p, hp⟩ | hp
          · rw [hp] at hf; cases hf
          · rw [hp] at hf; cases hf; exact hr rfl
    | .call .., .ret .., h, _ | .call .., .run .., h, _
    | .ret .., .call .., h, _ | .ret .., .run .., h, _
    | .run .., .call .., h, _ | .run .., .ret .., h, _ => cases h

/-! ## 4. Structural properties of `hoistStrings` (`params`, `dense`, `Ordered`, entry) -/

/-- `lowerCfg P` preserves `Cfg.Fun.params` for every function `< P.size`. -/
theorem lowerCfg_fun? {P : Cfg.Program} {f : Nat} (hf : f < P.size) :
    (Rt.lowerCfg P).fun? f =
      if (Rt.lowerStrs P).isEmpty then P.fun? f
      else (P.fun? f).map (hoistFun (tables P) (Rt.lowerStrFns P)) := by
  unfold Rt.lowerCfg
  split
  · rfl
  · exact hoistStrings_fun? hf

/-- `lowerCfg P` preserves `size`, `tables`, and `dense`. -/
theorem hoistStrings_dense {P : Cfg.Program} (strFns : List (String × Fir.FunId))
    (hdense : ∀ {f : Nat} {fd : Cfg.Fun}, P.fun? f = some fd → f < P.size) :
    ∀ {f : Nat} {fd : Cfg.Fun}, (hoistStrings P strFns).fun? f = some fd → f < P.size := by
  intro f fd hfd
  unfold hoistStrings Cfg.Program.fun? at hfd
  dsimp only at hfd
  have aux : ∀ (fs : List Nat) (m : Src.NatMap Cfg.Fun),
      (∀ k v, m.get? k = some v → k < P.size) →
      (∀ k ∈ fs, k < P.size) →
      ∀ k v, (fs.foldl (fun m f => match P.funs.get? f with
        | some fd => m.insert f (hoistFun (tables P) strFns fd)
        | none => m) m).get? k = some v → k < P.size := by
    intro fs
    induction fs with
    | nil => intro m hm _ k v h; exact hm k v h
    | cons a fs ih =>
      intro m hm hfs k v h
      apply ih _ _ (fun j hj => hfs j (by simp [hj])) k v h
      intro j w hj
      dsimp only at hj
      cases ha : P.funs.get? a with
      | none => rw [ha] at hj; exact hm j w hj
      | some fda =>
        rw [ha] at hj
        by_cases hja : j = a
        · subst hja; exact hfs j (by simp)
        · rw [Src.NatMap.get?_insert_ne _ _ hja] at hj; exact hm j w hj
  exact aux (List.range P.size) P.funs (fun k v hk => hdense hk)
    (fun k hk => List.mem_range.1 hk) f fd hfd

/-- `Cfg.Ordered` transfers backwards from `hoistStrings P (lowerStrFns P)` to `P`. -/
theorem hoistStrings_ordered {P P' : Cfg.Program}
    (hP' : P' = hoistStrings P (Rt.lowerStrFns P))
    (hdense : ∀ {f fd}, P.fun? f = some fd → f < P.size)
    (ho : Cfg.Ordered P') : Cfg.Ordered P where
  dense := hdense
  forward := by
    intro f fd blk b e hfd hb he hback
    have hf : f < P.size := hdense hfd
    have hfd' : P'.fun? f = some (hoistFun (tables P) (Rt.lowerStrFns P) fd) := by
      rw [hP', hoistStrings_fun? hf, hfd]; rfl
    obtain ⟨f0, _, hget⟩ := hoistBlocks_getElem? (tables P) (useCounts fd) (Rt.lowerStrFns P)
      (supOf fd) fd.blocks blk b hb
    -- Every edge of `b.term` appears in `(hoistBlock ... f0 b).1.term` with same `target` & `back`
    have hterm_fa : ∃ fa, (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b).1.term =
        (hoistTerm (Rt.lowerStrFns P) fa b.term).2.1 := by
      unfold hoistBlock
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    obtain ⟨fa, hterm_eq⟩ := hterm_fa
    have hedge : ∃ e', e' ∈ (hoistTerm (Rt.lowerStrFns P) fa b.term).2.1.edges ∧
        e'.target = e.target ∧ e'.back = e.back := by
      cases htm : b.term with
      | jump e0 =>
        simp only [htm, Cfg.Term.edges, List.mem_singleton] at he
        subst he
        exact ⟨(hoistEdge (Rt.lowerStrFns P) fa e).2.1, by simp [hoistTerm, Cfg.Term.edges], rfl, rfl⟩
      | switch x alts d =>
        simp only [htm, Cfg.Term.edges, List.mem_append, List.mem_map] at he
        rcases he with ⟨⟨k, e0⟩, hm, rfl⟩ | hd
        · have hal : ∀ (al : List (Key.CtorKey × Cfg.Edge)) (fr0 : Nat),
              (k, e0) ∈ al → ∃ e', e' ∈ (hoistAlts (Rt.lowerStrFns P) fr0 al).2.1.map (·.2) ∧
                e'.target = e0.target ∧ e'.back = e0.back := by
            intro al
            induction al with
            | nil => intro _ h; cases h
            | cons p al ih =>
              intro fr0 hm'
              rcases List.mem_cons.1 hm' with rfl | hm''
              · exact ⟨(hoistEdge (Rt.lowerStrFns P) fr0 e0).2.1, by simp [hoistAlts], rfl, rfl⟩
              · obtain ⟨e', he', ht', hb'⟩ := ih (hoistEdge (Rt.lowerStrFns P) fr0 p.2).2.2 hm''
                exact ⟨e', by simp [hoistAlts, he'], ht', hb'⟩
          obtain ⟨e', he', ht', hb'⟩ := hal alts fa hm
          exact ⟨e', by simp [hoistTerm, Cfg.Term.edges, he'], ht', hb'⟩
        · cases d with
          | none => simp at hd
          | some e0 =>
            simp only [Option.mem_toList, Option.some.injEq] at hd
            subst hd
            exact ⟨(hoistEdge (Rt.lowerStrFns P) (hoistAlts (Rt.lowerStrFns P) fa alts).2.2 e0).2.1,
              by simp [hoistTerm, hoistOptEdge, Cfg.Term.edges], rfl, rfl⟩
      | ret _ | tcall _ _ | trap => simp [htm, Cfg.Term.edges] at he
    obtain ⟨e', he', htgt, hbk⟩ := hedge
    have hlt := ho.forward hfd' (by unfold supOf at hget; unfold Cfg.Fun.block? hoistFun; exact hget)
      (by rw [hterm_eq]; exact he') (by rw [hbk]; exact hback)
    rw [htgt] at hlt
    exact hlt

/-- Entry-frame correspondence for `hoistStrings P (lowerStrFns P)`. -/
theorem hoistStrings_entry {P P' : Cfg.Program} (hP' : P' = hoistStrings P (Rt.lowerStrFns P))
    {g : Nat} {fd : Cfg.Fun} {b0 : Cfg.Block} {args : List Own.RVal} {H : Own.Heap}
    (hg : g < P.size) (hfd : P.fun? g = some fd) (hb0 : fd.blocks[0]? = some b0) :
    ∃ fd' b0', P'.fun? g = some fd' ∧ fd'.blocks[0]? = some b0' ∧ b0'.params = b0.params ∧
      HoistRel P P'
        (.run { fn := g, blk := 0, rest := b0.body, env := Own.bindAll .leaf (b0.params.map (·.1)) args } [] H)
        (.run { fn := g, blk := 0, rest := b0'.body, env := Own.bindAll .leaf (b0'.params.map (·.1)) args } [] H) := by
  have hba := bindAll_dom_ag (b0.params.map (·.1)) args .leaf .leaf (params_lt_sup hb0)
    (fun _ _ h => nomatch h) (fun _ _ h => h) (fun _ _ h => .inl h)
  obtain ⟨f0, _, hget, hframe⟩ := hoistFrame_of_block hP' hg hfd hb0
    (ρ := Own.bindAll .leaf (b0.params.map (·.1)) args)
    (ρ' := Own.bindAll .leaf (b0.params.map (·.1)) args)
    hba.1 hba.2.1 hba.2.2
  have hpar := hoistBlock_params (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b0
  refine ⟨hoistFun (tables P) (Rt.lowerStrFns P) fd,
    (hoistBlock (tables P) (useCounts fd) (Rt.lowerStrFns P) f0 b0).1,
    by rw [hP', hoistStrings_fun? hg, hfd]; rfl, hget, hpar, rfl, ?_, .nil⟩
  simpa [hpar] using hframe

end IxCC.Rt.Proof

