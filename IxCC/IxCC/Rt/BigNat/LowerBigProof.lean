import IxCC.Rt.BigNat.LowerBig
import IxCC.Rt.BigNat.Proof
import IxCC.Rt.Proof.ReadbackCongr

/-! # Phase 4 Arbitrary-Precision `Nat` Lowering & Zero-`natOverflow` Proofs (`IxCC.Rt.BigNat.LowerBigProof`)

Establishes the formal correctness and zero-`.fail .natOverflow` invariants of Phase 4
arbitrary-precision `Nat` lowering (`IxCC.Rt.BigNat.LowerBig` & `IxCC.Rt.BigNat.Link`):

1. **Structural & Semantic Zero-`natOverflow` Theorems:**
   - `lirProgramNoOvf_iff_checkEmpty`: exact equivalence between structural
     `LirProgramNoOvf` and `IxCC.BigNat.Bootstrap.checkLirHasNoNatOverflow prog = []`.
   - `lirStep_ne_natOverflow`, `semStep_ne_natOverflow`, `failsNoOvf_of_noNatOverflow`,
     `lirRun_ne_natOverflow`, `lirEval_ne_natOverflow`:
     NO LIR program whose functions satisfy `LirFuncNoOvf` can EVER fail with `.natOverflow`!
   - `functionBig_noNatOverflow`, `functionsBig_noNatOverflow`, `arrayPrimFuncBig_noNatOverflow`,
     `functionRepBig_noNatOverflow`, `functionsRepBig_noNatOverflow`, `bigNatLitProc_noNatOverflow`,
     `strLitProc_noNatOverflow`, `cxInit_noNatOverflow`, `natPowBig_noNatOverflow`,
     `natGcdBig_noNatOverflow`, `extendedArrayRuntimeFuncs_noNatOverflow`,
     `buildCoreWrappers_noNatOverflow`.
   - **`lowerBig_noNatOverflow`** and **`lowerRepBig_noNatOverflow`**:
     EVERY user function `0 ..< P.size`, `cxInit`, `natPowBig`, `natGcdBig`, array runtime proc,
     literal materializer proc, and `BigNat` ABI wrapper lowered by `lowerBig` / `lowerRepBig`
     contains ZERO `.fail .natOverflow` blocks!
2. **Static `.rodata` `≥ 2^63` Literal Proofs:**
   - `buildBigNatRodataK_eq`: `buildBigNatRodataK nats = buildBigNatRodata nats`.
   - `buildBigNatRodata_natVal`: every `(n, off)` built by `buildBigNatRodata` (with `n ≥ 2^63`)
     satisfies `NatVal mem n (base + UInt64.ofNat off)` and reads back via `Rt.readbackBig` to
     `some (.nat n)` under `RodataMapped base tbl.bytes mem`.
3. **End-to-End Arbitrary-Precision Simulation under `FailsNoOvf` + `Rt.readbackBig`:**
   - `readbackBig_congr`: `SameReadable m₁ m₂ → Rt.readbackBig sig fuel m₁ ty w = Rt.readbackBig sig fuel m₂ ty w`.
   - `natSwitchBig_isZero_iff`: `NatVal mem n w → (w = 1 ↔ n = 0)` (exact across all `Nat`).
   - `operandBig_nat_sim`: arbitrary-precision `Nat` literal evaluation via `.rodata`
     or `bigNatLitProc` under `FailsNoOvf`.
   - `primitiveBig_sim_readback_noOvf` & `projBig_natSucc_sim_readback_noOvf`: full composition of
     `PrimCoreBig` / `natSuccPeelBig_core` with `Rt.readbackBig` under `FailsNoOvf` (STRICTLY NO
     `.natOverflow` disjunct!).

Strictly standard axioms `[propext, Classical.choice, Quot.sound]`; zero `sorry`. -/

set_option autoImplicit false

namespace IxCC.Rt.BigNat

open IxCC
open IxCC.BigNat.Bootstrap (checkLirHasNoNatOverflow)
open IxCC.Fir (FunId)
open IxCC.Lir (VReg Label Word)
open IxCC.Rt
open IxCC.Rt.Lower
open IxCC.Rt.LowerRep
open IxCC.Rt.Proof
open IxCC.Rt.Rc.Array
open IxCC.Src (NatMap)
open IxCC.X86 (Memory)
open IxCC.X86.ELFRodata

/-! ## Section 1: Structural & Semantic Zero-`.fail .natOverflow` Predicates -/

def PTermNoOvf : PTerm → Prop
  | .fail .natOverflow => False
  | _ => True

def PBlockNoOvf (b : PBlock) : Prop :=
  PTermNoOvf b.term

def StNoOvf (st : St) : Prop :=
  ∀ l b, st.done.get? l = some b → PBlockNoOvf b

def LirTermNoOvf : Lir.Term → Prop
  | .fail .natOverflow => False
  | _ => True

def LirBlockNoOvf (b : Lir.Block) : Prop :=
  LirTermNoOvf b.term

def LirFuncNoOvf (f : Lir.Func) : Prop :=
  ∀ b ∈ f.blocks.toList, LirBlockNoOvf b

def LirProgramNoOvf (p : Lir.Program) : Prop :=
  ∀ f ∈ p.funcs.toList, LirFuncNoOvf f

theorem lirTermNoOvf_iff (t : Lir.Term) : LirTermNoOvf t ↔ t ≠ .fail .natOverflow := by
  cases t with
  | fail r => cases r <;> simp [LirTermNoOvf]
  | _ => simp [LirTermNoOvf]

/-- `LirFuncNoOvf f` holds iff every indexed block `f.blocks[l]? = some b` has `b.term ≠ .fail .natOverflow`. -/
theorem LirFuncNoOvf.of_getElem? {f : Lir.Func} (h : LirFuncNoOvf f) {l : Nat} {b : Lir.Block}
    (hb : f.blocks[l]? = some b) : LirBlockNoOvf b :=
  h b (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb))

private theorem mem_of_mem_zipIdx {α : Type} {xs : List α} {x : α} {i : Nat}
    (h : (x, i) ∈ xs.zipIdx) : x ∈ xs := by
  have haux : ∀ (ys : List α) (k : Nat), (x, i) ∈ ys.zipIdx k → x ∈ ys := by
    intro ys
    induction ys with
    | nil => intro _ hm; cases hm
    | cons y ys ih =>
      intro k hm
      simp only [List.zipIdx_cons, List.mem_cons, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, _⟩ | hm'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (k + 1) hm')
  exact haux xs 0 h

/-- Exact equivalence between `LirProgramNoOvf p` and `Bootstrap.checkLirHasNoNatOverflow p = []`. -/
theorem lirProgramNoOvf_iff_checkEmpty (p : Lir.Program) :
    LirProgramNoOvf p ↔ checkLirHasNoNatOverflow p = [] := by
  unfold checkLirHasNoNatOverflow LirProgramNoOvf LirFuncNoOvf LirBlockNoOvf
  constructor
  · intro h
    rw [List.flatMap_eq_nil_iff]
    intro ⟨f, fi⟩ hmem
    have hf : f ∈ p.funcs.toList := mem_of_mem_zipIdx hmem
    rw [List.filterMap_eq_nil_iff]
    intro ⟨b, bi⟩ hbm
    have hb : b ∈ f.blocks.toList := mem_of_mem_zipIdx hbm
    have hno := h f hf b hb
    cases ht : b.term with
    | fail r =>
      cases r with
      | natOverflow => rw [ht] at hno; exact False.elim hno
      | heap => simp [ht]
      | stack => simp [ht]
    | jump _ => simp [ht]
    | br _ _ _ _ _ _ => simp [ht]
    | brOvf _ _ _ _ _ _ => simp [ht]
    | ret _ => simp [ht]
    | tail _ _ => simp [ht]
    | trap => simp [ht]
  · intro h f hf b hb
    rw [List.flatMap_eq_nil_iff] at h
    obtain ⟨fi, hfi, rfl⟩ := List.getElem_of_mem hf
    obtain ⟨bi, hbi, rfl⟩ := List.getElem_of_mem hb
    have hfmem : (p.funcs.toList[fi], fi) ∈ p.funcs.toList.zipIdx := by
      rw [List.mem_iff_getElem]
      exact ⟨fi, by simpa using hfi, by simp⟩
    have hfm := h _ hfmem
    rw [List.filterMap_eq_nil_iff] at hfm
    have hbmem : (p.funcs.toList[fi].blocks.toList[bi], bi) ∈
        p.funcs.toList[fi].blocks.toList.zipIdx := by
      rw [List.mem_iff_getElem]
      exact ⟨bi, by simpa using hbi, by simp⟩
    have hnone := hfm _ hbmem
    cases ht : p.funcs.toList[fi].blocks.toList[bi].term with
    | fail r =>
      cases r with
      | natOverflow =>
        simp only [Array.getElem_toList] at ht
        simp [ht] at hnone
      | _ => trivial
    | _ => trivial

private theorem takeEdge_ne_fail (f : Lir.Func) (s : Lir.State) (fr : Lir.Frame)
    (rest : List Lir.Frame) (ρ : Lir.Env) (e : Lir.Edge) (r : Sem.Resource) :
    Lir.takeEdge f s fr rest ρ e ≠ .fail r := by
  unfold Lir.takeEdge
  split
  · split <;> (intro h; cases h)
  · intro h; cases h

/-- A single `Lir.step` in a `LirProgramNoOvf` program can NEVER return `.fail .natOverflow`. -/
theorem lirStep_ne_natOverflow {p : Lir.Program} (hp : LirProgramNoOvf p) (s : Lir.State) :
    Lir.step p s ≠ .fail .natOverflow := by
  unfold Lir.step
  cases hs : s.stack with
  | nil => intro h; cases h
  | cons fr rest =>
    dsimp only
    cases hf : p.funcs[fr.fn]? with
    | none => intro h; cases h
    | some f =>
      dsimp only
      cases hb : f.blocks[fr.label]? with
      | none => intro h; cases h
      | some b =>
        dsimp only
        split
        · split
          · split <;> (intro h; cases h)
          · split <;> (intro h; cases h)
        · have hno : LirBlockNoOvf b :=
            (hp f (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hf))).of_getElem? hb
          cases ht : b.term with
          | jump e =>
            dsimp only
            exact takeEdge_ne_fail _ _ _ _ _ _ _
          | br c w a b' t e =>
            dsimp only
            cases Lir.Arg.eval fr.env a with
            | none => intro h; cases h
            | some va =>
              cases Lir.Arg.eval fr.env b' with
              | none => intro h; cases h
              | some vb => exact takeEdge_ne_fail _ _ _ _ _ _ _
          | brOvf o x a b' ok ovf =>
            dsimp only
            cases Lir.Arg.eval fr.env a with
            | none => intro h; cases h
            | some va =>
              cases Lir.Arg.eval fr.env b' with
              | none => intro h; cases h
              | some vb => exact takeEdge_ne_fail _ _ _ _ _ _ _
          | ret as =>
            dsimp only
            cases Lir.evalArgs fr.env as with
            | none => intro h; cases h
            | some vals =>
              cases rest with
              | nil => intro h; cases h
              | cons caller rest' =>
                dsimp only
                cases Lir.bindParams caller.env caller.dsts vals <;> (intro h; cases h)
          | tail g as =>
            dsimp only
            cases (Lir.evalArgs fr.env as >>= Lir.enter p g) <;> (intro h; cases h)
          | fail r =>
            dsimp only
            rw [LirBlockNoOvf, ht] at hno
            cases r with
            | natOverflow => exact False.elim hno
            | heap => intro heq; cases heq
            | stack => intro heq; cases heq
          | trap => dsimp only; intro h; cases h

/-- `Lir.semStep` in a `LirProgramNoOvf` program can NEVER return `.fail .natOverflow`. -/
theorem semStep_ne_natOverflow {p : Lir.Program} (hp : LirProgramNoOvf p) (s : Lir.State) :
    Lir.semStep p s ≠ .fail .natOverflow := by
  have h := lirStep_ne_natOverflow hp s
  unfold Lir.semStep
  cases hst : Lir.step p s with
  | next _ _ => intro heq; cases heq
  | done _ _ => intro heq; cases heq
  | fail r =>
    intro heq
    cases heq
    exact h hst
  | trap => intro heq; cases heq
  | stuck => intro heq; cases heq

/-- Any `Sem.Fails` in a `LirProgramNoOvf` program automatically strengthens to `FailsNoOvf`. -/
theorem failsNoOvf_of_noNatOverflow {p : Lir.Program} (hp : LirProgramNoOvf p) {s : Lir.State}
    (hf : Sem.Fails (Lir.semStep p) s) : FailsNoOvf p s := by
  obtain ⟨c, s', r, hstar, hstep⟩ := hf
  refine ⟨c, s', r, hstar, hstep, ?_⟩
  intro hr
  rw [hr] at hstep
  exact semStep_ne_natOverflow hp s' hstep

/-- `Lir.run` on a `LirProgramNoOvf` program NEVER returns `.resource .natOverflow`. -/
theorem lirRun_ne_natOverflow {p : Lir.Program} (hp : LirProgramNoOvf p) :
    ∀ (fuel k : Nat) (s : Lir.State), Lir.run p fuel k s ≠ .resource .natOverflow
  | 0, _, _ => by intro heq; cases heq
  | fuel + 1, k, s => by
    unfold Lir.run
    have hstep := lirStep_ne_natOverflow hp s
    cases hs : Lir.step p s with
    | next s' charge =>
      cases charge with
      | false => exact lirRun_ne_natOverflow hp fuel k s'
      | true =>
        cases k with
        | zero => intro heq; cases heq
        | succ k' => exact lirRun_ne_natOverflow hp fuel k' s'
    | done _ _ => intro heq; cases heq
    | fail r =>
      intro heq
      cases heq
      exact hstep hs
    | trap => intro heq; cases heq
    | stuck => intro heq; cases heq

/-- **`Lir.eval` on any `LirProgramNoOvf` program NEVER returns `.resource .natOverflow`.** -/
theorem lirEval_ne_natOverflow {p : Lir.Program} (hp : LirProgramNoOvf p)
    (k : Nat) (args : List Word) (mem : Memory) (ctx : Word) :
    Lir.eval p k args mem ctx ≠ .resource .natOverflow := by
  unfold Lir.eval
  cases Lir.State.initial p args mem ctx with
  | none => intro heq; cases heq
  | some s => exact lirRun_ne_natOverflow hp (Lir.fuelFor p k) k s

/-! ## Section 2: Resolution, Pruning & Critical-Edge Splitting Preservation -/

private theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem resolveTerm_noNatOverflow {f : FunId} {off : Nat} {starts : NatMap Nat}
    {pt : PTerm} {lt : Lir.Term} (hpt : PTermNoOvf pt)
    (hres : resolveTerm f off starts pt = .ok lt) : LirTermNoOvf lt := by
  cases pt with
  | jump e =>
    unfold resolveTerm at hres
    cases he : resolveEdge f off starts e with
    | error _ => simp [he, bind, Except.bind] at hres
    | ok e' =>
      simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres
      subst hres; trivial
  | br c a b t e =>
    unfold resolveTerm at hres
    cases ht : resolveEdge f off starts t with
    | error _ => simp [ht, bind, Except.bind] at hres
    | ok t' =>
      cases he : resolveEdge f off starts e with
      | error _ => simp [ht, he, bind, Except.bind] at hres
      | ok e' =>
        simp only [ht, he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres
        subst hres; trivial
  | brOvf o x a b ok ovf =>
    unfold resolveTerm at hres
    cases hok : resolveEdge f off starts ok with
    | error _ => simp [hok, bind, Except.bind] at hres
    | ok ok' =>
      cases hovf : resolveEdge f off starts ovf with
      | error _ => simp [hok, hovf, bind, Except.bind] at hres
      | ok ovf' =>
        simp only [hok, hovf, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres
        subst hres; trivial
  | ret a =>
    simp only [resolveTerm, pure, Except.pure, Except.ok.injEq] at hres
    subst hres; trivial
  | tail g as =>
    simp only [resolveTerm, pure, Except.pure, Except.ok.injEq] at hres
    subst hres; trivial
  | fail r =>
    simp only [resolveTerm, pure, Except.pure, Except.ok.injEq] at hres
    subst hres
    cases r with
    | natOverflow => exact False.elim hpt
    | _ => trivial
  | trap =>
    simp only [resolveTerm, pure, Except.pure, Except.ok.injEq] at hres
    subst hres; trivial

theorem resolveBlock_noNatOverflow {f : FunId} {off : Nat} {starts : NatMap Nat}
    {pb : PBlock} {lb : Lir.Block} (hpb : PBlockNoOvf pb)
    (hres : resolveBlock f off starts pb = .ok lb) : LirBlockNoOvf lb := by
  unfold resolveBlock at hres
  cases ht : resolveTerm f off starts pb.term with
  | error _ => simp [ht, bind, Except.bind] at hres
  | ok lt =>
    simp only [ht, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres
    subst hres
    exact resolveTerm_noNatOverflow hpb ht

private theorem mapM_resolveBlock_noNatOverflow {f : FunId} {off : Nat} {starts : NatMap Nat} :
    ∀ {pbs : List PBlock} {lbs : List Lir.Block},
      (∀ pb ∈ pbs, PBlockNoOvf pb) →
      pbs.mapM (resolveBlock f off starts) = .ok lbs →
      ∀ lb ∈ lbs, LirBlockNoOvf lb
  | [], lbs, _, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro _ hm; cases hm
  | pb :: pbs, lbs, hall, h => by
    rw [List.mapM_cons] at h
    cases hb : resolveBlock f off starts pb with
    | error _ => simp [hb, bind, Except.bind] at h
    | ok lb =>
      simp only [hb, bind, Except.bind] at h
      cases hrest : pbs.mapM (resolveBlock f off starts) with
      | error _ => simp [hrest] at h
      | ok rest =>
        simp only [hrest, pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro b hm
        cases hm with
        | head => exact resolveBlock_noNatOverflow (hall pb List.mem_cons_self) hb
        | tail _ hm' =>
          exact mapM_resolveBlock_noNatOverflow (fun x hx => hall x (List.mem_cons_of_mem _ hx)) hrest b hm'

theorem resolveChunks_noNatOverflow {f : FunId} {starts : NatMap Nat} :
    ∀ {cs : List (List PBlock × Nat)} {lbs : List Lir.Block},
      (∀ c ∈ cs, ∀ pb ∈ c.1, PBlockNoOvf pb) →
      resolveChunks f starts cs = .ok lbs →
      ∀ lb ∈ lbs, LirBlockNoOvf lb
  | [], lbs, _, h => by
    simp only [resolveChunks, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro _ hm; cases hm
  | (c, i) :: cs, lbs, hall, h => by
    unfold resolveChunks at h
    cases hbs : c.mapM (resolveBlock f (starts.getD i 0) starts) with
    | error _ => simp [hbs, bind, Except.bind] at h
    | ok bs =>
      simp only [hbs, bind, Except.bind] at h
      cases hrest : resolveChunks f starts cs with
      | error _ => simp [hrest] at h
      | ok rest =>
        simp only [hrest, pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro b hm
        rcases List.mem_append.mp hm with h1 | h2
        · exact mapM_resolveBlock_noNatOverflow (hall (c, i) List.mem_cons_self) hbs b h1
        · exact resolveChunks_noNatOverflow (fun x hx => hall x (List.mem_cons_of_mem _ hx)) hrest b h2

theorem setEdges_noNatOverflow {t : Lir.Term} (ht : LirTermNoOvf t) (es : List Lir.Edge) :
    LirTermNoOvf (t.setEdges es) := by
  cases t with
  | jump e =>
    cases es with
    | nil => simp [Lir.Term.setEdges, LirTermNoOvf]
    | cons _ tl => cases tl <;> simp [Lir.Term.setEdges, LirTermNoOvf]
  | br c w a b t' e' =>
    cases es with
    | nil => simp [Lir.Term.setEdges, LirTermNoOvf]
    | cons _ tl =>
      cases tl with
      | nil => simp [Lir.Term.setEdges, LirTermNoOvf]
      | cons _ tl' => cases tl' <;> simp [Lir.Term.setEdges, LirTermNoOvf]
  | brOvf o x a b ok ovf =>
    cases es with
    | nil => simp [Lir.Term.setEdges, LirTermNoOvf]
    | cons _ tl =>
      cases tl with
      | nil => simp [Lir.Term.setEdges, LirTermNoOvf]
      | cons _ tl' => cases tl' <;> simp [Lir.Term.setEdges, LirTermNoOvf]
  | ret _ => simp [Lir.Term.setEdges, LirTermNoOvf]
  | tail _ _ => simp [Lir.Term.setEdges, LirTermNoOvf]
  | fail r =>
    cases r with
    | natOverflow => exact False.elim ht
    | _ => simp [Lir.Term.setEdges, LirTermNoOvf]
  | trap => simp [Lir.Term.setEdges, LirTermNoOvf]

theorem pruneWith_noNatOverflow {seen : Src.NatSet} {blocks : List Lir.Block}
    (h : ∀ b ∈ blocks, LirBlockNoOvf b) :
    ∀ b ∈ pruneWith seen blocks, LirBlockNoOvf b := by
  unfold pruneWith
  intro b hb
  rw [List.mem_map] at hb
  obtain ⟨⟨b0, l⟩, hmem, rfl⟩ := hb
  rw [List.mem_filter] at hmem
  exact setEdges_noNatOverflow (h b0 (mem_of_mem_zipIdx hmem.1)) _

private theorem splitEmit_noNatOverflow (blocks : List Lir.Block)
    (critical : Lir.Block → Lir.Edge → Bool) (relabel : Label → Label) :
    ∀ (bs : List Lir.Block) (ls : List Label),
      (∀ x ∈ bs, LirBlockNoOvf x) →
      ∀ x ∈ Lir.Func.splitCriticalEdges.emit blocks critical relabel bs ls, LirBlockNoOvf x
  | [], _, _, _, hx => by simp [Lir.Func.splitCriticalEdges.emit] at hx
  | _ :: _, [], _, _, hx => by simp [Lir.Func.splitCriticalEdges.emit] at hx
  | b0 :: rest, l :: ls, hall, x, hx => by
    unfold Lir.Func.splitCriticalEdges.emit at hx
    dsimp only at hx
    rcases List.mem_append.mp hx with hhead | htail
    · cases hhead with
      | head => exact setEdges_noNatOverflow (hall b0 List.mem_cons_self) _
      | tail _ hpend =>
        have hmem : x ∈ List.map
            (fun e =>
              let targetCold := ((blocks[e.target]?).map (·.cold)).getD false
              ({ term := .jump { e with target := relabel e.target }, cold := b0.cold || targetCold } : Lir.Block))
            (Lir.Func.splitEdges (critical b0) relabel (l + 1) b0.term.edges [] []).2 := hpend
        rw [List.mem_map] at hmem
        obtain ⟨_, _, rfl⟩ := hmem
        trivial
    · exact splitEmit_noNatOverflow blocks critical relabel rest ls
        (fun y hy => hall y (List.mem_cons_of_mem _ hy)) x htail

theorem splitCriticalEdges_noNatOverflow {f : Lir.Func} (hf : LirFuncNoOvf f) :
    LirFuncNoOvf f.splitCriticalEdges := by
  unfold Lir.Func.splitCriticalEdges
  dsimp only
  split
  · exact hf
  · intro b hb
    exact splitEmit_noNatOverflow f.blocks.toList _ _ f.blocks.toList _ hf b hb

theorem chunkBlocks_noNatOverflow {f : FunId} {st : St} {pbs : List PBlock}
    (hst : StNoOvf st) (h : chunkBlocks f st = .ok pbs) :
    ∀ pb ∈ pbs, PBlockNoOvf pb := by
  unfold chunkBlocks at h
  dsimp only at h
  by_cases hok : (st.done.toList.all (·.1 < st.next) && (st.done.get? st.cur).isSome) = true
  · simp only [hok, ↓reduceIte, pure, Except.pure] at h
    let stepFn : Nat → Except Error PBlock := fun j =>
      match st.done.get? j with
      | some b => Except.ok b
      | none => throw (Error.internal f s!"chunk label {j} left open")
    have aux : ∀ (js : List Nat) (out : List PBlock),
        js.mapM stepFn = .ok out → ∀ b ∈ out, PBlockNoOvf b := by
      intro js
      induction js with
      | nil =>
        intro out hm b hb
        simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm
        subst hm; cases hb
      | cons j js ih =>
        intro out hm b hb
        rw [List.mapM_cons] at hm
        cases hg : st.done.get? j with
        | none =>
          simp [stepFn, hg, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hm
        | some bj =>
          have hstep : stepFn j = Except.ok bj := by simp [stepFn, hg]
          rw [hstep] at hm
          simp only [bind, Except.bind, pure, Except.pure] at hm
          cases hrest : js.mapM stepFn with
          | error _ => rw [hrest] at hm; cases hm
          | ok rest =>
            rw [hrest] at hm
            simp only [Except.ok.injEq] at hm
            subst hm
            cases hb with
            | head => exact hst j b hg
            | tail _ hb' => exact ih rest hrest b hb'
    exact aux (List.range st.next) pbs h
  · simp [hok, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-! ## Section 3: Monad `M`-Level Zero-`.fail .natOverflow` Preservation -/

/-- Action `m : M α` preserves `StNoOvf` on every `.ok` transition. -/
structure PreservesNoOvf {α : Type} (m : M α) : Prop where
  run : ∀ st a st', StNoOvf st → m.run st = .ok (a, st') → StNoOvf st'

theorem preserves_pure {α : Type} (a : α) : PreservesNoOvf (pure a : M α) := ⟨by
  intro st _ st' hst h
  simp only [pure, StateT.pure, Except.pure, StateT.run, Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2 ▸ hst⟩

theorem preserves_throw {α : Type} (e : Error) : PreservesNoOvf (throw e : M α) := ⟨by
  intro st _ st' _ h
  simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.run, Functor.map, Except.map] at h⟩

theorem preserves_bind {α β : Type} {m : M α} {k : α → M β}
    (hm : PreservesNoOvf m) (hk : ∀ a, PreservesNoOvf (k a)) :
    PreservesNoOvf (m >>= k) := ⟨by
  intro st b st'' hst h
  simp only [bind, StateT.bind, StateT.run] at h
  cases h1 : m st with
  | error e => rw [h1] at h; cases h
  | ok p =>
    rw [h1] at h
    exact (hk p.1).run p.2 b st'' (hm.run st p.1 p.2 hst h1) h⟩

theorem preserves_bind_throw {α β : Type} (e : Error) (k : α → M β) :
    PreservesNoOvf (throw e >>= k) := ⟨by
  intro st _ _ _ h
  simp [bind, StateT.bind, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, StateT.run] at h⟩

theorem preserves_get : PreservesNoOvf (get : M St) := ⟨by
  intro st _ st' hst h
  simp only [get, MonadState.get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure,
    StateT.run, Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2 ▸ hst⟩

theorem preserves_freshReg : PreservesNoOvf freshReg := ⟨by
  intro st _ st' hst h
  simp [freshReg, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run] at h
  obtain ⟨_, rfl⟩ := h
  exact hst⟩

theorem preserves_newLabel : PreservesNoOvf newLabel := ⟨by
  intro st _ st' hst h
  simp [newLabel, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run] at h
  obtain ⟨_, rfl⟩ := h
  exact hst⟩

theorem preserves_openAt (l : Nat) (ps : List VReg) : PreservesNoOvf (openAt l ps) := ⟨by
  intro st _ st' hst h
  simp [openAt, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run] at h
  obtain ⟨_, rfl⟩ := h
  exact hst⟩

theorem preserves_emit (s : Lir.Stmt) : PreservesNoOvf (emit s) := ⟨by
  intro st _ st' hst h
  simp [emit, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run] at h
  obtain ⟨_, rfl⟩ := h
  exact hst⟩

theorem preserves_assign (x : VReg) (r : Lir.Rhs) : PreservesNoOvf (assign x r) :=
  preserves_emit (.assign x r)

theorem preserves_temp (r : Lir.Rhs) : PreservesNoOvf (temp r) :=
  preserves_bind preserves_freshReg fun t =>
  preserves_bind (preserves_assign t r) fun _ => preserves_pure (Lir.Arg.v t)

theorem preserves_bin (o : Lir.BinOp) (a b : Lir.Arg) : PreservesNoOvf (bin o a b) :=
  preserves_temp (.bin o .w64 a b)

theorem preserves_untag (a : Lir.Arg) : PreservesNoOvf (untag a) := by
  cases a with
  | imm w => exact preserves_pure _
  | v y => exact preserves_bin .shr (.v y) (.imm 1)

theorem preserves_put {l : Nat} {b : PBlock} (hb : PBlockNoOvf b) : PreservesNoOvf (put l b) := ⟨by
  intro st _ st' hst h
  simp [put, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run] at h
  obtain ⟨_, rfl⟩ := h
  intro l' b' hg
  by_cases heq : l' = l
  · subst heq
    rw [NatMap.get?_insert_self] at hg
    cases hg
    exact hb
  · rw [NatMap.get?_insert_ne _ _ heq] at hg
    exact hst l' b' hg⟩

theorem preserves_close {t : PTerm} (ht : PTermNoOvf t) : PreservesNoOvf (close t) := ⟨by
  intro st _ st' hst h
  simp [close, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run] at h
  obtain ⟨_, rfl⟩ := h
  intro l' b' hg
  by_cases heq : l' = st.cur
  · subst heq
    rw [NatMap.get?_insert_self] at hg
    cases hg
    exact ht
  · rw [NatMap.get?_insert_ne _ _ heq] at hg
    exact hst l' b' hg⟩

theorem preserves_coldBlock {t : PTerm} (ht : PTermNoOvf t) : PreservesNoOvf (coldBlock t) :=
  preserves_bind preserves_newLabel fun l =>
  preserves_bind (preserves_put ht) fun _ => preserves_pure l

theorem preserves_check {r : Sem.Resource} (hr : r ≠ .natOverflow)
    {mk : PEdge → PEdge → PTerm} (hmk : ∀ ok bad, PTermNoOvf (mk ok bad)) :
    PreservesNoOvf (check r mk) := by
  have htr : PTermNoOvf (.fail r) := by
    cases r with
    | natOverflow => exact absurd rfl hr
    | _ => trivial
  exact preserves_bind (preserves_coldBlock htr) fun bad =>
    preserves_bind preserves_newLabel fun cont =>
    preserves_bind (preserves_close (hmk (loc cont) (loc bad))) fun _ =>
    preserves_openAt cont []

theorem preserves_forM {α : Type} {xs : List α} {f : α → M Unit}
    (hf : ∀ x ∈ xs, PreservesNoOvf (f x)) : PreservesNoOvf (xs.forM f) := by
  induction xs with
  | nil => exact preserves_pure ()
  | cons x xs ih =>
    exact preserves_bind (hf x List.mem_cons_self) fun _ =>
      ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))

theorem preserves_mapM {α β : Type} {xs : List α} {f : α → M β}
    (hf : ∀ x ∈ xs, PreservesNoOvf (f x)) : PreservesNoOvf (xs.mapM f) := by
  induction xs with
  | nil => exact preserves_pure []
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact preserves_bind (hf x List.mem_cons_self) fun y =>
      preserves_bind (ih (fun z hz => hf z (List.mem_cons_of_mem _ hz))) fun ys =>
      preserves_pure (y :: ys)

theorem preserves_optMapM {α β : Type} {ox : Option α} {f : α → M β}
    (hf : ∀ x, ox = some x → PreservesNoOvf (f x)) : PreservesNoOvf (ox.mapM f) := by
  cases ox with
  | none => exact preserves_pure none
  | some x =>
    simp only [Option.mapM_some]
    exact preserves_bind (hf x rfl) fun y => preserves_pure (some y)

theorem preserves_liftExcept {α : Type} (e : Except Error α) : PreservesNoOvf (e : M α) := by
  cases e with
  | error err => exact preserves_throw err
  | ok a => exact preserves_pure a

private theorem preserves_modify_keepDone (g : St → St) (hd : ∀ st, (g st).done = st.done) :
    PreservesNoOvf (modify g : M Unit) := ⟨by
  intro st _ st' hst h
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run] at h
  obtain ⟨_, rfl⟩ := h
  intro l b hg
  rw [hd] at hg
  exact hst l b hg⟩

/-- Automated tactic solving `PreservesNoOvf` goals without blind `split` recursion. -/
macro "solve_no_ovf_step" : tactic =>
  `(tactic| repeat (first
    | exact preserves_pure _
    | exact preserves_throw _
    | exact preserves_bind_throw _ _
    | exact preserves_get
    | exact preserves_freshReg
    | exact preserves_newLabel
    | exact preserves_openAt _ _
    | exact preserves_emit _
    | exact preserves_assign _ _
    | exact preserves_temp _
    | exact preserves_bin _ _ _
    | exact preserves_untag _
    | exact preserves_put (by trivial)
    | exact preserves_close (by trivial)
    | exact preserves_coldBlock (by trivial)
    | exact preserves_check (by decide) (fun _ _ => by trivial)
    | (refine preserves_bind ?_ fun _ => ?_)))

/-- Automated tactic solving `PreservesNoOvf` goals over monadic lowering helpers
(including `do`-notation `if ... then throw ...` join points!). -/
macro "solve_no_ovf" : tactic =>
  `(tactic| repeat (first
    | exact preserves_pure _
    | exact preserves_throw _
    | exact preserves_bind_throw _ _
    | exact preserves_get
    | exact preserves_freshReg
    | exact preserves_newLabel
    | exact preserves_openAt _ _
    | exact preserves_emit _
    | exact preserves_assign _ _
    | exact preserves_temp _
    | exact preserves_bin _ _ _
    | exact preserves_untag _
    | exact preserves_put (by trivial)
    | exact preserves_close (by trivial)
    | exact preserves_coldBlock (by trivial)
    | exact preserves_check (by decide) (fun _ _ => by trivial)
    | (refine preserves_bind ?_ fun _ => ?_)
    | split))

/-! ## Section 4: Zero-`.fail .natOverflow` for Every Phase 4 Builder -/

theorem divModVar_noNatOverflow (x : VReg) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (a b : Lir.Arg) :
    PreservesNoOvf (divModVar x o zero a b) := by
  unfold divModVar
  solve_no_ovf

theorem divMod_noNatOverflow (x : VReg) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (a b : Lir.Arg) :
    PreservesNoOvf (divMod x o zero a b) := by
  unfold divMod
  cases b with
  | imm w => dsimp only; solve_no_ovf
  | v y => exact divModVar_noNatOverflow x o zero a (.v y)

theorem wordCount_noNatOverflow (w : Src.Width) (b : Lir.Arg) : PreservesNoOvf (wordCount w b) := by
  unfold wordCount; solve_no_ovf

theorem wordNarrow_noNatOverflow (f : FunId) (x : VReg) (w : Src.Width) (op : Src.WordOp) (as : List Lir.Arg) :
    PreservesNoOvf (wordNarrow f x w op as) := by
  unfold wordNarrow
  split <;> first
    | exact preserves_throw _
    | exact preserves_assign ..
    | exact preserves_bind (wordCount_noNatOverflow ..) fun _ => by solve_no_ovf
    | solve_no_ovf

theorem word_non64_noNatOverflow (f : FunId) (x : VReg) {w : Src.Width} (hw : w ≠ .w64)
    (op : Src.WordOp) (as : List Lir.Arg) :
    PreservesNoOvf (Lower.word f x w op as) := by
  unfold Lower.word
  split
  · exact divMod_noNatOverflow ..
  · exact divMod_noNatOverflow ..
  · exact preserves_assign ..
  · exact preserves_assign ..
  · solve_no_ovf
  · exact preserves_bind (wordCount_noNatOverflow ..) fun _ => by solve_no_ovf
  · exact preserves_assign ..
  · split <;> exact preserves_assign ..
  · simp only [hw, ↓reduceIte]
    exact wordNarrow_noNatOverflow f x w op as

theorem clz64Code_noNatOverflow (x : VReg) (a : Lir.Arg) (retagRes : Bool) :
    PreservesNoOvf (clz64Code x a retagRes) := by
  unfold clz64Code
  cases retagRes <;> solve_no_ovf

theorem divModRaw64_noNatOverflow (x : VReg) (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (a b : Lir.Arg) :
    PreservesNoOvf (divModRaw64 x o zero a b) := by
  unfold divModRaw64
  solve_no_ovf

theorem wordRaw64_noNatOverflow (f : FunId) (x : VReg) (op : Src.WordOp) (as : List Lir.Arg) :
    PreservesNoOvf (wordRaw64 f x op as) := by
  unfold wordRaw64
  split
  · exact preserves_assign _ _
  · exact preserves_assign _ _
  · exact preserves_assign _ _
  · exact divModRaw64_noNatOverflow _ _ _ _ _
  · exact divModRaw64_noNatOverflow _ _ _ _ _
  · exact preserves_assign _ _
  · exact preserves_assign _ _
  · exact preserves_assign _ _
  · solve_no_ovf_step
  · solve_no_ovf_step
  · exact preserves_assign _ _
  · exact preserves_assign _ _
  · exact preserves_assign _ _
  · exact preserves_assign _ _
  · exact preserves_assign _ _
  · exact preserves_assign _ _
  · exact clz64Code_noNatOverflow _ _ _
  · solve_no_ovf_step
  · solve_no_ovf_step
  · solve_no_ovf_step
  · solve_no_ovf_step
  · solve_no_ovf_step
  · solve_no_ovf_step
  · solve_no_ovf_step
  · solve_no_ovf_step
  · exact preserves_throw _

theorem box64_noNatOverflow (x : VReg) (r : Lir.Arg) : PreservesNoOvf (box64 x r) := by
  unfold box64
  solve_no_ovf

theorem promoteRaw64ToNatVal_noNatOverflow (x : VReg) (r : Lir.Arg) :
    PreservesNoOvf (promoteRaw64ToNatVal x r) := by
  unfold promoteRaw64ToNatVal
  solve_no_ovf

theorem natValLow64_noNatOverflow (x : VReg) (a : Lir.Arg) :
    PreservesNoOvf (natValLow64 x a) := by
  cases a with
  | imm _ => exact preserves_assign ..
  | v _ => unfold natValLow64; dsimp only; solve_no_ovf

theorem unbox64OrBigNat_noNatOverflow (x : VReg) (a : Lir.Arg) :
    PreservesNoOvf (unbox64OrBigNat x a) := by
  cases a with
  | imm _ => exact preserves_assign ..
  | v _ => unfold unbox64OrBigNat; dsimp only; solve_no_ovf

theorem objToNatVal_noNatOverflow (x : VReg) (a : Lir.Arg) :
    PreservesNoOvf (objToNatVal x a) := by
  cases a with
  | imm _ => exact preserves_assign ..
  | v _ =>
    unfold objToNatVal
    dsimp only
    exact preserves_bind preserves_newLabel fun _ =>
      preserves_bind preserves_newLabel fun _ =>
      preserves_bind preserves_newLabel fun _ =>
      preserves_bind preserves_newLabel fun _ =>
      preserves_bind preserves_newLabel fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_put (by trivial)) fun _ =>
      preserves_bind preserves_freshReg fun _ =>
      preserves_bind (preserves_put (by trivial)) fun _ =>
      preserves_bind (preserves_put (by trivial)) fun _ =>
      preserves_bind (preserves_openAt _ _) fun _ =>
      preserves_bind preserves_freshReg fun _ =>
      preserves_bind (preserves_assign _ _) fun _ =>
      preserves_bind preserves_freshReg fun _ =>
      preserves_bind (promoteRaw64ToNatVal_noNatOverflow _ _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_openAt _ _

theorem natValSaturate64_noNatOverflow (x : VReg) (a : Lir.Arg) :
    PreservesNoOvf (natValSaturate64 x a) := by
  cases a with
  | imm _ => exact preserves_assign ..
  | v _ => unfold natValSaturate64; dsimp only; solve_no_ovf

theorem unbox64OrSaturateBigNat_noNatOverflow (x : VReg) (a : Lir.Arg) :
    PreservesNoOvf (unbox64OrSaturateBigNat x a) := by
  cases a with
  | imm _ => exact preserves_assign ..
  | v _ => unfold unbox64OrSaturateBigNat; dsimp only; solve_no_ovf

theorem word64Big_noNatOverflow (f : FunId) (x : VReg) (op : Src.WordOp) (as : List Lir.Arg) :
    PreservesNoOvf (word64Big f x op as) := by
  unfold word64Big
  refine preserves_bind (preserves_mapM fun a _ =>
    preserves_bind preserves_freshReg fun t =>
    preserves_bind (natValLow64_noNatOverflow t a) fun _ => preserves_pure (Lir.Arg.v t)) fun raws =>
    preserves_bind preserves_freshReg fun tmp =>
    preserves_bind (wordRaw64_noNatOverflow f tmp op raws) fun _ =>
    promoteRaw64ToNatVal_noNatOverflow x (.v tmp)

theorem wordBig_noNatOverflow (f : FunId) (x : VReg) (w : Src.Width) (op : Src.WordOp) (as : List Lir.Arg) :
    PreservesNoOvf (wordBig f x w op as) := by
  unfold wordBig
  by_cases hw : w = .w64
  · subst hw
    simp only [beq_self_eq_true, ↓reduceIte]
    split
    · exact preserves_assign ..
    · exact preserves_assign ..
    · exact preserves_bind preserves_freshReg fun u =>
        preserves_bind (natValLow64_noNatOverflow u _) fun _ =>
        preserves_bind (preserves_temp _) fun _ => preserves_assign ..
    · exact word64Big_noNatOverflow f x op as
  · have hbeq : (w == .w64) = false := beq_false_of_ne hw
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    split
    · exact preserves_bind preserves_freshReg fun u =>
        preserves_bind (natValLow64_noNatOverflow u _) fun _ =>
        preserves_bind (preserves_temp _) fun _ => preserves_assign ..
    · exact word_non64_noNatOverflow f x hw op as

theorem binFastSlow_noNatOverflow (slowFn : FunId) (x : VReg) (a b : Lir.Arg)
    (fastBody : List Lir.Stmt) (fastRes : Lir.Arg → Lir.Arg) :
    PreservesNoOvf (binFastSlow slowFn x a b fastBody fastRes) := by
  unfold binFastSlow; solve_no_ovf

theorem natAddBig_noNatOverflow (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) :
    PreservesNoOvf (natAddBig procs x a b) := by
  unfold natAddBig; solve_no_ovf

theorem natSubBig_noNatOverflow (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) :
    PreservesNoOvf (natSubBig procs x a b) := by
  unfold natSubBig
  exact preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    binFastSlow_noNatOverflow ..

theorem natPredBig_noNatOverflow (procs : BigNatProcs) (x : VReg) (a : Lir.Arg) :
    PreservesNoOvf (natPredBig procs x a) := by
  unfold natPredBig; solve_no_ovf

theorem natSuccPeelBig_noNatOverflow (procs : BigNatProcs) (x y : VReg) :
    PreservesNoOvf (natSuccPeelBig procs x y) := by
  unfold natSuccPeelBig; exact natPredBig_noNatOverflow ..

theorem natMulBig_noNatOverflow (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) :
    PreservesNoOvf (natMulBig procs x a b) := by
  unfold natMulBig; solve_no_ovf

theorem natDivModBig_noNatOverflow (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (slowFn : FunId)
    (x : VReg) (a b : Lir.Arg) :
    PreservesNoOvf (natDivModBig o zero slowFn x a b) := by
  unfold natDivModBig; solve_no_ovf

theorem natCmpBig_noNatOverflow (c : Lir.Cond) (slowFn : FunId) (tWord fWord : Word)
    (x : VReg) (a b : Lir.Arg) :
    PreservesNoOvf (natCmpBig c slowFn tWord fWord x a b) := by
  unfold natCmpBig
  exact preserves_bind preserves_freshReg fun _ => binFastSlow_noNatOverflow ..

theorem natShrBig_noNatOverflow (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) :
    PreservesNoOvf (natShrBig procs x a b) := by
  unfold natShrBig
  exact preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    binFastSlow_noNatOverflow ..

theorem natShlBig_noNatOverflow (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) :
    PreservesNoOvf (natShlBig procs x a b) := by
  unfold natShlBig; solve_no_ovf

theorem primitiveBig_noNatOverflow (f : FunId) (T : BigNatTables) (x : VReg)
    (op : Lam.Prim) (as : List Lir.Arg) :
    PreservesNoOvf (primitiveBig f T x op as) := by
  unfold primitiveBig
  split
  · exact natAddBig_noNatOverflow _ _ _ _
  · exact natSubBig_noNatOverflow _ _ _ _
  · exact natPredBig_noNatOverflow _ _ _
  · exact natMulBig_noNatOverflow _ _ _ _
  · unfold natDivBig; exact natDivModBig_noNatOverflow _ _ _ _ _ _
  · unfold natModBig; exact natDivModBig_noNatOverflow _ _ _ _ _ _
  · unfold natPowBig; exact preserves_emit _
  · unfold natGcdBig; exact preserves_emit _
  · cases T.bools with
    | none => exact preserves_throw _
    | some _ => unfold natBeqBig; exact natCmpBig_noNatOverflow _ _ _ _ _ _ _
  · cases T.bools with
    | none => exact preserves_throw _
    | some _ => unfold natBleBig; exact natCmpBig_noNatOverflow _ _ _ _ _ _ _
  · cases T.bools with
    | none => exact preserves_throw _
    | some _ => unfold natBltBig; exact natCmpBig_noNatOverflow _ _ _ _ _ _ _
  · unfold natLandBig; exact binFastSlow_noNatOverflow _ _ _ _ _ _
  · unfold natLorBig; exact preserves_bind preserves_freshReg fun _ => binFastSlow_noNatOverflow _ _ _ _ _ _
  · unfold natXorBig; exact preserves_bind preserves_freshReg fun _ =>
      preserves_bind preserves_freshReg fun _ => binFastSlow_noNatOverflow _ _ _ _ _ _
  · exact natShlBig_noNatOverflow _ _ _ _
  · exact natShrBig_noNatOverflow _ _ _ _
  · exact preserves_throw _

theorem primitiveBigAll_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (x : VReg) (op : Lam.Prim) (as : List Lir.Arg) :
    PreservesNoOvf (primitiveBigAll f T procs x op as) := by
  unfold primitiveBigAll
  cases op with
  | word w wo => exact wordBig_noNatOverflow f x w wo as
  | _ => exact primitiveBig_noNatOverflow f { bools := T.bools, procs } x _ as

theorem lowerAlloc_noNatOverflow (f : FunId) (T : Tables) (x : VReg)
    (c : Fir.CtorInfo) (as : List Lir.Arg) :
    PreservesNoOvf (Lower.alloc f T x c as) := by
  unfold Lower.alloc
  -- Peel each guard (`if ... then throw ...`) cleanly via `by_cases`
  by_cases h1 : isNatKey T c.key = true
  · simp [h1]; exact preserves_bind_throw ..
  simp only [h1]
  by_cases h2 : (c.nscalar != 0) = true
  · simp [h2]; exact preserves_bind_throw ..
  simp only [h2]
  by_cases h3 : (as.length != c.arity) = true
  · simp [h3]; exact preserves_bind_throw ..
  simp only [h3]
  by_cases h4 : (Fir.CtorInfo.ofKey T.ctors c.key != some c) = true
  · simp [h4]; exact preserves_bind_throw ..
  simp only [h4]
  by_cases h5 : (as.any (· == .v x)) = true
  · simp [h5]; exact preserves_bind_throw ..
  simp only [h5]
  by_cases h6 : c.tag > maxTag
  · simp [h6]; exact preserves_bind_throw ..
  simp only [h6, ↓reduceIte]
  by_cases h7 : c.fieldless = true
  · simp [h7]; exact preserves_assign ..
  simp only [h7]
  by_cases h8 : c.arity > maxFields
  · simp [h8]; exact preserves_bind_throw ..
  simp only [h8, ↓reduceIte]
  exact preserves_bind (preserves_assign _ _) fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind (preserves_assign _ _) fun _ =>
    preserves_bind (preserves_temp _) fun _ =>
    preserves_bind (preserves_check (by decide) fun _ _ => by trivial) fun _ =>
    preserves_bind (preserves_emit _) fun _ =>
    preserves_bind (preserves_emit _) fun _ =>
    preserves_bind (preserves_emit _) fun _ =>
    preserves_forM fun _ _ => preserves_emit _

theorem operandBig_noNatOverflow (f : FunId) (sc : StrCtx) (bc : BigNatLitCtx) (a : Fir.Arg) :
    PreservesNoOvf (operandBig f sc bc a) := by
  unfold operandBig
  cases a with
  | var _ => exact preserves_pure _
  | erased => exact preserves_pure _
  | lit l =>
    cases l with
    | nat n =>
      dsimp only
      split
      · exact preserves_pure _
      · cases bc.rodataAddrs.lookup n with
        | some _ => exact preserves_pure _
        | none =>
          cases bc.litFns.lookup n with
          | some _ => solve_no_ovf
          | none => exact preserves_throw _
    | str s =>
      dsimp only
      cases sc.rodataAddrs.lookup s with
      | some _ => exact preserves_pure _
      | none =>
        cases sc.strFns.lookup s with
        | some _ => solve_no_ovf
        | none => exact preserves_throw _

theorem operandsBig_noNatOverflow (f : FunId) (sc : StrCtx) (bc : BigNatLitCtx) :
    ∀ as, PreservesNoOvf (operandsBig f sc bc as)
  | [] => preserves_pure []
  | a :: as =>
    preserves_bind (operandBig_noNatOverflow f sc bc a) fun la =>
    preserves_bind (operandsBig_noNatOverflow f sc bc as) fun las =>
    preserves_pure (la :: las)

theorem projBig_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (x y : VReg) (c : Key.CtorKey) (i : Nat) :
    PreservesNoOvf (projBig f T procs x y c i) := by
  unfold projBig
  split
  · split
    · exact natSuccPeelBig_noNatOverflow procs x y
    · exact preserves_throw _
  · split
    · exact preserves_throw _
    · cases Fir.CtorInfo.ofKey T.ctors c with
      | none => exact preserves_throw _
      | some info =>
        dsimp only
        split
        · exact preserves_assign _ _
        · exact preserves_throw _

theorem instrBig_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (sc : StrCtx) (bc : BigNatLitCtx) (ins : Cfg.Instr) :
    PreservesNoOvf (instrBig f T procs sc bc ins) := by
  cases ins with
  | bind x rhs =>
    cases rhs with
    | fir fr =>
      cases fr with
      | arg a => exact preserves_bind (operandBig_noNatOverflow ..) fun _ => preserves_assign ..
      | prim op as => exact preserves_bind (operandsBig_noNatOverflow ..) fun las =>
          primitiveBigAll_noNatOverflow f T procs x op las
      | call g as => exact preserves_bind (operandsBig_noNatOverflow ..) fun _ => preserves_emit ..
      | ctor _ _ => exact preserves_throw _
      | proj _ _ _ => exact preserves_throw _
    | alloc c as _ => exact preserves_bind (operandsBig_noNatOverflow ..) fun las =>
        lowerAlloc_noNatOverflow f T x c las
    | proj y c i => exact projBig_noNatOverflow f T procs x y c i

theorem instrsBig_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (sc : StrCtx) (bc : BigNatLitCtx) : ∀ is, PreservesNoOvf (instrsBig f T procs sc bc is)
  | [] => preserves_pure ()
  | _ :: _ => preserves_bind (instrBig_noNatOverflow ..) fun _ => instrsBig_noNatOverflow ..

theorem chain_noNatOverflow (x : Lir.Arg) : ∀ tests els, PreservesNoOvf (chain x tests els)
  | [], els => preserves_close (by trivial)
  | [(_, _)], _ => preserves_close (by trivial)
  | (_, _) :: b :: rest, els =>
    preserves_bind preserves_newLabel fun l =>
    preserves_bind (preserves_close (by trivial)) fun _ =>
    preserves_bind (preserves_openAt l []) fun _ =>
    chain_noNatOverflow x (b :: rest) els

theorem chainOr_noNatOverflow (x : Lir.Arg) (tests : List (Lir.Arg × PEdge)) (od : Option PEdge) :
    PreservesNoOvf (chainOr x tests od) := by
  unfold chainOr
  cases od with
  | some d => exact chain_noNatOverflow x tests d
  | none =>
    cases unsnoc tests with
    | none => exact preserves_close (by trivial)
    | some p => exact chain_noNatOverflow x p.1 p.2.2

theorem natSwitch_noNatOverflow (x : VReg) (es : List (KeyKind × PEdge)) (dd : Option PEdge) :
    PreservesNoOvf (natSwitch x es dd) := by
  unfold natSwitch
  split <;> exact preserves_close (by trivial)

theorem tagSwitch_noNatOverflow (x : VReg) (es : List (KeyKind × PEdge)) (dd : Option PEdge) :
    PreservesNoOvf (tagSwitch x es dd) := by
  unfold tagSwitch
  split
  · exact chainOr_noNatOverflow ..
  · exact preserves_bind (preserves_temp _) fun _ => chainOr_noNatOverflow ..
  · exact preserves_bind preserves_newLabel fun p =>
      preserves_bind preserves_newLabel fun i =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_openAt p []) fun _ =>
      preserves_bind (preserves_temp _) fun t =>
      preserves_bind (chainOr_noNatOverflow t _ _) fun _ =>
      preserves_bind (preserves_openAt i []) fun _ =>
      chainOr_noNatOverflow ..

theorem fusedClose_noNatOverflow (c : Lir.Cond) (a b : Lir.Arg) (te fe : Option PEdge) :
    PreservesNoOvf (fusedClose c a b te fe) := by
  unfold fusedClose
  split <;> exact preserves_close (by trivial)

theorem edgeBig_noNatOverflow (f : FunId) (sc : StrCtx) (bc : BigNatLitCtx) (src : Nat) (e : Cfg.Edge) :
    PreservesNoOvf (edgeBig f sc bc src e) := by
  unfold edgeBig
  by_cases hord : (e.back == decide (e.target ≤ src)) = true
  · simp only [hord, ↓reduceIte]
    refine preserves_bind (preserves_liftExcept _) fun opt => ?_
    cases opt with
    | some _ => exact preserves_pure _
    | none =>
      exact preserves_bind preserves_get fun _ =>
        preserves_bind preserves_newLabel fun _ =>
        preserves_bind (preserves_modify_keepDone _ fun _ => rfl) fun _ =>
        preserves_bind (operandsBig_noNatOverflow ..) fun _ =>
        preserves_bind (preserves_close (by trivial)) fun _ =>
        preserves_bind (preserves_modify_keepDone _ fun _ => rfl) fun _ =>
        preserves_pure _
  · simp only [hord]
    exact preserves_bind_throw ..

theorem switchBig_noNatOverflow (f : FunId) (T : Tables) (sc : StrCtx) (bc : BigNatLitCtx)
    (src : Nat) (x : VReg) (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge) :
    PreservesNoOvf (switchBig f T sc bc src x alts d) := by
  unfold switchBig
  refine preserves_bind (preserves_mapM fun ke _ => by
      unfold switchAltBig
      cases keyKind T ke.1 with
      | none => exact preserves_throw _
      | some kind => exact preserves_bind (edgeBig_noNatOverflow ..) fun _ => preserves_pure _) fun es =>
    preserves_bind (preserves_optMapM fun e _ => edgeBig_noNatOverflow ..) fun dd => ?_
  dsimp only
  split
  · by_cases hlen : ((es.filter (·.1.isNat)).length == es.length) = true
    · simp only [hlen, ↓reduceIte]; exact natSwitch_noNatOverflow ..
    · simp only [hlen]; exact preserves_bind_throw ..
  · exact tagSwitch_noNatOverflow ..

theorem termBig_noNatOverflow (f : FunId) (T : Tables) (sc : StrCtx) (bc : BigNatLitCtx)
    (src : Nat) (t : Cfg.Term) : PreservesNoOvf (termBig f T sc bc src t) := by
  cases t with
  | jump e => exact preserves_bind (edgeBig_noNatOverflow ..) fun _ => preserves_close (by trivial)
  | switch x alts d => exact switchBig_noNatOverflow ..
  | ret a => exact preserves_bind (operandBig_noNatOverflow ..) fun _ => preserves_close (by trivial)
  | tcall g as => exact preserves_bind (operandsBig_noNatOverflow ..) fun _ => preserves_close (by trivial)
  | trap => exact preserves_close (by trivial)

theorem blockBig_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (sc : StrCtx) (bc : BigNatLitCtx) (src : Nat) (entry : Bool) (b : Cfg.Block) :
    PreservesNoOvf (blockBig f T procs sc bc src entry b) :=
  preserves_bind (preserves_openAt _ _) fun _ =>
  preserves_bind (instrsBig_noNatOverflow ..) fun _ =>
  termBig_noNatOverflow ..

private theorem chunksBig_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (sc : StrCtx) (bc : BigNatLitCtx) (merged : Bool) :
    ∀ bs fresh cs fresh',
      chunksBig f T procs sc bc merged bs fresh = .ok (cs, fresh') →
      ∀ c ∈ cs, ∀ pb ∈ c, PBlockNoOvf pb
  | [], _, cs, _, h => by
    simp only [chunksBig, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; intro _ hm; cases hm
  | (b, i) :: bs, fresh, cs, fresh', h => by
    unfold chunksBig at h
    cases hrun : (blockBig f T procs sc bc i (merged && i == 0) b).run { fresh } with
    | error _ => simp [hrun, bind, Except.bind] at h
    | ok p =>
      simp only [hrun, bind, Except.bind] at h
      cases hchk : chunkBlocks f p.2 with
      | error _ => simp [hchk] at h
      | ok blks =>
        simp only [hchk] at h
        cases hrest : chunksBig f T procs sc bc merged bs p.2.fresh with
        | error _ => simp [hrest] at h
        | ok pr =>
          simp only [hrest, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have hst0 : StNoOvf { fresh := fresh } := fun l _ hg => by simp [NatMap.get?] at hg
          have hst' := (blockBig_noNatOverflow f T procs sc bc i (merged && i == 0) b).run
            { fresh } p.1 p.2 hst0 hrun
          intro c hc
          cases hc with
          | head => exact chunkBlocks_noNatOverflow hst' hchk
          | tail _ hc' => exact chunksBig_noNatOverflow f T procs sc bc merged bs p.2.fresh pr.1 pr.2 hrest c hc'

/-- **Every user function lowered by `functionBig` has ZERO `.fail .natOverflow` blocks.** -/
theorem functionBig_noNatOverflow {T : Tables} {procs : BigNatProcs}
    {sc : StrCtx} {bc : BigNatLitCtx} {f : FunId} {fd : Cfg.Fun} {conv : Lir.Conv}
    {lf : Lir.Func} (h : functionBig T procs sc bc f fd conv = .ok lf) :
    LirFuncNoOvf lf := by
  unfold functionBig at h
  cases hraw : functionRawBig T procs sc bc f fd with
  | error _ => simp [hraw, bind, Except.bind] at h
  | ok p =>
    simp only [hraw, bind, Except.bind] at h
    by_cases hrc : reachClosed p.2 (reachable p.2) = true
    · simp only [hrc, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      apply splitCriticalEdges_noNatOverflow
      intro b hb
      apply pruneWith_noNatOverflow _ b hb
      unfold functionRawBig at hraw
      cases hb0 : fd.blocks.head? with
      | none => simp [hb0, throw, throwThe, MonadExceptOf.throw] at hraw
      | some b0 =>
        simp only [hb0] at hraw
        cases hmis : misordered fd with
        | some _ => simp [hmis, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hraw
        | none =>
          simp only [hmis] at hraw
          obtain ⟨pcs, hcs, hraw⟩ := except_bind_ok hraw
          obtain ⟨body, hres, hraw⟩ := except_bind_ok hraw
          simp only [pure, Except.pure, Except.ok.injEq] at hraw
          obtain ⟨_, rfl⟩ := hraw
          have hbody : ∀ lb ∈ body, LirBlockNoOvf lb :=
            resolveChunks_noNatOverflow (fun c hc =>
              chunksBig_noNatOverflow _ _ _ _ _ _ _ _ _ _ hcs c.1 (mem_of_mem_zipIdx hc)) hres
          intro lb hlb
          rcases List.mem_append.mp hlb with hentry | hbdy
          · split at hentry
            · cases hentry
            · cases hentry with
              | head => trivial
              | tail _ hm => cases hm
          · exact hbody lb hbdy
    · simp [hrc, throw, throwThe, MonadExceptOf.throw] at h

theorem functionsBig_noNatOverflow {T : Tables} {procs : BigNatProcs}
    {sc : StrCtx} {bc : BigNatLitCtx} {P : Cfg.Program} {roots : List (FunId × String)} :
    ∀ {fs : List Nat} {lfs : List Lir.Func},
      functionsBig T procs sc bc P roots fs = .ok lfs →
      ∀ lf ∈ lfs, LirFuncNoOvf lf
  | [], lfs, h => by
    simp only [functionsBig, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro _ hm; cases hm
  | f :: fs, lfs, h => by
    unfold functionsBig at h
    cases hfd : P.fun? f with
    | none => simp [hfd, throw, throwThe, MonadExceptOf.throw] at h
    | some fd =>
      simp only [hfd] at h
      obtain ⟨lf, h1, h⟩ := except_bind_ok h
      obtain ⟨rest, hrest, h⟩ := except_bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro x hx
      cases hx with
      | head => exact functionBig_noNatOverflow h1
      | tail _ hx' => exact functionsBig_noNatOverflow hrest x hx'

/-! ### `lowerRepBig` Zero-`.fail .natOverflow` Proofs -/

theorem finishRaw64Big_noNatOverflow (x : VReg) (rx : Fir.Rep) (r : Lir.Arg) :
    PreservesNoOvf (finishRaw64Big x rx r) := by
  cases rx with
  | word => exact preserves_assign ..
  | obj => exact box64_noNatOverflow x r
  | tobj => exact promoteRaw64ToNatVal_noNatOverflow x r
  | erased => exact preserves_assign ..

theorem operandRaw64Big_noNatOverflow (f : FunId) (fc : Fir.Rep.FunCert) (a : Fir.Arg) :
    PreservesNoOvf (operandRaw64Big f fc a) := by
  unfold operandRaw64Big
  cases a with
  | var y =>
    dsimp only
    cases fc.varRep y with
    | word => exact preserves_pure _
    | tobj => exact preserves_bind preserves_freshReg fun r =>
        preserves_bind (natValLow64_noNatOverflow r (.v y)) fun _ => preserves_pure _
    | obj => exact preserves_bind preserves_freshReg fun r =>
        preserves_bind (unbox64OrBigNat_noNatOverflow r (.v y)) fun _ => preserves_pure _
    | erased => exact preserves_pure _
  | lit l =>
    cases l with
    | nat _ => exact preserves_pure _
    | str _ => exact preserves_throw _
  | erased => exact preserves_pure _

theorem operandsRaw64Big_noNatOverflow (f : FunId) (fc : Fir.Rep.FunCert) :
    ∀ as, PreservesNoOvf (operandsRaw64Big f fc as)
  | [] => preserves_pure []
  | a :: as =>
    preserves_bind (operandRaw64Big_noNatOverflow f fc a) fun _ =>
    preserves_bind (operandsRaw64Big_noNatOverflow f fc as) fun _ => preserves_pure _

theorem operandAtRepBig_noNatOverflow (f : FunId) (fc : Fir.Rep.FunCert)
    (a : Fir.Arg) (expected : Fir.Rep) (sc : StrCtx) (bc : BigNatLitCtx) :
    PreservesNoOvf (operandAtRepBig f fc a expected sc bc) := by
  unfold operandAtRepBig
  cases expected with
  | word => exact operandRaw64Big_noNatOverflow f fc a
  | tobj =>
    cases a with
    | var y =>
      dsimp only
      split
      · exact preserves_bind preserves_freshReg fun r =>
          preserves_bind (promoteRaw64ToNatVal_noNatOverflow r (.v y)) fun _ => preserves_pure _
      · exact preserves_pure _
    | lit _ => exact operandBig_noNatOverflow ..
    | erased => exact operandBig_noNatOverflow ..
  | obj =>
    cases a with
    | var y =>
      dsimp only
      split
      · exact preserves_bind preserves_freshReg fun b =>
          preserves_bind (box64_noNatOverflow b (.v y)) fun _ => preserves_pure _
      · exact preserves_pure _
    | lit l =>
      cases l with
      | nat n =>
        dsimp only
        split
        · exact preserves_pure _
        · exact operandBig_noNatOverflow ..
      | str s => exact operandBig_noNatOverflow ..
    | erased => exact operandBig_noNatOverflow ..
  | erased => exact preserves_pure _

theorem operandsAtRepsBig_noNatOverflow (f : FunId) (fc : Fir.Rep.FunCert) :
    ∀ as rs sc bc, PreservesNoOvf (operandsAtRepsBig f fc as rs sc bc)
  | [], _, _, _ => preserves_pure []
  | a :: as, rs, sc, bc =>
    preserves_bind (operandAtRepBig_noNatOverflow f fc a (rs.headD .tobj) sc bc) fun _ =>
    preserves_bind (operandsAtRepsBig_noNatOverflow f fc as rs.tail sc bc) fun _ =>
    preserves_pure _

theorem emitIncCallArgs_noNatOverflow (rc : RcCtx) (fc : Fir.Rep.FunCert)
    (liveAfter : Src.NatSet) (as : List Fir.Arg) (mutFlags : List Bool) :
    PreservesNoOvf (emitIncCallArgs rc fc liveAfter as mutFlags) := by
  unfold emitIncCallArgs
  exact preserves_forM fun _ _ => preserves_emit _

theorem operandNatValBig_noNatOverflow (f : FunId) (fc : Fir.Rep.FunCert)
    (sc : StrCtx) (bc : BigNatLitCtx) (a : Fir.Arg) :
    PreservesNoOvf (operandNatValBig f fc sc bc a) := by
  unfold operandNatValBig
  cases a with
  | var y =>
    dsimp only
    cases fc.varRep y with
    | word => exact preserves_bind preserves_freshReg fun r =>
        preserves_bind (promoteRaw64ToNatVal_noNatOverflow r (.v y)) fun _ => preserves_pure _
    | obj => exact preserves_bind preserves_freshReg fun r =>
        preserves_bind (objToNatVal_noNatOverflow r (.v y)) fun _ => preserves_pure _
    | tobj => exact preserves_pure _
    | erased => exact preserves_pure _
  | lit _ => exact operandBig_noNatOverflow ..
  | erased => exact operandBig_noNatOverflow ..

theorem operandsNatValBig_noNatOverflow (f : FunId) (fc : Fir.Rep.FunCert)
    (sc : StrCtx) (bc : BigNatLitCtx) :
    ∀ as, PreservesNoOvf (operandsNatValBig f fc sc bc as)
  | [] => preserves_pure []
  | a :: as =>
    preserves_bind (operandNatValBig_noNatOverflow f fc sc bc a) fun _ =>
    preserves_bind (operandsNatValBig_noNatOverflow f fc sc bc as) fun _ =>
    preserves_pure _

theorem operandNarrowRepBig_noNatOverflow (f : FunId) (fc : Fir.Rep.FunCert)
    (sc : StrCtx) (bc : BigNatLitCtx) (a : Fir.Arg) :
    PreservesNoOvf (operandNarrowRepBig f fc sc bc a) := by
  unfold operandNarrowRepBig
  cases a with
  | var y =>
    dsimp only
    cases fc.varRep y with
    | word => exact preserves_temp _
    | obj => exact preserves_bind preserves_freshReg fun u =>
        preserves_bind (unbox64OrBigNat_noNatOverflow u (.v y)) fun _ => preserves_temp _
    | tobj => exact preserves_pure _
    | erased => exact preserves_pure _
  | lit _ => exact operandBig_noNatOverflow ..
  | erased => exact operandBig_noNatOverflow ..

theorem operandsNarrowRepBig_noNatOverflow (f : FunId) (fc : Fir.Rep.FunCert)
    (sc : StrCtx) (bc : BigNatLitCtx) :
    ∀ as, PreservesNoOvf (operandsNarrowRepBig f fc sc bc as)
  | [] => preserves_pure []
  | a :: as =>
    preserves_bind (operandNarrowRepBig_noNatOverflow f fc sc bc a) fun _ =>
    preserves_bind (operandsNarrowRepBig_noNatOverflow f fc sc bc as) fun _ =>
    preserves_pure _

theorem emitLimbPairBig_noNatOverflow (f : FunId) (fc : Fir.Rep.FunCert)
    (kind : LimbPairKind) (r1 r2 : VReg) (as : List Fir.Arg) :
    PreservesNoOvf (emitLimbPairBig f fc kind r1 r2 as) := by
  unfold emitLimbPairBig
  refine preserves_bind (operandsRaw64Big_noNatOverflow f fc as) fun las =>
    preserves_bind preserves_freshReg fun t1 =>
    preserves_bind preserves_freshReg fun t2 => ?_
  split
  · exact preserves_bind (preserves_emit _) fun _ =>
      preserves_bind (finishRaw64Big_noNatOverflow ..) fun _ => finishRaw64Big_noNatOverflow ..
  · exact preserves_bind (preserves_emit _) fun _ =>
      preserves_bind (finishRaw64Big_noNatOverflow ..) fun _ => finishRaw64Big_noNatOverflow ..
  · exact preserves_bind (preserves_emit _) fun _ =>
      preserves_bind (finishRaw64Big_noNatOverflow ..) fun _ => finishRaw64Big_noNatOverflow ..
  · exact preserves_bind (preserves_emit _) fun _ =>
      preserves_bind (finishRaw64Big_noNatOverflow ..) fun _ => finishRaw64Big_noNatOverflow ..
  · exact preserves_throw _

theorem primitiveRepBig_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (fc : Fir.Rep.FunCert) (sc : StrCtx) (bc : BigNatLitCtx) (x : VReg)
    (op : Lam.Prim) (as : List Fir.Arg) :
    PreservesNoOvf (primitiveRepBig f T procs fc sc bc x op as) := by
  unfold primitiveRepBig
  dsimp only
  split
  · split
    · split
      · exact preserves_bind (operandRaw64Big_noNatOverflow ..) fun _ => finishRaw64Big_noNatOverflow ..
      · exact preserves_throw _
    · split
      · split
        · exact preserves_bind (operandRaw64Big_noNatOverflow ..) fun _ => finishRaw64Big_noNatOverflow ..
        · exact preserves_throw _
      · split
        · refine preserves_bind (operandRaw64Big_noNatOverflow ..) fun _ =>
            preserves_bind (preserves_bin _ _ _) fun _ => ?_
          cases fc.varRep x <;> exact preserves_assign ..
        · exact preserves_throw _
    · refine preserves_bind (operandsRaw64Big_noNatOverflow ..) fun las => ?_
      split
      · exact wordRaw64_noNatOverflow ..
      · exact preserves_bind preserves_freshReg fun tmp =>
          preserves_bind (wordRaw64_noNatOverflow ..) fun _ => finishRaw64Big_noNatOverflow ..
  · refine preserves_bind (operandsRaw64Big_noNatOverflow ..) fun las => ?_
    cases las with
    | cons a rest =>
      cases rest with
      | nil => exact finishRaw64Big_noNatOverflow ..
      | cons _ _ => exact preserves_throw _
    | nil => exact preserves_throw _
  · refine preserves_bind (operandsNarrowRepBig_noNatOverflow ..) fun las => ?_
    split
    · exact preserves_bind preserves_freshReg fun tmp =>
        preserves_bind (wordBig_noNatOverflow ..) fun _ => natValLow64_noNatOverflow ..
    · exact wordBig_noNatOverflow ..
  · split
    · split
      · refine preserves_bind (operandsRaw64Big_noNatOverflow ..) fun las => ?_
        cases las with
        | cons la rest =>
          cases rest with
          | cons lb rest2 =>
            cases rest2 with
            | nil =>
              cases T.bools with
              | none => exact preserves_throw _
              | some _ => exact preserves_assign ..
            | cons _ _ => exact preserves_throw _
          | nil => exact preserves_throw _
        | nil => exact preserves_throw _
      · exact preserves_bind (operandsNatValBig_noNatOverflow ..) fun las =>
          primitiveBig_noNatOverflow ..
    · exact preserves_bind (operandsNatValBig_noNatOverflow ..) fun las =>
        primitiveBig_noNatOverflow ..

theorem allocRepBig_noNatOverflow (f : FunId) (T : Tables) (cert : Fir.Rep.Cert)
    (fc : Fir.Rep.FunCert) (x : VReg) (c : Fir.CtorInfo) (as : List Fir.Arg)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) (liveAfter : Src.NatSet) :
    PreservesNoOvf (allocRepBig f T cert fc x c as sc bc rc liveAfter) := by
  unfold allocRepBig
  by_cases ha : (rc.enabled && cert.arrayMkKey == some c.key) = true
  · simp only [ha, ↓reduceIte]
    cases as with
    | cons xs rest =>
      cases rest with
      | nil =>
        refine preserves_bind (operandsAtRepsBig_noNatOverflow ..) fun las => ?_
        cases las with
        | cons _ r =>
          cases r with
          | nil => exact preserves_emit _
          | cons _ _ => exact preserves_pure ()
        | nil => exact preserves_pure ()
      | cons _ _ => exact preserves_throw _
    | nil => exact preserves_throw _
  simp only [ha]
  by_cases hba : (rc.enabled && cert.byteArrayMkKey == some c.key) = true
  · simp only [hba, ↓reduceIte]
    cases as with
    | cons arr rest =>
      cases rest with
      | nil =>
        refine preserves_bind (operandsAtRepsBig_noNatOverflow ..) fun las => ?_
        cases las with
        | cons _ r =>
          cases r with
          | nil => exact preserves_emit _
          | cons _ _ => exact preserves_pure ()
        | nil => exact preserves_pure ()
      | cons _ _ => exact preserves_throw _
    | nil => exact preserves_throw _
  simp only [hba]
  by_cases hnat : isNatKey T c.key = true
  · simp [hnat]; exact preserves_bind_throw ..
  simp only [hnat]
  cases Fir.CtorInfo.ofKey T.ctors c.key with
  | none => exact preserves_throw _
  | some baseInfo =>
    have finish : ∀ (nobj nscalar : Nat) (fieldReps : List Fir.Rep),
        PreservesNoOvf (do
          let totalArity := nobj + nscalar
          if as.length != totalArity || totalArity != baseInfo.arity then
            throw (.form f s!"an allocation of {as.length} fields for {totalArity}")
          if baseInfo.tag > maxTag then throw (.layout f s!"constructor tag {baseInfo.tag} above {maxTag}")
          if totalArity == 0 then
            assign x (.arg (.imm (ctor0Word baseInfo.tag)))
          else
            if totalArity > maxFields then throw (.layout f s!"{totalArity} fields, above {maxFields}")
            emitIncCallArgs rc fc liveAfter as (List.replicate nobj true ++ List.replicate nscalar false)
            let las ← operandsAtRepsBig f fc as fieldReps sc bc
            if las.any (· == .v x) then throw (.form f "an allocation reads the variable it defines")
            assign x (.load .w64 .zero (ctxAt bumpOff))
            let e ← freshReg
            assign e (.addr (mem x (cellBytes totalArity)))
            let l ← temp (.load .w64 .zero (ctxAt limitOff))
            check .heap fun ok bad => .br .ugt (.v e) l bad ok
            emit (.store .w64 (ctxAt bumpOff) (.v e))
            emit (.store .w32 (mem x 0) (.imm (UInt64.ofNat (headerLow nobj 0 baseInfo.tag))))
            emit (.store .w32 (mem x 4) (.imm (UInt64.ofNat immortalRc)))
            las.zipIdx.forM fun (a, i) => emit (.store .w64 (mem x (fieldOffset i)) a)) := by
      intro nobj nscalar fieldReps
      dsimp only
      by_cases har : (as.length != nobj + nscalar || nobj + nscalar != baseInfo.arity) = true
      · simp only [har, ↓reduceIte]; exact preserves_bind_throw ..
      simp only [har]
      by_cases htag : baseInfo.tag > maxTag
      · simp only [htag, ↓reduceIte]; exact preserves_bind_throw ..
      simp only [htag, ↓reduceIte]
      by_cases h0 : (nobj + nscalar == 0) = true
      · simp only [h0, ↓reduceIte]; exact preserves_assign ..
      simp only [h0]
      by_cases hmf : nobj + nscalar > maxFields
      · simp only [hmf, ↓reduceIte]; exact preserves_bind_throw ..
      simp only [hmf, ↓reduceIte]
      refine preserves_bind (emitIncCallArgs_noNatOverflow ..) fun _ =>
        preserves_bind (operandsAtRepsBig_noNatOverflow ..) fun las => ?_
      by_cases hself : (las.any (· == .v x)) = true
      · simp only [hself, ↓reduceIte]; exact preserves_bind_throw ..
      simp only [hself]
      exact preserves_bind (preserves_assign _ _) fun _ =>
        preserves_bind preserves_freshReg fun _ =>
        preserves_bind (preserves_assign _ _) fun _ =>
        preserves_bind (preserves_temp _) fun _ =>
        preserves_bind (preserves_check (by decide) fun _ _ => by trivial) fun _ =>
        preserves_bind (preserves_emit _) fun _ =>
        preserves_bind (preserves_emit _) fun _ =>
        preserves_bind (preserves_emit _) fun _ =>
        preserves_forM fun _ _ => preserves_emit _
    cases cert.ctorRep? c.key with
    | some cr => exact finish cr.nobj cr.nscalar (List.replicate cr.nobj cr.objRep ++ List.replicate cr.nscalar Fir.Rep.word)
    | none => exact finish c.nobj c.nscalar (List.replicate c.nobj Fir.Rep.tobj ++ List.replicate c.nscalar Fir.Rep.word)

theorem projRepBig_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert) (x y : VReg) (c : Key.CtorKey) (i : Nat)
    (rc : RcCtx) (liveAfter liveTerm : Src.NatSet) (rest : List Cfg.Instr) :
    PreservesNoOvf (projRepBig f T procs cert fc x y c i rc liveAfter liveTerm rest) := by
  unfold projRepBig
  split
  · exact preserves_emit _
  · split
    · exact preserves_emit _
    · split
      · split
        · exact natSuccPeelBig_noNatOverflow procs x y
        · exact preserves_throw _
      · split
        · exact preserves_throw _
        · cases Fir.CtorInfo.ofKey T.ctors c with
          | none => exact preserves_throw _
          | some info =>
            dsimp only
            split
            · split
              · exact preserves_bind preserves_freshReg fun tmp =>
                  preserves_bind (preserves_assign _ _) fun _ => box64_noNatOverflow ..
              · split
                · exact preserves_bind preserves_freshReg fun tmp =>
                    preserves_bind (preserves_assign _ _) fun _ => promoteRaw64ToNatVal_noNatOverflow ..
                · split
                  · exact preserves_bind preserves_freshReg fun tmp =>
                      preserves_bind (preserves_assign _ _) fun _ => unbox64OrBigNat_noNatOverflow ..
                  · refine preserves_bind (preserves_assign _ _) fun _ => ?_
                    split
                    · exact preserves_emit _
                    · exact preserves_pure ()
            · exact preserves_throw _

theorem instrRepBig_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert) (ins : Cfg.Instr)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) (liveAfter liveTerm : Src.NatSet)
    (rest : List Cfg.Instr) :
    PreservesNoOvf (instrRepBig f T procs cert fc ins sc bc rc liveAfter liveTerm rest) := by
  cases ins with
  | bind x rhs =>
    cases rhs with
    | fir fr =>
      cases fr with
      | arg a =>
        unfold instrRepBig
        dsimp only
        cases a with
        | var y =>
          dsimp only
          split
          · exact preserves_bind (preserves_emit _) fun _ =>
              preserves_bind (operandAtRepBig_noNatOverflow ..) fun _ => preserves_assign _ _
          · exact preserves_bind (operandAtRepBig_noNatOverflow ..) fun _ => preserves_assign _ _
        | _ => exact preserves_bind (operandAtRepBig_noNatOverflow ..) fun _ => preserves_assign _ _
      | prim op as => exact primitiveRepBig_noNatOverflow ..
      | call g as =>
        refine preserves_bind (emitIncCallArgs_noNatOverflow ..) fun _ =>
          preserves_bind (operandsAtRepsBig_noNatOverflow ..) fun las => ?_
        dsimp only
        split
        · exact preserves_bind preserves_freshReg fun _ =>
            preserves_bind (preserves_emit _) fun _ => box64_noNatOverflow ..
        · split
          · exact preserves_bind preserves_freshReg fun _ =>
              preserves_bind (preserves_emit _) fun _ => promoteRaw64ToNatVal_noNatOverflow ..
          · exact preserves_emit _
      | ctor _ _ => exact preserves_throw _
      | proj _ _ _ => exact preserves_throw _
    | alloc c as _ => exact allocRepBig_noNatOverflow ..
    | proj y c i => exact projRepBig_noNatOverflow ..

theorem instrsRepBigAnn_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert) (sc : StrCtx) (bc : BigNatLitCtx)
    (rc : RcCtx) (liveTerm : Src.NatSet) :
    ∀ xs, PreservesNoOvf (instrsRepBigAnn f T procs cert fc sc bc rc liveTerm xs)
  | [] => preserves_pure ()
  | [(i, la)] => instrRepBig_noNatOverflow ..
  | (i1, la1) :: (i2, la2) :: rest => by
    unfold instrsRepBigAnn
    cases matchLimbPair i1 i2 with
    | some _ =>
      exact preserves_bind (emitLimbPairBig_noNatOverflow ..) fun _ =>
        instrsRepBigAnn_noNatOverflow ..
    | none =>
      exact preserves_bind (instrRepBig_noNatOverflow ..) fun _ =>
        instrsRepBigAnn_noNatOverflow ..

theorem edgeRepBig_noNatOverflow (f : FunId) (fc : Fir.Rep.FunCert)
    (blockReps : NatMap (List Fir.Rep)) (src : Nat) (e : Cfg.Edge)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) :
    PreservesNoOvf (edgeRepBig f fc blockReps src e sc bc rc) := by
  unfold edgeRepBig
  by_cases hord : (e.back == decide (e.target ≤ src)) = true
  · simp only [hord, ↓reduceIte]
    have hcont : ∀ (opt : Option (List Lir.Arg)), PreservesNoOvf (match opt with
      | some las => pure ⟨.blk e.target, las⟩
      | none => do
        let saved ← get
        let tramp ← newLabel
        modify fun st => { st with cur := tramp, params := [], acc := [] }
        (edgeIncVars fc rc e).forM fun y => emit (.call [] (rc.arrBase + Rt.Rc.Array.fnIncVal) [.v y])
        let las ← operandsAtRepsBig f fc e.args (blockReps.getD e.target (List.replicate e.args.length .tobj)) sc bc
        close (.jump ⟨.blk e.target, las⟩)
        modify fun st => { st with cur := saved.cur, params := saved.params, acc := saved.acc }
        pure (loc tramp)) := by
      intro opt
      cases opt with
      | some _ => exact preserves_pure _
      | none =>
        exact preserves_bind preserves_get fun _ =>
          preserves_bind preserves_newLabel fun _ =>
          preserves_bind (preserves_modify_keepDone _ fun _ => rfl) fun _ =>
          preserves_bind (preserves_forM fun _ _ => preserves_emit _) fun _ =>
          preserves_bind (operandsAtRepsBig_noNatOverflow ..) fun _ =>
          preserves_bind (preserves_close (by trivial)) fun _ =>
          preserves_bind (preserves_modify_keepDone _ fun _ => rfl) fun _ =>
          preserves_pure _
    split
    · exact preserves_bind (preserves_liftExcept _) hcont
    · exact preserves_bind (preserves_pure _) hcont
  · simp only [hord]
    exact preserves_bind_throw ..

theorem switchRepBig_noNatOverflow (f : FunId) (T : Tables) (cert : Fir.Rep.Cert)
    (fc : Fir.Rep.FunCert) (blockReps : NatMap (List Fir.Rep)) (src : Nat) (x : VReg)
    (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) :
    PreservesNoOvf (switchRepBig f T cert fc blockReps src x alts d sc bc rc) := by
  unfold switchRepBig
  have hbody : PreservesNoOvf (do
      let es ← alts.mapM (switchAltRepBig f T fc blockReps src · sc bc rc)
      let dd ← d.mapM (edgeRepBig f fc blockReps src · sc bc rc)
      let nats := es.filter (·.1.isNat)
      if !nats.isEmpty then
        unless nats.length == es.length do throw (.switch f src "Nat keys mixed with other keys")
        natSwitch x es dd
      else tagSwitch x es dd) := by
    refine preserves_bind (preserves_mapM fun ke _ => by
        unfold switchAltRepBig
        cases keyKind T ke.1 with
        | none => exact preserves_throw _
        | some _ => exact preserves_bind (edgeRepBig_noNatOverflow ..) fun _ => preserves_pure _) fun es =>
      preserves_bind (preserves_optMapM fun e _ => edgeRepBig_noNatOverflow ..) fun dd => ?_
    dsimp only
    split
    · by_cases hlen : ((es.filter (·.1.isNat)).length == es.length) = true
      · simp only [hlen, ↓reduceIte]; exact natSwitch_noNatOverflow ..
      · simp only [hlen]; exact preserves_bind_throw ..
    · exact tagSwitch_noNatOverflow ..
  dsimp only
  cases alts with
  | cons p rest =>
    cases rest with
    | nil =>
      cases d with
      | none =>
        dsimp only
        split
        · exact preserves_bind (edgeRepBig_noNatOverflow ..) fun _ =>
            preserves_bind (preserves_close (by trivial)) fun _ => preserves_pure ()
        · exact hbody
      | some _ => exact hbody
    | cons _ _ => exact hbody
  | nil => exact hbody

theorem termRepBig_noNatOverflow (f : FunId) (T : Tables) (cert : Fir.Rep.Cert)
    (fc : Fir.Rep.FunCert) (blockReps : NatMap (List Fir.Rep)) (src : Nat) (t : Cfg.Term)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) :
    PreservesNoOvf (termRepBig f T cert fc blockReps src t sc bc rc) := by
  cases t with
  | jump e => exact preserves_bind (edgeRepBig_noNatOverflow ..) fun _ => preserves_close (by trivial)
  | switch x alts d => exact switchRepBig_noNatOverflow ..
  | ret a => exact preserves_bind (operandAtRepBig_noNatOverflow ..) fun _ => preserves_close (by trivial)
  | tcall g as =>
    exact preserves_bind (emitIncCallArgs_noNatOverflow ..) fun _ =>
      preserves_bind (operandsAtRepsBig_noNatOverflow ..) fun _ => preserves_close (by trivial)
  | trap => exact preserves_close (by trivial)

theorem blockRepBig_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert) (blockReps : NatMap (List Fir.Rep))
    (uses : NatMap Nat) (src : Nat) (entry : Bool) (b : Cfg.Block)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) :
    PreservesNoOvf (blockRepBig f T procs cert fc blockReps uses src entry b sc bc rc) := by
  unfold blockRepBig blockCodeRepBig
  refine preserves_bind (preserves_openAt _ _) fun _ => ?_
  dsimp only
  cases fusable T uses b with
  | none =>
    exact preserves_bind (instrsRepBigAnn_noNatOverflow ..) fun _ => termRepBig_noNatOverflow ..
  | some p =>
    dsimp only
    split
    · refine preserves_bind (instrsRepBigAnn_noNatOverflow ..) fun _ =>
        preserves_bind (operandsRaw64Big_noNatOverflow ..) fun las => ?_
      cases las with
      | cons la rest =>
        cases rest with
        | cons la' rest2 =>
          cases rest2 with
          | nil =>
            cases b.term with
            | switch _ alts d =>
              exact preserves_bind (preserves_optMapM fun _ _ => edgeRepBig_noNatOverflow ..) fun te =>
                preserves_bind (preserves_optMapM fun _ _ => edgeRepBig_noNatOverflow ..) fun fe =>
                fusedClose_noNatOverflow ..
            | _ => exact termRepBig_noNatOverflow ..
          | cons _ _ => exact preserves_throw _
        | nil => exact preserves_throw _
      | nil => exact preserves_throw _
    · exact preserves_bind (instrsRepBigAnn_noNatOverflow ..) fun _ => termRepBig_noNatOverflow ..

private theorem chunksRepBig_noNatOverflow (f : FunId) (T : Tables) (procs : BigNatProcs)
    (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert) (blockReps : NatMap (List Fir.Rep))
    (uses : NatMap Nat) (merged : Bool) (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) :
    ∀ bs fresh cs fresh',
      chunksRepBig f T procs cert fc blockReps uses merged bs fresh sc bc rc = .ok (cs, fresh') →
      ∀ c ∈ cs, ∀ pb ∈ c, PBlockNoOvf pb
  | [], _, cs, _, h => by
    simp only [chunksRepBig, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; intro _ hm; cases hm
  | (b, i) :: bs, fresh, cs, fresh', h => by
    unfold chunksRepBig at h
    cases hrun : (blockRepBig f T procs cert fc blockReps uses i (merged && i == 0) b sc bc rc).run { fresh } with
    | error _ => simp [hrun, bind, Except.bind] at h
    | ok p =>
      simp only [hrun, bind, Except.bind] at h
      cases hchk : chunkBlocks f p.2 with
      | error _ => simp [hchk] at h
      | ok blks =>
        simp only [hchk] at h
        cases hrest : chunksRepBig f T procs cert fc blockReps uses merged bs p.2.fresh sc bc rc with
        | error _ => simp [hrest] at h
        | ok pr =>
          simp only [hrest, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have hst0 : StNoOvf { fresh := fresh } := fun l _ hg => by simp [NatMap.get?] at hg
          have hst' := (blockRepBig_noNatOverflow f T procs cert fc blockReps uses i
            (merged && i == 0) b sc bc rc).run { fresh } p.1 p.2 hst0 hrun
          intro c hc
          cases hc with
          | head => exact chunkBlocks_noNatOverflow hst' hchk
          | tail _ hc' => exact chunksRepBig_noNatOverflow f T procs cert fc blockReps uses merged sc bc rc bs p.2.fresh pr.1 pr.2 hrest c hc'

private theorem toRawWordParamBig_noNatOverflow (reg : VReg) (rep : Fir.Rep) :
    PreservesNoOvf (toRawWordParamBig reg rep) := by
  cases rep with
  | word => exact preserves_pure _
  | tobj => exact preserves_bind preserves_freshReg fun r =>
      preserves_bind (natValLow64_noNatOverflow r (.v reg)) fun _ => preserves_pure _
  | obj => exact preserves_bind preserves_freshReg fun r =>
      preserves_bind (unbox64OrBigNat_noNatOverflow r (.v reg)) fun _ => preserves_pure _
  | erased => exact preserves_pure _

private theorem toRawIndexBig_noNatOverflow (reg : VReg) (rep : Fir.Rep) :
    PreservesNoOvf (toRawIndexBig reg rep) := by
  cases rep with
  | word => exact preserves_pure _
  | tobj => exact preserves_bind preserves_freshReg fun r =>
      preserves_bind (natValSaturate64_noNatOverflow r (.v reg)) fun _ => preserves_pure _
  | obj => exact preserves_bind preserves_freshReg fun r =>
      preserves_bind (unbox64OrSaturateBigNat_noNatOverflow r (.v reg)) fun _ => preserves_pure _
  | erased => exact preserves_pure _

private theorem paramRegRepBig_noNatOverflow (f : FunId) (params : List VReg)
    (fc : Fir.Rep.FunCert) (idx : Nat) :
    PreservesNoOvf (paramRegRepBig f params fc idx) := by
  unfold paramRegRepBig
  cases params[idx]? with
  | none => exact preserves_throw _
  | some _ => exact preserves_pure _

private theorem arrayPrimBody_noNatOverflow (arrBase : FunId) (f : FunId)
    (params : List VReg) (fc : Fir.Rep.FunCert) (spec : Fir.Rep.ArrayPrimSpec) :
    PreservesNoOvf (arrayPrimBody arrBase f params fc spec) := by
  unfold arrayPrimBody
  refine preserves_bind (preserves_openAt 0 []) fun _ => ?_
  split
  · solve_no_ovf
  · exact preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (toRawIndexBig_noNatOverflow ..) fun _ => by solve_no_ovf
  · refine preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind preserves_freshReg fun _ =>
      preserves_bind (preserves_emit _) fun _ => ?_
    split
    · exact preserves_close (by trivial)
    · exact preserves_bind preserves_freshReg fun _ =>
        preserves_bind (promoteRaw64ToNatVal_noNatOverflow ..) fun _ =>
        preserves_close (by trivial)
  · refine preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (toRawIndexBig_noNatOverflow ..) fun _ => ?_
    cases spec.kind with
    | bytes =>
      refine preserves_bind preserves_freshReg fun _ =>
        preserves_bind (preserves_emit _) fun _ => ?_
      split
      · exact preserves_close (by trivial)
      · exact preserves_bind (preserves_temp _) fun _ => preserves_close (by trivial)
    | limbs =>
      exact preserves_bind preserves_freshReg fun _ =>
        preserves_bind (preserves_emit _) fun _ =>
        preserves_bind preserves_freshReg fun _ =>
        preserves_bind (finishRaw64Big_noNatOverflow ..) fun _ =>
        preserves_close (by trivial)
    | boxed =>
      refine preserves_bind preserves_freshReg fun _ =>
        preserves_bind (preserves_emit _) fun _ =>
        preserves_bind (preserves_emit _) fun _ => ?_
      split
      · exact preserves_bind preserves_freshReg fun _ =>
          preserves_bind (unbox64OrBigNat_noNatOverflow ..) fun _ =>
          preserves_close (by trivial)
      · exact preserves_close (by trivial)
  · by_cases hbytes : (spec.kind == .bytes) = true
    · simp only [hbytes, ↓reduceIte]
      refine preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
        preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
        preserves_bind (toRawIndexBig_noNatOverflow ..) fun _ =>
        preserves_bind preserves_freshReg fun _ =>
        preserves_bind (preserves_emit _) fun _ =>
        preserves_bind preserves_newLabel fun _ =>
        preserves_bind preserves_newLabel fun _ =>
        preserves_bind (preserves_close (by trivial)) fun _ =>
        preserves_bind (preserves_openAt _ _) fun _ =>
        preserves_bind preserves_freshReg fun _ =>
        preserves_bind (preserves_emit _) fun _ => ?_
      split
      · exact preserves_bind (preserves_close (by trivial)) fun _ =>
          preserves_bind (preserves_openAt _ _) fun _ => preserves_close (by trivial)
      · exact preserves_bind (preserves_temp _) fun _ =>
          preserves_bind (preserves_close (by trivial)) fun _ =>
          preserves_bind (preserves_openAt _ _) fun _ => preserves_close (by trivial)
    · simp only [hbytes]
      exact preserves_bind_throw ..
  · refine preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (toRawIndexBig_noNatOverflow ..) fun _ =>
      preserves_bind preserves_freshReg fun _ => ?_
    dsimp only
    cases spec.kind with
    | bytes => exact preserves_bind (toRawWordParamBig_noNatOverflow ..) fun _ =>
        preserves_bind (preserves_emit _) fun _ => preserves_close (by trivial)
    | limbs => exact preserves_bind (toRawWordParamBig_noNatOverflow ..) fun _ =>
        preserves_bind (preserves_emit _) fun _ => preserves_close (by trivial)
    | boxed =>
      dsimp only
      split
      · exact preserves_bind preserves_freshReg fun _ =>
          preserves_bind (box64_noNatOverflow ..) fun _ =>
          preserves_bind (preserves_pure _) fun _ =>
          preserves_bind (preserves_emit _) fun _ => preserves_close (by trivial)
      · exact preserves_bind (preserves_pure _) fun _ =>
          preserves_bind (preserves_emit _) fun _ => preserves_close (by trivial)
  · refine preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind preserves_freshReg fun _ => ?_
    dsimp only
    cases spec.kind with
    | bytes => exact preserves_bind (toRawWordParamBig_noNatOverflow ..) fun _ =>
        preserves_bind (preserves_emit _) fun _ => preserves_close (by trivial)
    | limbs => exact preserves_bind (toRawWordParamBig_noNatOverflow ..) fun _ =>
        preserves_bind (preserves_emit _) fun _ => preserves_close (by trivial)
    | boxed =>
      dsimp only
      split
      · exact preserves_bind preserves_freshReg fun _ =>
          preserves_bind (box64_noNatOverflow ..) fun _ =>
          preserves_bind (preserves_pure _) fun _ =>
          preserves_bind (preserves_emit _) fun _ => preserves_close (by trivial)
      · exact preserves_bind (preserves_pure _) fun _ =>
          preserves_bind (preserves_emit _) fun _ => preserves_close (by trivial)
  · exact preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ => by solve_no_ovf
  · exact preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (toRawIndexBig_noNatOverflow ..) fun _ =>
      preserves_bind (toRawIndexBig_noNatOverflow ..) fun _ => by solve_no_ovf
  · exact preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (toRawIndexBig_noNatOverflow ..) fun _ =>
      preserves_bind (toRawIndexBig_noNatOverflow ..) fun _ =>
      preserves_bind (toRawIndexBig_noNatOverflow ..) fun _ => by solve_no_ovf
  · exact preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (paramRegRepBig_noNatOverflow ..) fun _ =>
      preserves_bind (toRawIndexBig_noNatOverflow ..) fun _ =>
      preserves_bind (toRawIndexBig_noNatOverflow ..) fun _ => by solve_no_ovf
  · exact preserves_throw _

theorem arrayPrimFuncBig_noNatOverflow {arrBase : FunId} {f : FunId} {fd : Cfg.Fun}
    {fc : Fir.Rep.FunCert} {spec : Fir.Rep.ArrayPrimSpec} {conv : Lir.Conv} {lf : Lir.Func}
    (h : arrayPrimFuncBig arrBase f fd fc spec conv = .ok lf) :
    LirFuncNoOvf lf := by
  unfold arrayPrimFuncBig at h
  cases hb0 : fd.blocks.head? with
  | none => simp [hb0, throw, throwThe, MonadExceptOf.throw] at h
  | some b0 =>
    simp only [hb0] at h
    obtain ⟨p, hrun, h⟩ := except_bind_ok h
    obtain ⟨pblocks, hchk, h⟩ := except_bind_ok h
    obtain ⟨raw, hres, h⟩ := except_bind_ok h
    by_cases hrc : reachClosed raw (reachable raw) = true
    · simp only [hrc, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      apply splitCriticalEdges_noNatOverflow
      intro b hb
      apply pruneWith_noNatOverflow _ b hb
      have hst0 : StNoOvf { fresh := max fd.vars (maxVar fd + 1) } :=
        fun l _ hg => by simp [NatMap.get?] at hg
      have hst' := (arrayPrimBody_noNatOverflow arrBase f (b0.params.map (·.1)) fc spec).run
        _ p.1 p.2 hst0 hrun
      exact resolveChunks_noNatOverflow (fun c hc => by
        cases hc with
        | head => exact chunkBlocks_noNatOverflow hst' hchk
        | tail _ hm => cases hm) hres
    · simp [hrc, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h

/-- **Every user function lowered by `functionRepBig` has ZERO `.fail .natOverflow` blocks.** -/
theorem functionRepBig_noNatOverflow {T : Tables} {procs : BigNatProcs}
    {cert : Fir.Rep.Cert} {f : FunId} {fd : Cfg.Fun} {conv : Lir.Conv}
    {sc : StrCtx} {bc : BigNatLitCtx} {rc : RcCtx} {lf : Lir.Func}
    (h : functionRepBig T procs cert f fd conv sc bc rc = .ok lf) :
    LirFuncNoOvf lf := by
  unfold functionRepBig at h
  have hmain : (do
      let (params, raw) ← functionRawRepBig T procs cert f fd sc bc rc
      let seen := reachable raw
      unless reachClosed raw seen do throw (Error.internal f "a reached block has an unreached successor")
      pure (Lir.Func.splitCriticalEdges
        { name := s!"f{f}", params, results := 1, blocks := (pruneWith seen raw).toArray, conv })) = .ok lf →
      LirFuncNoOvf lf := by
    intro hm
    cases hraw : functionRawRepBig T procs cert f fd sc bc rc with
    | error _ => simp [hraw, bind, Except.bind] at hm
    | ok p =>
      simp only [hraw, bind, Except.bind] at hm
      by_cases hrc : reachClosed p.2 (reachable p.2) = true
      · simp only [hrc, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hm
        subst hm
        apply splitCriticalEdges_noNatOverflow
        intro b hb
        apply pruneWith_noNatOverflow _ b hb
        unfold functionRawRepBig at hraw
        cases hb0 : fd.blocks.head? with
        | none => simp [hb0, throw, throwThe, MonadExceptOf.throw] at hraw
        | some b0 =>
          simp only [hb0] at hraw
          cases hmis : misordered fd with
          | some _ => simp [hmis, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hraw
          | none =>
            simp only [hmis] at hraw
            obtain ⟨pcs, hcs, hraw⟩ := except_bind_ok hraw
            obtain ⟨body, hres, hraw⟩ := except_bind_ok hraw
            simp only [pure, Except.pure, Except.ok.injEq] at hraw
            obtain ⟨_, rfl⟩ := hraw
            have hbody : ∀ lb ∈ body, LirBlockNoOvf lb :=
              resolveChunks_noNatOverflow (fun c hc =>
                chunksRepBig_noNatOverflow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcs c.1 (mem_of_mem_zipIdx hc)) hres
            intro lb hlb
            rcases List.mem_append.mp hlb with hentry | hbdy
            · split at hentry
              · cases hentry
              · cases hentry with
                | head => trivial
                | tail _ hm' => cases hm'
            · exact hbody lb hbdy
      · simp [hrc, throw, throwThe, MonadExceptOf.throw] at hm
  by_cases hrcEn : rc.enabled = true
  · simp only [hrcEn, ↓reduceIte] at h
    cases hsp : cert.arrayPrims.get? f with
    | some spec =>
      simp only [hsp] at h
      exact arrayPrimFuncBig_noNatOverflow h
    | none =>
      simp only [hsp, pure, Except.pure, bind, Except.bind] at h
      exact hmain h
  · simp only [hrcEn] at h
    exact hmain h

theorem functionsRepBig_noNatOverflow {T : Tables} {procs : BigNatProcs}
    {cert : Fir.Rep.Cert} {P : Cfg.Program} {roots : List (FunId × String)}
    {sc : StrCtx} {bc : BigNatLitCtx} {rc : RcCtx} :
    ∀ {fs : List Nat} {lfs : List Lir.Func},
      functionsRepBig T procs cert P roots fs sc bc rc = .ok lfs →
      ∀ lf ∈ lfs, LirFuncNoOvf lf
  | [], lfs, h => by
    simp only [functionsRepBig, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro _ hm; cases hm
  | f :: fs, lfs, h => by
    unfold functionsRepBig at h
    cases hfd : P.fun? f with
    | none => simp [hfd, throw, throwThe, MonadExceptOf.throw] at h
    | some fd =>
      simp only [hfd] at h
      obtain ⟨lf, h1, h⟩ := except_bind_ok h
      obtain ⟨rest, hrest, h⟩ := except_bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro x hx
      cases hx with
      | head => exact functionRepBig_noNatOverflow h1
      | tail _ hx' => exact functionsRepBig_noNatOverflow hrest x hx'

/-! ### Runtime Procedures, Materializers, and `BigNat` ABI Wrappers: Zero `.fail .natOverflow` -/

theorem bigNatLitProc_noNatOverflow (idx n : Nat) : LirFuncNoOvf (bigNatLitProc idx n) := by
  unfold bigNatLitProc
  dsimp only
  split
  · intro b hb; simp at hb; subst hb; trivial
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> trivial

theorem strLitProc_noNatOverflow (idx : Nat) (s : String) :
    LirFuncNoOvf (Rt.Rc.Array.strLitProc idx s) := by
  unfold Rt.Rc.Array.strLitProc
  dsimp only
  split
  · intro b hb; simp at hb; subst hb; trivial
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> trivial

theorem cxInit_noNatOverflow : LirFuncNoOvf Procs.cxInit := by
  intro b hb
  unfold Procs.cxInit at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem natPowBig_noNatOverflow (slowPow : FunId) : LirFuncNoOvf (Procs.natPowBig slowPow) := by
  intro b hb
  unfold Procs.natPowBig at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  repeat (rcases hb with rfl | hb; · trivial)

theorem natGcdBig_noNatOverflow (slowGcd : FunId) : LirFuncNoOvf (Procs.natGcdBig slowGcd) := by
  intro b hb
  unfold Procs.natGcdBig at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  repeat (rcases hb with rfl | hb; · trivial)

private theorem relocateFunc_noNatOverflow (base : FunId) {f : Lir.Func} (hf : LirFuncNoOvf f) :
    LirFuncNoOvf (relocateFunc base f) := by
  unfold relocateFunc
  apply splitCriticalEdges_noNatOverflow
  intro b hb
  rw [Array.toList_map, List.mem_map] at hb
  obtain ⟨b0, hb0, rfl⟩ := hb
  have h0 := hf b0 hb0
  unfold LirBlockNoOvf at h0 ⊢
  cases ht : b0.term <;> (simp [Rt.Rc.Array.relocateBlock, Rt.Rc.Array.relocateTerm, ht] at h0 ⊢; first | exact h0 | trivial)

private theorem arrayRuntimeFuncs_noNatOverflow :
    ∀ f ∈ Rt.Rc.Array.arrayRuntimeFuncs.toList, LirFuncNoOvf f := by
  have hdec : (Rt.Rc.Array.arrayRuntimeFuncs.toList.all fun f =>
      f.blocks.toList.all fun b =>
        match b.term with | .fail .natOverflow => false | _ => true) = true := by decide
  rw [List.all_eq_true] at hdec
  intro f hf b hb
  have hbf := hdec f hf
  rw [List.all_eq_true] at hbf
  have hbb := hbf b hb
  unfold LirBlockNoOvf
  cases ht : b.term with
  | fail r =>
    rw [ht] at hbb
    cases r with
    | natOverflow => cases hbb
    | _ => trivial
  | _ => trivial

private theorem lirFuncNoOvf_of_all (f : Lir.Func)
    (h : (f.blocks.toList.all fun b =>
      match b.term with | .fail .natOverflow => false | _ => true) = true) :
    LirFuncNoOvf f := by
  rw [List.all_eq_true] at h
  intro b hb
  have hbb := h b hb
  unfold LirBlockNoOvf
  cases ht : b.term with
  | fail r =>
    rw [ht] at hbb
    cases r with
    | natOverflow => cases hbb
    | _ => trivial
  | _ => trivial

theorem extendedArrayRuntimeFuncs_noNatOverflow (base : FunId) (nilTag consTag : Nat) :
    ∀ f ∈ Rt.Rc.Array.extendedArrayRuntimeFuncs base nilTag consTag, LirFuncNoOvf f := by
  unfold Rt.Rc.Array.extendedArrayRuntimeFuncs
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨f0, hf0, rfl⟩ := hf
  apply relocateFunc_noNatOverflow
  rcases List.mem_append.mp hf0 with hbase | hext
  · exact arrayRuntimeFuncs_noNatOverflow f0 hbase
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hext
    rcases hext with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lirFuncNoOvf_of_all _ (by decide)
    · exact lirFuncNoOvf_of_all _ (by decide)
    · exact lirFuncNoOvf_of_all _ (by decide)
    · exact lirFuncNoOvf_of_all _ (by simp [arrToListBoxed])
    · exact lirFuncNoOvf_of_all _ (by decide)
    · exact lirFuncNoOvf_of_all _ (by simp [arrToListLimbs])
    · exact lirFuncNoOvf_of_all _ (by decide)
    · exact lirFuncNoOvf_of_all _ (by decide)

theorem bumpAllocCell_noNatOverflow (ptr : VReg) (nobj tag : Nat) (field : Lir.Arg) :
    PreservesNoOvf (bumpAllocCell ptr nobj tag field) := by
  unfold bumpAllocCell; solve_no_ovf_step

theorem emitNatValToSlowNat_noNatOverflow (smallTag bigTag : Nat) (smallFieldRep : Fir.Rep)
    (out w : VReg) : PreservesNoOvf (emitNatValToSlowNat smallTag bigTag smallFieldRep out w) := by
  unfold emitNatValToSlowNat
  refine preserves_bind preserves_newLabel fun smallBlk =>
    preserves_bind preserves_newLabel fun bigBlk =>
    preserves_bind preserves_newLabel fun incRcBlk =>
    preserves_bind preserves_newLabel fun noIncBlk =>
    preserves_bind preserves_newLabel fun allocBigBlk =>
    preserves_bind preserves_newLabel fun joinBlk =>
    preserves_bind (preserves_close (by trivial)) fun _ =>
    preserves_bind (preserves_openAt _ _) fun _ =>
    preserves_bind preserves_freshReg fun pSmall => ?_
  dsimp only
  split
  · exact preserves_bind (preserves_bin _ _ _) fun _ =>
      preserves_bind (bumpAllocCell_noNatOverflow _ _ _ _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_openAt _ _) fun _ =>
      preserves_bind (preserves_temp _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_openAt _ _) fun _ =>
      preserves_bind preserves_freshReg fun _ =>
      preserves_bind (preserves_assign _ _) fun _ =>
      preserves_bind (preserves_emit _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_openAt _ _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_openAt _ _) fun _ =>
      preserves_bind preserves_freshReg fun _ =>
      preserves_bind (bumpAllocCell_noNatOverflow _ _ _ _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_openAt _ _
  · exact preserves_bind (bumpAllocCell_noNatOverflow _ _ _ _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_openAt _ _) fun _ =>
      preserves_bind (preserves_temp _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_openAt _ _) fun _ =>
      preserves_bind preserves_freshReg fun _ =>
      preserves_bind (preserves_assign _ _) fun _ =>
      preserves_bind (preserves_emit _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_openAt _ _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_openAt _ _) fun _ =>
      preserves_bind preserves_freshReg fun _ =>
      preserves_bind (bumpAllocCell_noNatOverflow _ _ _ _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_openAt _ _

theorem emitSlowNatToNatVal_noNatOverflow (smallTag : Nat) (smallFieldRep : Fir.Rep)
    (out sn : VReg) : PreservesNoOvf (emitSlowNatToNatVal smallTag smallFieldRep out sn) := by
  unfold emitSlowNatToNatVal
  refine preserves_bind (preserves_temp _) fun _ =>
    preserves_bind preserves_newLabel fun smallBlk =>
    preserves_bind preserves_newLabel fun bigBlk =>
    preserves_bind preserves_newLabel fun joinBlk =>
    preserves_bind (preserves_close (by trivial)) fun _ =>
    preserves_bind (preserves_openAt _ _) fun _ =>
    preserves_bind preserves_freshReg fun f =>
    preserves_bind (preserves_assign _ _) fun _ => ?_
  have htail : PreservesNoOvf (do
      openAt bigBlk
      let lp ← freshReg
      assign lp (.load .w64 .zero (mem sn (fieldOffset 0)))
      let rc ← temp (.load .w32 .zero (mem lp 4))
      let setRcBlk ← newLabel
      let keepRcBlk ← newLabel
      close (.br .eq rc (.imm 0) (loc setRcBlk) (loc keepRcBlk))
      openAt setRcBlk
      emit (.store .w32 (mem lp 4) (.imm 1))
      close (.jump ⟨.loc joinBlk, [.v lp]⟩)
      openAt keepRcBlk
      close (.jump ⟨.loc joinBlk, [.v lp]⟩)
      openAt joinBlk [out]) := by
    solve_no_ovf_step
  dsimp only
  split
  · exact preserves_bind (preserves_temp _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ => htail
  · exact preserves_bind preserves_newLabel fun _ =>
      preserves_bind preserves_newLabel fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_openAt _ _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ =>
      preserves_bind (preserves_openAt _ _) fun _ =>
      preserves_bind (preserves_temp _) fun _ =>
      preserves_bind (preserves_temp _) fun _ =>
      preserves_bind (preserves_close (by trivial)) fun _ => htail

private theorem buildWrapperFunc_noNatOverflow {name : String} {params : List VReg}
    {freshStart : VReg} {conv : Lir.Conv} {act : M Unit} {lf : Lir.Func}
    (hact : PreservesNoOvf act)
    (h : buildWrapperFunc name params freshStart conv act = .ok lf) :
    LirFuncNoOvf lf := by
  unfold buildWrapperFunc at h
  obtain ⟨p, hrun, h⟩ := except_bind_ok h
  obtain ⟨pblocks, hchk, h⟩ := except_bind_ok h
  obtain ⟨raw, hres, h⟩ := except_bind_ok h
  by_cases hrc : reachClosed raw (reachable raw) = true
  · simp only [hrc, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    subst h
    apply splitCriticalEdges_noNatOverflow
    intro b hb
    apply pruneWith_noNatOverflow _ b hb
    have hst0 : StNoOvf { fresh := freshStart } := fun l _ hg => by simp [NatMap.get?] at hg
    have hst' := hact.run _ p.1 p.2 hst0 hrun
    exact resolveChunks_noNatOverflow (fun c hc => by
      cases hc with
      | head => exact chunkBlocks_noNatOverflow hst' hchk
      | tail _ hm => cases hm) hres
  · simp [hrc, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h

theorem mkBinNatWrapper_noNatOverflow {lib : CompiledBigNatLib} {name : String}
    {callee : FunId} {conv : Lir.Conv} {lf : Lir.Func}
    (h : mkBinNatWrapper lib name callee conv = .ok lf) : LirFuncNoOvf lf := by
  unfold mkBinNatWrapper at h
  refine buildWrapperFunc_noNatOverflow ?_ h
  exact preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind (emitNatValToSlowNat_noNatOverflow ..) fun _ =>
    preserves_bind (emitNatValToSlowNat_noNatOverflow ..) fun _ =>
    preserves_bind (preserves_emit _) fun _ =>
    preserves_bind (emitSlowNatToNatVal_noNatOverflow ..) fun _ =>
    preserves_close (by trivial)

theorem mkUnNatWrapper_noNatOverflow {lib : CompiledBigNatLib} {name : String}
    {callee : FunId} {conv : Lir.Conv} {lf : Lir.Func}
    (h : mkUnNatWrapper lib name callee conv = .ok lf) : LirFuncNoOvf lf := by
  unfold mkUnNatWrapper at h
  refine buildWrapperFunc_noNatOverflow ?_ h
  exact preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind (emitNatValToSlowNat_noNatOverflow ..) fun _ =>
    preserves_bind (preserves_emit _) fun _ =>
    preserves_bind (emitSlowNatToNatVal_noNatOverflow ..) fun _ =>
    preserves_close (by trivial)

theorem mkOptBinNatWrapper_noNatOverflow {lib : CompiledBigNatLib} {name : String}
    {callee : FunId} {conv : Lir.Conv} {lf : Lir.Func}
    (h : mkOptBinNatWrapper lib name callee conv = .ok lf) : LirFuncNoOvf lf := by
  unfold mkOptBinNatWrapper at h
  refine buildWrapperFunc_noNatOverflow ?_ h
  exact preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind (emitNatValToSlowNat_noNatOverflow ..) fun _ =>
    preserves_bind (emitNatValToSlowNat_noNatOverflow ..) fun _ =>
    preserves_bind (preserves_emit _) fun _ =>
    preserves_bind preserves_newLabel fun _ =>
    preserves_bind preserves_newLabel fun _ =>
    preserves_bind (preserves_close (by trivial)) fun _ =>
    preserves_bind (preserves_put (by trivial)) fun _ =>
    preserves_bind (preserves_openAt _ _) fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind (preserves_assign _ _) fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind (emitSlowNatToNatVal_noNatOverflow ..) fun _ =>
    preserves_close (by trivial)

theorem mkCmpNatWrapper_noNatOverflow {lib : CompiledBigNatLib} {name : String}
    {callee : FunId} {tWord fWord : Word} {conv : Lir.Conv} {lf : Lir.Func}
    (h : mkCmpNatWrapper lib name callee tWord fWord conv = .ok lf) : LirFuncNoOvf lf := by
  unfold mkCmpNatWrapper at h
  refine buildWrapperFunc_noNatOverflow ?_ h
  exact preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind (emitNatValToSlowNat_noNatOverflow ..) fun _ =>
    preserves_bind (emitNatValToSlowNat_noNatOverflow ..) fun _ =>
    preserves_bind (preserves_emit _) fun _ =>
    preserves_bind (preserves_assign _ _) fun _ =>
    preserves_close (by trivial)

theorem mkToDecimalWrapper_noNatOverflow {lib : CompiledBigNatLib} {name : String}
    {callee : FunId} {conv : Lir.Conv} {lf : Lir.Func}
    (h : mkToDecimalWrapper lib name callee conv = .ok lf) : LirFuncNoOvf lf := by
  unfold mkToDecimalWrapper at h
  refine buildWrapperFunc_noNatOverflow ?_ h
  exact preserves_bind preserves_freshReg fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind (emitNatValToSlowNat_noNatOverflow ..) fun _ =>
    preserves_bind (preserves_emit _) fun _ =>
    preserves_close (by trivial)

theorem mkOfDecimalWrapper_noNatOverflow {lib : CompiledBigNatLib} {name : String}
    {callee : FunId} {conv : Lir.Conv} {lf : Lir.Func}
    (h : mkOfDecimalWrapper lib name callee conv = .ok lf) : LirFuncNoOvf lf := by
  unfold mkOfDecimalWrapper at h
  refine buildWrapperFunc_noNatOverflow ?_ h
  exact preserves_bind preserves_freshReg fun _ =>
    preserves_bind (preserves_emit _) fun _ =>
    preserves_bind preserves_newLabel fun _ =>
    preserves_bind preserves_newLabel fun _ =>
    preserves_bind (preserves_close (by trivial)) fun _ =>
    preserves_bind (preserves_put (by trivial)) fun _ =>
    preserves_bind (preserves_openAt _ _) fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind (preserves_assign _ _) fun _ =>
    preserves_bind preserves_freshReg fun _ =>
    preserves_bind (emitSlowNatToNatVal_noNatOverflow ..) fun _ =>
    preserves_close (by trivial)

theorem buildCoreWrappers_noNatOverflow {lib : CompiledBigNatLib}
    {libBase wrapBase natPowId natGcdId : FunId} {bools : Option (Word × Word)}
    {wrappers : List Lir.Func} {procs : BigNatProcs} {sp sg : FunId}
    (h : buildCoreWrappers lib libBase wrapBase natPowId natGcdId bools = .ok (wrappers, procs, sp, sg)) :
    ∀ lf ∈ wrappers, LirFuncNoOvf lf := by
  unfold buildCoreWrappers at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fAdd, hAdd, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fSub, hSub, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fPred, hPred, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fMul, hMul, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fDiv, hDiv, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fMod, hMod, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fPow, hPow, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fGcd, hGcd, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fBeq, hBeq, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fBle, hBle, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fBlt, hBlt, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fLand, hLand, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fLor, hLor, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fXor, hXor, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fShl, hShl, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h; obtain ⟨fShr, hShr, h⟩ := except_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _, _, _⟩ := h
  intro lf hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mkBinNatWrapper_noNatOverflow hAdd
  · exact mkBinNatWrapper_noNatOverflow hSub
  · exact mkUnNatWrapper_noNatOverflow hPred
  · exact mkBinNatWrapper_noNatOverflow hMul
  · exact mkBinNatWrapper_noNatOverflow hDiv
  · exact mkBinNatWrapper_noNatOverflow hMod
  · exact mkOptBinNatWrapper_noNatOverflow hPow
  · exact mkBinNatWrapper_noNatOverflow hGcd
  · exact mkCmpNatWrapper_noNatOverflow hBeq
  · exact mkCmpNatWrapper_noNatOverflow hBle
  · exact mkCmpNatWrapper_noNatOverflow hBlt
  · exact mkBinNatWrapper_noNatOverflow hLand
  · exact mkBinNatWrapper_noNatOverflow hLor
  · exact mkBinNatWrapper_noNatOverflow hXor
  · exact mkOptBinNatWrapper_noNatOverflow hShl
  · exact mkBinNatWrapper_noNatOverflow hShr

theorem buildLiteralContexts_litProcs_noNatOverflow (cfg : Config)
    (strs : List String) (nats : List Nat) (litBase : FunId) :
    ∀ lf ∈ (buildLiteralContexts cfg strs nats litBase).2.2.1, LirFuncNoOvf lf := by
  unfold buildLiteralContexts
  split
  · intro _ hm; cases hm
  · dsimp only
    cases cfg.rodataBase with
    | some _ => intro _ hm; cases hm
    | none =>
      intro lf hmem
      rcases List.mem_append.mp hmem with hstr | hnat
      · rw [List.mem_map] at hstr
        obtain ⟨⟨⟨s, _⟩, i⟩, _, rfl⟩ := hstr
        exact strLitProc_noNatOverflow i s
      · rw [List.mem_map] at hnat
        obtain ⟨⟨⟨n, _⟩, i⟩, _, rfl⟩ := hnat
        exact bigNatLitProc_noNatOverflow i n

/-- **Top-level structural zero-`natOverflow` theorem for `lowerBig`:**
In any `lowerBig cfg lib P = .ok lo`, EVERY user function `0 ..< P.size`, `cxInit`, `natPowBig`,
`natGcdBig`, every literal materializer (`strLitProc` / `bigNatLitProc`), and every one of the 16
`BigNat` ABI wrappers has ZERO `.fail .natOverflow` blocks; and when `lib` itself satisfies
`LirFuncNoOvf`, the entire linked `Lir.Program` satisfies `LirProgramNoOvf` (so `Lir.eval` can
NEVER return `.resource .natOverflow`). -/
theorem lowerBig_noNatOverflow {cfg : Config} {lib : CompiledBigNatLib} {P : Cfg.Program}
    {lo : Lowered} (h : lowerBig cfg lib P = .ok lo)
    (hlib : ∀ f ∈ lib.funcs, LirFuncNoOvf f) :
    LirProgramNoOvf lo.program := by
  unfold lowerBig at h
  cases hmain : P.exports.head? with
  | none => simp [hmain, throw, throwThe, MonadExceptOf.throw] at h
  | some main =>
    simp only [hmain] at h
    cases hrange : P.funs.toList.find? (P.size ≤ ·.1) with
    | some _ => simp [hrange, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    | none =>
      simp only [hrange] at h
      obtain ⟨wp, hwrap, h⟩ := except_bind_ok h
      obtain ⟨funcs, hfuncs, h⟩ := except_bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro f hf
      rcases List.mem_append.mp hf with h1 | hwrapMem
      · rcases List.mem_append.mp h1 with h2 | hrelocMem
        · rcases List.mem_append.mp h2 with h3 | hlitMem
          · rcases List.mem_append.mp h3 with hfunMem | hprocMem
            · exact functionsBig_noNatOverflow hfuncs f hfunMem
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hprocMem
              rcases hprocMem with rfl | rfl | rfl
              · exact cxInit_noNatOverflow
              · exact natPowBig_noNatOverflow _
              · exact natGcdBig_noNatOverflow _
          · exact buildLiteralContexts_litProcs_noNatOverflow cfg _ _ _ f hlitMem
        · unfold CompiledBigNatLib.relocate at hrelocMem
          rw [List.mem_map] at hrelocMem
          obtain ⟨f0, hf0, rfl⟩ := hrelocMem
          exact relocateFunc_noNatOverflow _ (hlib f0 hf0)
      · exact buildCoreWrappers_noNatOverflow hwrap f hwrapMem

/-- **Top-level structural zero-`natOverflow` theorem for `lowerRepBig`:**
Same full guarantee for `lowerRepBig cfg lib cert P = .ok lo` (covering all user functions,
DR3 `arrayPrimFuncBig` wrappers, `extendedArrayRuntimeFuncs`, `cxInit`, `natPowBig`, `natGcdBig`,
literal materializers, and all 16 `BigNat` ABI wrappers). -/
theorem lowerRepBig_noNatOverflow {cfg : Config} {lib : CompiledBigNatLib}
    {cert : Fir.Rep.Cert} {P : Cfg.Program} {lo : Lowered}
    (h : lowerRepBig cfg lib cert P = .ok lo)
    (hlib : ∀ f ∈ lib.funcs, LirFuncNoOvf f) :
    LirProgramNoOvf lo.program := by
  unfold lowerRepBig at h
  cases hmain : P.exports.head? with
  | none => simp [hmain, throw, throwThe, MonadExceptOf.throw] at h
  | some main =>
    simp only [hmain] at h
    cases hrange : P.funs.toList.find? (P.size ≤ ·.1) with
    | some _ => simp [hrange, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    | none =>
      simp only [hrange] at h
      obtain ⟨wp, hwrap, h⟩ := except_bind_ok h
      obtain ⟨funcs, hfuncs, h⟩ := except_bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro f hf
      rcases List.mem_append.mp hf with h1 | hwrapMem
      · rcases List.mem_append.mp h1 with h2 | hrelocMem
        · rcases List.mem_append.mp h2 with h3 | hlitMem
          · rcases List.mem_append.mp h3 with h4 | harrMem
            · rcases List.mem_append.mp h4 with hfunMem | hprocMem
              · exact functionsRepBig_noNatOverflow hfuncs f hfunMem
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hprocMem
                rcases hprocMem with rfl | rfl | rfl
                · exact cxInit_noNatOverflow
                · exact natPowBig_noNatOverflow _
                · exact natGcdBig_noNatOverflow _
            · split at harrMem
              · exact extendedArrayRuntimeFuncs_noNatOverflow _ _ _ f harrMem
              · cases harrMem
          · exact buildLiteralContexts_litProcs_noNatOverflow cfg _ _ _ f hlitMem
        · unfold CompiledBigNatLib.relocate at hrelocMem
          rw [List.mem_map] at hrelocMem
          obtain ⟨f0, hf0, rfl⟩ := hrelocMem
          exact relocateFunc_noNatOverflow _ (hlib f0 hf0)
      · exact buildCoreWrappers_noNatOverflow hwrap f hwrapMem

/-! ## Section 5: Static `.rodata` `≥ 2^63` BigNat Literal Representation Proofs -/

/-- `buildBigNatRodataK` produces the exact same `.rodata` table and offsets as `buildBigNatRodata`. -/
theorem buildBigNatRodataK_eq (nats : List Nat) :
    buildBigNatRodataK nats = buildBigNatRodata nats := by
  unfold buildBigNatRodataK buildBigNatRodata
  have aux : ∀ (xs : List (Nat × Nat)) (tk : RodataTableK) (offs : List (Nat × Nat)),
      let resK := xs.foldl (init := (tk, offs)) fun (tbl, offs) (n, i) =>
        let (tbl', off) := addBigNatLiteralK tbl s!"cx_bignat_lit_{i}" n
        (tbl', offs ++ [(n, off)])
      let res := xs.foldl (init := (tk.toRodataTable, offs)) fun (tbl, offs) (n, i) =>
        let (tbl', off) := addBigNatLiteral tbl s!"cx_bignat_lit_{i}" n
        (tbl', offs ++ [(n, off)])
      (resK.1.toRodataTable, resK.2) = res := by
    intro xs
    induction xs with
    | nil => intro _ _; rfl
    | cons p xs ih =>
      intro tk offs
      simp only [List.foldl_cons]
      have hstep := addBigNatLiteralK_toRodataTable tk s!"cx_bignat_lit_{p.2}" p.1
      dsimp only at hstep ⊢
      have h1 : (addBigNatLiteralK tk s!"cx_bignat_lit_{p.2}" p.1).1.toRodataTable =
          (addBigNatLiteral tk.toRodataTable s!"cx_bignat_lit_{p.2}" p.1).1 :=
        congrArg Prod.fst hstep
      have h2 : (addBigNatLiteralK tk s!"cx_bignat_lit_{p.2}" p.1).2 =
          (addBigNatLiteral tk.toRodataTable s!"cx_bignat_lit_{p.2}" p.1).2 :=
        congrArg Prod.snd hstep
      rw [← h1, ← h2]
      exact ih _ _
  have h0 := aux nats.zipIdx RodataTableK.empty []
  exact h0

/-- Every `(n, off)` recorded by `buildBigNatRodata` is placed at an 8-byte-aligned offset
with its exact `encodeBigNatLiteral n` bytes preserved in the final `.rodata` section. -/
theorem buildBigNatRodata_entry_bytes (nats : List Nat) :
    let (tbl, offs) := buildBigNatRodata nats
    ∀ p ∈ offs,
      p.2 % 8 = 0 ∧
      ∃ (hbd : p.2 + (encodeBigNatLiteral p.1).size ≤ tbl.bytes.size),
        ∀ j (hj : j < (encodeBigNatLiteral p.1).size),
          tbl.bytes[p.2 + j]'(by omega) = (encodeBigNatLiteral p.1)[j]'hj := by
  unfold buildBigNatRodata
  have aux : ∀ (xs : List (Nat × Nat)) (t0 : RodataTable) (offs0 : List (Nat × Nat)),
      (∀ p ∈ offs0,
        p.2 % 8 = 0 ∧
        ∃ (hbd : p.2 + (encodeBigNatLiteral p.1).size ≤ t0.bytes.size),
          ∀ j (hj : j < (encodeBigNatLiteral p.1).size),
            t0.bytes[p.2 + j]'(by omega) = (encodeBigNatLiteral p.1)[j]'hj) →
      let res := xs.foldl (init := (t0, offs0)) fun (tbl, offs) (n, i) =>
        let (tbl', off) := addBigNatLiteral tbl s!"cx_bignat_lit_{i}" n
        (tbl', offs ++ [(n, off)])
      ∀ p ∈ res.2,
        p.2 % 8 = 0 ∧
        ∃ (hbd : p.2 + (encodeBigNatLiteral p.1).size ≤ res.1.bytes.size),
          ∀ j (hj : j < (encodeBigNatLiteral p.1).size),
            res.1.bytes[p.2 + j]'(by omega) = (encodeBigNatLiteral p.1)[j]'hj := by
    intro xs
    induction xs with
    | nil => intro _ _ h; exact h
    | cons x xs ih =>
      intro t0 offs0 h0
      simp only [List.foldl_cons]
      apply ih
      intro p hp
      rcases List.mem_append.mp hp with hold | hnew
      · obtain ⟨hal, hbd, hby⟩ := h0 p hold
        have hgrow : t0.bytes.size ≤ (addBigNatLiteral t0 s!"cx_bignat_lit_{x.2}" x.1).1.bytes.size := by
          unfold addBigNatLiteral RodataTable.addLimbArray
          have h1 := alignUp8_ge t0.bytes.size
          have h2 := RodataTable.addCell_bounds t0 s!"cx_bignat_lit_{x.2}"
            (encodeStaticLimbArray (IxCC.BigNat.ofNat x.1).toList)
          simp only [RodataTable.addCell] at h2 ⊢
          omega
        refine ⟨hal, by omega, fun j hj => ?_⟩
        unfold addBigNatLiteral RodataTable.addLimbArray
        rw [RodataTable.addCell_preserves_prefix t0 _ _ (by omega)]
        exact hby j hj
      · rw [List.mem_singleton] at hnew
        subst hnew
        unfold addBigNatLiteral encodeBigNatLiteral RodataTable.addLimbArray
        refine ⟨RodataTable.addCell_aligned t0 s!"cx_bignat_lit_{x.2}"
            (encodeStaticLimbArray (IxCC.BigNat.ofNat x.1).toList),
          RodataTable.addCell_bounds t0 s!"cx_bignat_lit_{x.2}"
            (encodeStaticLimbArray (IxCC.BigNat.ofNat x.1).toList), fun j hj => ?_⟩
        exact RodataTable.addCell_bytes_eq t0 s!"cx_bignat_lit_{x.2}"
          (encodeStaticLimbArray (IxCC.BigNat.ofNat x.1).toList) hj
  exact aux nats.zipIdx RodataTable.empty [] (fun _ h => by cases h)

/-- **Every `≥ 2^63` literal placed by `buildBigNatRodata` satisfies `NatVal` and reads back
identically via `Rt.readbackBig` once `.rodata` is mapped at `base`.** -/
theorem buildBigNatRodata_natVal {nats : List Nat} {mem : Memory} {base : Word}
    {n off : Nat} (hge : Rt.natLimit ≤ n)
    (hmem : (n, off) ∈ (buildBigNatRodata nats).2)
    (hmap : RodataMapped base (buildBigNatRodata nats).1.bytes mem)
    (hnonzero : base + UInt64.ofNat off ≠ 0) (sig : Sig) (fuel : Nat) :
    NatVal mem n (base + UInt64.ofNat off) ∧
      Rt.readbackBig sig fuel mem .nat (base + UInt64.ofNat off) = some (.nat n) := by
  obtain ⟨hal, hbd, hby⟩ := buildBigNatRodata_entry_bytes nats (n, off) hmem
  have ⟨hnv, _⟩ := NatVal.ofRodataLiteral hge hmap hal hnonzero hbd hby
  exact ⟨hnv, hnv.readbackBig⟩

/-! ## Section 6: `SameReadable` Readback Congruence & End-to-End Arbitrary-Precision Simulation -/

/-- **`Rt.readbackBig` depends only on readable bytes (`SameReadable`).**
Counterpart to `Rt.readback_congr` extending exact readback congruence to arbitrary-precision `Nat`s. -/
theorem readbackBig_congr {m₁ m₂ : Memory} (h : SameReadable m₁ m₂) (sig : Sig)
    (fuel : Nat) (ty : FoTy) (w : Word) :
    Rt.readbackBig sig fuel m₁ ty w = Rt.readbackBig sig fuel m₂ ty w :=
  Rt.readbackBig_congr_read64 (fun a => h.read? .w64 a) sig fuel ty w

/-- In Phase 4, the 1-instruction `natSwitch` test `w == 1` is exact for `n == 0` across ALL
arbitrary-precision `Nat` values (small immediates `< 2^63` AND canonical `LimbArray` cells `≥ 2^63`). -/
theorem natSwitchBig_isZero_iff {mem : Memory} {n : Nat} {w : Word}
    (h : NatVal mem n w) : w = 1 ↔ n = 0 :=
  h.eq_one_iff_zero

/-- Contract tying a `BigNatLitCtx` to mapped `.rodata` / `bigNatLitProc` runtime semantics:
every `≥ 2^63` entry in `bc` produces a valid `NatVal` word (and preserves `MemStep`). -/
structure BigNatLitEnv (lp : Lir.Program) (ctx : Word)
    (MemStep : Memory → Memory → Prop) (bc : BigNatLitCtx) : Prop where
  mem_refl : ∀ m, MemStep m m
  mem_trans : ∀ m₁ m₂ m₃, MemStep m₁ m₂ → MemStep m₂ m₃ → MemStep m₁ m₃
  rodata_ok : ∀ mem n addr, bc.rodataAddrs.lookup n = some addr → Rt.natLimit ≤ n →
    NatVal mem n addr
  litFn_ok : ∀ mem n fnId, bc.litFns.lookup n = some fnId → Rt.natLimit ≤ n →
    ProcSpec lp fnId ctx [] mem (fun mem' w => MemStep mem mem' ∧ NatVal mem' n w)

/-- **Evaluating an arbitrary-precision `Nat` literal via `operandBig` yields a valid `NatVal`
word (with exact `Rt.readbackBig`) or fails strictly with `FailsNoOvf` (ZERO `.natOverflow`!).** -/
theorem operandBig_nat_sim {f : FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : Memory → Memory → Prop} {sc : StrCtx} {bc : BigNatLitCtx}
    (hlenv : BigNatLitEnv lp ctx MemStep bc)
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {n : Nat} {la : Lir.Arg}
    (hrun : (operandBig f sc bc (.lit (.nat n))).run st = .ok (la, st'))
    (hC : Ext C st') (ho : Open st)
    (ρl : Lir.Env) (mem : Memory) (rest : List Lir.Frame) :
    (∃ c ρl' mem' w,
        Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) c
          (Lir.atState mem' ctx fn (off + st'.cur) st'.acc.length ρl' rest) ∧
        MemStep mem mem' ∧ la.eval ρl' = some w ∧ NatVal mem' n w ∧
        ∀ y, y < st.fresh → ρl'[y]? = ρl[y]?) ∨
    FailsNoOvf lp (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) := by
  unfold operandBig at hrun
  dsimp only at hrun
  split at hrun
  · rename_i hlt
    simp only [pure, StateT.pure, Except.pure, StateT.run, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    left
    refine ⟨0, ρl, mem, UInt64.ofNat (2 * n + 1), .refl _, hlenv.mem_refl mem, rfl, ?_, fun _ _ => rfl⟩
    exact NatVal.small (natWord_of_lt hlt)
  · rename_i hge
    have hge' : Rt.natLimit ≤ n := Nat.le_of_not_lt hge
    cases hro : bc.rodataAddrs.lookup n with
    | some addr =>
      simp only [hro, pure, StateT.pure, Except.pure, StateT.run, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      left
      exact ⟨0, ρl, mem, addr, .refl _, hlenv.mem_refl mem, rfl,
        hlenv.rodata_ok mem n addr hro hge', fun _ _ => rfl⟩
    | none =>
      simp only [hro] at hrun
      cases hfn : bc.litFns.lookup n with
      | none =>
        simp [hfn, throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.run, Functor.map, Except.map] at hrun
      | some fnId =>
        simp only [hfn, bind, StateT.bind, freshReg, emit, pure, StateT.pure, Except.pure,
          modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, modify, StateT.run,
          Except.bind, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        obtain ⟨B, _, hB, -, hbody⟩ := holds_open hH [.call [st.fresh] fnId []] (st.fresh + 1) hC ho
        have hpos : st.acc.length < B.body.size := by rw [← Array.length_toList, hbody]; simp
        have hcall : B.body[st.acc.length] = .call [st.fresh] fnId [] := by
          rw [← Array.getElem_toList (h := hpos)]
          simp only [hbody]
          rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
          simp
        have hspec := hlenv.litFn_ok mem n fnId hfn hge'
        rcases call_procSpec (rest := rest) hF hB hpos hcall rfl hspec with ⟨c, mem', w, hstar, hms, hnv⟩ | hfail
        · left
          refine ⟨c, ρl.insert st.fresh w, mem', w, ?_, hms, ?_, hnv, ?_⟩
          · simpa [List.length_cons] using hstar
          · simp [Lir.Arg.eval]
          · intro y hy
            exact Lir.env_insert_ne _ _ (Nat.ne_of_gt hy)
        · right; exact hfail

/-- **End-to-end arbitrary-precision `Nat` primitive simulation with `Rt.readbackBig` (ZERO `.natOverflow`):**
Composes `Rt.BigNat.primitiveBig_core` with `NatVal.readbackBig` under `SlowPathEnv` and `FailsNoOvf`. -/
theorem primitiveBig_sim_readback_noOvf {f : FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : Memory → Memory → Prop} {procs : BigNatProcs} {tWord fWord : Word}
    (henv : SlowPathEnv lp ctx MemStep procs tWord fWord)
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {op : Lam.Prim} {las : List Lir.Arg}
    (hrun : (primitiveBig f { bools := some (tWord, fWord), procs } x op las).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (ho : Open st) (hsup : sup ≤ st.fresh)
    (ρl : Lir.Env) (mem : Memory) (rest : List Lir.Frame)
    (ns : List Nat) (ws : List Word) (n : Nat) (sig : Sig) (fuel : Nat)
    (hargs : Lir.evalArgs ρl las = some ws)
    (hrel : ListRel (NatVal mem) ns ws)
    (hreads : ∀ la ∈ las, ArgReads sup la)
    (hsem : op.sem ns = some (.nat n)) :
    (∃ c ρl' mem' w,
        Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) c
          (Lir.atState mem' ctx fn (off + st'.cur) st'.acc.length ρl' rest) ∧
        MemStep mem mem' ∧ NatVal mem' n w ∧
        Rt.readbackBig sig fuel mem' .nat w = some (.nat n) ∧
        ρl'[x]? = some w ∧
        ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) ∨
    FailsNoOvf lp (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) := by
  have hcore := (primitiveBig_core henv hF hH hrun hC hl ho hsup).1
  rcases hcore ρl mem rest ns ws n hargs hrel hreads hsem with
    ⟨c, ρl', mem', w, hstar, hms, hnv, hrx, hpres⟩ | hfail
  · left
    exact ⟨c, ρl', mem', w, hstar, hms, hnv, hnv.readbackBig, hrx, hpres⟩
  · right; exact hfail

/-- **End-to-end arbitrary-precision `Nat.succ` peel simulation with `Rt.readbackBig` (ZERO `.natOverflow`):**
Composes `Rt.BigNat.natSuccPeelBig_core` with `NatVal.readbackBig` under `FailsNoOvf`. -/
theorem projBig_natSucc_sim_readback_noOvf {f : FunId} {lp : Lir.Program} {ctx : Word}
    {MemStep : Memory → Memory → Prop} {procs : BigNatProcs}
    (hrefl : ∀ m, MemStep m m)
    (hpred : SlowNatUnSpec lp ctx MemStep procs.pred (· - 1))
    {sup fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x y : VReg}
    (hrun : (natSuccPeelBig procs x y).run st = .ok ((), st'))
    (hC : Ext C st') (hl : Labels st) (hsup : sup ≤ st.fresh) (hy : y < sup)
    (ρl : Lir.Env) (mem : Memory) (rest : List Lir.Frame)
    (n : Nat) (wy : Word) (sig : Sig) (fuel : Nat)
    (hry : ρl[y]? = some wy) (hnv : NatVal mem (n + 1) wy) :
    (∃ c ρl' mem' w,
        Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) c
          (Lir.atState mem' ctx fn (off + st'.cur) st'.acc.length ρl' rest) ∧
        MemStep mem mem' ∧ NatVal mem' n w ∧
        Rt.readbackBig sig fuel mem' .nat w = some (.nat n) ∧
        ρl'[x]? = some w ∧
        ∀ z, z < sup → z ≠ x → ρl'[z]? = ρl[z]?) ∨
    FailsNoOvf lp (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) := by
  have hcore := natSuccPeelBig_core hrefl hpred hF hH hrun hC hl hsup
  have hargs : Lir.evalArgs ρl [.v y] = some [wy] := by
    simp [Lir.evalArgs, Lir.Arg.eval, hry]
  have hrel : ListRel (NatVal mem) [n + 1] [wy] := .cons hnv .nil
  have hreads : ∀ la ∈ ([Lir.Arg.v y] : List Lir.Arg), ArgReads sup la := by
    intro la hla; simp only [List.mem_singleton] at hla; subst hla
    intro z hz; cases hz; exact hy
  have hsem : Lam.Prim.natPred.sem [n + 1] = some (.nat n) := by
    simp [Lam.Prim.sem, Src.PrimOp.eval2]
  rcases hcore ρl mem rest [n + 1] [wy] n hargs hrel hreads hsem with
    ⟨c, ρl', mem', w, hstar, hms, hnv', hrx, hpres⟩ | hfail
  · left
    exact ⟨c, ρl', mem', w, hstar, hms, hnv', hnv'.readbackBig, hrx, hpres⟩
  · right; exact hfail

end IxCC.Rt.BigNat
