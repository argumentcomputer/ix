import IxCC.Xv.Validate.Proof.Inst

/-!
# What an accepted allocation looks like

Unfolding a successful `Validate.program` and `Alloc.applyProgram`: every
function is validated (`FuncOk`: parameters distinct, the entry certificate
below the convention's state, every block checked) and applied (`ApplyOk`),
block by block, with block `L`'s certificate and parameters in the
function's `BlockInfo`. `BlockRest` is the invariant of a running frame: the
rest of its block, from Xv position `i` with abstract state `a`, is what the
validator accepted, and the Xl block from position `j` is its image.
-/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg Word Env Operand)
open IxCC.Xv.Alloc (Edit Output BlockOut takeAt editsOrdered interleave applyBlock applyBlocks)
open IxCC.Xv

/-! ## Functions -/

/-- The context `func` checks a function's blocks in. -/
def funcCtx (env : Xl.Env) (f : Func VReg) (o : Output) : Ctx :=
  { env, numSlots := o.numSlots, stackParams := f.params.length - Xl.nArgRegs }

/-- The certificates and parameters `func` checks edges against. -/
def funcInfo (f : Func VReg) (o : Output) : BlockInfo := blockInfo f.blocks.toList o.blocks

set_option linter.unusedSimpArgs false in
theorem checkBlocks_ok {c : Ctx} {fi : Nat} {info : BlockInfo} :
    ∀ {bs : List (Block VReg)} {os : List BlockOut} {l : Nat}, checkBlocks c fi info bs os l = .ok () →
      bs.length = os.length ∧ ∀ (k : Nat) b bo, bs[k]? = some b → os[k]? = some bo → checkBlock c info b bo = .ok ()
  | [], [], _, _ => ⟨rfl, by simp⟩
  | [], _ :: _, _, h => by simp [checkBlocks, throw, throwThe, MonadExceptOf.throw] at h
  | _ :: _, [], _, h => by simp [checkBlocks, throw, throwThe, MonadExceptOf.throw] at h
  | b :: bs, o :: os, l, h => by
      simp only [checkBlocks, bind, Except.bind] at h
      cases hb : checkBlock c info b o with
      | error e => simp [hb, throw, throwThe, MonadExceptOf.throw] at h
      | ok u =>
        simp only [hb] at h
        obtain ⟨hl, ih⟩ := checkBlocks_ok h
        refine ⟨by simp [hl], fun k b' bo hb' ho => ?_⟩
        cases k with
        | zero => simp at hb' ho; subst hb' ho; exact hb
        | succ k => exact ih k b' bo (by simpa using hb') (by simpa using ho)

/-- What `Validate.func` establishes. -/
structure FuncOk (env : Xl.Env) (f : Func VReg) (o : Output) : Prop where
  len : f.blocks.size = o.blocks.length
  params : f.params.Nodup
  entry : ∃ o0 rest, o.blocks = o0 :: rest ∧ (AState.ofList o0.cert).le (entryState f.params) = true
  blocks : ∀ (L : Nat) b bo, f.blocks[L]? = some b → o.blocks[L]? = some bo →
    checkBlock (funcCtx env f o) (funcInfo f o) b bo = .ok ()

set_option linter.unusedSimpArgs false in
theorem func_ok {env : Xl.Env} {fi : Nat} {f : Func VReg} {o : Output} (h : func env fi f o = .ok ()) :
    FuncOk env f o := by
  unfold func at h
  simp only [bind, Except.bind] at h
  cases h₀ : sizeOk f o <;>
    simp only [h₀, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  cases h₁ : (f.blocks.toList.length == o.blocks.length) <;>
    simp only [h₁, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  cases h₂ : nodup f.params <;>
    simp only [h₂, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  cases hb : o.blocks with
  | nil => simp [hb] at h
  | cons o0 rest =>
    simp only [hb] at h
    cases h₃ : (AState.ofList o0.cert).le (entryState f.params) <;>
      simp only [h₃, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
    obtain ⟨-, hblocks⟩ := checkBlocks_ok h
    refine ⟨?_, nodup_iff.1 h₂, ⟨o0, rest, hb, h₃⟩, ?_⟩
    · simp only [beq_iff_eq, Array.length_toList] at h₁; rw [h₁, hb]
    · intro L b bo hb' ho
      rw [← hb] at hblocks
      exact hblocks L b bo (by simpa using hb') ho

/-- The block information of a validated function. -/
theorem blockInfo_find {bs : List (Block VReg)} {os : List BlockOut} (_hl : bs.length = os.length)
    {L : Nat} {b : Block VReg} {bo : BlockOut} (hb : bs[L]? = some b) (ho : os[L]? = some bo) :
    (blockInfo bs os).find? L = some (b.params, AState.ofList bo.cert) := by
  unfold blockInfo
  have key : ∀ (ps : List ((Block VReg × BlockOut) × Nat)) (m : BlockInfo),
      (ps.map (·.2)).Nodup →
      ((ps.foldl (fun m (p : (Block VReg × BlockOut) × Nat) =>
          m.insert p.2 (p.1.1.params, AState.ofList p.1.2.cert)) m).find? L =
        match ps.find? (·.2 == L) with
        | some p => some (p.1.1.params, AState.ofList p.1.2.cert)
        | none => m.find? L) := by
    intro ps
    induction ps with
    | nil => intro m _; rfl
    | cons p ps ih =>
      intro m hn
      simp only [List.map_cons, List.nodup_cons] at hn
      simp only [List.foldl_cons, List.find?_cons]
      rw [ih _ hn.2]
      by_cases e : p.2 = L
      · subst e
        have : ps.find? (·.2 == p.2) = none := by
          rw [List.find?_eq_none]
          intro q hq e'
          simp only [beq_iff_eq] at e'
          exact hn.1 (e' ▸ List.mem_map_of_mem hq)
        simp [this, NatMap.find?_insert]
      · have : (p.2 == L) = false := by simpa using e
        simp only [this]
        cases ps.find? (·.2 == L) <;> simp [NatMap.find?_insert, Ne.symm e]
  have hz : ((bs.zip os).zipIdx.map (·.2)).Nodup := by
    rw [List.zipIdx_map_snd]; exact List.nodup_range'
  rw [key _ _ hz]
  have hmem : ((b, bo), L) ∈ (bs.zip os).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getElem?_zip_eq_some, hb, ho]
  have hfind : (bs.zip os).zipIdx.find? (·.2 == L) = some ((b, bo), L) := by
    have hex : ((bs.zip os).zipIdx.find? (·.2 == L)).isSome := List.find?_isSome.2 ⟨((b, bo), L), hmem, beq_self_eq_true L⟩
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hex
    have hqm := List.mem_of_find?_eq_some hq
    have hqL : q.2 = L := by simpa using List.find?_some hq
    have hq' : q = ((b, bo), L) := by
      rcases q with ⟨⟨b', bo'⟩, L'⟩
      simp only at hqL
      subst hqL
      rw [List.mem_zipIdx_iff_getElem?] at hqm
      simp [List.getElem?_zip_eq_some, hb, ho] at hqm
      obtain ⟨rfl, rfl⟩ := hqm
      rfl
    rw [hq, hq']
  rw [hfind]

/-! ## Applying -/

theorem applyBlocks_ok :
    ∀ {bs : List (Block VReg)} {os : List BlockOut} {l : Nat} {gs : List (Block Loc)},
      applyBlocks bs os l = .ok gs →
      gs.length = bs.length ∧ ∀ (k : Nat) b bo, bs[k]? = some b → os[k]? = some bo →
        ∃ bl, gs[k]? = some bl ∧ applyBlock b bo = .ok bl
  | [], [], _, gs, h => by simp [applyBlocks, pure, Except.pure] at h; subst h; simp
  | [], _ :: _, _, _, h => by simp [applyBlocks, throw, throwThe, MonadExceptOf.throw] at h
  | _ :: _, [], _, _, h => by simp [applyBlocks, throw, throwThe, MonadExceptOf.throw] at h
  | b :: bs, o :: os, l, gs, h => by
      simp only [applyBlocks, bind, Except.bind] at h
      cases hb : applyBlock b o with
      | error e => simp [hb, throw, throwThe, MonadExceptOf.throw] at h
      | ok x =>
        simp only [hb] at h
        cases hr : applyBlocks bs os (l + 1) with
        | error e => simp [hr, pure, Except.pure] at h
        | ok xs =>
          simp only [hr, pure, Except.pure, Except.ok.injEq] at h
          subst h
          obtain ⟨hl, ih⟩ := applyBlocks_ok hr
          refine ⟨by simp [hl], fun k b' bo hb' ho => ?_⟩
          cases k with
          | zero => simp at hb' ho ⊢; subst hb' ho; exact hb
          | succ k => simpa using ih k b' bo (by simpa using hb') (by simpa using ho)

/-- What `Alloc.apply` establishes. -/
structure ApplyOk (f : Func VReg) (o : Output) (g : Func Loc) : Prop where
  params : g.params = (List.range f.params.length).map Xl.paramLoc
  size : g.blocks.size = f.blocks.size
  blocks : ∀ (L : Nat) b bo, f.blocks[L]? = some b → o.blocks[L]? = some bo →
    ∃ bl, g.blocks[L]? = some bl ∧ applyBlock b bo = .ok bl

theorem apply_ok {f : Func VReg} {o : Output} {g : Func Loc} (h : Alloc.apply f o = .ok g) :
    ApplyOk f o g := by
  unfold Alloc.apply at h
  simp only [bind, Except.bind] at h
  cases hb : applyBlocks f.blocks.toList o.blocks 0 with
  | error e => simp [hb] at h
  | ok gs =>
    simp only [hb, pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hblocks⟩ := applyBlocks_ok hb
    refine ⟨rfl, by simp [hl], fun L b bo hb' ho => ?_⟩
    obtain ⟨bl, hbl, ha⟩ := hblocks L b bo (by simpa using hb') ho
    exact ⟨bl, by simpa using hbl, ha⟩

/-- What `Alloc.applyBlock` establishes. -/
structure ApplyBlockOk (b : Block VReg) (bo : BlockOut) (bl : Block Loc) : Prop where
  params : bl.params = []
  term : b.term.substitute bo.termLocs (b.term.edges.map fun _ => []) = some bl.term
  body : ∃ insts left, interleave b.body.toList bo.locs bo.edits 0 = some (insts, left) ∧
    (takeAt b.body.size left).2 = [] ∧ bl.body.toList = insts ++ (takeAt b.body.size left).1.map Edit.toInst

set_option linter.unusedSimpArgs false in
theorem applyBlock_ok {b : Block VReg} {bo : BlockOut} {bl : Block Loc} (h : applyBlock b bo = .ok bl) :
    ApplyBlockOk b bo bl := by
  unfold applyBlock at h
  simp only [bind, Except.bind] at h
  cases h₁ : editsOrdered b.body.toList.length bo.edits 0 <;>
    simp only [h₁, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  cases hi : interleave b.body.toList bo.locs bo.edits 0 with
  | none => simp [hi, throw, throwThe, MonadExceptOf.throw] at h
  | some r =>
    obtain ⟨insts, left⟩ := r
    simp only [hi] at h
    cases h₂ : (takeAt b.body.toList.length left).2.isEmpty <;>
      simp only [h₂, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
    cases ht : b.term.substitute bo.termLocs (b.term.edges.map fun _ => []) with
    | none => simp [ht, throw, throwThe, MonadExceptOf.throw] at h
    | some t =>
      simp only [ht, Except.ok.injEq] at h
      subst h
      refine ⟨rfl, ht, insts, left, hi, by simpa using h₂, ?_⟩
      simp

/-! ## Programs -/

theorem program_go_ok {env : Xl.Env} :
    ∀ {fs : List (Func VReg)} {os : List Output} {i : Nat}, program.go env fs os i = .ok () →
      fs.length = os.length ∧ ∀ (k : Nat) f, fs[k]? = some f → ∃ o, os[k]? = some o ∧ func env (i + k) f o = .ok ()
  | [], [], _, _ => ⟨rfl, by simp⟩
  | [], _ :: _, _, h => by simp [program.go, throw, throwThe, MonadExceptOf.throw] at h
  | _ :: _, [], _, h => by simp [program.go, throw, throwThe, MonadExceptOf.throw] at h
  | f :: fs, o :: os, i, h => by
      simp only [program.go, bind, Except.bind] at h
      cases hf : func env i f o with
      | error e => simp [hf] at h
      | ok u =>
        simp only [hf] at h
        obtain ⟨hl, ih⟩ := program_go_ok h
        refine ⟨by simp [hl], fun k f' hf' => ?_⟩
        cases k with
        | zero => simp at hf'; subst hf'; exact ⟨o, rfl, hf⟩
        | succ k =>
          obtain ⟨o', ho', hf''⟩ := ih k f' (by simpa using hf')
          exact ⟨o', by simpa using ho', by rw [show i + (k + 1) = i + 1 + k by omega]; exact hf''⟩

theorem applyProgram_go_ok :
    ∀ {fs : List (Func VReg)} {os : List Output} {i : Nat} {gs : List (Func Loc)},
      Alloc.applyProgram.go fs os i = .ok gs →
      gs.length = fs.length ∧ ∀ (k : Nat) f o, fs[k]? = some f → os[k]? = some o →
        ∃ g, gs[k]? = some g ∧ Alloc.apply f o = .ok g
  | [], [], _, gs, h => by simp [Alloc.applyProgram.go, pure, Except.pure] at h; subst h; simp
  | [], _ :: _, _, _, h => by simp [Alloc.applyProgram.go, throw, throwThe, MonadExceptOf.throw] at h
  | _ :: _, [], _, _, h => by simp [Alloc.applyProgram.go, throw, throwThe, MonadExceptOf.throw] at h
  | f :: fs, o :: os, i, gs, h => by
      simp only [Alloc.applyProgram.go, bind, Except.bind] at h
      cases hf : Alloc.apply f o with
      | error e => simp [hf, throw, throwThe, MonadExceptOf.throw] at h
      | ok g =>
        simp only [hf] at h
        cases hr : Alloc.applyProgram.go fs os (i + 1) with
        | error e => simp [hr, pure, Except.pure] at h
        | ok xs =>
          simp only [hr, pure, Except.pure, Except.ok.injEq] at h
          subst h
          obtain ⟨hl, ih⟩ := applyProgram_go_ok hr
          refine ⟨by simp [hl], fun k f' o' hf' ho' => ?_⟩
          cases k with
          | zero => simp at hf' ho' ⊢; subst hf' ho'; exact hf
          | succ k => simpa using ih k f' o' (by simpa using hf') (by simpa using ho')

/-- An accepted allocation of a program: every function validated and
applied. -/
structure Accepted (env : Xl.Env) (p : VProgram) (outs : List Output) (q : LProgram) : Prop where
  main : q.main = p.main
  size : q.funcs.size = p.funcs.size
  funcs : ∀ (fi : Nat) f, p.funcs[fi]? = some f → ∃ o g, outs[fi]? = some o ∧ q.funcs[fi]? = some g ∧
    func env fi f o = .ok () ∧ Alloc.apply f o = .ok g

theorem accepted_of_run {env : Xl.Env} {p : VProgram} {outs : List Output} {q : LProgram}
    (h : Validate.run env p outs = .ok q) : Accepted env p outs q := by
  unfold Validate.run at h
  cases hp : program env p outs with
  | error e => simp [hp, throw, throwThe, MonadExceptOf.throw] at h
  | ok u =>
    simp only [hp] at h
    unfold Alloc.applyProgram at h
    simp only [bind, Except.bind] at h
    cases ha : Alloc.applyProgram.go p.funcs.toList outs 0 with
    | error e => simp [ha] at h
    | ok gs =>
      simp only [ha, pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hl₁, hf₁⟩ := program_go_ok hp
      obtain ⟨hl₂, hf₂⟩ := applyProgram_go_ok ha
      refine ⟨rfl, by simp [hl₂], fun fi f hf => ?_⟩
      obtain ⟨o, ho, hv⟩ := hf₁ fi f (by simpa using hf)
      obtain ⟨g, hg, happ⟩ := hf₂ fi f o (by simpa using hf) ho
      exact ⟨o, g, ho, by simpa using hg, by simpa using hv, happ⟩

/-! ## The rest of a block -/

theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {e : Except ε α} {a : α} (h : e.mapError f = .ok a) :
    e = .ok a := by
  cases e <;> simp_all [Except.mapError]

set_option linter.unusedSimpArgs false in
theorem checkBlock_ok {c : Ctx} {info : BlockInfo} {b : Block VReg} {bo : BlockOut}
    (h : checkBlock c info b bo = .ok ()) :
    b.params.Nodup ∧ ∃ aEnd left, walkBody c (AState.ofList bo.cert) b.body.toList bo.locs bo.edits 0 =
      .ok (aEnd, left) ∧ (takeAt b.body.size left).2 = [] ∧
      ∃ a₁, stepEdits c aEnd (takeAt b.body.size left).1 = .ok a₁ ∧
      ∃ a₂, stepTerm c a₁ b.term bo.termLocs = .ok a₂ ∧ checkEdges info a₂ b.term.edges = none := by
  unfold checkBlock at h
  simp only [bind, Except.bind] at h
  cases h₁ : nodup b.params <;>
    simp only [h₁, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  cases h₂ : editsOrdered b.body.toList.length bo.edits 0 <;>
    simp only [h₂, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  obtain ⟨w, hw⟩ : ∃ w, walkBody c (AState.ofList bo.cert) b.body.toList bo.locs bo.edits 0 = w := ⟨_, rfl⟩
  rw [hw] at h
  cases w with
  | error e => simp at h
  | ok r =>
    obtain ⟨aEnd, left⟩ := r
    simp only at h
    simp only [Array.length_toList] at h
    cases h₃ : (takeAt b.body.size left).2.isEmpty <;>
      simp only [h₃, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
    cases he : stepEdits c aEnd (takeAt b.body.size left).1 with
    | error e => simp [he, Except.mapError] at h
    | ok a₁ =>
      simp only [he, Except.mapError] at h
      cases ht : stepTerm c a₁ b.term bo.termLocs with
      | error e => simp [ht] at h
      | ok a₂ =>
        simp only [ht] at h
        cases hc : checkEdges info a₂ b.term.edges with
        | some code => simp [hc] at h
        | none =>
          exact ⟨nodup_iff.1 h₁, aEnd, left, hw, by simpa using h₃, a₁, he, a₂, ht, hc⟩

theorem walk_interleave {c : Ctx} :
    ∀ {insts : List (Inst VReg)} {lss : List (List Loc)} {es : List (Nat × Edit)} {i : Nat} {a aEnd : AState}
      {left left' : List (Nat × Edit)} {xs : List (Inst Loc)},
      walkBody c a insts lss es i = .ok (aEnd, left) → interleave insts lss es i = some (xs, left') →
      left = left'
  | [], [], es, i, a, aEnd, left, left', xs, hw, hi => by
      simp [walkBody, pure, Except.pure] at hw
      simp [interleave] at hi
      rw [← hw.2, ← hi.2]
  | [], _ :: _, _, _, _, _, _, _, _, _, hi => by simp [interleave] at hi
  | _ :: _, [], _, _, _, _, _, _, _, _, hi => by simp [interleave] at hi
  | inst :: insts, ls :: lss, es, i, a, aEnd, left, left', xs, hw, hi => by
      simp only [walkBody, bind, Except.bind] at hw
      cases he : (stepEdits c a (takeAt i es).1).mapError (i, ·) with
      | error e => simp [he] at hw
      | ok a₁ =>
        simp only [he] at hw
        cases hs : (stepInst c a₁ inst ls).mapError (i, ·) with
        | error e => simp [hs] at hw
        | ok a₂ =>
          simp only [hs] at hw
          simp only [interleave, Option.bind_eq_bind, Option.bind_eq_some_iff] at hi
          obtain ⟨x, -, ⟨rest, l'⟩, hr, he'⟩ := hi
          simp only [pure, Option.some.injEq, Prod.mk.injEq] at he'
          rw [← he'.2]
          exact walk_interleave hw hr

/-- The invariant of a running frame: the rest of its block from Xv
position `i` with abstract state `a` is what the validator accepted, and the
Xl block from position `j` is its image. -/
structure BlockRest (c : Ctx) (info : BlockInfo) (b : Block VReg) (bo : BlockOut) (bl : Block Loc)
    (i j : Nat) (a : AState) : Prop where
  pos : i ≤ b.body.size
  rest : ∃ lss es aEnd left xs,
    walkBody c a (b.body.toList.drop i) lss es i = .ok (aEnd, left) ∧
    interleave (b.body.toList.drop i) lss es i = some (xs, left) ∧
    bl.body.toList.drop j = xs ++ (takeAt b.body.size left).1.map Edit.toInst ∧
    (takeAt b.body.size left).2 = [] ∧
    ∃ a₁, stepEdits c aEnd (takeAt b.body.size left).1 = .ok a₁ ∧
    ∃ a₂, stepTerm c a₁ b.term bo.termLocs = .ok a₂ ∧ checkEdges info a₂ b.term.edges = none
  term : b.term.substitute bo.termLocs (b.term.edges.map fun _ => []) = some bl.term

theorem BlockRest.start {c : Ctx} {info : BlockInfo} {b : Block VReg} {bo : BlockOut} {bl : Block Loc}
    (hc : checkBlock c info b bo = .ok ()) (ha : applyBlock b bo = .ok bl) :
    BlockRest c info b bo bl 0 0 (AState.ofList bo.cert) := by
  obtain ⟨-, aEnd, left, hw, hrest, a₁, he, a₂, ht, hce⟩ := checkBlock_ok hc
  obtain ⟨-, hterm, insts, left', hi, -, hbody⟩ := applyBlock_ok ha
  have := walk_interleave hw hi
  subst this
  exact ⟨Nat.zero_le _, ⟨bo.locs, bo.edits, aEnd, left, insts, by simpa using hw, by simpa using hi,
    by simpa using hbody, hrest, a₁, he, a₂, ht, hce⟩, hterm⟩

theorem BlockRest.inst {c : Ctx} {info : BlockInfo} {b : Block VReg} {bo : BlockOut} {bl : Block Loc}
    {i j : Nat} {a : AState} (h : BlockRest c info b bo bl i j a) {inst : Inst VReg}
    {insts : List (Inst VReg)} (hi : b.body.toList.drop i = inst :: insts) :
    ∃ ls now x a₁ a₂, bl.body.toList.drop j = now.map Edit.toInst ++ x :: bl.body.toList.drop
        (j + now.length + 1) ∧
      stepEdits c a now = .ok a₁ ∧ stepInst c a₁ inst ls = .ok a₂ ∧ inst.substitute ls = some x ∧
      BlockRest c info b bo bl (i + 1) (j + now.length + 1) a₂ := by
  obtain ⟨hpos, ⟨lss, es, aEnd, left, xs, hw, hint, hdrop, hrest, a₁', he', a₂', ht', hce'⟩, hterm⟩ := h
  rw [hi] at hw hint
  cases lss with
  | nil => simp [walkBody, throw, throwThe, MonadExceptOf.throw] at hw
  | cons ls lss =>
  simp only [walkBody, bind, Except.bind] at hw
  cases he : stepEdits c a (takeAt i es).1 with
  | error e => simp [he, Except.mapError] at hw
  | ok a₁ =>
  simp only [he, Except.mapError] at hw
  cases hs : stepInst c a₁ inst ls with
  | error e => simp [hs] at hw
  | ok a₂ =>
  simp only [hs] at hw
  simp only [interleave, Option.bind_eq_bind, Option.bind_eq_some_iff] at hint
  obtain ⟨x, hx, ⟨rest, l'⟩, hr, he''⟩ := hint
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at he''
  obtain ⟨hxs, hl'⟩ := he''
  rw [hl'] at hr
  rw [← hxs] at hdrop
  have hlen : i < b.body.size := by
    have : (b.body.toList.drop i).length = b.body.size - i := by simp
    rw [hi] at this
    simp at this
    omega
  have hdrop' : b.body.toList.drop (i + 1) = insts := by
    rw [← List.drop_drop, hi]; rfl
  have hj : bl.body.toList.drop (j + (takeAt i es).1.length + 1) = rest ++
      (takeAt b.body.size left).1.map Edit.toInst := by
    rw [show j + (takeAt i es).1.length + 1 = j + ((takeAt i es).1.map Edit.toInst ++ [x]).length by
      simp; omega, ← List.drop_drop, hdrop]
    rw [List.append_assoc, List.drop_append]
    simp
  refine ⟨ls, (takeAt i es).1, x, a₁, a₂, ?_, he, hs, hx, ⟨by omega, ?_, hterm⟩⟩
  · rw [hdrop, hj]; simp
  · refine ⟨lss, (takeAt i es).2, aEnd, left, rest, ?_, ?_, hj, hrest, a₁', he', a₂', ht', hce'⟩
    · rw [hdrop']; exact hw
    · rw [hdrop']; exact hr

theorem BlockRest.atTerm {c : Ctx} {info : BlockInfo} {b : Block VReg} {bo : BlockOut} {bl : Block Loc}
    {i j : Nat} {a : AState} (h : BlockRest c info b bo bl i j a) (hi : b.body.size ≤ i) :
    ∃ now a₁ a₂, bl.body.toList.drop j = now.map Edit.toInst ∧ stepEdits c a now = .ok a₁ ∧
      stepTerm c a₁ b.term bo.termLocs = .ok a₂ ∧ checkEdges info a₂ b.term.edges = none := by
  obtain ⟨hpos, ⟨lss, es, aEnd, left, xs, hw, hint, hdrop, hrest, a₁, he, a₂, ht, hce⟩, hterm⟩ := h
  have hd : b.body.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hi)
  rw [hd] at hw hint
  cases lss with
  | cons => simp [walkBody, throw, throwThe, MonadExceptOf.throw] at hw
  | nil =>
    simp [walkBody, pure, Except.pure] at hw
    simp [interleave] at hint
    obtain ⟨ha, hl⟩ := hw
    obtain ⟨hx, hl'⟩ := hint
    subst ha
    rw [hx, List.nil_append] at hdrop
    refine ⟨(takeAt b.body.size left).1, a₁, a₂, hdrop, he, ht, hce⟩

end IxCC.Xv.Validate

