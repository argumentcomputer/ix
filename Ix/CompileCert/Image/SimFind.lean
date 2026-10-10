import Ix.CompileCert.Image.SimTel
import Batteries.Tactic.OpenPrivate

/-!
# M7 L2a-syn: the construction's analyses from shifted counters

The analyses that open binders (`elimMotiveTypes`, `findElim`, `analyzeLeanMinor`,
`analyzeCanonMinor`) give the same answers from a shifted counter: indices, names and levels
equal, terms renamed.
-/

open private Ix.Compile.Canon.substLevels.go from Ix.Compile.Canon.Expr

namespace Ix.CompileCert.Img

open Ix (Name Level Expr ConstantInfo InductiveVal RecursorVal)
open Ix.Compile.Image (GenM GenState freshName Local telescope LCtx Elim LeanMinor)

section
variable {s0 d B : Nat}

/-- Arrays of expressions of the two runs. -/
def ARE (s0 d B : Nat) (xs ys : Array Expr) : Prop :=
  ARen (shift s0 d) xs ys ∧ LFv (FreshBelow B) xs.toList

theorem ARE.size {xs ys : Array Expr} (h : ARE s0 d B xs ys) : xs.size = ys.size := h.1.size

theorem ARE.get {xs ys : Array Expr} (h : ARE s0 d B xs ys) (i : Nat) (h1 : i < xs.size)
    (h2 : i < ys.size) : RE s0 d B xs[i] ys[i] :=
  ⟨h.1.get i h1 h2, h.2 _ (by simp)⟩

theorem RE.ren {a b : Expr} (h : RE s0 d B a b) : Ren (shift s0 d) a b := h.1

/-- The context of the image construction: its free variables are fresh names below `s0`. -/
def CtxOK (s0 : Nat) (c : LCtx) : Prop :=
  (∀ l ∈ c.ps ++ c.ms ++ c.mins, FreshBelow s0 l.fvar ∧ FvAll (FreshBelow s0) l.type) ∧
    ∀ ty ∈ c.motiveTys, FvAll (FreshBelow s0) ty

theorem shift_fix {n : Name} (h : FreshBelow s0 n) : shift s0 d n = n := by
  obtain ⟨i, hi, rfl⟩ := h
  rw [shift_fresh]; simp only [show ¬ (s0 ≤ i) by omega, ↓reduceIte]

theorem RE.refl {e : Expr} (h : FvAll (FreshBelow s0) e) (hB : s0 ≤ B) : RE s0 d B e e :=
  ⟨Ren.refl_of (FvAll.mono (fun _ hn => shift_fix hn) h),
    FvAll.mono (fun _ hn => FreshBelow.mono hB hn) h⟩

theorem RLs.refl {xs : Array Local} (h : ∀ l ∈ xs, FreshBelow s0 l.fvar ∧ FvAll (FreshBelow s0) l.type)
    (hB : s0 ≤ B) : RLs s0 d B xs xs := by
  refine ⟨rfl, fun i h1 _ => ?_⟩
  obtain ⟨hf, ht⟩ := h _ (Array.getElem_mem h1)
  exact ⟨⟨(shift_fix (d := d) hf).symm, rfl, (RE.refl (d := d) ht hB).1, rfl⟩, FreshBelow.mono hB hf,
    (RE.refl (d := d) ht hB).2⟩

theorem CtxOK.ps {c : LCtx} (h : CtxOK s0 c) (hB : s0 ≤ B) : RLs s0 d B c.ps c.ps :=
  RLs.refl (fun l hl => h.1 l (by simp [hl])) hB
theorem CtxOK.ms {c : LCtx} (h : CtxOK s0 c) (hB : s0 ≤ B) : RLs s0 d B c.ms c.ms :=
  RLs.refl (fun l hl => h.1 l (by simp [hl])) hB
theorem CtxOK.mins {c : LCtx} (h : CtxOK s0 c) (hB : s0 ≤ B) : RLs s0 d B c.mins c.mins :=
  RLs.refl (fun l hl => h.1 l (by simp [hl])) hB

/-- The context of the two runs: its locals and motive types related to themselves (from `CtxOK`
when they are fresh names below `s0`; at `d = 0` whenever they are fresh names below `B`). -/
def CtxRE (s0 d B : Nat) (c : LCtx) : Prop :=
  (∀ l ∈ c.ps ++ c.ms ++ c.mins, shift s0 d l.fvar = l.fvar ∧ FreshBelow B l.fvar ∧
    RE s0 d B l.type l.type) ∧ ∀ ty ∈ c.motiveTys, RE s0 d B ty ty

theorem CtxOK.re {c : LCtx} (h : CtxOK s0 c) (hB : s0 ≤ B) : CtxRE s0 d B c :=
  ⟨fun l hl => ⟨shift_fix (h.1 l hl).1, FreshBelow.mono hB (h.1 l hl).1, RE.refl (h.1 l hl).2 hB⟩,
    fun ty hty => RE.refl (h.2 ty hty) hB⟩

theorem RLs.refl' {xs : Array Local}
    (h : ∀ l ∈ xs, shift s0 d l.fvar = l.fvar ∧ FreshBelow B l.fvar ∧ RE s0 d B l.type l.type) :
    RLs s0 d B xs xs := by
  refine ⟨rfl, fun i h1 _ => ?_⟩
  obtain ⟨hf, hb, ht⟩ := h _ (Array.getElem_mem h1)
  exact ⟨⟨hf.symm, rfl, ht.1, rfl⟩, hb, ht.2⟩

theorem CtxRE.ps {c : LCtx} (h : CtxRE s0 d B c) : RLs s0 d B c.ps c.ps :=
  RLs.refl' (fun l hl => h.1 l (by simp [hl]))
theorem CtxRE.ms {c : LCtx} (h : CtxRE s0 d B c) : RLs s0 d B c.ms c.ms :=
  RLs.refl' (fun l hl => h.1 l (by simp [hl]))
theorem CtxRE.mins {c : LCtx} (h : CtxRE s0 d B c) : RLs s0 d B c.mins c.mins :=
  RLs.refl' (fun l hl => h.1 l (by simp [hl]))

theorem getAppFn_fv {e : Expr} (h : FvAll (FreshBelow B) e) :
    FvAll (FreshBelow B) (Ix.Compile.Image.getAppFn e) := (getAppFnArgs_fv h).1

theorem appArg?_rel {a b : Expr} (h : RE s0 d B a b) :
    match Ix.Compile.Image.appArg? a, Ix.Compile.Image.appArg? b with
    | some x, some y => RE s0 d B x y
    | none, none => True
    | _, _ => False := by
  obtain ⟨hr, hf⟩ := h
  cases hr
  case app _ _ h1 h2 => exact ⟨h2, hf.2⟩
  all_goals trivial

/-! ## The analyses -/

theorem mono_analyzeLeanMinor (ms : Array Local) (ty : Expr) :
    Mono (Ix.Compile.Image.analyzeLeanMinor ms ty) := by
  unfold Ix.Compile.Image.analyzeLeanMinor
  refine Mono.bind (mono_telescope _ _) fun p => ?_
  obtain ⟨_, concl⟩ := p
  simp only
  split
  · split
    · split
      · exact Mono.pure _
      · exact Mono.throw _
    · exact Mono.throw _
  · exact Mono.throw _

theorem sim_analyzeLeanMinor (hok : InjOn (shift s0 d) (FreshBelow B)) {ms ms' : Array Local}
    (hms : RLs s0 d B ms ms') {ty ty' : Expr} (hty : RE s0 d B ty ty') :
    Sim s0 d B (fun (a b : LeanMinor) => a.motive = b.motive ∧ a.ctor = b.ctor)
      (Ix.Compile.Image.analyzeLeanMinor ms ty) (Ix.Compile.Image.analyzeLeanMinor ms' ty') := by
  have hi := hok
  unfold Ix.Compile.Image.analyzeLeanMinor
  refine Sim.bind (sim_telescope' hok hty) (fun p q hpq => ?_) (fun p => ?_)
  · obtain ⟨_, concl⟩ := p
    obtain ⟨_, concl'⟩ := q
    obtain ⟨-, hc⟩ := hpq
    simp only at hc ⊢
    rw [fvarIdx?_ren hi hms.lsRen (fun l hl => (hms.fv l hl).1) (getAppFn_ren hc.1) (getAppFn_fv hc.2)]
    cases Ix.Compile.Image.fvarIdx? ms (Ix.Compile.Image.getAppFn concl) with
    | none => exact Sim.throw _
    | some m =>
      simp only
      have ha := appArg?_rel hc
      revert ha
      cases Ix.Compile.Image.appArg? concl <;> cases Ix.Compile.Image.appArg? concl' <;>
        simp only [false_implies, true_implies]
      · exact Sim.throw _
      · intro ha
        rw [headConst?_ren ha.1]
        cases Ix.Compile.Image.headConst? _ with
        | none => exact Sim.throw _
        | some p => exact Sim.pure ⟨rfl, rfl⟩
  · obtain ⟨_, concl⟩ := p
    simp only
    split
    · split
      · split
        · exact Mono.pure _
        · exact Mono.throw _
      · exact Mono.throw _
    · exact Mono.throw _

theorem RLs.idx_eq (hok : InjOn (shift s0 d) (FreshBelow B)) {xs ys : Array Local} (h : RLs s0 d B xs ys) {e e' : Expr}
    (he : RE s0 d B e e') :
    Ix.Compile.Image.fvarIdx? ys (Ix.Compile.Image.getAppFn e') =
      Ix.Compile.Image.fvarIdx? xs (Ix.Compile.Image.getAppFn e) :=
  fvarIdx?_ren hok h.lsRen (fun l hl => (h.fv l hl).1) (getAppFn_ren he.1)
    (getAppFn_fv he.2)

theorem mono_analyzeCanonMinor (const? : Name → Option ConstantInfo) (ms : Array Local) (ty : Expr) :
    Mono (Ix.Compile.Image.analyzeCanonMinor const? ms ty) := by
  unfold Ix.Compile.Image.analyzeCanonMinor
  refine Mono.bind (mono_telescope _ _) fun p => ?_
  obtain ⟨bs, concl⟩ := p
  simp only
  split
  · split
    · split
      · refine Mono.bind (Mono.liftExcept _) fun cv => ?_
        refine Mono.bind (Mono.forIn_array (fun ih acc => ?_) _ _) fun _ => Mono.pure _
        refine Mono.bind (mono_telescope _ _) fun p => ?_
        obtain ⟨_, cc⟩ := p
        simp only
        split
        · split
          · split
            · exact Mono.pure _
            · exact Mono.of_fail (throw_bind_fail _ _)
          · exact Mono.of_fail (throw_bind_fail _ _)
        · exact Mono.of_fail (throw_bind_fail _ _)
      · exact Mono.throw _
    · exact Mono.throw _
  · exact Mono.throw _

theorem sim_analyzeCanonMinor (hok : InjOn (shift s0 d) (FreshBelow B)) (const? : Name → Option ConstantInfo)
    {ms ms' : Array Local} (hms : RLs s0 d B ms ms') {ty ty' : Expr} (hty : RE s0 d B ty ty') :
    Sim s0 d B Eq (Ix.Compile.Image.analyzeCanonMinor const? ms ty)
      (Ix.Compile.Image.analyzeCanonMinor const? ms' ty') := by
  unfold Ix.Compile.Image.analyzeCanonMinor
  refine Sim.bind (sim_telescope' hok hty) (fun p q hpq => ?_) (fun p => ?_)
  · obtain ⟨bs, concl⟩ := p
    obtain ⟨bs', concl'⟩ := q
    obtain ⟨hbs, hc⟩ := hpq
    simp only at hbs hc ⊢
    rw [RLs.idx_eq hok hms hc]
    cases Ix.Compile.Image.fvarIdx? ms (Ix.Compile.Image.getAppFn concl) with
    | none => exact Sim.throw _
    | some mi =>
      simp only
      have ha := appArg?_rel hc
      revert ha
      cases Ix.Compile.Image.appArg? concl <;> cases Ix.Compile.Image.appArg? concl' <;>
        simp only [false_implies, true_implies]
      · exact Sim.throw _
      · intro ha
        rw [headConst?_ren ha.1]
        cases Ix.Compile.Image.headConst? _ with
        | none => exact Sim.throw _
        | some p =>
          obtain ⟨ctor, lv⟩ := p
          simp only
          refine Sim.bind (R := Eq) (Sim.liftExcept (by
            cases Ix.Compile.Image.ctorOf const? ctor <;> simp [ExRel])) (fun cv cv' hcv => ?_)
            (fun _ => ?_)
          · subst hcv
            refine Sim.bind (R := Eq) ?_ (fun r r' hr => Sim.pure (by rw [hr])) (fun _ => Mono.pure _)
            refine Sim.forIn_array (Ra := RL s0 d B) (fun ih ih' acc acc' hih hacc => ?_)
              (fun ih acc => ?_) ?_ rfl
            · subst hacc
              refine Sim.bind (sim_telescope' hok ⟨hih.1.2.2.1, hih.2.2⟩) (fun p q hpq => ?_)
                (fun p => ?_)
              · obtain ⟨_, cc⟩ := p
                obtain ⟨_, cc'⟩ := q
                obtain ⟨-, hcc⟩ := hpq
                simp only at hcc ⊢
                rw [RLs.idx_eq hok hms hcc]
                cases Ix.Compile.Image.fvarIdx? ms (Ix.Compile.Image.getAppFn cc) with
                | none => exact Sim.of_fail (throw_bind_fail _ _)
                | some m =>
                  simp only
                  have hfa := appArg?_rel hcc
                  revert hfa
                  cases Ix.Compile.Image.appArg? cc <;> cases Ix.Compile.Image.appArg? cc' <;>
                    simp only [false_implies, true_implies]
                  · exact Sim.of_fail (throw_bind_fail _ _)
                  · intro hfa
                    rw [RLs.idx_eq hok (hbs.extract 0 cv.numFields) hfa]
                    cases Ix.Compile.Image.fvarIdx? (bs.extract 0 cv.numFields) (Ix.Compile.Image.getAppFn _) with
                    | none => exact Sim.of_fail (throw_bind_fail _ _)
                    | some f => exact Sim.pure rfl
              · obtain ⟨_, cc⟩ := p
                simp only
                split
                · split
                  · split
                    · exact Mono.pure _
                    · exact Mono.of_fail (throw_bind_fail _ _)
                  · exact Mono.of_fail (throw_bind_fail _ _)
                · exact Mono.of_fail (throw_bind_fail _ _)
            · refine Mono.bind (mono_telescope _ _) fun p => ?_
              obtain ⟨_, cc⟩ := p
              simp only
              split
              · split
                · split
                  · exact Mono.pure _
                  · exact Mono.of_fail (throw_bind_fail _ _)
                · exact Mono.of_fail (throw_bind_fail _ _)
              · exact Mono.of_fail (throw_bind_fail _ _)
            · have he := hbs.extract cv.numFields bs.size
              have e : bs'.size = bs.size := hbs.1.symm
              rw [e]
              apply LRel.of_getElem _ _ (by simp [e])
              intro i h1 h2
              simp only [Array.getElem_toList]
              simp only [Array.length_toList] at h1 h2
              exact he.2 i h1 h2
          · refine Mono.bind (Mono.forIn_array (fun ih acc => ?_) _ _) fun _ => Mono.pure _
            refine Mono.bind (mono_telescope _ _) fun p => ?_
            obtain ⟨_, cc⟩ := p
            simp only
            split
            · split
              · split
                · exact Mono.pure _
                · exact Mono.of_fail (throw_bind_fail _ _)
              · exact Mono.of_fail (throw_bind_fail _ _)
            · exact Mono.of_fail (throw_bind_fail _ _)
  · obtain ⟨bs, concl⟩ := p
    simp only
    split
    · split
      · split
        · refine Mono.bind (Mono.liftExcept _) fun cv => ?_
          refine Mono.bind (Mono.forIn_array (fun ih acc => ?_) _ _) fun _ => Mono.pure _
          refine Mono.bind (mono_telescope _ _) fun p => ?_
          obtain ⟨_, cc⟩ := p
          simp only
          split
          · split
            · split
              · exact Mono.pure _
              · exact Mono.of_fail (throw_bind_fail _ _)
            · exact Mono.of_fail (throw_bind_fail _ _)
          · exact Mono.of_fail (throw_bind_fail _ _)
        · exact Mono.throw _
      · exact Mono.throw _
    · exact Mono.throw _

/-- The constants of the environment carry no free variable. -/
def EnvClosed (const? : Name → Option ConstantInfo) : Prop :=
  ∀ n ci, const? n = some ci → FvAll (fun _ => False) ci.getCnst.type

theorem RE.closed {e : Expr} (h : FvAll (fun _ => False) e) : RE s0 d B e e :=
  ⟨Ren.refl_of (FvAll.mono (fun _ hn => hn.elim) h), FvAll.mono (fun _ hn => hn.elim) h⟩

theorem substLevels_go_fv {P : Name → Prop} (ps : Array Name) (us : Array Level) :
    ∀ {e : Expr}, FvAll P e → FvAll P (Ix.Compile.Canon.substLevels.go ps us e)
  | .sort .., _ | .const .., _ => trivial
  | .app .., h => ⟨substLevels_go_fv ps us h.1, substLevels_go_fv ps us h.2⟩
  | .lam .., h | .forallE .., h => ⟨substLevels_go_fv ps us h.1, substLevels_go_fv ps us h.2⟩
  | .letE .., h =>
    ⟨substLevels_go_fv ps us h.1, substLevels_go_fv ps us h.2.1, substLevels_go_fv ps us h.2.2⟩
  | .proj _ _ x _, h => substLevels_go_fv ps us (e := x) h
  | .mdata _ x _, h => substLevels_go_fv ps us (e := x) h
  | .bvar .., h | .fvar .., h | .mvar .., h | .lit .., h => h

theorem substLevels_fv {P : Name → Prop} (ps : Array Name) (us : Array Level) {e : Expr}
    (h : FvAll P e) : FvAll P (Ix.Compile.Canon.substLevels ps us e) := by
  unfold Ix.Compile.Canon.substLevels; split
  · exact h
  · exact substLevels_go_fv ps us h

theorem stripSort_fv {P : Name → Prop} : ∀ {e : Expr}, FvAll P e → FvAll P (Ix.Compile.Image.stripSort e)
  | .forallE _ t b _ _, h => by
    simp only [Ix.Compile.Image.stripSort]; exact ⟨h.1, stripSort_fv (e := b) h.2⟩
  | .mdata _ x _, h => by simp only [Ix.Compile.Image.stripSort]; exact stripSort_fv (e := x) h
  | .sort .., _ => by simp only [Ix.Compile.Image.stripSort]; trivial
  | .bvar .., h | .fvar .., h | .mvar .., h | .const .., h | .lit .., h | .app .., h | .lam .., h
  | .letE .., h | .proj .., h => by simp only [Ix.Compile.Image.stripSort]; exact h

/-- `liftExcept` of the same computation in both runs, remembering the value. -/
theorem Sim.liftExcept_same {α : Type} (x : Except String α) :
    Sim s0 d B (fun a b => a = b ∧ x = .ok a) (Ix.Compile.Image.liftExcept x)
      (Ix.Compile.Image.liftExcept x) :=
  Sim.liftExcept (by cases x <;> simp [ExRel])

theorem recOf_ok {const? : Name → Option ConstantInfo} {n : Name} {rv : RecursorVal}
    (h : Ix.Compile.Image.recOf const? n = .ok rv) : const? n = some (.recInfo rv) := by
  unfold Ix.Compile.Image.recOf at h
  split at h
  · cases h; assumption
  · cases h
  · cases h

theorem mono_elimMotiveTypes (const? : Name → Option ConstantInfo) (ind : InductiveVal)
    (lvls : Array Level) (ps : Array Expr) :
    Mono (Ix.Compile.Image.elimMotiveTypes const? ind lvls ps) := by
  unfold Ix.Compile.Image.elimMotiveTypes
  split
  · refine Mono.bind (Mono.liftExcept _) fun rv => ?_
    refine Mono.bind (Mono.liftExcept _) fun ty => ?_
    refine Mono.bind (mono_telescope _ _) fun p => ?_
    obtain ⟨_, _⟩ := p
    exact Mono.pure _
  · exact Mono.throw _

theorem ARE.lsMapType {xs ys : Array Local} (h : RLs s0 d B xs ys) :
    ARE s0 d B (xs.map fun m => Ix.Compile.Image.stripSort m.type)
      (ys.map fun m => Ix.Compile.Image.stripSort m.type) := by
  refine ⟨?_, ?_⟩
  · unfold ARen
    apply (LRel.of_getElem (R := Ren (shift s0 d)) _ _ (by simp [h.1]) fun i h1 h2 => ?_).rec
      (motive := fun l l' _ => LRen (shift s0 d) l l') .nil (fun hab _ ih => .cons hab ih)
    simp only [Array.getElem_toList, Array.getElem_map]
    simp only [Array.length_toList, Array.size_map] at h1 h2
    exact stripSort_ren (h.2 i h1 h2).1.2.2.1
  · intro x hx
    simp only [Array.toList_map, List.mem_map, Array.mem_toList_iff] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact stripSort_fv (h.fv l hl).2

theorem sim_elimMotiveTypes (hok : InjOn (shift s0 d) (FreshBelow B)) {const? : Name → Option ConstantInfo}
    (hc : EnvClosed const?) (ind : InductiveVal) (lvls : Array Level) {ps ps' : Array Expr}
    (hps : ARE s0 d B ps ps') :
    Sim s0 d B (ARE s0 d B) (Ix.Compile.Image.elimMotiveTypes const? ind lvls ps)
      (Ix.Compile.Image.elimMotiveTypes const? ind lvls ps') := by
  unfold Ix.Compile.Image.elimMotiveTypes
  split
  · rename_i a ha
    refine Sim.bind (Sim.liftExcept_same _) (fun rv rv' hrv => ?_) (fun rv => ?_)
    · obtain ⟨rfl, hrv⟩ := hrv
      have hcl : FvAll (fun _ => False) rv.cnst.type := hc _ _ (recOf_ok hrv)
      have hty := RE.closed (s0 := s0) (d := d) (B := B)
        (substLevels_fv rv.cnst.levelParams
          ((if rv.cnst.levelParams.size > ind.cnst.levelParams.size then #[Ix.Compile.Image.lvlZero]
            else #[]) ++ lvls) hcl)
      have hif := instForall_ren hty.1 hps.1
      have hiff := fun r (h : Ix.Compile.Image.instForall _ ps = .ok r) => instForall_fv hty.2 hps.2 h
      refine Sim.bind (R := RE s0 d B) (Sim.liftExcept ?_) (fun ty ty' hty' => ?_) (fun _ => ?_)
      · revert hif hiff
        cases Ix.Compile.Image.instForall _ ps <;> cases Ix.Compile.Image.instForall _ ps' <;>
          simp [ExRel]
        intro h1 h2; exact ⟨h1, h2⟩
      · refine Sim.bind (sim_telescope hok hty' _) (fun p q hpq => ?_) (fun p => ?_)
        · obtain ⟨msC, _⟩ := p
          obtain ⟨msC', _⟩ := q
          exact Sim.pure (ARE.lsMapType hpq.1)
        · obtain ⟨_, _⟩ := p; exact Mono.pure _
      · refine Mono.bind (mono_telescope _ _) fun p => ?_
        obtain ⟨_, _⟩ := p; exact Mono.pure _
    · refine Mono.bind (Mono.liftExcept _) fun ty => ?_
      refine Mono.bind (mono_telescope _ _) fun p => ?_
      obtain ⟨_, _⟩ := p
      exact Mono.pure _
  · exact Sim.throw _

/-! ## The eliminator choice -/

/-- Candidates of the two runs. -/
def CRel (s0 d B : Nat) (a b : Name × Array Expr × Array Level) : Prop :=
  a.1 = b.1 ∧ ARE s0 d B a.2.1 b.2.1 ∧ a.2.2 = b.2.2

/-- Arrays related pointwise. -/
def ARel {α β : Type} (R : α → β → Prop) (xs : Array α) (ys : Array β) : Prop :=
  xs.size = ys.size ∧ ∀ i (h : i < xs.size) (h' : i < ys.size), R xs[i] ys[i]

theorem ARel.push {α β : Type} {R : α → β → Prop} {xs : Array α} {ys : Array β} (h : ARel R xs ys)
    {a : α} {b : β} (hab : R a b) : ARel R (xs.push a) (ys.push b) := by
  have hsz := h.1
  refine ⟨by simp [h.1], fun i hi hi' => ?_⟩
  simp only [Array.size_push] at hi hi'
  by_cases hlt : i < xs.size
  · rw [Array.getElem_push_lt hlt, Array.getElem_push_lt (by omega)]; exact h.2 i hlt (by omega)
  · have e1 : i = xs.size := by omega
    have e2 : i = ys.size := by omega
    subst e1
    rw [Array.getElem_push_eq]; simp only [e2, Array.getElem_push_eq]; exact hab

theorem ARel.lrel {α β : Type} {R : α → β → Prop} {xs : Array α} {ys : Array β} (h : ARel R xs ys) :
    LRel R xs.toList ys.toList :=
  LRel.of_getElem _ _ (by simp [h.1]) fun i h1 h2 => by
    simp only [Array.getElem_toList]; exact h.2 i (by simpa using h1) (by simpa using h2)

/-- Eliminators of the two runs. -/
def ElimRel (s0 d B : Nat) (e e' : Elim) : Prop :=
  e.recName = e'.recName ∧ e.ind = e'.ind ∧ e.indLevels = e'.indLevels ∧
    ARE s0 d B e.params e'.params ∧ e.k = e'.k ∧ e.hasElimLevel = e'.hasElimLevel

/-- The final loop's state of the eliminator choice. -/
def OElimRel (s0 d B : Nat) (a b : Option Elim × Unit) : Prop :=
  match a.1, b.1 with
  | some e, some e' => ElimRel s0 d B e e'
  | none, none => True
  | _, _ => False

theorem ARE.extract {xs ys : Array Expr} (h : ARE s0 d B xs ys) (a b : Nat) :
    ARE s0 d B (xs.extract a b) (ys.extract a b) := by
  refine ⟨?_, ?_⟩
  · unfold ARen
    apply (LRel.of_getElem (R := Ren (shift s0 d)) _ _ (by simp [h.size]) fun i h1 h2 => ?_).rec
      (motive := fun l l' _ => LRen (shift s0 d) l l') .nil (fun hab _ ih => .cons hab ih)
    simp only [Array.getElem_toList, Array.getElem_extract]
    simp only [Array.length_toList, Array.size_extract] at h1 h2
    exact h.1.get _ (by omega) (by omega)
  · intro x hx
    simp only [Array.mem_toList_iff] at hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    simp only [Array.getElem_extract]
    simp only [Array.size_extract] at hi
    exact h.2 _ (by simp)

theorem getAppArgs_rel {a b : Expr} (h : RE s0 d B a b) :
    ARE s0 d B (Ix.Compile.Image.getAppArgs a) (Ix.Compile.Image.getAppArgs b) :=
  ⟨getAppArgs_ren h.1, (getAppFnArgs_fv h.2).2⟩

theorem first2_some {α : Type} {o1 o2 : Option α} {x : α} (h : Ix.Compile.Image.first2 o1 o2 = some x) :
    o1 = some x ∨ o2 = some x := by
  cases o1 <;> simp_all [Ix.Compile.Image.first2]

theorem findSub?_fv {P : Name → Prop} (p : Expr → Bool) :
    ∀ (e : Expr) {x : Expr}, Ix.Compile.Image.findSub? p e = some x → FvAll P e → FvAll P x
  | .app f a _, x, hx, hf => by
    unfold Ix.Compile.Image.findSub? at hx; split at hx
    · cases hx; exact hf
    · rcases first2_some hx with h1 | h2
      · exact findSub?_fv p f h1 hf.1
      · exact findSub?_fv p a h2 hf.2
  | .lam _ t b _ _, x, hx, hf => by
    unfold Ix.Compile.Image.findSub? at hx; split at hx
    · cases hx; exact hf
    · rcases first2_some hx with h1 | h2
      · exact findSub?_fv p t h1 hf.1
      · exact findSub?_fv p b h2 hf.2
  | .forallE _ t b _ _, x, hx, hf => by
    unfold Ix.Compile.Image.findSub? at hx; split at hx
    · cases hx; exact hf
    · rcases first2_some hx with h1 | h2
      · exact findSub?_fv p t h1 hf.1
      · exact findSub?_fv p b h2 hf.2
  | .letE _ t v b _ _, x, hx, hf => by
    unfold Ix.Compile.Image.findSub? at hx; split at hx
    · cases hx; exact hf
    · rcases first2_some hx with h1 | h2
      · exact findSub?_fv p t h1 hf.1
      · rcases first2_some h2 with h3 | h4
        · exact findSub?_fv p v h3 hf.2.1
        · exact findSub?_fv p b h4 hf.2.2
  | .proj _ _ y _, x, hx, hf => by
    unfold Ix.Compile.Image.findSub? at hx; split at hx
    · cases hx; exact hf
    · exact findSub?_fv p y hx hf
  | .mdata _ y _, x, hx, hf => by
    unfold Ix.Compile.Image.findSub? at hx; split at hx
    · cases hx; exact hf
    · exact findSub?_fv p y hx hf
  | .bvar .., x, hx, hf | .fvar .., x, hx, hf | .mvar .., x, hx, hf | .sort .., x, hx, hf
  | .const .., x, hx, hf | .lit .., x, hx, hf => by
    unfold Ix.Compile.Image.findSub? at hx; split at hx
    · cases hx; exact hf
    · cases hx

theorem findSub?_rel {p : Expr → Bool} (hp : ∀ a b, Ren (shift s0 d) a b → p b = p a)
    {a b : Expr} (h : RE s0 d B a b) :
    match Ix.Compile.Image.findSub? p a, Ix.Compile.Image.findSub? p b with
    | some x, some y => RE s0 d B x y
    | none, none => True
    | _, _ => False := by
  have hr := findSub?_ren hp h.1
  have hf : ∀ x, Ix.Compile.Image.findSub? p a = some x → FvAll (FreshBelow B) x :=
    fun x hx => findSub?_fv p a hx h.2
  revert hr hf
  cases Ix.Compile.Image.findSub? p a <;> cases Ix.Compile.Image.findSub? p b <;> simp [ORen]
  intro h1 h2; exact ⟨h1, h2⟩

theorem indOf_ok {const? : Name → Option ConstantInfo} {n : Name} {iv : InductiveVal}
    (h : Ix.Compile.Image.indOf const? n = .ok iv) : const? n = some (.inductInfo iv) := by
  unfold Ix.Compile.Image.indOf at h
  split at h
  · cases h; assumption
  · cases h

theorem mono_findElim (c : LCtx) (t : Nat) : Mono (Ix.Compile.Image.findElim c t) := by
  unfold Ix.Compile.Image.findElim
  split
  · refine Mono.bind (Mono.idx _ _ _) fun target => ?_
    refine Mono.bind (mono_telescope _ _) fun p => ?_
    obtain ⟨xs, _⟩ := p
    simp only
    split
    · split
      · refine Mono.bind (Mono.forIn_array (fun i acc => ?_) _ _) fun cands => ?_
        · split <;> exact Mono.pure _
        refine Mono.bind (Mono.forIn_array (fun i acc => ?_) _ _) fun cands => ?_
        · split
          · refine Mono.bind (Mono.liftExcept _) fun iv => ?_
            split <;> exact Mono.pure _
          · exact Mono.pure _
        refine Mono.bind (Mono.liftExcept _) fun hInfo => ?_
        split
        · split
          all_goals
            refine Mono.bind (Mono.forIn_array (fun x s => ?_) _ _) fun r => ?_
            · refine Mono.bind (Mono.liftExcept _) fun ind => ?_
              split
              · exact Mono.pure _
              · refine Mono.bind (mono_elimMotiveTypes _ _ _ _) fun mts => ?_
                split
                · exact Mono.bind (Mono.liftExcept _) fun _ => Mono.pure _
                · exact Mono.pure _
            · split
              · exact Mono.pure _
              · exact Mono.throw _
        · refine Mono.bind (Mono.forIn_array (fun x s => ?_) _ _) fun r => ?_
          · refine Mono.bind (Mono.liftExcept _) fun ind => ?_
            split
            · exact Mono.pure _
            · refine Mono.bind (mono_elimMotiveTypes _ _ _ _) fun mts => ?_
              split
              · exact Mono.bind (Mono.liftExcept _) fun _ => Mono.pure _
              · exact Mono.pure _
          · split
            · exact Mono.pure _
            · exact Mono.throw _
      · exact Mono.throw _
    · exact Mono.throw _
  · exact Mono.throw _

theorem LRel.refl_eq {α : Type} : ∀ (l : List α), LRel Eq l l
  | [] => .nil
  | _ :: l => .cons rfl (LRel.refl_eq l)

theorem ARel.empty {α β : Type} {R : α → β → Prop} : ARel R (#[] : Array α) (#[] : Array β) :=
  ⟨rfl, fun i h => by simp at h⟩

theorem ARel.pop {α β : Type} {R : α → β → Prop} {xs : Array α} {ys : Array β} (h : ARel R xs ys) :
    ARel R xs.pop ys.pop := by
  refine ⟨by simp [h.1], fun i h1 h2 => ?_⟩
  simp only [Array.getElem_pop]
  simp only [Array.size_pop] at h1 h2
  exact h.2 i (by omega) (by omega)

theorem ARel.singleton_append {α β : Type} {R : α → β → Prop} {a : α} {b : β} (hab : R a b)
    {xs : Array α} {ys : Array β} (h : ARel R xs ys) : ARel R (#[a] ++ xs) (#[b] ++ ys) := by
  refine ⟨by simp [h.1], fun i h1 h2 => ?_⟩
  simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil] at h1 h2
  rcases i with _ | i
  · simp only [Array.getElem_append_left (show 0 < (#[a] : Array α).size by simp),
      Array.getElem_append_left (show 0 < (#[b] : Array β).size by simp)]
    simpa using hab
  · rw [Array.getElem_append_right (by simp), Array.getElem_append_right (by simp)]
    simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.add_sub_cancel]
    exact h.2 i (by omega) (by omega)

theorem ARel.back? {α β : Type} {R : α → β → Prop} {xs : Array α} {ys : Array β} (h : ARel R xs ys) :
    match xs.back?, ys.back? with
    | some a, some b => R a b
    | none, none => True
    | _, _ => False := by
  have hs := h.1
  rw [Array.back?_eq_getElem?, Array.back?_eq_getElem?]
  by_cases h0 : xs.size = 0
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]; trivial
  · rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)]
    have := h.2 (xs.size - 1) (by omega) (by omega)
    simp only [show ys.size - 1 = xs.size - 1 by omega]
    exact this

theorem ARE.ofCtx {xs : Array Local} (h : ∀ l ∈ xs, FreshBelow s0 l.fvar ∧ FvAll (FreshBelow s0) l.type)
    (hB : s0 ≤ B) : ARE s0 d B (xs.map (·.expr)) (xs.map (·.expr)) :=
  (RLs.refl (d := d) h hB).exprs

/-- The motive-type comparison of the eliminator choice, from related motive types. -/
theorem findIdx_alphaEq_eq (_hok : InjOn (shift s0 d) (FreshBelow B)) {mts mts' : Array Expr} (h : ARE s0 d B mts mts')
    {target : Expr} (htr : RE s0 d B target target) :
    mts'.findIdx? (fun x => Ix.Compile.Image.alphaEq x target) =
      mts.findIdx? (fun x => Ix.Compile.Image.alphaEq x target) := by
  apply array_findIdx?_congr _ _ h.size.symm
  intro i h1 h2
  exact alphaEq_ren exactInjOn_shift (h.1.get i h2 h1) htr.1 (h.2 _ (by simp)) htr.2

/-- The occurrence finder of `findElim`, through any head-respecting predicate: related answers. -/
theorem occ_match {P : Expr → Bool} (hP : ∀ a b, Ren (shift s0 d) a b → P b = P a)
    {G : Expr → Array Expr × Array Level}
    (hG : ∀ a b, RE s0 d B a b → ARE s0 d B (G a).1 (G b).1 ∧ (G a).2 = (G b).2)
    {a b : Expr} (h : RE s0 d B a b) :
    match Option.map G (Ix.Compile.Image.findSub? P a), Option.map G (Ix.Compile.Image.findSub? P b) with
    | some r, some r' => ARE s0 d B r.1 r'.1 ∧ r.2 = r'.2
    | none, none => True
    | _, _ => False := by
  have hf := findSub?_rel hP h
  revert hf
  cases Ix.Compile.Image.findSub? P a <;> cases Ix.Compile.Image.findSub? P b <;>
    simp only [Option.map_none, Option.map_some, imp_self]
  intro hxy; exact hG _ _ hxy

theorem occ_G (np : Nat) {a b : Expr} (h : RE s0 d B a b) :
    ARE s0 d B ((Ix.Compile.Image.getAppArgs a).extract 0 np) ((Ix.Compile.Image.getAppArgs b).extract 0 np) ∧
      (Option.map (fun x => x.snd) (Ix.Compile.Image.headConst? a)).getD #[] =
        (Option.map (fun x => x.snd) (Ix.Compile.Image.headConst? b)).getD #[] :=
  ⟨ARE.extract (getAppArgs_rel h) 0 np, by rw [headConst?_ren h.1]⟩

theorem occ_match_ss {P : Expr → Bool} (hP : ∀ a b, Ren (shift s0 d) a b → P b = P a)
    {G : Expr → Array Expr × Array Level}
    (hG : ∀ a b, RE s0 d B a b → ARE s0 d B (G a).1 (G b).1 ∧ (G a).2 = (G b).2)
    {a b : Expr} (h : RE s0 d B a b) {r r' : Array Expr × Array Level}
    (h1 : Option.map G (Ix.Compile.Image.findSub? P a) = some r)
    (h2 : Option.map G (Ix.Compile.Image.findSub? P b) = some r') : ARE s0 d B r.1 r'.1 ∧ r.2 = r'.2 := by
  have ho := occ_match hP hG h
  rw [h1, h2] at ho; exact ho

theorem occ_match_sn {P : Expr → Bool} (hP : ∀ a b, Ren (shift s0 d) a b → P b = P a)
    {G : Expr → Array Expr × Array Level}
    (hG : ∀ a b, RE s0 d B a b → ARE s0 d B (G a).1 (G b).1 ∧ (G a).2 = (G b).2)
    {a b : Expr} (h : RE s0 d B a b) {r : Array Expr × Array Level}
    (h1 : Option.map G (Ix.Compile.Image.findSub? P a) = some r)
    (h2 : ∀ r', Option.map G (Ix.Compile.Image.findSub? P b) ≠ some r') : False := by
  have ho := occ_match hP hG h
  rw [h1] at ho
  revert ho
  cases hb : Option.map G (Ix.Compile.Image.findSub? P b) with
  | none => simp
  | some r' => exact fun _ => h2 r' hb

theorem occ_match_ns {P : Expr → Bool} (hP : ∀ a b, Ren (shift s0 d) a b → P b = P a)
    {G : Expr → Array Expr × Array Level}
    (hG : ∀ a b, RE s0 d B a b → ARE s0 d B (G a).1 (G b).1 ∧ (G a).2 = (G b).2)
    {a b : Expr} (h : RE s0 d B a b) {r' : Array Expr × Array Level}
    (h1 : ∀ r, Option.map G (Ix.Compile.Image.findSub? P a) ≠ some r)
    (h2 : Option.map G (Ix.Compile.Image.findSub? P b) = some r') : False := by
  have ho := occ_match hP hG h
  rw [h2] at ho
  revert ho
  cases ha : Option.map G (Ix.Compile.Image.findSub? P a) with
  | none => simp
  | some r => exact fun _ => h1 r ha

set_option hygiene false in
macro "rfl_tail" : tactic => `(tactic| (
  refine Sim.bind (R := OElimRel s0 d B) ?_ (fun r r' hr => ?_) (fun r => ?_)
  · refine Sim.forIn_array (Ra := CRel s0 d B) (fun x x' s s' hx hs => ?_) (fun x s => ?_) hrel.lrel
      (by simp [OElimRel])
    · obtain ⟨i, ps, lv⟩ := x
      obtain ⟨i', ps', lv'⟩ := x'
      obtain ⟨hi, hps, hlv⟩ := hx
      simp only at hi hps hlv
      subst hi hlv
      simp only
      refine Sim.bind (Sim.liftExcept_same _) (fun ind ind' hind => ?_) (fun _ => ?_)
      · obtain ⟨rfl, -⟩ := hind
        rw [hps.size]
        split
        · exact Sim.pure (by simp [StepRel, OElimRel])
        · refine Sim.bind (sim_elimMotiveTypes hok hcl ind lv hps) (fun mts mts' hm => ?_) (fun _ => ?_)
          · rw [findIdx_alphaEq_eq hok hm htf]
            cases Array.findIdx? (fun x => Ix.Compile.Image.alphaEq x target) mts with
            | none => exact Sim.pure (by simp [StepRel, OElimRel])
            | some k =>
              simp only
              refine Sim.bind (Sim.liftExcept_same _) (fun rv rv' hrv => ?_) (fun _ => Mono.pure _)
              obtain ⟨rfl, -⟩ := hrv
              exact Sim.pure ⟨rfl, rfl, rfl, hps, rfl, rfl⟩
          · split
            · exact Mono.bind (Mono.liftExcept _) fun _ => Mono.pure _
            · exact Mono.pure _
      · split
        · exact Mono.pure _
        · refine Mono.bind (mono_elimMotiveTypes _ _ _ _) fun mts => ?_
          split
          · exact Mono.bind (Mono.liftExcept _) fun _ => Mono.pure _
          · exact Mono.pure _
    · refine Mono.bind (Mono.liftExcept _) fun ind => ?_
      split
      · exact Mono.pure _
      · refine Mono.bind (mono_elimMotiveTypes _ _ _ _) fun mts => ?_
        split
        · exact Mono.bind (Mono.liftExcept _) fun _ => Mono.pure _
        · exact Mono.pure _
  · obtain ⟨o, _⟩ := r
    obtain ⟨o', _⟩ := r'
    simp only [OElimRel] at hr
    cases o <;> cases o' <;> simp only at hr
    · exact Sim.throw _
    · exact Sim.pure hr
  · split
    · exact Mono.pure _
    · exact Mono.throw _))

set_option hygiene false in
macro "rfl_mono" : tactic => `(tactic| (
  refine Mono.bind (Mono.forIn_array (fun x s => ?_) _ _) fun r => ?_
  · refine Mono.bind (Mono.liftExcept _) fun ind => ?_
    split
    · exact Mono.pure _
    · refine Mono.bind (mono_elimMotiveTypes _ _ _ _) fun mts => ?_
      split
      · exact Mono.bind (Mono.liftExcept _) fun _ => Mono.pure _
      · exact Mono.pure _
  · split
    · exact Mono.pure _
    · exact Mono.throw _))

set_option hygiene false in
macro "mono_after2" : tactic => `(tactic| (
  refine Mono.bind (Mono.liftExcept _) fun hInfo => ?_
  split
  · split
    all_goals rfl_mono
  · rfl_mono))

set_option hygiene false in
macro "mono_after1" : tactic => `(tactic| (
  refine Mono.bind (Mono.forIn_array (fun i acc => ?_) _ _) fun cands => ?_
  · split
    · refine Mono.bind (Mono.liftExcept _) fun iv => ?_
      split <;> exact Mono.pure _
    · exact Mono.pure _
  mono_after2))

set_option hygiene false in
macro "mono_aftertel" : tactic => `(tactic| (
  obtain ⟨xs, _⟩ := p
  simp only
  split
  · split
    · refine Mono.bind (Mono.forIn_array (fun i acc => ?_) _ _) fun cands => ?_
      · split <;> exact Mono.pure _
      mono_after1
    · exact Mono.throw _
  · exact Mono.throw _))

theorem sim_findElim (hok : InjOn (shift s0 d) (FreshBelow B)) (c : LCtx) (hc : CtxRE s0 d B c)
    (hcl : EnvClosed c.const?) (t : Nat) :
    Sim s0 d B (ElimRel s0 d B) (Ix.Compile.Image.findElim c t) (Ix.Compile.Image.findElim c t) := by
  unfold Ix.Compile.Image.findElim
  split
  · rename_i m hm
    have hmem : m ∈ c.ms := Array.mem_of_getElem? hm
    refine Sim.bind (R := fun a b => a = b ∧ RE s0 d B a a)
      (Sim.idx rfl (fun i h1 h2 => ⟨rfl, hc.2 _ (Array.getElem_mem h1)⟩) _ _)
      (fun target target' ht => ?_) (fun _ => ?_)
    · obtain ⟨rfl, htf⟩ := ht
      have hmt : RE s0 d B m.type m.type := (hc.1 m (by simp [hmem])).2.2
      refine Sim.bind (sim_telescope' hok hmt) (fun p q hpq => ?_) (fun p => ?_)
      · obtain ⟨xs, _⟩ := p
        obtain ⟨xs', _⟩ := q
        obtain ⟨hxs, -⟩ := hpq
        simp only
        have hb := ARel.back? (R := RL s0 d B) (⟨hxs.1, hxs.2⟩ : ARel _ xs xs')
        revert hb
        cases xs.back? <;> cases xs'.back? <;> simp only [false_implies, true_implies]
        · exact Sim.throw _
        · rename_i x x'
          intro hx
          have hT : RE s0 d B x.type x'.type := ⟨hx.1.2.2.1, hx.2.2⟩
          rw [headConst?_ren hT.1]
          cases Ix.Compile.Image.headConst? x.type with
          | none => exact Sim.throw _
          | some p =>
            obtain ⟨H, hLvls⟩ := p
            simp only
            rw [usedConstants_ren hT.1]
            have hps : ARE s0 d B (c.ps.map (·.expr)) (c.ps.map (·.expr)) := hc.ps.exprs
            refine Sim.bind (R := ARel (CRel s0 d B)) (Sim.forIn_array (Ra := Eq)
              (fun i i' s s' hi hs => ?_) (fun i s => ?_) (LRel.refl_eq _) ARel.empty)
              (fun cs cs' hcs => ?_) (fun _ => ?_)
            · subst hi
              split
              · exact Sim.pure (show ARel _ _ _ from hs.push ⟨rfl, hps, rfl⟩)
              · exact Sim.pure (show ARel _ _ _ from hs)
            · split <;> exact Mono.pure _
            · refine Sim.bind (R := ARel (CRel s0 d B)) (Sim.forIn_array (Ra := Eq)
                (fun i i' s s' hi hs => ?_) (fun i s => ?_) (LRel.refl_eq _) hcs)
                (fun cs2 cs2' hcs2 => ?_) (fun _ => ?_)
              · subst hi
                split
                · refine Sim.bind (Sim.liftExcept_same _) (fun iv iv' hiv => ?_) (fun _ => ?_)
                  · obtain ⟨rfl, -⟩ := hiv
                    split
                    · rename_i ps lv heq1
                      split
                      · rename_i ps' lv' heq2
                        obtain ⟨h1, h2⟩ := occ_match_ss (s0 := s0) (d := d) (B := B) (h1 := heq1) (h2 := heq2)
                          (fun a b hab => by try dsimp only
                                             rw [headConst?_ren hab, (getAppArgs_ren hab).size])
                          (fun a b hab => by exact occ_G _ hab) hT
                        simp only at h1 h2
                        subst h2
                        exact Sim.pure (show ARel _ _ _ from hs.push ⟨rfl, h1, rfl⟩)
                      · rename_i hne
                        exact (occ_match_sn (s0 := s0) (d := d) (B := B) (h1 := heq1)
                          (h2 := fun r hr => hne r.1 r.2 hr)
                          (fun a b hab => by try dsimp only
                                             rw [headConst?_ren hab, (getAppArgs_ren hab).size])
                          (fun a b hab => by exact occ_G _ hab) hT).elim
                    · rename_i hne
                      split
                      · rename_i ps' lv' heq2
                        exact (occ_match_ns (s0 := s0) (d := d) (B := B) (h2 := heq2)
                          (h1 := fun r hr => hne r.1 r.2 hr)
                          (fun a b hab => by try dsimp only
                                             rw [headConst?_ren hab, (getAppArgs_ren hab).size])
                          (fun a b hab => by exact occ_G _ hab) hT).elim
                      · exact Sim.pure (show ARel _ _ _ from hs)
                  · split <;> exact Mono.pure _
                · exact Sim.pure (show ARel _ _ _ from hs)
              · split
                · refine Mono.bind (Mono.liftExcept _) fun _ => ?_
                  split <;> exact Mono.pure _
                · exact Mono.pure _
              · refine Sim.bind (Sim.liftExcept_same _) (fun hInfo hInfo' hh => ?_) (fun _ => ?_)
                · obtain ⟨rfl, -⟩ := hh
                  have hpush := hcs2.push (a := (H, (Ix.Compile.Image.getAppArgs x.type).extract 0 hInfo.numParams, hLvls))
                    (b := (H, (Ix.Compile.Image.getAppArgs x'.type).extract 0 hInfo.numParams, hLvls))
                    ⟨rfl, ARE.extract (getAppArgs_rel hT) 0 _, rfl⟩
                  have hback := ARel.back? hpush
                  split
                  · split
                    · rename_i b hb1
                      split
                      · rename_i b' hb2
                        rw [hb1, hb2] at hback
                        have hrel := ARel.singleton_append (show CRel s0 d B b b' from hback) hpush.pop
                        clear hback hb1 hb2
                        rfl_tail
                      · rename_i hne
                        exfalso
                        rw [hb1] at hback
                        revert hback
                        cases hq : (cs2'.push _).back? with
                        | none => simp
                        | some q => exact absurd hq (hne q)
                    · rename_i hne
                      split
                      · rename_i b' hb2
                        exfalso
                        rw [hb2] at hback
                        revert hback
                        cases hq : (cs2.push _).back? with
                        | none => simp
                        | some q => exact absurd hq (hne q)
                      · have hrel := hpush
                        rfl_tail
                  · have hrel := hpush
                    rfl_tail
                · split
                  · split
                    all_goals rfl_mono
                  · rfl_mono
              · mono_after2
            · mono_after1
      · mono_aftertel
    · refine Mono.bind (mono_telescope _ _) fun p => ?_
      mono_aftertel
  · exact Sim.throw _

end

end Ix.CompileCert.Img
