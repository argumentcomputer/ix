import Compilatrix.Rt.Proof.Switch

/-!
# Switches on tags and words: the Lir side

`tagSwitch` without cell keys is a chain on the word. With cell keys and
neither field-less keys nor a default it loads the tag and chains on it;
otherwise it tests the low bit first: an even word (a cell) loads its tag
and chains on it, an odd one chains on the word. `tagSwitch_odd` runs an
odd word to its pick (outside the cells-only shape, where an odd word has
no tag to load); `tagSwitch_even` runs a cell's even word, whose tag
half-word reads `tagw`.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap)

theorem run_bind {α β : Type} {a : M α} {g : α → M β} {s s' : St} {r : β}
    (h : (a >>= g).run s = .ok (r, s')) : ∃ x s₁, a.run s = .ok (x, s₁) ∧ (g x).run s₁ = .ok (r, s') := by
  simp only [StateT.run, bind, StateT.bind, Except.bind] at h
  cases ha : a s with
  | error e => simp [ha] at h
  | ok p => exact ⟨p.1, p.2, by rw [StateT.run, ha], by simp only [ha] at h; exact h⟩

/-- The tag load's statement. -/
def tagStmt (t x : Nat) : Lir.Stmt := .assign t (.load .w16 .zero (mem x tagOffset))

/-- The block a mixed switch ends with its low-bit test. -/
def tzBlock (st : St) (x : Nat) : PBlock :=
  { params := st.params, body := st.acc.reverse, term := .br .tz (.v x) (.imm 1) (loc st.next) (loc (st.next + 1)) }

/-- The state after loading the tag in the open block. -/
def loadSt (st : St) (x : Nat) : St :=
  { st with fresh := st.fresh + 1, acc := [tagStmt st.fresh x].reverse ++ st.acc }

/-- The state after the low-bit test, in the cell block with the tag
loaded. -/
def mixSt (st : St) (x : Nat) : St :=
  { closeSt { st with next := st.next + 2 } (.br .tz (.v x) (.imm 1) (loc st.next) (loc (st.next + 1))) with
    cur := st.next, params := [], acc := [tagStmt st.fresh x], fresh := st.fresh + 1 }

/-- The state in the word block. -/
def wordSt (st : St) (x : Nat) (s₄ : St) : St := { s₄ with cur := st.next + 1, params := [], acc := [] }

theorem mixed_run {x : Nat} {cells imms : List (Lir.Arg × PEdge)} {dd : Option PEdge} {st st' : St}
    (h : (do
      let p ← newLabel
      let i ← newLabel
      close (.br .tz (.v x) (.imm 1) (loc p) (loc i))
      openAt p
      chainOr (← loadTag x) cells dd
      openAt i
      chainOr (.v x) imms dd : M Unit).run st = .ok ((), st')) :
    ∃ s₄, (chainOr (.v st.fresh) cells dd).run (mixSt st x) = .ok ((), s₄) ∧
      (chainOr (.v x) imms dd).run (wordSt st x s₄) = .ok ((), st') := by
  have key : (do
      let p ← newLabel
      let i ← newLabel
      close (.br .tz (.v x) (.imm 1) (loc p) (loc i))
      openAt p
      chainOr (← loadTag x) cells dd
      openAt i
      chainOr (.v x) imms dd : M Unit).run st =
      (do chainOr (.v st.fresh) cells dd; openAt (st.next + 1); chainOr (.v x) imms dd : M Unit).run (mixSt st x) :=
    rfl
  rw [key] at h
  obtain ⟨_, s₄, h₁, h₂⟩ := run_bind h
  obtain ⟨_, s₅, h₃, h₄⟩ := run_bind h₂
  rw [openAt_run] at h₃
  cases h₃
  exact ⟨s₄, h₁, h₄⟩

theorem cellsOnly_run {x : Nat} {cells : List (Lir.Arg × PEdge)} {st st' : St}
    (h : (do chainOr (← loadTag x) cells none : M Unit).run st = .ok ((), st')) :
    (chainOr (.v st.fresh) cells none).run (loadSt st x) = .ok ((), st') := by
  obtain ⟨_, s₁, h₁, h₂⟩ := run_bind h
  have : (loadTag x).run st = .ok (.v st.fresh, loadSt st x) := rfl
  rw [this] at h₁
  cases h₁
  exact h₂

theorem labels_mixSt {st : St} (hl : Labels st) (x : Nat) : Labels (mixSt st x) where
  cur := by simp [mixSt, closeSt]
  done {j b} h := by
    simp only [mixSt, closeSt, NatMap.get?_insert] at h
    show j < st.next + 2
    split at h
    · have := hl.cur; omega
    · have := hl.done h; omega

theorem open_mixSt {st : St} (hl : Labels st) (x : Nat) : Open (mixSt st x) := by
  simp only [Open, mixSt, closeSt, NatMap.get?_insert]
  rw [if_neg (by have := hl.cur; omega)]
  cases h : st.done.get? st.next with
  | none => rfl
  | some b => have := hl.done h; omega

theorem grows_mixSt {st : St} (hl : Labels st) (ho : Open st) (x : Nat) : Grows st (mixSt st x) where
  next := by simp [mixSt, closeSt]
  fresh := by simp [mixSt, closeSt]
  done {j b} h := by
    simp only [mixSt, closeSt, NatMap.get?_insert]
    rw [if_neg (by intro e; subst e; rw [ho] at h; cases h)]
    exact h
  cur _ := .inr ⟨tzBlock st x,
    by simp [tzBlock, mixSt, closeSt, NatMap.get?_insert], rfl, List.prefix_refl _⟩

/-- What the mixed shape's two chains leave. -/
theorem mixed_facts {x : Nat} {cells imms : List (Lir.Arg × PEdge)} {dd : Option PEdge} {st s₄ st' : St}
    (hl : Labels st) (h₁ : (chainOr (.v st.fresh) cells dd).run (mixSt st x) = .ok ((), s₄))
    (h₂ : (chainOr (.v x) imms dd).run (wordSt st x s₄) = .ok ((), st')) :
    Grows (mixSt st x) s₄ ∧ Grows s₄ (wordSt st x s₄) ∧ Grows (wordSt st x s₄) st' ∧
      Labels (wordSt st x s₄) ∧ Open (wordSt st x s₄) := by
  have hl₃ := labels_mixSt hl x
  have ho₃ := open_mixSt hl x
  obtain ⟨hg₄, hl₄, ho₄, -⟩ := chainOr_grows h₁ hl₃ ho₃
  have hk₄ : NewKeys (mixSt st x) s₄ := chainOr_keys h₁
  have hl₅ : Labels (wordSt st x s₄) :=
    { cur := by have := hg₄.next; simp [wordSt, mixSt, closeSt] at this ⊢; omega, done := hl₄.done }
  have ho₅ : Open (wordSt st x s₄) := by
    simp only [Open, wordSt]
    cases hj : s₄.done.get? (st.next + 1) with
    | none => rfl
    | some b =>
      rcases hk₄ hj with hj' | hj' | hj'
      · simp only [mixSt, closeSt, NatMap.get?_insert] at hj'
        split at hj'
        · have := hl.cur; omega
        · have := hl.done hj'; omega
      · simp [mixSt] at hj'
      · simp [mixSt, closeSt] at hj'
  have hg₅ : Grows s₄ (wordSt st x s₄) :=
    { next := Nat.le_refl _, fresh := Nat.le_refl _, done := id, cur := fun h => absurd h ho₄ }
  obtain ⟨hg₆, -, -, -⟩ := chainOr_grows h₂ hl₅ ho₅
  exact ⟨hg₄, hg₅, hg₆, hl₅, ho₅⟩

/-- A switch on tags and words finishes every block it opens. -/
theorem tagSwitch_grows {x : Nat} {es : List (KeyKind × PEdge)} {dd : Option PEdge} {st st' : St}
    (h : (tagSwitch x es dd).run st = .ok ((), st')) (hl : Labels st) (ho : Open st) : Grows st st' := by
  cases hc : cellTests es with
  | nil =>
    simp only [tagSwitch, hc] at h
    exact (chainOr_grows h hl ho).1
  | cons c cs =>
    have hmixed : ∀ (imms : List (Lir.Arg × PEdge)) (dd' : Option PEdge), (do
        let p ← newLabel
        let i ← newLabel
        close (.br .tz (.v x) (.imm 1) (loc p) (loc i))
        openAt p
        chainOr (← loadTag x) (c :: cs) dd'
        openAt i
        chainOr (.v x) imms dd' : M Unit).run st = .ok ((), st') → Grows st st' := by
      intro imms dd' hm
      obtain ⟨s₄, h₁, h₂⟩ := mixed_run hm
      obtain ⟨hg₄, hg₅, hg₆, -, -⟩ := mixed_facts hl h₁ h₂
      exact (((grows_mixSt hl ho x).trans hg₄).trans hg₅).trans hg₆
    cases hi : immTests es with
    | nil =>
      cases dd with
      | none =>
        simp only [tagSwitch, hc, hi] at h
        have h' := cellsOnly_run h
        exact (grows_acc _ _ (Nat.le_succ _)).trans (chainOr_grows h' (labels_acc _ _ hl) (open_acc _ _ ho)).1
      | some d => simp only [tagSwitch, hc, hi] at h; exact hmixed _ _ h
    | cons i is => simp only [tagSwitch, hc, hi] at h; exact hmixed _ _ h

/-- **An odd word takes the word chain's pick** (outside the cells-only
shape). -/
theorem tagSwitch_odd {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {mem : X86.Memory} {ctx : Word} {rest : List Lir.Frame} {x : Nat} {es : List (KeyKind × PEdge)}
    {dd : Option PEdge} {st st' stF : St} (h : (tagSwitch x es dd).run st = .ok ((), st')) (hl : Labels st)
    (ho : Open st) (hg : Grows st' stF) (hC : Ext C stF) {ρl : Lir.Env} {wx : Word} (hx : ρl[x]? = some wx)
    (hodd : wx &&& 1 ≠ 0) (hshape : cellTests es = [] ∨ immTests es ≠ [] ∨ dd ≠ none) {pe : PEdge}
    (hpick : chainOrPick wx (immTests es) dd = some pe) :
    ∃ le, resolveEdge f off starts pe = .ok le ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        le ρl := by
  have hxv : (Lir.Arg.v x).eval ρl = some wx := hx
  have himm : ∀ t ∈ immTests es, ∃ w, t.1 = .imm w := by
    intro t ht
    simp only [immTests, List.mem_filterMap] at ht
    obtain ⟨⟨k, e⟩, -, hk⟩ := ht
    cases k <;> simp only [immTest, cellTest, Option.some.injEq, reduceCtorEq] at hk <;> subst hk <;> exact ⟨_, rfl⟩
  cases hc : cellTests es with
  | nil =>
    simp only [tagSwitch, hc] at h
    exact chainOr_reaches hF hH hxv h hl ho hg hC himm hpick
  | cons c cs =>
    have hmix : (do
        let p ← newLabel
        let i ← newLabel
        close (.br .tz (.v x) (.imm 1) (loc p) (loc i))
        openAt p
        chainOr (← loadTag x) (c :: cs) dd
        openAt i
        chainOr (.v x) (immTests es) dd : M Unit).run st = .ok ((), st') := by
      rcases hshape with hcs | hne | hdd
      · rw [hc] at hcs; cases hcs
      · cases hi : immTests es with
        | nil => exact absurd hi hne
        | cons i is => simp only [tagSwitch, hc, hi] at h; exact h
      · cases dd with
        | none => exact absurd rfl hdd
        | some d =>
          cases hi : immTests es with
          | nil => simp only [tagSwitch, hc, hi] at h; exact h
          | cons i is => simp only [tagSwitch, hc, hi] at h; exact h
    obtain ⟨s₄, h₁, h₂⟩ := mixed_run hmix
    have hl₃ := labels_mixSt hl x
    have ho₃ := open_mixSt hl x
    obtain ⟨hg₄, hl₄, ho₄, -⟩ := chainOr_grows h₁ hl₃ ho₃
    have hk₄ : NewKeys (mixSt st x) s₄ := chainOr_keys h₁
    have hl₅ : Labels (wordSt st x s₄) :=
      { cur := by have := hg₄.next; simp [wordSt, mixSt, closeSt] at this ⊢; omega, done := hl₄.done }
    have ho₅ : Open (wordSt st x s₄) := by
      simp only [Open, wordSt]
      cases hj : s₄.done.get? (st.next + 1) with
      | none => rfl
      | some b =>
        rcases hk₄ hj with hj' | hj' | hj'
        · simp only [mixSt, closeSt, NatMap.get?_insert] at hj'
          split at hj'
          · have := hl.cur; omega
          · have := hl.done hj'; omega
        · simp [mixSt] at hj'
        · simp [mixSt, closeSt] at hj'
    have hg₅ : Grows s₄ (wordSt st x s₄) :=
      { next := Nat.le_refl _, fresh := Nat.le_refl _, done := id, cur := fun h => absurd h ho₄ }
    obtain ⟨hg₆, -, -, -⟩ := chainOr_grows h₂ hl₅ ho₅
    -- the low-bit test sends an odd word to the word block
    have hCt : C[st.cur]? = some (tzBlock st x) :=
      hC.done (((hg₄.trans hg₅).trans hg₆).trans hg |>.done (by simp [mixSt, closeSt, tzBlock, NatMap.get?_insert]))
    obtain ⟨lb, hlb, -, hsize, hterm⟩ := closed_block hH hCt
    simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hterm
    obtain ⟨b₅, hb₅, hp₅, -⟩ := (Grows.ext (hg₆.trans hg) hC).cur ho₅
    obtain ⟨lb₅, hres₅, hlb₅⟩ := hH hb₅
    obtain ⟨hp₅', -, -⟩ := resolveBlock_ok hres₅
    have hstep := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl)
      (e := { target := off + (st.next + 1), args := [] }) (vals := []) (ρ' := ρl) hF hlb hsize.symm hterm.symm hxv
      rfl (by simp [Lir.holds_tz, hodd]) rfl (by simpa [wordSt] using hlb₅)
      (by simp [hp₅', hp₅, wordSt, Lir.bindParams])
    obtain ⟨le, hle, hreach⟩ := chainOr_reaches hF hH hxv h₂ hl₅ ho₅ hg hC himm hpick
    refine ⟨le, hle, hreach.prepend (Lir.star_of_step hstep) ?_⟩
    have := hl.cur
    simp [wordSt]
    omega

/-- The tag load reads the half-word at `x + 2`. -/
theorem exec_tag {ρl : Lir.Env} {mem : X86.Memory} {ctx : Word} {t x : Nat} {wx tagw : Word}
    (hx : ρl[x]? = some wx) (htag : mem.read? .w16 (wx + 2) = .ok tagw) :
    Lir.execList ρl mem ctx [tagStmt t x] = some (ρl.insert t tagw, mem) := by
  have ha : Lir.Addr.eval ρl ctx (Lower.mem x tagOffset) = some (wx + 2) := eval_mem hx 2
  simp only [Lir.execList, tagStmt, Lir.Stmt.exec, Lir.Rhs.eval, ha, Lir.loadWord, htag, Option.bind_eq_bind,
    Option.bind_some]

/-- The mixed shape on an even word: the low-bit test to the cell block,
the tag load, the tag chain. -/
theorem mixed_even {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {mem : X86.Memory} {ctx : Word} {rest : List Lir.Frame} {x : Nat} {cells imms : List (Lir.Arg × PEdge)}
    {dd : Option PEdge} {st st' stF : St}
    (h : (do
      let p ← newLabel
      let i ← newLabel
      close (.br .tz (.v x) (.imm 1) (loc p) (loc i))
      openAt p
      chainOr (← loadTag x) cells dd
      openAt i
      chainOr (.v x) imms dd : M Unit).run st = .ok ((), st'))
    (hl : Labels st) (ho : Open st) (hg : Grows st' stF) (hC : Ext C stF) {ρl : Lir.Env} {wx tagw : Word}
    (hx : ρl[x]? = some wx) (heven : wx &&& 1 = 0)
    (hexec : Lir.execList ρl mem ctx [tagStmt st.fresh x] = some (ρl.insert st.fresh tagw, mem))
    (hcell : ∀ t ∈ cells, ∃ w, t.1 = .imm w) {pe : PEdge} (hpick : chainOrPick tagw cells dd = some pe) :
    ∃ le ρl', resolveEdge f off starts pe = .ok le ∧ (ρl' = ρl ∨ ρl' = ρl.insert st.fresh tagw) ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        le ρl' := by
  have hxv : (Lir.Arg.v x).eval ρl = some wx := hx
  have htv : (Lir.Arg.v st.fresh).eval (ρl.insert st.fresh tagw) = some tagw := Lir.env_insert_self _ _ _
  obtain ⟨s₄, h₁, h₂⟩ := mixed_run h
  have hl₃ := labels_mixSt hl x
  have ho₃ := open_mixSt hl x
  obtain ⟨hg₄, hl₄, ho₄, -⟩ := chainOr_grows h₁ hl₃ ho₃
  have hk₄ : NewKeys (mixSt st x) s₄ := chainOr_keys h₁
  have hl₅ : Labels (wordSt st x s₄) :=
    { cur := by have := hg₄.next; simp [wordSt, mixSt, closeSt] at this ⊢; omega, done := hl₄.done }
  have ho₅ : Open (wordSt st x s₄) := by
    simp only [Open, wordSt]
    cases hj : s₄.done.get? (st.next + 1) with
    | none => rfl
    | some b =>
      rcases hk₄ hj with hj' | hj' | hj'
      · simp only [mixSt, closeSt, NatMap.get?_insert] at hj'
        split at hj'
        · have := hl.cur; omega
        · have := hl.done hj'; omega
      · simp [mixSt] at hj'
      · simp [mixSt, closeSt] at hj'
  have hg₅ : Grows s₄ (wordSt st x s₄) :=
    { next := Nat.le_refl _, fresh := Nat.le_refl _, done := id, cur := fun h => absurd h ho₄ }
  obtain ⟨hg₆, -, -, -⟩ := chainOr_grows h₂ hl₅ ho₅
  have hgF : Grows s₄ stF := (hg₅.trans hg₆).trans hg
  -- the low-bit test sends an even word to the cell block
  have hCt : C[st.cur]? = some (tzBlock st x) :=
    hC.done ((hg₄.trans hgF).done (by simp [mixSt, closeSt, tzBlock, NatMap.get?_insert]))
  obtain ⟨lb, hlb, -, hsize, hterm⟩ := closed_block hH hCt
  simp only [resolveTerm, resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hterm
  -- the cell block: its parameters are none, its body starts with the tag load
  let st₀ : St := { mixSt st x with acc := [], fresh := st.fresh }
  have ho₀ : Open st₀ := ho₃
  have hC₀ : Ext C { st₀ with acc := [tagStmt st.fresh x].reverse ++ st₀.acc, fresh := st.fresh + 1 } :=
    Grows.ext (hg₄.trans hgF) hC
  obtain ⟨lb₃, post, hlb₃, hp₃, -⟩ := holds_open hH [tagStmt st.fresh x] (st.fresh + 1) hC₀ ho₀
  have hstep := Lir.br_at (p := lp) (mem := mem) (ctx := ctx) (rest := rest) (ρ := ρl)
    (e := { target := off + st.next, args := [] }) (vals := []) (ρ' := ρl) hF hlb hsize.symm hterm.symm hxv
    rfl (by simp [Lir.holds_tz, heven]) rfl (by simpa [st₀, mixSt] using hlb₃)
    (by simp [hp₃, st₀, mixSt, Lir.bindParams])
  have hstar := straight_star (lp := lp) (ctx := ctx) (rest := rest) hF hH (st := st₀) (ss := [tagStmt st.fresh x])
    (f' := st.fresh + 1) hC₀ ho₀ (by simp [tagStmt, Lir.Stmt.isCall]) hexec
  obtain ⟨le, hle, hr⟩ := chainOr_reaches hF hH htv h₁ hl₃ ho₃ (hg₅.trans hg₆ |>.trans hg) hC hcell hpick
  refine ⟨le, _, hle, .inr rfl, (hr.prepend (low := off + st.next) hstar (by simp [st₀, mixSt])).prepend
    (Lir.star_of_step hstep) ?_⟩
  have := hl.cur
  simp [st₀, mixSt]
  omega

/-- **A cell's even word takes the tag chain's pick** (or the word
chain's, where the switch has no cell keys). -/
theorem tagSwitch_even {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {mem : X86.Memory} {ctx : Word} {rest : List Lir.Frame} {x : Nat} {es : List (KeyKind × PEdge)}
    {dd : Option PEdge} {st st' stF : St} (h : (tagSwitch x es dd).run st = .ok ((), st')) (hl : Labels st)
    (ho : Open st) (hg : Grows st' stF) (hC : Ext C stF) {ρl : Lir.Env} {wx tagw : Word} (hx : ρl[x]? = some wx)
    (heven : wx &&& 1 = 0) (htag : mem.read? .w16 (wx + 2) = .ok tagw) {pe : PEdge}
    (hpick : (if cellTests es = [] then chainOrPick wx (immTests es) dd else chainOrPick tagw (cellTests es) dd) =
      some pe) :
    ∃ le ρl', resolveEdge f off starts pe = .ok le ∧ (ρl' = ρl ∨ ρl' = ρl.insert st.fresh tagw) ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        le ρl' := by
  have hxv : (Lir.Arg.v x).eval ρl = some wx := hx
  have htv : (Lir.Arg.v st.fresh).eval (ρl.insert st.fresh tagw) = some tagw := Lir.env_insert_self _ _ _
  have himm : ∀ t ∈ immTests es, ∃ w, t.1 = .imm w := by
    intro t ht
    simp only [immTests, List.mem_filterMap] at ht
    obtain ⟨⟨k, e⟩, -, hk⟩ := ht
    cases k <;> simp only [immTest, cellTest, Option.some.injEq, reduceCtorEq] at hk <;> subst hk <;> exact ⟨_, rfl⟩
  have hcell : ∀ t ∈ cellTests es, ∃ w, t.1 = .imm w := by
    intro t ht
    simp only [cellTests, List.mem_filterMap] at ht
    obtain ⟨⟨k, e⟩, -, hk⟩ := ht
    cases k <;> simp only [immTest, cellTest, Option.some.injEq, reduceCtorEq] at hk <;> subst hk <;> exact ⟨_, rfl⟩
  have hexec := exec_tag (ctx := ctx) (t := st.fresh) hx htag
  cases hc : cellTests es with
  | nil =>
    simp only [hc, ↓reduceIte] at hpick
    simp only [tagSwitch, hc] at h
    obtain ⟨le, hle, hr⟩ := chainOr_reaches hF hH hxv h hl ho hg hC himm hpick
    exact ⟨le, ρl, hle, .inl rfl, hr⟩
  | cons c cs =>
    simp only [hc, reduceCtorEq, ↓reduceIte] at hpick
    rw [hc] at hcell
    cases hi : immTests es with
    | nil =>
      cases dd with
      | none =>
        -- cells only: load the tag in this block
        simp only [tagSwitch, hc, hi] at h
        have h' := cellsOnly_run h
        have hl₁ : Labels (loadSt st x) := labels_acc _ _ hl
        have ho₁ : Open (loadSt st x) := open_acc _ _ ho
        obtain ⟨hg₁, -, -, -⟩ := chainOr_grows h' hl₁ ho₁
        obtain ⟨le, hle, hr⟩ := chainOr_reaches hF hH htv h' hl₁ ho₁ hg hC hcell hpick
        have hstar := straight_star (lp := lp) (ctx := ctx) (rest := rest) hF hH
          (st := st) (ss := [tagStmt st.fresh x]) (f' := st.fresh + 1) (Grows.ext (hg₁.trans hg) hC) ho
          (by simp [tagStmt, Lir.Stmt.isCall]) hexec
        refine ⟨le, _, hle, .inr rfl, hr.prepend hstar ?_⟩
        simp [loadSt]
      | some d =>
        have hmix : (do
            let p ← newLabel
            let i ← newLabel
            close (.br .tz (.v x) (.imm 1) (loc p) (loc i))
            openAt p
            chainOr (← loadTag x) (c :: cs) (some d)
            openAt i
            chainOr (.v x) (immTests es) (some d) : M Unit).run st = .ok ((), st') := by
          simp only [tagSwitch, hc, hi] at h; rw [hi]; exact h
        exact mixed_even hF hH hmix hl ho hg hC hx heven hexec hcell hpick
    | cons i is =>
      have hmix : (do
          let p ← newLabel
          let i ← newLabel
          close (.br .tz (.v x) (.imm 1) (loc p) (loc i))
          openAt p
          chainOr (← loadTag x) (c :: cs) dd
          openAt i
          chainOr (.v x) (immTests es) dd : M Unit).run st = .ok ((), st') := by
        simp only [tagSwitch, hc, hi] at h; rw [hi]; exact h
      exact mixed_even hF hH hmix hl ho hg hC hx heven hexec hcell hpick

end Compilatrix.Rt.Proof
