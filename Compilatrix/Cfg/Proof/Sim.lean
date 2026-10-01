import Compilatrix.Cfg.Proof.Step
import Compilatrix.Own.Proof.Mono

/-! # The Own → Cfg simulation

Own (big-step, depth clock) against `Cfg.lower` (small-step, total clock),
by a CPS forward lemma quantified over the continuation stack
(`eval_reach`, as `Toy.Stack.eval_fwd`): from a Cfg frame that runs the
Own code (`At`), the Cfg run does what `Reach` asks of Own's outcome: a
value is returned to the stack, a trap traps, and a depth-`k` timeout
spends more than `k` charges.

**The frame relation `At`** follows `count`'s block layout (`Impl`): the
frame is in the block lowering `c` writes, with the rest of the block's
instructions (`spine c`, the `bind`s along `c`'s join-point scopes) still
to run. Join points: Own's stack and the lowering's scope correspond entry
by entry (`JC`): the entry's body is implemented by its block, with the
back flag Own's `charged` flag. Environments: Own's environment is included
in Cfg's frame environment (`Sub`); Cfg keeps every binding of the
activation, so a later binding must never overwrite one Own still reads.
That is what `Scoped` guarantees: every variable code binds is at least a
bound `lo` above every variable of Own's environment and of the join
entries' environments (`Below`), as the lowering's name supply provides. -/

set_option autoImplicit false

namespace Compilatrix.Cfg.Proof

open Compilatrix.Sem (Result Star)
open Compilatrix.Own (RVal Heap AllocPol Env)
open Compilatrix.Fir (Var FunId JoinId Arg)
open Compilatrix.Cfg.Lower

/-! ## Code shape -/

/-- The instructions lowering `c` puts in the current block. -/
def spine : Own.Code → List Instr
  | .bind x r k => .bind x r :: spine k
  | .jp _ _ _ _ _ k => spine k
  | _ => []

/-- The block `cur` holds the instructions so far and `c`'s spine. -/
theorem impl_head {B : Blocks} {self : FunId} :
    ∀ {J : JScope} {cur : BlockId} {params : List (Var × Own.PSig)} {acc : List Instr} {next : BlockId}
      {c : Own.Code}, Impl B self J cur params acc next c →
      ∃ t, B cur = some { params, body := acc.reverse ++ spine c, term := t }
  | _, _, _, _, _, .bind x r k, h => by
    obtain ⟨t, ht⟩ := impl_head (c := k) h
    exact ⟨t, by simpa [spine] using ht⟩
  | _, _, _, _, _, .jp j ps φ r b k, h => by
    obtain ⟨t, ht⟩ := impl_head h.1
    exact ⟨t, by simpa [spine] using ht⟩
  | _, _, _, _, _, .jmp .., h => ⟨_, by simp only [Impl] at h; simpa [spine] using h⟩
  | _, _, _, _, _, .case .., h => ⟨_, by simp only [Impl] at h; simpa [spine] using h.1⟩
  | _, _, _, _, _, .ret _, h => ⟨_, by simp only [Impl] at h; simpa [spine] using h⟩
  | _, _, _, _, _, .tcall .., h => ⟨_, by simp only [Impl] at h; simpa [spine] using h⟩
  | _, _, _, _, _, .trap, h => ⟨_, by simp only [Impl] at h; simpa [spine] using h⟩

/-! ## Names -/

mutual

/-- Every variable `c` binds is at least `lo`, and a join point's body binds
above its parameters. -/
def Scoped : Nat → Own.Code → Prop
  | lo, .bind x _ k => lo ≤ x ∧ Scoped (x + 1) k
  | lo, .jp _ ps _ _ b k =>
    (∀ p ∈ ps, lo ≤ p.1) ∧ (∃ lo', lo ≤ lo' ∧ (∀ p ∈ ps, p.1 < lo') ∧ Scoped lo' b) ∧ Scoped lo k
  | lo, .case _ alts d => ScopedAlts lo alts ∧ ScopedOpt lo d
  | _, .jmp .. | _, .ret _ | _, .tcall .. | _, .trap => True

def ScopedAlts : Nat → List Own.Alt → Prop
  | _, [] => True
  | lo, .mk _ b :: as => Scoped lo b ∧ ScopedAlts lo as

def ScopedOpt : Nat → Option Own.Code → Prop
  | _, none => True
  | lo, some c => Scoped lo c

end

/-- Own's environment is included in Cfg's. -/
def Sub (ρ ρ' : Env) : Prop := ∀ x v, ρ.get? x = some v → ρ'.get? x = some v

/-- Every variable of an environment is below `lo`. -/
def Below (lo : Nat) (ρ : Env) : Prop := ∀ x v, ρ.get? x = some v → x < lo

theorem Sub.refl (ρ : Env) : Sub ρ ρ := fun _ _ h => h

theorem sub_leaf (ρ : Env) : Sub .leaf ρ := fun _ _ h => by simp [Src.NatMap.get?] at h

theorem Sub.insert {ρ ρ' : Env} (h : Sub ρ ρ') (x : Var) (v : RVal) : Sub (ρ.insert x v) (ρ'.insert x v) := by
  intro y w hy
  by_cases hyx : y = x
  · subst hyx; rw [Src.NatMap.get?_insert_self] at hy ⊢; exact hy
  · rw [Src.NatMap.get?_insert_ne _ _ hyx] at hy ⊢; exact h y w hy

theorem Sub.bindAll {ρ ρ' : Env} (h : Sub ρ ρ') :
    ∀ (xs : List Var) (vs : List RVal), Sub (Own.bindAll ρ xs vs) (Own.bindAll ρ' xs vs)
  | [], vs => by cases vs <;> exact h
  | _ :: _, [] => h
  | x :: xs, v :: vs => (h.insert x v).bindAll xs vs

theorem bindAll_get_notin {ρ : Env} {x : Var} :
    ∀ {xs : List Var} {vs : List RVal}, x ∉ xs → (Own.bindAll ρ xs vs).get? x = ρ.get? x
  | [], vs, _ => by cases vs <;> rfl
  | _ :: _, [], _ => rfl
  | y :: xs, v :: vs, hx => by
    simp only [List.mem_cons, not_or] at hx
    simp only [Own.bindAll]
    rw [bindAll_get_notin hx.2, Src.NatMap.get?_insert_ne _ _ hx.1]

theorem bindAll_get_mem {ρ : Env} {x : Var} :
    ∀ {xs : List Var} {vs : List RVal}, xs.length = vs.length → x ∈ xs → ∃ v, (Own.bindAll ρ xs vs).get? x = some v
  | [], _, _, h => by cases h
  | _ :: _, [], hl, _ => by simp at hl
  | y :: xs, v :: vs, hl, hx => by
    simp only [Own.bindAll]
    by_cases hxs : x ∈ xs
    · exact bindAll_get_mem (by simpa using hl) hxs
    · have : x = y := by simpa [hxs] using hx
      subst this
      exact ⟨v, by rw [bindAll_get_notin hxs, Src.NatMap.get?_insert_self]⟩

theorem below_bindAll {lo : Nat} {ρ : Env} (h : Below lo ρ) {xs : List Var} (hxs : ∀ x ∈ xs, x < lo)
    (vs : List RVal) : Below lo (Own.bindAll ρ xs vs) := by
  intro y w hy
  by_cases hyx : y ∈ xs
  · exact hxs y hyx
  · rw [bindAll_get_notin hyx] at hy; exact h y w hy

theorem below_leaf (lo : Nat) : Below lo .leaf := fun _ _ h => by simp [Src.NatMap.get?] at h

/-! ## Join points -/

/-- Own's join stack against the lowering's join scope, entry by entry,
with the bounds that keep their environments from being overwritten:
entries deeper in the stack were defined below lower bounds. -/
inductive JC (B : Blocks) (self : FunId) (ρc : Env) : Nat → JScope → List Own.JEntry → Prop
  | nil {lo : Nat} : JC B self ρc lo [] []
  | cons {lo loₑ lo_b : Nat} {bj : BlockId} {Jc : JScope} {e : Own.JEntry} {Jo : List Own.JEntry}
      {ps : List (Var × Own.PSig)} :
      JC B self ρc loₑ Jc Jo → loₑ ≤ lo → e.params = ps.map (·.1) → (e.charged = true → e.isRec = true) →
      Impl B self (if e.isRec then (e.id, bj, true) :: Jc else Jc) bj ps [] (bj + 1) e.body →
      Sub e.env ρc → Below loₑ e.env → (∀ p ∈ ps, loₑ ≤ p.1) → loₑ ≤ lo_b → (∀ p ∈ ps, p.1 < lo_b) →
      Scoped lo_b e.body → JC B self ρc lo ((e.id, bj, e.charged) :: Jc) (e :: Jo)

namespace JC

variable {B : Blocks} {self : FunId}

theorem mono {ρc : Env} {lo lo' : Nat} {Jc : JScope} {Jo : List Own.JEntry} (h : JC B self ρc lo Jc Jo)
    (hle : lo ≤ lo') : JC B self ρc lo' Jc Jo := by
  cases h with
  | nil => exact .nil
  | cons hr hlo hp hc hi hs hb hps hlb hpb hsc => exact .cons hr (Nat.le_trans hlo hle) hp hc hi hs hb hps hlb hpb hsc

/-- Changing Cfg's environment only at or above `lo` keeps the stack. -/
theorem agree {ρc ρc' : Env} {lo : Nat} {Jc : JScope} {Jo : List Own.JEntry} (h : JC B self ρc lo Jc Jo)
    (ha : ∀ x, x < lo → ρc'.get? x = ρc.get? x) : JC B self ρc' lo Jc Jo := by
  induction h with
  | nil => exact .nil
  | @cons lo loₑ lo_b bj Jc e Jo ps hr hlo hp hc hi hs hb hps hlb hpb hsc ih =>
    refine .cons (ih fun x hx => ha x (by cfg_omega)) hlo hp hc hi (fun x v hx => ?_) hb hps hlb hpb hsc
    rw [ha x (by have := hb x v hx; cfg_omega)]
    exact hs x v hx

/-- A jump: Own's lookup and the lowering's scope find the same entry. -/
theorem lookup {ρc : Env} {lo : Nat} {Jc : JScope} {Jo : List Own.JEntry} (h : JC B self ρc lo Jc Jo)
    {j : JoinId} {e : Own.JEntry} {rest : List Own.JEntry} (hl : Own.lookupJ j Jo = some (e, rest)) :
    ∃ bj Jc' ps loₑ lo_b, Jc.lookup j = some (bj, e.charged) ∧ e.id = j ∧ JC B self ρc loₑ Jc' rest ∧
      loₑ ≤ lo ∧ e.params = ps.map (·.1) ∧ (e.charged = true → e.isRec = true) ∧
      Impl B self (if e.isRec then (e.id, bj, true) :: Jc' else Jc') bj ps [] (bj + 1) e.body ∧
      Sub e.env ρc ∧ Below loₑ e.env ∧ (∀ p ∈ ps, loₑ ≤ p.1) ∧ loₑ ≤ lo_b ∧ (∀ p ∈ ps, p.1 < lo_b) ∧
      Scoped lo_b e.body := by
  induction h generalizing e rest with
  | nil => simp [Own.lookupJ] at hl
  | @cons lo loₑ lo_b bj Jc e' Jo ps hr hlo hp hc hi hs hb hps hlb hpb hsc ih =>
    simp only [Own.lookupJ] at hl
    split at hl
    · next hid =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      refine ⟨bj, Jc, ps, loₑ, lo_b, ?_, hid, hr, hlo, hp, hc, hi, hs, hb, hps, hlb, hpb, hsc⟩
      simp [List.lookup, hid]
    · next hid =>
      obtain ⟨bj', Jc', ps', lo₁, lo₂, hlk, hid', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ := ih hl
      refine ⟨bj', Jc', ps', lo₁, lo₂, ?_, hid', h₁, by cfg_omega, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩
      have : (j == e'.id) = false := by simpa using fun h => hid h.symm
      simp [List.lookup, this, hlk]

end JC

/-! ## The frame relation -/

/-- What the simulation needs of the Own program: functions below its size,
signatures as long as the parameters, and names bound above the parameters
and the environments in scope (`Scoped`). -/
structure Good (q : Own.Program) : Prop where
  dense : ∀ {f : FunId} {fd : Own.Fun}, q.fun? f = some fd → f < q.size
  sigLen : ∀ {f : FunId} {fd : Own.Fun}, q.fun? f = some fd → fd.sig.params.length = fd.params.length
  names : ∀ {f : FunId} {fd : Own.Fun}, q.fun? f = some fd →
    ∃ lo, (∀ p ∈ fd.params, p < lo) ∧ Scoped lo fd.body

/-- The Cfg frame `fr` runs Own code `c` with Own's environment `ρo` and
join stack `Jo` (see the module comment). -/
def At (q : Own.Program) (fr : Frame) (ρo : Env) (Jo : List Own.JEntry) (c : Own.Code) : Prop :=
  ∃ (fd : Own.Fun) (Jc : JScope) (params : List (Var × Own.PSig)) (acc : List Instr) (next : BlockId) (lo : Nat),
    q.fun? fr.fn = some fd ∧ fr.fn < q.size ∧
    Impl (Lower.function fr.fn fd).block? fr.fn Jc fr.blk params acc next c ∧ fr.rest = spine c ∧
    Sub ρo fr.env ∧ Below lo ρo ∧ Scoped lo c ∧ JC (Lower.function fr.fn fd).block? fr.fn fr.env lo Jc Jo

/-! ## Right-hand sides under a larger environment -/

theorem evalArg_sub {ρ ρ' : Env} (h : Sub ρ ρ') {a : Arg} {v : RVal} (ha : Own.evalArg ρ a = some v) :
    Own.evalArg ρ' a = some v := by
  cases a with
  | var x => exact h x v ha
  | lit l => exact ha
  | erased => exact ha

theorem evalArgs_sub {ρ ρ' : Env} (h : Sub ρ ρ') :
    ∀ {as : List Arg} {vs : List RVal}, Own.evalArgs ρ as = some vs → Own.evalArgs ρ' as = some vs
  | [], _, ha => ha
  | a :: as, vs, ha => by
    rw [Own.evalArgs_cons] at ha ⊢
    cases hv : Own.evalArg ρ a with
    | none => rw [hv] at ha; cases ha
    | some v =>
      rw [hv] at ha
      rw [evalArg_sub h hv]
      cases hvs : Own.evalArgs ρ as with
      | none => rw [hvs] at ha; cases ha
      | some vs' => rw [hvs] at ha; rw [evalArgs_sub h hvs]; exact ha


theorem primResult_cases (T : Own.Tables) (op : Lam.Prim) (vs : List RVal) :
    Own.primResult T op vs = .stuck ∨ ∃ v, Own.primResult T op vs = .ok v := by
  unfold Own.primResult
  split
  · split
    · exact .inr ⟨_, rfl⟩
    · split
      · cases Own.ctor0Of T _ with
        | none => exact .inl rfl
        | some v => exact .inr ⟨v, rfl⟩
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

/-- A right-hand side is a value or stuck. -/
theorem evalRhs_cases (pol : AllocPol) (T : Own.Tables) (ρ : Env) (H : Heap) (r : Own.Rhs) :
    Own.evalRhs pol T ρ H r = .stuck ∨ ∃ p, Own.evalRhs pol T ρ H r = .ok p := by
  cases r with
  | fir e =>
    cases e with
    | arg a =>
      simp only [Own.evalRhs]
      cases Own.evalArg ρ a with
      | none => exact .inl rfl
      | some v => exact .inr ⟨_, rfl⟩
    | prim op as =>
      simp only [Own.evalRhs]
      cases Own.evalArgs ρ as with
      | none => exact .inl rfl
      | some vs =>
        rcases primResult_cases T op vs with h | ⟨v, h⟩
        · exact .inl (by simp [h, Result.map, Result.bind])
        · exact .inr ⟨(v, H), by simp [h, Result.map]⟩
    | _ => exact .inl rfl
  | alloc c as κ =>
    simp only [Own.evalRhs]
    cases Own.evalArgs ρ as with
    | none => exact .inl rfl
    | some vs =>
      by_cases hl : vs.length = c.arity
      · by_cases hfl : c.fieldless = true
        · exact .inr ⟨(RVal.ctor0 c, H), by simp [hl, hfl]⟩
        · exact .inr ⟨H.alloc pol { ctor := c, fields := vs }, by simp [hl, hfl]⟩
      · exact .inl (by simp [hl])
  | proj x c i =>
    simp only [Own.evalRhs]
    cases ρ.get? x with
    | none => exact .inl rfl
    | some v =>
      simp only
      cases v.asCtor T.known H with
      | none => exact .inl rfl
      | some p =>
        obtain ⟨c', fs⟩ := p
        simp only
        by_cases hc : c' = c
        · cases hfi : fs[i]? with
          | none => exact .inl (by simp [hc, Result.ofOption, Result.map, Result.bind])
          | some w => exact .inr ⟨(w, H), by simp [hc, Result.ofOption, Result.map]⟩
        · exact .inl (by simp [hc])

/-- A larger environment gives the same value. -/
theorem evalRhs_sub_ok {pol : AllocPol} {T : Own.Tables} {ρ ρ' : Env} (h : Sub ρ ρ') {H : Heap}
    {r : Own.Rhs} {p : RVal × Heap} (he : Own.evalRhs pol T ρ H r = .ok p) :
    Own.evalRhs pol T ρ' H r = .ok p := by
  cases r with
  | fir e =>
    cases e with
    | arg a =>
      simp only [Own.evalRhs] at he ⊢
      cases ha : Own.evalArg ρ a with
      | none => rw [ha] at he; cases he
      | some v => rw [ha] at he; rw [evalArg_sub h ha]; exact he
    | prim op as =>
      simp only [Own.evalRhs] at he ⊢
      cases has : Own.evalArgs ρ as with
      | none => rw [has] at he; cases he
      | some vs => rw [has] at he; rw [evalArgs_sub h has]; exact he
    | _ => simp [Own.evalRhs] at he
  | alloc c as κ =>
    simp only [Own.evalRhs] at he ⊢
    cases has : Own.evalArgs ρ as with
    | none => rw [has] at he; cases he
    | some vs => rw [has] at he; rw [evalArgs_sub h has]; exact he
  | proj x c i =>
    simp only [Own.evalRhs] at he ⊢
    cases hx : ρ.get? x with
    | none => rw [hx] at he; cases he
    | some v => rw [hx] at he; rw [h x v hx]; exact he

/-! ## Entering a function -/

/-- Block 0 of a lowered function: the function's parameters and the
body's spine. -/
theorem block_zero (f : FunId) (fd : Own.Fun) :
    ∃ t, (Lower.function f fd).block? 0 =
      some { params := fd.params.zip fd.sig.params, body := spine fd.body, term := t } := by
  obtain ⟨t, ht⟩ := impl_head (function_impl f fd)
  exact ⟨t, by simpa using ht⟩

theorem zip_fst {fd : Own.Fun} (h : fd.sig.params.length = fd.params.length) :
    (fd.params.zip fd.sig.params).map (·.1) = fd.params :=
  List.map_fst_zip (by cfg_omega)

/-- A frame entering function `f`'s body from any environment its
parameters are bound in. -/
theorem at_entry {q : Own.Program} (G : Good q) {f : FunId} {fd : Own.Fun} (hf : q.fun? f = some fd)
    (ρb : Env) (vs : List RVal) (fr : Frame) (hfn : fr.fn = f) (hblk : fr.blk = 0)
    (hrest : fr.rest = spine fd.body) (henv : fr.env = Own.bindAll ρb fd.params vs) :
    At q fr (Own.bindAll .leaf fd.params vs) [] fd.body := by
  obtain ⟨lo, hlo, hsc⟩ := G.names hf
  subst hfn
  refine ⟨fd, [], fd.params.zip fd.sig.params, [], 1, lo, hf, G.dense hf, ?_, hrest, ?_, ?_, hsc, .nil⟩
  · rw [hblk]; exact function_impl fr.fn fd
  · rw [henv]; exact (sub_leaf ρb).bindAll _ _
  · exact below_bindAll (below_leaf lo) hlo vs

/-! ## The simulation -/

section

variable {pol : AllocPol} {q : Own.Program} (G : Good q) {k : Nat}
  (ih : ∀ k' < k, ∀ (fr : Frame) (ρo : Env) (Jo : List Own.JEntry) (H : Heap) (c : Own.Code)
    (stk : List (Frame × Var)), At q fr ρo Jo c →
    Reach pol (lower q) k' (.run fr stk H) stk (Own.eval pol q k' ρo Jo H c))
include G ih

omit ih in
theorem lower_fun_of {f : FunId} {fd : Own.Fun} (hf : q.fun? f = some fd) :
    (lower q).fun? f = some (Lower.function f fd) := by
  rw [lower_fun?]; simp [G.dense hf, hf]

/-- **A call**: the entry charge, then the callee's body. -/
theorem call_reach (f : FunId) (vs : List RVal) (stk : List (Frame × Var)) (H : Heap) :
    Reach pol (lower q) k (.call f vs stk H) stk (Own.evalCall pol q k f vs H) := by
  rw [Own.evalCall_eq]
  cases hf : q.fun? f with
  | none => exact Reach.stuck
  | some fd =>
    simp only [Result.ofOption, Result.bind_ok, Own.callFun]
    by_cases hl : vs.length = fd.params.length
    · simp only [hl, ↓reduceIte]
      obtain ⟨t, hb⟩ := block_zero f fd
      have hsig := G.sigLen hf
      refine Reach.charge (step_call (lower_fun_of G hf) hb (by simp [hl, hsig])) fun k' hk => ?_
      refine ih k' (by cfg_omega) _ _ [] H fd.body stk (at_entry G hf .leaf vs _ rfl rfl rfl ?_)
      simp only [zip_fst hsig]
    · simp only [hl, ↓reduceIte]
      exact Reach.stuck

set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
mutual

/-- **The forward lemma**, over every continuation stack. -/
theorem eval_reach (fr : Frame) (ρo : Env) (Jo : List Own.JEntry) (H : Heap) (c : Own.Code)
    (stk : List (Frame × Var)) (hat : At q fr ρo Jo c) :
    Reach pol (lower q) k (.run fr stk H) stk (Own.eval pol q k ρo Jo H c) := by
  match c with
  | .bind x r c' =>
    obtain ⟨fd, Jc, params, acc, next, lo, hf, hs, himpl, hrest, hsub, hbelow, hsc, hjc⟩ := hat
    have hfun := lower_fun_of G hf
    simp only [Impl] at himpl
    simp only [spine] at hrest
    simp only [Scoped] at hsc
    have hat' : ∀ v, At q { fr with rest := spine c', env := fr.env.insert x v } (ρo.insert x v) Jo c' := by
      intro v
      refine ⟨fd, Jc, params, _, next, x + 1, hf, hs, himpl, rfl, hsub.insert x v, ?_, hsc.2, ?_⟩
      · intro y w hy
        by_cases hyx : y = x
        · cfg_omega
        · rw [Src.NatMap.get?_insert_ne _ _ hyx] at hy; have := hbelow y w hy; cfg_omega
      · refine (hjc.agree fun y hy => ?_).mono (by cfg_omega)
        exact Src.NatMap.get?_insert_ne _ _ (by cfg_omega)
    by_cases hr : ∃ f as, r = .fir (.call f as)
    · obtain ⟨f, as, rfl⟩ := hr
      rw [Own.eval_bindCall]
      cases hv : Own.evalArgs ρo as with
      | none => exact Reach.stuck
      | some vs =>
        simp only [Result.ofOption, Result.bind_ok]
        exact Reach.call (step_run_call hrest (evalArgs_sub hsub hv)) (call_reach G ih f vs _ H)
          fun v H' _ => eval_reach _ _ Jo H' c' stk (hat' v)
    · have hr' : ∀ f as, r ≠ .fir (.call f as) := fun f as h => hr ⟨f, as, h⟩
      rw [Own.eval_bindRhs _ _ _ _ _ _ _ _ _ hr']
      rcases evalRhs_cases pol q.tables ρo H r with he | ⟨p, he⟩
      · rw [he]; exact Reach.stuck
      · rw [he, Result.bind_ok]
        have he' : Own.evalRhs pol (lower q).tables fr.env H r = .ok p := evalRhs_sub_ok hsub he
        refine Reach.free ?_ (eval_reach _ _ Jo p.2 c' stk (hat' p.1))
        rw [step_run_bind hrest hr', he']
  | .jp j ps φ r b c' =>
    obtain ⟨fd, Jc, params, acc, next, lo, hf, hs, himpl, hrest, hsub, hbelow, hsc, hjc⟩ := hat
    simp only [Impl] at himpl
    simp only [spine] at hrest
    simp only [Scoped] at hsc
    obtain ⟨hps, ⟨lo', hlo', hpl, hscb⟩, hsck⟩ := hsc
    rw [Own.eval_jp]
    refine eval_reach fr ρo _ H c' stk ⟨fd, _, params, acc, next, lo, hf, hs, himpl.1, hrest, hsub, hbelow, hsck,
      ?_⟩
    exact .cons (e := { id := j, charged := false, env := ρo, params := ps.map (·.1), body := b, isRec := r })
      (ps := ps) hjc (Nat.le_refl lo) rfl (fun h => by cases h) himpl.2 hsub hbelow hps hlo' hpl hscb
  | .jmp j as =>
    obtain ⟨fd, Jc, params, acc, next, lo, hf, hs, himpl, hrest, hsub, hbelow, hsc, hjc⟩ := hat
    have hfun := lower_fun_of G hf
    simp only [Impl] at himpl
    simp only [spine] at hrest
    rw [Own.eval_jmp]
    cases hl : Own.lookupJ j Jo with
    | none => exact Reach.stuck
    | some p =>
      obtain ⟨e, rest⟩ := p
      simp only [Result.ofOption, Result.bind_ok]
      obtain ⟨bj, Jc', ps, loₑ, lo_b, hlk, hid, hjc', hloₑ, hpe, hch, hib, hse, hbe, hpsₑ, hlob, hpb, hscb⟩ :=
        hjc.lookup hl
      cases hv : Own.evalArgs ρo as with
      | none => exact Reach.stuck
      | some vs =>
        simp only [Result.bind_ok]
        unfold Own.jumpTo
        by_cases hlen : vs.length = e.params.length
        · simp only [hlen, ↓reduceIte]
          obtain ⟨t, htb⟩ := impl_head hib
          have hlen' : vs.length = ps.length := by rw [hlen, hpe]; simp
          have hstep : step pol (lower q) (.run fr stk H) =
              .next (.run { fr with blk := bj, rest := spine e.body, env := Own.bindAll fr.env (ps.map (·.1)) vs }
                stk H) e.charged := by
            rw [step_run_term hrest hfun himpl]
            simp only [termStep, jumpTerm, hlk]
            rw [takeEdge_eq htb (evalArgs_sub hsub hv) hlen']
            simp
          have hat' : At q { fr with blk := bj, rest := spine e.body, env := Own.bindAll fr.env (ps.map (·.1)) vs }
              (Own.bindAll e.env e.params vs) (e.after rest) e.body := by
            refine ⟨fd, _, ps, [], bj + 1, lo_b, hf, hs, hib, rfl, ?_, ?_, hscb, ?_⟩
            · rw [hpe]; exact hse.bindAll _ _
            · refine below_bindAll (fun y w hy => by have := hbe y w hy; cfg_omega) ?_ vs
              intro y hy; rw [hpe] at hy
              obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
              exact hpb p hp
            · have hag : ∀ y, y < loₑ → (Own.bindAll fr.env (ps.map (·.1)) vs).get? y = fr.env.get? y := by
                intro y hy
                refine bindAll_get_notin fun hm => ?_
                obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
                have := hpsₑ p hp; cfg_omega
              have hrest' := (hjc'.agree hag).mono hlob
              unfold Own.JEntry.after
              cases hr : e.isRec with
              | false => simpa [hr] using hrest'
              | true =>
                simp only [↓reduceIte]
                have := JC.cons (e := { e with charged := true }) (ps := ps) (bj := bj) (hjc'.agree hag) hlob hpe
                  (fun _ => hr) (by simpa [hr] using hib) (fun y w hy => by
                    rw [hag y (by have := hbe y w hy; cfg_omega)]; exact hse y w hy) hbe hpsₑ hlob hpb hscb
                simpa [hr] using this
          cases hc : e.charged with
          | true =>
            simp only [↓reduceIte]
            exact Reach.charge (by rw [hstep, hc]) fun k' hk => ih k' (by cfg_omega) _ _ _ H e.body stk hat'
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            have := Own.jump_measure hl hc
            exact Reach.free (by rw [hstep, hc]) (eval_reach _ _ _ H e.body stk hat')
        · simp only [hlen, ↓reduceIte]
          exact Reach.stuck
  | .case x alts d =>
    obtain ⟨fd, Jc, params, acc, next, lo, hf, hs, himpl, hrest, hsub, hbelow, hsc, hjc⟩ := hat
    have hfun := lower_fun_of G hf
    simp only [Impl] at himpl
    simp only [spine] at hrest
    simp only [Scoped] at hsc
    rw [Own.eval_case]
    cases hx : ρo.get? x with
    | none => exact Reach.stuck
    | some v =>
      simp only [Result.ofOption, Result.bind_ok]
      cases hac : v.asCtor q.known H with
      | none => exact Reach.stuck
      | some p =>
        obtain ⟨key, fs⟩ := p
        simp only
        refine alts_reach fr ρo Jo H stk key alts d next fd Jc lo hf hs hrest himpl.2.1 himpl.2.2 hsc.1 hsc.2 hsub
          hbelow hjc ?_
        rw [step_run_term hrest hfun himpl.1]
        simp only [termStep, caseTerm, hsub x v hx]
        have : v.asCtor (lower q).known H = some (key, fs) := hac
        simp only [this]
        rfl
  | .ret a =>
    obtain ⟨fd, Jc, params, acc, next, lo, hf, hs, himpl, hrest, hsub, hbelow, hsc, hjc⟩ := hat
    have hfun := lower_fun_of G hf
    simp only [Impl] at himpl
    simp only [spine] at hrest
    rw [Own.eval_ret]
    cases ha : Own.evalArg ρo a with
    | none => exact Reach.stuck
    | some v =>
      simp only [Result.ofOption, Result.bind_ok]
      refine ⟨0, .free ?_ (.refl _)⟩
      rw [step_run_term hrest hfun himpl]
      simp only [termStep, evalArg_sub hsub ha]
  | .tcall f as =>
    obtain ⟨fd, Jc, params, acc, next, lo, hf, hs, himpl, hrest, hsub, hbelow, hsc, hjc⟩ := hat
    have hfun := lower_fun_of G hf
    simp only [Impl] at himpl
    simp only [spine] at hrest
    rw [Own.eval_tcall]
    cases hv : Own.evalArgs ρo as with
    | none => exact Reach.stuck
    | some vs =>
      simp only [Result.ofOption, Result.bind_ok]
      by_cases hself : f = fr.fn
      · subst hself
        rw [Own.evalCall_eq, hf]
        simp only [Result.ofOption, Result.bind_ok, Own.callFun]
        by_cases hl : vs.length = fd.params.length
        · simp only [hl, ↓reduceIte]
          obtain ⟨t, hb⟩ := block_zero fr.fn fd
          have hsig := G.sigLen hf
          let fr' : Frame :=
            { fr with blk := 0, rest := spine fd.body, env := Own.bindAll fr.env (fd.params.zip fd.sig.params |>.map (·.1)) vs }
          refine Reach.charge (s' := .run fr' stk H) ?_ fun k' hk => ih k' (by cfg_omega) _ _ [] H fd.body stk
            (at_entry G hf fr.env vs fr' rfl rfl rfl (by simp only [fr', zip_fst hsig]))
          rw [step_run_term hrest hfun himpl]
          simp only [termStep, tcallTerm, ↓reduceIte]
          rw [takeEdge_eq hb (evalArgs_sub hsub hv) (by simp [hl, hsig])]
        · simp only [hl, ↓reduceIte]
          exact Reach.stuck
      · refine Reach.free ?_ (call_reach G ih f vs stk H)
        rw [step_run_term hrest hfun himpl]
        simp only [termStep, tcallTerm, hself, ↓reduceIte, evalArgs_sub hsub hv]
  | .trap =>
    obtain ⟨fd, Jc, params, acc, next, lo, hf, hs, himpl, hrest, hsub, hbelow, hsc, hjc⟩ := hat
    have hfun := lower_fun_of G hf
    simp only [Impl] at himpl
    simp only [spine] at hrest
    rw [Own.eval_trap]
    refine ⟨0, _, .refl _, ?_⟩
    rw [step_run_term hrest hfun himpl]
    rfl
termination_by c.size + Own.jweight Jo
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Own.Code.size]; cfg_omega)
    | (simp only [Own.Code.size, Own.jweight, Own.JEntry.weight, Bool.false_eq_true, ↓reduceIte]; cfg_omega)
    | (simp only [Own.Code.size] at this ⊢; cfg_omega)

/-- A `case`'s alternatives against the `switch`'s edges, in order. -/
theorem alts_reach (fr : Frame) (ρo : Env) (Jo : List Own.JEntry) (H : Heap) (stk : List (Frame × Var))
    (key : Key.CtorKey) (alts : List Own.Alt) (d : Option Own.Code) (next : BlockId) (fd : Own.Fun)
    (Jc : JScope) (lo : Nat) (hf : q.fun? fr.fn = some fd) (hs : fr.fn < q.size) (hrest : fr.rest = [])
    (harms : ImplArms (Lower.function fr.fn fd).block? fr.fn Jc next alts)
    (hopt : ImplOpt (Lower.function fr.fn fd).block? fr.fn Jc (next + countAlts alts) d)
    (hsa : ScopedAlts lo alts) (hso : ScopedOpt lo d) (hsub : Sub ρo fr.env) (hbelow : Below lo ρo)
    (hjc : JC (Lower.function fr.fn fd).block? fr.fn fr.env lo Jc Jo)
    (hstep : step pol (lower q) (.run fr stk H) =
      match selectEdge key (armEdges next alts) (d.map fun _ => ({ target := next + countAlts alts } : Edge)) with
      | some e => takeEdge (Lower.function fr.fn fd) fr stk H e
      | none => .stuck) :
    Reach pol (lower q) k (.run fr stk H) stk (Own.evalAlts pol q k ρo Jo H key alts d) := by
  match alts, d with
  | [], none =>
    rw [Own.evalAlts_nil]
    exact Reach.stuck
  | [], some c =>
    rw [Own.evalAlts_nil]
    simp only [ImplOpt] at hopt
    simp only [ScopedOpt] at hso
    obtain ⟨t, hb⟩ := impl_head hopt
    refine Reach.free ?_ (eval_reach { fr with blk := next + countAlts [], rest := spine c } ρo Jo H c stk
      ⟨fd, Jc, [], [], _, lo, hf, hs, hopt, rfl, hsub, hbelow, hso, hjc⟩)
    rw [hstep]
    simp only [armEdges, selectEdge, Option.map_some]
    rw [takeEdge_eq (vs := []) hb rfl (by simp)]
    simp [Own.bindAll]
  | .mk key' b :: as, d =>
    rw [Own.evalAlts_cons]
    simp only [ImplArms] at harms
    simp only [ScopedAlts] at hsa
    by_cases hk : key' = key
    · simp only [hk, ↓reduceIte]
      obtain ⟨t, hb⟩ := impl_head harms.1
      refine Reach.free ?_ (eval_reach { fr with blk := next, rest := spine b } ρo Jo H b stk
        ⟨fd, Jc, [], [], _, lo, hf, hs, harms.1, rfl, hsub, hbelow, hsa.1, hjc⟩)
      rw [hstep]
      simp only [armEdges, selectEdge, hk, ↓reduceIte]
      rw [takeEdge_eq (vs := []) hb rfl (by simp)]
      simp [Own.bindAll]
    · simp only [hk, ↓reduceIte]
      have hc : next + countAlts (.mk key' b :: as) = next + 1 + count b + countAlts as := by
        simp only [countAlts]; cfg_omega
      refine alts_reach fr ρo Jo H stk key as d (next + 1 + count b) fd Jc lo hf hs hrest harms.2
        (by rw [← hc]; exact hopt) hsa.2 hso hsub hbelow hjc ?_
      rw [hstep]
      simp only [armEdges, selectEdge, hk, ↓reduceIte, hc]
termination_by Own.Code.altsSize alts + Own.Code.optSize d + Own.jweight Jo + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [Own.Code.altsSize, Own.Code.optSize]
  all_goals first
    | cfg_omega
    | (have := Own.Code.size_pos b; cfg_omega)

end

end

/-- **The simulation at every clock.** -/
theorem eval_reach_all {pol : AllocPol} {q : Own.Program} (G : Good q) :
    ∀ (k : Nat) (fr : Frame) (ρo : Env) (Jo : List Own.JEntry) (H : Heap) (c : Own.Code)
      (stk : List (Frame × Var)), At q fr ρo Jo c →
      Reach pol (lower q) k (.run fr stk H) stk (Own.eval pol q k ρo Jo H c) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih => exact eval_reach G ih

/-- A run of function `f`: the Cfg run from its call state. -/
theorem run_reach {pol : AllocPol} {q : Own.Program} (G : Good q) (k : Nat) (f : FunId) (vs : List RVal)
    (H : Heap) : Reach pol (lower q) k (.call f vs [] H) [] (Own.run pol q k f vs H) :=
  call_reach G (fun k' _ => eval_reach_all G k') f vs [] H

end Compilatrix.Cfg.Proof
