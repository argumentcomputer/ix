import IxCC.Own.Plain.Proof.Owned.Actions
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.Frames
import IxCC.Fir.Proof.Unfold

/-! # One binding that calls nothing, against the source's step

From the checker's verdict on `x := r` and the source's successful step, the Own step and the
state after it: a moved token (`x := y`, preserving static uniqueness), an immediate (literals,
field-less constructors, projections of immediates), a fresh allocation (statically unique!), a
borrowed projection (with `setProj` recorded), or a primitive under its ownership signature
(`prim_step_pure`: what is an immediate afterwards is what the signature says, from its contract
`PrimSig.PureSound`, which `lamSig_pureSound` gives for every primitive of today). -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var Arg)

theorem except_bind_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem except_pure_ok {ε α : Type} {a b : α} (h : (pure a : Except ε α) = .ok b) : a = b :=
  Except.ok.inj h

theorem Result.ofOption_ok {α : Type} {o : Option α} {a : α} (h : Result.ofOption o = .ok a) :
    o = some a := by
  cases o with
  | none => cases h
  | some b => cases h; rfl

theorem firEvalArgs_length {ρ : Fir.Env} :
    ∀ {args : List Arg} {ws : List Fir.Val}, Fir.evalArgs ρ args = some ws → ws.length = args.length
  | [], ws, h => by simp [Fir.evalArgs] at h; subst h; rfl
  | a :: as, ws, h => by
    cases ha : a.eval ρ with
    | none => simp [Fir.evalArgs, ha] at h
    | some w =>
      cases hs : Fir.evalArgs ρ as with
      | none => simp [Fir.evalArgs, ha, hs] at h
      | some ws' =>
        have : w :: ws' = ws := by simpa [Fir.evalArgs, ha, hs] using h
        subst this
        simp [firEvalArgs_length hs]

theorem evalArgs_mem {ρ : Own.Env} :
    ∀ {args : List Arg} {vs : List RVal} {y : Var} {u : RVal}, Own.evalArgs ρ args = some vs →
      Arg.var y ∈ args → ρ.get? y = some u → u ∈ vs
  | [], _, _, _, _, hy, _ => by simp at hy
  | a :: as, vs, y, u, h, hy, hu => by
    cases ha : Own.evalArg ρ a with
    | none => simp [Own.evalArgs, ha] at h
    | some v =>
      cases hs : Own.evalArgs ρ as with
      | none => simp [Own.evalArgs, ha, hs] at h
      | some vs' =>
        have : v :: vs' = vs := by simpa [Own.evalArgs, ha, hs] using h
        subst this
        rcases List.mem_cons.mp hy with he | hy
        · subst he
          have : v = u := Option.some.inj (ha.symm.trans hu)
          subst this; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (evalArgs_mem hs hy hu)

/-- The value of a variable argument, at its position. -/
theorem evalArgs_var_at {ρ : Own.Env} :
    ∀ {args : List Arg} {vs : List RVal} {i : Nat} {y : Var}, Own.evalArgs ρ args = some vs →
      args[i]? = some (Arg.var y) → ∃ u, ρ.get? y = some u ∧ vs[i]? = some u
  | [], _, _, _, _, hy => by simp at hy
  | a :: as, vs, i, y, h, hy => by
    cases ha : Own.evalArg ρ a with
    | none => simp [Own.evalArgs, ha] at h
    | some v =>
      cases hs : Own.evalArgs ρ as with
      | none => simp [Own.evalArgs, ha, hs] at h
      | some vs' =>
        have : v :: vs' = vs := by simpa [Own.evalArgs, ha, hs] using h
        subst this
        cases i with
        | zero =>
          have hay : a = .var y := by simpa using hy
          subst hay
          exact ⟨v, ha, rfl⟩
        | succ i =>
          obtain ⟨u, hu, hi⟩ := evalArgs_var_at hs (i := i) (y := y) (by simpa using hy)
          exact ⟨u, hu, by simpa using hi⟩

/-- Variables a primitive reads are available, so they denote. -/
theorem needArgs_sem {H : Heap} {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env}
    (hden : ∀ x, Γ.avail x = true →
      ∃ v w, ρo.get? x = some v ∧ ρf.get? x = some w ∧ Proof.Den H v w) :
    ∀ {args : List Arg}, (∀ x, Arg.var x ∈ args → Γ.avail x = true) →
      ∃ vs ws, Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
        Sem.Forall2 (Proof.Den H) vs ws
  | [], _ => ⟨[], [], rfl, rfl, .nil⟩
  | a :: as, h => by
    obtain ⟨vs, ws, h1, h2, h3⟩ := needArgs_sem hden (args := as)
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha : ∃ v w, Own.evalArg ρo a = some v ∧ a.eval ρf = some w ∧ Proof.Den H v w := by
      cases a with
      | var x => exact hden x (h x List.mem_cons_self)
      | lit l => exact ⟨.lit l, .lit l, rfl, rfl, Proof.den_lit H l⟩
      | erased => exact ⟨.erased, .erased, rfl, rfl, Proof.den_erased H⟩
    obtain ⟨v, w, h4, h5, h6⟩ := ha
    exact ⟨v :: vs, w :: ws, by simp [Own.evalArgs, h4, h1], by simp [Fir.evalArgs, h5, h2],
      .cons h6 h3⟩

private theorem ofKey_key_eq {ctors : List Lam.CtorInfo} {key : Key.CtorKey} {info : Fir.CtorInfo}
    (h : Fir.CtorInfo.ofKey ctors key = some info) : info.key = key := by
  unfold Fir.CtorInfo.ofKey at h
  cases hf : ctors.find? (·.key == key) with
  | none => simp [hf] at h
  | some r =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    subst h; rfl

theorem primResult_immUniq {F : Fir.Program} {H : Heap}
    {op : Lam.Prim} {vs : List RVal} {ws : List Fir.Val} {w : Fir.Val}
    (hpins : BoolPinsOk F) (hargs : Sem.Forall2 (Proof.Den H) vs ws)
    (hp : op.isArr = false) (hresult : Fir.primResult F op ws = .ok w) :
    ∃ v, Own.primResult { ctors := F.ctors, known := F.known } op vs = .ok v ∧
      Proof.Den H v w ∧ ImmUniq F.ctors v := by
  unfold Fir.primResult at hresult
  rw [Fir.arrResult_of_not_arr hp] at hresult
  unfold Own.primResult
  rw [Values.natArgs_den hargs]
  cases hn : Fir.natArgs ws with
  | none => simp [hn] at hresult
  | some ns =>
    simp only [hn] at hresult ⊢
    cases hs : op.sem ns with
    | none => simp [hs] at hresult
    | some pr =>
      cases pr with
      | nat n =>
        simp only [hs, Result.ok.injEq] at hresult
        subst w
        exact ⟨.lit (.nat n), by simp, Proof.den_lit H _, ⟨(fun _ h => by cases h), trivial⟩⟩
      | bool b =>
        simp only [hs] at hresult ⊢
        cases hpin : (if b then F.known.boolTrue else F.known.boolFalse) with
        | none => simp [Fir.boolVal, hpin, Result.ofOption] at hresult
        | some key =>
          simp only [Fir.boolVal, hpin, Fir.Program.ctorInfo?] at hresult
          cases hi : Fir.CtorInfo.ofKey F.ctors key with
          | none => simp [hi, Result.ofOption] at hresult
          | some info =>
            have ha := hpins b key info hpin hi
            have hfieldless : info.fieldless = true := by simp [Fir.CtorInfo.fieldless, ha]
            simp only [hi, Option.map_some, Result.ofOption, Result.ok.injEq] at hresult
            subst w
            refine ⟨.ctor0 info, by simp [ctor0Of, hi, hfieldless, Result.ofOption],
              Proof.den_ctor0 H _, ⟨(fun _ h => by cases h), fun info' hi' => ?_⟩⟩
            rw [ofKey_key_eq hi] at hi'
            rw [hi] at hi'
            cases hi'; exact ha

theorem natArgs_immUniq {ctors : List Lam.CtorInfo} : ∀ {vs : List RVal} {ns : List Nat},
    Own.natArgs vs = some ns → ∀ v ∈ vs, ImmUniq ctors v
  | [], _, _, _, hv => by simp at hv
  | v :: vs, ns, h, u, hu => by
    cases v with
    | lit lit =>
      cases lit with
      | nat n =>
        simp only [Own.natArgs, Option.map_eq_some_iff] at h
        obtain ⟨ns', hns', rfl⟩ := h
        rcases List.mem_cons.mp hu with rfl | hu
        · exact ⟨(fun _ hc => by cases hc), trivial⟩
        · exact natArgs_immUniq hns' u hu
      | str _ => simp [Own.natArgs] at h
    | loc _ | ctor0 _ | erased => simp [Own.natArgs] at h

theorem primResult_args_immUniq {F : Fir.Program} {H : Heap}
    {op : Lam.Prim} {vs : List RVal} {ws : List Fir.Val} {w : Fir.Val}
    (hargs : Sem.Forall2 (Proof.Den H) vs ws) (hp : op.isArr = false)
    (hresult : Fir.primResult F op ws = .ok w) :
    ∀ v ∈ vs, ImmUniq F.ctors v := by
  unfold Fir.primResult at hresult
  rw [Fir.arrResult_of_not_arr hp] at hresult
  have hnat := Values.natArgs_den hargs
  cases hn : Fir.natArgs ws with
  | none => simp [hn] at hresult
  | some ns =>
    rw [hn] at hnat
    exact natArgs_immUniq hnat

/-! ## What a signature promises

The checker learns that a value is an immediate from a signature (`primStep`: `markImm` for the
arguments marked `imm`, `ResUse.imm` for the result), so each signature owes the fact. -/

/-- **The contract of a signature for a primitive that touches no heap** (every primitive of
today). On argument values `vs` with result `v`:
* each argument the signature marks `imm` is a valid immediate;
* each argument it consumes is an immediate, so the token taken was vacuous and nothing was
  released;
* the result is a valid immediate, whatever the signature calls it: `imm` asks exactly this, and
  a token (`fresh`) or a borrow (`borrowed`) of an immediate is vacuous.

A primitive that reads or makes a cell (an array operation, a `Nat` held in a limb cell) meets a
contract over the heap instead; this one is the case in which the heap is unchanged. -/
structure PrimSig.PureSound (ctors : List Lam.CtorInfo) (sig : PrimSig) (vs : List RVal)
    (v : RVal) : Prop where
  immArgs : ∀ (i : Nat) (u : RVal), sig.args[i]? = some ArgUse.imm → vs[i]? = some u →
    ImmUniq ctors u
  consumed : ∀ (i : Nat) (u : RVal), sig.args[i]? = some ArgUse.consume → vs[i]? = some u →
    ImmVal u
  result : ImmUniq ctors v

/-- **Today's primitives meet their signature.** A primitive that succeeds read every argument
as a `Nat` literal (`natArgs`) and returned a literal or a pinned Boolean constructor: the
arguments `lamSig` marks `imm` are immediates and so is the result. The fact comes from the
primitive's semantics, per signature, and not from a rule about primitives in general. -/
theorem lamSig_pureSound {F : Fir.Program} {H : Heap}
    {op : Lam.Prim} {vs : List RVal} {ws : List Fir.Val} {w : Fir.Val}
    (hpins : BoolPinsOk F) (hargs : Sem.Forall2 (Proof.Den H) vs ws) (hp : op.isArr = false)
    (hresult : Fir.primResult F op ws = .ok w) (arity : Nat) :
    ∃ v, Own.primResult { ctors := F.ctors, known := F.known } op vs = .ok v ∧
      Proof.Den H v w ∧ (lamSig op arity).PureSound F.ctors vs v := by
  obtain ⟨v, hres, hden, himm⟩ := primResult_immUniq hpins hargs hp hresult
  have hall := primResult_args_immUniq hargs hp hresult
  refine ⟨v, hres, hden, fun i u _ hu => hall u (List.mem_of_getElem? hu), fun i u hi _ => ?_,
    himm⟩
  have hm : ArgUse.consume ∈ List.replicate arity ArgUse.imm := List.mem_of_getElem? hi
  cases List.eq_of_mem_replicate hm

private theorem asCtor_field_immUniq {ctors : List Lam.CtorInfo} {H : Heap} {K : Lam.Known}
    {parent v : RVal} {key : Key.CtorKey} {fields : List RVal}
    (himm : ImmVal parent) (hc : parent.asCtor K H = some (key, fields)) (hm : v ∈ fields) :
    ImmUniq ctors v := by
  cases parent with
  | loc l => exact absurd rfl (himm l)
  | erased => simp [RVal.asCtor] at hc
  | ctor0 c =>
    have he : c.key = key ∧ [] = fields := by simpa [RVal.asCtor] using hc
    rw [← he.2] at hm; simp at hm
  | lit lit =>
    cases lit with
    | str _ => simp [RVal.asCtor] at hc
    | nat n =>
      cases n with
      | zero =>
        cases hk : K.natZero <;> simp [RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc; simp at hm
      | succ n =>
        cases hk : K.natSucc <;> simp [RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have : v = .lit (.nat n) := by simpa using hm
        subst this; exact ⟨(fun _ h => by cases h), trivial⟩

private theorem asCtor_field_noPriv {H : Heap} {K : Lam.Known} {priv : Nat → Prop}
    (he : ∀ l, priv l → edgeCount H l = 0) {parent v : RVal} {key : Key.CtorKey}
    {fields : List RVal} (hc : parent.asCtor K H = some (key, fields)) (hm : v ∈ fields) :
    ∀ l, priv l → v ≠ .loc l := by
  intro l hl hEq; subst hEq
  cases parent with
  | loc k =>
    cases hk : H.cell? k with
    | none => simp [RVal.asCtor, hk] at hc
    | some cell =>
      cases cell with
      | dead => simp [RVal.asCtor, hk] at hc
      | live rc m b =>
        have hbf : b.fields = fields := (Prod.mk.inj (Option.some.inj (by simpa [RVal.asCtor, hk] using hc))).2
        rw [← hbf] at hm
        exact fields_avoid (he l hl) hk hm
  | lit lit =>
    cases lit with
    | str _ => simp [RVal.asCtor] at hc
    | nat n =>
      cases n with
      | zero =>
        cases hk : K.natZero <;> simp [RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc; simp at hm
      | succ n =>
        cases hk : K.natSucc <;> simp [RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc; simp at hm
  | ctor0 c =>
    have hbf : [] = fields := (Prod.mk.inj (Option.some.inj (by simpa [RVal.asCtor] using hc))).2
    rw [← hbf] at hm; simp at hm
  | erased => simp [RVal.asCtor] at hc

section
variable {functions : Signatures} {H : Heap} {external : Nat → Nat} {live : List Var}
  {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins} {Δ : JCtx}
  {Jf : List Fir.JEntry} {Jo : List JEntry} {borrows : BorrowSigs} {uniqs : UniqSigs}
  {retUniq : Bool} {ctors : List Lam.CtorInfo} {K : Lam.Known} {priv : Nat → Prop}
  {slots : Src.NatMap RVal} {slotVals : List RVal}

private theorem taken_avoids_localPriv (st : OwnedState functions H external live Γ ρf ρo owned
    lex Δ Jf Jo borrows uniqs retUniq ctors K priv slots slotVals)
    {Γ₁ : Ctx} {owned₁ taken : List RVal}
    (hwk : Ctx.Weaker Γ₁ Γ)
    (hroots₁ : ∃ toks, Ctx.Tokens Γ₁ toks ∧ EnvRoots ρo toks owned₁)
    (hs : SameRefs owned (taken ++ owned₁))
    (hpriv_taken : ∀ l, priv l → refsIn l taken = 0) :
    ∀ l, (st.pre.weaker hwk hroots₁ (fun k => by
      have := hs k; rw [refsIn_append] at this; omega)).localPriv l → refsIn l taken = 0 := by
  have hle : ∀ k, refsIn k owned₁ ≤ refsIn k owned := fun k => by
    have := hs k; rw [refsIn_append] at this; omega
  let pre₁ := st.pre.weaker hwk hroots₁ hle
  intro l hl
  rcases hl with hpr | ⟨s, cls, u, hrs, hsl⟩ | ⟨z, huz, hiz, hz⟩
  · exact hpriv_taken l hpr
  · obtain ⟨sv, hsv, hrc⟩ := pre₁.rsetOk s cls u hrs
    have : sv = .loc l := Option.some.inj (hsv.symm.trans hsl); subst this
    rcases hrc with ⟨hc0, _⟩ | ⟨l', _, hEq', _, _, _, _, _, hrefs⟩
    · cases hc0
    · cases hEq'
      have hrefs0 : refsIn l (owned ++ slotVals) = 1 := by
        obtain ⟨sv', hsv', hrc'⟩ := st.rsetOk s cls u (by rw [← hwk.rset]; exact hrs)
        have : sv' = .loc l := Option.some.inj (hsv'.symm.trans hsl); subst this
        rcases hrc' with ⟨hc0, _⟩ | ⟨l'', _, hEq'', _, _, _, _, _, hr0⟩
        · cases hc0
        · cases hEq''; exact hr0
      rw [refsIn_append, hs l, refsIn_append] at hrefs0
      rw [refsIn_append] at hrefs
      omega
  · obtain ⟨_, u', hu', hvu⟩ := pre₁.uniqOk z huz
    have : u' = .loc l := Option.some.inj (hu'.symm.trans hz); subst this
    obtain ⟨_, _, _, _, hrefs⟩ := hvu
    have hrefs0 : refsIn l (owned ++ slotVals) = 1 := by
      obtain ⟨_, u'', hu'', hvu0⟩ := st.uniqOk z (hwk.isUniq z huz)
      have : u'' = .loc l := Option.some.inj (hu''.symm.trans hz); subst this
      obtain ⟨_, _, _, _, hr0⟩ := hvu0; exact hr0
    rw [refsIn_append, hs l, refsIn_append] at hrefs0
    rw [refsIn_append] at hrefs
    omega

/-- **A primitive that touches no heap, under its signature.** From the checker's verdict on
`x := op args` under `sig` (`primStep`) and a result that meets the signature's contract
(`PrimSig.PureSound`), the state after the binding: the consumed arguments' tokens were vacuous,
the arguments marked `imm` are immediates, a release ends the epoch borrows, and the result is
bound as an immediate, an owned value or a borrow as the signature says. The heap is the same and
so are the references the tokens hold. The fact that an operand or the result is an immediate is
the signature's, through the contract. -/
theorem prim_step_pure (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} (hx : x ∉ live) {sig : PrimSig} {args : List Arg} {Γ' : Ctx}
    (hc : primStep Γ sig x args = .ok Γ')
    {vs : List RVal} (hvs : Own.evalArgs ρo args = some vs)
    {v : RVal} {w : Fir.Val} (hd : Proof.Den H v w)
    (sound : sig.PureSound ctors vs v) :
    ∃ owned', OwnedState functions H external (live ++ [x]) Γ' (ρf.insert x w) (ρo.insert x v)
        owned' lex Δ Jf Jo borrows uniqs retUniq ctors K priv slots slotVals ∧
      SameRefs owned owned' := by
  obtain ⟨Γ₁, _, htake, hread, rfl⟩ := primStep_ok hc
  -- the consumed arguments: immediates, so the tokens taken held no reference
  obtain ⟨taken, owned₁, inv₁, hs₁, hwk, hpos⟩ := takeConsumed_sem st.takeInv htake
  have htaken : AllImm taken := fun t ht => by
    obtain ⟨i, y, hi, hy, hv⟩ := hpos t ht
    obtain ⟨u, hu, hvi⟩ := evalArgs_var_at hvs hy
    have : u = t := Option.some.inj (hu.symm.trans hv)
    subst this
    exact sound.consumed i u hi hvi
  have hs₁' : SameRefs owned owned₁ := hs₁.trans (SameRefs.allImm htaken owned₁)
  have pre₁ := st.pre.weaker hwk inv₁.roots (fun k => Nat.le_of_eq (hs₁' k).symm)
  -- the arguments marked `imm`: still held (`checkRead`), and immediates by the contract
  obtain ⟨owned₂, pre₂, hs₂⟩ := pre₁.markImm sig.args args (fun i y hi hy => by
    obtain ⟨u, hu, hvi⟩ := evalArgs_var_at hvs hy
    exact ⟨checkRead_held hread i .imm y hi (fun h => by cases h) hy, u, hu,
      sound.immArgs i u hi hvi⟩)
  have hs : SameRefs owned owned₂ := hs₁'.trans hs₂
  have pre₃ := pre₂.releaseIf sig.release
  have hbal : Balance H external (owned₂ ++ slotVals) :=
    (SameRefs.append hs (SameRefs.refl slotVals)).balance st.counts
  have himm : ImmVal v := sound.result.1
  -- the result
  cases hres : sig.result with
  | imm => exact ⟨owned₂, pre₃.bindImmUniq hx hd sound.result hbal, hs⟩
  | fresh unique =>
    have hcons : SameRefs owned₂ (v :: owned₂) := (SameRefs.imm_cons himm owned₂).symm
    have hbal' : Balance H external ((v :: owned₂) ++ slotVals) :=
      (SameRefs.append hcons (SameRefs.refl slotVals)).balance hbal
    have hpv : ∀ l, pre₃.localPriv l → v ≠ .loc l := fun l _ => himm l
    cases unique with
    | true =>
      exact ⟨v :: owned₂, pre₃.bindUniqOwned hx hd hbal' sound.result.toUniqVal hpv,
        hs.trans hcons⟩
    | false => exact ⟨v :: owned₂, pre₃.bindOwned hx hd hbal' hpv, hs.trans hcons⟩
  | borrowed ofArg =>
    have hbrw : BorrowVal H v := by
      cases v with
      | loc l => exact absurd rfl (himm l)
      | lit _ | ctor0 _ | erased => trivial
    exact ⟨owned₂, pre₃.bindBorrow hx hd hbrw hbal, hs⟩

theorem rhs_step {F : Fir.Program} (pins : BoolPinsOk F)
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq F.ctors F.known priv slots slotVals)
    {x : Var} {r : Fir.Rhs} (hx : x ∉ live) (hn : ∀ f args, r ≠ .call f args)
    {Γ' : Ctx} (hc : bindStep Γ x r borrows uniqs F.ctors = .ok Γ')
    {w : Fir.Val} (hw : Fir.evalRhs F ρf r = .ok w) :
    ∃ v H' owned', evalRhs { ctors := F.ctors, known := F.known } ρo H r = .ok (v, H') ∧
      OwnedState functions H' external (live ++ [x]) Γ' (ρf.insert x w) (ρo.insert x v) owned'
        lex Δ Jf Jo borrows uniqs retUniq F.ctors F.known priv slots slotVals ∧
      ReachablePreserved H H' external ∧ PrivPreserved H H' priv := by
  have same : ReachablePreserved H H external := ReachablePreserved.refl H external
  have sameP : PrivPreserved H H priv := PrivPreserved.refl st.privNoEdge
  cases r with
  | call f args => exact absurd rfl (hn f args)
  | arg a =>
    replace hc : bindCtx Γ x (.arg a) borrows uniqs F.ctors = .ok Γ' := hc
    cases a with
    | var y =>
      have hwy : ρf.get? y = some w := Result.ofOption_ok hw
      simp only [bindCtx] at hc
      cases hi : Γ.isImm y with
      | true =>
        simp only [hi, ↓reduceIte, Except.ok.injEq] at hc
        subst hc
        obtain ⟨v, w', hv, hw', hd⟩ := st.den y (by simp [Ctx.avail_eq, hi])
        have : w' = w := Option.some.inj (hw'.symm.trans hwy); subst this
        obtain ⟨u, hu, himm⟩ := st.immOk y hi
        have huv : u = v := Option.some.inj (hu.symm.trans hv); subst huv
        have hev : evalRhs { ctors := F.ctors, known := F.known } ρo H (.arg (.var y)) = .ok (u, H) := by
          simp [evalRhs, Own.evalRhs, Own.evalArg, hv]
        cases huy : Γ.isUniq y with
        | true =>
          simp only [↓reduceIte]
          obtain ⟨_, u', hu', hvu⟩ := st.uniqOk y huy
          have : u' = u := Option.some.inj (hu'.symm.trans hv); subst this
          have himmU : ImmUniq F.ctors u' := by
            refine ⟨himm, ?_⟩
            cases u' with
            | loc l => exact absurd rfl (himm l)
            | ctor0 c => exact hvu
            | lit _ | erased => trivial
          exact ⟨u', H, owned, hev, st.pre.bindImmUniq hx hd himmU st.counts, same, sameP⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨u, H, owned, hev, st.pre.bindImm hx hd himm st.counts, same, sameP⟩
      | false =>
        simp only [hi, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases hpb : (Γ.tokens y == 0 && Γ.isPbrw y) = true
        · simp only [hpb, ↓reduceIte, Except.ok.injEq] at hc
          subst hc
          have hpb' : Γ.isPbrw y = true := (Bool.and_eq_true _ _).mp hpb |>.2
          have havy : Γ.avail y = true := by simp [Ctx.avail_eq, hpb']
          obtain ⟨v, w', hv, hw', hd⟩ := st.den y havy
          have : w' = w := Option.some.inj (hw'.symm.trans hwy); subst this
          obtain ⟨u, hu, hreach⟩ := st.pbrwOk y hpb'
          have huv : u = v := Option.some.inj (hu.symm.trans hv); subst huv
          have hev : evalRhs { ctors := F.ctors, known := F.known } ρo H (.arg (.var y)) = .ok (u, H) := by
            simp [evalRhs, Own.evalRhs, Own.evalArg, hv]
          have hpv : ∀ l, priv l → u ≠ .loc l := fun l hl hEq => st.privNoVar l hl y havy (hEq ▸ hv)
          exact ⟨u, H, owned, hev, st.pre.bindPbrw hx hd hreach st.counts hpv, same, sameP⟩
        · have hpbF : (Γ.tokens y == 0 && Γ.isPbrw y) = false := by
            cases hb : (Γ.tokens y == 0 && Γ.isPbrw y)
            · rfl
            · exact absurd hb hpb
          simp only [hpbF, Bool.false_eq_true, ↓reduceIte] at hc
          obtain ⟨Γ₁, ht, hΓ⟩ := except_bind_ok hc
          have hΓ := except_pure_ok hΓ
          subst hΓ
          obtain ⟨v, w', owned₁, hv, hw', hd, inv₁, hs, hwk⟩ := take_sem st.takeInv ht
          have : w' = w := Option.some.inj (hw'.symm.trans hwy); subst this
          have hev : evalRhs { ctors := F.ctors, known := F.known } ρo H (.arg (.var y)) = .ok (v, H) := by
            simp [evalRhs, Own.evalRhs, Own.evalArg, hv]
          have hle : ∀ k, refsIn k owned₁ ≤ refsIn k owned := fun k => by
            have := hs k; simp only [refsIn] at this; omega
          have pre₁ := st.pre.weaker hwk inv₁.roots hle
          have havy : Γ.avail y = true := by
            rcases Ctx.take_ok ht with ⟨hi', _⟩ | ⟨_, n, hn, _⟩
            · simp [Ctx.avail_eq, hi']
            · simp [Ctx.avail_eq, Ctx.tokens_eq, hn]
          have hpriv_v : ∀ l, pre₁.localPriv l → v ≠ .loc l := fun l hl hEq => by
            have h0 := taken_avoids_localPriv st hwk inv₁.roots (taken := [v])
              (by simpa using hs) (fun l' hl' => by
                have : v ≠ .loc l' := fun h => st.privNoVar l' hl' y havy (h ▸ hv)
                simp [refsIn, this]) l hl
            subst hEq; simp [refsIn] at h0
          have hbal' : Balance H external ((v :: owned₁) ++ slotVals) :=
            (SameRefs.append hs (SameRefs.refl slotVals)).balance st.counts
          by_cases hwu : (Γ.isUniq y && Γ.tokens y == 1) = true
          · simp only [hwu, ↓reduceIte]
            have huy : Γ.isUniq y = true := (Bool.and_eq_true _ _).mp hwu |>.1
            obtain ⟨_, u', hu', hvu⟩ := st.uniqOk y huy
            have : u' = v := Option.some.inj (hu'.symm.trans hv); subst this
            have hvU : UniqVal F.ctors H external ((u' :: owned₁) ++ slotVals) u' :=
              hvu.sameRefs (fun k => by rw [refsIn_append, hs k, refsIn_append])
            exact ⟨u', H, u' :: owned₁, hev, pre₁.bindUniqOwned hx hd hbal' hvU hpriv_v, same, sameP⟩
          · have hwuF : (Γ.isUniq y && Γ.tokens y == 1) = false := by
              cases hb : (Γ.isUniq y && Γ.tokens y == 1)
              · rfl
              · exact absurd hb hwu
            simp only [hwuF, Bool.false_eq_true, ↓reduceIte]
            exact ⟨v, H, v :: owned₁, hev, pre₁.bindOwned hx hd hbal' hpriv_v, same, sameP⟩
    | lit l =>
      cases hc
      have : w = .lit l := (Option.some.inj (Result.ofOption_ok hw)).symm; subst this
      refine ⟨.lit l, H, owned, by simp [evalRhs, Own.evalRhs, Own.evalArg], ?_, same, sameP⟩
      exact st.pre.bindImmUniq hx (Proof.den_lit H l) ⟨(fun _ h => by cases h), trivial⟩ st.counts
    | erased =>
      cases hc
      have : w = .erased := (Option.some.inj (Result.ofOption_ok hw)).symm; subst this
      refine ⟨.erased, H, owned, by simp [evalRhs, Own.evalRhs, Own.evalArg], ?_, same, sameP⟩
      exact st.pre.bindImmUniq hx (Proof.den_erased H) ⟨(fun _ h => by cases h), trivial⟩ st.counts
  | ctor c args =>
    replace hc : bindCtx Γ x (.ctor c args) borrows uniqs F.ctors = .ok Γ' := hc
    cases hws : Fir.evalArgs ρf args with
    | none => simp [Fir.evalRhs, hws] at hw
    | some ws =>
      by_cases harity : ws.length = c.arity
      · have hw' : w = .ctor c ws := by simp [Fir.evalRhs, hws, harity] at hw; exact hw.symm
        subst hw'
        by_cases hz : c.arity = 0
        · have hc' : bindCtx Γ x (.ctor c args) borrows uniqs F.ctors =
              .ok (if ctor0Valid F.ctors c then Γ.setImmUniq x else Γ.setImm x) := by
            simp [bindCtx, hz]
          rw [hc'] at hc; cases hc
          have hws0 : ws = [] := List.eq_nil_of_length_eq_zero (harity.trans hz); subst hws0
          have hargs : args = [] := List.eq_nil_of_length_eq_zero (firEvalArgs_length hws).symm
          subst hargs
          have hev : evalRhs { ctors := F.ctors, known := F.known } ρo H (.ctor c []) =
              .ok (.ctor0 c, H) := by
            simp [evalRhs, Own.evalRhs, Own.evalArgs, hz, Fir.CtorInfo.fieldless]
          cases hcv : ctor0Valid F.ctors c with
          | true =>
            simp only [↓reduceIte]
            exact ⟨.ctor0 c, H, owned, hev, st.pre.bindImmUniq hx (Proof.den_ctor0 H c)
              ⟨(fun _ h => by cases h), ctor0Valid_ok hcv⟩ st.counts, same, sameP⟩
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨.ctor0 c, H, owned, hev, st.pre.bindImm hx (Proof.den_ctor0 H c)
              (fun _ h => by cases h) st.counts, same, sameP⟩
        · have hz' : (c.arity == 0) = false := by simpa using hz
          simp only [bindCtx, hz', Bool.false_eq_true, ↓reduceIte] at hc
          obtain ⟨Γ₁, ht, hΓ⟩ := except_bind_ok hc
          have hΓ := except_pure_ok hΓ; subst hΓ
          obtain ⟨vs, ws', owned₁, hvs, hws', hds, inv₁, hs, hwk⟩ := takeArgs_sem st.takeInv ht
          have : ws' = ws := Option.some.inj (hws'.symm.trans hws); subst this
          have hvlen : vs.length = c.arity := hds.length.trans harity
          have hpos : 0 < c.arity := by omega
          have held : Balance H (holdRoots external (owned₁ ++ slotVals)) vs := by
            apply balance_hold.mp
            exact (SameRefs.append hs (SameRefs.refl slotVals)).trans
              (by intro k; simp [refsIn_append]) |>.balance st.counts
          obtain ⟨hr, hb, hresult, hpreserve⟩ :=
            evalRhs_alloc_owned (T := { ctors := F.ctors, known := F.known }) hvs hvlen hpos held hds
          have hreach := ReachablePreserved.alloc H external { ctor := c, fields := vs }
          have hle : ∀ k, refsIn k owned₁ ≤ refsIn k owned := fun k => by
            have := hs k; rw [refsIn_append] at this; omega
          have pre₁ := st.pre.weaker hwk inv₁.roots hle
          have hpriv_vs : ∀ l, priv l → refsIn l vs = 0 := by
            intro l hl
            by_cases hnz : refsIn l vs = 0
            · exact hnz
            · exfalso
              have hmem : RVal.loc l ∈ vs := mem_of_refsIn_pos (by omega)
              have hfind : ∀ (as' : List Arg) (vs' : List RVal) (Γa Γb : Ctx),
                  Own.evalArgs ρo as' = some vs' → Γa.takeArgs as' = .ok Γb → Ctx.Weaker Γa Γ →
                  RVal.loc l ∈ vs' → False := by
                intro as'
                induction as' with
                | nil => intro vs' _ _ hev' _ _ hm'; simp [Own.evalArgs] at hev'; subst hev'; cases hm'
                | cons a as'' ih =>
                  intro vs' Γa Γb hev' hta' hwa hm'
                  cases ha : Own.evalArg ρo a with
                  | none => simp [Own.evalArgs, ha] at hev'
                  | some v0 =>
                    cases has : Own.evalArgs ρo as'' with
                    | none => simp [Own.evalArgs, ha, has] at hev'
                    | some vs'' =>
                      have : v0 :: vs'' = vs' := by simpa [Own.evalArgs, ha, has] using hev'
                      subst this
                      simp only [Ctx.takeArgs] at hta'
                      cases hta0 : Γa.takeArg a with
                      | error _ => rw [hta0] at hta'; cases hta'
                      | ok Γm =>
                        rw [hta0] at hta'
                        rcases List.mem_cons.mp hm' with hEq | hm''
                        · subst hEq
                          cases a with
                          | lit _ | erased => simp [Own.evalArg] at ha
                          | var y =>
                            have havy : Γa.avail y = true := by
                              rcases Ctx.take_ok hta0 with ⟨hi', _⟩ | ⟨_, n, hn, _⟩
                              · simp [Ctx.avail_eq, hi']
                              · simp [Ctx.avail_eq, Ctx.tokens_eq, hn]
                            exact st.privNoVar l hl y (hwa.avail havy) ha
                        · exact ih vs'' Γm Γb has hta' ((Ctx.takeArg_weaker hta0).trans hwa) hm''
              exact hfind args vs Γ Γ₁ hvs ht (Ctx.Weaker.refl Γ) hmem
          have hloc_vs := taken_avoids_localPriv st hwk inv₁.roots hs hpriv_vs
          have hprivLoc : PrivPreserved H (H.alloc .rc { ctor := c, fields := vs }).2 pre₁.localPriv :=
            PrivPreserved.alloc (fun l hl => (pre₁.localPriv_facts hl).1)
              (fun l hl => (pre₁.localPriv_facts hl).2) hloc_vs
          have pre₂ := pre₁.transport hpreserve (fun v hv => hv.alloc _) hreach
            (fun _ _ _ _ _ _ hac => asCtor_alloc hac) hprivLoc
          have hbal' : Balance (H.alloc .rc { ctor := c, fields := vs }).2 external
              (((H.alloc .rc { ctor := c, fields := vs }).1 :: owned₁) ++ slotVals) := by
            have hr' := balance_resume hb
            refine (SameRefs.balance ?_ hr')
            intro k; simp only [List.cons_append, refsIn_append, refsIn]; omega
          have hfresh0 := st.counts H.size
          rw [dynCount_fresh] at hfresh0
          have hfreshExt : external H.size = 0 := by omega
          have hfreshOwned : refsIn H.size (owned ++ slotVals) = 0 := by omega
          have hfreshEdge : edgeCount H H.size = 0 := by omega
          have hfreshSplit : refsIn H.size vs + refsIn H.size owned₁ + refsIn H.size slotVals = 0 := by
            rw [refsIn_append, hs H.size, refsIn_append] at hfreshOwned; omega
          have hvU : UniqVal F.ctors (H.alloc .rc { ctor := c, fields := vs }).2 external
              (((H.alloc .rc { ctor := c, fields := vs }).1 :: owned₁) ++ slotVals)
              (H.alloc .rc { ctor := c, fields := vs }).1 := by
            show ∃ b', (H.alloc .rc { ctor := c, fields := vs }).2.cell? H.size = some (.live 1 .dyn b') ∧
              external H.size = 0 ∧
              edgeCount (H.alloc .rc { ctor := c, fields := vs }).2 H.size = 0 ∧
              refsIn H.size ((.loc H.size :: owned₁) ++ slotVals) = 1
            refine ⟨{ ctor := c, fields := vs }, ?_, hfreshExt, ?_, ?_⟩
            · simpa [AllocPol.mode] using Proof.alloc_cell .rc H { ctor := c, fields := vs }
            · simp only [edgeCount_alloc]; omega
            · simp only [List.cons_append, refsIn_append, refsIn, ↓reduceIte]; omega
          have hpvNew : ∀ l, pre₂.localPriv l → (H.alloc .rc { ctor := c, fields := vs }).1 ≠ .loc l := by
            intro l hl hEq
            have hlt : l < H.size := (pre₁.localPriv_facts hl).1
            simp only [Heap.alloc, Heap.size] at hEq hlt
            cases hEq; omega
          exact ⟨(H.alloc .rc { ctor := c, fields := vs }).1, (H.alloc .rc { ctor := c, fields := vs }).2,
            (H.alloc .rc { ctor := c, fields := vs }).1 :: owned₁, hr,
            pre₂.bindUniqOwned hx hresult hbal' hvU hpvNew, hreach,
            hprivLoc.mono (fun _ h => Or.inl h)⟩
      · simp [Fir.evalRhs, hws, harity] at hw
  | proj y key i =>
    replace hc : bindCtx Γ x (.proj y key i) borrows uniqs F.ctors = .ok Γ' := hc
    obtain ⟨u, hneed, hΓ⟩ := except_bind_ok hc
    have hΓ := except_pure_ok hΓ
    have hy : Γ.avail y = true := Ctx.need_avail hneed
    have hylive : y ∈ live := st.known y (Ctx.avail_known hy)
    have hyx : y ≠ x := fun h => hx (h ▸ hylive)
    obtain ⟨vy, wy, hvy, hwy, hdy⟩ := st.den y hy
    simp only [Fir.evalRhs, hwy] at hw
    cases hcw : wy.asCtor F.known with
    | none => rw [hcw] at hw; cases hw
    | some p =>
      obtain ⟨key', fields⟩ := p
      rw [hcw] at hw
      by_cases hk : key' = key
      · subst hk
        simp only [↓reduceIte] at hw
        have hi : fields[i]? = some w := Result.ofOption_ok hw
        obtain ⟨vs, hview, hfields⟩ := (Values.asCtor_den F.known hdy).1 key' fields hcw
        obtain ⟨v, hget, hv⟩ := hfields.get' hi
        have hm : v ∈ vs := List.mem_of_getElem? hget
        have hev : evalRhs { ctors := F.ctors, known := F.known } ρo H (.proj y key' i) = .ok (v, H) := by
          simp [evalRhs, Own.evalRhs, hvy, hview, hget, Result.ofOption, Result.map]
        refine ⟨v, H, owned, hev, ?_, same, sameP⟩
        subst hΓ
        have hxlive : x ∈ live ++ [x] := List.mem_append_right _ (List.mem_singleton_self _)
        have hylive' : y ∈ live ++ [x] := List.mem_append_left _ hylive
        have hvy' : (ρo.insert x v).get? y = some vy := by
          rw [Src.NatMap.get?_insert_ne _ _ hyx]; exact hvy
        have hvx' : (ρo.insert x v).get? x = some v := Src.NatMap.get?_insert_self ..
        cases hi' : Γ.isImm y with
        | true =>
          simp only [↓reduceIte]
          obtain ⟨u', hu', himm⟩ := st.immOk y hi'
          have : u' = vy := Option.some.inj (hu'.symm.trans hvy); subst this
          exact (st.pre.bindImmUniq hx hv (asCtor_field_immUniq himm hview hm) st.counts).setProj
            hxlive hylive' hvy' hview hget hvx'
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hpb' : Γ.isPbrw y with
          | true =>
            simp only [↓reduceIte]
            obtain ⟨u', hu', hreach⟩ := st.pbrwOk y hpb'
            have : u' = vy := Option.some.inj (hu'.symm.trans hvy); subst this
            exact (st.pre.bindPbrw hx hv (hreach.asCtor_field hview hm) st.counts
              (asCtor_field_noPriv st.privNoEdge hview hm)).setProj
              hxlive hylive' hvy' hview hget hvx'
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact (st.pre.bindBorrow hx hv (BorrowVal.asCtor_field hview hm) st.counts).setProj
              hxlive hylive' hvy' hview hget hvx'
      · simp only [hk, ↓reduceIte] at hw; cases hw
  | prim op args =>
    -- under the primitive's signature: the step is `primStep`, the facts are its contract's
    obtain ⟨hpa, hc⟩ := bindStep_prim hc
    obtain ⟨_, hneed, _, _, _⟩ := primStep_ok hc
    obtain ⟨vs, ws, hvs, hws, hds⟩ := needArgs_sem st.den (Ctx.needArgs_avail hneed)
    simp only [Fir.evalRhs, hws] at hw
    obtain ⟨v, hres, hden, sound⟩ := lamSig_pureSound pins hds hpa hw args.length
    have hev : evalRhs { ctors := F.ctors, known := F.known } ρo H (.prim op args) = .ok (v, H) := by
      simp [evalRhs, Own.evalRhs, hvs, hres, Result.map]
    obtain ⟨owned', st', _⟩ := prim_step_pure st hx hc hvs hden sound
    exact ⟨v, H, owned', hev, st', same, sameP⟩

/-- An argument binding (a move, immediate copy, or borrowed copy) changes no heap and keeps the
token count: the bound value's token is the argument's (or vacuous). -/
theorem arg_step_refs (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} {a : Arg} (hx : x ∉ live)
    {Γ' : Ctx} (hc : bindCtx Γ x (.arg a) borrows uniqs ctors = .ok Γ')
    {w : Fir.Val} (hw : a.eval ρf = some w) :
    ∃ v owned', Own.evalArg ρo a = some v ∧
      OwnedState functions H external (live ++ [x]) Γ' (ρf.insert x w) (ρo.insert x v) owned'
        lex Δ Jf Jo borrows uniqs retUniq ctors K priv slots slotVals ∧ SameRefs owned' owned := by
  cases a with
  | var y =>
    simp only [bindCtx] at hc
    cases hi : Γ.isImm y with
    | true =>
      simp only [hi, ↓reduceIte, Except.ok.injEq] at hc
      subst hc
      obtain ⟨v, w', hv, hw', hd⟩ := st.den y (by simp [Ctx.avail_eq, hi])
      have : w' = w := Option.some.inj (hw'.symm.trans hw); subst this
      obtain ⟨u, hu, himm⟩ := st.immOk y hi
      have huv : u = v := Option.some.inj (hu.symm.trans hv); subst huv
      cases huy : Γ.isUniq y with
      | true =>
        simp only [↓reduceIte]
        obtain ⟨_, u', hu', hvu⟩ := st.uniqOk y huy
        have : u' = u := Option.some.inj (hu'.symm.trans hv); subst this
        have himmU : ImmUniq ctors u' := by
          refine ⟨himm, ?_⟩
          cases u' with
          | loc l => exact absurd rfl (himm l)
          | ctor0 c => exact hvu
          | lit _ | erased => trivial
        exact ⟨u', owned, hv, st.pre.bindImmUniq hx hd himmU st.counts, SameRefs.refl _⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨u, owned, hv, st.pre.bindImm hx hd himm st.counts, SameRefs.refl _⟩
    | false =>
      simp only [hi, Bool.false_eq_true, ↓reduceIte] at hc
      by_cases hpb : (Γ.tokens y == 0 && Γ.isPbrw y) = true
      · simp only [hpb, ↓reduceIte, Except.ok.injEq] at hc
        subst hc
        have hpb' : Γ.isPbrw y = true := (Bool.and_eq_true _ _).mp hpb |>.2
        have havy : Γ.avail y = true := by simp [Ctx.avail_eq, hpb']
        obtain ⟨v, w', hv, hw', hd⟩ := st.den y havy
        have : w' = w := Option.some.inj (hw'.symm.trans hw); subst this
        obtain ⟨u, hu, hreach⟩ := st.pbrwOk y hpb'
        have huv : u = v := Option.some.inj (hu.symm.trans hv); subst huv
        have hpv : ∀ l, priv l → u ≠ .loc l := fun l hl hEq => st.privNoVar l hl y havy (hEq ▸ hv)
        exact ⟨u, owned, hv, st.pre.bindPbrw hx hd hreach st.counts hpv, SameRefs.refl _⟩
      · have hpbF : (Γ.tokens y == 0 && Γ.isPbrw y) = false := by
          cases hb : (Γ.tokens y == 0 && Γ.isPbrw y)
          · rfl
          · exact absurd hb hpb
        simp only [hpbF, Bool.false_eq_true, ↓reduceIte] at hc
        obtain ⟨Γ₁, ht, hΓ⟩ := except_bind_ok hc
        have hΓ := except_pure_ok hΓ; subst hΓ
        obtain ⟨v, w', owned₁, hv, hw', hd, inv₁, hs, hwk⟩ := take_sem st.takeInv ht
        have : w' = w := Option.some.inj (hw'.symm.trans hw); subst this
        have hle : ∀ k, refsIn k owned₁ ≤ refsIn k owned := fun k => by
          have := hs k; simp only [refsIn] at this; omega
        have pre₁ := st.pre.weaker hwk inv₁.roots hle
        have havy : Γ.avail y = true := by
          rcases Ctx.take_ok ht with ⟨hi', _⟩ | ⟨_, n, hn, _⟩
          · simp [Ctx.avail_eq, hi']
          · simp [Ctx.avail_eq, Ctx.tokens_eq, hn]
        have hpriv_v : ∀ l, pre₁.localPriv l → v ≠ .loc l := fun l hl hEq => by
          have h0 := taken_avoids_localPriv st hwk inv₁.roots (taken := [v])
            (by simpa using hs) (fun l' hl' => by
              have : v ≠ .loc l' := fun h => st.privNoVar l' hl' y havy (h ▸ hv)
              simp [refsIn, this]) l hl
          subst hEq; simp [refsIn] at h0
        have hbal' : Balance H external ((v :: owned₁) ++ slotVals) :=
          (SameRefs.append hs (SameRefs.refl slotVals)).balance st.counts
        by_cases hwu : (Γ.isUniq y && Γ.tokens y == 1) = true
        · simp only [hwu, ↓reduceIte]
          have huy : Γ.isUniq y = true := (Bool.and_eq_true _ _).mp hwu |>.1
          obtain ⟨_, u', hu', hvu⟩ := st.uniqOk y huy
          have : u' = v := Option.some.inj (hu'.symm.trans hv); subst this
          have hvU : UniqVal ctors H external ((u' :: owned₁) ++ slotVals) u' :=
            hvu.sameRefs (fun k => by rw [refsIn_append, hs k, refsIn_append])
          exact ⟨u', u' :: owned₁, hv, pre₁.bindUniqOwned hx hd hbal' hvU hpriv_v, hs.symm⟩
        · have hwuF : (Γ.isUniq y && Γ.tokens y == 1) = false := by
            cases hb : (Γ.isUniq y && Γ.tokens y == 1)
            · rfl
            · exact absurd hb hwu
          simp only [hwuF, Bool.false_eq_true, ↓reduceIte]
          exact ⟨v, v :: owned₁, hv, pre₁.bindOwned hx hd hbal' hpriv_v, hs.symm⟩
  | lit l =>
    cases hc
    have : w = .lit l := (Option.some.inj hw).symm; subst this
    exact ⟨.lit l, owned, rfl,
      st.pre.bindImmUniq hx (Proof.den_lit H l) ⟨(fun _ h => by cases h), trivial⟩ st.counts,
      SameRefs.refl _⟩
  | erased =>
    cases hc
    have : w = .erased := (Option.some.inj hw).symm; subst this
    exact ⟨.erased, owned, rfl,
      st.pre.bindImmUniq hx (Proof.den_erased H) ⟨(fun _ h => by cases h), trivial⟩ st.counts,
      SameRefs.refl _⟩

end

end IxCC.Own.Plain
