import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarInstr
import IxCC.Cfg.Rc.Proof.Physical.Bridge.RawSlots
import IxCC.Rt.Proof.LowerRep
import IxCC.Own.Proof.Unfold

/-!
# The raw path of a pure binding on the plain-RC route

A 64-bit word operation that reads or writes a raw register runs on raw operands
(`Rt.Lower.rawWord`): its operands at the flags `rawFlag` gives (`slot_operands_words`), the
tagged ones untagged by a shift (`untagAt_run`), the raw core (`LowerRep.wordRaw64_core`, over
the whole of `[0, 2^64)`), and the result raw or retagged through `checked64` (`checked64_run`,
`natOverflow` at or above `2^63`). A copy into a raw register moves a raw word. Both keep every
register below the supply but the destination, so the tagged relation over the omitted registers
(`Omit`) and the raw one (`RawWords`) survive (`raw_pure_sim`).
-/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs
open IxCC.Lir (Word)
open IxCC.Src (NatMap)

/-- A pure binding on the raw path: a 64-bit word operation `rawPrim` takes, or a copy into a raw
register of a raw register or a literal. -/
def RawPure (T : Tables) (f x : Nat) : Own.Rhs → Prop
  | .fir (.prim op as) => rawPrim T f x op as = true
  | .fir (.arg a) => T.rawVar f x = true ∧ Cfg.Rc.Raw.argFits (T.rawVar f) true a = true
  | _ => False

/-- The raw path is a 64-bit word operation's. -/
theorem rawPrim_word {T : Tables} {f : Fir.FunId} {x : Nat} {op : Lam.Prim} {as : List Fir.Arg}
    (h : rawPrim T f x op as = true) : ∃ o, op = .word .w64 o := by
  unfold rawPrim at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- An operand's word as the raw core reads it: a raw word as it is, a tagged one untagged. -/
def untagWord (raw : Bool) (w : Word) : Word := if raw then w else w >>> 1

/-- A word operation's operands fit the flags `rawFlag` gives them. -/
theorem argsFit_rawFlag (T : Tables) (f : Fir.FunId) :
    ∀ as : List Fir.Arg, Cfg.Rc.Raw.argsFit (T.rawVar f) (as.map (rawFlag T f)) as = true
  | [] => rfl
  | a :: as => by
    simp only [Cfg.Rc.Raw.argsFit, List.map_cons, List.headD_cons, List.tail_cons, Bool.and_eq_true]
    refine ⟨?_, argsFit_rawFlag T f as⟩
    cases a <;> simp [Cfg.Rc.Raw.argFits, rawFlag]

/-- The numbers of operands at their positions, as the raw core reads them. -/
theorem slots_untag {addresses : AddressMap} :
    ∀ {rs : List Bool} {vs : List Own.RVal} {ws : List Word},
      SlotsRel addresses rs vs ws → rs.length = vs.length →
      ∀ {ns : List Nat}, Own.natArgs vs = some ns →
        ListRel (fun n w => w.toNat = n) ns (List.zipWith untagWord rs ws)
  | _, _, _, .nil _, _, ns, numbers => by
    simp only [Own.natArgs, Option.some.injEq] at numbers
    subst numbers
    simp only [List.zipWith_nil_right]
    exact .nil
  | rs, v :: vs, w :: ws, .cons hv tail, length, ns, numbers => by
    cases rs with
    | nil => simp at length
    | cons r rs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at length
      simp only [List.headD_cons, List.tail_cons] at hv tail
      match v, numbers with
      | .lit (.nat n), numbers =>
        simp only [Own.natArgs] at numbers
        cases rest : Own.natArgs vs with
        | none => simp [rest] at numbers
        | some ns' =>
          simp only [rest, Option.map_some, Option.some.injEq] at numbers
          subst numbers
          simp only [List.zipWith_cons_cons]
          refine .cons ?_ (slots_untag tail length rest)
          cases r with
          | true =>
            simp only [untagWord, ↓reduceIte]
            exact RawVal.toNat (SlotVal.raw.1 hv)
          | false =>
            simp only [untagWord, Bool.false_eq_true, ↓reduceIte]
            exact untag_toNat (SlotVal.tagged.1 hv)

/-- Operands that read below the supply keep their words while a temporary is assigned. -/
theorem evalArgs_temp {sup t : Nat} (ht : sup ≤ t) (u : Word) {ρl : Lir.Env} :
    ∀ {las : List Lir.Arg}, (∀ la ∈ las, ArgReads sup la) →
      Lir.evalArgs (ρl.insert t u) las = Lir.evalArgs ρl las
  | [], _ => rfl
  | la :: las, reads => by
    have rest := evalArgs_temp (las := las) (ρl := ρl) ht u
      (fun la' member => reads la' (List.mem_cons_of_mem _ member))
    simp only [Lir.evalArgs_cons, arg_eval_temp (reads la (List.mem_cons_self ..)) ht u, rest]

/-- **Untagging the operands read from tagged registers**: straight-line shifts into fresh
registers, keeping every register below the supply. -/
theorem untagAt_run {T : Tables} {f : Fir.FunId} {mem : X86.Memory} {ctx : Word} :
    ∀ {as : List Fir.Arg} {las : List Lir.Arg} {st st₁ : St} {us : List Lir.Arg},
      (untagAt T f as las).run st = .ok (us, st₁) →
      ∃ ss, st₁ = { st with acc := ss.reverse ++ st.acc, fresh := st₁.fresh } ∧
        st.fresh ≤ st₁.fresh ∧ (∀ s ∈ ss, s.isCall = false) ∧
        ∀ (ρl : Lir.Env) (ws : List Word), Lir.evalArgs ρl las = some ws →
          (∀ la ∈ las, ArgReads st.fresh la) →
          ∃ ρl₁, Lir.execList ρl mem ctx ss = some (ρl₁, mem) ∧
            (∀ y, y < st.fresh → ρl₁[y]? = ρl[y]?) ∧
            Lir.evalArgs ρl₁ us = some (List.zipWith untagWord (as.map (rawFlag T f)) ws) ∧
            ∀ u ∈ us, ArgReads st₁.fresh u
  | [], las, st, st₁, us, h => by
    have h' : (pure [] : M (List Lir.Arg)).run st = .ok (us, st₁) := by
      cases las <;> exact h
    simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    refine ⟨[], by cases st; rfl, Nat.le_refl _, by simp, ?_⟩
    intro ρl ws _ _
    exact ⟨ρl, rfl, fun _ _ => rfl, by simp, by simp⟩
  | a :: as, [], st, st₁, us, h => by
    simp only [untagAt, StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨[], by cases st; rfl, Nat.le_refl _, by simp, ?_⟩
    intro ρl ws evaluated _
    simp only [Lir.evalArgs_nil, Option.some.injEq] at evaluated
    subst evaluated
    exact ⟨ρl, rfl, fun _ _ => rfl, by simp, by simp⟩
  | a :: as, la :: las, st, st₁, us, h => by
    simp only [untagAt] at h
    cases flag : rawFlag T f a with
    | true =>
      simp only [flag, ↓reduceIte] at h
      obtain ⟨u, st₀, hu, h'⟩ := run_bind h
      obtain ⟨us', st₁', hus, hpure⟩ := run_bind h'
      simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hpure hu
      obtain ⟨rfl, rfl⟩ := hpure
      obtain ⟨rfl, rfl⟩ := hu
      obtain ⟨ss, state, grows, noCall, sem⟩ := untagAt_run (mem := mem) (ctx := ctx) hus
      refine ⟨ss, state, grows, noCall, ?_⟩
      intro ρl ws evaluated reads
      simp only [Lir.evalArgs_cons] at evaluated
      cases hw : la.eval ρl with
      | none => simp [hw] at evaluated
      | some w =>
        cases hws : Lir.evalArgs ρl las with
        | none => simp [hw, hws] at evaluated
        | some ws' =>
          simp only [hw, hws, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at evaluated
          subst evaluated
          obtain ⟨ρl₁, exec, keep, evalUs, readsUs⟩ :=
            sem ρl ws' hws (fun la' member => reads la' (by simp [member]))
          refine ⟨ρl₁, exec, keep, ?_, ?_⟩
          · have same : la.eval ρl₁ = some w := by
              rw [← hw]
              cases la with
              | v y => exact keep y (reads (.v y) (by simp) y rfl)
              | imm _ => rfl
            simp [Lir.evalArgs_cons, same, evalUs, untagWord, flag]
          · intro u' member
            rcases List.mem_cons.mp member with rfl | member
            · intro y equal
              exact Nat.lt_of_lt_of_le (reads _ (by simp) y equal) grows
            · exact readsUs u' member
    | false =>
      simp only [flag, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨u, st₀, hu, h'⟩ := run_bind h
      obtain ⟨us', st₁', hus, hpure⟩ := run_bind h'
      simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hpure
      obtain ⟨rfl, rfl⟩ := hpure
      have run : (bin .shr la (.imm 1)).run st = .ok (Lir.Arg.v st.fresh,
          { st with
            fresh := st.fresh + 1
            acc := Lir.Stmt.assign st.fresh (.bin .shr .w64 la (.imm 1)) :: st.acc }) := rfl
      rw [run] at hu
      simp only [Except.ok.injEq, Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      obtain ⟨ss, state, grows, noCall, sem⟩ := untagAt_run (mem := mem) (ctx := ctx) hus
      refine ⟨.assign st.fresh (.bin .shr .w64 la (.imm 1)) :: ss, ?_, ?_, ?_, ?_⟩
      · rw [state]
        simp
      · exact Nat.le_trans (Nat.le_succ _) grows
      · intro s member
        rcases List.mem_cons.mp member with rfl | member
        · rfl
        · exact noCall s member
      · intro ρl ws evaluated reads
        simp only [Lir.evalArgs_cons] at evaluated
        cases hw : la.eval ρl with
        | none => simp [hw] at evaluated
        | some w =>
          cases hws : Lir.evalArgs ρl las with
          | none => simp [hw, hws] at evaluated
          | some ws' =>
            simp only [hw, hws, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at evaluated
            subst evaluated
            let ρl₀ := ρl.insert st.fresh (w >>> 1)
            have exec₀ : (Lir.Stmt.assign st.fresh (.bin .shr .w64 la (.imm 1))).exec ρl mem ctx =
                some (ρl₀, mem) := by
              simp [lir_eval, hw, ρl₀]
            have evaluated₀ : Lir.evalArgs ρl₀ las = some ws' := by
              show Lir.evalArgs (ρl.insert st.fresh (w >>> 1)) las = some ws'
              rw [evalArgs_temp (Nat.le_refl _) _ (fun la' member => reads la' (by simp [member]))]
              exact hws
            obtain ⟨ρl₁, exec, keep, evalUs, readsUs⟩ :=
              sem ρl₀ ws' evaluated₀ (fun la' member y equal =>
                Nat.lt_succ_of_lt (reads la' (by simp [member]) y equal))
            refine ⟨ρl₁, ?_, ?_, ?_, ?_⟩
            · simp only [Lir.execList, exec₀]
              exact exec
            · intro y below
              rw [keep y (Nat.lt_succ_of_lt below)]
              exact Lir.env_insert_ne _ _ (Nat.ne_of_gt below)
            · have same : ρl₁[st.fresh]? = some (w >>> 1) := by
                rw [keep st.fresh (Nat.lt_succ_self _)]
                exact Lir.env_insert_self _ _ _
              simp [Lir.evalArgs_cons, Lir.Arg.eval_v, same, evalUs, untagWord, flag]
            · intro u' member
              rcases List.mem_cons.mp member with rfl | member
              · intro y equal
                cases equal
                exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) grows
              · exact readsUs u' member

/-- `checked64` from any open state: the check's code, then `x := 2r + 1`. -/
theorem checked64_run (x r : Nat) (st : St) :
    (checked64 x (.v r)).run st = .ok ((), CheckSt st .natOverflow [] [.assign x (retag (.v r))]
      (.br .ugt (.v r) (.imm 0x7fffffffffffffff) (loc st.next) (loc (st.next + 1))) st.fresh) := rfl

/-- A failure reached after a run is a failure of its start. -/
theorem fails_back {lp : Lir.Program} {s s' : Lir.State} {c : Nat}
    (run : Sem.Star (Lir.semStep lp) s c s') (failed : Sem.Fails (Lir.semStep lp) s') :
    Sem.Fails (Lir.semStep lp) s := by
  obtain ⟨c₂, final, r, run₂, stuck⟩ := failed
  exact ⟨c + c₂, final, r, run.trans run₂, stuck⟩

/-- **A binding at its position**: the destination holds the value's word at its own raw or
tagged position, every other register below the supply as before. -/
theorem omit_insert_frame {addresses : AddressMap} {T : Tables} {f : Fir.FunId} {fd : Cfg.Fun}
    {sup : Nat} {ρ : Own.Env} {ρl ρl' : Lir.Env}
    (words : FusedWords addresses (Omit T f fd) sup ρ ρl) (raws : RawWords (T.rawVar f) ρ ρl)
    {x : Nat} (hx : x < sup) {v : Own.RVal} {w : Word} (hρx : ρl'[x]? = some w)
    (same : ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?)
    (slot : SlotVal addresses (T.rawVar f x) v w) :
    FusedWords addresses (Omit T f fd) sup (ρ.insert x v) ρl' ∧
      RawWords (T.rawVar f) (ρ.insert x v) ρl' := by
  cases flag : T.rawVar f x with
  | true =>
    rw [flag] at slot
    refine ⟨(words.bind_omitted hx (.inr flag) v).agree ?_,
      raws.insert_raw words.dom (SlotVal.raw.1 slot) hρx same⟩
    intro y u lookup live
    have ne : y ≠ x := fun equal => live (equal ▸ .inr flag)
    exact same y ((words.bind_omitted hx (.inr flag) v).dom lookup) ne
  | false =>
    rw [flag] at slot
    refine ⟨(words.bind hx (SlotVal.tagged.1 slot)).agree ?_,
      raws.insert_tagged words.dom flag v same⟩
    intro y u lookup _
    by_cases equal : y = x
    · subst y
      rw [hρx, Lir.env_insert_self]
    · rw [Lir.env_insert_ne _ _ (Ne.symm equal)]
      exact same y ((words.bind hx (SlotVal.tagged.1 slot)).dom lookup) equal

/-- The raw word a 64-bit word operation computes, as a raw slot. -/
theorem rawVal_of_toNat {n : Nat} {w : Word} (hw : w.toNat = n) : RawVal (.lit (.nat n)) w := by
  subst hw
  refine ⟨?_, (UInt64.ofNat_toNat).symm⟩
  have := w.toNat_lt_size
  exact this

/-- **The raw path of a 64-bit word operation simulates it**, over the tagged relation (which
omits raw registers) and the raw one. Its operands are read at the flags `rawFlag` gives; a
tagged destination is retagged through `checked64`, whose overflow branch is the actual
`natOverflow` failure. -/
theorem rawWord_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {fd : Cfg.Fun} {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat}
    {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {op : Src.WordOp} {as : List Fir.Arg}
    (hrun : (rawWord f T x op as).run st = .ok (true, st')) (hC : Ext C st') (hl : Labels st)
    (ho : Open st) (hsup : sup ≤ st.fresh) (hx : x < sup)
    (hlive : ∀ a ∈ as, LiveArg (Fused T fd) a)
    {addresses : AddressMap} {H H' : Own.Heap} {ρ : Own.Env} {ρl : Lir.Env} {mem : X86.Memory}
    {rest : List Lir.Frame} {v : Own.RVal}
    (words : FusedWords addresses (Omit T f fd) sup ρ ρl) (raws : RawWords (T.rawVar f) ρ ρl)
    (effect : Own.evalRhs .rc (ownTables T) ρ H (.fir (.prim (.word .w64 op) as)) = .ok (v, H')) :
    (∃ charge after n, v = .lit (.nat n) ∧
      Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) charge
        (Lir.atState mem ctx fn (off + st'.cur) st'.acc.length after rest) ∧
      FusedWords addresses (Omit T f fd) sup (ρ.insert x v) after ∧
      RawWords (T.rawVar f) (ρ.insert x v) after) ∨
    Sem.Fails (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) := by
  unfold rawWord at hrun
  obtain ⟨las, hops, _, hk⟩ := (withOperandsAt_run hrun).resolve_right fun failed => by
    obtain ⟨_, impossible, _⟩ := failed
    cases impossible
  obtain ⟨us, st₁, hu, hk'⟩ := run_bind hk
  obtain ⟨ss, state, grows₁, noCall, untagged⟩ := untagAt_run (mem := mem) (ctx := ctx) hu
  obtain ⟨_, hl₁, ho₁⟩ := Mono.untagAt' T f as las hu hl ho
  have hcur : st₁.cur = st.cur := by rw [state]
  have hacc : st₁.acc = ss.reverse ++ st.acc := by rw [state]
  -- the source value
  obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim effect
  obtain ⟨ws, hws, slots, reads⟩ :=
    slot_operands_words words raws hops (argsFit_rawFlag T f as) hlive hvs
  simp only [Own.primResult] at hres
  cases hn : Own.natArgs vs with
  | none => simp [hn] at hres
  | some ns =>
  simp only [hn] at hres
  cases hs : (Lam.Prim.word .w64 op).sem ns with
  | none => simp [hs] at hres
  | some r =>
  cases r with
  | bool b => exact absurd hs (word_not_bool .w64 op ns b)
  | nat n =>
  simp only [hs, Sem.Result.ok.injEq] at hres
  subst hres
  have nums := slots_untag slots (by simp [Own.evalArgs_length ρ hvs]) hn
  obtain ⟨ρl₁, exec, keep₁, evalUs, readsUs⟩ := untagged ρl ws hws
    (fun la member y equal => Nat.lt_of_lt_of_le (reads la member y equal) hsup)
  -- the shifts
  have grow₁ : Grows st₁ st' := by
    split at hk'
    · exact (Mono.wordRaw64' f x op us hk' hl₁ ho₁).1
    · exact (Mono.bind' Mono.freshReg' (fun r => Mono.bind' (Mono.wordRaw64' f r op us)
        (fun _ => Mono.checked64' x (.v r))) hk' hl₁ ho₁).1
  have ext₁ : Ext C { st with acc := ss.reverse ++ st.acc, fresh := st₁.fresh } :=
    state ▸ grow₁.ext hC
  have star₁ := straight_star (rest := rest) hF hH ext₁ ho noCall exec
  cases flag : T.rawVar f x with
  | true =>
    rw [if_pos flag] at hk'
    have core := LowerRep.wordRaw64_core (ctx := ctx) hF hH hk' hC hl₁ ho₁ (Nat.le_refl _)
      (Nat.lt_of_lt_of_le hx (Nat.le_trans hsup grows₁))
    obtain ⟨c, ρl', w, star₂, hw, hρx, keep₂⟩ := core ρl₁ mem rest ns _ n evalUs nums readsUs hs
    rw [hcur, hacc] at star₂
    have same : ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]? := fun y below ne =>
      (keep₂ y (Nat.lt_of_lt_of_le below (Nat.le_trans hsup grows₁)) ne).trans
        (keep₁ y (Nat.lt_of_lt_of_le below hsup))
    obtain ⟨afterWords, afterRaws⟩ := omit_insert_frame words raws hx hρx same
      (v := .lit (.nat n)) (by rw [flag]; exact SlotVal.raw.2 (rawVal_of_toNat hw))
    exact .inl ⟨0 + c, ρl', n, rfl, star₁.trans star₂, afterWords, afterRaws⟩
  | false =>
    rw [if_neg (by simp [flag])] at hk'
    obtain ⟨r, st₂, hr, hk''⟩ := run_bind hk'
    have fresh : freshReg.run st₁ = .ok (st₁.fresh, { st₁ with fresh := st₁.fresh + 1 }) := rfl
    rw [fresh] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨⟨⟩, st₃, hw64, hchk⟩ := run_bind hk''
    rw [checked64_run] at hchk
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hchk
    subst hchk
    obtain ⟨_, hl₂, ho₂⟩ := Mono.freshReg' (show freshReg.run st₁ = .ok (st₁.fresh,
      { st₁ with fresh := st₁.fresh + 1 }) from rfl) hl₁ ho₁
    obtain ⟨grow₃, hl₃, ho₃⟩ := Mono.wordRaw64' f st₁.fresh op us hw64 hl₂ ho₂
    have ext₃ : Ext C st₃ := (Mono.checked64' x (.v st₁.fresh) (checked64_run x st₁.fresh st₃)
      hl₃ ho₃).1.ext hC
    have core := LowerRep.wordRaw64_core (ctx := ctx) hF hH hw64 ext₃ hl₂ ho₂ (Nat.le_refl _)
      (Nat.lt_succ_self st₁.fresh)
    obtain ⟨c, ρl₂, u, star₂, hu₂, hρr, keep₂⟩ := core ρl₁ mem rest ns _ n evalUs nums
      (fun u member y equal => Nat.lt_succ_of_lt (readsUs u member y equal)) hs
    rw [hcur, hacc] at star₂
    rcases checked_core (sup := st₁.fresh + 1) (ss1 := []) hF hH hC hl₃ ho₃ (by simp)
        (ρl := ρl₂) (mem := mem) (rest := rest) rfl hρr hu₂ (fun _ _ => rfl)
      with ⟨c₃, ρl', w, star₃, hw, hρx, keep₃⟩ | failed
    · have same : ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]? := by
        intro y below ne
        have small : y < st₁.fresh := Nat.lt_of_lt_of_le below (Nat.le_trans hsup grows₁)
        rw [keep₃ y (Nat.lt_succ_of_lt small) ne, keep₂ y (Nat.lt_succ_of_lt small)
          (Nat.ne_of_lt small)]
        exact keep₁ y (Nat.lt_of_lt_of_le below hsup)
      obtain ⟨afterWords, afterRaws⟩ := omit_insert_frame words raws hx hρx same
        (v := .lit (.nat n)) (by rw [flag]; exact SlotVal.tagged.2 (show valueWord addresses (.lit (.nat n)) = some w from hw))
      exact .inl ⟨_, ρl', n, rfl, (star₁.trans star₂).trans star₃, afterWords, afterRaws⟩
    · exact .inr (fails_back (star₁.trans star₂) failed)

/-- **A copy into a raw register** moves the raw word of a raw register or a literal. -/
theorem rawCopy_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {fd : Cfg.Fun} {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat}
    {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {a : Fir.Arg} (rawX : T.rawVar f x = true)
    (fits : Cfg.Rc.Raw.argFits (T.rawVar f) true a = true)
    (hrun : (instr f T (.bind x (.fir (.arg a)))).run st = .ok (true, st')) (hC : Ext C st')
    (ho : Open st) (hx : x < sup) (hlive : LiveArg (Fused T fd) a)
    {addresses : AddressMap} {H H' : Own.Heap} {ρ : Own.Env} {ρl : Lir.Env} {mem : X86.Memory}
    {rest : List Lir.Frame} {v : Own.RVal}
    (words : FusedWords addresses (Omit T f fd) sup ρ ρl) (raws : RawWords (T.rawVar f) ρ ρl)
    (effect : Own.evalRhs .rc (ownTables T) ρ H (.fir (.arg a)) = .ok (v, H')) :
    ∃ after, Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) 0
        (Lir.atState mem ctx fn (off + st'.cur) st'.acc.length after rest) ∧
      FusedWords addresses (Omit T f fd) sup (ρ.insert x v) after ∧
      RawWords (T.rawVar f) (ρ.insert x v) after ∧ ValueCtorOk T v := by
  simp only [instr] at hrun
  obtain ⟨las, hops, _, hk⟩ := (withOperandsAt_run hrun).resolve_right fun failed => by
    obtain ⟨_, impossible, _⟩ := failed
    cases impossible
  obtain ⟨la, rfl, hop⟩ := operandsAt_one hops
  simp only [assign_run, Except.ok.injEq, Prod.mk.injEq, true_and] at hk
  subst hk
  obtain ⟨_, hv⟩ := evalRhs_arg (T := ownTables T) effect
  simp only [List.headD_cons, rawX] at hop
  obtain ⟨w, hw, slot, _⟩ := slot_operand_word words raws hop fits hlive hv
  have exec : Lir.execList ρl mem ctx [Lir.Stmt.assign x (.arg la)] =
      some (ρl.insert x w, mem) := by
    simp [lir_eval, hw]
  have star := straight_star (rest := rest) (ss := [Lir.Stmt.assign x (.arg la)]) (f' := st.fresh)
    hF hH hC ho (by simp [Lir.Stmt.isCall]) exec
  obtain ⟨afterWords, afterRaws⟩ := omit_insert_frame words raws hx (Lir.env_insert_self ..)
    (fun y _ ne => Lir.env_insert_ne _ _ (Ne.symm ne)) (by rw [rawX]; exact slot)
  obtain ⟨n, rfl, _, _⟩ := (SlotVal.raw.1 slot).lit
  exact ⟨ρl.insert x w, star, afterWords, afterRaws, trivial⟩

/-- **A pure binding on the raw path simulates it**, over the tagged relation (which omits raw
registers) and the raw one. -/
theorem raw_pure_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {fd : Cfg.Fun} {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat}
    {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {st st' : St} {x : Nat} {r : Own.Rhs} (raw : RawPure T f x r)
    (hrun : (instr f T (.bind x r)).run st = .ok (true, st')) (hC : Ext C st') (hl : Labels st)
    (ho : Open st) (hsup : sup ≤ st.fresh) (hx : x < sup)
    (hlive : ∀ y ∈ Cfg.Check.rhsVars r, ¬ Fused T fd y)
    {addresses : AddressMap} {H H' : Own.Heap} {ρ : Own.Env} {ρl : Lir.Env} {mem : X86.Memory}
    {rest : List Lir.Frame} {v : Own.RVal}
    (words : FusedWords addresses (Omit T f fd) sup ρ ρl) (raws : RawWords (T.rawVar f) ρ ρl)
    (effect : Own.evalRhs .rc (ownTables T) ρ H r = .ok (v, H')) :
    (∃ charge after,
      Sem.Star (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) charge
        (Lir.atState mem ctx fn (off + st'.cur) st'.acc.length after rest) ∧
      FusedWords addresses (Omit T f fd) sup (ρ.insert x v) after ∧
      RawWords (T.rawVar f) (ρ.insert x v) after ∧ ValueCtorOk T v) ∨
    Sem.Fails (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) := by
  match r, raw, hrun, hlive, effect with
  | .fir (.prim op as), raw, hrun, hlive, effect =>
    obtain ⟨o, rfl⟩ := rawPrim_word raw
    simp only [instr] at hrun
    have raw' : rawPrim T f x (.word .w64 o) as = true := raw
    rw [if_pos raw'] at hrun
    change (rawWord f T x o as).run st = .ok (true, st') at hrun
    rcases rawWord_sim hF hH hrun hC hl ho hsup hx (liveArgs_of hlive) words raws effect with
      ⟨charge, after, n, rfl, trace, afterWords, afterRaws⟩ | failed
    · exact .inl ⟨charge, after, trace, afterWords, afterRaws, trivial⟩
    · exact .inr failed
  | .fir (.arg a), ⟨rawX, fits⟩, hrun, hlive, effect =>
    obtain ⟨after, trace, afterWords, afterRaws, compatible⟩ := rawCopy_sim hF hH rawX fits hrun hC ho
      hx (liveArgs_of hlive a (by simp)) words raws effect
    exact .inl ⟨0, after, trace, afterWords, afterRaws, compatible⟩

end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
