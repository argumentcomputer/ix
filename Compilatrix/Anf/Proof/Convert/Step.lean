import Compilatrix.Anf.Proof.Convert.Force

/-! # ANF conversion: the simulation at one fuel level

`ConvAt n fuel` states the simulation, at clock bound `n`, of every function
of the conversion (`conv`, `caseOn`, `caseBody`, `convAlts`, `convList`,
`convArgs`, `groups`, `spine`) at fuel `fuel`: from related environments and
a related continuation, the converted code simulates the Lam computation
followed by the continuation's source (P1, M2.3). Every function at
`fuel + 1` calls the others at `fuel`, so `ConvAt n` holds at every fuel by
induction (`Convert/Level`), given application at `n` and bodies below `n`.

This module fixes the statement and the facts the cases share: operand
lists, argument slots against expected kinds, primitives and projections on
related values, and λ-telescopes in plain positions. -/

set_option autoImplicit false

namespace Compilatrix.Anf.Convert.Proof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Lam (Kind Mode argSlot applyArgs)
open Compilatrix.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec)
open Compilatrix.Ixon

namespace Setting

variable (S : Setting)

/-- Operand lists whose values are related plain values. -/
def OpdsR (xs : List Lam.Val) (os : List Opd) (ρ : List Val) : Prop :=
  ∃ ws, os.mapM (·.val ρ) = some ws ∧ VRs S.A S.G xs ws

/-- Argument slots against values, by the kinds `e` expects from position
`i`. -/
inductive ArgsE (e : Nat → Kind) : Nat → List Lam.Slot → List Val → Prop
  | nil {i : Nat} : ArgsE e i [] []
  | cons {i : Nat} {s : Lam.Slot} {ss : List Lam.Slot} {w : Val} {ws : List Val} :
      SlotR S.A S.G (e i) s w → ArgsE e (i + 1) ss ws → ArgsE e i (s :: ss) (w :: ws)

/-- Argument operands against slots, by the spine's expected kinds. -/
def SlotsMatch (tele : List Mode) (sigs : List (List Mode)) (i : Nat) (ss : List Lam.Slot)
    (os : List Opd) (ρ : List Val) : Prop :=
  ∃ ws, os.mapM (·.val ρ) = some ws ∧ S.ArgsE (expKind tele sigs) i ss ws

/-- The source of a `case` on a value. -/
def caseSrc (k : Nat) (ρ : Lam.Env) (v : Lam.Val) (alts : List Lam.Alt) (dflt : Option Lam.Term) :
    Result Lam.Val :=
  match v.asCtor S.L.known with
  | some (c, fs) => Lam.evalAlts S.L k ρ c fs alts dflt
  | none => .stuck

/-- Well-moded alternatives and default. -/
def AltsOk (ks : List Kind) (alts : List Lam.Alt) : Prop :=
  ∀ a ∈ alts, TermOk S.G (List.replicate a.arity .strict ++ ks) a.body

def DfltOk (ks : List Kind) (dflt : Option Lam.Term) : Prop := ∀ t ∈ dflt, TermOk S.G ks t

/-- A default and its conversion: both absent, or simulating. -/
def DfltSim (n : Nat) (ρ : Lam.Env) (ρ' : List Val) (J' : List JClo)
    (SK : Lam.Val → Nat → Result Lam.Val) (dflt : Option Lam.Term) (dflt' : Option Exp) : Prop :=
  (dflt = none ∧ dflt' = none) ∨ ∃ t e, dflt = some t ∧ dflt' = some e ∧
    SimUpTo S.V n (fun k => (Lam.eval S.L k ρ t).bind (SK · k)) (fun k => eval S.Q k ρ' J' e)

/-- The simulation of every conversion function at fuel `fuel`, clock bound
`n`. -/
structure ConvAt (n fuel : Nat) : Prop where
  conv : ∀ ⦃cx : Cx⦄ ⦃t : Lam.Term⦄ ⦃k : Kont⦄ ⦃e : Exp⦄ ⦃ρ : Lam.Env⦄ ⦃ρ' : List Val⦄
      ⦃J' : List JClo⦄ ⦃ks : List Kind⦄ ⦃SK : Lam.Val → Nat → Result Lam.Val⦄,
    conv S.A fuel cx t k = .ok e → EnvR S.A S.G ks cx.vars ρ ρ' → ρ'.length = cx.d →
    J'.length = cx.dj → S.KontR n cx.dj k SK ρ' J' → TermOk S.G ks t →
    SimUpTo S.V n (fun k => (Lam.eval S.L k ρ t).bind (SK · k)) (fun k => eval S.Q k ρ' J' e)
  caseOn : ∀ ⦃cx : Cx⦄ ⦃o : Opd⦄ ⦃alts : List Lam.Alt⦄ ⦃dflt : Option Lam.Term⦄ ⦃k : Kont⦄
      ⦃e : Exp⦄ ⦃ρ : Lam.Env⦄ ⦃ρ' : List Val⦄ ⦃J' : List JClo⦄ ⦃ks : List Kind⦄
      ⦃SK : Lam.Val → Nat → Result Lam.Val⦄ ⦃v : Lam.Val⦄ ⦃w : Val⦄,
    caseOn S.A fuel cx o alts dflt k = .ok e → EnvR S.A S.G ks cx.vars ρ ρ' → ρ'.length = cx.d →
    J'.length = cx.dj → S.KontR n cx.dj k SK ρ' J' → o.val ρ' = some w → S.V v w →
    S.AltsOk ks alts → S.DfltOk ks dflt →
    SimUpTo S.V n (fun k => (S.caseSrc k ρ v alts dflt).bind (SK · k)) (fun k => eval S.Q k ρ' J' e)
  caseBody : ∀ ⦃cx : Cx⦄ ⦃o : Opd⦄ ⦃alts : List Lam.Alt⦄ ⦃dflt : Option Lam.Term⦄ ⦃k : Kont⦄
      ⦃e : Exp⦄ ⦃ρ : Lam.Env⦄ ⦃ρ' : List Val⦄ ⦃J' : List JClo⦄ ⦃ks : List Kind⦄
      ⦃SK : Lam.Val → Nat → Result Lam.Val⦄ ⦃v : Lam.Val⦄ ⦃w : Val⦄,
    caseBody S.A fuel cx o alts dflt k = .ok e → EnvR S.A S.G ks cx.vars ρ ρ' → ρ'.length = cx.d →
    J'.length = cx.dj → S.KontR n cx.dj k SK ρ' J' → o.val ρ' = some w → S.V v w →
    S.AltsOk ks alts → S.DfltOk ks dflt →
    SimUpTo S.V n (fun k => (S.caseSrc k ρ v alts dflt).bind (SK · k)) (fun k => eval S.Q k ρ' J' e)
  convAlts : ∀ ⦃cx : Cx⦄ ⦃alts : List Lam.Alt⦄ ⦃k : Kont⦄ ⦃alts' : List Alt⦄ ⦃ρ : Lam.Env⦄
      ⦃ρ' : List Val⦄ ⦃J' : List JClo⦄ ⦃ks : List Kind⦄ ⦃SK : Lam.Val → Nat → Result Lam.Val⦄,
    convAlts S.A fuel cx alts k = .ok alts' → EnvR S.A S.G ks cx.vars ρ ρ' → ρ'.length = cx.d →
    J'.length = cx.dj → S.KontR n cx.dj k SK ρ' J' → S.AltsOk ks alts →
    ∀ ⦃c : Key.CtorKey⦄ ⦃fs : List Lam.Val⦄ ⦃fs' : List Val⦄ ⦃dflt : Option Lam.Term⦄
      ⦃dflt' : Option Exp⦄, VRs S.A S.G fs fs' → S.DfltSim n ρ ρ' J' SK dflt dflt' →
    SimUpTo S.V n (fun k => (Lam.evalAlts S.L k ρ c fs alts dflt).bind (SK · k))
      (fun k => evalAlts S.Q k ρ' J' c fs' alts' dflt')
  convList : ∀ ⦃cx : Cx⦄ ⦃ts : List Lam.Term⦄ ⦃f : Nat → Nat → List Opd → M Exp⦄ ⦃e : Exp⦄
      ⦃ρ : Lam.Env⦄ ⦃ρ' : List Val⦄ ⦃J' : List JClo⦄ ⦃ks : List Kind⦄
      ⦃SKL : List Lam.Val → Nat → Result Lam.Val⦄,
    convList S.A fuel cx ts f = .ok e → EnvR S.A S.G ks cx.vars ρ ρ' → ρ'.length = cx.d →
    J'.length = cx.dj → S.KFunR n ρ' J' S.OpdsR f SKL → (∀ t ∈ ts, TermOk S.G ks t) →
    SimUpTo S.V n (fun k => (Lam.evalList S.L k ρ ts).bind (SKL · k)) (fun k => eval S.Q k ρ' J' e)
  convArgs : ∀ ⦃cx : Cx⦄ ⦃args : List (Lam.Term × Mode)⦄ ⦃f : Nat → Nat → List Opd → M Exp⦄
      ⦃e : Exp⦄ ⦃ρ : Lam.Env⦄ ⦃ρ' : List Val⦄ ⦃J' : List JClo⦄ ⦃ks : List Kind⦄
      ⦃tele : List Mode⦄ ⦃sigs : List (List Mode)⦄ ⦃i : Nat⦄
      ⦃SKS : List Lam.Slot → Nat → Result Lam.Val⦄,
    convArgs S.A fuel cx args f = .ok e → EnvR S.A S.G ks cx.vars ρ ρ' → ρ'.length = cx.d →
    J'.length = cx.dj →
    S.KFunR n ρ' J' (fun ss os ρ => S.SlotsMatch tele sigs i ss os ρ ∧ ss.length = args.length) f SKS →
    ArgsOk S.G ks tele sigs i args →
    SimUpTo S.V n (fun k => lamArgs S.L k ρ args SKS) (fun k => eval S.Q k ρ' J' e)
  groups : ∀ ⦃cx : Cx⦄ ⦃fo : Opd⦄ ⦃args : List (Lam.Term × Mode)⦄ ⦃k : Kont⦄ ⦃e : Exp⦄
      ⦃ρ : Lam.Env⦄ ⦃ρ' : List Val⦄ ⦃J' : List JClo⦄ ⦃ks : List Kind⦄
      ⦃SK : Lam.Val → Nat → Result Lam.Val⦄ ⦃tele : List Mode⦄ ⦃sigs : List (List Mode)⦄
      ⦃i : Nat⦄ ⦃fv : Lam.Val⦄ ⦃w : Val⦄,
    groups S.A fuel cx fo args k = .ok e → EnvR S.A S.G ks cx.vars ρ ρ' → ρ'.length = cx.d →
    J'.length = cx.dj → S.KontR n cx.dj k SK ρ' J' → fo.val ρ' = some w →
    S.GroupHead tele sigs i fv w → ArgsOk S.G ks tele sigs i args →
    (∀ p, tele.getD p .strict = .name → p < i + args.length) →
    SimUpTo S.V n (fun k => (applyArgs S.L k ρ fv args).bind (SK · k)) (fun k => eval S.Q k ρ' J' e)
  spine : ∀ ⦃cx : Cx⦄ ⦃f a : Lam.Term⦄ ⦃m : Mode⦄ ⦃k : Kont⦄ ⦃e : Exp⦄ ⦃ρ : Lam.Env⦄
      ⦃ρ' : List Val⦄ ⦃J' : List JClo⦄ ⦃ks : List Kind⦄ ⦃SK : Lam.Val → Nat → Result Lam.Val⦄,
    spine S.A fuel cx (.app f a m) k = .ok e → EnvR S.A S.G ks cx.vars ρ ρ' → ρ'.length = cx.d →
    J'.length = cx.dj → S.KontR n cx.dj k SK ρ' J' → TermOk S.G ks (.app f a m) →
    SimUpTo S.V n (fun k => (Lam.eval S.L k ρ (.app f a m)).bind (SK · k))
      (fun k => eval S.Q k ρ' J' e)

variable {S}

/-! ## Operands -/

theorem opds_eval {ρ : List Val} : ∀ {os : List Opd} {ws : List Val}, os.mapM (·.val ρ) = some ws →
    evalAtoms ρ (os.map (·.atom ρ.length)) = some ws
  | [], ws, h => by simp at h; subst h; rfl
  | o :: os, ws, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws, rfl⟩ := h
    simp only [List.map_cons, evalAtoms_cons, Opd.val_atom hw, opds_eval hws, Option.bind_some,
      Option.map_some]

theorem opds_suffix {ρ ρ₂ : List Val} (hs : ρ <:+ ρ₂) : ∀ {os : List Opd} {ws : List Val},
    os.mapM (·.val ρ) = some ws → os.mapM (·.val ρ₂) = some ws
  | [], ws, h => h
  | o :: os, ws, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨w, hw, ws', hws, rfl⟩ := h
    exact ⟨w, Opd.val_suffix hs hw, ws', opds_suffix hs hws, rfl⟩

theorem OpdR.suffix {x : Lam.Val} {o : Opd} {ρ ρ₂ : List Val} (h : S.OpdR x o ρ) (hs : ρ <:+ ρ₂) :
    S.OpdR x o ρ₂ := by
  obtain ⟨w, hw, hx⟩ := h
  exact ⟨w, Opd.val_suffix hs hw, hx⟩

/-! ## Argument slots -/

theorem ArgsE.length {e : Nat → Kind} : ∀ {i : Nat} {ss : List Lam.Slot} {ws : List Val},
    S.ArgsE e i ss ws → ws.length = ss.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => by simp [h.length]

/-- Expected kinds fitting binder kinds: the slots fit the binders. -/
theorem ArgsE.argsR {tele : List Mode} {sigs : List (List Mode)} {tk : List Kind}
    (hc : Compat tele sigs tk) : ∀ {i : Nat} {ss : List Lam.Slot} {ws : List Val},
    S.ArgsE (expKind tele sigs) i ss ws → ArgsR S.A S.G tk i ss ws
  | _, _, _, .nil => .nil
  | i, _, _, .cons hs h => .cons (hs.kindOk (hc i)) (h.argsR hc)

theorem expKind_strict {tele : List Mode} {sigs : List (List Mode)} {p : Nat}
    (h : tele.getD p .strict = .strict) : expKind tele sigs p = .strict := by
  unfold expKind; rw [if_neg (by rw [h]; decide)]

/-- Strict expected positions: slots for a plain head. -/
theorem ArgsE.strict {tele : List Mode} {sigs : List (List Mode)} :
    ∀ {i : Nat} {ss : List Lam.Slot} {ws : List Val}, (∀ p, i ≤ p → tele.getD p .strict = .strict) →
    S.ArgsE (expKind tele sigs) i ss ws → ∀ j, ArgsR S.A S.G [] j ss ws
  | _, _, _, _, .nil, _ => .nil
  | i, _, _, hst, .cons hs h, j => by
    refine .cons ?_ (ArgsE.strict (fun p hp => hst p (by omega)) h (j + 1))
    rw [getD_nil_strict]
    rw [expKind_strict (hst i (Nat.le_refl i))] at hs
    exact hs

theorem ArgsE.append {e : Nat → Kind} : ∀ {i : Nat} {ss : List Lam.Slot} {ws : List Val},
    S.ArgsE e i ss ws → ∀ {ss' : List Lam.Slot} {ws' : List Val},
    S.ArgsE e (i + ss.length) ss' ws' → S.ArgsE e i (ss ++ ss') (ws ++ ws')
  | i, _, _, .nil, _, _, h' => by simpa using h'
  | i, _ :: ss, _, .cons hs h, _, _, h' =>
    .cons hs (h.append (by rwa [show i + 1 + ss.length = i + (ss.length + 1) by omega]))

/-- A spine's arguments split: `ArgsOk` for a prefix and the rest. -/
theorem argsOk_append {ks : List Kind} {tele : List Mode} {sigs : List (List Mode)} :
    ∀ {i : Nat} (xs ys : List (Lam.Term × Mode)), ArgsOk S.G ks tele sigs i (xs ++ ys) →
      ArgsOk S.G ks tele sigs i xs ∧ ArgsOk S.G ks tele sigs (i + xs.length) ys
  | _, [], ys, h => ⟨.nil, by simpa using h⟩
  | i, x :: xs, ys, h => by
    cases h with
    | strict he ht hr =>
      obtain ⟨h1, h2⟩ := argsOk_append xs ys hr
      exact ⟨.strict he ht h1, by rwa [show i + 1 + xs.length = i + (xs.length + 1) by omega] at h2⟩
    | name he hn hr =>
      obtain ⟨h1, h2⟩ := argsOk_append xs ys hr
      exact ⟨.name he hn h1, by rwa [show i + 1 + xs.length = i + (xs.length + 1) by omega] at h2⟩

/-! ## Primitives and projections -/

theorem natArgs_rel : ∀ {vs : List Lam.Val} {ws : List Val}, VRs S.A S.G vs ws →
    Anf.natArgs ws = Lam.natArgs vs
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hv h => by
    cases hv with
    | lit =>
      rename_i l
      cases l with
      | nat n => simp [Anf.natArgs, Lam.natArgs, natArgs_rel h]
      | str s => simp [Anf.natArgs, Lam.natArgs]
    | box => simp [Anf.natArgs, Lam.natArgs]
    | con _ => simp [Anf.natArgs, Lam.natArgs]
    | clo hc _ =>
      cases hc with
      | mk _ _ _ _ _ _ _ _ hv hw => subst hv hw; simp [Anf.natArgs, Lam.natArgs]

theorem prim_sim {n : Nat} {K : Lam.Known} (p : Lam.Prim) {vs : List Lam.Val} {ws : List Val}
    (h : VRs S.A S.G vs ws) :
    SimUpTo S.V n (fun _ => Lam.primResult K p vs) (fun _ => Anf.primResult K p ws) := by
  unfold Lam.primResult Anf.primResult
  rw [natArgs_rel h]
  cases Lam.natArgs vs with
  | none => exact SimUpTo.stuck _
  | some ns =>
    simp only
    cases p.sem ns with
    | none => exact SimUpTo.stuck _
    | some r =>
      cases r with
      | nat m => exact SimUpTo.ok .lit
      | bool b =>
        simp only
        cases (if b then K.boolTrue else K.boolFalse) with
        | none => exact SimUpTo.stuck _
        | some c => exact SimUpTo.ok (.con .nil)

theorem _root_.Compilatrix.Anf.Convert.Proof.VRs.get : ∀ {vs : List Lam.Val} {ws : List Val},
    VRs S.A S.G vs ws → ∀ (i : Nat),
    (vs[i]? = none ∧ ws[i]? = none) ∨ ∃ v w, vs[i]? = some v ∧ ws[i]? = some w ∧ S.V v w
  | [], [], .nil, _ => .inl ⟨rfl, rfl⟩
  | _ :: _, _ :: _, .cons hv _, 0 => .inr ⟨_, _, rfl, rfl, hv⟩
  | _ :: _, _ :: _, .cons _ h, i + 1 => by simpa using h.get i

theorem _root_.Compilatrix.Anf.Convert.Proof.VRs.length : ∀ {vs : List Lam.Val} {ws : List Val}, VRs S.A S.G vs ws →
    ws.length = vs.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [h.length]

theorem _root_.Compilatrix.Anf.Convert.Proof.VRs.slots : ∀ {vs : List Lam.Val} {ws : List Val},
    VRs S.A S.G vs ws → SlotsR S.A S.G (List.replicate vs.length .strict) (vs.map .val) ws
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hv h => .cons (.val hv) h.slots

theorem _root_.Compilatrix.Anf.Convert.Proof.VRs.reverse_append {vs : List Lam.Val} {ws : List Val} (h : VRs S.A S.G vs ws)
    {ks : List Kind} {vars : List VarInfo} {ρ : Lam.Env} {ρt : List Val}
    (henv : EnvR S.A S.G ks vars ρ ρt) :
    EnvR S.A S.G (List.replicate vs.length .strict ++ ks)
      (pushParams vars ρt.length (List.replicate vs.length false))
      (vs.reverse.map .val ++ ρ) (ws.reverse ++ ρt) := by
  have := henv.push h.slots (by simp)
  simpa [List.map_reverse, List.map_replicate, Kind.isName] using this

/-- The projection on the Lam side. -/
def projL (c : Key.CtorKey) (i : Nat) : Lam.Val → Result Lam.Val
  | .con c' fs => if c' = c then Result.ofOption fs[i]? else .stuck
  | _ => .stuck

theorem proj_sim {n : Nat} (c : Key.CtorKey) (i : Nat) {v : Lam.Val} {w : Val} (h : S.V v w) :
    SimUpTo S.V n (fun _ => projL c i v) (fun _ => projVal c i w) := by
  cases h with
  | con hfs =>
    simp only [projL, projVal]
    split
    · rcases hfs.get i with ⟨h1, h2⟩ | ⟨v', w', h1, h2, hvw⟩
      · rw [h1]; exact SimUpTo.stuck _
      · rw [h1, h2]; exact SimUpTo.ok hvw
    · exact SimUpTo.stuck _
  | lit => exact SimUpTo.stuck _
  | box => exact SimUpTo.stuck _
  | clo hc _ =>
    cases hc with
    | mk _ _ _ _ _ _ _ _ hv hw => subst hv hw; exact SimUpTo.stuck _

/-! ## Constructor views -/

theorem asCtor_rel {K : Lam.Known} {v : Lam.Val} {w : Val} (h : S.V v w) :
    (v.asCtor K = none ∧ w.asCtor K = none) ∨
      ∃ c fs fs', v.asCtor K = some (c, fs) ∧ w.asCtor K = some (c, fs') ∧ VRs S.A S.G fs fs' := by
  cases h with
  | lit =>
    rename_i l
    cases l with
    | nat m =>
      cases m with
      | zero =>
        cases hz : K.natZero with
        | none => exact .inl ⟨by simp [Lam.Val.asCtor, hz], by simp [Val.asCtor, hz]⟩
        | some z => exact .inr ⟨z, [], [], by simp [Lam.Val.asCtor, hz], by simp [Val.asCtor, hz], .nil⟩
      | succ m =>
        cases hs : K.natSucc with
        | none => exact .inl ⟨by simp [Lam.Val.asCtor, hs], by simp [Val.asCtor, hs]⟩
        | some s =>
          exact .inr ⟨s, [.lit (.nat m)], [.lit (.nat m)], by simp [Lam.Val.asCtor, hs],
            by simp [Val.asCtor, hs], .cons .lit .nil⟩
    | str _ => exact .inl ⟨rfl, rfl⟩
  | box => exact .inl ⟨rfl, rfl⟩
  | con hfs => exact .inr ⟨_, _, _, rfl, rfl, hfs⟩
  | clo hc _ =>
    cases hc with
    | mk _ _ _ _ _ _ _ _ hv hw => subst hv hw; exact .inl ⟨rfl, rfl⟩

/-! ## λ-telescopes in plain positions -/

theorem termOk_lams {ks : List Kind} : ∀ (ps : List (Mode × V3.BinderContract)) {body : Lam.Term},
    TermOk S.G ks (lamsWith ps body) →
      (∀ p ∈ ps, p.1 = .strict) ∧ TermOk S.G (List.replicate ps.length .strict ++ ks) body
  | [], _, h => ⟨by simp, by simpa [lamsWith] using h⟩
  | (m, c) :: ps, body, h => by
    cases h with
    | lam hm hb =>
      obtain ⟨h1, h2⟩ := termOk_lams (ks := .strict :: ks) ps hb
      refine ⟨fun p hp => ?_, ?_⟩
      · rcases List.mem_cons.1 hp with rfl | hp
        · exact hm
        · exact h1 p hp
      · simpa [List.replicate_succ', List.append_assoc] using h2

theorem modesAgree_strict {ps : List (Mode × V3.BinderContract)} (h : ∀ p ∈ ps, p.1 = .strict) :
    ModesAgree ps (List.replicate ps.length .strict) := by
  refine ⟨by simp, fun i p q hp hq => ?_⟩
  have hpm : p.1 = .strict := h p (List.mem_of_getElem? hp)
  rw [List.getElem?_replicate] at hq
  split at hq
  · cases hq; simp [hpm, Kind.isName]
  · cases hq

/-! ## Heads -/

theorem GroupHead.vr {tele : List Mode} {sigs : List (List Mode)} {i : Nat} {v : Lam.Val} {w : Val}
    (h : S.GroupHead tele sigs i v w) (hcov : ∀ p, tele.getD p .strict = .name → p < i) :
    S.V v w := by
  rcases h with ⟨h, _⟩ | ⟨tk, hc, hcomp⟩
  · exact h
  · refine .clo hc fun q hq => ?_
    obtain ⟨p', hp'⟩ := List.mem_iff_getElem?.1 hq
    rw [List.getElem?_drop] at hp'
    have hk := hcomp (i + p')
    have hstrict : tele.getD (i + p') .strict = .strict := by
      cases ht : tele.getD (i + p') .strict with
      | strict => rfl
      | name => have := hcov _ ht; omega
    rw [expKind_strict hstrict, List.getD_eq_getElem?_getD, hp'] at hk
    rcases hk with hk | ⟨_, _, hk, _⟩
    · exact hk.symm
    · cases hk

/-- After a group: the next head. -/
theorem GroupHead.of_res {tele : List Mode} {sigs : List (List Mode)} {tk : List Kind} {i : Nat}
    {v : Lam.Val} {w : Val} (hcomp : Compat tele sigs tk) (h : Res S.A S.G tk i v w) :
    S.GroupHead tele sigs i v w := by
  unfold Res at h
  split at h
  · exact .inr ⟨tk, h, hcomp⟩
  · refine .inl ⟨h, fun p hp => ?_⟩
    have hk := hcomp p
    rw [getD_beyond (by omega)] at hk
    unfold expKind at hk
    split at hk
    · rcases hk with hk | ⟨_, _, _, hk, _⟩ <;> cases hk
    · next hne =>
      cases ht : tele.getD p .strict with
      | strict => rfl
      | name => exact absurd ht hne

end Setting

end Compilatrix.Anf.Convert.Proof
