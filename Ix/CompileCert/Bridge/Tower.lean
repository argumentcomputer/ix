import Ix.CompileCert.Bridge.Pair

/-!
# M7 X2: the model's tower law on the public reading, and the pair law discharged

IxC's strong model carries, for every stored projection-table entry, the tower projection law
(`TowerOk`, the `tower_ok` field of `EnvModelM`; clause (B) of `TowerEntryLaw`,
`IxC/Kernel/Model/Annot/Laws.lean`): on the internal annotated reading, a graded constructor
application that fits the constructor's type reading has its `i`-th field at position `i + off`
of its pair chain. This module transports it to the public reading (`tower_field`): for any
values typed against the constructor's installed telescope (`InstalledTelescope`), the field of
the constructor's value applied to them is the corresponding argument. The internal premises are
built from the public typing exactly as the lane builds them for recursor rules
(`StrongInstalledModel.arbitrary_installed_fit`, `AnnotatedApplication.applied_argument`), with
IxC's `teleFit_of_teleFitPA` for the value-level fit; the telescope's ∀-chain shape gives the
reading's Π-chain (`piChain_of_reading`).

Then the public projection of a constructor application reads its argument
(`denotes_proj_ctor`), and **the pair law holds in every strong model** for a structure whose
projection entries `0` and `1` name the constructor with two parameters, under the tower guard
(`pairLaw_of_tower`): X1's projection rules are sound with no hypothesis about the model.
-/

namespace Ix.CompileCert.Bridge

open Kernel (Denotes push)
open Kernel.SetTheory Kernel.SetModel
open Kernel.Semantics Kernel.Model Kernel.SetTheory.Tower

universe u

section Tower

variable {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env}

theorem field_eq_projS : ∀ (i : Nat) (p : V), Kernel.field i p = projS i p
  | 0, _ => rfl
  | i + 1, p => field_eq_projS i (ssnd p)

/-- A ∀-chain of `n` binders, syntactically. -/
def FChain : Nat → Kernel.Expr → Prop
  | 0, _ => True
  | n + 1, .forallE _ b _ => FChain n b
  | _ + 1, _ => False

theorem FChain.instantiate1 : ∀ (n : Nat) (e v : Kernel.Expr) (d : Nat),
    FChain n e → FChain n (e.instantiate1 v d)
  | 0, _, _, _, _ => trivial
  | n + 1, .forallE t b m, v, d, h => by
    simp only [Kernel.Expr.instantiate1, FChain] at h ⊢
    exact FChain.instantiate1 n b v (d + 1) h
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h => h.elim

/-- A typed tuple's type is a ∀-chain of the tuple's length. -/
theorem fchain_of_telescope {cval : Kernel.Name → (Kernel.Name → Nat) → V}
    {φ : Kernel.Name → Nat} {ρ finalρ : Nat → V} {e result : Kernel.Expr} {args : List V}
    (h : InstalledTelescope cval env φ ρ e args finalρ result) : FChain args.length e := by
  induction h with
  | nil => trivial
  | cons _ _ _ ih => exact ih

/-- The reading of a ∀-chain is a Π-chain. -/
theorem piChain_of_reading {acval : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm}
    {φ : Kernel.Name → Nat} : ∀ (n : Nat) {d : Nat} {e : Kernel.Expr} {ta : AnnotTerm},
    FChain n e → denoteMeta acval env φ d e = some ta → Kernel.Model.Rules.PiChain n ta
  | 0, _, _, _, _, _ => trivial
  | n + 1, d, .forallE t b m, ta, h, hr => by
    obtain ⟨ta', ba, -, hb, rfl⟩ := denoteMeta_forallE_inv hr
    exact piChain_of_reading n (FChain.instantiate1 n b _ 0 h) hb
  | _ + 1, _, .bvar _, _, h, _ | _ + 1, _, .fvar _ _, _, h, _ | _ + 1, _, .sort _, _, h, _
  | _ + 1, _, .const _ _, _, h, _ | _ + 1, _, .app _ _, _, h, _ | _ + 1, _, .lam _ _ _, _, h, _
  | _ + 1, _, .letE _ _ _, _, h, _ | _ + 1, _, .lit _, _, h, _ | _ + 1, _, .proj _ _ _, _, h, _ =>
    h.elim

/-- **The tower law on the public reading**: for values typed against an installed structure
constructor's telescope, the field at the entry's position of the constructor's value applied to
them is the corresponding argument. -/
theorem tower_field (strong : StrongInstalledModel V env) (φ : Kernel.Name → Nat)
    {s : Kernel.Name} {i : Nat} {entry : Kernel.ProjEntry} (ht : env.findProj? s i = some entry)
    {us : List Kernel.Level} (guard : TowerGuardAt φ entry us)
    {cv : Kernel.ConstantVal} {nP nF : Nat} (hc : env.find? entry.ctor = some (.ctorInfo cv nP nF))
    (arity' : us.length = cv.levelParams.length)
    {ρ finalρ : Nat → V} {argsV : List V} {result : Kernel.Expr}
    (hlen : argsV.length = entry.numParams + entry.numFields)
    (typed : InstalledTelescope strong.public.cval env φ ρ
      (cv.type.instantiateLevelParams cv.levelParams us) argsV finalρ result) :
    ∃ hk : entry.numParams + i < argsV.length,
      Kernel.field (i + entry.off)
        (argsV.foldl app (strong.public.cval entry.ctor (Kernel.Level.substFn φ cv.levelParams us))) =
        argsV[entry.numParams + i] := by
  have law := strong.internal.tower_ok φ s i entry ht
  obtain ⟨-, -, hi, -, -, cvC, hcC, hlps, hUs, -⟩ := law
  rw [hc] at hcC
  obtain ⟨rfl, rfl, rfl⟩ : cv = cvC ∧ nP = entry.numParams ∧ nF = entry.numFields := by
    simp only [Option.some.injEq, Kernel.ConstantInfo.ctorInfo.injEq] at hcC
    exact ⟨hcC.1, hcC.2.1, hcC.2.2⟩
  have hk : entry.numParams + i < argsV.length := by omega
  refine ⟨hk, ?_⟩
  have arity : us.length = entry.levelParams.length := by rw [← hlps]; exact arity'
  obtain ⟨TCa, hTCa, hB⟩ := (hUs us arity).2
  -- the internal premises, from the public typing
  obtain ⟨residual, typeAnnotation, residualAnnotation, application, typeRead, fitPA, -, -, -⟩ :=
    strong.arbitrary_installed_fit φ entry.ctor (.ctorInfo cv entry.numParams entry.numFields) hc rfl
      us arity' typed (fun _ => .sort .zero) (fun _ _ => by simp [Kernel.Expr.WScoped])
  have typeRead' : denoteMeta strong.internal.base2.acval env φ 0
      (cv.type.instantiateLevelParams cv.levelParams us) = some typeAnnotation := typeRead
  have hT : TCa = typeAnnotation := by
    rw [hTCa] at typeRead'; exact Option.some.inj typeRead'
  subst hT
  have graded : WellDenotedV V (pushArguments ρ argsV)
      (AnnotTerm.mkAppN (strong.internal.base2.acval entry.ctor
        (Kernel.Level.substFn φ cv.levelParams us)) (argumentReadings argsV.length)) :=
    (application.applied_argument entry.ctor (.ctorInfo cv entry.numParams entry.numFields)
      hc rfl us arity').graded
  have chain : Kernel.Model.Rules.PiChain (argumentReadings argsV.length).length TCa := by
    have := piChain_of_reading (acval := strong.internal.base2.acval) argsV.length (fchain_of_telescope typed) hTCa
    simpa [argumentReadings] using this
  have fit := Kernel.Model.Rules.teleFit_of_teleFitPA chain fitPA
  have hlen' : (argumentReadings argsV.length).length = entry.numParams + entry.numFields := by
    simp [argumentReadings, hlen]
  rw [hlps] at graded
  have key := hB guard (pushArguments ρ argsV) (argumentReadings argsV.length) _ hlen' graded fit
  rw [projAV_interp, interp_mkAppN_map, argumentReadings_values,
    interp_cvalOf strong.internal.base2.cval_closedL] at key
  rw [field_eq_projS, hlps]
  have hget : interp V (pushArguments ρ argsV)
      ((argumentReadings argsV.length).getD (entry.numParams + i) default) = argsV[entry.numParams + i] := by
    have hm := argumentReadings_values ρ argsV
    have hlt : entry.numParams + i < (argumentReadings argsV.length).length := by
      simp [argumentReadings]; exact hk
    simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    have := congrArg (fun l : List V => l[entry.numParams + i]?) hm
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hk,
      Option.map_some, Option.some.injEq] at this
    exact this
  rw [hget] at key
  exact key

/-- Each expression reads to its value. -/
inductive Reads (cval : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) : List Kernel.Expr → List V → Prop
  | nil : Reads cval env φ ρ [] []
  | cons {a : Kernel.Expr} {x : V} {as : List Kernel.Expr} {xs : List V} :
      Denotes cval env φ ρ a x → Reads cval env φ ρ as xs → Reads cval env φ ρ (a :: as) (x :: xs)

theorem Reads.mkAppN {cval : Kernel.Name → (Kernel.Name → Nat) → V} {φ : Kernel.Name → Nat}
    {ρ : Nat → V} : ∀ {args : List Kernel.Expr} {argsV : List V}, Reads cval env φ ρ args argsV →
    ∀ {f : Kernel.Expr} {F : V}, Denotes cval env φ ρ f F →
      Denotes cval env φ ρ (Kernel.Expr.mkAppN f args) (argsV.foldl app F)
  | [], [], .nil, _, _, hf => hf
  | _ :: _, _ :: _, .cons ha hs, _, _, hf => by
    simp only [Kernel.Expr.mkAppN, List.foldl_cons]
    exact Reads.mkAppN hs (.app hf ha)

/-- **The public projection of a constructor application reads its argument.** -/
theorem denotes_proj_ctor (strong : StrongInstalledModel V env) (φ : Kernel.Name → Nat)
    {s : Kernel.Name} {i : Nat} {entry : Kernel.ProjEntry} (ht : env.findProj? s i = some entry)
    {us : List Kernel.Level} (guard : TowerGuardAt φ entry us)
    {cv : Kernel.ConstantVal} {nP nF : Nat} (hc : env.find? entry.ctor = some (.ctorInfo cv nP nF))
    (harity : us.length = cv.levelParams.length)
    {ρ finalρ : Nat → V} {args : List Kernel.Expr} {argsV : List V} {result : Kernel.Expr}
    (hargs : Reads strong.public.cval env φ ρ args argsV)
    (hlen : argsV.length = entry.numParams + entry.numFields)
    (typed : InstalledTelescope strong.public.cval env φ ρ
      (cv.type.instantiateLevelParams cv.levelParams us) argsV finalρ result) :
    ∃ hk : entry.numParams + i < argsV.length,
      (∃ v, Denotes strong.public.cval env φ ρ (.proj s i (Kernel.Expr.mkAppN (.const entry.ctor us) args)) v) ∧
      ∀ v, Denotes strong.public.cval env φ ρ (.proj s i (Kernel.Expr.mkAppN (.const entry.ctor us) args)) v →
        v = argsV[entry.numParams + i] := by
  obtain ⟨hk, hf⟩ := tower_field strong φ ht guard hc harity hlen typed
  have happ : Denotes strong.public.cval env φ ρ (Kernel.Expr.mkAppN (.const entry.ctor us) args)
      (argsV.foldl app (strong.public.cval entry.ctor (Kernel.Level.substFn φ cv.levelParams us))) :=
    hargs.mkAppN (.const hc harity)
  refine ⟨hk, ⟨_, .proj_table ht happ⟩, fun v hv => ?_⟩
  cases hv with
  | proj_table ht' hd =>
    rw [ht] at ht'; cases ht'
    rw [Kernel.Denotes_functional hd happ]; exact hf
  | proj_fst ht' _ => rw [ht] at ht'; cases ht'
  | proj_snd ht' _ => rw [ht] at ht'; cases ht'

/-- **The pair law holds in every strong model** for a structure whose projection entries `0` and
`1` name the constructor with two parameters and two fields (`PProd`/`PProd.mk`,
`And`/`And.intro`), under the tower guard. -/
theorem pairLaw_of_tower (strong : StrongInstalledModel V env) (φ : Kernel.Name → Nat)
    {s c : Kernel.Name} {e0 e1 : Kernel.ProjEntry}
    (h0 : env.findProj? s 0 = some e0) (h1 : env.findProj? s 1 = some e1)
    (hc0 : e0.ctor = c) (hc1 : e1.ctor = c)
    (hp0 : e0.numParams = 2) (hp1 : e1.numParams = 2) (hf0 : e0.numFields = 2) (hf1 : e1.numFields = 2)
    (guard : ∀ us, TowerGuardAt φ e0 us ∧ TowerGuardAt φ e1 us) :
    PairLaw strong.public.cval env φ s c := by
  intro ρ us α β a b A B X Y cv nP nF finalρ result hc harity hα hβ ha hb typed
  have hargs : Reads strong.public.cval env φ ρ [α, β, a, b] [A, B, X, Y] :=
    .cons hα (.cons hβ (.cons ha (.cons hb .nil)))
  subst hc0
  have hc1' : env.find? e1.ctor = some (.ctorInfo cv nP nF) := by rw [hc1]; exact hc
  obtain ⟨hk0, ⟨v0, hv0⟩, hu0⟩ := denotes_proj_ctor strong φ h0 (guard us).1 hc harity hargs
    (by simp [hp0, hf0]) typed
  obtain ⟨hk1, ⟨v1, hv1⟩, hu1⟩ := denotes_proj_ctor strong φ h1 (guard us).2 hc1' harity hargs
    (by simp [hp1, hf1]) typed
  rw [hc1] at hv1 hu1
  refine ⟨⟨v0, hv0⟩, fun v hv => ?_, ⟨v1, hv1⟩, fun v hv => ?_⟩
  · rw [hu0 v hv]; simp [hp0]
  · rw [hu1 v hv]; simp [hp1]

/-- The tower guard from the checker's own fire guard (`ProjEntry.fireOk`, decidable on the stored
entry) and the law's O5 conjunct. -/
theorem towerGuard_of_fireOk (strong : StrongInstalledModel V env) (φ : Kernel.Name → Nat)
    {s : Kernel.Name} {i : Nat} {entry : Kernel.ProjEntry} (ht : env.findProj? s i = some entry)
    {us : List Kernel.Level} (hfire : entry.fireOk us = true) : TowerGuardAt φ entry us :=
  towerGuardAt_of_fireOk (strong.internal.tower_ok φ s i entry ht).2.2.2.2.1 hfire

/-- **The pair law in every strong model**, under the checker's fire guard of the two entries. -/
theorem pairLaw_of_fireOk (strong : StrongInstalledModel V env) (φ : Kernel.Name → Nat)
    {s c : Kernel.Name} {e0 e1 : Kernel.ProjEntry}
    (h0 : env.findProj? s 0 = some e0) (h1 : env.findProj? s 1 = some e1)
    (hc0 : e0.ctor = c) (hc1 : e1.ctor = c)
    (hp0 : e0.numParams = 2) (hp1 : e1.numParams = 2) (hf0 : e0.numFields = 2) (hf1 : e1.numFields = 2)
    (hfire : ∀ us, e0.fireOk us = true ∧ e1.fireOk us = true) :
    PairLaw strong.public.cval env φ s c :=
  pairLaw_of_tower strong φ h0 h1 hc0 hc1 hp0 hp1 hf0 hf1 fun us =>
    ⟨towerGuard_of_fireOk strong φ h0 (hfire us).1, towerGuard_of_fireOk strong φ h1 (hfire us).2⟩

end Tower

end Ix.CompileCert.Bridge
