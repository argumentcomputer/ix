module

public import IxCK.Kernel.Model.Inductives.FixStageRec
public import IxCK.Kernel.Model.Inductives.FixCtorCross
public import IxCK.Kernel.Model.Inductives.FixData
public import IxCK.Kernel.Model.Inductives.StructData
public import IxCK.Kernel.Model.ThmVal
public import IxCK.Kernel.Semantics.Tower.TowerIntro
public import IxCK.Kernel.Semantics.Inductives.DeclNativeRecLateJ
import IxCK.Kernel.Verify.Inductives.FixRec
public section

/-!
# A stored native family's data, along model extensions

The recursor's stage of the native route (`stageFixRecJ`) is stated at any environment
that stores the family: it reads the former's and the constructors' data, the two leaf
equations and the frames. This module bundles those hypotheses for a family that is
already stored (`NativeFamAt`, `NativeFamOk` over the family's summary `NativeFam`)
and carries the bundle along a model extension (`NativeFamOk.ext`), so that the
recursor's stage applies at every later environment.

* The readings in the bundle are readings of the telescope constant's type, of the
  constructors' types and of sub-expressions of their openings. A later fresh cons
  changes a reading only at a projection table's head, and only for a `.proj` node at
  that table's structure. The bundle records that those types have no such node at any
  structure whose table is not stored (`NoProjFresh`), which the constant check gives
  (`noProjFresh_of_check`) and which every extension keeps.
* The constructors' data cross a cons under that condition on the constructor's type
  alone (`FixCtorDataI.crossAt`): the opened variables' types and the index
  expressions are sub-expressions of it. `FixCtorDataI.transfer` is the general form,
  over any reading transfer closed under opening and argument selection; the step that
  re-attaches rule lists (`ModelExt.swap`) is its instance where every reading is kept.
* The bundle holds the constructors' data at the small eliminator (`large := false`),
  so it does not depend on a recursor record. `FixCtorDataI.withSrcs` replaces the
  field sources and the flag when a recursor's own evidence is available; a family
  that is not syntactically propositional needs none, since its fields are bounded by
  its sort (`fieldsBound`).
* The bundle keeps names, not lookups: a model extension is not known to keep a stored
  record (`ModelExt.swap` keeps only which names are stored), so the stage's lookups
  are read at the environment where it is applied.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory Ix.Kernel.SetTheory.Tower
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  NativeParts RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Projection nodes through openings -/

/-- An opening's variables and residual have no node at a slot the opened term has
none at. -/
theorem noProjAt_openPisAtFvars {T : Key md} {i : Nat} :
    ∀ (n : Nat) {e : Expr md} {d : Nat} {fvs : List (Expr md)} {o : Expr md},
      Expr.NoProjAt T i e → openPisAtFvars n e d = some (fvs, o) →
      (∀ x ∈ fvs, Expr.NoProjAt T i x) ∧ Expr.NoProjAt T i o
  | 0, e, d, fvs, o, he, hop => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun x hx => nomatch hx), he⟩
  | n + 1, e, d, fvs, o, he, hop => by
    match e, he, hop with
    | .forallE dom bd mb, he, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        rw [Ix.Kernel.Expr.noProjAt_forallE] at he
        have hfv : Expr.NoProjAt T i (Expr.fvar d dom) := by
          rw [Ix.Kernel.Expr.noProjAt_fvar]; exact he.1
        obtain ⟨hfvs, ho⟩ := noProjAt_openPisAtFvars n
          (Ix.Kernel.Expr.NoProjAt.instantiate1 hfv bd 0 he.2) h₁
        refine ⟨fun x hx => ?_, ho⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hfv
        · exact hfvs x hx
      · exact nomatch hop

/-- The crossing condition through an opening. -/
theorem consCrossAt_openPis {c₀ : ConstantInfo md} (n : Nat) {e : Expr md} {d : Nat}
    {fvs : List (Expr md)} {o : Expr md} (h : ConsCrossAt c₀ e)
    (hop : openPisAtFvars n e d = some (fvs, o)) :
    (∀ x ∈ fvs, ConsCrossAt c₀ x) ∧ ConsCrossAt c₀ o :=
  ⟨fun x hx tbl heq i => (noProjAt_openPisAtFvars n (h tbl heq i) hop).1 x hx,
    fun tbl heq i => (noProjAt_openPisAtFvars n (h tbl heq i) hop).2⟩

/-! ## No projection node at a structure without a stored table -/

/-- **No `.proj` node at any structure whose table is not stored.** A fresh table
head is such a structure, so a reading of the term crosses its cons. -/
@[expose] def NoProjFresh (env : Env md) (e : Expr md) : Prop :=
  ∀ T : Key md, env.find? (Ix.Kernel.projTableName T) = none → ∀ i : Nat, Expr.NoProjAt T i e

/-- The condition is kept wherever fewer names are free. -/
theorem NoProjFresh.mono {env env' : Env md} {e : Expr md} (h : NoProjFresh env e)
    (hle : ∀ n : Key md, env'.find? n = none → env.find? n = none) : NoProjFresh env' e :=
  fun T hT i => h T (hle _ hT) i

/-- A term with the condition crosses a fresh head. -/
theorem NoProjFresh.consCross {env : Env md} {e : Expr md} (h : NoProjFresh env e)
    {c₀ : ConstantInfo md} (hfresh : env.find? c₀.name = none) : ConsCrossAt c₀ e := by
  intro tbl heq i
  refine h tbl.structName ?_ i
  rw [heq] at hfresh
  exact hfresh

/-- **A checked constant's type has the condition**, at the environment it was checked
at: its annotation has no node at an empty slot. -/
theorem noProjFresh_of_check {J : Judgements md} (hI : JudgeInv J) {env : Env md}
    {cv cv' : ConstantVal md} (h : ConstantValCheckJ J env cv cv') :
    NoProjFresh env cv'.type := by
  obtain ⟨-, -, -, -, -, hnf, type, stype, -, hann, -, -, hinf, -, rfl⟩ := h.inv
  intro T hT i
  exact hI.annot_noProjAt hann ⟨stype, hinf⟩ hnf (Ix.Kernel.Env.findProj?_none_of_fresh hT i)

/-! ## The constructor's data along a reading transfer -/

/-- A read spine transfers with its terms' readings. -/
theorem DenoteMetaSpine.transfer {acval acval' : Key md → (LevelParam → Nat) → AnnotTerm}
    {env env' : Env md} {ψ : LevelParam → Nat} {d : Nat} {P : Expr md → Prop}
    (hP : ∀ (e : Expr md) (ea : AnnotTerm), P e → denoteMeta acval env ψ d e = some ea →
      denoteMeta acval' env' ψ d e = some ea) :
    ∀ {as : List (Expr md)} {vs : List AnnotTerm}, (∀ a ∈ as, P a) →
      DenoteMetaSpine acval env ψ d as vs → DenoteMetaSpine acval' env' ψ d as vs
  | _, _, _, .nil => .nil
  | a :: _, _, hall, .cons ha htl =>
    .cons (hP _ _ (hall a List.mem_cons_self) ha)
      (DenoteMetaSpine.transfer hP (fun a' ha' => hall a' (List.mem_cons_of_mem _ ha')) htl)

/-- **The sum data along a reading transfer**: the former's leaf is kept, and the
readings of the constructor's type and of the index expressions are carried. -/
theorem CtorDataI.transfer {env env' : Env md} {m : EnvModel V env} {m' : EnvModel V env'}
    {T : Key md} {lps : List LevelParam} {cvC : ConstantVal md}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List (Expr md)}
    {ds : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (LevelParam → Nat) → List AnnotTerm} {srcs : List (Option Nat)}
    (h : CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (hT : m'.acval T = m.acval T) {P : Expr md → Prop}
    (hP : ∀ (ψ : LevelParam → Nat) (d : Nat) (e : Expr md) (ea : AnnotTerm), P e →
      denoteMeta m.acval env ψ d e = some ea → denoteMeta m'.acval env' ψ d e = some ea)
    (hPty : P cvC.type) (hPidx : ∀ e ∈ idxArgs, P e) :
    CtorDataI m' T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs := by
  have hbody : ∀ ψ, ctorBodyAVI m' T nP nF ψ (Es ψ) = ctorBodyAVI m T nP nF ψ (Es ψ) := by
    intro ψ
    unfold ctorBodyAVI
    rw [hT]
  refine ⟨h.resid, fun ψ => ?_, h.len, h.lenE, h.idxLen, fun ψ => ?_, h.bits,
    fun ψ ρ => ?_, h.below, h.belowE, h.params, h.srcLen, h.srcBnd, h.srcIdx, h.srcProp⟩
  · rw [hbody]
    exact hP ψ 0 _ _ hPty (h.read ψ)
  · exact DenoteMetaSpine.transfer (hP ψ (nP + nF)) hPidx (h.idxRead ψ)
  · rw [hbody]; exact h.okTy ψ ρ

/-- **The recursive constructor data along a reading transfer** that is closed under
opening binders, reading a variable's type and selecting application arguments: every
reading in the data is of the constructor's type or of such a sub-expression. -/
theorem FixCtorDataI.transfer {env env' : Env md} {m : EnvModel V env} {m' : EnvModel V env'}
    {env₀ : Env md} {T : Key md} {lps : List LevelParam}
    {cvC : ConstantVal md} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List (Expr md)} {ds : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (LevelParam → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List (Expr md)} {xrest : Expr md} {Eiss : (LevelParam → Nat) → List (List AnnotTerm)}
    {tss : (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss)
    (hT : m'.acval T = m.acval T) {P : Expr md → Prop}
    (hP : ∀ (ψ : LevelParam → Nat) (d : Nat) (e : Expr md) (ea : AnnotTerm), P e →
      denoteMeta m.acval env ψ d e = some ea → denoteMeta m'.acval env' ψ d e = some ea)
    (hPopen : ∀ (n : Nat) (e : Expr md) (d : Nat) (fvs : List (Expr md)) (o : Expr md), P e →
      openPisAtFvars n e d = some (fvs, o) → (∀ x ∈ fvs, P x) ∧ P o)
    (hPfv : ∀ (k : Nat) (ty : Expr md), P (Expr.fvar k ty) → P ty)
    (hPargs : ∀ e : Expr md, P e → ∀ a ∈ e.getAppArgs, P a)
    (hPty : P cvC.type) :
    FixCtorDataI m' env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss := by
  obtain ⟨crest, hopP, hopX⟩ := h.opens
  have hopAll : openPisAtFvars (nP + nF) cvC.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hfvs, hrest⟩ := hPopen (nP + nF) cvC.type 0 _ _ hPty hopAll
  -- the opened variables' types
  have hx : ∀ (i : Nat) (x : Expr md), xFvs[i]? = some x → P x.fvarTypeD := by
    intro i x hxi
    have hb := hfvs x (List.mem_append_right _ (List.mem_of_getElem? hxi))
    obtain ⟨ty, rfl⟩ := h.xIdx i x hxi
    exact hPfv _ _ hb
  -- the index expressions are the residual's arguments
  have hidx : ∀ e ∈ idxArgs, P e := by
    intro e he
    rw [h.idxEq] at he
    exact hPargs xrest hrest e (List.mem_of_mem_drop he)
  have hbase := h.toCtorDataI.transfer hT hP hPty hidx
  exact {
    toCtorDataI := hbase
    opened := h.opened
    opens := h.opens
    ksLen := h.ksLen
    xLen := h.xLen
    pLen := h.pLen
    xIdx := h.xIdx
    pIdx := h.pIdx
    idxEq := h.idxEq
    domRead := fun ψ i x hxi => hP ψ (nP + i) _ _ (hx i x hxi) (h.domRead ψ i x hxi)
    eissLen := h.eissLen
    eisRead := fun ψ i x hxi hk =>
      DenoteMetaSpine.transfer (hP ψ (nP + i))
        (fun a ha => hPargs _ (hx i x hxi) a (List.mem_of_mem_drop ha)) (h.eisRead ψ i x hxi hk)
    eisLen := h.eisLen
    recEntry := fun ψ i hk hi => by
      rw [hT]
      exact h.recEntry ψ i hk hi
    eissParams := h.eissParams
    eissBelow := h.eissBelow
    ordNone := h.ordNone
    tssLen := h.tssLen
    tssNone := h.tssNone
    tssBits := h.tssBits
    tssPiBits := h.tssPiBits
    tssBelow := h.tssBelow
    tssParams := h.tssParams
    reflOpen := fun ψ i x hxi hk => by
      obtain ⟨afvs, body, hop, hlenTl, hdoms, hsp⟩ := h.reflOpen ψ i x hxi hk
      obtain ⟨hafvs, hbody⟩ := hPopen _ _ _ _ _ (hx i x hxi) hop
      refine ⟨afvs, body, hop, hlenTl, fun k a hka => ?_, ?_⟩
      · refine hP ψ (nP + i + k) _ _ ?_ (hdoms k a hka)
        have hb := hafvs a (List.mem_of_getElem? hka)
        obtain ⟨ty, hy⟩ := (opening_vars_at hop).2.1 k a hka
        rw [hy] at hb
        rw [hy]
        exact hPfv _ _ hb
      · exact DenoteMetaSpine.transfer (hP ψ _)
          (fun a ha => hPargs _ hbody a (List.mem_of_mem_drop ha)) hsp
    eisLenRefl := h.eisLenRefl
    reflEntry := fun ψ i hk hi => by
      rw [hT]
      exact h.reflEntry ψ i hk hi }

/-- **The recursive constructor data cross a cons** whose head is not the block's
former, when the head's slots are not mentioned by the constructor's type. The other
terms the data read are sub-expressions of its openings. -/
theorem FixCtorDataI.crossAt {env : Env md} {m : EnvModel V env} {env₀ : Env md} {T : Key md}
    {lps : List LevelParam}
    {cvC : ConstantVal md} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List (Expr md)} {ds : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (LevelParam → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List (Expr md)} {xrest : Expr md} {Eiss : (LevelParam → Nat) → List (List AnnotTerm)}
    {tss : (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss)
    {c₀ : ConstantInfo md} {A : (LevelParam → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hat : ConsCrossAt c₀ cvC.type) (hcb : ConstsBound env cvC.type)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    FixCtorDataI m₂ env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss := by
  refine h.transfer (m' := m₂) (P := fun e => ConstsBound env e ∧ ConsCrossAt c₀ e)
    (by rw [hac, acvalWith_ne hT]) ?_ ?_ ?_ ?_ ⟨hcb, hat⟩
  · intro ψ d e ea hPe hr
    obtain ⟨hb, hc⟩ := hPe
    rw [hac]
    exact denoteMeta_cons_mono hfresh hc ψ d hb hr
  · intro n e d fvs o hPe hop
    obtain ⟨hb, hc⟩ := hPe
    obtain ⟨hb1, hb2⟩ := openPisAtFvars_constsBound n hb hop
    obtain ⟨hc1, hc2⟩ := consCrossAt_openPis n hc hop
    exact ⟨fun x hx => ⟨hb1 x hx, hc1 x hx⟩, hb2, hc2⟩
  · intro k ty hPe
    obtain ⟨hb, hc⟩ := hPe
    exact ⟨constsBound_fvar.mp hb, fun tbl heq i => Ix.Kernel.Expr.noProjAt_fvar.mp (hc tbl heq i)⟩
  · intro e hPe a ha
    obtain ⟨hb, hc⟩ := hPe
    exact ⟨constsBound_getAppArgs e hb a ha,
      fun tbl heq i => Ix.Kernel.Expr.NoProjAt.getAppArgs (hc tbl heq i) a ha⟩

/-- **The field sources replaced**: the data at other sources and another eliminator
flag, from the sources' own facts. The readings are untouched. -/
theorem FixCtorDataI.withSrcs {env : Env md} {m : EnvModel V env} {env₀ : Env md} {T : Key md}
    {lps : List LevelParam}
    {cvC : ConstantVal md} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List (Expr md)} {ds : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (LevelParam → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List (Expr md)} {xrest : Expr md} {Eiss : (LevelParam → Nat) → List (List AnnotTerm)}
    {tss : (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss)
    {large' : Bool} {srcs' : List (Option Nat)}
    (hlen : srcs'.length = nF)
    (hbnd : ∀ s ∈ srcs', ∀ l, s = some l → l < nIdx)
    (hidx : ∀ j l, srcs'[j]? = some (some l) → ∀ ψ : LevelParam → Nat,
      (Es ψ)[l]? = some (AnnotTerm.bvar (nF - 1 - j)))
    (hprop : large' = true → ∀ ψ : LevelParam → Nat, resSort.eval ψ = 0 → ∀ ρ : Nat → V,
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      FieldsBoundSrc ρ (((ds ψ).drop nP).map (·.2.2)) srcs') :
    FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp large' idxArgs ds Es srcs' ks fvsP
      xFvs xrest Eiss tss :=
  { toCtorDataI := ⟨h.resid, h.read, h.len, h.lenE, h.idxLen, h.idxRead, h.bits, h.okTy,
      h.below, h.belowE, h.params, hlen, hbnd, hidx, hprop⟩
    opened := h.opened
    opens := h.opens
    ksLen := h.ksLen
    xLen := h.xLen
    pLen := h.pLen
    xIdx := h.xIdx
    pIdx := h.pIdx
    idxEq := h.idxEq
    domRead := h.domRead
    eissLen := h.eissLen
    eisRead := h.eisRead
    eisLen := h.eisLen
    recEntry := h.recEntry
    eissParams := h.eissParams
    eissBelow := h.eissBelow
    ordNone := h.ordNone
    tssLen := h.tssLen
    tssNone := h.tssNone
    tssBits := h.tssBits
    tssPiBits := h.tssPiBits
    tssBelow := h.tssBelow
    tssParams := h.tssParams
    reflOpen := h.reflOpen
    eisLenRefl := h.eisLenRefl
    reflEntry := h.reflEntry }

/-- The data at the small eliminator: the large eliminator's clause is vacuous. -/
theorem FixCtorDataI.small {env : Env md} {m : EnvModel V env} {env₀ : Env md} {T : Key md}
    {lps : List LevelParam}
    {cvC : ConstantVal md} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List (Expr md)} {ds : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (LevelParam → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List (Expr md)} {xrest : Expr md} {Eiss : (LevelParam → Nat) → List (List AnnotTerm)}
    {tss : (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss) :
    FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp false idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss :=
  h.withSrcs h.srcLen h.srcBnd h.srcIdx (fun hl => absurd hl Bool.false_ne_true)

/-! ## The family's data

The family's summary `NativeFam` is a judgement-level datum
(`Semantics/Inductives/DeclNativeRecLateJ.lean`). -/

/-- **The data of a stored native family at a model**: what the recursor's stage
(`stageFixRecJ`) reads of the family, with the constructors' data at the small
eliminator, and what carries it along a model extension.

* `resT` … `uParams`: the record's pins, statements about the record alone;
* `boundT`, `boundC`: the former's and the constructors' names are stored;
* `projT`, `projC`, `resC`, `idxRes`: the telescope's and the constructors' types have
  no projection node at a structure without a table, and resolve;
* `former`, `ctor`: the readings;
* `leafT`, `leafC`: the former's leaf is the fixed point over the constructors' data,
  each constructor's leaf is its injection;
* `paramsIff`, `frames`, `fieldsBound`: statements about interpretations alone. -/
structure NativeFamAt {env : Env md} (mp : EnvModelM V μ env) (p : NativeParts md)
    (cvS cvTa : ConstantVal md) (ctorsA : List (ConstantVal md × Nat))
    (env₀ : Env md) (bsT : List (Expr md × BinderMeta))
    (ppsAll : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm))
    (uAV : (LevelParam → Nat) → Nat) (fssZ : (LevelParam → Nat) → List (List AnnotTerm))
    (idxF : Nat → List (Expr md))
    (dsF : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (LevelParam → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List RecFieldKind) (fvsPF xFvsF : Nat → List (Expr md))
    (xrestF : Nat → Expr md)
    (eissF : Nat → (LevelParam → Nat) → List (List AnnotTerm))
    (tssF : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))) : Prop where
  resT : Ix.Kernel.reservedBasisNames.contains p.cvT.name = false
  lenA : ctorsA.length = p.ctors.length
  lenK : p.kinds.length = ctorsA.length
  ks : ∀ i, i < ctorsA.length → p.kinds[i]? = some (ksF i)
  stripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort)
  lpsT : cvTa.levelParams = p.cvT.levelParams
  lpsS : cvS.levelParams = p.cvT.levelParams
  lpsA : ∀ cA ∈ ctorsA, cA.1.levelParams = p.cvT.levelParams
  uParams : ∀ ψ₁ ψ₂ : LevelParam → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) →
    uAV ψ₁ = uAV ψ₂
  boundT : (env.find? p.cvT.name).isSome = true
  boundC : ∀ cA ∈ ctorsA, (env.find? cA.1.name).isSome = true
  projT : NoProjFresh env cvTa.type
  projC : ∀ cA ∈ ctorsA, NoProjFresh env cA.1.type
  resC : ∀ cA ∈ ctorsA, cA.1.type.constsResolve env = true
  idxRes : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true
  former : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll
  ctor : ∀ j cA, ctorsA[j]? = some cA →
    FixCtorDataI mp.base2 env₀ p.cvT.name p.cvT.levelParams cA.1 p.nP cA.2 p.nIdx p.resSort
      p.isProp false (idxF j) (dsF j) (esF j) (srcsF j) (ksF j) (fvsPF j) (xFvsF j) (xrestF j)
      (eissF j) (tssF j)
  leafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
    = nativeTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (((ppsAll ψ).drop p.nP).map (·.2.2))
        (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (fssZ ψ)
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
  leafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, mp.base2.acval cA.1.name ψ
    = sumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
        (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
  paramsIff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : LevelParam → Nat) (ρ : Nat → V),
    Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
      Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ
  frames : ∀ (ψ : LevelParam → Nat) (ρp : Nat → V),
    Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
    XChainsOk (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
      (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (fssZ ψ)
      (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
    ChainsRealI (fixFamI (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) p.nIdx
        (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (fssZ ψ)
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
      (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
      (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (fssZ ψ)
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
    (∀ j, j < ctorsA.length →
      FieldsOkB (p.resSort.eval ψ) ρp
        ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) ∧
      ∀ bs : List V, SpineFit ρp
          ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs →
        (∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [],
          WellDenoted V (consList bs ρp) E) ∧
        SpineFit ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
          (idxValsAt ρp ((essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [])
            bs)) ∧
    SumFieldsValid ρp (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
    (∀ j, j < ctorsA.length →
      ∀ i ∈ recIdx ((rssOfK ksF ctorsA.length).getD j [])
        ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).length,
      ∀ fs : List V, SpineFit ρp
          ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) fs →
      FieldsValid (consList (fs.take i) ρp)
        ((((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).map
          (·.2.2)) ∧
      ∀ bs : List V, SpineFit (consList (fs.take i) ρp)
        ((((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).map
          (·.2.2)) bs →
      ∀ E ∈ ((eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i [],
        AnnotValid V (consList bs (consList (fs.take i) ρp)) E) ∧
    (∀ j, j < ctorsA.length →
      ∀ bs : List V, SpineFit ρp
          ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs →
      ∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [],
        AnnotValid V (consList bs ρp) E)
  fieldsBound : p.isProp = false → ∀ j cA, ctorsA[j]? = some cA →
    ∀ (ψ : LevelParam → Nat) (ρ : Nat → V),
      Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
      FieldsBound (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2))

/-- **A stored native family is well-formed at a model**: `NativeFamAt` at some
readings. -/
@[expose] def NativeFamOk {env : Env md} (mp : EnvModelM V μ env) (fam : NativeFam md) : Prop :=
  ∃ (env₀ : Env md) (bsT : List (Expr md × BinderMeta))
    (ppsAll : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm))
    (uAV : (LevelParam → Nat) → Nat) (fssZ : (LevelParam → Nat) → List (List AnnotTerm))
    (idxF : Nat → List (Expr md))
    (dsF : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (LevelParam → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List RecFieldKind) (fvsPF xFvsF : Nat → List (Expr md))
    (xrestF : Nat → Expr md)
    (eissF : Nat → (LevelParam → Nat) → List (List AnnotTerm))
    (tssF : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))),
    NativeFamAt mp fam.p fam.cvS fam.cvTa fam.ctorsA env₀ bsT ppsAll uAV fssZ idxF dsF esF srcsF
      ksF fvsPF xFvsF xrestF eissF tssF

/-! ## Along a model extension -/

section Transport

variable {p : NativeParts md} {cvS cvTa : ConstantVal md}
  {ctorsA : List (ConstantVal md × Nat)}
  {env₀ : Env md} {bsT : List (Expr md × BinderMeta)}
  {ppsAll : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
  {uAV : (LevelParam → Nat) → Nat} {fssZ : (LevelParam → Nat) → List (List AnnotTerm)}
  {idxF : Nat → List (Expr md)}
  {dsF : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (LevelParam → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List (Expr md)}
  {xrestF : Nat → Expr md}
  {eissF : Nat → (LevelParam → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}

/-- The data at a model are the family's well-formedness there. -/
theorem NativeFamAt.ok {env : Env md} {mp : EnvModelM V μ env}
    (h : NativeFamAt mp p cvS cvTa ctorsA env₀ bsT ppsAll uAV fssZ idxF dsF esF srcsF ksF fvsPF
      xFvsF xrestF eissF tssF) :
    NativeFamOk mp ⟨p, cvS, cvTa, ctorsA⟩ := by
  unfold NativeFamOk
  exact ⟨env₀, bsT, ppsAll, uAV, fssZ, idxF, dsF, esF, srcsF, ksF, fvsPF, xFvsF, xrestF, eissF,
    tssF, h⟩

/-- **The data cross a fresh cons.** A head that is a projection table is fresh, so
its structure has no stored table and the tracked types have no node at its slots; any
other head changes no reading. The leaves are kept: the family's names are stored, so
the head is none of them. -/
theorem NativeFamAt.cons {env : Env md} {mp : EnvModelM V μ env}
    (h : NativeFamAt mp p cvS cvTa ctorsA env₀ bsT ppsAll uAV fssZ idxF dsF esF srcsF ksF fvsPF
      xFvsF xrestF eissF tssF)
    {c₀ : ConstantInfo md} {A : (LevelParam → Nat) → AnnotTerm}
    {mp₂ : EnvModelM V μ ⟨c₀ :: env.consts⟩}
    (hfresh : env.find? c₀.name = none)
    (hac : mp₂.base2.acval = acvalWith mp.base2.acval c₀.name A) :
    NativeFamAt mp₂ p cvS cvTa ctorsA env₀ bsT ppsAll uAV fssZ idxF dsF esF srcsF ksF fvsPF
      xFvsF xrestF eissF tssF := by
  have hsome : ∀ n : Key md, (env.find? n).isSome = true →
      ((⟨c₀ :: env.consts⟩ : Env md).find? n).isSome = true := by
    intro n hn
    rw [Ix.Kernel.Env.find?_cons]
    split
    · rfl
    · exact hn
  have hnone : ∀ n : Key md, (⟨c₀ :: env.consts⟩ : Env md).find? n = none →
      env.find? n = none := by
    intro n hn
    rw [Ix.Kernel.Env.find?_cons] at hn
    split at hn
    · exact nomatch hn
    · exact hn
  have hne : ∀ n : Key md, (env.find? n).isSome = true → n ≠ c₀.name := by
    intro n hn heq
    rw [heq, hfresh] at hn
    simp at hn
  have hTne : p.cvT.name ≠ c₀.name := hne _ h.boundT
  exact {
    resT := h.resT
    lenA := h.lenA
    lenK := h.lenK
    ks := h.ks
    stripT := h.stripT
    lpsT := h.lpsT
    lpsS := h.lpsS
    lpsA := h.lpsA
    uParams := h.uParams
    boundT := hsome _ h.boundT
    boundC := fun cA hcA => hsome _ (h.boundC cA hcA)
    projT := h.projT.mono hnone
    projC := fun cA hcA => (h.projC cA hcA).mono hnone
    resC := fun cA hcA => Ix.Kernel.Expr.constsResolve_mono (h.resC cA hcA)
    idxRes := fun j cA hj e he => Ix.Kernel.Expr.constsResolve_mono (h.idxRes j cA hj e he)
    former := h.former.cross hfresh (h.projT.consCross hfresh)
      (constsBound_of_constsResolve _ h.former.cr) mp₂.base2 hac
    ctor := fun j cA hj =>
      (h.ctor j cA hj).crossAt hfresh hTne
        ((h.projC cA (List.mem_of_getElem? hj)).consCross hfresh)
        (constsBound_of_constsResolve _ (h.resC cA (List.mem_of_getElem? hj))) mp₂.base2 hac
    leafT := fun ψ => by
      rw [hac, acvalWith_ne hTne]
      exact h.leafT ψ
    leafC := fun j cA hj ψ => by
      rw [hac, acvalWith_ne (hne _ (h.boundC cA (List.mem_of_getElem? hj)))]
      exact h.leafC j cA hj ψ
    paramsIff := h.paramsIff
    frames := h.frames
    fieldsBound := h.fieldsBound }

/-- **The data cross a step that keeps every leaf and every reading** and stores at
least the same names (`ModelExt.swap`'s step). -/
theorem NativeFamAt.swap {env env' : Env md} {mp : EnvModelM V μ env}
    {mp' : EnvModelM V μ env'}
    (h : NativeFamAt mp p cvS cvTa ctorsA env₀ bsT ppsAll uAV fssZ idxF dsF esF srcsF ksF fvsPF
      xFvsF xrestF eissF tssF)
    (hsome : ∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true)
    (hden : ∀ (ψ : LevelParam → Nat) (d : Nat) (e : Expr md),
      denoteMeta mp.base2.acval env ψ d e = denoteMeta mp.base2.acval env' ψ d e)
    (hac : mp'.base2.acval = mp.base2.acval) :
    NativeFamAt mp' p cvS cvTa ctorsA env₀ bsT ppsAll uAV fssZ idxF dsF esF srcsF ksF fvsPF
      xFvsF xrestF eissF tssF := by
  have hnone : ∀ n : Key md, env'.find? n = none → env.find? n = none := by
    intro n hn
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      have h1 := hsome n (by rw [hf]; rfl)
      rw [hn] at h1
      simp at h1
  exact {
    resT := h.resT
    lenA := h.lenA
    lenK := h.lenK
    ks := h.ks
    stripT := h.stripT
    lpsT := h.lpsT
    lpsS := h.lpsS
    lpsA := h.lpsA
    uParams := h.uParams
    boundT := hsome _ h.boundT
    boundC := fun cA hcA => hsome _ (h.boundC cA hcA)
    projT := h.projT.mono hnone
    projC := fun cA hcA => (h.projC cA hcA).mono hnone
    resC := fun cA hcA => Ix.Kernel.Expr.constsResolve_of_find hsome (h.resC cA hcA)
    idxRes := fun j cA hj e he =>
      Ix.Kernel.Expr.constsResolve_of_find hsome (h.idxRes j cA hj e he)
    former := {
      read := fun ψ => by
        rw [hac, ← hden ψ 0 cvTa.type]
        exact h.former.read ψ
      len := h.former.len
      bits := h.former.bits
      okTy := h.former.okTy
      below := h.former.below
      params := h.former.params
      tf := h.former.tf
      tb := h.former.tb
      cr := Ix.Kernel.Expr.constsResolve_of_find hsome h.former.cr }
    ctor := fun j cA hj =>
      (h.ctor j cA hj).transfer (m' := mp'.base2) (P := fun _ => True) (by rw [hac])
        (fun ψ d e ea _ hr => by
          rw [hac, ← hden ψ d e]
          exact hr)
        (fun _ _ _ _ _ _ _ => ⟨fun _ _ => trivial, trivial⟩)
        (fun _ _ _ => trivial) (fun _ _ _ _ => trivial) trivial
    leafT := fun ψ => by
      rw [hac]
      exact h.leafT ψ
    leafC := fun j cA hj ψ => by
      rw [hac]
      exact h.leafC j cA hj ψ
    paramsIff := h.paramsIff
    frames := h.frames
    fieldsBound := h.fieldsBound }

/-- **The data along a model extension.** -/
theorem NativeFamAt.ext {env₁ env₂ : Env md} {mp₁ : EnvModelM V μ env₁}
    {mp₂ : EnvModelM V μ env₂}
    (h : NativeFamAt mp₁ p cvS cvTa ctorsA env₀ bsT ppsAll uAV fssZ idxF dsF esF srcsF ksF fvsPF
      xFvsF xrestF eissF tssF)
    (hext : ModelExt mp₁ mp₂) :
    NativeFamAt mp₂ p cvS cvTa ctorsA env₀ bsT ppsAll uAV fssZ idxF dsF esF srcsF ksF fvsPF
      xFvsF xrestF eissF tssF := by
  induction hext with
  | refl => exact h
  | step _ hfresh _ _ hac ih => exact ih.cons hfresh hac
  | swap _ hsome _ hden hac ih => exact ih.swap hsome hden hac

end Transport

/-- **A stored native family stays well-formed along a model extension**, at the same
summary: every declaration step extends the model it is given, so the recursor's stage
applies to the family at every later environment. -/
theorem NativeFamOk.ext {env₁ env₂ : Env md} {mp₁ : EnvModelM V μ env₁}
    {mp₂ : EnvModelM V μ env₂} {fam : NativeFam md}
    (h : NativeFamOk mp₁ fam) (hext : ModelExt mp₁ mp₂) : NativeFamOk mp₂ fam := by
  unfold NativeFamOk at h ⊢
  obtain ⟨env₀, bsT, ppsAll, uAV, fssZ, idxF, dsF, esF, srcsF, ksF, fvsPF, xFvsF, xrestF, eissF,
    tssF, h⟩ := h
  exact ⟨env₀, bsT, ppsAll, uAV, fssZ, idxF, dsF, esF, srcsF, ksF, fvsPF, xFvsF, xrestF, eissF,
    tssF, h.ext hext⟩

end Ix.Kernel.Model
