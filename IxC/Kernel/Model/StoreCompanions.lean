module

public import IxC.Kernel.Model.NoRecBlock
public import IxC.Kernel.Rules.Transport
/- `Ix.Kernel.PropWhen` seals its representation; the pinned blocks' facts are decided by
evaluating terms that carry it, so `import all` gives that view HERE only. -/
import all IxC.Kernel.PropWhen

@[expose] public section

/-!
# Four store facts along a run, model-free

Companions of the store invariant (`StoreInv`, `Model/StoreFold.lean`), each kept by every
declaration step of a run over the derivation package (`DeclsRunJ rulesJ (IndRoutesJ rulesJ)`):

* `ThmTyped env`: every stored theorem's value is closed and typed, against its type, which is a
  proposition at every assignment, by derivations at `env` (`thmTyped_declsRunJ`). Each theorem's
  own step derives it; a later step extends the store (`EnvExt`), and the derivations move along
  it (`Infer.weaken`, `DefEq.weaken`, `Red.weaken`). A basis step extends the store too
  (`basisRun_envExt`).
* `RecKExact env`: every stored rule's K bit is the store's verdict `recRuleKOf` at `env`, and a
  rule with the K bit set is the only rule of a recursor without a model companion
  (`recK_declsRunJ`).
* `EtaTowers env`: a stored family with the η capability has a projection table entry at each of
  its `etaFields` slots (`towerSlotsAll`, `etaTowers_declsRunJ`).
* `TableBodies env`: every stored projection table's bodies are the generator's
  (`structProjBodies`) at its stored constructor's type, and its guards are the generator's
  (`structProjGuards`) at that type and some field sorts, one per field
  (`tableBodies_declsRunJ`).

The steps are read through `NewSat`: every constant a step stores is the old environment's or of
a kind the step installs.
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics
open Ix.Kernel.Open (StoreInv)
open Ix.Kernel (Env Key Expr Level ConstantInfo ConstantVal RecRule Declaration BasisKind IndCaps
  InductiveShape NativeParts RecFieldKind EnvExt ProjTable)

/-! ## What a step stores -/

/-- **Every constant `env₂` stores is `env`'s or satisfies `Q`.** -/
def NewSat (env env₂ : Env md) (Q : ConstantInfo md → Prop) : Prop :=
  ∀ (n : Key md) (x : ConstantInfo md), env₂.find? n = some x → env.find? n = some x ∨ Q x

namespace NewSat

theorem refl (env : Env md) (Q : ConstantInfo md → Prop) : NewSat env env Q :=
  fun _ _ hf => .inl hf

theorem cons {env : Env md} {c : ConstantInfo md} {Q : ConstantInfo md → Prop} (hQ : Q c) :
    NewSat env ⟨c :: env.consts⟩ Q := by
  intro n x hf
  rw [Ix.Kernel.Env.find?_cons] at hf
  split at hf
  · obtain rfl := Option.some.inj hf
    exact .inr hQ
  · exact .inl hf

theorem trans {e₁ e₂ e₃ : Env md} {Q : ConstantInfo md → Prop} (h₁ : NewSat e₁ e₂ Q)
    (h₂ : NewSat e₂ e₃ Q) : NewSat e₁ e₃ Q := by
  intro n x hf
  rcases h₂ n x hf with h | h
  · exact h₁ n x h
  · exact .inr h

end NewSat

theorem consSumCtors_newSat {nP : Nat} {Q : ConstantInfo md → Prop}
    (hQ : ∀ cv a b, Q (.ctorInfo cv a b)) :
    ∀ {ctorsA : List (ConstantVal md × Nat)} {env : Env md},
      NewSat env (Ix.Kernel.consSumCtors nP ctorsA env) Q
  | [], env => NewSat.refl env Q
  | _ :: _, _ => by
    simp only [Ix.Kernel.consSumCtors]
    exact (NewSat.cons (hQ _ _ _)).trans (consSumCtors_newSat hQ)

theorem nativeTable_newSat {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {X X₂ : Env md} {Q : ConstantInfo md → Prop}
    (hQ : ∀ t, Q (.projInfo t))
    (h : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss X = .ok X₂) :
    NewSat X X₂ Q := by
  unfold Ix.Kernel.checkNativeTable at h
  split at h
  · split at h
    · obtain ⟨bodies, -, -, -, -, rfl⟩ := Ix.Kernel.checkStructProjTable_inv h
      exact NewSat.cons (hQ _)
    · obtain rfl := Except.ok.inj h
      exact NewSat.refl _ Q
  · obtain rfl := Except.ok.inj h
    exact NewSat.refl _ Q

/-- **The native route stores a former, constructors, a recursor and a table.** -/
theorem native_newSat {J : Judgements md} {env env₂ : Env md} {p₀ : NativeParts md}
    {Q : ConstantInfo md → Prop}
    (hQi : ∀ cv caps, Q (.indInfo cv caps)) (hQc : ∀ cv a b, Q (.ctorInfo cv a b))
    (hQr : ∀ cv a b rs, Q (.recInfo cv a b rs)) (hQp : ∀ t, Q (.projInfo t))
    (hrun : DeclNativeRunJ J env p₀ env₂) : NewSat env env₂ Q := by
  obtain ⟨-, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, -, -, -, hInd, -,
    -, -, -, -, -, -, -, -, -, -, hTbl⟩ := hrun
  obtain ⟨_, _, _, _, _, _, henv₁, _, _⟩ := hInd.shape
  subst henv₁
  exact (NewSat.cons (hQi _ _)).trans ((consSumCtors_newSat hQc).trans
    ((NewSat.cons (hQr _ _ _ _)).trans (nativeTable_newSat hQp hTbl)))

/-- **The native route without a recursor stores a former, constructors and a table.** -/
theorem nativeNoRec_newSat {J : Judgements md} {env env₂ : Env md} {p₀ : NativeParts md}
    {Q : ConstantInfo md → Prop}
    (hQi : ∀ cv caps, Q (.indInfo cv caps)) (hQc : ∀ cv a b, Q (.ctorInfo cv a b))
    (hQp : ∀ t, Q (.projInfo t))
    (hrun : DeclNativeNoRecRunJ J env p₀ env₂) : NewSat env env₂ Q := by
  obtain ⟨-, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, -, -, -, -, -, -,
    -, hTbl⟩ := hrun
  obtain ⟨_, _, _, _, _, _, henv₁, _, _⟩ := hInd.shape
  subst henv₁
  exact (NewSat.cons (hQi _ _)).trans ((consSumCtors_newSat hQc).trans
    (nativeTable_newSat hQp hTbl))

theorem indMembersRunJ_newSat {J : Judgements md} {blockNames : List (Key md)}
    {caps : IndCaps md} {Q : ConstantInfo md → Prop}
    (hQi : ∀ cv, Q (.indInfo cv caps)) (hQc : ∀ cv a b, Q (.ctorInfo cv a b)) :
    ∀ {env' : Env md} {members : List (ConstantInfo md)} {env₂ : Env md},
      IndMembersRunJ J blockNames caps env' members env₂ → NewSat env' env₂ Q
  | _, [], _, h => by
    subst h
    exact NewSat.refl _ Q
  | _, ci :: _, _, h => by
    obtain ⟨_, -, hm⟩ := h
    cases ci with
    | indInfo _ _ => exact (NewSat.cons (hQi _)).trans (indMembersRunJ_newSat hQi hQc hm)
    | ctorInfo _ _ _ => exact (NewSat.cons (hQc _ _ _)).trans (indMembersRunJ_newSat hQi hQc hm)
    | axiomInfo _ => exact nomatch hm
    | defnInfo _ _ _ => exact nomatch hm
    | thmInfo _ _ => exact nomatch hm
    | recInfo _ _ _ _ => exact nomatch hm
    | projInfo _ => exact nomatch hm

theorem indRecsFoldRunJ_newSat {J : Judgements md} {blockNames : List (Key md)}
    {envBase envSelf : Env md} {Q : ConstantInfo md → Prop}
    (hQr : ∀ cv a b rs, Q (.recInfo cv a b rs)) :
    ∀ {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))} {acc out : Env md},
      IndRecsFoldRunJ J blockNames envBase envSelf acc checked out → NewSat acc out Q
  | [], acc, out, h => by
    obtain rfl : out = acc := h
    exact NewSat.refl _ Q
  | _ :: _, _, _, h => by
    obtain ⟨_, -, h'⟩ := h
    exact (NewSat.cons (hQr _ _ _ _)).trans (indRecsFoldRunJ_newSat hQr h')

/-- **The modeled route stores members at the empty capability record, and recursors.** -/
theorem modeled_newSat {J : Judgements md} {env env₂ : Env md} {block : List (ConstantInfo md)}
    {Q : ConstantInfo md → Prop}
    (hQi : ∀ cv, Q (.indInfo cv {})) (hQc : ∀ cv a b, Q (.ctorInfo cv a b))
    (hQr : ∀ cv a b rs, Q (.recInfo cv a b rs))
    (hrun : DeclIndRunJ J env block env₂) : NewSat env env₂ Q := by
  obtain ⟨-, envM, hmem, hrecs⟩ := hrun
  have hM := indMembersRunJ_newSat hQi hQc hmem
  rcases hrecs with ⟨-, rfl⟩ | ⟨-, -, envSelf, checked, -, hfold⟩
  · exact hM
  · exact hM.trans (indRecsFoldRunJ_newSat hQr hfold)

/-! ## A basis step extends the store -/

/-- A role's key. -/
def keyIsRole : Key md → Bool
  | .role _ => true
  | _ => false

/-- A basis block's constants are stored at role keys. -/
def basisNamesRoleb {md : Ix.Kernel.Mode} (kind : BasisKind) : Bool :=
  (kind.declsA (md := md)).all fun c => keyIsRole c.name

theorem basis_names_role (kind : BasisKind) : basisNamesRoleb (md := md) kind = true := by
  cases kind <;> (cases md <;> decide +kernel)

theorem basis_find_projTable_none (kind : BasisKind) (T : Key md) :
    Env.find? ⟨(kind.declsA (md := md)).reverse⟩ (Ix.Kernel.projTableName T) = none := by
  cases hf : Env.find? ⟨(kind.declsA (md := md)).reverse⟩ (Ix.Kernel.projTableName T) with
  | none => rfl
  | some c =>
    exfalso
    have hmem : c ∈ kind.declsA := List.mem_reverse.mp (Ix.Kernel.Semantics.Env.find?_mem hf)
    have hname : c.name = Ix.Kernel.projTableName T := Ix.Kernel.Semantics.Env.find?_name hf
    have hr : keyIsRole c.name = true := List.all_eq_true.mp (basis_names_role (md := md) kind) c hmem
    rw [hname] at hr
    simp [keyIsRole, Ix.Kernel.projTableName, Ix.Kernel.auxKey] at hr

/-- **A basis step extends the store**: its constants are fresh, and none is a projection
table, so every stored structure keeps its table. -/
theorem basisRun_envExt {env env₂ : Env md} {kind : BasisKind}
    (hrun : DeclBasisRun env kind env₂) : EnvExt env env₂ where
  find := basisRun_find hrun
  tables := by
    intro T _ _ _
    obtain ⟨-, hinst⟩ := hrun
    obtain ⟨rfl, -⟩ := basisInstallRun_eq hinst
    rw [find?_prefix, basis_find_projTable_none kind T]
    rfl

/-- **A step extends the store**, at every declaration kind and inductive route. -/
theorem declRunJ_envExt_routes {J : Judgements md} {env env₂ : Env md} {d : Declaration md}
    (hrun : DeclRunJ J (IndRoutesJ J env) env d env₂) : EnvExt env env₂ :=
  declRunJ_envExt (fun hb => basisRun_envExt hb) (fun hI => indRoutesJ_envExt hI) hrun

/-- A basis block stores its own constants. -/
theorem basis_newSat {env env₂ : Env md} {kind : BasisKind} {Q : ConstantInfo md → Prop}
    (hQ : ∀ c ∈ kind.declsA, Q c) (hrun : DeclBasisRun env kind env₂) : NewSat env env₂ Q := by
  obtain ⟨-, hinst⟩ := hrun
  obtain ⟨rfl, -⟩ := basisInstallRun_eq hinst
  intro n x hf
  rw [find?_prefix] at hf
  cases hb : Env.find? ⟨kind.declsA.reverse⟩ n with
  | none =>
    rw [hb] at hf
    exact .inl hf
  | some c =>
    rw [hb] at hf
    obtain rfl := Option.some.inj hf
    exact .inr (hQ c (List.mem_reverse.mp (Ix.Kernel.Semantics.Env.find?_mem hb)))

/-! ## Stored theorems are typed -/

/-- **Every stored theorem's value is closed and typed against its type**, a proposition at
every assignment, by derivations at `env`: `Red.deltaThm`'s premises. -/
def ThmTyped (env : Env md) : Prop :=
  ∀ n cv value, env.find? n = some (.thmInfo cv value) →
    value.hasFvar = false ∧ value.looseBVarsBounded 0 = true ∧
    ∃ vt s u, Ix.Kernel.Rules.Infer env .full 0 value vt ∧
      Ix.Kernel.Rules.DefEq env 0 vt cv.type ∧
      Ix.Kernel.Rules.Infer env .full 0 cv.type s ∧ Ix.Kernel.Rules.Red env 0 s (.sort u) ∧
      ∀ φ : LevelParam → Nat, Level.eval φ u = 0

theorem ThmTyped.empty : ThmTyped (md := md) Env.empty := by
  intro n cv value h
  simp [Env.find?, Env.empty] at h

/-- Not a theorem. -/
def NotThm (x : ConstantInfo md) : Prop := ∀ cv v, x ≠ .thmInfo cv v

/-- **One step keeps the stored theorems typed**, given the theorems it stores. -/
theorem thmTyped_step {env env₂ : Env md} (hext : EnvExt env env₂) (h : ThmTyped env)
    (hnew : ∀ n cv value, env₂.find? n = some (.thmInfo cv value) → env.find? n = none →
      value.hasFvar = false ∧ value.looseBVarsBounded 0 = true ∧
      ∃ vt s u, Ix.Kernel.Rules.Infer env₂ .full 0 value vt ∧
        Ix.Kernel.Rules.DefEq env₂ 0 vt cv.type ∧
        Ix.Kernel.Rules.Infer env₂ .full 0 cv.type s ∧
        Ix.Kernel.Rules.Red env₂ 0 s (.sort u) ∧ ∀ φ : LevelParam → Nat, Level.eval φ u = 0) :
    ThmTyped env₂ := by
  intro n cv value hf
  cases hold : env.find? n with
  | none => exact hnew n cv value hf hold
  | some c =>
    have h2 := hext.find hold
    rw [hf] at h2
    obtain rfl := Option.some.inj h2
    obtain ⟨h1, h2, vt, s, u, hi, hd, hs, hr, hz⟩ := h n cv value hold
    exact ⟨h1, h2, vt, s, u, Ix.Kernel.Rules.Infer.weaken hext hi,
      Ix.Kernel.Rules.DefEq.weaken hext hd, Ix.Kernel.Rules.Infer.weaken hext hs,
      Ix.Kernel.Rules.Red.weaken hext hr, hz⟩

/-- A step that stores no theorem keeps them typed. -/
theorem thmTyped_step_noThm {env env₂ : Env md} (hext : EnvExt env env₂) (h : ThmTyped env)
    (hno : NewSat env env₂ NotThm) : ThmTyped env₂ := by
  refine thmTyped_step hext h ?_
  intro n cv value hf hn
  rcases hno _ _ hf with h' | h'
  · rw [h'] at hn
    exact nomatch hn
  · exact absurd rfl (h' cv value)

/-- A basis block stores no theorem. -/
def basisNoThmb {md : Ix.Kernel.Mode} (kind : BasisKind) : Bool :=
  (kind.declsA (md := md)).all fun c => match c with
    | .thmInfo _ _ => false
    | _ => true

theorem basis_noThm (kind : BasisKind) : basisNoThmb (md := md) kind = true := by
  cases kind <;> (cases md <;> decide +kernel)

theorem basis_newSat_noThm {env env₂ : Env md} {kind : BasisKind}
    (hrun : DeclBasisRun env kind env₂) : NewSat env env₂ NotThm := by
  refine basis_newSat (fun c hc cv v heq => ?_) hrun
  have h := List.all_eq_true.mp (basis_noThm (md := md) kind) c hc
  subst heq
  simp at h

theorem indRoutes_newSat_noThm {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} {nP : Nat} (hI : IndRoutesJ J env block nP env₂) :
    NewSat env env₂ NotThm := by
  rcases hI with ⟨_, -, hN⟩ | hM | ⟨_, -, hN⟩
  · exact native_newSat (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
      (fun _ _ _ _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h) hN
  · exact modeled_newSat (fun _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
      (fun _ _ _ _ _ _ h => nomatch h) hM
  · exact nativeNoRec_newSat (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) hN

/-- **One declaration step keeps the stored theorems typed**, over the derivation package. -/
theorem thmTyped_declRunJ {env env₂ : Env md} {d : Declaration md} (h : ThmTyped env)
    (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) : ThmTyped env₂ := by
  have hext := declRunJ_envExt_routes hrun
  cases d with
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, ⟨stype, u, hst, hsu, hz⟩, hvf, rfl⟩ := hrun
    refine thmTyped_step hext h ?_
    intro n cv' value'' hf hn
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · obtain ⟨rfl, rfl⟩ := ConstantInfo.thmInfo.inj (Option.some.inj hf)
      obtain ⟨hb, hfv, hann, -, -, vt, hvt, hde⟩ := hvf
      obtain ⟨hfv', hb'⟩ := (judgeFrames_rulesJ env).annot_syntax hann hfv hb
      exact ⟨hfv', hb', vt, stype, u, Ix.Kernel.Rules.Infer.weaken hext hvt,
        Ix.Kernel.Rules.DefEq.weaken hext hde, Ix.Kernel.Rules.Infer.weaken hext hst,
        Ix.Kernel.Rules.Red.weaken hext hsu, hz⟩
    · rw [hf] at hn
      exact nomatch hn
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hrun
    exact thmTyped_step_noThm hext h (NewSat.cons (fun _ _ heq => nomatch heq))
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl⟩ := hrun
    exact thmTyped_step_noThm hext h (NewSat.cons (fun _ _ heq => nomatch heq))
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact h
    · exact thmTyped_step_noThm hext h (NewSat.cons (fun _ _ heq => nomatch heq))
    · exact h
  | basisDecl kind => exact thmTyped_step_noThm hext h (basis_newSat_noThm hrun)
  | indDecl block nP =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact thmTyped_step_noThm hext h (basis_newSat_noThm hrun)
    · exact thmTyped_step_noThm hext h (indRoutes_newSat_noThm hrun)
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact thmTyped_step_noThm hext h (basis_newSat_noThm hrun)
    · subst hrun
      exact h

/-- **Along a run, every stored theorem is typed**, from an environment where they are. -/
theorem thmTyped_declsRunJ {env env' : Env md} {ds : List (Declaration md)}
    (hds : DeclsRunJ rulesJ (IndRoutesJ rulesJ) env ds env') (h : ThmTyped env) :
    ThmTyped env' := by
  revert h
  induction hds with
  | nil => exact id
  | cons hd _ ih => exact fun h => ih (thmTyped_declRunJ h hd)

/-! ## The K bit is the store's verdict -/

/-- Not an inductive type. -/
def NotInd (x : ConstantInfo md) : Prop := ∀ cv caps, x ≠ .indInfo cv caps

/-- Not a recursor. -/
def NotRec (x : ConstantInfo md) : Prop := ∀ cv a b rs, x ≠ .recInfo cv a b rs

/-- **The K verdict is kept** by an extension that keeps the constructor's lookup and, unless the
constructor's family is already found, stores no inductive type at the family's key. -/
theorem recRuleKOf_ext {f g : Key md → Option (ConstantInfo md)} {c : Key md}
    (hext : ∀ {k : Key md} {x : ConstantInfo md}, f k = some x → g k = some x)
    {cvj : ConstantVal md} {a b : Nat} (hc : f c = some (.ctorInfo cvj a b))
    (hT : ∀ T us, (cvj.type.piResult).getAppFn = .const T us →
      (f T).isSome = true ∨ ∀ x, g T = some x → f T = none → NotInd x) :
    Ix.Kernel.recRuleKOf f c = Ix.Kernel.recRuleKOf g c := by
  unfold Ix.Kernel.recRuleKOf
  rw [hc, hext hc]
  dsimp only
  generalize hh : (cvj.type.piResult).getAppFn = hd
  cases hd with
  | const T us =>
    dsimp only
    rcases hT T us hh with hs | hn
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
      rw [hy, hext hy]
    · cases hfT : f T with
      | some y => rw [hext hfT]
      | none =>
        cases hgT : g T with
        | none => rfl
        | some x =>
          cases x with
          | indInfo cv caps => exact absurd rfl (hn _ hgT hfT cv caps)
          | _ => rfl
  | _ => rfl

/-- **Every stored rule's K bit is the store's verdict.** -/
def RecKExact (env : Env md) : Prop :=
  ∀ n cv mI rP rules, env.find? n = some (.recInfo cv mI rP rules) → ∀ r ∈ rules,
    r.k = Ix.Kernel.recRuleKOf env.find? r.ctor

/-- **A rule with the K bit is its recursor's only rule**, at a recursor without a model
companion (a modeled recursor's rules are its model's equations and may sit at any stored
constructor, `NoRuleFamily`). -/
def RecKSingle (env : Env md) : Prop :=
  ∀ n cv mI rP rules, env.find? n = some (.recInfo cv mI rP rules) → ¬ HasModel env n →
    ∀ r ∈ rules, r.k = true → rules = [r]

/-- The K facts. -/
structure RecK (env : Env md) : Prop where
  kExact : RecKExact env
  kSingle : RecKSingle env

theorem RecK.empty : RecK (md := md) Env.empty :=
  ⟨fun _ _ _ _ _ h => by simp [Env.find?, Env.empty] at h,
    fun _ _ _ _ _ h => by simp [Env.find?, Env.empty] at h⟩

/-- An old rule's verdict is kept by every extension: its constructor is stored, and so is the
family its type ends in. -/
theorem recRuleKOf_stable {env env₂ : Env md} (h : StoreInv env)
    (hfind : ∀ {k : Key md} {x : ConstantInfo md}, env.find? k = some x → env₂.find? k = some x)
    {n : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hf : env.find? n = some (.recInfo cv mI rP rules)) {r : RecRule md} (hr : r ∈ rules) :
    Ix.Kernel.recRuleKOf env.find? r.ctor = Ix.Kernel.recRuleKOf env₂.find? r.ctor := by
  obtain ⟨⟨cvj, hc, -⟩, -, -⟩ := h.rec_ctors n cv mI rP rules hf r hr
  refine recRuleKOf_ext hfind hc (fun T us heq => .inl ?_)
  have hres : cvj.type.constsResolve env = true :=
    (h.wf _ (Ix.Kernel.Semantics.Env.find?_mem hc)).2.2.1
  have h2 := constsResolve_getAppFn (constsResolve_piResult hres)
  rw [heq] at h2
  simpa [Ix.Kernel.Expr.constsResolve] using h2

/-- **One step keeps the K facts**, given those of the recursors it stores. -/
theorem recK_step {env env₂ : Env md} (h : StoreInv env) (hK : RecK env)
    (hfind : ∀ {k : Key md} {x : ConstantInfo md}, env.find? k = some x → env₂.find? k = some x)
    (hnew : ∀ n cv mI rP rules, env₂.find? n = some (.recInfo cv mI rP rules) →
      env.find? n = none →
      (∀ r ∈ rules, r.k = Ix.Kernel.recRuleKOf env₂.find? r.ctor) ∧
      (¬ HasModel env₂ n → ∀ r ∈ rules, r.k = true → rules = [r])) :
    RecK env₂ := by
  refine ⟨?_, ?_⟩
  · intro n cv mI rP rules hf r hr
    cases hold : env.find? n with
    | none => exact (hnew n cv mI rP rules hf hold).1 r hr
    | some c =>
      have h2 := hfind hold
      rw [hf] at h2
      obtain rfl := Option.some.inj h2
      rw [hK.kExact n cv mI rP rules hold r hr]
      exact recRuleKOf_stable h hfind hold hr
  · intro n cv mI rP rules hf hm r hr hk
    cases hold : env.find? n with
    | none => exact (hnew n cv mI rP rules hf hold).2 hm r hr hk
    | some c =>
      have h2 := hfind hold
      rw [hf] at h2
      obtain rfl := Option.some.inj h2
      exact hK.kSingle n cv mI rP rules hold (fun hm' => hm (hm'.mono hfind)) r hr hk

/-- A step that stores no recursor keeps the K facts. -/
theorem recK_step_noRec {env env₂ : Env md} (h : StoreInv env) (hK : RecK env)
    (hfind : ∀ {k : Key md} {x : ConstantInfo md}, env.find? k = some x → env₂.find? k = some x)
    (hno : NewSat env env₂ NotRec) : RecK env₂ := by
  refine recK_step h hK hfind ?_
  intro n cv mI rP rules hf hn
  rcases hno _ _ hf with h' | h'
  · rw [h'] at hn
    exact nomatch hn
  · exact absurd rfl (h' cv mI rP rules)

/-- A one-element bound on a list holding `r`. -/
theorem eq_singleton_of_length_le_one {l : List α} {r : α} (hl : l.length ≤ 1) (hr : r ∈ l) :
    l = [r] := by
  match l, hl, hr with
  | [a], _, hr => rw [List.mem_singleton.mp hr]
  | _ :: _ :: _, hl, _ => simp at hl

theorem sumRules_length_le {find? : Key md → Option (ConstantInfo md)} {recName : Key md}
    {nP mI rP : Nat} {recTy : Expr md} :
    ∀ {ctorsA : List (ConstantVal md × Nat)} {rhss : List (Expr md)},
      (Ix.Kernel.sumRules find? recName nP mI rP recTy ctorsA rhss).length ≤ ctorsA.length
  | [], _ => by simp [Ix.Kernel.sumRules]
  | _ :: _, [] => by simp [Ix.Kernel.sumRules]
  | _ :: cs, _ :: rhss => by
    simp only [Ix.Kernel.sumRules, List.length_cons]
    have := sumRules_length_le (find? := find?) (recName := recName) (nP := nP) (mI := mI)
      (rP := rP) (recTy := recTy) (ctorsA := cs) (rhss := rhss)
    omega

/-- The K capability is a one-constructor block's. -/
theorem nativeCapsAt_ruleK {p : InductiveShape md} {isRec : Bool}
    (h : (Ix.Kernel.nativeCapsAt p isRec).ruleK = true) : ∃ c, p.ctors = [c] := by
  unfold Ix.Kernel.nativeCapsAt at h
  split at h
  · next c hc => exact ⟨c, hc⟩
  · exact nomatch h

/-- **The native route's recursor**: its rules' K bits are the verdict at the step's end, and a
rule with the K bit is the only one (the K capability is a one-constructor block's). -/
theorem native_recK_new {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {p₀ : NativeParts md} (hrc : NativeRecog p₀) (h : StoreInv env)
    (hrun : DeclNativeRunJ J env p₀ env₂) :
    ∀ n cv mI rP rules, env₂.find? n = some (.recInfo cv mI rP rules) → env.find? n = none →
      (∀ r ∈ rules, r.k = Ix.Kernel.recRuleKOf env₂.find? r.ctor) ∧
      (∀ r ∈ rules, r.k = true → rules = [r]) := by
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, -, -, -, hInd, hp,
    hCtors, -, -, -, -, -, -, -, hRec, -, hTbl⟩ := hrun
  have hF := nativeFront hfr h hrc hnd hInd hp hCtors
  obtain ⟨_, s, _, _, _, hp₁, henv₁, _, _⟩ := hInd.shape
  obtain ⟨hnR, -, hfR, -⟩ := hRec.recursor
  let envC := Ix.Kernel.consSumCtors p.nP ctorsA env₁
  have hfreshR : envC.find? cvRa.name = none := by rw [hnR]; exact hfR
  -- lookups of the constructors' environment survive the recursor's cons and the table
  have hkeep : ∀ {k : Key md} {x : ConstantInfo md}, envC.find? k = some x → env₂.find? k = some x :=
    fun hk => nativeTable_keep hTbl (Ix.Kernel.Env.find?_cons_of_fresh hfreshR hk)
  intro n cv mI rP rules hf hn0
  have hR := nativeTable_rec hTbl hf
  rw [Ix.Kernel.Env.find?_cons] at hR
  split at hR
  · obtain ⟨-, -, -, hrules⟩ := ConstantInfo.recInfo.inj (Option.some.inj hR)
    subst hrules
    -- each rule: the constructor's verdict at the constructors' environment
    have hrule : ∀ r ∈ Ix.Kernel.sumRules envC.find? cvRa.name p.nP p.majorIdx p.rulePrefix
        cvRa.type ctorsA rhss, ∃ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA ∧
          r.ctor = cA.1.name ∧
          r.k = Ix.Kernel.recRuleKOf envC.find? r.ctor := by
      intro r hr
      obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Ix.Kernel.sumRules_getElem? hr
      exact ⟨j, cA, hj, rfl, (Ix.Kernel.sumRules_bits hr).1⟩
    refine ⟨fun r hr => ?_, fun r hr hk => ?_⟩
    · obtain ⟨j, cA, hj, hctor, hk⟩ := hrule r hr
      obtain ⟨hfC, -, -, -⟩ := hF.ctor j cA hj
      rw [hk]
      refine recRuleKOf_ext (cvj := cA.1) (a := p.nP) (b := cA.2) hkeep (by rw [hctor]; exact hfC)
        (fun T us heq => .inl ?_)
      have hres : cA.1.type.constsResolve envC = true :=
        (hF.store.wf _ (Ix.Kernel.Semantics.Env.find?_mem hfC)).2.2.1
      have h2 := constsResolve_getAppFn (constsResolve_piResult hres)
      rw [heq] at h2
      simpa [Ix.Kernel.Expr.constsResolve] using h2
    · obtain ⟨j, cA, hj, hctor, hk'⟩ := hrule r hr
      obtain ⟨hfC, -, -, cbs, es, hres, -⟩ := hF.ctor j cA hj
      rw [hk] at hk'
      obtain ⟨cvj, cnP, T, us, cvT, caps, hcj, hhead, hfT, hK⟩ :=
        Ix.Kernel.recRuleKOf_inv hk'.symm
      rw [hctor, hfC] at hcj
      obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hcj)
      rw [family_of_residual hres] at hhead
      injection hhead with hTe _
      subst hTe
      -- the family's capability record is the former's, at the former's environment
      have hT₁ : env₁.find? p.cvT.name = some (.indInfo cvT caps) := by
        rcases consSumCtors_newSat (Q := fun x => ∃ cv a b, x = .ctorInfo cv a b)
            (fun cv a b => ⟨cv, a, b, rfl⟩) _ _ hfT with h1 | ⟨_, _, _, h1⟩
        · exact h1
        · exact nomatch h1
      rw [henv₁, Ix.Kernel.Env.find?_cons] at hT₁
      split at hT₁
      · obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hT₁)
        obtain ⟨c, hc⟩ := nativeCapsAt_ruleK hK
        have hlen : ctorsA.length ≤ 1 := by
          obtain ⟨hlA, -, -⟩ := id hCtors
          rw [hlA]
          subst hp hp₁
          have hc' : p₀.ctors = [c] := by simpa [InductiveShape.withSort] using hc
          simp [NativeParts.withKinds, hc']
        exact eq_singleton_of_length_le_one (Nat.le_trans sumRules_length_le hlen) hr
      · next hne =>
        exfalso
        apply hne
        obtain ⟨cvT', s', hn', -, hcc, -⟩ := hInd.shape
        show cvTa.name = p.cvT.name
        rw [native_cvT hInd hp, hcc.name_eq, hn']
  · have h1 := consSumCtors_rec hR
    rw [henv₁] at h1
    rw [find?_rec_of_cons h1 (fun _ _ _ _ heq => nomatch heq)] at hn0
    exact nomatch hn0

/-- A modeled recursor's rules carry the K verdict at the members' environment `envB`. -/
def ModeledBits (envB : Env md) (x : ConstantInfo md) : Prop :=
  ∀ cv mI rP rules, x = .recInfo cv mI rP rules → ∀ r ∈ rules,
    ∃ cvj cnP cnF, envB.find? r.ctor = some (.ctorInfo cvj cnP cnF) ∧
      r.k = Ix.Kernel.recRuleKOf envB.find? r.ctor

theorem iotaRulesRunJ_bits {J : Judgements md} {env' envSelf : Env md} {f : Key md → Key md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP : Nat} :
    ∀ {j : Nat} {rs out : List (RecRule md)},
      IotaRulesRunJ J env' envSelf f cvName lps tyA mI rP j rs out →
      ∀ r ∈ out, ∃ cvj cnP cnF, env'.find? r.ctor = some (.ctorInfo cvj cnP cnF) ∧
        r.k = Ix.Kernel.recRuleKOf env'.find? r.ctor
  | _, [], out, h => by
    obtain rfl : out = [] := h
    intro r hr
    exact nomatch hr
  | _, _ :: _, _, h => by
    obtain ⟨r'', rest', hrule, hrest, rfl⟩ := h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨cvj, cnP, cnF, rhsA, hc, -, -, -, -, -, -, -, -, fire, hbits, -⟩ := hrule
      subst hbits
      exact ⟨cvj, cnP, cnF, hc, rfl⟩
    · exact iotaRulesRunJ_bits hrest r hr

theorem indRecsFoldRunJ_bits {J : Judgements md} {blockNames : List (Key md)}
    {envBase envSelf : Env md} :
    ∀ {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))} {acc out : Env md},
      IndRecsFoldRunJ J blockNames envBase envSelf acc checked out →
      NewSat acc out (ModeledBits envBase)
  | [], acc, out, h => by
    obtain rfl : out = acc := h
    exact NewSat.refl _ _
  | _ :: _, _, _, h => by
    obtain ⟨rules', hrules, h'⟩ := h
    refine (NewSat.cons ?_).trans (indRecsFoldRunJ_bits h')
    intro cv mI rP rules heq r hr
    obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj heq
    exact iotaRulesRunJ_bits hrules r hr

/-- **A modeled step's recursors**: their rules' K bits are the verdict at the step's end (the
single-rule fact is not claimed: a modeled recursor carries a model companion). -/
theorem modeled_recK_new {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (hrun : DeclIndRunJ J env block env₂) :
    ∀ n cv mI rP rules, env₂.find? n = some (.recInfo cv mI rP rules) → env.find? n = none →
      (∀ r ∈ rules, r.k = Ix.Kernel.recRuleKOf env₂.find? r.ctor) ∧
      (¬ HasModel env₂ n → ∀ r ∈ rules, r.k = true → rules = [r]) := by
  intro n cv mI rP rules hf hn0
  refine ⟨?_, fun hm => absurd (declIndRunJ_hasModel hrun hf hn0) hm⟩
  obtain ⟨-, envM, hmem, hrecs⟩ := hrun
  rcases hrecs with ⟨-, rfl⟩ | ⟨-, -, envSelf, checked, hprov, hfold⟩
  · rw [indMembersRunJ_rec hmem hf] at hn0
    exact nomatch hn0
  · have hextM : ∀ {k : Key md} {x : ConstantInfo md}, envM.find? k = some x → env₂.find? k = some x :=
      (indRecsFoldRunJ_envExt hprov hfold (fun _ => rfl) (Ix.Kernel.EnvExt.refl _)).find
    have hnM : envM.find? n = none := by
      cases hM : envM.find? n with
      | none => rfl
      | some c =>
        have h2 := hextM hM
        rw [hf] at h2
        obtain rfl := Option.some.inj h2
        rw [indMembersRunJ_rec hmem hM] at hn0
        exact nomatch hn0
    rcases indRecsFoldRunJ_bits hfold _ _ hf with h1 | h1
    · rw [h1] at hnM
      exact nomatch hnM
    · intro r hr
      obtain ⟨cvj, cnP, cnF, hc, hk⟩ := h1 cv mI rP rules rfl r hr
      rw [hk]
      refine recRuleKOf_ext hextM hc (fun T us _ => .inr ?_)
      intro x hgT hfT
      rcases indRecsFoldRunJ_newSat (Q := NotInd) (fun _ _ _ _ _ _ heq => nomatch heq) hfold _ _ hgT
        with h2 | h2
      · rw [h2] at hfT
        exact nomatch hfT
      · exact h2

/-- The K verdict of a pinned rule reads only the block's own constants. -/
def kStableb (F : Env md) (ctor : Key md) : Bool :=
  match F.find? ctor with
  | some (.ctorInfo cvj _ _) =>
    match (cvj.type.piResult).getAppFn with
    | .const T _ => (F.find? T).isSome
    | _ => true
  | _ => false

theorem kStableb_inv {F : Env md} {ctor : Key md} (h : kStableb F ctor = true) :
    ∃ cvj a b, F.find? ctor = some (.ctorInfo cvj a b) ∧
      ∀ T us, (cvj.type.piResult).getAppFn = .const T us → (F.find? T).isSome = true := by
  unfold kStableb at h
  split at h
  · next cvj a b hf =>
    refine ⟨cvj, a, b, hf, fun T us heq => ?_⟩
    rw [heq] at h
    exact h
  · exact nomatch h

/-- A pinned block's rules: the K bit is the block's verdict, read off its own constants, and
a rule with the K bit is its recursor's only rule. -/
def basisKb {md : Ix.Kernel.Mode} (kind : BasisKind) : Bool :=
  (kind.declsA (md := md)).all fun c => match c with
    | .recInfo _ _ _ rules => rules.all fun r =>
        (r.k == Ix.Kernel.recRuleKOf (Env.find? ⟨(kind.declsA (md := md)).reverse⟩) r.ctor) &&
        kStableb ⟨(kind.declsA (md := md)).reverse⟩ r.ctor && (!r.k || rules.length == 1)
    | _ => true

theorem basis_K (kind : BasisKind) : basisKb (md := md) kind = true := by
  cases kind <;> (cases md <;> decide +kernel)

theorem basis_recK_new {env env₂ : Env md} {kind : BasisKind}
    (hrun : DeclBasisRun env kind env₂) :
    ∀ n cv mI rP rules, env₂.find? n = some (.recInfo cv mI rP rules) → env.find? n = none →
      (∀ r ∈ rules, r.k = Ix.Kernel.recRuleKOf env₂.find? r.ctor) ∧
      (¬ HasModel env₂ n → ∀ r ∈ rules, r.k = true → rules = [r]) := by
  obtain ⟨-, hinst⟩ := hrun
  obtain ⟨rfl, -⟩ := basisInstallRun_eq hinst
  intro n cv mI rP rules hf hn0
  have hpre : ∀ {k : Key md} {x : ConstantInfo md},
      Env.find? ⟨(kind.declsA (md := md)).reverse⟩ k = some x →
      Env.find? ⟨kind.declsA.reverse ++ env.consts⟩ k = some x := by
    intro k x hk
    rw [find?_prefix, hk]
    rfl
  rw [find?_prefix] at hf
  cases hb : Env.find? ⟨(kind.declsA (md := md)).reverse⟩ n with
  | none =>
    rw [hb, Option.none_or] at hf
    rw [hf] at hn0
    exact nomatch hn0
  | some c =>
    rw [hb, Option.some_or] at hf
    obtain rfl := Option.some.inj hf
    have hmem : ConstantInfo.recInfo cv mI rP rules ∈ kind.declsA :=
      List.mem_reverse.mp (Ix.Kernel.Semantics.Env.find?_mem hb)
    have hall : (rules.all fun r =>
        (r.k == Ix.Kernel.recRuleKOf (Env.find? ⟨(kind.declsA (md := md)).reverse⟩) r.ctor) &&
        kStableb ⟨(kind.declsA (md := md)).reverse⟩ r.ctor && (!r.k || rules.length == 1)) = true :=
      List.all_eq_true.mp (basis_K (md := md) kind) _ hmem
    have hr' : ∀ r ∈ rules,
        r.k = Ix.Kernel.recRuleKOf (Env.find? ⟨(kind.declsA (md := md)).reverse⟩) r.ctor ∧
        kStableb ⟨(kind.declsA (md := md)).reverse⟩ r.ctor = true ∧
        (r.k = true → rules.length = 1) := by
      intro r hr
      have := List.all_eq_true.mp hall r hr
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at this
      obtain ⟨⟨h1, h2⟩, h3⟩ := this
      refine ⟨h1, h2, fun hk => ?_⟩
      rcases h3 with h3 | h3
      · rw [hk] at h3
        exact nomatch h3
      · exact h3
    refine ⟨fun r hr => ?_, fun _ r hr hk => ?_⟩
    · obtain ⟨h1, h2, -⟩ := hr' r hr
      obtain ⟨cvj, a, b, hc, hT⟩ := kStableb_inv h2
      rw [h1]
      exact recRuleKOf_ext hpre hc (fun T us heq => .inl (hT T us heq))
    · exact eq_singleton_of_length_le_one (Nat.le_of_eq ((hr' r hr).2.2 hk)) hr

/-- **One declaration step keeps the K facts**, over the derivation package. -/
theorem recK_declRunJ {env env₂ : Env md} {d : Declaration md} (h : StoreInv env) (hK : RecK env)
    (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) : RecK env₂ := by
  have hext := declRunJ_envExt_routes hrun
  have hfr : ∀ e : Env md, JudgeFrames rulesJ e := fun e => judgeFrames_rulesJ e
  cases d with
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
    exact recK_step_noRec h hK hext.find (NewSat.cons (fun _ _ _ _ heq => nomatch heq))
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hrun
    exact recK_step_noRec h hK hext.find (NewSat.cons (fun _ _ _ _ heq => nomatch heq))
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl⟩ := hrun
    exact recK_step_noRec h hK hext.find (NewSat.cons (fun _ _ _ _ heq => nomatch heq))
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact hK
    · exact recK_step_noRec h hK hext.find (NewSat.cons (fun _ _ _ _ heq => nomatch heq))
    · exact hK
  | basisDecl kind => exact recK_step h hK hext.find (basis_recK_new hrun)
  | indDecl block nP =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact recK_step h hK hext.find (basis_recK_new hrun)
    · rcases hrun with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩
      · refine recK_step h hK hext.find (fun n cv mI rP rules hf hn => ?_)
        obtain ⟨h1, h2⟩ := native_recK_new hfr (nativeRecog_of hdp) h hN n cv mI rP rules hf hn
        exact ⟨h1, fun _ => h2⟩
      · exact recK_step h hK hext.find (modeled_recK_new hM)
      · exact recK_step_noRec h hK hext.find
          (nativeNoRec_newSat (fun _ _ _ _ _ _ heq => nomatch heq)
            (fun _ _ _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq) hN)
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact recK_step h hK hext.find (basis_recK_new hrun)
    · subst hrun
      exact hK

/-- **Along a run, the K facts hold**, from an environment keeping them and the store invariant. -/
theorem recK_declsRunJ {env env' : Env md} {ds : List (Declaration md)}
    (hds : DeclsRunJ rulesJ (IndRoutesJ rulesJ) env ds env') :
    StoreInv env → RecK env → RecK env' := by
  induction hds with
  | nil => exact fun _ hK => hK
  | cons hd _ ih =>
    intro h hK
    have hfr : ∀ e : Env md, JudgeFrames rulesJ e := fun e => judgeFrames_rulesJ e
    exact ih (storeInv_declRunJ hfr (fun hI => storeInv_indRoutesJ hfr h hI) h hd)
      (recK_declRunJ h hK hd)


/-! ## The native table, read -/

/-- **What the table stage stores**: nothing, or, at a one-constructor index-free block, the
table at the generator's bodies and guards. -/
theorem nativeTable_cases {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {X X₂ : Env md}
    (h : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss X = .ok X₂) :
    X₂ = X ∨ ∃ cA sorts bodies, ctorsA = [cA] ∧ sortss = [sorts] ∧ p.nIdx = 0 ∧
      Ix.Kernel.structProjBodies p.cvT.name p.nP cA.2 cA.1.type = some bodies ∧
      X₂ = ⟨.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort, bodies,
        Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩ :: X.consts⟩ := by
  unfold Ix.Kernel.checkNativeTable at h
  split at h
  · next cA sorts =>
    split at h
    · next hI =>
      obtain ⟨bodies, hb, -, -, -, rfl⟩ := Ix.Kernel.checkStructProjTable_inv h
      exact .inr ⟨cA, sorts, bodies, rfl, rfl, by simpa using hI, hb, rfl⟩
    · exact .inl (Except.ok.inj h).symm
  · exact .inl (Except.ok.inj h).symm

/-- At a one-constructor index-free block the table is stored. -/
theorem nativeTable_struct {p : NativeParts md} {cA : ConstantVal md × Nat} {sorts : List Level}
    {X X₂ : Env md} (hI : p.nIdx = 0)
    (h : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p [cA] [sorts] X = .ok X₂) :
    ∃ bodies, X₂ = ⟨.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort,
      bodies, Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩ :: X.consts⟩ := by
  unfold Ix.Kernel.checkNativeTable at h
  simp only [hI, beq_self_eq_true, if_true] at h
  obtain ⟨bodies, -, -, -, -, rfl⟩ := Ix.Kernel.checkStructProjTable_inv h
  exact ⟨bodies, rfl⟩

/-- A table at the front answers every slot below its field count. -/
theorem towerSlotsAll_table {X : Env md} {tbl : ProjTable md} :
    Ix.Kernel.towerSlotsAll ⟨.projInfo tbl :: X.consts⟩ tbl.structName tbl.numFields = true := by
  unfold Ix.Kernel.towerSlotsAll Ix.Kernel.Env.findProj?
  rw [Ix.Kernel.Env.find?_cons,
    if_pos (show (ConstantInfo.projInfo tbl).name = Ix.Kernel.projTableName tbl.structName from rfl)]
  simp only [List.all_eq_true, List.mem_range]
  intro j hj
  simp [hj]

/-! ## η families have their towers -/

/-- **A stored η-capable family has a table entry at each of its `etaFields` slots.** -/
def EtaTowers (env : Env md) : Prop :=
  ∀ T cvT caps, env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    Ix.Kernel.towerSlotsAll env T caps.etaFields = true

theorem EtaTowers.empty : EtaTowers (md := md) Env.empty := by
  intro T cvT caps h
  simp [Env.find?, Env.empty] at h

theorem towerSlotsAll_ext {env env₂ : Env md} (hext : EnvExt env env₂) {T : Key md}
    {cvT : ConstantVal md} {caps : IndCaps md} (hf : env.find? T = some (.indInfo cvT caps))
    (k : Nat) : Ix.Kernel.towerSlotsAll env₂ T k = Ix.Kernel.towerSlotsAll env T k := by
  unfold Ix.Kernel.towerSlotsAll Ix.Kernel.Env.findProj?
  rw [hext.tables hf]

theorem etaTowers_step {env env₂ : Env md} (hext : EnvExt env env₂) (h : EtaTowers env)
    (hnew : ∀ T cvT caps, env₂.find? T = some (.indInfo cvT caps) → env.find? T = none →
      caps.eta = true → Ix.Kernel.towerSlotsAll env₂ T caps.etaFields = true) :
    EtaTowers env₂ := by
  intro T cvT caps hf he
  cases hold : env.find? T with
  | none => exact hnew T cvT caps hf hold he
  | some c =>
    have h2 := hext.find hold
    rw [hf] at h2
    obtain rfl := Option.some.inj h2
    rw [towerSlotsAll_ext hext hold]
    exact h T cvT caps hold he

/-- No η-capable family with a field. -/
def TowerFree (x : ConstantInfo md) : Prop :=
  ∀ cv caps, x = .indInfo cv caps → caps.eta = true → caps.etaFields = 0

theorem etaTowers_step_noEta {env env₂ : Env md} (hext : EnvExt env env₂) (h : EtaTowers env)
    (hno : NewSat env env₂ TowerFree) : EtaTowers env₂ := by
  refine etaTowers_step hext h ?_
  intro T cvT caps hf hn he
  rcases hno _ _ hf with h' | h'
  · rw [h'] at hn
    exact nomatch hn
  · rw [h' cvT caps rfl he]
    simp [Ix.Kernel.towerSlotsAll]

/-- A pinned block's η family has no field. -/
def basisTowerFreeb {md : Ix.Kernel.Mode} (kind : BasisKind) : Bool :=
  (kind.declsA (md := md)).all fun c => match c with
    | .indInfo _ caps => !caps.eta || caps.etaFields == 0
    | _ => true

theorem basis_towerFree (kind : BasisKind) : basisTowerFreeb (md := md) kind = true := by
  cases kind <;> (cases md <;> decide +kernel)

theorem basis_newSat_noEta {env env₂ : Env md} {kind : BasisKind}
    (hrun : DeclBasisRun env kind env₂) : NewSat env env₂ TowerFree := by
  refine basis_newSat (fun c hc cv caps heq he => ?_) hrun
  have h := List.all_eq_true.mp (basis_towerFree (md := md) kind) c hc
  subst heq
  simp [he] at h
  exact h

/-- The η capability is a one-constructor index-free block's. -/
theorem nativeCapsAt_eta {p : InductiveShape md} {isRec : Bool}
    (h : (Ix.Kernel.nativeCapsAt p isRec).eta = true) :
    ∃ c, p.ctors = [c] ∧ p.nIdx = 0 ∧ (Ix.Kernel.nativeCapsAt p isRec).etaFields = c.2 := by
  unfold Ix.Kernel.nativeCapsAt at h ⊢
  split at h
  · next c hc =>
    rw [hc]
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨c, rfl, h.1.1, rfl⟩
  · exact nomatch h

/-- **The native routes' η family has its table**: the only new family is the former, and at an
η-capable former the table stage stores the table at the constructor's field count. -/
theorem nativeFormer_towers {J : Judgements md} {env env₁ X env₂ : Env md}
    {p₀ p : NativeParts md} {isRec : Bool} {cvTa : ConstantVal md} {p₁ : InductiveShape md}
    {kinds : List (List RecFieldKind)} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)}
    (hInd : SumIndRunJ J env p₀.toInductiveShape (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
      env₁ cvTa p₁)
    (hp : p = (p₀.complete p₁).withKinds kinds)
    (hCtors : SumCtorsRunJ J env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort
      p.isProp p.large cvTa p.ctors ctorsA sortss)
    (hX : NewSat env₁ X (fun x => ∀ cv caps, x ≠ .indInfo cv caps))
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss X = .ok env₂) :
    ∀ T cvT caps, env₂.find? T = some (.indInfo cvT caps) → env.find? T = none →
      caps.eta = true → Ix.Kernel.towerSlotsAll env₂ T caps.etaFields = true := by
  obtain ⟨_, s, _, _, _, hp₁, henv₁, _, _⟩ := hInd.shape
  intro T cvT caps hf hn he
  -- the family is the former
  have hT₁ : env₁.find? T = some (.indInfo cvT caps) := by
    rcases (hX.trans (nativeTable_newSat (Q := fun x => ∀ cv caps, x ≠ .indInfo cv caps)
        (fun _ _ _ heq => nomatch heq) hTbl)) _ _ hf with h1 | h1
    · exact h1
    · exact absurd rfl (h1 cvT caps)
  rw [henv₁, Ix.Kernel.Env.find?_cons] at hT₁
  split at hT₁
  · next hname =>
    obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hT₁)
    obtain ⟨c, hc, hI, hF⟩ := nativeCapsAt_eta he
    rw [hF]
    have hT : T = p.cvT.name := by
      rw [← hname, native_cvT hInd hp]
      obtain ⟨cvT', s', hn', -, hcc, -⟩ := hInd.shape
      show cvTa.name = p₀.cvT.name
      rw [hcc.name_eq, hn']
    subst hT
    subst hp hp₁
    have hc' : p₀.ctors = [c] := by simpa [InductiveShape.withSort] using hc
    have hI' : p₀.nIdx = 0 := by simpa [InductiveShape.withSort] using hI
    obtain ⟨hlA, hlS, hall⟩ := id hCtors
    have hpc : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).ctors = [c] := by
      simp [NativeParts.withKinds, hc']
    rw [hpc] at hlA hlS
    obtain ⟨cA, rfl⟩ : ∃ cA, ctorsA = [cA] := by
      match ctorsA, hlA with
      | [cA], _ => exact ⟨cA, rfl⟩
      | [], h => simp at h
      | _ :: _ :: _, h => simp at h
    obtain ⟨sorts, rfl⟩ : ∃ sorts, sortss = [sorts] := by
      match sortss, hlS with
      | [sorts], _ => exact ⟨sorts, rfl⟩
      | [], h => simp at h
      | _ :: _ :: _, h => simp at h
    obtain ⟨hnF, -⟩ := hall 0 c cA (by rw [hpc]; rfl) rfl
    have hI'' : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).nIdx = 0 := by
      simp [NativeParts.withKinds, hI']
    obtain ⟨bodies, rfl⟩ := nativeTable_struct hI'' hTbl
    rw [← hnF]
    exact towerSlotsAll_table
  · rw [hT₁] at hn
    exact nomatch hn

/-- **One declaration step keeps the η towers**, over the derivation package. -/
theorem etaTowers_declRunJ {env env₂ : Env md} {d : Declaration md} (h : EtaTowers env)
    (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) : EtaTowers env₂ := by
  have hext := declRunJ_envExt_routes hrun
  cases d with
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
    exact etaTowers_step_noEta hext h (NewSat.cons (fun _ _ heq => nomatch heq))
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hrun
    exact etaTowers_step_noEta hext h (NewSat.cons (fun _ _ heq => nomatch heq))
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl⟩ := hrun
    exact etaTowers_step_noEta hext h (NewSat.cons (fun _ _ heq => nomatch heq))
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact h
    · exact etaTowers_step_noEta hext h (NewSat.cons (fun _ _ heq => nomatch heq))
    · exact h
  | basisDecl kind => exact etaTowers_step_noEta hext h (basis_newSat_noEta hrun)
  | indDecl block nP =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact etaTowers_step_noEta hext h (basis_newSat_noEta hrun)
    · rcases hrun with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩
      · refine etaTowers_step hext h ?_
        obtain ⟨-, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, -, -, -, hInd, hp,
          hCtors, -, -, -, -, -, -, -, -, -, hTbl⟩ := hN
        exact nativeFormer_towers hInd hp hCtors
          ((consSumCtors_newSat (fun _ _ _ _ _ heq => nomatch heq)).trans
            (NewSat.cons (c := .recInfo _ _ _ _) (fun _ _ heq => nomatch heq))) hTbl
      · exact etaTowers_step_noEta hext h
          (modeled_newSat (fun _ _ _ heq he => by
              obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj heq
              simp at he)
            (fun _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ _ heq => nomatch heq) hM)
      · refine etaTowers_step hext h ?_
        obtain ⟨-, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, hp, hCtors, -,
          -, -, -, -, hTbl⟩ := hN
        exact nativeFormer_towers hInd hp hCtors
          (consSumCtors_newSat (fun _ _ _ _ _ heq => nomatch heq)) hTbl
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact etaTowers_step_noEta hext h (basis_newSat_noEta hrun)
    · subst hrun
      exact h

/-- **Along a run, every η family has its towers.** -/
theorem etaTowers_declsRunJ {env env' : Env md} {ds : List (Declaration md)}
    (hds : DeclsRunJ rulesJ (IndRoutesJ rulesJ) env ds env') : EtaTowers env → EtaTowers env' := by
  induction hds with
  | nil => exact id
  | cons hd _ ih => exact fun h => ih (etaTowers_declRunJ h hd)


/-! ## Projection tables are the generator's -/

/-- **Every stored projection table is the generator's for its stored constructor**: the bodies
are `structProjBodies` at the constructor's type, and the guards are `structProjGuards` at that
type and some field sorts, one per field. -/
def TableBodies (env : Env md) : Prop :=
  ∀ n tbl, env.find? n = some (.projInfo tbl) →
    ∃ cvC, env.find? tbl.ctor = some (.ctorInfo cvC tbl.numParams tbl.numFields) ∧
      Ix.Kernel.structProjBodies tbl.structName tbl.numParams tbl.numFields cvC.type
        = some tbl.bodies ∧
      ∃ sorts : List Level, sorts.length = tbl.numFields ∧
        tbl.guards = Ix.Kernel.structProjGuards cvC.type tbl.numParams tbl.numFields sorts

theorem TableBodies.empty : TableBodies (md := md) Env.empty := by
  intro n tbl h
  simp [Env.find?, Env.empty] at h

theorem tableBodies_step {env env₂ : Env md}
    (hfind : ∀ {k : Key md} {x : ConstantInfo md}, env.find? k = some x → env₂.find? k = some x)
    (h : TableBodies env)
    (hnew : ∀ n tbl, env₂.find? n = some (.projInfo tbl) → env.find? n = none →
      ∃ cvC, env₂.find? tbl.ctor = some (.ctorInfo cvC tbl.numParams tbl.numFields) ∧
        Ix.Kernel.structProjBodies tbl.structName tbl.numParams tbl.numFields cvC.type
          = some tbl.bodies ∧
        ∃ sorts : List Level, sorts.length = tbl.numFields ∧
          tbl.guards = Ix.Kernel.structProjGuards cvC.type tbl.numParams tbl.numFields sorts) :
    TableBodies env₂ := by
  intro n tbl hf
  cases hold : env.find? n with
  | none => exact hnew n tbl hf hold
  | some c =>
    have h2 := hfind hold
    rw [hf] at h2
    obtain rfl := Option.some.inj h2
    obtain ⟨cvC, hc, hb, hg⟩ := h n tbl hold
    exact ⟨cvC, hfind hc, hb, hg⟩

/-- Not a projection table. -/
def NotProj (x : ConstantInfo md) : Prop := ∀ t, x ≠ .projInfo t

theorem tableBodies_step_noProj {env env₂ : Env md}
    (hfind : ∀ {k : Key md} {x : ConstantInfo md}, env.find? k = some x → env₂.find? k = some x)
    (h : TableBodies env) (hno : NewSat env env₂ NotProj) : TableBodies env₂ := by
  refine tableBodies_step hfind h ?_
  intro n tbl hf hn
  rcases hno _ _ hf with h' | h'
  · rw [h'] at hn
    exact nomatch hn
  · exact absurd rfl (h' tbl)

theorem basis_newSat_noProj {env env₂ : Env md} {kind : BasisKind}
    (hrun : DeclBasisRun env kind env₂) : NewSat env env₂ NotProj := by
  refine basis_newSat (fun c hc t heq => ?_) hrun
  have hr : keyIsRole c.name = true := List.all_eq_true.mp (basis_names_role (md := md) kind) c hc
  subst heq
  simp [keyIsRole, ConstantInfo.name, ConstantInfo.toConstantVal, Ix.Kernel.projTableName,
    Ix.Kernel.auxKey] at hr

/-- **The native routes' table is the generator's** for the block's constructor. -/
theorem nativeTable_bodies {J : Judgements md} {envO env₁ X env₂ : Env md} {p : NativeParts md}
    {cvTa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)} {sortss : List (List Level)}
    (hCtors : SumCtorsRunJ J env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort
      p.isProp p.large cvTa p.ctors ctorsA sortss)
    (hCfind : ∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
      X.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2))
    (hX : NewSat envO X NotProj)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss X = .ok env₂) :
    ∀ n tbl, env₂.find? n = some (.projInfo tbl) → envO.find? n = none →
      ∃ cvC, env₂.find? tbl.ctor = some (.ctorInfo cvC tbl.numParams tbl.numFields) ∧
        Ix.Kernel.structProjBodies tbl.structName tbl.numParams tbl.numFields cvC.type
          = some tbl.bodies ∧
        ∃ sorts : List Level, sorts.length = tbl.numFields ∧
          tbl.guards = Ix.Kernel.structProjGuards cvC.type tbl.numParams tbl.numFields sorts := by
  intro n tbl hf hn
  have hold : ∀ {tbl : ProjTable md}, X.find? n = some (.projInfo tbl) → False := by
    intro tbl hx
    rcases hX _ _ hx with h1 | h1
    · rw [h1] at hn
      exact nomatch hn
    · exact h1 tbl rfl
  rcases nativeTable_cases hTbl with rfl | ⟨cA, sorts, bodies, rfl, rfl, -, hb, rfl⟩
  · exact (hold hf).elim
  · rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · obtain rfl := ConstantInfo.projInfo.inj (Option.some.inj hf)
      obtain ⟨hlA, -, hall⟩ := id hCtors
      obtain ⟨c, hc0⟩ : ∃ c, p.ctors[0]? = some c := by
        cases hpc : p.ctors with
        | nil =>
          rw [hpc] at hlA
          simp at hlA
        | cons c _ => exact ⟨c, rfl⟩
      obtain ⟨hnF, sorts', hs', hCtor⟩ := hall 0 c cA hc0 rfl
      have hss : sorts = sorts' := Option.some.inj hs'
      obtain ⟨-, -, fvsP, crest, tfvs, trest, xFvs, idxArgs, -, -, -, -, -, -, -, hFS⟩ := hCtor
      refine ⟨cA.1, ?_, hb, sorts, ?_, rfl⟩
      · exact nativeTable_keep hTbl (hCfind 0 cA rfl)
      · show sorts.length = cA.2
        rw [hss, hFS.1, hnF]
    · exact (hold hf).elim

/-- **One declaration step keeps the tables the generator's**, over the derivation package. -/
theorem tableBodies_declRunJ {env env₂ : Env md} {d : Declaration md} (hS : StoreInv env)
    (h : TableBodies env)
    (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) : TableBodies env₂ := by
  have hext := declRunJ_envExt_routes hrun
  have hfr : ∀ e : Env md, JudgeFrames rulesJ e := fun e => judgeFrames_rulesJ e
  cases d with
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
    exact tableBodies_step_noProj hext.find h (NewSat.cons (fun _ heq => nomatch heq))
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hrun
    exact tableBodies_step_noProj hext.find h (NewSat.cons (fun _ heq => nomatch heq))
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl⟩ := hrun
    exact tableBodies_step_noProj hext.find h (NewSat.cons (fun _ heq => nomatch heq))
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact h
    · exact tableBodies_step_noProj hext.find h (NewSat.cons (fun _ heq => nomatch heq))
    · exact h
  | basisDecl kind => exact tableBodies_step_noProj hext.find h (basis_newSat_noProj hrun)
  | indDecl block nP =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact tableBodies_step_noProj hext.find h (basis_newSat_noProj hrun)
    · rcases hrun with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩
      · refine tableBodies_step hext.find h ?_
        obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, -, -, -, hInd,
          hp, hCtors, -, -, -, -, -, -, -, hRec, -, hTbl⟩ := hN
        have hF := nativeFront hfr hS (nativeRecog_of hdp) hnd hInd hp hCtors
        obtain ⟨hnR, -, hfR, -⟩ := hRec.recursor
        have hfreshR : (Ix.Kernel.consSumCtors p.nP ctorsA env₁).find? cvRa.name = none := by
          rw [hnR]; exact hfR
        obtain ⟨_, _, _, _, _, _, henv₁, _, _⟩ := hInd.shape
        have hXno : NewSat env ⟨.recInfo cvRa p.majorIdx p.rulePrefix
            (Ix.Kernel.sumRules (Ix.Kernel.consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP
              p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
            :: (Ix.Kernel.consSumCtors p.nP ctorsA env₁).consts⟩ NotProj := by
          subst henv₁
          exact (NewSat.cons (fun _ heq => nomatch heq)).trans
            ((consSumCtors_newSat (fun _ _ _ _ heq => nomatch heq)).trans
              (NewSat.cons (fun _ heq => nomatch heq)))
        exact nativeTable_bodies hCtors
          (fun j cA hj => Ix.Kernel.Env.find?_cons_of_fresh hfreshR (hF.ctor j cA hj).1) hXno hTbl
      · exact tableBodies_step_noProj hext.find h
          (modeled_newSat (fun _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
            (fun _ _ _ _ _ heq => nomatch heq) hM)
      · refine tableBodies_step hext.find h ?_
        obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, hp, hCtors,
          -, -, -, -, -, hTbl⟩ := hN
        have hF := nativeFront hfr hS (nativeRecog_noRec hdp) hnd hInd hp hCtors
        obtain ⟨_, _, _, _, _, _, henv₁, _, _⟩ := hInd.shape
        have hXno : NewSat env (Ix.Kernel.consSumCtors p.nP ctorsA env₁) NotProj := by
          subst henv₁
          exact (NewSat.cons (fun _ heq => nomatch heq)).trans
            (consSumCtors_newSat (fun _ _ _ _ heq => nomatch heq))
        exact nativeTable_bodies hCtors (fun j cA hj => (hF.ctor j cA hj).1) hXno hTbl
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact tableBodies_step_noProj hext.find h (basis_newSat_noProj hrun)
    · subst hrun
      exact h

/-- **Along a run, every stored projection table is the generator's.** -/
theorem tableBodies_declsRunJ {env env' : Env md} {ds : List (Declaration md)}
    (hds : DeclsRunJ rulesJ (IndRoutesJ rulesJ) env ds env') :
    StoreInv env → TableBodies env → TableBodies env' := by
  induction hds with
  | nil => exact fun _ h => h
  | cons hd _ ih =>
    intro hS h
    have hfr : ∀ e : Env md, JudgeFrames rulesJ e := fun e => judgeFrames_rulesJ e
    exact ih (storeInv_declRunJ hfr (fun hI => storeInv_indRoutesJ hfr hS hI) hS hd)
      (tableBodies_declRunJ hS h hd)

end Ix.Kernel.Model
