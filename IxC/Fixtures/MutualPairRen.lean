import IxC.Kernel.Checker
import IxC.Kernel.Inductives.Modeled
import IxC.Kernel.BasisA
import IxC.Kernel.Verify.InferLemmas
import IxC.Kernel.Semantics.Bridge.DeclIndRun
import IxC.Kernel.Model.Fold
import IxC.Kernel.Model.JudgeSound
import IxC.Kernel.Model.IndRenEmbed

/-! # A mutual pair through IxC's executable check, on the renamed route

The smallest mutual block over the basis, with its model advice, checked by IxC's own executable
checker (fuel 16, evaluated by the Lean kernel):

* the block: `A B : Type`, `A.a : A`, `B.b : B`, and the family's recursors
  `A.rec.{u} : (mA : A → Sort u) → (mB : B → Sort u) → mA A.a → mB B.b → (t : A) → mA t` and
  `B.rec.{u}` (eliminating into `mB`), one rule each;
* the advice, installed by the checker's fold from the empty environment after the `Eq` and
  `PUnit` basis blocks: `A._model := PUnit.{1}`, `A.a._model := PUnit.unit`,
  `A.rec._model := fun mA mB ha hb t => PUnit.rec (motive := mA) ha t`, likewise for `B`, and the
  two `iota` theorems by `Eq.refl` (`advRun`);
* the block's modeled check at that environment (`blockRun`), which IxC's bridge turns into the
  kernel's record (`pairRun`).

Both rules fire plain, so the record embeds in the renamed one (`pairRen`, by
`declIndRun_modeled_toRen`), and the variant's model step applies to it at the advice
environment's model (`pair_envOk`): `DeclIndRenRunJ` holds of a concrete family and
`declIndRenJ`'s premises are met there. -/

open Ix.Kernel Ix.Kernel.BasisDSL Ix.Kernel.Semantics Ix.Kernel.Model

universe u

namespace Tests.Ix.Kernel.MutualPairRen

abbrev E := Expr .source

def key (s : String) : Key .source := .id (.str .anonymous s)
def kA : Key .source := key "A"
def kB : Key .source := key "B"
def ka : Key .source := key "A.a"
def kb : Key .source := key "B.b"
def kRA : Key .source := key "A.rec"
def kRB : Key .source := key "B.rec"
def blockNames : List (Key .source) := [kA, kB, ka, kb, kRA, kRB]

/-- The block renaming. -/
def ren (n : Key .source) : Key .source :=
  if blockNames.contains n then auxKey n .model else n

def mdl (k : Key .source) : Key .source := auxKey k .model
def iota0 (k : Key .source) : Key .source := auxKey (mdl k) (.iota 0)

def lvl1 : Level := .succ .zero

/-! ## The block -/

def motA : E := pi "t" (cnst kA) (srt u)
def motB : E := pi "t" (cnst kB) (srt u)

/-- `A.rec`'s type: `(mA) (mB) (ha : mA A.a) (hb : mB B.b) (t : A) → mA t`. -/
def tyRA : E :=
  pi "mA" motA <| pi "mB" motB <| pi "ha" (.app (bv 1) (cnst ka)) <|
  pi "hb" (.app (bv 1) (cnst kb)) <| pi "t" (cnst kA) (.app (bv 4) (bv 0))

/-- `B.rec`'s type: `… (t : B) → mB t`. -/
def tyRB : E :=
  pi "mA" motA <| pi "mB" motB <| pi "ha" (.app (bv 1) (cnst ka)) <|
  pi "hb" (.app (bv 1) (cnst kb)) <| pi "t" (cnst kB) (.app (bv 3) (bv 0))

/-- The four leading λs of a rule. -/
def ruleLams (body : E) : E :=
  lm "mA" motA <| lm "mB" motB <| lm "ha" (.app (bv 1) (cnst ka)) <|
  lm "hb" (.app (bv 1) (cnst kb)) body

def block : List (ConstantInfo .source) :=
  [ .indInfo ⟨kA, [], type1⟩ {},
    .indInfo ⟨kB, [], type1⟩ {},
    .ctorInfo ⟨ka, [], cnst kA⟩ 0 0,
    .ctorInfo ⟨kb, [], cnst kB⟩ 0 0,
    .recInfo ⟨kRA, [uN], tyRA⟩ 4 4 [rule ka 0 (ruleLams (bv 1))],
    .recInfo ⟨kRB, [uN], tyRB⟩ 4 4 [rule kb 0 (ruleLams (bv 0))] ]

/-! ## The model advice -/

def punitOne : E := cnst punitName [lvl1]
def unitOne : E := cnst punitUnitName [lvl1]

/-- A recursor model: `fun mA mB ha hb t => PUnit.rec (motive := m) h t`. -/
def recModel (ty : E) (mot minor : Nat) : E :=
  let tyR := ty.renameConsts ren
  match tyR with
  | .forallE dA (.forallE dB (.forallE dHa (.forallE dHb (.forallE dT _ _) _) _) _) _ =>
    lm "mA" dA <| lm "mB" dB <| lm "ha" dHa <| lm "hb" dHb <| lm "t" dT <|
      ap3 (cnst punitRecName [u, lvl1]) (bv mot) (bv minor) (bv 0)
  | _ => .bvar 0

/-- `iota_0` of a recursor model: `∀ mA mB ha hb, @Eq (m c) (R._model mA mB ha hb c._model) h`. -/
def iotaStmt (kR kc : Key .source) (mot rhs : Nat) : E :=
  let base := ruleLams (.bvar 0)
  match base.renameConsts ren with
  | .lam dA (.lam dB (.lam dHa (.lam dHb _ _) _) _) _ =>
    pi "mA" dA <| pi "mB" dB <| pi "ha" dHa <| pi "hb" dHb <|
      ap3 (cnst eqName [u]) (.app (bv mot) (cnst (mdl kc)))
        (Expr.mkAppN (cnst (mdl kR) [u]) [bv 3, bv 2, bv 1, bv 0, cnst (mdl kc)])
        (bv rhs)
  | _ => .bvar 0

def iotaProof (kc : Key .source) (mot rhs : Nat) : E :=
  match (ruleLams (.bvar 0)).renameConsts ren with
  | .lam dA (.lam dB (.lam dHa (.lam dHb _ _) _) _) _ =>
    lm "mA" dA <| lm "mB" dB <| lm "ha" dHa <| lm "hb" dHb <|
      ap2 (cnst eqReflName [u]) (.app (bv mot) (cnst (mdl kc))) (bv rhs)
  | _ => .bvar 0

def advDecls : List (Declaration .source) :=
  [ .basisDecl .eqK,
    .basisDecl .punitK,
    .defnDecl ⟨mdl kA, [], type1⟩ punitOne (.regular 0),
    .defnDecl ⟨mdl kB, [], type1⟩ punitOne (.regular 0),
    .defnDecl ⟨mdl ka, [], cnst (mdl kA)⟩ unitOne (.regular 0),
    .defnDecl ⟨mdl kb, [], cnst (mdl kB)⟩ unitOne (.regular 0),
    .defnDecl ⟨mdl kRA, [uN], tyRA.renameConsts ren⟩ (recModel tyRA 4 2) (.regular 1),
    .defnDecl ⟨mdl kRB, [uN], tyRB.renameConsts ren⟩ (recModel tyRB 3 1) (.regular 1),
    .thmDecl ⟨iota0 kRA, [uN], iotaStmt kRA ka 3 1⟩ (iotaProof ka 3 1),
    .thmDecl ⟨iota0 kRB, [uN], iotaStmt kRB kb 2 0⟩ (iotaProof kb 2 0) ]

/-- The value of a run, or `d` if it failed. -/
def okOr {ε : Type _} {α : Type _} (r : Except ε α) (d : α) : α :=
  match r with
  | .ok x => x
  | .error _ => d

def advRun : Except (CheckError .source) (Env .source) :=
  checkDeclsPure .verified (fueledOps .verified 16) [] advDecls

def envAdv : Env .source := okOr advRun Env.empty

def blockRun : Except (CheckError .source) (Env .source) :=
  checkModeled (m := CheckM .source) .verified (fueledOps .verified 16) envAdv block

def env₂ : Env .source := okOr blockRun envAdv

theorem ok_okOr {ε : Type _} {α : Type _} {r : Except ε α} {d : α}
    (h : r.toBool = true) : r = .ok (okOr r d) := by
  cases r with
  | ok _ => rfl
  | error _ =>
    have h' : false = true := h
    cases h'

/-! ## The runs, evaluated -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The advice installs** (IxC's fold, evaluated). -/
theorem advRun_ok : advRun.toBool = true := by decide +kernel

theorem advRun_eq : advRun = .ok envAdv := ok_okOr advRun_ok

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The block's modeled check passes** at the advice environment (evaluated). -/
theorem blockRun_ok : blockRun.toBool = true := by decide +kernel

theorem blockRun_eq : blockRun = .ok env₂ := ok_okOr blockRun_ok

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- No stored recursor fires a rule nested (evaluated). -/
theorem env₂_recs_plain : env₂.consts.all (fun ci => match ci with
    | .recInfo _ _ _ rs => rs.all (fun r => match r.fire with
      | .nested _ _ => false
      | _ => true)
    | _ => true) = true := by decide +kernel

/-! ## The records -/

/-- **The kernel's record of the block** (`declIndRun_of`). -/
theorem pairRun : DeclIndRun .verified 16 envAdv block env₂ :=
  declIndRun_of blockRun_eq

theorem pair_noNested : NoNestedRules (block.map (·.name)) env₂ := by
  intro n cv mI rP rules _ hf rl hrl lvls pins hfire
  have hmem := Ix.Kernel.find?_mem hf
  have h1 := List.all_eq_true.mp env₂_recs_plain _ hmem
  simp only at h1
  have h2 := List.all_eq_true.mp h1 rl hrl
  simp [hfire] at h2

/-- **The renamed record holds of the pair**, at the kernel's runs. -/
theorem pairRen : DeclIndRenRunJ (runJ .verified 16) envAdv block env₂ :=
  declIndRun_modeled_toRen pairRun (by
    rintro ⟨cvT, capsT, cvC, nP, nF, h1, -⟩
    have hl := congrArg List.length h1
    simp only [List.length_cons, List.length_nil] at hl
    exact absurd hl (by decide +kernel)) pair_noNested

/-! ## The models -/

/-- The advice environment carries the fold invariant (`foldPM` on the accepted run). -/
theorem envAdv_ok (W : Type u) [SetTheory W] : EnvModelOk W .verified envAdv :=
  foldPM (ev := []) (F := 16) rfl advDecls Env.empty
    ⟨⟨EnvModelM.empty W .verified⟩, EtaFamiliesClosed.empty⟩ advRun_eq

/-- **The variant's model step at the pair**: `declIndStepRenJ` at the kernel's runs extends
the advice environment's model to the block's. -/
theorem pair_envOk (W : Type u) [SetTheory W] : EnvModelOk W .verified env₂ := by
  obtain ⟨⟨mp⟩, hE⟩ := envAdv_ok W
  obtain ⟨hE₂, mp₂, -⟩ :=
    declIndStepRenJ (fun _ => judgeFrames_runJ 16) (fun m => judgeSound_runJ rfl m 16) mp hE
      pairRen
  exact ⟨⟨mp₂⟩, hE₂⟩

end Tests.Ix.Kernel.MutualPairRen
