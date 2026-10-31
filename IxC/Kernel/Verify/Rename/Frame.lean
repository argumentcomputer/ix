module

public import IxC.Kernel.Verify.Rename.Fold

@[expose] public section

/-!
# The frame step: locality from the renaming walk at `f = id` (S1, part 1)

The renaming walk's simulations are stated over any link (`EnvRelG P f L`). At
the identity renaming and the trivial link they are **locality**: a run over
`B` is matched by the run over any `B'` that answers as `B` does at the keys
the run can read (the `P`-good keys, whose constants in `B` are `P`-good)
(`EnvFrame`). `checkDecl_frame` is one declaration, `foldlM_checkDecl_frame` a
list of them: whatever the first run accepts, the second accepts, and the two
environments it installs again answer alike at `P`-good keys.
-/

namespace Ix.Kernel

variable {md : Mode} {P : KeyScope md}

/-! ## The identity renaming -/

theorem Expr.mapKeys_id_fun : (Expr.mapKeys (md := md) (md' := md) fun i => i) = _root_.id :=
  funext Expr.mapKeys_id

theorem Key.map_id_fun : (Key.map (md := md) (md' := md) fun i => i) = _root_.id :=
  funext Key.map_id

@[simp] theorem ConstantVal.mapKeys_id (cv : ConstantVal md) : cv.mapKeys (fun i => i) = cv := by
  cases cv
  simp [ConstantVal.mapKeys]

@[simp] theorem RecRuleFire.mapKeys_id (r : RecRuleFire md) : r.mapKeys (fun i => i) = r := by
  cases r <;> simp [RecRuleFire.mapKeys, Expr.mapKeys_id_fun]

@[simp] theorem RecRule.mapKeys_id (r : RecRule md) : r.mapKeys (fun i => i) = r := by
  cases r
  simp [RecRule.mapKeys]

theorem RecRule.mapKeys_id_fun : (RecRule.mapKeys (md := md) (md' := md) fun i => i) = _root_.id :=
  funext RecRule.mapKeys_id

@[simp] theorem IndCaps.mapKeys_id (c : IndCaps md) : c.mapKeys (fun i => i) = c := by
  cases c
  simp [IndCaps.mapKeys, Key.map_id_fun]

@[simp] theorem ProjTable.mapKeys_id (t : ProjTable md) : t.mapKeys (fun i => i) = t := by
  cases t
  simp [ProjTable.mapKeys, Expr.mapKeys_id_fun]

@[simp] theorem ConstantInfo.mapKeys_id (c : ConstantInfo md) : c.mapKeys (fun i => i) = c := by
  cases c <;> simp [ConstantInfo.mapKeys, RecRule.mapKeys_id_fun]

theorem ConstantInfo.mapKeys_id_fun :
    (ConstantInfo.mapKeys (md := md) (md' := md) fun i => i) = _root_.id :=
  funext ConstantInfo.mapKeys_id

@[simp] theorem Declaration.mapKeys_id (d : Declaration md) : d.mapKeys (fun i => i) = d := by
  cases d <;> simp [Declaration.mapKeys, ConstantInfo.mapKeys_id_fun]

@[simp] theorem Evidence.mapKeys_id (e : Evidence (Key md × Expr md)) :
    e.mapKeys (fun i => i) = e := by
  cases e with
  | defeq => rfl
  | proof kv => obtain ⟨k, v⟩ := kv; simp [Evidence.mapKeys]

theorem Evidence.mapKeys_id_fun :
    (Evidence.mapKeys (md := md) (md' := md) fun i => i) = _root_.id :=
  funext Evidence.mapKeys_id

@[simp] theorem Evidences.mapKeys_id (ev : Evidences md) : ev.mapKeys (fun i => i) = ev := by
  simp [Evidences.mapKeys, Evidence.mapKeys_id_fun]

/-! ## The frame relation -/

/-- **The frame relation** at `P`: `env'` answers as `env` does at `P`-good
keys, and `env`'s constants at `P`-good keys are `P`-good. -/
abbrev EnvFrame (P : KeyScope md) (env env' : Env md) : Prop :=
  EnvRelG P (fun i => i) TrueLink env env'

theorem EnvFrame.mk {env env' : Env md} (hfind : ∀ k : Key md, k.Good P → env'.find? k = env.find? k)
    (hgood : ∀ (k : Key md) (c : ConstantInfo md), k.Good P → env.find? k = some c → c.Good P)
    (habsent : ∀ r : Role, ¬ P.role r → env.find? (roleKey r) = none) (hpre : P.Pre) :
    EnvFrame P env env' where
  inj := fun _ _ _ _ h => h
  find k hk := by
    rw [Key.map_id, hfind k hk]
    cases env.find? k <;> simp
  good := hgood
  absent := habsent
  pre := hpre
  link := trivial

/-- At a `P`-good key, the frame answers as `env` does. -/
theorem EnvFrame.find_eq {env env' : Env md} (h : EnvFrame P env env') {k : Key md}
    (hk : k.Good P) : env'.find? k = env.find? k := by
  have := h.find k hk
  rw [Key.map_id] at this
  rw [this]
  cases env.find? k <;> simp

/-- An environment frames itself. -/
theorem EnvFrame.refl {env : Env md} (hgood : ∀ (k : Key md) (c : ConstantInfo md), k.Good P →
    env.find? k = some c → c.Good P)
    (habsent : ∀ r : Role, ¬ P.role r → env.find? (roleKey r) = none) (hpre : P.Pre) :
    EnvFrame P env env :=
  EnvFrame.mk (fun _ _ => rfl) hgood habsent hpre

/-! ## The frame step -/

/-- **One declaration, framed**: a declaration naming `P`-good keys only, checked
over `B`, is matched by its check over a framing `B'`. -/
theorem checkDecl_frame (mode : CheckMode) (F : Nat) {ev : Evidences md} (hev : ev.Good P)
    {B B' : Env md} (hE : EnvFrame P B B') {d : Declaration md} (hd : d.Good P)
    (hop : d.NoOp ∨ P.All) :
    SimR (EnvFrame P) (checkDecl mode (fueledOps mode F) ev B d)
      (checkDecl mode (fueledOps mode F) ev B' d) := by
  have h := checkDecl_sim mode
    (fueledOps_sim (P := P) (f := fun i => i) (L := TrueLink) mode F) hev hE hd hop
  rwa [Declaration.mapKeys_id, Evidences.mapKeys_id] at h

/-- **A list of declarations, framed.** -/
theorem foldlM_checkDecl_frame (mode : CheckMode) (F : Nat) {ev : Evidences md} (hev : ev.Good P)
    {ds : List (Declaration md)} (hds : ∀ d ∈ ds, d.Good P) (hop : P.All ∨ ∀ d ∈ ds, d.NoOp)
    {B B' : Env md} (hE : EnvFrame P B B') :
    SimR (EnvFrame P) (ds.foldlM (checkDecl mode (fueledOps mode F) ev) B)
      (ds.foldlM (checkDecl mode (fueledOps mode F) ev) B') := by
  have h := checkDeclsPure_simG mode
    (fueledOps_sim (P := P) (f := fun i => i) (L := TrueLink) mode F) hev hds hop hE
  have hmap : ds.map (Declaration.mapKeys fun i => i) = ds := by
    rw [show (Declaration.mapKeys (md := md) (md' := md) fun i => i) = id from
      funext Declaration.mapKeys_id, List.map_id]
  rwa [hmap, Evidences.mapKeys_id] at h

end Ix.Kernel
