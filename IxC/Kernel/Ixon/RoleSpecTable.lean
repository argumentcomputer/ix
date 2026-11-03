module

public import IxC.Kernel.Roles
public import IxC.Kernel.RoleEquations
public import IxC.Kernel.Ixon.RoleTable

/-! # Flattened DAG table representation of `Role.spec` and correspondence proofs

Defines the pure DAG table representation (`SpecUnivTable`, `SpecExprTable`) generated
by `RoleSpecGen` from `Ix.Kernel.Role.spec` and proves (with zero `sorry`) that
reconstructing a `Level` or `Expr .anon` from the DAG table via `evalSpecUniv` and
`evalSpecExpr` under a role-key resolver (such as `RoleTable.keyOf` or `RoleTable.roleKeyOf`)
produces the exact `Ix.Kernel.Role.spec r` (`Spec.anchor`, `Spec.axiom`, `Spec.ops`,
`Spec.eqns`, `Spec.block`). -/

@[expose] public section

namespace Ix.Kernel

/-- The address key bound to role `r` in role table `t`, if `r` is bound in `t`. -/
def RoleTable.keyOf (t : RoleTable) (r : Role) : Option (Key .anon) :=
  (t.addressOf? r).map Key.id

/-- The canonical `.role r` key resolver. -/
def RoleTable.roleKeyOf (r : Role) : Option (Key .anon) :=
  some (.role r)

/-! ## Universe Level DAG Table (`SpecUnivNode`, `SpecUnivTable`) -/

/-- A node in the flattened universe-level specification DAG table. -/
inductive SpecUnivNode where
  | zero
  | succ (u : Nat)
  | max (u v : Nat)
  | imax (u v : Nat)
  | param (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Flattened DAG table of universe level nodes. -/
abbrev SpecUnivTable := List SpecUnivNode

/-- `tbl₁` is a prefix of `tbl₂` (`tbl₂` extends `tbl₁` by appending nodes). -/
abbrev SpecUnivTable.Extends (tbl₁ tbl₂ : SpecUnivTable) : Prop :=
  tbl₁ <+: tbl₂

/-- Find the first index of `p` in `ps`. -/
def paramIdx? : List LevelParam → LevelParam → Option Nat
  | [], _ => none
  | a :: as, p => if p == a then some 0 else (paramIdx? as p).map (· + 1)

theorem paramIdx?_spec {p : LevelParam} (ps : List LevelParam) :
    ∀ {i : Nat}, paramIdx? ps p = some i → ps[i]? = some p := by
  induction ps with
  | nil => intro i h; nomatch h
  | cons a as ih =>
    intro i h
    unfold paramIdx? at h
    cases hpa : p == a with
    | true =>
      rw [hpa, if_pos rfl, Option.some.injEq] at h
      subst h
      exact congrArg some (beq_iff_eq.mp hpa).symm
    | false =>
      rw [hpa, if_neg Bool.false_ne_true] at h
      cases hrec : paramIdx? as p with
      | none => rw [hrec] at h; nomatch h
      | some j =>
        rw [hrec] at h
        injection h with hj
        subst hj
        exact ih hrec

/-- Whether every level parameter in `l` appears in `ps`. -/
def Level.allParamsIn (ps : List LevelParam) : Level → Bool
  | .zero => Bool.true
  | .succ u => u.allParamsIn ps
  | .max u v | .imax u v => u.allParamsIn ps && v.allParamsIn ps
  | .param p => (paramIdx? ps p).isSome

/-- Structural recursion depth of a `Level`, bounding the fuel needed by `evalSpecUniv`. -/
def Level.dagDepth : Level → Nat
  | .zero | .param _ => 1
  | .succ u => u.dagDepth + 1
  | .max u v | .imax u v => Nat.max u.dagDepth v.dagDepth + 1

/-- Compile a `Level` into a `SpecUnivTable` under parameter list `ps`, returning
`(rootIdx, updatedTable)`. -/
def buildSpecUniv (ps : List LevelParam) : Level → SpecUnivTable → Option (Nat × SpecUnivTable)
  | .zero, tbl => some (tbl.length, tbl ++ [.zero])
  | .succ u, tbl =>
    match buildSpecUniv ps u tbl with
    | some (uIdx, tbl₁) => some (tbl₁.length, tbl₁ ++ [.succ uIdx])
    | none => none
  | .max u v, tbl =>
    match buildSpecUniv ps u tbl with
    | some (uIdx, tbl₁) =>
      match buildSpecUniv ps v tbl₁ with
      | some (vIdx, tbl₂) => some (tbl₂.length, tbl₂ ++ [.max uIdx vIdx])
      | none => none
    | none => none
  | .imax u v, tbl =>
    match buildSpecUniv ps u tbl with
    | some (uIdx, tbl₁) =>
      match buildSpecUniv ps v tbl₁ with
      | some (vIdx, tbl₂) => some (tbl₂.length, tbl₂ ++ [.imax uIdx vIdx])
      | none => none
    | none => none
  | .param p, tbl =>
    match paramIdx? ps p with
    | some i => some (tbl.length, tbl ++ [.param i])
    | none => none

/-- Reconstruct a `Level` from `tbl : SpecUnivTable` at index `idx` with `fuel`. -/
def evalSpecUniv (ps : List LevelParam) (tbl : SpecUnivTable) : Nat → Nat → Option Level
  | 0, _ => none
  | fuel + 1, idx =>
    match tbl[idx]? with
    | some .zero => some .zero
    | some (.succ u) =>
      match evalSpecUniv ps tbl fuel u with
      | some lu => some (.succ lu)
      | none => none
    | some (.max u v) =>
      match evalSpecUniv ps tbl fuel u, evalSpecUniv ps tbl fuel v with
      | some lu, some lv => some (.max lu lv)
      | _, _ => none
    | some (.imax u v) =>
      match evalSpecUniv ps tbl fuel u, evalSpecUniv ps tbl fuel v with
      | some lu, some lv => some (.imax lu lv)
      | _, _ => none
    | some (.param i) =>
      match ps[i]? with
      | some p => some (.param p)
      | none => none
    | none => none

theorem evalSpecUniv_idx_lt {ps : List LevelParam} {tbl : SpecUnivTable} {fuel idx : Nat} {l : Level}
    (h : evalSpecUniv ps tbl fuel idx = some l) : idx < tbl.length := by
  cases fuel with
  | zero => simp [evalSpecUniv] at h
  | succ f =>
    unfold evalSpecUniv at h
    rcases Nat.lt_or_ge idx tbl.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at h
      simp at h

theorem evalSpecUniv_mono {ps : List LevelParam} {tbl₁ tbl₂ : SpecUnivTable}
    (hext : tbl₁ <+: tbl₂) :
    ∀ {fuel₁ fuel₂ idx : Nat} {l : Level},
      fuel₁ ≤ fuel₂ →
      evalSpecUniv ps tbl₁ fuel₁ idx = some l →
      evalSpecUniv ps tbl₂ fuel₂ idx = some l
  | 0, _, _, _, _, h => by simp [evalSpecUniv] at h
  | _ + 1, 0, _, _, hle, _ => by omega
  | f₁ + 1, f₂ + 1, idx, l, hle, h => by
    have hlt : idx < tbl₁.length := evalSpecUniv_idx_lt h
    obtain ⟨suf, rfl⟩ := hext
    have hget : (tbl₁ ++ suf)[idx]? = tbl₁[idx]? := List.getElem?_append_left hlt
    have hle' : f₁ ≤ f₂ := by omega
    unfold evalSpecUniv at h ⊢
    rw [hget]
    cases hnode : tbl₁[idx]? with
    | none => rw [hnode] at h; simp at h
    | some node =>
      rw [hnode] at h
      cases node with
      | zero => exact h
      | param i => exact h
      | succ u =>
        dsimp only at h ⊢
        cases hu : evalSpecUniv ps tbl₁ f₁ u with
        | none => rw [hu] at h; simp at h
        | some lu =>
          rw [hu] at h
          rw [evalSpecUniv_mono ⟨suf, rfl⟩ hle' hu]
          exact h
      | max u v =>
        dsimp only at h ⊢
        cases hu : evalSpecUniv ps tbl₁ f₁ u with
        | none => rw [hu] at h; simp at h
        | some lu =>
          cases hv : evalSpecUniv ps tbl₁ f₁ v with
          | none => rw [hu, hv] at h; simp at h
          | some lv =>
            rw [hu, hv] at h
            rw [evalSpecUniv_mono ⟨suf, rfl⟩ hle' hu, evalSpecUniv_mono ⟨suf, rfl⟩ hle' hv]
            exact h
      | imax u v =>
        dsimp only at h ⊢
        cases hu : evalSpecUniv ps tbl₁ f₁ u with
        | none => rw [hu] at h; simp at h
        | some lu =>
          cases hv : evalSpecUniv ps tbl₁ f₁ v with
          | none => rw [hu, hv] at h; simp at h
          | some lv =>
            rw [hu, hv] at h
            rw [evalSpecUniv_mono ⟨suf, rfl⟩ hle' hu, evalSpecUniv_mono ⟨suf, rfl⟩ hle' hv]
            exact h

/-- **Universe DAG Table Soundness**: Every `Level` whose parameters belong to `ps`
compiles via `buildSpecUniv` into a table extension that `evalSpecUniv` evaluates
back to the exact `Level`. -/
theorem buildSpecUniv_spec (ps : List LevelParam) :
    ∀ (l : Level) (tbl : SpecUnivTable),
      l.allParamsIn ps = Bool.true →
      ∃ idx tbl', buildSpecUniv ps l tbl = some (idx, tbl') ∧
        tbl <+: tbl' ∧
        evalSpecUniv ps tbl' l.dagDepth idx = some l
  | .zero, tbl, _ => by
    refine ⟨tbl.length, tbl ++ [.zero], rfl, ⟨[.zero], rfl⟩, ?_⟩
    simp [Level.dagDepth, evalSpecUniv]
  | .param p, tbl, hwf => by
    unfold Level.allParamsIn at hwf
    cases hi : paramIdx? ps p with
    | none => rw [hi] at hwf; nomatch hwf
    | some i =>
      have hget := paramIdx?_spec ps hi
      refine ⟨tbl.length, tbl ++ [.param i], ?_, ⟨[.param i], rfl⟩, ?_⟩
      · simp [buildSpecUniv, hi]
      · simp [Level.dagDepth, evalSpecUniv, hget]
  | .succ u, tbl, hwf => by
    obtain ⟨uIdx, tbl₁, hbu, hext₁, hevu⟩ := buildSpecUniv_spec ps u tbl hwf
    refine ⟨tbl₁.length, tbl₁ ++ [.succ uIdx], ?_, hext₁.trans ⟨[.succ uIdx], rfl⟩, ?_⟩
    · simp [buildSpecUniv, hbu]
    · have hevu' := evalSpecUniv_mono ⟨[.succ uIdx], rfl⟩ (Nat.le_refl _) hevu
      simp [Level.dagDepth, evalSpecUniv, hevu']
  | .max u v, tbl, hwf => by
    simp only [Level.allParamsIn, Bool.and_eq_true] at hwf
    obtain ⟨uIdx, tbl₁, hbu, hext₁, hevu⟩ := buildSpecUniv_spec ps u tbl hwf.1
    obtain ⟨vIdx, tbl₂, hbv, hext₂, hevv⟩ := buildSpecUniv_spec ps v tbl₁ hwf.2
    let tbl' := tbl₂ ++ [.max uIdx vIdx]
    have hext_u : tbl₁ <+: tbl' := hext₂.trans ⟨[.max uIdx vIdx], rfl⟩
    have hext_v : tbl₂ <+: tbl' := ⟨[.max uIdx vIdx], rfl⟩
    have hevu' := evalSpecUniv_mono hext_u (Nat.le_max_left u.dagDepth v.dagDepth) hevu
    have hevv' := evalSpecUniv_mono hext_v (Nat.le_max_right u.dagDepth v.dagDepth) hevv
    refine ⟨tbl₂.length, tbl', ?_, hext₁.trans hext_u, ?_⟩
    · simp [buildSpecUniv, hbu, hbv, tbl']
    · simp [Level.dagDepth, evalSpecUniv, tbl', hevu', hevv']
  | .imax u v, tbl, hwf => by
    simp only [Level.allParamsIn, Bool.and_eq_true] at hwf
    obtain ⟨uIdx, tbl₁, hbu, hext₁, hevu⟩ := buildSpecUniv_spec ps u tbl hwf.1
    obtain ⟨vIdx, tbl₂, hbv, hext₂, hevv⟩ := buildSpecUniv_spec ps v tbl₁ hwf.2
    let tbl' := tbl₂ ++ [.imax uIdx vIdx]
    have hext_u : tbl₁ <+: tbl' := hext₂.trans ⟨[.imax uIdx vIdx], rfl⟩
    have hext_v : tbl₂ <+: tbl' := ⟨[.imax uIdx vIdx], rfl⟩
    have hevu' := evalSpecUniv_mono hext_u (Nat.le_max_left u.dagDepth v.dagDepth) hevu
    have hevv' := evalSpecUniv_mono hext_v (Nat.le_max_right u.dagDepth v.dagDepth) hevv
    refine ⟨tbl₂.length, tbl', ?_, hext₁.trans hext_u, ?_⟩
    · simp [buildSpecUniv, hbu, hbv, tbl']
    · simp [Level.dagDepth, evalSpecUniv, tbl', hevu', hevv']

/-- Compile a list of universe levels into `SpecUnivTable`. -/
def buildSpecUnivList (ps : List LevelParam) :
    List Level → SpecUnivTable → Option (List Nat × SpecUnivTable)
  | [], tbl => some ([], tbl)
  | u :: us, tbl =>
    match buildSpecUniv ps u tbl with
    | some (uIdx, tbl₁) =>
      match buildSpecUnivList ps us tbl₁ with
      | some (usIdx, tbl₂) => some (uIdx :: usIdx, tbl₂)
      | none => none
    | none => none

/-- Reconstruct a list of universe levels from `SpecUnivTable`. -/
def evalSpecUnivList (ps : List LevelParam) (tbl : SpecUnivTable) (fuel : Nat) :
    List Nat → Option (List Level)
  | [] => some []
  | u :: us =>
    match evalSpecUniv ps tbl fuel u, evalSpecUnivList ps tbl fuel us with
    | some lu, some lus => some (lu :: lus)
    | _, _ => none

def Level.listDagDepth : List Level → Nat
  | [] => 1
  | u :: us => Nat.max u.dagDepth (Level.listDagDepth us)

theorem evalSpecUnivList_mono {ps : List LevelParam} {u₁ u₂ : SpecUnivTable}
    (hext : u₁ <+: u₂) {f₁ f₂ : Nat} (hle : f₁ ≤ f₂) :
    ∀ {idxs : List Nat} {ls : List Level},
      evalSpecUnivList ps u₁ f₁ idxs = some ls →
      evalSpecUnivList ps u₂ f₂ idxs = some ls
  | [], _, h => h
  | i :: is, _, h => by
    unfold evalSpecUnivList at h ⊢
    cases hi : evalSpecUniv ps u₁ f₁ i with
    | none => rw [hi] at h; simp at h
    | some l =>
      cases his : evalSpecUnivList ps u₁ f₁ is with
      | none => rw [hi, his] at h; simp at h
      | some rest =>
        rw [hi, his] at h
        rw [evalSpecUniv_mono hext hle hi, evalSpecUnivList_mono hext hle his]
        exact h

theorem buildSpecUnivList_spec (ps : List LevelParam) :
    ∀ (us : List Level) (tbl : SpecUnivTable),
      (us.all (·.allParamsIn ps)) = Bool.true →
      ∃ idxs tbl', buildSpecUnivList ps us tbl = some (idxs, tbl') ∧
        tbl <+: tbl' ∧
        evalSpecUnivList ps tbl' (Level.listDagDepth us) idxs = some us
  | [], tbl, _ => ⟨[], tbl, rfl, List.prefix_refl tbl, rfl⟩
  | u :: us, tbl, hwf => by
    simp only [List.all_cons, Bool.and_eq_true] at hwf
    obtain ⟨uIdx, tbl₁, hbu, hext₁, hevu⟩ := buildSpecUniv_spec ps u tbl hwf.1
    obtain ⟨usIdx, tbl₂, hbus, hext₂, hevus⟩ := buildSpecUnivList_spec ps us tbl₁ hwf.2
    have hevu' := evalSpecUniv_mono hext₂ (Nat.le_max_left u.dagDepth (Level.listDagDepth us)) hevu
    have hevus' := evalSpecUnivList_mono (List.prefix_refl tbl₂)
      (Nat.le_max_right u.dagDepth (Level.listDagDepth us)) hevus
    refine ⟨uIdx :: usIdx, tbl₂, ?_, hext₁.trans hext₂, ?_⟩
    · simp [buildSpecUnivList, hbu, hbus]
    · simp [Level.listDagDepth, evalSpecUnivList, hevu', hevus']

/-! ## Expression DAG Table (`SpecExprNode`, `SpecExprTable`) -/

/-- A node in the flattened expression specification DAG table. -/
inductive SpecExprNode where
  | bvar (i : Nat)
  | sort (u : Nat)
  | const (roleIdx : Nat) (us : List Nat)
  | app (f a : Nat)
  | lam (ty body : Nat)
  | forallE (ty body : Nat)
  | letE (ty val body : Nat)
  | proj (roleIdx : Nat) (fieldIdx : Nat) (struct : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Flattened DAG table of universe levels and expression nodes. -/
structure SpecExprTable where
  univs : SpecUnivTable := []
  nodes : List SpecExprNode := []
  deriving DecidableEq, Repr, Inhabited

/-- `t₂` extends `t₁` if both its universe table and its expression node table extend `t₁`'s. -/
def SpecExprTable.Extends (t₁ t₂ : SpecExprTable) : Prop :=
  t₁.univs <+: t₂.univs ∧ t₁.nodes <+: t₂.nodes

theorem SpecExprTable.Extends.refl (t : SpecExprTable) : t.Extends t :=
  ⟨List.prefix_refl _, List.prefix_refl _⟩

theorem SpecExprTable.Extends.trans {t₁ t₂ t₃ : SpecExprTable}
    (h₁₂ : t₁.Extends t₂) (h₂₃ : t₂.Extends t₃) : t₁.Extends t₃ :=
  ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.trans h₂₃.2⟩

/-- Substitute role keys in an `Expr .anon` using `resolve : Role → Option (Key .anon)`,
normalizing binder metadata to Lean defaults (`default : BinderMeta`, `default : LetMeta`). -/
def substRoleKeysM (resolve : Role → Option (Key .anon)) : Expr .anon → Option (Expr .anon)
  | .bvar i => some (.bvar i)
  | .fvar _ _ => none
  | .sort u => some (.sort u)
  | .const (.role r) us =>
    match resolve r with
    | some k => some (.const k us)
    | none => none
  | .const _ _ => none
  | .app f a =>
    match substRoleKeysM resolve f, substRoleKeysM resolve a with
    | some ef, some ea => some (.app ef ea)
    | _, _ => none
  | .lam ty body _ =>
    match substRoleKeysM resolve ty, substRoleKeysM resolve body with
    | some ety, some eb => some (.lam ety eb default)
    | _, _ => none
  | .forallE ty body _ =>
    match substRoleKeysM resolve ty, substRoleKeysM resolve body with
    | some ety, some eb => some (.forallE ety eb default)
    | _, _ => none
  | .letE ty val body _ =>
    match substRoleKeysM resolve ty, substRoleKeysM resolve val, substRoleKeysM resolve body with
    | some ety, some ev, some eb => some (.letE ety ev eb default)
    | _, _, _ => none
  | .lit _ => none
  | .proj (.role r) i e =>
    match resolve r, substRoleKeysM resolve e with
    | some k, some e' => some (.proj k i e')
    | _, _ => none
  | .proj _ _ _ => none

/-- Well-formedness of a closed role-specification `Expr .anon` under universe parameters `ps`:
all universe parameters are in `ps`, all constant/projection keys are `.role r`,
all binders have Lean contracts (`.many`, `.shared`, `.lean false`), and there are
no loose `.fvar`s or literals. -/
def Expr.specClosedWF (ps : List LevelParam) : Expr .anon → Bool
  | .bvar _ => Bool.true
  | .fvar _ _ => Bool.false
  | .sort u => u.allParamsIn ps
  | .const (.role _) us => us.all (·.allParamsIn ps)
  | .const _ _ => Bool.false
  | .app f a => f.specClosedWF ps && a.specClosedWF ps
  | .lam ty body bm | .forallE ty body bm =>
    decide (bm.contract = .many ∧ bm.result = .shared) &&
    ty.specClosedWF ps && body.specClosedWF ps
  | .letE ty val body lm =>
    decide (lm.contract = .lean Bool.false) &&
    ty.specClosedWF ps && val.specClosedWF ps && body.specClosedWF ps
  | .lit _ => Bool.false
  | .proj (.role _) _ e => e.specClosedWF ps
  | .proj _ _ _ => Bool.false

/-- Structural recursion depth of an `Expr .anon` for `evalSpecExpr`. -/
def Expr.dagDepth : Expr .anon → Nat
  | .bvar _ | .fvar _ _ | .lit _ => 1
  | .sort u => u.dagDepth + 1
  | .const _ us => Level.listDagDepth us + 1
  | .app f a | .lam f a _ | .forallE f a _ => Nat.max f.dagDepth a.dagDepth + 1
  | .letE t v b _ => Nat.max t.dagDepth (Nat.max v.dagDepth b.dagDepth) + 1
  | .proj _ _ e => e.dagDepth + 1

/-- Compile a closed `Expr .anon` into a `SpecExprTable` under universe parameters `ps`. -/
def buildSpecExpr (ps : List LevelParam) :
    Expr .anon → SpecExprTable → Option (Nat × SpecExprTable)
  | .bvar i, tbl =>
    some (tbl.nodes.length, { tbl with nodes := tbl.nodes ++ [.bvar i] })
  | .fvar _ _, _ => none
  | .sort u, tbl =>
    match buildSpecUniv ps u tbl.univs with
    | some (uIdx, univs₁) =>
      some (tbl.nodes.length, { univs := univs₁, nodes := tbl.nodes ++ [.sort uIdx] })
    | none => none
  | .const (.role r) us, tbl =>
    match buildSpecUnivList ps us tbl.univs with
    | some (usIdx, univs₁) =>
      some (tbl.nodes.length, { univs := univs₁, nodes := tbl.nodes ++ [.const r.idx usIdx] })
    | none => none
  | .const _ _, _ => none
  | .app f a, tbl =>
    match buildSpecExpr ps f tbl with
    | some (fIdx, tbl₁) =>
      match buildSpecExpr ps a tbl₁ with
      | some (aIdx, tbl₂) =>
        some (tbl₂.nodes.length, { tbl₂ with nodes := tbl₂.nodes ++ [.app fIdx aIdx] })
      | none => none
    | none => none
  | .lam ty body _, tbl =>
    match buildSpecExpr ps ty tbl with
    | some (tyIdx, tbl₁) =>
      match buildSpecExpr ps body tbl₁ with
      | some (bIdx, tbl₂) =>
        some (tbl₂.nodes.length, { tbl₂ with nodes := tbl₂.nodes ++ [.lam tyIdx bIdx] })
      | none => none
    | none => none
  | .forallE ty body _, tbl =>
    match buildSpecExpr ps ty tbl with
    | some (tyIdx, tbl₁) =>
      match buildSpecExpr ps body tbl₁ with
      | some (bIdx, tbl₂) =>
        some (tbl₂.nodes.length, { tbl₂ with nodes := tbl₂.nodes ++ [.forallE tyIdx bIdx] })
      | none => none
    | none => none
  | .letE ty val body _, tbl =>
    match buildSpecExpr ps ty tbl with
    | some (tyIdx, tbl₁) =>
      match buildSpecExpr ps val tbl₁ with
      | some (vIdx, tbl₂) =>
        match buildSpecExpr ps body tbl₂ with
        | some (bIdx, tbl₃) =>
          some (tbl₃.nodes.length, { tbl₃ with nodes := tbl₃.nodes ++ [.letE tyIdx vIdx bIdx] })
        | none => none
      | none => none
    | none => none
  | .lit _, _ => none
  | .proj (.role r) fIdx s, tbl =>
    match buildSpecExpr ps s tbl with
    | some (sIdx, tbl₁) =>
      some (tbl₁.nodes.length, { tbl₁ with nodes := tbl₁.nodes ++ [.proj r.idx fIdx sIdx] })
    | none => none
  | .proj _ _ _, _ => none

/-- Reconstruct an `Expr .anon` from `tbl : SpecExprTable` at node index `idx` with `fuel`,
resolving role references via `resolve : Role → Option (Key .anon)`. -/
def evalSpecExpr (resolve : Role → Option (Key .anon)) (ps : List LevelParam)
    (tbl : SpecExprTable) : Nat → Nat → Option (Expr .anon)
  | 0, _ => none
  | fuel + 1, idx =>
    match tbl.nodes[idx]? with
    | some (.bvar i) => some (.bvar i)
    | some (.sort u) =>
      match evalSpecUniv ps tbl.univs fuel u with
      | some lu => some (.sort lu)
      | none => none
    | some (.const rIdx us) =>
      match Role.ofIdx? rIdx with
      | some r =>
        match resolve r, evalSpecUnivList ps tbl.univs fuel us with
        | some k, some ls => some (.const k ls)
        | _, _ => none
      | none => none
    | some (.app f a) =>
      match evalSpecExpr resolve ps tbl fuel f, evalSpecExpr resolve ps tbl fuel a with
      | some ef, some ea => some (.app ef ea)
      | _, _ => none
    | some (.lam ty body) =>
      match evalSpecExpr resolve ps tbl fuel ty, evalSpecExpr resolve ps tbl fuel body with
      | some ety, some eb => some (.lam ety eb default)
      | _, _ => none
    | some (.forallE ty body) =>
      match evalSpecExpr resolve ps tbl fuel ty, evalSpecExpr resolve ps tbl fuel body with
      | some ety, some eb => some (.forallE ety eb default)
      | _, _ => none
    | some (.letE ty val body) =>
      match evalSpecExpr resolve ps tbl fuel ty,
            evalSpecExpr resolve ps tbl fuel val,
            evalSpecExpr resolve ps tbl fuel body with
      | some ety, some ev, some eb => some (.letE ety ev eb default)
      | _, _, _ => none
    | some (.proj rIdx fIdx s) =>
      match Role.ofIdx? rIdx with
      | some r =>
        match resolve r, evalSpecExpr resolve ps tbl fuel s with
        | some k, some es => some (.proj k fIdx es)
        | _, _ => none
      | none => none
    | none => none

theorem evalSpecExpr_idx_lt {resolve : Role → Option (Key .anon)} {ps : List LevelParam}
    {tbl : SpecExprTable} {fuel idx : Nat} {e : Expr .anon}
    (h : evalSpecExpr resolve ps tbl fuel idx = some e) : idx < tbl.nodes.length := by
  cases fuel with
  | zero => simp [evalSpecExpr] at h
  | succ f =>
    unfold evalSpecExpr at h
    rcases Nat.lt_or_ge idx tbl.nodes.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at h
      simp at h

theorem evalSpecExpr_mono {resolve : Role → Option (Key .anon)} {ps : List LevelParam}
    {t₁ t₂ : SpecExprTable} (hext : t₁.Extends t₂) :
    ∀ {fuel₁ fuel₂ idx : Nat} {e : Expr .anon},
      fuel₁ ≤ fuel₂ →
      evalSpecExpr resolve ps t₁ fuel₁ idx = some e →
      evalSpecExpr resolve ps t₂ fuel₂ idx = some e
  | 0, _, _, _, _, h => by simp [evalSpecExpr] at h
  | _ + 1, 0, _, _, hle, _ => by omega
  | f₁ + 1, f₂ + 1, idx, e, hle, h => by
    have hlt : idx < t₁.nodes.length := evalSpecExpr_idx_lt h
    obtain ⟨hextU, suf, hnodes⟩ := hext
    have hget : t₂.nodes[idx]? = t₁.nodes[idx]? := by
      rw [← hnodes]
      exact List.getElem?_append_left hlt
    have hle' : f₁ ≤ f₂ := by omega
    unfold evalSpecExpr at h ⊢
    rw [hget]
    cases hnode : t₁.nodes[idx]? with
    | none => rw [hnode] at h; simp at h
    | some node =>
      rw [hnode] at h
      cases node with
      | bvar i => exact h
      | sort u =>
        dsimp only at h ⊢
        cases hu : evalSpecUniv ps t₁.univs f₁ u with
        | none => rw [hu] at h; simp at h
        | some lu =>
          rw [hu] at h
          rw [evalSpecUniv_mono hextU hle' hu]
          exact h
      | const rIdx us =>
        dsimp only at h ⊢
        cases hr : Role.ofIdx? rIdx with
        | none => rw [hr] at h; simp at h
        | some r =>
          rw [hr] at h
          dsimp only at h ⊢
          cases hk : resolve r with
          | none => rw [hk] at h; simp at h
          | some k =>
            cases hus : evalSpecUnivList ps t₁.univs f₁ us with
            | none => rw [hk, hus] at h; simp at h
            | some ls =>
              rw [hk, hus] at h
              rw [evalSpecUnivList_mono hextU hle' hus]
              exact h
      | app f a =>
        dsimp only at h ⊢
        cases hf : evalSpecExpr resolve ps t₁ f₁ f with
        | none => rw [hf] at h; simp at h
        | some ef =>
          cases ha : evalSpecExpr resolve ps t₁ f₁ a with
          | none => rw [hf, ha] at h; simp at h
          | some ea =>
            rw [hf, ha] at h
            rw [evalSpecExpr_mono ⟨hextU, suf, hnodes⟩ hle' hf,
                evalSpecExpr_mono ⟨hextU, suf, hnodes⟩ hle' ha]
            exact h
      | lam ty body =>
        dsimp only at h ⊢
        cases hty : evalSpecExpr resolve ps t₁ f₁ ty with
        | none => rw [hty] at h; simp at h
        | some ety =>
          cases hb : evalSpecExpr resolve ps t₁ f₁ body with
          | none => rw [hty, hb] at h; simp at h
          | some eb =>
            rw [hty, hb] at h
            rw [evalSpecExpr_mono ⟨hextU, suf, hnodes⟩ hle' hty,
                evalSpecExpr_mono ⟨hextU, suf, hnodes⟩ hle' hb]
            exact h
      | forallE ty body =>
        dsimp only at h ⊢
        cases hty : evalSpecExpr resolve ps t₁ f₁ ty with
        | none => rw [hty] at h; simp at h
        | some ety =>
          cases hb : evalSpecExpr resolve ps t₁ f₁ body with
          | none => rw [hty, hb] at h; simp at h
          | some eb =>
            rw [hty, hb] at h
            rw [evalSpecExpr_mono ⟨hextU, suf, hnodes⟩ hle' hty,
                evalSpecExpr_mono ⟨hextU, suf, hnodes⟩ hle' hb]
            exact h
      | letE ty val body =>
        dsimp only at h ⊢
        cases hty : evalSpecExpr resolve ps t₁ f₁ ty with
        | none => rw [hty] at h; simp at h
        | some ety =>
          cases hv : evalSpecExpr resolve ps t₁ f₁ val with
          | none => rw [hty, hv] at h; simp at h
          | some ev =>
            cases hb : evalSpecExpr resolve ps t₁ f₁ body with
            | none => rw [hty, hv, hb] at h; simp at h
            | some eb =>
              rw [hty, hv, hb] at h
              rw [evalSpecExpr_mono ⟨hextU, suf, hnodes⟩ hle' hty,
                  evalSpecExpr_mono ⟨hextU, suf, hnodes⟩ hle' hv,
                  evalSpecExpr_mono ⟨hextU, suf, hnodes⟩ hle' hb]
              exact h
      | proj rIdx fIdx s =>
        dsimp only at h ⊢
        cases hr : Role.ofIdx? rIdx with
        | none => rw [hr] at h; simp at h
        | some r =>
          rw [hr] at h
          dsimp only at h ⊢
          cases hk : resolve r with
          | none => rw [hk] at h; simp at h
          | some k =>
            cases hs : evalSpecExpr resolve ps t₁ f₁ s with
            | none => rw [hk, hs] at h; simp at h
            | some es =>
              rw [hk, hs] at h
              rw [evalSpecExpr_mono ⟨hextU, suf, hnodes⟩ hle' hs]
              exact h

/-- **Expression DAG Table Soundness (under any role resolver `resolve`, e.g. `t.keyOf`)**:
Whenever `e.specClosedWF ps = Bool.true` and `substRoleKeysM resolve e = some e'`,
`buildSpecExpr ps e tbl` succeeds and produces `(idx, tbl')` such that
`tbl.Extends tbl'` and `evalSpecExpr resolve ps tbl' e.dagDepth idx = some e'`. -/
theorem buildSpecExpr_spec (resolve : Role → Option (Key .anon)) (ps : List LevelParam) :
    ∀ (e : Expr .anon) (tbl : SpecExprTable) {e' : Expr .anon},
      e.specClosedWF ps = Bool.true →
      substRoleKeysM resolve e = some e' →
      ∃ idx tbl', buildSpecExpr ps e tbl = some (idx, tbl') ∧
        tbl.Extends tbl' ∧
        evalSpecExpr resolve ps tbl' e.dagDepth idx = some e'
  | .bvar i, tbl, _, _, hsub => by
    simp only [substRoleKeysM, Option.some.injEq] at hsub
    subst hsub
    refine ⟨tbl.nodes.length, { tbl with nodes := tbl.nodes ++ [.bvar i] }, rfl,
      ⟨List.prefix_refl _, ⟨[.bvar i], rfl⟩⟩, ?_⟩
    simp [Expr.dagDepth, evalSpecExpr]
  | .fvar _ _, _, _, hwf, _ => by simp [Expr.specClosedWF] at hwf
  | .lit _, _, _, hwf, _ => by simp [Expr.specClosedWF] at hwf
  | .sort u, tbl, _, hwf, hsub => by
    simp only [substRoleKeysM, Option.some.injEq] at hsub
    subst hsub
    obtain ⟨uIdx, univs₁, hbu, hextU, hevu⟩ := buildSpecUniv_spec ps u tbl.univs hwf
    let tbl' : SpecExprTable := { univs := univs₁, nodes := tbl.nodes ++ [.sort uIdx] }
    refine ⟨tbl.nodes.length, tbl', ?_, ⟨hextU, ⟨[.sort uIdx], rfl⟩⟩, ?_⟩
    · simp [buildSpecExpr, hbu, tbl']
    · simp [Expr.dagDepth, evalSpecExpr, tbl', hevu]
  | .const (.role r) us, tbl, _, hwf, hsub => by
    unfold substRoleKeysM at hsub
    cases hk : resolve r with
    | none => rw [hk] at hsub; simp at hsub
    | some k =>
      rw [hk, Option.some.injEq] at hsub
      subst hsub
      obtain ⟨usIdx, univs₁, hbus, hextU, hevus⟩ := buildSpecUnivList_spec ps us tbl.univs hwf
      let tbl' : SpecExprTable := { univs := univs₁, nodes := tbl.nodes ++ [.const r.idx usIdx] }
      refine ⟨tbl.nodes.length, tbl', ?_, ⟨hextU, ⟨[.const r.idx usIdx], rfl⟩⟩, ?_⟩
      · simp [buildSpecExpr, hbus, tbl']
      · simp [Expr.dagDepth, evalSpecExpr, tbl', Role.ofIdx?_idx, hk, hevus]
  | .const (.id _) _, _, _, hwf, _ => by simp [Expr.specClosedWF] at hwf
  | .const (.aux _ _) _, _, _, hwf, _ => by simp [Expr.specClosedWF] at hwf
  | .app f a, tbl, _, hwf, hsub => by
    simp only [Expr.specClosedWF, Bool.and_eq_true] at hwf
    unfold substRoleKeysM at hsub
    cases hf : substRoleKeysM resolve f with
    | none => rw [hf] at hsub; simp at hsub
    | some ef =>
      cases ha : substRoleKeysM resolve a with
      | none => rw [hf, ha] at hsub; simp at hsub
      | some ea =>
        rw [hf, ha, Option.some.injEq] at hsub
        subst hsub
        obtain ⟨fIdx, tbl₁, hbf, hext₁, hevf⟩ := buildSpecExpr_spec resolve ps f tbl hwf.1 hf
        obtain ⟨aIdx, tbl₂, hba, hext₂, heva⟩ := buildSpecExpr_spec resolve ps a tbl₁ hwf.2 ha
        let tbl' : SpecExprTable := { tbl₂ with nodes := tbl₂.nodes ++ [.app fIdx aIdx] }
        have hext_a : tbl₂.Extends tbl' := ⟨List.prefix_refl _, ⟨[.app fIdx aIdx], rfl⟩⟩
        have hext_f : tbl₁.Extends tbl' := hext₂.trans hext_a
        have hevf' := evalSpecExpr_mono hext_f (Nat.le_max_left f.dagDepth a.dagDepth) hevf
        have heva' := evalSpecExpr_mono hext_a (Nat.le_max_right f.dagDepth a.dagDepth) heva
        refine ⟨tbl₂.nodes.length, tbl', ?_, hext₁.trans hext_f, ?_⟩
        · simp [buildSpecExpr, hbf, hba, tbl']
        · simp [Expr.dagDepth, evalSpecExpr, tbl', hevf', heva']
  | .lam ty body _, tbl, _, hwf, hsub => by
    simp only [Expr.specClosedWF, Bool.and_eq_true] at hwf
    unfold substRoleKeysM at hsub
    cases hty : substRoleKeysM resolve ty with
    | none => rw [hty] at hsub; simp at hsub
    | some ety =>
      cases hb : substRoleKeysM resolve body with
      | none => rw [hty, hb] at hsub; simp at hsub
      | some eb =>
        rw [hty, hb, Option.some.injEq] at hsub
        subst hsub
        obtain ⟨tyIdx, tbl₁, hbty, hext₁, hevty⟩ := buildSpecExpr_spec resolve ps ty tbl hwf.1.2 hty
        obtain ⟨bIdx, tbl₂, hbb, hext₂, hevb⟩ := buildSpecExpr_spec resolve ps body tbl₁ hwf.2 hb
        let tbl' : SpecExprTable := { tbl₂ with nodes := tbl₂.nodes ++ [.lam tyIdx bIdx] }
        have hext_b : tbl₂.Extends tbl' := ⟨List.prefix_refl _, ⟨[.lam tyIdx bIdx], rfl⟩⟩
        have hext_ty : tbl₁.Extends tbl' := hext₂.trans hext_b
        have hevty' := evalSpecExpr_mono hext_ty (Nat.le_max_left ty.dagDepth body.dagDepth) hevty
        have hevb' := evalSpecExpr_mono hext_b (Nat.le_max_right ty.dagDepth body.dagDepth) hevb
        refine ⟨tbl₂.nodes.length, tbl', ?_, hext₁.trans hext_ty, ?_⟩
        · simp [buildSpecExpr, hbty, hbb, tbl']
        · simp [Expr.dagDepth, evalSpecExpr, tbl', hevty', hevb']
  | .forallE ty body _, tbl, _, hwf, hsub => by
    simp only [Expr.specClosedWF, Bool.and_eq_true] at hwf
    unfold substRoleKeysM at hsub
    cases hty : substRoleKeysM resolve ty with
    | none => rw [hty] at hsub; simp at hsub
    | some ety =>
      cases hb : substRoleKeysM resolve body with
      | none => rw [hty, hb] at hsub; simp at hsub
      | some eb =>
        rw [hty, hb, Option.some.injEq] at hsub
        subst hsub
        obtain ⟨tyIdx, tbl₁, hbty, hext₁, hevty⟩ := buildSpecExpr_spec resolve ps ty tbl hwf.1.2 hty
        obtain ⟨bIdx, tbl₂, hbb, hext₂, hevb⟩ := buildSpecExpr_spec resolve ps body tbl₁ hwf.2 hb
        let tbl' : SpecExprTable := { tbl₂ with nodes := tbl₂.nodes ++ [.forallE tyIdx bIdx] }
        have hext_b : tbl₂.Extends tbl' := ⟨List.prefix_refl _, ⟨[.forallE tyIdx bIdx], rfl⟩⟩
        have hext_ty : tbl₁.Extends tbl' := hext₂.trans hext_b
        have hevty' := evalSpecExpr_mono hext_ty (Nat.le_max_left ty.dagDepth body.dagDepth) hevty
        have hevb' := evalSpecExpr_mono hext_b (Nat.le_max_right ty.dagDepth body.dagDepth) hevb
        refine ⟨tbl₂.nodes.length, tbl', ?_, hext₁.trans hext_ty, ?_⟩
        · simp [buildSpecExpr, hbty, hbb, tbl']
        · simp [Expr.dagDepth, evalSpecExpr, tbl', hevty', hevb']
  | .letE ty val body _, tbl, _, hwf, hsub => by
    simp only [Expr.specClosedWF, Bool.and_eq_true] at hwf
    unfold substRoleKeysM at hsub
    cases hty : substRoleKeysM resolve ty with
    | none => rw [hty] at hsub; simp at hsub
    | some ety =>
      cases hv : substRoleKeysM resolve val with
      | none => rw [hty, hv] at hsub; simp at hsub
      | some ev =>
        cases hb : substRoleKeysM resolve body with
        | none => rw [hty, hv, hb] at hsub; simp at hsub
        | some eb =>
          rw [hty, hv, hb, Option.some.injEq] at hsub
          subst hsub
          obtain ⟨tyIdx, tbl₁, hbty, hext₁, hevty⟩ := buildSpecExpr_spec resolve ps ty tbl hwf.1.1.2 hty
          obtain ⟨vIdx, tbl₂, hbv, hext₂, hevv⟩ := buildSpecExpr_spec resolve ps val tbl₁ hwf.1.2 hv
          obtain ⟨bIdx, tbl₃, hbb, hext₃, hevb⟩ := buildSpecExpr_spec resolve ps body tbl₂ hwf.2 hb
          let tbl' : SpecExprTable := { tbl₃ with nodes := tbl₃.nodes ++ [.letE tyIdx vIdx bIdx] }
          have hext_b : tbl₃.Extends tbl' := ⟨List.prefix_refl _, ⟨[.letE tyIdx vIdx bIdx], rfl⟩⟩
          have hext_v : tbl₂.Extends tbl' := hext₃.trans hext_b
          have hext_ty : tbl₁.Extends tbl' := hext₂.trans hext_v
          have hle_ty : ty.dagDepth ≤ Nat.max ty.dagDepth (Nat.max val.dagDepth body.dagDepth) :=
            Nat.le_max_left _ _
          have hle_v : val.dagDepth ≤ Nat.max ty.dagDepth (Nat.max val.dagDepth body.dagDepth) :=
            Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
          have hle_b : body.dagDepth ≤ Nat.max ty.dagDepth (Nat.max val.dagDepth body.dagDepth) :=
            Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
          have hevty' := evalSpecExpr_mono hext_ty hle_ty hevty
          have hevv' := evalSpecExpr_mono hext_v hle_v hevv
          have hevb' := evalSpecExpr_mono hext_b hle_b hevb
          refine ⟨tbl₃.nodes.length, tbl', ?_, hext₁.trans hext_ty, ?_⟩
          · simp [buildSpecExpr, hbty, hbv, hbb, tbl']
          · simp [Expr.dagDepth, evalSpecExpr, tbl', hevty', hevv', hevb']
  | .proj (.role r) fIdx s, tbl, _, hwf, hsub => by
    unfold substRoleKeysM at hsub
    cases hk : resolve r with
    | none => rw [hk] at hsub; simp at hsub
    | some k =>
      cases hs : substRoleKeysM resolve s with
      | none => rw [hk, hs] at hsub; simp at hsub
      | some es =>
        rw [hk, hs, Option.some.injEq] at hsub
        subst hsub
        obtain ⟨sIdx, tbl₁, hbs, hext₁, hevs⟩ := buildSpecExpr_spec resolve ps s tbl hwf hs
        let tbl' : SpecExprTable := { tbl₁ with nodes := tbl₁.nodes ++ [.proj r.idx fIdx sIdx] }
        have hext_s : tbl₁.Extends tbl' := ⟨List.prefix_refl _, ⟨[.proj r.idx fIdx sIdx], rfl⟩⟩
        have hevs' := evalSpecExpr_mono hext_s (Nat.le_refl _) hevs
        refine ⟨tbl₁.nodes.length, tbl', ?_, hext₁.trans hext_s, ?_⟩
        · simp [buildSpecExpr, hbs, tbl']
        · simp [Expr.dagDepth, evalSpecExpr, tbl', Role.ofIdx?_idx, hk, hevs']
  | .proj (.id _) _ _, _, _, hwf, _ => by simp [Expr.specClosedWF] at hwf
  | .proj (.aux _ _) _ _, _, _, hwf, _ => by simp [Expr.specClosedWF] at hwf

/-- Under `RoleTable.roleKeyOf` (`fun r => some (.role r)`), `substRoleKeysM` on any
well-formed specification expression produces `some e.erasePw`. -/
theorem substRoleKeysM_roleKeyOf :
    ∀ (ps : List LevelParam) (e : Expr .anon),
      e.specClosedWF ps = Bool.true →
      substRoleKeysM RoleTable.roleKeyOf e = some e.erasePw
  | _, .bvar i, _ => rfl
  | ps, .fvar _ _, hwf => by simp [Expr.specClosedWF] at hwf
  | ps, .lit _, hwf => by simp [Expr.specClosedWF] at hwf
  | _, .sort u, _ => rfl
  | _, .const (.role r) us, _ => rfl
  | ps, .const (.id _) _, hwf => by simp [Expr.specClosedWF] at hwf
  | ps, .const (.aux _ _) _, hwf => by simp [Expr.specClosedWF] at hwf
  | ps, .app f a, hwf => by
    simp only [Expr.specClosedWF, Bool.and_eq_true] at hwf
    simp [substRoleKeysM, Expr.erasePw,
      substRoleKeysM_roleKeyOf ps f hwf.1, substRoleKeysM_roleKeyOf ps a hwf.2]
  | ps, .lam ty body bm, hwf => by
    simp only [Expr.specClosedWF, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have hbm : { bm with pw := .never } = (default : BinderMeta) := by
      cases bm with
      | mk pw contract result display =>
        obtain ⟨rfl, rfl⟩ := hwf.1.1
        show BinderMeta.mk .never .many .shared display = BinderMeta.mk .never .many .shared BinderDisplay.anon
        rw [Subsingleton.elim display BinderDisplay.anon]
    simp [substRoleKeysM, Expr.erasePw, hbm,
      substRoleKeysM_roleKeyOf ps ty hwf.1.2, substRoleKeysM_roleKeyOf ps body hwf.2]
  | ps, .forallE ty body bm, hwf => by
    simp only [Expr.specClosedWF, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have hbm : { bm with pw := .never } = (default : BinderMeta) := by
      cases bm with
      | mk pw contract result display =>
        obtain ⟨rfl, rfl⟩ := hwf.1.1
        show BinderMeta.mk .never .many .shared display = BinderMeta.mk .never .many .shared BinderDisplay.anon
        rw [Subsingleton.elim display BinderDisplay.anon]
    simp [substRoleKeysM, Expr.erasePw, hbm,
      substRoleKeysM_roleKeyOf ps ty hwf.1.2, substRoleKeysM_roleKeyOf ps body hwf.2]
  | ps, .letE ty val body lm, hwf => by
    simp only [Expr.specClosedWF, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have hlm : lm = (default : LetMeta) := by
      cases lm with
      | mk contract display =>
        have hc : contract = .lean Bool.false := hwf.1.1.1
        subst hc
        show LetMeta.mk (.lean Bool.false) display = LetMeta.mk (.lean Bool.false) LetDisplay.anon
        rw [Subsingleton.elim display LetDisplay.anon]
    simp [substRoleKeysM, Expr.erasePw, hlm,
      substRoleKeysM_roleKeyOf ps ty hwf.1.1.2,
      substRoleKeysM_roleKeyOf ps val hwf.1.2,
      substRoleKeysM_roleKeyOf ps body hwf.2]
  | ps, .proj (.role r) fIdx s, hwf => by
    simp [substRoleKeysM, RoleTable.roleKeyOf, Expr.erasePw, substRoleKeysM_roleKeyOf ps s hwf]
  | ps, .proj (.id _) _ _, hwf => by simp [Expr.specClosedWF] at hwf
  | ps, .proj (.aux _ _) _ _, hwf => by simp [Expr.specClosedWF] at hwf

/-- **Exact Reconstruction at `RoleTable.roleKeyOf`**: Compiling any well-formed
specification expression `e` into `SpecExprTable` and evaluating it with `evalSpecExpr`
under `RoleTable.roleKeyOf` produces `some e.erasePw` (and `some e` when `e.erasePw = e`). -/
theorem buildSpecExpr_eval_roleKeyOf (ps : List LevelParam) (e : Expr .anon) (tbl : SpecExprTable)
    (hwf : e.specClosedWF ps = Bool.true) :
    ∃ idx tbl', buildSpecExpr ps e tbl = some (idx, tbl') ∧
      tbl.Extends tbl' ∧
      evalSpecExpr RoleTable.roleKeyOf ps tbl' e.dagDepth idx = some e.erasePw :=
  buildSpecExpr_spec RoleTable.roleKeyOf ps e tbl hwf (substRoleKeysM_roleKeyOf ps e hwf)

/-! ## Per-Role Specification Builders & Exact `Role.spec` Correspondence -/

/-- Turn an open `Spec.ops` equation `(hyps, lhs, rhs)` over `x, y : Nat` into a
standard `Equation .anon`. -/
def opEquationToEquation (hyps : List (Expr .anon)) (lhs rhs : Expr .anon) : Equation .anon :=
  { vars := [specNat, specNat], hyps, level := .succ .zero, carrier := specNat, lhs, rhs }

/-- Extract the closed anchor type `(levels, type)` for an `.anchor` role. -/
def specAnchorOf (r : Role) : Option (Nat × Expr .anon) :=
  match r.spec (md := .anon) with
  | .anchor n ty => some (n, ty)
  | _ => none

/-- Extract the closed axiom type `(levels, type)` for an `.axiom` role. -/
def specAxiomOf (r : Role) : Option (Nat × Option (Expr .anon)) :=
  match r.spec (md := .anon) with
  | .axiom n ty? => some (n, ty?)
  | _ => none

/-- Extract the closed type `(levels, type)` for an `.eqns` or `.ops` role. -/
def specEqnTypeOf (r : Role) : Option (Nat × Expr .anon) :=
  match r.spec (md := .anon) with
  | .ops ty _ => some (0, ty)
  | .eqns n ty _ => some (n, ty)
  | _ => none

/-- Build the DAG table for a role's anchor type (`Spec.anchor`). -/
def buildAnchorType (r : Role) : Option (Nat × Nat × SpecExprTable) :=
  match specAnchorOf r with
  | some (n, ty) =>
    match buildSpecExpr (List.range n) ty {} with
    | some (idx, tbl) => some (n, idx, tbl)
    | none => none
  | none => none

/-- Build the DAG table for a role's axiom type (`Spec.axiom`). -/
def buildAxiomType (r : Role) : Option (Nat × Nat × SpecExprTable) :=
  match specAxiomOf r with
  | some (n, some ty) =>
    match buildSpecExpr (List.range n) ty {} with
    | some (idx, tbl) => some (n, idx, tbl)
    | none => none
  | _ => none

/-- Build the DAG table for a role's operation/equation type (`Spec.ops` / `Spec.eqns`). -/
def buildEqnType (r : Role) : Option (Nat × Nat × SpecExprTable) :=
  match specEqnTypeOf r with
  | some (n, ty) =>
    match buildSpecExpr (List.range n) ty {} with
    | some (idx, tbl) => some (n, idx, tbl)
    | none => none
  | none => none

/-- Closed unconditional equation pairs `(closedLhs, closedRhs)` of a role (`Spec.ops` or `Spec.eqns`). -/
def roleClosedOpEqs (r : Role) : List (Nat × Expr .anon × Expr .anon) :=
  match r.spec (md := .anon) with
  | .ops _ eqs =>
    eqs.filterMap fun (hyps, lhs, rhs) =>
      if hyps.isEmpty then
        let eq := opEquationToEquation [] lhs rhs
        some (0, eq.closedSide lhs, eq.closedSide rhs)
      else none
  | .eqns n _ eqs =>
    eqs.filterMap fun eq =>
      if eq.hyps.isEmpty then
        some (n, eq.closedSide eq.lhs, eq.closedSide eq.rhs)
      else none
  | _ => []

/-- Closed equation/certificate statements of a role (`Spec.ops` certificates or `Spec.eqns` statements). -/
def roleClosedStatements (r : Role) : List (Nat × Expr .anon) :=
  match r.spec (md := .anon) with
  | .ops _ eqs =>
    eqs.filterMap fun (hyps, lhs, rhs) =>
      if hyps.isEmpty then none
      else some (0, (opEquationToEquation hyps lhs rhs).statement)
  | .eqns n _ eqs =>
    eqs.map fun eq => (n, eq.statement)
  | _ => []

/-- Build DAG tables for all unconditional equations `(lhs, rhs)` of `r`. -/
def buildOpEqs (r : Role) : Option (List (Nat × Nat × Nat × SpecExprTable)) :=
  (roleClosedOpEqs r).mapM fun (n, lhs, rhs) =>
    let ps := List.range n
    match buildSpecExpr ps lhs {} with
    | some (lIdx, tbl₁) =>
      match buildSpecExpr ps rhs tbl₁ with
      | some (rIdx, tbl₂) => some (n, lIdx, rIdx, tbl₂)
      | none => none
    | none => none

/-- Build DAG tables for all closed equation/certificate statements of `r`. -/
def buildEqnList (r : Role) : Option (List (Nat × Nat × SpecExprTable)) :=
  (roleClosedStatements r).mapM fun (n, stmt) =>
    match buildSpecExpr (List.range n) stmt {} with
    | some (idx, tbl) => some (n, idx, tbl)
    | none => none

/-- Build DAG tables for all members of a `.block` role `r`. -/
def buildRoleBlockExpected (r : Role) : Option (List (Key .anon × List LevelParam × Nat × SpecExprTable)) :=
  match r.spec (md := .anon) with
  | .block decls =>
    decls.mapM fun d =>
      let cv := d.toConstantVal
      match buildSpecExpr cv.levelParams cv.type {} with
      | some (idx, tbl) => some (cv.name, cv.levelParams, idx, tbl)
      | none => none
  | _ => none

/-- **Anchor Type DAG Correspondence**: For any role `r` with `r.spec = .anchor n ty`
and `ty.specClosedWF (List.range n) = Bool.true`, `buildAnchorType r` succeeds and its DAG
evaluates under any `resolve` (such as `t.keyOf`) to `substRoleKeysM resolve ty`
(and under `RoleTable.roleKeyOf` to `some ty.erasePw`). -/
theorem buildAnchorType_spec (resolve : Role → Option (Key .anon)) (r : Role)
    {n : Nat} {ty ty' : Expr .anon}
    (hspec : r.spec (md := .anon) = .anchor n ty)
    (hwf : ty.specClosedWF (List.range n) = Bool.true)
    (hsub : substRoleKeysM resolve ty = some ty') :
    ∃ idx tbl, buildAnchorType r = some (n, idx, tbl) ∧
      evalSpecExpr resolve (List.range n) tbl ty.dagDepth idx = some ty' := by
  obtain ⟨idx, tbl, hb, -, hev⟩ := buildSpecExpr_spec resolve (List.range n) ty {} hwf hsub
  refine ⟨idx, tbl, ?_, hev⟩
  simp [buildAnchorType, specAnchorOf, hspec, hb]

/-- **Axiom Type DAG Correspondence**: For any role `r` with `r.spec = .axiom n (some ty)`
and `ty.specClosedWF (List.range n) = Bool.true`, `buildAxiomType r` succeeds and its DAG
evaluates under any `resolve` (such as `t.keyOf`) to `substRoleKeysM resolve ty`. -/
theorem buildAxiomType_spec (resolve : Role → Option (Key .anon)) (r : Role)
    {n : Nat} {ty ty' : Expr .anon}
    (hspec : r.spec (md := .anon) = .axiom n (some ty))
    (hwf : ty.specClosedWF (List.range n) = Bool.true)
    (hsub : substRoleKeysM resolve ty = some ty') :
    ∃ idx tbl, buildAxiomType r = some (n, idx, tbl) ∧
      evalSpecExpr resolve (List.range n) tbl ty.dagDepth idx = some ty' := by
  obtain ⟨idx, tbl, hb, -, hev⟩ := buildSpecExpr_spec resolve (List.range n) ty {} hwf hsub
  refine ⟨idx, tbl, ?_, hev⟩
  simp [buildAxiomType, specAxiomOf, hspec, hb]

/-- **Equation/Operation Type DAG Correspondence**: For any role `r` with
`specEqnTypeOf r = some (n, ty)` and `ty.specClosedWF (List.range n) = Bool.true`,
`buildEqnType r` succeeds and its DAG evaluates under any `resolve` (such as `t.keyOf`)
to `substRoleKeysM resolve ty`. -/
theorem buildEqnType_spec (resolve : Role → Option (Key .anon)) (r : Role)
    {n : Nat} {ty ty' : Expr .anon}
    (hspec : specEqnTypeOf r = some (n, ty))
    (hwf : ty.specClosedWF (List.range n) = Bool.true)
    (hsub : substRoleKeysM resolve ty = some ty') :
    ∃ idx tbl, buildEqnType r = some (n, idx, tbl) ∧
      evalSpecExpr resolve (List.range n) tbl ty.dagDepth idx = some ty' := by
  obtain ⟨idx, tbl, hb, -, hev⟩ := buildSpecExpr_spec resolve (List.range n) ty {} hwf hsub
  refine ⟨idx, tbl, ?_, hev⟩
  simp [buildEqnType, hspec, hb]

/-- **Operation Equations (`buildOpEqs`) Member DAG Correspondence**:
For any `(n, lhs, rhs) ∈ roleClosedOpEqs r` with well-formed `lhs, rhs`, building its
`(lIdx, rIdx, tbl₂)` entry evaluates under any `resolve` (such as `t.keyOf`) to
`substRoleKeysM resolve lhs` and `substRoleKeysM resolve rhs`. -/
theorem buildOpEqEntry_spec (resolve : Role → Option (Key .anon))
    (n : Nat) (lhs rhs lhs' rhs' : Expr .anon)
    (hwfL : lhs.specClosedWF (List.range n) = Bool.true)
    (hwfR : rhs.specClosedWF (List.range n) = Bool.true)
    (hsubL : substRoleKeysM resolve lhs = some lhs')
    (hsubR : substRoleKeysM resolve rhs = some rhs') :
    ∃ lIdx rIdx tbl₁ tbl₂,
      buildSpecExpr (List.range n) lhs {} = some (lIdx, tbl₁) ∧
      buildSpecExpr (List.range n) rhs tbl₁ = some (rIdx, tbl₂) ∧
      evalSpecExpr resolve (List.range n) tbl₂ (Nat.max lhs.dagDepth rhs.dagDepth) lIdx = some lhs' ∧
      evalSpecExpr resolve (List.range n) tbl₂ (Nat.max lhs.dagDepth rhs.dagDepth) rIdx = some rhs' := by
  obtain ⟨lIdx, tbl₁, hbL, -, hevL⟩ := buildSpecExpr_spec resolve (List.range n) lhs {} hwfL hsubL
  obtain ⟨rIdx, tbl₂, hbR, hextR, hevR⟩ := buildSpecExpr_spec resolve (List.range n) rhs tbl₁ hwfR hsubR
  exact ⟨lIdx, rIdx, tbl₁, tbl₂, hbL, hbR,
    evalSpecExpr_mono hextR (Nat.le_max_left _ _) hevL,
    evalSpecExpr_mono (SpecExprTable.Extends.refl tbl₂) (Nat.le_max_right _ _) hevR⟩

/-- **Equation Statement (`buildEqnList`) Member DAG Correspondence**:
For any `(n, stmt) ∈ roleClosedStatements r` with well-formed `stmt`, building its
`(idx, tbl)` entry evaluates under any `resolve` (such as `t.keyOf`) to
`substRoleKeysM resolve stmt`. -/
theorem buildEqnStatementEntry_spec (resolve : Role → Option (Key .anon))
    (n : Nat) (stmt stmt' : Expr .anon)
    (hwf : stmt.specClosedWF (List.range n) = Bool.true)
    (hsub : substRoleKeysM resolve stmt = some stmt') :
    ∃ idx tbl,
      buildSpecExpr (List.range n) stmt {} = some (idx, tbl) ∧
      evalSpecExpr resolve (List.range n) tbl stmt.dagDepth idx = some stmt' := by
  obtain ⟨idx, tbl, hb, -, hev⟩ := buildSpecExpr_spec resolve (List.range n) stmt {} hwf hsub
  exact ⟨idx, tbl, hb, hev⟩

/-- **Block Member (`buildRoleBlockExpected`) DAG Correspondence**:
For any declaration `d` in `Spec.block decls` with well-formed `d.toConstantVal.type`,
building its `(idx, tbl)` entry evaluates under any `resolve` (such as `t.keyOf`) to
`substRoleKeysM resolve d.toConstantVal.type`. -/
theorem buildRoleBlockMember_spec (resolve : Role → Option (Key .anon))
    (d : ConstantInfo .anon) {ty' : Expr .anon}
    (hwf : d.toConstantVal.type.specClosedWF d.toConstantVal.levelParams = Bool.true)
    (hsub : substRoleKeysM resolve d.toConstantVal.type = some ty') :
    ∃ idx tbl,
      buildSpecExpr d.toConstantVal.levelParams d.toConstantVal.type {} = some (idx, tbl) ∧
      evalSpecExpr resolve d.toConstantVal.levelParams tbl d.toConstantVal.type.dagDepth idx = some ty' := by
  obtain ⟨idx, tbl, hb, -, hev⟩ :=
    buildSpecExpr_spec resolve d.toConstantVal.levelParams d.toConstantVal.type {} hwf hsub
  exact ⟨idx, tbl, hb, hev⟩

/-- Check that every expression in `r.spec` (anchor type, axiom type, operation/equation
type, closed equation sides, closed statements, and block member types) satisfies
`Expr.specClosedWF`. -/
def Role.specAllClosedWF (r : Role) : Bool :=
  (match r.spec (md := .anon) with
   | .block decls => decls.all fun d => d.toConstantVal.type.specClosedWF d.toConstantVal.levelParams
   | .anchor n ty => ty.specClosedWF (List.range n)
   | .ops ty _ => ty.specClosedWF []
   | .axiom n (some ty) => ty.specClosedWF (List.range n)
   | .axiom _ none => Bool.true
   | .eqns n ty _ => ty.specClosedWF (List.range n)) &&
  (roleClosedOpEqs r).all (fun (n, l, rhs) =>
    l.specClosedWF (List.range n) && rhs.specClosedWF (List.range n)) &&
  (roleClosedStatements r).all (fun (n, stmt) => stmt.specClosedWF (List.range n))

set_option maxRecDepth 65536 in
/-- **Every `Role` has well-formed closed specification terms.** -/
theorem Role.specAllClosedWF_eq_true (r : Role) : r.specAllClosedWF = Bool.true := by
  cases r <;> decide

/-- **Every role in `Role.all` has well-formed closed specification terms.** -/
theorem Role.all_specAllClosedWF : (Role.all.all Role.specAllClosedWF) = Bool.true := by
  rw [List.all_eq_true]
  intro r _
  exact r.specAllClosedWF_eq_true

end Ix.Kernel
