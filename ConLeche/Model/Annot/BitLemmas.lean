module

public import ConLeche.Model.Annot.Bit

public section

/-!
# The `denoteMeta` lemma battery (task #161, P3.2)

The Steps ladder consumes `denoteAnnot` through a fixed lemma surface —
clause equations, inversions, the depth shift, the environment
crossing — stated and proved at `DefEqRun.lean`'s prelude,
`Dispatch.lean`, and `Denote2Extend.lean`.  This file is that surface
for `denoteMeta`, mirror by mirror, with the systematic deltas of the
validated-annotation reading:

* **no fuel parameter** — the fuel-monotonicity/cross-fuel/`fuelDown`
  family has no mirror because there is nothing to be monotone in;
* **no sort-run conjuncts** — the binder inversions conclude
  `ea = .pi 0 (pwBit φ mb.pw) ta ba` (resp. `.lam (pwBit φ mb.pw)`)
  *definitionally*, where `denoteAnnot`'s conclude `sortOfE`/`lamSortE`
  successes;
* **premises that existed only to move a sort run are dropped** —
  `EnvWF` in the depth shift, `SortAgree` in the environment crossing.
  A premise kept by a mirror is one the *reading itself* needs
  (`hacl`: leaf lift-invariance; `FindPreserved`/`LitGuardsAgree`:
  the constant and literal clauses read the environment).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level PropWhen ProjEntry)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## Clause equations -/

theorem denoteMeta_sort (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (u : Level) :
    denoteMeta acval env φ d (.sort u) = some (.sort (u.eval φ)) := by
  rw [denoteMeta]

theorem denoteMeta_fvar (acval : Name → (Name → Nat) → AnnotTerm)
    (d idx : Nat) (ty : Expr) :
    denoteMeta acval env φ d (.fvar idx ty)
      = some (.bvar (d - 1 - idx)) := by
  rw [denoteMeta]

theorem denoteMeta_const {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    (hf : env.find? n = some ci)
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    denoteMeta acval env φ d (.const n us)
      = some (acval n
          (Level.substFn φ ci.toConstantVal.levelParams us)) := by
  rw [denoteMeta, hf]
  simp [hlen]

theorem denoteMeta_app (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (f a : Expr) :
    denoteMeta acval env φ d (.app f a)
      = (do
        let fa ← denoteMeta acval env φ d f
        let aa ← denoteMeta acval env φ d a
        some (.app fa aa)) := by
  rw [denoteMeta]

theorem denoteMeta_proj (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (s : Name) (i : Nat) (e : Expr) :
    denoteMeta acval env φ d (.proj s i e)
      = (do
        let ea ← denoteMeta acval env φ d e
        match env.findProj? s i with
        | some entry => some (projAV (i + entry.off) ea)
        | none => AnnotTerm.projPair? i ea) := by
  rw [denoteMeta]
  rfl

/-- The clause at an absent entry — the pre-W3 shape, for consumers
holding an absence fact. -/
theorem denoteMeta_proj_pair (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (s : Name) (i : Nat) (e : Expr)
    (hnt : env.findProj? s i = none) :
    denoteMeta acval env φ d (.proj s i e)
      = (do
        let ea ← denoteMeta acval env φ d e
        AnnotTerm.projPair? i ea) := by
  rw [denoteMeta_proj]
  cases he : denoteMeta acval env φ d e with
  | none => rfl
  | some ea =>
    show (match env.findProj? s i with
      | some entry => some (projAV (i + entry.off) ea)
      | none => AnnotTerm.projPair? i ea)
        = AnnotTerm.projPair? i ea
    rw [hnt]

theorem denoteMeta_forallE (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (ty body : Expr) (mb : ConLeche.BinderMeta) :
    denoteMeta acval env φ d (.forallE ty body mb)
      = (do
        let ta ← denoteMeta acval env φ d ty
        let ba ← denoteMeta acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty))
        some (.pi 0 (pwBit φ mb.pw) ta ba)) := by
  rw [denoteMeta]

theorem denoteMeta_lam (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (ty body : Expr) (mb : ConLeche.BinderMeta) :
    denoteMeta acval env φ d (.lam ty body mb)
      = (do
        let ta ← denoteMeta acval env φ d ty
        let ba ← denoteMeta acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty))
        some (.lam (pwBit φ mb.pw) ta ba)) := by
  rw [denoteMeta]

theorem denoteMeta_natLit {acval : Name → (Name → Nat) → AnnotTerm}
    {d n : Nat} (hg : natLitSupported env = true) :
    denoteMeta acval env φ d (.lit (.natVal n))
      = some (natLitAV (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] [])) n) := by
  rw [denoteMeta, if_pos hg]

/-! ## Inversions -/

theorem denoteMeta_app_inv {d : Nat} {f a : Expr} {ea : AnnotTerm}
    (h : denoteMeta acval env φ d (.app f a) = some ea) :
    ∃ fa aa, denoteMeta acval env φ d f = some fa ∧
      denoteMeta acval env φ d a = some aa ∧ ea = .app fa aa := by
  rw [denoteMeta] at h
  cases hf : denoteMeta acval env φ d f with
  | none => rw [hf] at h; exact nomatch h
  | some fa =>
    cases ha : denoteMeta acval env φ d a with
    | none => rw [hf, ha] at h; exact nomatch h
    | some aa =>
      rw [hf, ha] at h
      exact ⟨fa, aa, rfl, rfl, (Option.some.inj h).symm⟩

theorem denoteMeta_proj_inv {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {ea : AnnotTerm}
    (h : denoteMeta acval env φ d (.proj s i e) = some ea) :
    ∃ ia, denoteMeta acval env φ d e = some ia ∧
      ((∃ entry, env.findProj? s i = some entry ∧ ea = projAV (i + entry.off) ia) ∨
       (env.findProj? s i = none ∧ AnnotTerm.projPair? i ia = some ea)) := by
  rw [denoteMeta] at h
  cases he : denoteMeta acval env φ d e with
  | none => rw [he] at h; exact nomatch h
  | some ia =>
    rw [he] at h
    replace h : (match env.findProj? s i with
        | some entry => some (projAV (i + entry.off) ia)
        | none => AnnotTerm.projPair? i ia)
          = some ea := h
    cases hfp : env.findProj? s i with
    | some entry =>
      rw [hfp] at h
      dsimp only at h
      exact ⟨ia, rfl, Or.inl ⟨entry, rfl, (Option.some.inj h).symm⟩⟩
    | none =>
      rw [hfp] at h
      dsimp only at h
      exact ⟨ia, rfl, Or.inr ⟨rfl, h⟩⟩

/-- The inversion at an absent entry — the pre-W3 shape, for consumers
holding an absence fact. -/
theorem denoteMeta_proj_inv_pair {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {ea : AnnotTerm}
    (hnt : env.findProj? s i = none)
    (h : denoteMeta acval env φ d (.proj s i e) = some ea) :
    ∃ ia, denoteMeta acval env φ d e = some ia ∧
      AnnotTerm.projPair? i ia = some ea := by
  obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv h
  rcases hcase with ⟨entry, hfp, -⟩ | ⟨-, hdec⟩
  · rw [hnt] at hfp; exact nomatch hfp
  · exact ⟨ia, hia, hdec⟩

theorem denoteMeta_forallE_inv {d : Nat} {ty bd : Expr}
    {mb : ConLeche.BinderMeta} {ea : AnnotTerm}
    (h : denoteMeta acval env φ d (.forallE ty bd mb) = some ea) :
    ∃ ta ba, denoteMeta acval env φ d ty = some ta ∧
      denoteMeta acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) = some ba ∧
      ea = .pi 0 (pwBit φ mb.pw) ta ba := by
  rw [denoteMeta] at h
  cases ht : denoteMeta acval env φ d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
    cases hb : denoteMeta acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) with
    | none => rw [ht, hb] at h; exact nomatch h
    | some ba =>
      rw [ht, hb] at h
      exact ⟨ta, ba, rfl, rfl, (Option.some.inj h).symm⟩

theorem denoteMeta_lam_inv {d : Nat} {ty bd : Expr}
    {mb : ConLeche.BinderMeta} {ea : AnnotTerm}
    (h : denoteMeta acval env φ d (.lam ty bd mb) = some ea) :
    ∃ ta ba, denoteMeta acval env φ d ty = some ta ∧
      denoteMeta acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) = some ba ∧
      ea = .lam (pwBit φ mb.pw) ta ba := by
  rw [denoteMeta] at h
  cases ht : denoteMeta acval env φ d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
    cases hb : denoteMeta acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) with
    | none => rw [ht, hb] at h; exact nomatch h
    | some ba =>
      rw [ht, hb] at h
      exact ⟨ta, ba, rfl, rfl, (Option.some.inj h).symm⟩

theorem denoteMeta_natLit_inv {d n : Nat} {ea : AnnotTerm}
    (h : denoteMeta acval env φ d (.lit (.natVal n)) = some ea) :
    natLitSupported env = true ∧
      ea = natLitAV (acval natZeroName (Level.substFn φ [] []))
        (acval natSuccName (Level.substFn φ [] [])) n := by
  rw [denoteMeta] at h
  split at h
  · next hg => exact ⟨hg, (Option.some.inj h).symm⟩
  · exact nomatch h

/-! ## The spine kit (from `Model/Steps/{Stuck,CapsRows,IotaRows,TowerKit}.lean`,
task #305 closing)

`DenoteSpine`/`denote_mkAppN_inv` (`Verify/Denote/Tele.lean`) at the
validated reading.  Fuel-free, so the inversion is one induction and
the reconciliation of two readings is `Option.some.inj`.  Collected
here at the task #305 closing, from the four `Model/Steps` rows that
grew it; each statement and proof is the one it carried there. -/

/-- Each expression of a spine reads to the corresponding annotation
(`DenoteSpine`'s P transpose). -/
inductive DenoteMetaSpine (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (d : Nat) :
    List Expr → List AnnotTerm → Prop
  | nil : DenoteMetaSpine acval env φ d [] []
  | cons {a : Expr} {v : AnnotTerm} {as : List Expr} {vs : List AnnotTerm} :
      denoteMeta acval env φ d a = some v →
      DenoteMetaSpine acval env φ d as vs →
      DenoteMetaSpine acval env φ d (a :: as) (v :: vs)

/-- A member of a read spine reads (`DenoteMetaSpine`'s membership form —
the shape the projection clause's `getD` selection needs).  Relocated
from the retired `Steps/ProjPinsP.lean` (task #175 W6). -/
theorem DenoteMetaSpine.mem {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) :
    ∀ x ∈ as, ∃ v, denoteMeta acval env φ d x = some v := by
  induction h with
  | nil => intro x hx; exact nomatch hx
  | cons ha _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, ha⟩
    · exact ih x hx'

/-- A read spine has the length of its source. -/
theorem DenoteMetaSpine.length {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) : as.length = vs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- **The application spine, inverted at the validated reading**: the
head and every argument read, and the value is their `AnnotTerm`
application.  `denote_mkAppN_inv` without the fuel. -/
theorem denoteMeta_mkAppN_inv {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} : ∀ {as : List Expr} {f : Expr} {ea : AnnotTerm},
    denoteMeta acval env φ d (Expr.mkAppN f as) = some ea →
    ∃ fa vs, denoteMeta acval env φ d f = some fa ∧
      DenoteMetaSpine acval env φ d as vs ∧ ea = AnnotTerm.mkAppN fa vs := by
  intro as
  induction as with
  | nil => intro f ea h; exact ⟨ea, [], h, .nil, rfl⟩
  | cons a as ih =>
    intro f ea h
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := ih h
    obtain ⟨ff, aa, hff, haa, rfl⟩ := denoteMeta_app_inv hfa
    exact ⟨ff, aa :: vs, hff, .cons haa hsp, rfl⟩

theorem DenoteMetaSpine.take {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) :
    ∀ n, DenoteMetaSpine acval env φ d (as.take n) (vs.take n) := by
  induction h with
  | nil => intro n; simpa using DenoteMetaSpine.nil
  | @cons a v as vs ha _ ih =>
    intro n
    cases n with
    | zero => exact DenoteMetaSpine.nil
    | succ n => exact DenoteMetaSpine.cons ha (ih n)

theorem DenoteMetaSpine.drop {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) :
    ∀ n, DenoteMetaSpine acval env φ d (as.drop n) (vs.drop n) := by
  induction h with
  | nil => intro n; simpa using DenoteMetaSpine.nil
  | @cons a v as vs ha htl ih =>
    intro n
    cases n with
    | zero => exact DenoteMetaSpine.cons ha htl
    | succ n => exact ih n

theorem DenoteMetaSpine.append {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as bs : List Expr} {vs ws : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs)
    (h2 : DenoteMetaSpine acval env φ d bs ws) :
    DenoteMetaSpine acval env φ d (as ++ bs) (vs ++ ws) := by
  induction h with
  | nil => exact h2
  | cons ha _ ih => exact DenoteMetaSpine.cons ha ih

/-- A mapped spine reads pointwise (`DenoteSpine.map_list`'s mirror). -/
theorem DenoteMetaSpine.map_list {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {β : Type _} {g : β → Expr} {G : β → AnnotTerm} :
    ∀ l : List β, (∀ j ∈ l, denoteMeta acval env φ d (g j) = some (G j)) →
      DenoteMetaSpine acval env φ d (l.map g) (l.map G) := by
  intro l
  induction l with
  | nil => intro _; exact DenoteMetaSpine.nil
  | cons x xs ih =>
    intro h
    exact DenoteMetaSpine.cons (h x (by simp))
      (ih fun j hj => h j (by simp [hj]))

/-- **The application spine reads, constructing direction** —
`denoteMeta_mkAppN_inv`'s converse, the one the fabricated projection
spine needs. -/
theorem denoteMeta_mkAppN {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) :
    ∀ {f : Expr} {fa : AnnotTerm}, denoteMeta acval env φ d f = some fa →
      denoteMeta acval env φ d (Expr.mkAppN f as) = some (AnnotTerm.mkAppN fa vs) := by
  induction h with
  | nil => intro f fa hf; exact hf
  | cons ha _ ih =>
    intro f fa hf
    exact ih (by rw [denoteMeta_app, hf, ha]; rfl)

/-- A read spine reads at every slot. -/
theorem DenoteMetaSpine.getD {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {as : List Expr} {vs : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs) :
    ∀ (dflt : Expr) (i : Nat), i < as.length →
      denoteMeta acval env φ d (as.getD i dflt) = some (vs.getD i default) := by
  induction h with
  | nil => intro dflt i hi; exact absurd hi (by simp)
  | @cons a v as vs ha _ ih =>
    intro dflt i hi
    match i with
    | 0 => exact ha
    | j + 1 => exact ih dflt j (by simpa using hi)

/-- The clause at a stored entry: the uniform iterated projection of
the subject's reading. -/
theorem denoteMeta_proj_tower {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {entry : ProjEntry} {ia : AnnotTerm}
    (hfe : env.findProj? s i = some entry)
    (he : denoteMeta acval env φ d e = some ia) :
    denoteMeta acval env φ d (.proj s i e) = some (projAV (i + entry.off) ia) := by
  rw [denoteMeta_proj, he]
  show (match env.findProj? s i with
    | some entry => some (projAV (i + entry.off) ia)
    | none => AnnotTerm.projPair? i ia)
      = some (projAV (i + entry.off) ia)
  rw [hfe]

/-- The inversion at a stored entry. -/
theorem denoteMeta_proj_inv_tower {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {entry : ProjEntry} {ea : AnnotTerm}
    (hfe : env.findProj? s i = some entry)
    (h : denoteMeta acval env φ d (.proj s i e) = some ea) :
    ∃ ia, denoteMeta acval env φ d e = some ia ∧ ea = projAV (i + entry.off) ia := by
  obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv h
  rcases hcase with ⟨entry', hfe', rfl⟩ | ⟨hnt, -⟩
  · obtain rfl : entry = entry' := Option.some.inj (hfe.symm.trans hfe')
    exact ⟨ia, hia, rfl⟩
  · rw [hnt] at hfe; exact nomatch hfe

/-- A read spine extended by one read argument. -/
theorem DenoteMetaSpine.snoc {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    {a : Expr} {v : AnnotTerm}
    (h : DenoteMetaSpine acval env φ d as vs)
    (ha : denoteMeta acval env φ d a = some v) :
    DenoteMetaSpine acval env φ d (as ++ [a]) (vs ++ [v]) := by
  induction h with
  | nil => exact .cons ha .nil
  | cons h1 _ ih => exact .cons h1 ih

/-- The `k`-th argument of a read spine reads to the `k`-th reading. -/
theorem DenoteMetaSpine.getD_read {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      ∀ {k : Nat}, k < as.length →
        denoteMeta acval env φ d (as.getD k (.bvar 0))
          = some (vs.getD k default)
  | _, _, .nil, k, hk => absurd hk (Nat.not_lt_zero k)
  | _, _, .cons ha _, 0, _ => by simpa [List.getD] using ha
  | _, _, .cons _ hsp, k + 1, hk => by
    simpa [List.getD] using
      DenoteMetaSpine.getD_read hsp (Nat.lt_of_succ_lt_succ hk)

end ConLeche.Model
