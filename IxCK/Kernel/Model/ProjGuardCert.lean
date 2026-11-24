module

public import IxCK.Kernel.Model.GuardClassifier
public import IxCK.Kernel.Model.Inductives.StructEntryFree
public import IxCK.Kernel.Verify.Inductives.StructPartsInv
public import IxCK.Kernel.Rules.Rel

@[expose] public section

/-!
# The projection guard as a certificate per projection table

A projection out of a structure in `Prop` is typed only where the projected field, and every
earlier field a later field mentions, is a proof. The rules tier states this at a use as
`Rules.FireSem`: a condition on the stored table entry's guard level, the stored structure sort
and the use's levels. It mentions no environment, store or validation limit.

This module states what has to be recorded for one projection table so that `FireSem` follows at
every later use, and proves that it does.

* `fieldSignatures look fuel nP nF ctx raw`: the field classifier (`sortSignature`) run over the
  `nF` field domains of a raw constructor telescope after its `nP` parameters, each domain in the
  context of the binders before it. This is the walk of the installing check and of every use.
* `ProjGuardCert look raw cty tbl`: **the certificate**. The table's guards are
  `structProjGuards` at the stored constructor type `cty` and some field sorts `sorts` (the
  caller of the install chooses them: `checkNativeTable`'s `sortss` argument), and each of those
  sorts has the zero-set of the classifier's signature of the same field of the raw telescope
  `raw`, over the lookup `look`.
* `ProjGuardUse look raw cty nP f g`: **what one use observes**. The use's guard level `g` is the
  join of the field's own sort and the sorts of the flagged earlier fields; the flags cover the
  earlier fields a later field mentions; and each sort joined has the zero-set of the
  classifier's signature of its field, over the use's lookup.
* `ProjGuardCert.fireSem`: **the certificate and a use give `FireSem`**, whenever the two lookups
  have a common extension. The use's own sorts need no typing reading: only their zero-sets
  enter, through the two comparisons with one classifier value.

The classifier is a function of the raw syntax and of the positive answers of the lookup
(`sortSignature_mono`), and extra depth does not change a successful answer
(`sortSignature_le`), so the certificate is stable under extending the lookup
(`ProjGuardCert.mono`) and the two runs may use different depths.
-/

namespace Ix.Kernel.GuardClassifier

variable {md : Mode}

private theorem bind_keeps {α β : Type} {a b : Option α} {f g : α → Option β}
    (ha : ∀ x, a = some x → b = some x)
    (hf : ∀ x y, f x = some y → g x = some y)
    {r : β} (h : a.bind f = some r) : b.bind g = some r := by
  obtain ⟨x, hx, hr⟩ := Option.bind_eq_some_iff.mp h
  exact Option.bind_eq_some_iff.mpr ⟨x, ha x hx, hf x r hr⟩

/-! ## Depth -/

/-- Extra depth cannot change a successful signature. -/
theorem sortSignature_succ (look : Lookup md) {fuel : Nat} {ctx : List (Expr md)} {e : Expr md}
    {s : Level} (h : sortSignature look fuel ctx e = some s) :
    sortSignature look (fuel + 1) ctx e = some s := by
  refine bind_keeps (fun t ht => infer_succ look fuel ctx e t ht) ?_ h
  intro t r hr
  exact bind_keeps (fun t' ht' => head_succ look fuel t t' ht') (fun _ _ hx => hx) hr

/-- A successful signature is the signature at every larger depth. -/
theorem sortSignature_le (look : Lookup md) {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {ctx : List (Expr md)} {e : Expr md} {s : Level}
    (h : sortSignature look fuel ctx e = some s) : sortSignature look fuel' ctx e = some s := by
  induction hle with
  | refl => exact h
  | step _ ih => exact sortSignature_succ look ih

/-! ## The classifier's clauses, for computing a signature by hand -/

theorem infer_const (look : Lookup md) (fuel : Nat) (ctx : List (Expr md)) (k : Key md)
    (us : List Level) : infer look (fuel + 1) ctx (.const k us) = look.typeOf k us := rfl

theorem infer_bvar (look : Lookup md) (fuel : Nat) (ctx : List (Expr md)) (i : Nat) :
    infer look (fuel + 1) ctx (.bvar i) = (ctx[i]?).map (Expr.liftLooseBVars (i + 1) 0) := rfl

theorem head_sort (look : Lookup md) (fuel : Nat) (u : Level) :
    head look (fuel + 1) (.sort u) = some (.sort u) := rfl

theorem head_forallE (look : Lookup md) (fuel : Nat) (ty body : Expr md) (m : BinderMeta) :
    head look (fuel + 1) (.forallE ty body m) = some (.forallE ty body m) := rfl

/-- An application: the function's shape exposes a `∀`, whose body is instantiated. -/
theorem infer_app {look : Lookup md} {fuel : Nat} {ctx : List (Expr md)}
    {f arg tf dom body : Expr md} {m : BinderMeta}
    (hf : infer look fuel ctx f = some tf)
    (hh : head look fuel tf = some (.forallE dom body m)) :
    infer look (fuel + 1) ctx (.app f arg) = some (body.instantiate1Lift arg) := by
  simp [infer, hf, hh]

/-- A `∀`: the body's shape exposes a sort, which is the sort kept. -/
theorem infer_forallE {look : Lookup md} {fuel : Nat} {ctx : List (Expr md)}
    {ty body tb : Expr md} {m : BinderMeta} {u : Level}
    (hb : infer look fuel (ty :: ctx) body = some tb)
    (hh : head look fuel tb = some (.sort u)) :
    infer look (fuel + 1) ctx (.forallE ty body m) = some (.sort u) := by
  simp [infer, hb, hh]

/-- The signature of a term whose shape exposes a sort. -/
theorem sortSignature_of {look : Lookup md} {fuel : Nat} {ctx : List (Expr md)}
    {e t : Expr md} {u : Level}
    (hi : infer look fuel ctx e = some t) (hh : head look fuel t = some (.sort u)) :
    sortSignature look fuel ctx e = some (Level.guardSignatureLevel u) := by
  simp [sortSignature, hi, hh]

/-! ## The classifier over a constructor telescope -/

/-- **The signatures of the next `n` binder domains** of a raw telescope: each domain is
classified in the context of the binders before it, newest first, and then joins that
context. A term that is not a `∀` where a binder is expected has no answer. -/
def domainSignatures (look : Lookup md) (fuel : Nat) :
    Nat → List (Expr md) → Expr md → Option (List Level)
  | 0, _, _ => some []
  | n + 1, ctx, .forallE dom body _ =>
    (sortSignature look fuel ctx dom).bind fun s =>
      (domainSignatures look fuel n (dom :: ctx) body).map (s :: ·)
  | _ + 1, _, _ => none

/-- **The signatures of the `nF` fields of a raw constructor telescope** after its `nP`
parameters, whose domains only join the context. -/
def fieldSignatures (look : Lookup md) (fuel : Nat) :
    Nat → Nat → List (Expr md) → Expr md → Option (List Level)
  | 0, nF, ctx, e => domainSignatures look fuel nF ctx e
  | nP + 1, nF, ctx, .forallE dom body _ => fieldSignatures look fuel nP nF (dom :: ctx) body
  | _ + 1, _, _, _ => none

theorem domainSignatures_cons {look : Lookup md} {fuel n : Nat} {ctx : List (Expr md)}
    {dom body : Expr md} {m : BinderMeta} {s : Level} {l : List Level}
    (hs : sortSignature look fuel ctx dom = some s)
    (hl : domainSignatures look fuel n (dom :: ctx) body = some l) :
    domainSignatures look fuel (n + 1) ctx (.forallE dom body m) = some (s :: l) := by
  simp [domainSignatures, hs, hl]

/-- The walk keeps its answer when every signature it computes is kept. -/
theorem domainSignatures_keeps {a b : Lookup md} {fuel fuel' : Nat}
    (hs : ∀ ctx e s, sortSignature a fuel ctx e = some s → sortSignature b fuel' ctx e = some s) :
    ∀ (n : Nat) (ctx : List (Expr md)) (e : Expr md) (l : List Level),
      domainSignatures a fuel n ctx e = some l → domainSignatures b fuel' n ctx e = some l := by
  intro n
  induction n with
  | zero => intro ctx e l h; exact h
  | succ n ih =>
    intro ctx e l h
    cases e <;> simp only [domainSignatures] at h ⊢
    case forallE dom body m =>
      refine bind_keeps (fun s h' => hs ctx dom s h') ?_ h
      intro s r hr
      obtain ⟨l', hl', hcons⟩ := Option.map_eq_some_iff.mp hr
      exact Option.map_eq_some_iff.mpr ⟨l', ih _ _ _ hl', hcons⟩
    all_goals first | exact h | exact nomatch h

theorem fieldSignatures_keeps {a b : Lookup md} {fuel fuel' : Nat}
    (hs : ∀ ctx e s, sortSignature a fuel ctx e = some s → sortSignature b fuel' ctx e = some s) :
    ∀ (nP nF : Nat) (ctx : List (Expr md)) (e : Expr md) (l : List Level),
      fieldSignatures a fuel nP nF ctx e = some l → fieldSignatures b fuel' nP nF ctx e = some l := by
  intro nP
  induction nP with
  | zero => intro nF ctx e l h; exact domainSignatures_keeps hs nF ctx e l h
  | succ nP ih =>
    intro nF ctx e l h
    cases e <;> simp only [fieldSignatures] at h ⊢
    case forallE dom body m => exact ih nF _ _ l h
    all_goals first | exact h | exact nomatch h

/-- **The walk is stable under extending the lookup and raising the depth.** -/
theorem fieldSignatures_mono {a b : Lookup md} (hext : a.Extends b) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {nP nF : Nat} {ctx : List (Expr md)} {e : Expr md} {l : List Level}
    (h : fieldSignatures a fuel nP nF ctx e = some l) :
    fieldSignatures b fuel' nP nF ctx e = some l :=
  fieldSignatures_keeps
    (fun _ _ _ hs => sortSignature_le b hle (sortSignature_mono hext hs)) nP nF ctx e l h

private theorem getD_take {α : Type} (d : α) :
    ∀ (l : List α) (n j : Nat), j < n → (l.take n).getD j d = l.getD j d
  | [], n, _, _ => by cases n <;> rfl
  | _ :: _, 0, j, h => absurd h (Nat.not_lt_zero j)
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: l, n + 1, j + 1, h => getD_take d l n j (Nat.lt_of_succ_lt_succ h)

/-- The walk over fewer binders is the prefix of the walk over more. -/
theorem domainSignatures_take (look : Lookup md) (fuel : Nat) :
    ∀ (n k : Nat) (ctx : List (Expr md)) (e : Expr md) (l : List Level),
      domainSignatures look fuel (n + k) ctx e = some l →
      domainSignatures look fuel n ctx e = some (l.take n) := by
  intro n
  induction n with
  | zero => intro k ctx e l _; rfl
  | succ n ih =>
    intro k ctx e l h
    rw [show n + 1 + k = n + k + 1 by omega] at h
    cases e <;> simp only [domainSignatures] at h ⊢
    case forallE dom body m =>
      obtain ⟨s, hs, hr⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp hr
      exact Option.bind_eq_some_iff.mpr
        ⟨s, hs, Option.map_eq_some_iff.mpr ⟨l'.take n, ih k _ _ _ hl', rfl⟩⟩
    all_goals first | exact h | exact nomatch h

/-- **A use walks a prefix of the fields the install walked**: the signatures of the first
`nF` fields are the first `nF` of the signatures of `nF + k` fields. -/
theorem fieldSignatures_take (look : Lookup md) (fuel : Nat) :
    ∀ (nP nF k : Nat) (ctx : List (Expr md)) (e : Expr md) (l : List Level),
      fieldSignatures look fuel nP (nF + k) ctx e = some l →
      fieldSignatures look fuel nP nF ctx e = some (l.take nF) := by
  intro nP
  induction nP with
  | zero => intro nF k ctx e l h; exact domainSignatures_take look fuel nF k ctx e l h
  | succ nP ih =>
    intro nF k ctx e l h
    cases e <;> simp only [fieldSignatures] at h ⊢
    case forallE dom body m => exact ih nF k _ _ l h
    all_goals first | exact h | exact nomatch h

/-- **Two walks of one raw telescope agree on the fields both reach**, whatever their lookups
(with a common extension) and depths. -/
theorem fieldSignatures_agree {a b common : Lookup md} (ha : a.Extends common)
    (hb : b.Extends common) {fuel fuel' nP nF f : Nat} {raw : Expr md} {sigs sigs' : List Level}
    (hf : f < nF)
    (hs : fieldSignatures a fuel nP nF [] raw = some sigs)
    (hs' : fieldSignatures b fuel' nP (f + 1) [] raw = some sigs') :
    ∀ j, j ≤ f → sigs'.getD j .zero = sigs.getD j .zero := by
  have hc : fieldSignatures common (max fuel fuel') nP nF [] raw = some sigs :=
    fieldSignatures_mono ha (Nat.le_max_left fuel fuel') hs
  have hc' : fieldSignatures common (max fuel fuel') nP (f + 1) [] raw = some sigs' :=
    fieldSignatures_mono hb (Nat.le_max_right fuel fuel') hs'
  obtain ⟨k, hk⟩ : ∃ k, nF = f + 1 + k := ⟨nF - (f + 1), by omega⟩
  subst hk
  have hpre := fieldSignatures_take common (max fuel fuel') nP (f + 1) k [] raw sigs hc
  have hsame : sigs' = sigs.take (f + 1) := Option.some.inj (hc'.symm.trans hpre)
  intro j hj
  rw [hsame]
  exact getD_take Level.zero sigs (f + 1) j (by omega)

end Ix.Kernel.GuardClassifier

namespace Ix.Kernel

variable {md : Mode}

/-- **The projection guard's certificate for one projection table.**

`look` is the classifier's lookup of declared types and definition values; `raw` is the
constructor's type as the classifier reads it (de Bruijn syntax, the constructor's own level
parameters); `cty` is the stored constructor type the table's guards are computed at.

There are field sorts `sorts` such that the table's guards are `structProjGuards` at them, and
each has the zero-set of the classifier's signature of its field. Nothing here mentions an
environment, a store, a role context or a validation limit. -/
structure ProjGuardCert (look : GuardClassifier.Lookup md) (raw cty : Expr md)
    (tbl : ProjTable md) : Prop where
  cert : ∃ (sorts sigs : List Level) (fuel : Nat),
    tbl.guards = structProjGuards cty tbl.numParams tbl.numFields sorts ∧
    GuardClassifier.fieldSignatures look fuel tbl.numParams tbl.numFields [] raw = some sigs ∧
    ∀ j, j < tbl.numFields → ∀ φ : LevelParam → Nat,
      Level.eval φ (sorts.getD j .zero) = 0 ↔ Level.eval φ (sigs.getD j .zero) = 0

/-- The certificate is kept by every lookup that keeps the positive answers. -/
theorem ProjGuardCert.mono {look look' : GuardClassifier.Lookup md} {raw cty : Expr md}
    {tbl : ProjTable md} (hext : look.Extends look') (h : ProjGuardCert look raw cty tbl) :
    ProjGuardCert look' raw cty tbl := by
  obtain ⟨sorts, sigs, fuel, hguards, hsig, hz⟩ := h.cert
  exact ⟨sorts, sigs, fuel, hguards,
    GuardClassifier.fieldSignatures_mono hext (Nat.le_refl fuel) hsig, hz⟩

/-- **What one projection use observes**, at field `f` of a structure with `nP` parameters:
sorts `lus` for the fields `0, …, f`, the guard level `g` computed from them, and the
classifier's signatures of those fields over the use's lookup.

* each sort has the zero-set of its field's signature;
* `g` is the sort of field `f` joined, in field order, with the sorts of the flagged earlier
  fields;
* an earlier field that a later field mentions (`structUsedLater` at the stored constructor
  type) is flagged.

The sorts are whatever levels the use computed: no typing reading of them is asked. -/
structure ProjGuardUse (look : GuardClassifier.Lookup md) (raw cty : Expr md) (nP f : Nat)
    (g : Level) : Prop where
  obs : ∃ (lus sigs : List Level) (fuel : Nat) (flags : Nat → Bool),
    GuardClassifier.fieldSignatures look fuel nP (f + 1) [] raw = some sigs ∧
    (∀ j, j ≤ f → ∀ φ : LevelParam → Nat,
      Level.eval φ (lus.getD j .zero) = 0 ↔ Level.eval φ (sigs.getD j .zero) = 0) ∧
    (∀ j, j < f → structUsedLater cty nP j = true → flags j = true) ∧
    g = (List.range f).foldl
      (fun acc j => if flags j then Level.max acc (lus.getD j .zero) else acc)
      (lus.getD f .zero)

/-- **The certificate and a use give the rules tier's firing condition.** The install's and
the use's lookups need only a common extension; the depths may differ; the use's levels `us`
are arbitrary. -/
theorem ProjGuardCert.fireSem {look look' common : GuardClassifier.Lookup md}
    {raw cty : Expr md} {tbl : ProjTable md} {f : Nat} {g : Level} {us : List Level}
    (cert : ProjGuardCert look raw cty tbl)
    (hl : look.Extends common) (hl' : look'.Extends common)
    (use : ProjGuardUse look' raw cty tbl.numParams f g) (hf : f < tbl.numFields)
    (hzero : ∀ φ : LevelParam → Nat, Level.eval φ (Level.subst tbl.levelParams us g) = 0) :
    Rules.FireSem (tbl.entry f) us := by
  obtain ⟨sorts, sigs, fuel, hguards, hsig, hz⟩ := cert.cert
  obtain ⟨lus, sigs', fuel', flags, hsig', hz', hflags, rfl⟩ := use.obs
  have hsame := GuardClassifier.fieldSignatures_agree hl hl' hf hsig hsig'
  have key : ∀ j, j ≤ f → ∀ ψ : LevelParam → Nat,
      Level.eval ψ (lus.getD j .zero) = 0 → Level.eval ψ (sorts.getD j .zero) = 0 := by
    intro j hj ψ h
    have h' := (hz' j hj ψ).mp h
    rw [hsame j hj] at h'
    exact (hz j (by omega) ψ).mpr h'
  intro _ φ
  show Level.eval φ (Level.subst tbl.levelParams us (tbl.guards.getD f .zero)) = 0
  have h0 := hzero φ
  rw [Level.eval_subst] at h0 ⊢
  rw [Model.eval_foldl_max_if_zero_iff _ flags (fun j => lus.getD j .zero)] at h0
  rw [hguards, structProjGuards_getD _ _ _ _ hf,
    Model.eval_foldl_max_if_zero_iff _ (structUsedLater cty tbl.numParams)
      (fun j => sorts.getD j .zero)]
  exact ⟨key f (Nat.le_refl f) _ h0.1, fun j hj hu =>
    key j (Nat.le_of_lt (List.mem_range.mp hj)) _
      (h0.2 j hj (hflags j (List.mem_range.mp hj) hu))⟩

end Ix.Kernel
