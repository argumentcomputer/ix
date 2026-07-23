import Ix.Tc.Subst
import Ix.Tc.Verify.Expr

/-!
# Subst slice: `lift`/`subst` walkers against pure specs

Second layer of the Expr slice: WalkM memo-soundness —
the `(addr, depth)`-keyed cache pattern proven in its simplest (pure
StateM) home before it recurs in every kernel cache.

Scope decision (recorded): the walker theorems are stated for
**`m = .anon`** — the v1 checking kernel's mode, where `internKey =
addr` (one collision-freedom domain serves the memo and the intern
table) and `eraseMeta` is the identity, so soundness is EXACT equality
with the spec, not equality up to erasure. Meta-mode intern transparency
is a separate `metaAddr`-collision obligation with no bearing on what
the checker accepts; it stays out of scope until a consumer needs it.

The composability answer: each theorem's collision-freedom
hypothesis quantifies over an abstract support `S` that the caller can
instantiate with the FINITE, spec-determined set
`LiftReach ∪ (initial intern support)` — the walk only ever compares,
stores, or interns members of that set, and intern-table growth stays
inside it. No constructor-closure (which would force an infinite,
pigeonhole-false support) is ever required.

Side conditions: `Constructed` (expressions built by the smart
constructors, with the `var`-index no-wrap bound folded into the `var`
rule) and UInt64 no-wrap bounds (`cutoff.toNat + e.size <
UInt64.size` for the binder-descent `cutoff + 1`s). An in-memory
expression cannot violate them; a 2⁶⁴-deep tower genuinely would.
-/

namespace Ix.Tc

variable {m : Mode}

namespace KExpr

/-- Node count — the structural measure for bound threading. -/
def size : KExpr m → Nat
  | .var .. | .fvar .. | .sort .. | .const .. | .nat .. | .str .. => 1
  | .app f a _ => f.size + a.size + 1
  | .lam _ _ ty body _ | .all _ _ ty body _ => ty.size + body.size + 1
  | .letE _ ty val body _ _ => ty.size + val.size + body.size + 1
  | .prj _ _ val _ => val.size + 1

theorem size_pos : ∀ e : KExpr m, 0 < e.size
  | .var .. | .fvar .. | .sort .. | .const .. | .nat .. | .str .. =>
    Nat.zero_lt_one
  | .app .. | .lam .. | .all .. | .letE .. | .prj .. =>
    Nat.succ_pos _

/-! ### Smart-constructor shape and info equations

The `mk*` constructors are `Id.run do` hash computations; each reduces to
a raw constructor applied to its computed `ExprInfo`. The shape lemmas
expose the constructor head (so `match`es in walker bodies reduce) while
keeping the info opaque; the field equations are the recorded coherence
facts (`lbr`/`count0`/`hasFVars` vs the children's). All are `rfl`. -/

theorem mkVar_shape (idx : UInt64) (name : m.F Name) (md : m.F (Array MData)) :
    mkVar idx name md = .var idx name (mkVar idx name md).info := rfl

theorem mkFVar_shape (id : FVarId) (name : m.F Name) (md : m.F (Array MData)) :
    mkFVar id name md = .fvar id name (mkFVar id name md).info := rfl

theorem mkSort_shape (u : KUniv m) (md : m.F (Array MData)) :
    mkSort u md = .sort u (mkSort u md).info := rfl

theorem mkConst_shape (id : KId m) (us : Array (KUniv m))
    (md : m.F (Array MData)) :
    mkConst id us md = .const id us (mkConst id us md).info := rfl

theorem mkApp_shape (f a : KExpr m) (md : m.F (Array MData)) :
    mkApp f a md = .app f a (mkApp f a md).info := rfl

theorem mkLam_shape (n : m.F Name) (bi : m.F Lean.BinderInfo)
    (ty body : KExpr m) (md : m.F (Array MData)) :
    mkLam n bi ty body md = .lam n bi ty body (mkLam n bi ty body md).info :=
  rfl

theorem mkAll_shape (n : m.F Name) (bi : m.F Lean.BinderInfo)
    (ty body : KExpr m) (md : m.F (Array MData)) :
    mkAll n bi ty body md = .all n bi ty body (mkAll n bi ty body md).info :=
  rfl

theorem mkLet_shape (n : m.F Name) (ty val body : KExpr m) (nd : Bool)
    (md : m.F (Array MData)) :
    mkLet n ty val body nd md
      = .letE n ty val body nd (mkLet n ty val body nd md).info := rfl

theorem mkPrj_shape (id : KId m) (field : UInt64) (val : KExpr m)
    (md : m.F (Array MData)) :
    mkPrj id field val md = .prj id field val (mkPrj id field val md).info :=
  rfl

theorem mkNat_shape (v : Nat) (blob : Address) (md : m.F (Array MData)) :
    mkNat v blob md = .nat v blob (mkNat v blob md).info := rfl

theorem mkStr_shape (v : String) (blob : Address) (md : m.F (Array MData)) :
    mkStr v blob md = .str v blob (mkStr v blob md).info := rfl

@[simp] theorem mkVar_lbr (idx : UInt64) (name : m.F Name) (md) :
    (mkVar idx name md).lbr = idx + 1 := rfl

@[simp] theorem mkFVar_lbr (id : FVarId) (name : m.F Name) (md) :
    (mkFVar id name md).lbr = 0 := rfl

@[simp] theorem mkSort_lbr (u : KUniv m) (md) : (mkSort u md).lbr = 0 := rfl

@[simp] theorem mkConst_lbr (id : KId m) (us : Array (KUniv m)) (md) :
    (mkConst id us md).lbr = 0 := rfl

@[simp] theorem mkApp_lbr (f a : KExpr m) (md) :
    (mkApp f a md).lbr = max f.lbr a.lbr := rfl

@[simp] theorem mkLam_lbr (n : m.F Name) (bi : m.F Lean.BinderInfo)
    (ty body : KExpr m) (md) :
    (mkLam n bi ty body md).lbr = max ty.lbr body.lbr.sat1 := rfl

@[simp] theorem mkAll_lbr (n : m.F Name) (bi : m.F Lean.BinderInfo)
    (ty body : KExpr m) (md) :
    (mkAll n bi ty body md).lbr = max ty.lbr body.lbr.sat1 := rfl

@[simp] theorem mkLet_lbr (n : m.F Name) (ty val body : KExpr m) (nd : Bool)
    (md) :
    (mkLet n ty val body nd md).lbr
      = max (max ty.lbr val.lbr) body.lbr.sat1 := rfl

@[simp] theorem mkPrj_lbr (id : KId m) (field : UInt64) (val : KExpr m) (md) :
    (mkPrj id field val md).lbr = val.lbr := rfl

@[simp] theorem mkNat_lbr (v : Nat) (blob : Address) (md) :
    (mkNat (m := m) v blob md).lbr = 0 := rfl

@[simp] theorem mkStr_lbr (v : String) (blob : Address) (md) :
    (mkStr (m := m) v blob md).lbr = 0 := rfl

/-- Expressions built by the smart constructors — the info-coherence
    carrier: every stored `ExprInfo` is the one its `mk*` computed from
    the (recursively constructed) children. The `var` rule carries the
    index no-wrap bound (`idx + 1` is `mkVar`'s `lbr`; at `idx = 2⁶⁴ - 1`
    it wraps to 0 and the `lbr ≤ cutoff` fast paths would misfire). -/
inductive Constructed : KExpr m → Prop where
  | var {idx : UInt64} {name : m.F Name} {md} :
    idx.toNat + 1 < UInt64.size → Constructed (mkVar idx name md)
  | fvar {id : FVarId} {name : m.F Name} {md} :
    Constructed (mkFVar id name md)
  | sort {u : KUniv m} {md} : Constructed (mkSort u md)
  | const {id : KId m} {us : Array (KUniv m)} {md} :
    Constructed (mkConst id us md)
  | app {f a : KExpr m} {md} :
    Constructed f → Constructed a → Constructed (mkApp f a md)
  | lam {n : m.F Name} {bi : m.F Lean.BinderInfo} {ty body : KExpr m} {md} :
    Constructed ty → Constructed body → Constructed (mkLam n bi ty body md)
  | all {n : m.F Name} {bi : m.F Lean.BinderInfo} {ty body : KExpr m} {md} :
    Constructed ty → Constructed body → Constructed (mkAll n bi ty body md)
  | letE {n : m.F Name} {ty val body : KExpr m} {nd : Bool} {md} :
    Constructed ty → Constructed val → Constructed body →
    Constructed (mkLet n ty val body nd md)
  | prj {id : KId m} {field : UInt64} {val : KExpr m} {md} :
    Constructed val → Constructed (mkPrj id field val md)
  | nat {v : Nat} {blob : Address} {md} : Constructed (mkNat v blob md)
  | str {v : String} {blob : Address} {md} : Constructed (mkStr v blob md)

end KExpr

/-! ### The pure `lift` spec -/

private theorem toNat_max (a b : UInt64) :
    (max a b).toNat = max a.toNat b.toNat := by
  show (if a ≤ b then b else a).toNat = max a.toNat b.toNat
  rw [Nat.max_def]
  split <;> split <;>
    first
      | rfl
      | (rename_i h1 h2
         exact absurd (UInt64.le_iff_toNat_le.mp h1) h2)
      | (rename_i h1 h2
         exact absurd h2 fun hh => h1 (UInt64.le_iff_toNat_le.mpr hh))

/-- Saturating decrement in `Nat` terms: `x ≤ x.sat1 + 1`. -/
private theorem toNat_le_sat1_add_one (x : UInt64) :
    x.toNat ≤ x.sat1.toNat + 1 := by
  unfold UInt64.sat1
  split
  · next h => rw [eq_of_beq h]; exact Nat.le_succ _
  · next h =>
    have hx0 : x ≠ 0 := fun he => h (beq_iff_eq.mpr he)
    have hn0 : x.toNat ≠ 0 := fun h0 =>
      hx0 (UInt64.toNat_inj.mp (by simpa using h0))
    have hsub : (x - 1).toNat = x.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le x 1 (UInt64.le_iff_toNat_le.mpr (by
        rw [show (1 : UInt64).toNat = 1 from rfl]; omega))]
      rfl
    omega

namespace KExpr

/-- Pure, memo-free, intern-free `lift`: shift free de Bruijn indices
    ≥ `cutoff` up by `shift`. Anon-mode spec — mirrors the rebuild arms of
    `liftCached` exactly (anon metadata fields are all `()`). -/
def liftSpec (e : KExpr .anon) (shift cutoff : UInt64) : KExpr .anon :=
  match e with
  | .var i name _ => if i ≥ cutoff then mkVar (i + shift) name else e
  | .app f a _ => mkApp (liftSpec f shift cutoff) (liftSpec a shift cutoff)
  | .lam n bi ty body _ =>
    mkLam n bi (liftSpec ty shift cutoff) (liftSpec body shift (cutoff + 1))
  | .all n bi ty body _ =>
    mkAll n bi (liftSpec ty shift cutoff) (liftSpec body shift (cutoff + 1))
  | .letE n ty val body nd _ =>
    mkLet n (liftSpec ty shift cutoff) (liftSpec val shift cutoff)
      (liftSpec body shift (cutoff + 1)) nd
  | .prj id field val _ => mkPrj id field (liftSpec val shift cutoff)
  | e => e

/-- The `lbr ≤ cutoff` fast path is sound: a constructed expression with no
    loose indices ≥ `cutoff` lifts to itself. The size bound feeds the
    binder-descent `cutoff + 1`s (no-wrap threading); the
    `var`-index bound comes from `Constructed`. -/
theorem liftSpec_id {e : KExpr .anon} {shift cutoff : UInt64}
    (hcon : Constructed e)
    (hcut : cutoff.toNat + e.size < UInt64.size)
    (hlbr : e.lbr ≤ cutoff) :
    liftSpec e shift cutoff = e := by
  induction hcon generalizing cutoff with
  | @var idx name md hidx =>
    rw [mkVar_lbr] at hlbr
    have hle : idx.toNat + 1 ≤ cutoff.toNat := by
      have h := UInt64.le_iff_toNat_le.mp hlbr
      rwa [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt hidx] at h
    have hlt : ¬ idx ≥ cutoff := fun hge => by
      have := UInt64.le_iff_toNat_le.mp hge
      omega
    rw [mkVar_shape, liftSpec, if_neg hlt]
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | @app f a md hf ha ihf iha =>
    rw [mkApp_lbr] at hlbr
    rw [mkApp_shape, size] at hcut
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    rw [mkApp_shape, liftSpec,
      ihf (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      iha (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.2)]
    exact mkApp_shape f a md
  | @lam n bi ty body md hty hbody ihty ihbody =>
    rw [mkLam_lbr] at hlbr
    rw [mkLam_shape, size] at hcut
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkLam_shape, liftSpec,
      ihty (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      ihbody (cutoff := cutoff + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkLam_shape n bi ty body md
  | @all n bi ty body md hty hbody ihty ihbody =>
    rw [mkAll_lbr] at hlbr
    rw [mkAll_shape, size] at hcut
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkAll_shape, liftSpec,
      ihty (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      ihbody (cutoff := cutoff + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkAll_shape n bi ty body md
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    rw [mkLet_lbr] at hlbr
    rw [mkLet_shape, size] at hcut
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, toNat_max, Nat.max_le, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkLet_shape, liftSpec,
      ihty (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.1.1),
      ihval (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.1.2),
      ihbody (cutoff := cutoff + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkLet_shape n ty val body nd md
  | @prj id field val md hval ihval =>
    rw [mkPrj_lbr] at hlbr
    rw [mkPrj_shape, size] at hcut
    rw [mkPrj_shape, liftSpec,
      ihval (cutoff := cutoff) (Nat.lt_of_le_of_lt (by omega) hcut) hlbr]
    exact mkPrj_shape id field val md
  | nat => rfl
  | str => rfl

/-- `shift = 0` fast path: lifting by zero is the identity on constructed
    expressions (no bounds needed — nothing is rebuilt with new indices,
    and both `if` branches of the `var` arm coincide). -/
theorem liftSpec_zero {e : KExpr .anon} (hcon : Constructed e)
    (cutoff : UInt64) : liftSpec e 0 cutoff = e := by
  induction hcon generalizing cutoff with
  | @var idx name md hidx =>
    rw [mkVar_shape, KExpr.liftSpec]
    split
    · rw [UInt64.add_zero]
      exact mkVar_shape idx name md
    · rfl
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | @app f a md hf ha ihf iha =>
    rw [mkApp_shape, liftSpec, ihf (cutoff := cutoff), iha (cutoff := cutoff)]
    exact mkApp_shape f a md
  | @lam n bi ty body md hty hbody ihty ihbody =>
    rw [mkLam_shape, liftSpec, ihty (cutoff := cutoff),
      ihbody (cutoff := cutoff + 1)]
    exact mkLam_shape n bi ty body md
  | @all n bi ty body md hty hbody ihty ihbody =>
    rw [mkAll_shape, liftSpec, ihty (cutoff := cutoff),
      ihbody (cutoff := cutoff + 1)]
    exact mkAll_shape n bi ty body md
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    rw [mkLet_shape, liftSpec, ihty (cutoff := cutoff),
      ihval (cutoff := cutoff), ihbody (cutoff := cutoff + 1)]
    exact mkLet_shape n ty val body nd md
  | @prj id field val md hval ihval =>
    rw [mkPrj_shape, liftSpec, ihval (cutoff := cutoff)]
    exact mkPrj_shape id field val md
  | nat => rfl
  | str => rfl

/-! ### The reach set and the scratch invariant

`LiftReach shift e c` is everything the `liftCached` walk on `e` at
cutoff `c` can read, store, or intern: the subterms at their visit
cutoffs together with their spec images. It is FINITE and spec-determined
— the caller of the master theorem instantiates the abstract support `S`
with `LiftReach ∪ (initial intern support)`, which is what makes the
collision-freedom hypothesis composable: no closure under
constructors (that would make `S` infinite and the hypothesis
pigeonhole-false) is ever needed. -/

/-- Membership: `x` is a node the walk on `e` at cutoff `c` can touch. -/
def LiftReach (shift : UInt64) : KExpr .anon → UInt64 → KExpr .anon → Prop
  | e, c, x =>
    x = e ∨ x = liftSpec e shift c ∨
      match e with
      | .app f a _ => LiftReach shift f c x ∨ LiftReach shift a c x
      | .lam _ _ ty body _ =>
        LiftReach shift ty c x ∨ LiftReach shift body (c + 1) x
      | .all _ _ ty body _ =>
        LiftReach shift ty c x ∨ LiftReach shift body (c + 1) x
      | .letE _ ty val body _ _ =>
        LiftReach shift ty c x ∨ LiftReach shift val c x ∨
          LiftReach shift body (c + 1) x
      | .prj _ _ val _ => LiftReach shift val c x
      | _ => False

theorem LiftReach.self (shift : UInt64) (e : KExpr .anon) (c : UInt64) :
    LiftReach shift e c e := by
  cases e <;> exact .inl rfl

theorem LiftReach.spec (shift : UInt64) (e : KExpr .anon) (c : UInt64) :
    LiftReach shift e c (liftSpec e shift c) := by
  cases e <;> exact .inr (.inl rfl)

end KExpr

/-- What a valid `lift` scratch means at a fixed `shift`: every memo entry
    is the spec image of some ambient-support witness carrying the key's
    address, at the key's cutoff. A hit at `(e.addr, c)` then converts to
    the spec image of `e` itself via collision-freedom — the
    `(addr, depth)`-keyed cache soundness argument in its pure home. -/
def LiftScratchInv (S : KExpr .anon → Prop) (shift : UInt64)
    (sc : Scratch .anon) : Prop :=
  ∀ (a : Address) (c : UInt64) (r : KExpr .anon), sc[(a, c)]? = some r →
    ∃ w, S w ∧ w.addr = a ∧ r = KExpr.liftSpec w shift c

theorem LiftScratchInv.empty (S : KExpr .anon → Prop) (shift : UInt64) :
    LiftScratchInv S shift ({} : Scratch .anon) := by
  intro a c r hr
  simp at hr

theorem LiftScratchInv.insert {S : KExpr .anon → Prop} {shift : UInt64}
    {sc : Scratch .anon} (hsc : LiftScratchInv S shift sc)
    {e r : KExpr .anon} {cutoff : UInt64} (hSe : S e)
    (hr : r = KExpr.liftSpec e shift cutoff) :
    LiftScratchInv S shift (sc.insert (e.addr, cutoff) r) := by
  intro a c v hv
  rw [Std.HashMap.getElem?_insert] at hv
  split at hv
  · next hbeq =>
    cases hv
    cases eq_of_beq hbeq
    exact ⟨e, hSe, rfl, hr⟩
  · exact hsc _ _ _ hv

/-! ### Run-equation kit

`WalkM = StateM (InternTable × Scratch)`; every step of the do-elaborated
walker body reduces definitionally once the state pair is applied. These
`rfl` lemmas expose one step each, keeping goals tidy. -/

private theorem run_pure_bind {α β} (a : α) (f : α → WalkM .anon β)
    (s : InternTable .anon × Scratch .anon) : (pure a >>= f) s = f a s := rfl

private theorem run_bind {α β} (x : WalkM .anon α) (f : α → WalkM .anon β)
    (s : InternTable .anon × Scratch .anon) :
    (x >>= f) s = f (x s).1 (x s).2 := rfl

private theorem run_scratchGet_bind {α} (key : Address × UInt64)
    (f : Option (KExpr .anon) → WalkM .anon α) (it : InternTable .anon)
    (sc : Scratch .anon) :
    (scratchGet? key >>= f) (it, sc) = f sc[key]? (it, sc) := rfl

private theorem run_intern_bind {α} (r : KExpr .anon)
    (f : KExpr .anon → WalkM .anon α) (it : InternTable .anon)
    (sc : Scratch .anon) :
    (liftInternW (internExprM r) >>= f) (it, sc)
      = f (it.internExpr r).1 ((it.internExpr r).2, sc) := rfl

private theorem run_scratchInsert_bind {α} (key : Address × UInt64)
    (v : KExpr .anon) (f : PUnit → WalkM .anon α) (it : InternTable .anon)
    (sc : Scratch .anon) :
    (scratchInsert key v >>= f) (it, sc) = f ⟨⟩ (it, sc.insert key v) := rfl

private theorem run_pure {α} (a : α) (s : InternTable .anon × Scratch .anon) :
    (pure a : WalkM .anon α) s = (a, s) := rfl

/-- Post-state contract of one `liftCached` run: the result is the spec
    image, and every threaded invariant survives. -/
structure LiftPost (S : KExpr .anon → Prop) (shift cutoff : UInt64)
    (e : KExpr .anon)
    (out : KExpr .anon × (InternTable .anon × Scratch .anon)) : Prop where
  result : out.1 = KExpr.liftSpec e shift cutoff
  wf : out.2.1.WF
  sup : ∀ x, out.2.1.ExprSupport x → S x
  scr : LiftScratchInv S shift out.2.2

/-- Fast path (`shift = 0` or `lbr ≤ cutoff`): the walker returns its input
    unchanged, which IS the spec image. -/
private theorem liftPost_fast {S : KExpr .anon → Prop} {e : KExpr .anon}
    {shift cutoff : UInt64} {it : InternTable .anon} {sc : Scratch .anon}
    (hcon : KExpr.Constructed e)
    (hcut : cutoff.toNat + e.size < UInt64.size)
    (hfast : (shift == 0 || decide (e.lbr ≤ cutoff)) = true)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : LiftScratchInv S shift sc) :
    LiftPost S shift cutoff e (liftCached e shift cutoff (it, sc)) := by
  have hrun : liftCached e shift cutoff (it, sc) = (e, (it, sc)) := by
    rw [liftCached, if_pos hfast]
    rfl
  rw [hrun]
  refine ⟨?_, hwf, hsup, hsc⟩
  rcases Bool.or_eq_true_iff.mp hfast with h0 | hle
  · show e = KExpr.liftSpec e shift cutoff
    rw [eq_of_beq h0]
    exact (KExpr.liftSpec_zero hcon cutoff).symm
  · exact (KExpr.liftSpec_id hcon hcut (of_decide_eq_true hle)).symm

/-- Scratch hit: the stored entry converts to the spec image of the
    current node via collision-freedom on the support. -/
private theorem liftPost_hit {S : KExpr .anon → Prop} {e r : KExpr .anon}
    {shift cutoff : UInt64} {it : InternTable .anon} {sc : Scratch .anon}
    (hcf : KExpr.CollisionFree S)
    (hSe : S e)
    (hfast : ¬ (shift == 0 || decide (e.lbr ≤ cutoff)) = true)
    (hget : sc[(e.addr, cutoff)]? = some r)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : LiftScratchInv S shift sc) :
    LiftPost S shift cutoff e (liftCached e shift cutoff (it, sc)) := by
  have hrun : liftCached e shift cutoff (it, sc) = (r, (it, sc)) := by
    rw [liftCached, if_neg hfast, run_pure_bind]
    simp only []
    rw [run_scratchGet_bind, hget]
    rfl
  rw [hrun]
  refine ⟨?_, hwf, hsup, hsc⟩
  obtain ⟨w, hwS, hwaddr, hrspec⟩ := hsc _ _ _ hget
  have hwe : w = e := by
    have h := hcf hwS hSe hwaddr
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at h
  show r = KExpr.liftSpec e shift cutoff
  rw [hrspec, hwe]

/-- Rebuild tail (the `__do_jp` join point): intern the candidate, memoize,
    return. Under collision-freedom the intern step is exact, so the run
    lands on the candidate — which the caller supplies as the spec image. -/
private theorem liftPost_jp {S : KExpr .anon → Prop} {e cand : KExpr .anon}
    {shift cutoff : UInt64} {it : InternTable .anon} {sc : Scratch .anon}
    (hcf : KExpr.CollisionFree S)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : LiftScratchInv S shift sc)
    (hSe : S e) (hScand : S cand)
    (hcand : cand = KExpr.liftSpec e shift cutoff) :
    LiftPost S shift cutoff e
      ((it.internExpr cand).1,
        ((it.internExpr cand).2,
          sc.insert (e.addr, cutoff) (it.internExpr cand).1)) := by
  have hkcf : KExpr.KeyCollisionFree
      fun v => it.ExprSupport v ∨ v = cand :=
    KExpr.keyCollisionFree_anon.mpr
      (hcf.mono fun x hx => hx.elim (hsup x) fun hxe => hxe ▸ hScand)
  have hcanon : (it.internExpr cand).1 = cand := by
    have h := InternTable.internExpr_eraseMeta hwf hkcf
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at h
  refine ⟨?_, hwf.internExpr cand, ?_, ?_⟩
  · show (it.internExpr cand).1 = KExpr.liftSpec e shift cutoff
    rw [hcanon, hcand]
  · intro x hx
    rcases InternTable.ExprSupport.of_internExpr hx with h | h
    · exact hsup x h
    · exact h ▸ hScand
  · exact hsc.insert hSe (by rw [hcanon, hcand])

/-- Store-self tail (below-cutoff `var`s and atoms): memoize the node
    itself and return it, unchanged and un-interned. -/
private theorem liftPost_store_self {S : KExpr .anon → Prop}
    {e : KExpr .anon} {shift cutoff : UInt64} {it : InternTable .anon}
    {sc : Scratch .anon}
    (hspec : KExpr.liftSpec e shift cutoff = e) (hSe : S e)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : LiftScratchInv S shift sc) :
    LiftPost S shift cutoff e
      (e, (it, sc.insert (e.addr, cutoff) e)) :=
  ⟨hspec.symm, hwf, hsup, hsc.insert hSe hspec.symm⟩

/-- **WalkM memo-soundness for `lift`** — the pattern's validation site. Under
    collision-freedom of an abstract support `S` (instantiable with the
    finite `LiftReach ∪ intern-support` union), the memoized, interning
    walker computes exactly the pure spec, and every invariant survives
    into the post-state. -/
theorem liftCached_spec {S : KExpr .anon → Prop} {shift : UInt64}
    (hcf : KExpr.CollisionFree S) {e : KExpr .anon}
    (hcon : KExpr.Constructed e) :
    ∀ {cutoff : UInt64} {it : InternTable .anon} {sc : Scratch .anon},
      cutoff.toNat + e.size < UInt64.size →
      (∀ x, KExpr.LiftReach shift e cutoff x → S x) →
      it.WF → (∀ x, it.ExprSupport x → S x) →
      LiftScratchInv S shift sc →
      LiftPost S shift cutoff e (liftCached e shift cutoff (it, sc)) := by
  induction hcon with
  | @var idx name md hidx =>
    intro cutoff it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkVar_shape] at hreach ⊢
    by_cases hfast : (shift == 0
        || decide ((KExpr.var idx name (KExpr.mkVar idx name md).info).lbr
          ≤ cutoff)) = true
    · exact liftPost_fast (.var hidx) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.var idx name
          (KExpr.mkVar idx name md).info).addr, cutoff)]? with
      | some r =>
        exact liftPost_hit hcf (hreach _ (KExpr.LiftReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        by_cases hge : idx ≥ cutoff
        · have hrun : liftCached
              (.var idx name (KExpr.mkVar idx name md).info) shift cutoff
              (it, sc)
              = ((it.internExpr (KExpr.mkVar (idx + shift) name)).1,
                 ((it.internExpr (KExpr.mkVar (idx + shift) name)).2,
                  sc.insert ((KExpr.var idx name
                      (KExpr.mkVar idx name md).info).addr, cutoff)
                    (it.internExpr (KExpr.mkVar (idx + shift) name)).1)) := by
            rw [liftCached, if_neg hfast, run_pure_bind]
            try simp only []
            rw [run_scratchGet_bind, hget]
            try simp (config := { proj := false }) only []
            try rw [run_pure_bind]
            try simp only []
            rw [if_pos hge]
            rfl
          rw [hrun]
          have hcand : KExpr.mkVar (idx + shift) name
              = KExpr.liftSpec
                  (.var idx name (KExpr.mkVar idx name md).info)
                  shift cutoff := by
            rw [KExpr.liftSpec, if_pos hge]
          exact liftPost_jp hcf hwf hsup hsc
            (hreach _ (KExpr.LiftReach.self ..))
            (hreach _ (by rw [hcand]; exact KExpr.LiftReach.spec ..))
            hcand
        · have hrun : liftCached
              (.var idx name (KExpr.mkVar idx name md).info) shift cutoff
              (it, sc)
              = (.var idx name (KExpr.mkVar idx name md).info,
                 (it, sc.insert ((KExpr.var idx name
                     (KExpr.mkVar idx name md).info).addr, cutoff)
                   (.var idx name (KExpr.mkVar idx name md).info))) := by
            rw [liftCached, if_neg hfast, run_pure_bind]
            try simp only []
            rw [run_scratchGet_bind, hget]
            try simp (config := { proj := false }) only []
            try rw [run_pure_bind]
            try simp only []
            rw [if_neg hge]
            rfl
          rw [hrun]
          exact liftPost_store_self (by rw [KExpr.liftSpec, if_neg hge])
            (hreach _ (KExpr.LiftReach.self ..)) hwf hsup hsc
  | @fvar id name md =>
    intro cutoff it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkFVar_shape] at hreach ⊢
    by_cases hfast : (shift == 0
        || decide ((KExpr.fvar id name
          (KExpr.mkFVar id name md).info).lbr ≤ cutoff)) = true
    · exact liftPost_fast .fvar hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.fvar id name
          (KExpr.mkFVar id name md).info).addr, cutoff)]? with
      | some r =>
        exact liftPost_hit hcf (hreach _ (KExpr.LiftReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        have hrun : liftCached
            (.fvar id name (KExpr.mkFVar id name md).info) shift cutoff
            (it, sc)
            = (.fvar id name (KExpr.mkFVar id name md).info,
               (it, sc.insert ((KExpr.fvar id name
                   (KExpr.mkFVar id name md).info).addr, cutoff)
                 (.fvar id name (KExpr.mkFVar id name md).info))) := by
          rw [liftCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          rfl
        rw [hrun]
        exact liftPost_store_self rfl
          (hreach _ (KExpr.LiftReach.self ..)) hwf hsup hsc
  | @sort u md =>
    intro cutoff it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkSort_shape] at hreach ⊢
    by_cases hfast : (shift == 0
        || decide ((KExpr.sort u (KExpr.mkSort u md).info).lbr
          ≤ cutoff)) = true
    · exact liftPost_fast .sort hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.sort u
          (KExpr.mkSort u md).info).addr, cutoff)]? with
      | some r =>
        exact liftPost_hit hcf (hreach _ (KExpr.LiftReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        have hrun : liftCached
            (.sort u (KExpr.mkSort u md).info) shift cutoff (it, sc)
            = (.sort u (KExpr.mkSort u md).info,
               (it, sc.insert
                 ((KExpr.sort u (KExpr.mkSort u md).info).addr, cutoff)
                 (.sort u (KExpr.mkSort u md).info))) := by
          rw [liftCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          rfl
        rw [hrun]
        exact liftPost_store_self rfl
          (hreach _ (KExpr.LiftReach.self ..)) hwf hsup hsc
  | @const id us md =>
    intro cutoff it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkConst_shape] at hreach ⊢
    by_cases hfast : (shift == 0
        || decide ((KExpr.const id us
          (KExpr.mkConst id us md).info).lbr ≤ cutoff)) = true
    · exact liftPost_fast .const hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.const id us
          (KExpr.mkConst id us md).info).addr, cutoff)]? with
      | some r =>
        exact liftPost_hit hcf (hreach _ (KExpr.LiftReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        have hrun : liftCached
            (.const id us (KExpr.mkConst id us md).info) shift cutoff
            (it, sc)
            = (.const id us (KExpr.mkConst id us md).info,
               (it, sc.insert
                 ((KExpr.const id us
                     (KExpr.mkConst id us md).info).addr, cutoff)
                 (.const id us (KExpr.mkConst id us md).info))) := by
          rw [liftCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          rfl
        rw [hrun]
        exact liftPost_store_self rfl
          (hreach _ (KExpr.LiftReach.self ..)) hwf hsup hsc
  | @app f a md hf ha ihf iha =>
    intro cutoff it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkApp_shape] at hreach ⊢
    have hcut' : cutoff.toNat + (f.size + a.size + 1) < UInt64.size := hcut
    by_cases hfast : (shift == 0
        || decide ((KExpr.app f a
          (KExpr.mkApp f a md).info).lbr ≤ cutoff)) = true
    · exact liftPost_fast (.app hf ha) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.app f a
          (KExpr.mkApp f a md).info).addr, cutoff)]? with
      | some r =>
        exact liftPost_hit hcf (hreach _ (KExpr.LiftReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        rcases hrun1 : liftCached f shift cutoff (it, sc) with ⟨rf, it1, sc1⟩
        have post1 := ihf (cutoff := cutoff) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : liftCached a shift cutoff (it1, sc1) with ⟨ra, it2, sc2⟩
        have post2 := iha (cutoff := cutoff) (it := it1) (sc := sc1)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rf = KExpr.liftSpec f shift cutoff := post1.result
        have hres2 : ra = KExpr.liftSpec a shift cutoff := post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : LiftScratchInv S shift sc2 := post2.scr
        have hrun : liftCached
            (.app f a (KExpr.mkApp f a md).info) shift cutoff (it, sc)
            = ((it2.internExpr (KExpr.mkApp rf ra)).1,
               ((it2.internExpr (KExpr.mkApp rf ra)).2,
                sc2.insert ((KExpr.app f a
                    (KExpr.mkApp f a md).info).addr, cutoff)
                  (it2.internExpr (KExpr.mkApp rf ra)).1)) := by
          rw [liftCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkApp rf ra
            = KExpr.liftSpec (.app f a (KExpr.mkApp f a md).info)
                shift cutoff := by
          rw [KExpr.liftSpec, hres1, hres2]
        exact liftPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.LiftReach.self ..))
          (hreach _ (by rw [hcand]; exact KExpr.LiftReach.spec ..))
          hcand
  | @lam n bi ty body md hty hbody ihty ihbody =>
    intro cutoff it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkLam_shape] at hreach ⊢
    have hcut' : cutoff.toNat + (ty.size + body.size + 1) < UInt64.size :=
      hcut
    have hc1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut')
    by_cases hfast : (shift == 0
        || decide ((KExpr.lam n bi ty body
          (KExpr.mkLam n bi ty body md).info).lbr ≤ cutoff)) = true
    · exact liftPost_fast (.lam hty hbody) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.lam n bi ty body
          (KExpr.mkLam n bi ty body md).info).addr, cutoff)]? with
      | some r =>
        exact liftPost_hit hcf (hreach _ (KExpr.LiftReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        rcases hrun1 : liftCached ty shift cutoff (it, sc) with ⟨rty, it1, sc1⟩
        have post1 := ihty (cutoff := cutoff) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : liftCached body shift (cutoff + 1) (it1, sc1)
          with ⟨rbody, it2, sc2⟩
        have post2 := ihbody (cutoff := cutoff + 1) (it := it1) (sc := sc1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rty = KExpr.liftSpec ty shift cutoff := post1.result
        have hres2 : rbody = KExpr.liftSpec body shift (cutoff + 1) :=
          post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : LiftScratchInv S shift sc2 := post2.scr
        have hrun : liftCached
            (.lam n bi ty body (KExpr.mkLam n bi ty body md).info)
            shift cutoff (it, sc)
            = ((it2.internExpr (KExpr.mkLam n bi rty rbody)).1,
               ((it2.internExpr (KExpr.mkLam n bi rty rbody)).2,
                sc2.insert ((KExpr.lam n bi ty body
                    (KExpr.mkLam n bi ty body md).info).addr, cutoff)
                  (it2.internExpr (KExpr.mkLam n bi rty rbody)).1)) := by
          rw [liftCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkLam n bi rty rbody
            = KExpr.liftSpec
                (.lam n bi ty body (KExpr.mkLam n bi ty body md).info)
                shift cutoff := by
          rw [KExpr.liftSpec, hres1, hres2]
        exact liftPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.LiftReach.self ..))
          (hreach _ (by rw [hcand]; exact KExpr.LiftReach.spec ..))
          hcand
  | @all n bi ty body md hty hbody ihty ihbody =>
    intro cutoff it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkAll_shape] at hreach ⊢
    have hcut' : cutoff.toNat + (ty.size + body.size + 1) < UInt64.size :=
      hcut
    have hc1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut')
    by_cases hfast : (shift == 0
        || decide ((KExpr.all n bi ty body
          (KExpr.mkAll n bi ty body md).info).lbr ≤ cutoff)) = true
    · exact liftPost_fast (.all hty hbody) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.all n bi ty body
          (KExpr.mkAll n bi ty body md).info).addr, cutoff)]? with
      | some r =>
        exact liftPost_hit hcf (hreach _ (KExpr.LiftReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        rcases hrun1 : liftCached ty shift cutoff (it, sc) with ⟨rty, it1, sc1⟩
        have post1 := ihty (cutoff := cutoff) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : liftCached body shift (cutoff + 1) (it1, sc1)
          with ⟨rbody, it2, sc2⟩
        have post2 := ihbody (cutoff := cutoff + 1) (it := it1) (sc := sc1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rty = KExpr.liftSpec ty shift cutoff := post1.result
        have hres2 : rbody = KExpr.liftSpec body shift (cutoff + 1) :=
          post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : LiftScratchInv S shift sc2 := post2.scr
        have hrun : liftCached
            (.all n bi ty body (KExpr.mkAll n bi ty body md).info)
            shift cutoff (it, sc)
            = ((it2.internExpr (KExpr.mkAll n bi rty rbody)).1,
               ((it2.internExpr (KExpr.mkAll n bi rty rbody)).2,
                sc2.insert ((KExpr.all n bi ty body
                    (KExpr.mkAll n bi ty body md).info).addr, cutoff)
                  (it2.internExpr (KExpr.mkAll n bi rty rbody)).1)) := by
          rw [liftCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkAll n bi rty rbody
            = KExpr.liftSpec
                (.all n bi ty body (KExpr.mkAll n bi ty body md).info)
                shift cutoff := by
          rw [KExpr.liftSpec, hres1, hres2]
        exact liftPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.LiftReach.self ..))
          (hreach _ (by rw [hcand]; exact KExpr.LiftReach.spec ..))
          hcand
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    intro cutoff it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkLet_shape] at hreach ⊢
    have hcut' :
        cutoff.toNat + (ty.size + val.size + body.size + 1) < UInt64.size :=
      hcut
    have hc1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut')
    by_cases hfast : (shift == 0
        || decide ((KExpr.letE n ty val body nd
          (KExpr.mkLet n ty val body nd md).info).lbr ≤ cutoff)) = true
    · exact liftPost_fast (.letE hty hval hbody) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.letE n ty val body nd
          (KExpr.mkLet n ty val body nd md).info).addr, cutoff)]? with
      | some r =>
        exact liftPost_hit hcf (hreach _ (KExpr.LiftReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        rcases hrun1 : liftCached ty shift cutoff (it, sc) with ⟨rty, it1, sc1⟩
        have post1 := ihty (cutoff := cutoff) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : liftCached val shift cutoff (it1, sc1)
          with ⟨rval, it2, sc2⟩
        have post2 := ihval (cutoff := cutoff) (it := it1) (sc := sc1)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr (.inl hx)))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        rcases hrun3 : liftCached body shift (cutoff + 1) (it2, sc2)
          with ⟨rbody, it3, sc3⟩
        have post3 := ihbody (cutoff := cutoff + 1) (it := it2) (sc := sc2)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr (.inr hx)))))
          post2.wf post2.sup post2.scr
        rw [hrun3] at post3
        have hres1 : rty = KExpr.liftSpec ty shift cutoff := post1.result
        have hres2 : rval = KExpr.liftSpec val shift cutoff := post2.result
        have hres3 : rbody = KExpr.liftSpec body shift (cutoff + 1) :=
          post3.result
        have hwf3 : it3.WF := post3.wf
        have hsup3 : ∀ x, it3.ExprSupport x → S x := post3.sup
        have hsc3 : LiftScratchInv S shift sc3 := post3.scr
        have hrun : liftCached
            (.letE n ty val body nd
              (KExpr.mkLet n ty val body nd md).info) shift cutoff (it, sc)
            = ((it3.internExpr (KExpr.mkLet n rty rval rbody nd)).1,
               ((it3.internExpr (KExpr.mkLet n rty rval rbody nd)).2,
                sc3.insert ((KExpr.letE n ty val body nd
                    (KExpr.mkLet n ty val body nd md).info).addr, cutoff)
                  (it3.internExpr (KExpr.mkLet n rty rval rbody nd)).1)) := by
          rw [liftCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          try rw [run_bind]
          rw [hrun3]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkLet n rty rval rbody nd
            = KExpr.liftSpec
                (.letE n ty val body nd
                  (KExpr.mkLet n ty val body nd md).info) shift cutoff := by
          rw [KExpr.liftSpec, hres1, hres2, hres3]
        exact liftPost_jp hcf hwf3 hsup3 hsc3
          (hreach _ (KExpr.LiftReach.self ..))
          (hreach _ (by rw [hcand]; exact KExpr.LiftReach.spec ..))
          hcand
  | @prj id field val md hval ihval =>
    intro cutoff it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkPrj_shape] at hreach ⊢
    have hcut' : cutoff.toNat + (val.size + 1) < UInt64.size := hcut
    by_cases hfast : (shift == 0
        || decide ((KExpr.prj id field val
          (KExpr.mkPrj id field val md).info).lbr ≤ cutoff)) = true
    · exact liftPost_fast (.prj hval) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.prj id field val
          (KExpr.mkPrj id field val md).info).addr, cutoff)]? with
      | some r =>
        exact liftPost_hit hcf (hreach _ (KExpr.LiftReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        rcases hrun1 : liftCached val shift cutoff (it, sc)
          with ⟨rval, it1, sc1⟩
        have post1 := ihval (cutoff := cutoff) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr hx)))
          hwf hsup hsc
        rw [hrun1] at post1
        have hres1 : rval = KExpr.liftSpec val shift cutoff := post1.result
        have hwf1 : it1.WF := post1.wf
        have hsup1 : ∀ x, it1.ExprSupport x → S x := post1.sup
        have hsc1 : LiftScratchInv S shift sc1 := post1.scr
        have hrun : liftCached
            (.prj id field val (KExpr.mkPrj id field val md).info)
            shift cutoff (it, sc)
            = ((it1.internExpr (KExpr.mkPrj id field rval)).1,
               ((it1.internExpr (KExpr.mkPrj id field rval)).2,
                sc1.insert ((KExpr.prj id field val
                    (KExpr.mkPrj id field val md).info).addr, cutoff)
                  (it1.internExpr (KExpr.mkPrj id field rval)).1)) := by
          rw [liftCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkPrj id field rval
            = KExpr.liftSpec
                (.prj id field val (KExpr.mkPrj id field val md).info)
                shift cutoff := by
          rw [KExpr.liftSpec, hres1]
        exact liftPost_jp hcf hwf1 hsup1 hsc1
          (hreach _ (KExpr.LiftReach.self ..))
          (hreach _ (by rw [hcand]; exact KExpr.LiftReach.spec ..))
          hcand
  | @nat v blob md =>
    intro cutoff it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkNat_shape] at hreach ⊢
    by_cases hfast : (shift == 0
        || decide ((KExpr.nat v blob
          (KExpr.mkNat v blob md).info).lbr ≤ cutoff)) = true
    · exact liftPost_fast .nat hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.nat v blob
          (KExpr.mkNat v blob md).info).addr, cutoff)]? with
      | some r =>
        exact liftPost_hit hcf (hreach _ (KExpr.LiftReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        have hrun : liftCached
            (.nat v blob (KExpr.mkNat v blob md).info) shift cutoff
            (it, sc)
            = (.nat v blob (KExpr.mkNat v blob md).info,
               (it, sc.insert
                 ((KExpr.nat v blob
                     (KExpr.mkNat v blob md).info).addr, cutoff)
                 (.nat v blob (KExpr.mkNat v blob md).info))) := by
          rw [liftCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          rfl
        rw [hrun]
        exact liftPost_store_self rfl
          (hreach _ (KExpr.LiftReach.self ..)) hwf hsup hsc
  | @str v blob md =>
    intro cutoff it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkStr_shape] at hreach ⊢
    by_cases hfast : (shift == 0
        || decide ((KExpr.str v blob
          (KExpr.mkStr v blob md).info).lbr ≤ cutoff)) = true
    · exact liftPost_fast .str hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.str v blob
          (KExpr.mkStr v blob md).info).addr, cutoff)]? with
      | some r =>
        exact liftPost_hit hcf (hreach _ (KExpr.LiftReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        have hrun : liftCached
            (.str v blob (KExpr.mkStr v blob md).info) shift cutoff
            (it, sc)
            = (.str v blob (KExpr.mkStr v blob md).info,
               (it, sc.insert
                 ((KExpr.str v blob
                     (KExpr.mkStr v blob md).info).addr, cutoff)
                 (.str v blob (KExpr.mkStr v blob md).info))) := by
          rw [liftCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          rfl
        rw [hrun]
        exact liftPost_store_self rfl
          (hreach _ (KExpr.LiftReach.self ..)) hwf hsup hsc

/-- **`lift` is the pure spec** (InternM API level). Fresh scratch per call
    — mirroring the separate `lift_scratch` in Rust — so only the
    intern-table invariants thread in and out. Instantiate `S` with
    `LiftReach shift e cutoff ∪ it.ExprSupport` (both finite) to discharge
    `hreach`/`hsup` definitionally; `hcf` is then a finite-support
    collision-freedom hypothesis. -/
theorem lift_spec {S : KExpr .anon → Prop} {e : KExpr .anon}
    {shift cutoff : UInt64} {it : InternTable .anon}
    (hcf : KExpr.CollisionFree S) (hcon : KExpr.Constructed e)
    (hcut : cutoff.toNat + e.size < UInt64.size)
    (hreach : ∀ x, KExpr.LiftReach shift e cutoff x → S x)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x) :
    (lift e shift cutoff it).1 = KExpr.liftSpec e shift cutoff ∧
    (lift e shift cutoff it).2.WF ∧
    (∀ x, (lift e shift cutoff it).2.ExprSupport x → S x) := by
  by_cases hfast : (shift == 0 || decide (e.lbr ≤ cutoff)) = true
  · have hrun : lift e shift cutoff it = (e, it) := by
      rw [lift, if_pos hfast]
      rfl
    rw [hrun]
    refine ⟨?_, hwf, hsup⟩
    rcases Bool.or_eq_true_iff.mp hfast with h0 | hle
    · show e = KExpr.liftSpec e shift cutoff
      rw [eq_of_beq h0]
      exact (KExpr.liftSpec_zero hcon cutoff).symm
    · exact (KExpr.liftSpec_id hcon hcut (of_decide_eq_true hle)).symm
  · have post := liftCached_spec hcf hcon (cutoff := cutoff) (it := it)
      (sc := {}) hcut hreach hwf hsup (LiftScratchInv.empty S shift)
    have hrun : lift e shift cutoff it
        = ((liftCached e shift cutoff (it, {})).1,
           (liftCached e shift cutoff (it, {})).2.1) := by
      rw [lift, if_neg hfast]
      rfl
    rw [hrun]
    exact ⟨post.result, post.wf, post.sup⟩

/-! ## The `subst` walker

`substCached` shares `liftCached`'s tail discipline (memo-check →
rebuild → intern → memoize); its `var` arm at the substitution target
composes the whole `lift` walker (`lift arg depth 0`, with `lift`'s own
fresh scratch — the two memo spaces never mix, mirroring the separate
`lift_scratch` in Rust). The proof composes `lift_spec` at exactly that
point, so the support `S` must also cover `LiftReach depth arg 0` at
every `var` node.

`WalkScratchInv`/`WalkPost` below are `LiftScratchInv`/`LiftPost`
generalized over the pure spec; the remaining sibling walkers reuse
them. -/

namespace KExpr

/-- Pure, memo-free, intern-free single substitution
    `body[arg / Var(depth)]`: the target index is replaced by `arg`
    lifted by `depth`, indices above it shift down by one. Anon-mode
    spec — mirrors `substCached`'s rebuild arms exactly. -/
def substSpec (body arg : KExpr .anon) (depth : UInt64) : KExpr .anon :=
  match body with
  | .var i name _ =>
    if i == depth then liftSpec arg depth 0
    else if i > depth then mkVar (i - 1) name
    else body
  | .app f x _ => mkApp (substSpec f arg depth) (substSpec x arg depth)
  | .lam n bi ty inner _ =>
    mkLam n bi (substSpec ty arg depth) (substSpec inner arg (depth + 1))
  | .all n bi ty inner _ =>
    mkAll n bi (substSpec ty arg depth) (substSpec inner arg (depth + 1))
  | .letE n ty val inner nd _ =>
    mkLet n (substSpec ty arg depth) (substSpec val arg depth)
      (substSpec inner arg (depth + 1)) nd
  | .prj id field val _ => mkPrj id field (substSpec val arg depth)
  | body => body

/-- The `lbr ≤ depth` fast path is sound: with no loose index ≥ `depth`
    there is no substitution site and nothing to shift. -/
theorem substSpec_id {body arg : KExpr .anon} {depth : UInt64}
    (hcon : Constructed body)
    (hcut : depth.toNat + body.size < UInt64.size)
    (hlbr : body.lbr ≤ depth) :
    substSpec body arg depth = body := by
  induction hcon generalizing depth with
  | @var idx name md hidx =>
    rw [mkVar_lbr] at hlbr
    have hle : idx.toNat + 1 ≤ depth.toNat := by
      have h := UInt64.le_iff_toNat_le.mp hlbr
      rwa [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt hidx] at h
    have hne : ¬ (idx == depth) = true := fun h => by
      have := congrArg UInt64.toNat (eq_of_beq h)
      omega
    have hngt : ¬ idx > depth := fun h => by
      have := UInt64.lt_iff_toNat_lt.mp h
      omega
    rw [mkVar_shape, substSpec, if_neg hne, if_neg hngt]
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | @app f a md hf ha ihf iha =>
    rw [mkApp_lbr] at hlbr
    rw [mkApp_shape, size] at hcut
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    rw [mkApp_shape, substSpec,
      ihf (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      iha (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.2)]
    exact mkApp_shape f a md
  | @lam n bi ty body md hty hbody ihty ihbody =>
    rw [mkLam_lbr] at hlbr
    rw [mkLam_shape, size] at hcut
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkLam_shape, substSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkLam_shape n bi ty body md
  | @all n bi ty body md hty hbody ihty ihbody =>
    rw [mkAll_lbr] at hlbr
    rw [mkAll_shape, size] at hcut
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkAll_shape, substSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkAll_shape n bi ty body md
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    rw [mkLet_lbr] at hlbr
    rw [mkLet_shape, size] at hcut
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, toNat_max, Nat.max_le, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkLet_shape, substSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.1.1),
      ihval (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr hmax.1.2),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkLet_shape n ty val body nd md
  | @prj id field val md hval ihval =>
    rw [mkPrj_lbr] at hlbr
    rw [mkPrj_shape, size] at hcut
    rw [mkPrj_shape, substSpec,
      ihval (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut) hlbr]
    exact mkPrj_shape id field val md
  | nat => rfl
  | str => rfl

/-- Everything the `substCached` walk on `body` at depth `d` can read,
    store, or intern: subterms at their visit depths, their spec images,
    and — at `var` nodes — the footprint of the composed
    `lift arg d 0` call. Finite and spec-determined. -/
def SubstReach (arg : KExpr .anon) :
    KExpr .anon → UInt64 → KExpr .anon → Prop
  | body, d, x =>
    x = body ∨ x = substSpec body arg d ∨
      match body with
      | .var _ _ _ => LiftReach d arg 0 x
      | .app f a _ => SubstReach arg f d x ∨ SubstReach arg a d x
      | .lam _ _ ty inner _ =>
        SubstReach arg ty d x ∨ SubstReach arg inner (d + 1) x
      | .all _ _ ty inner _ =>
        SubstReach arg ty d x ∨ SubstReach arg inner (d + 1) x
      | .letE _ ty val inner _ _ =>
        SubstReach arg ty d x ∨ SubstReach arg val d x ∨
          SubstReach arg inner (d + 1) x
      | .prj _ _ val _ => SubstReach arg val d x
      | _ => False

theorem SubstReach.self (arg body : KExpr .anon) (d : UInt64) :
    SubstReach arg body d body := by
  cases body <;> exact .inl rfl

theorem SubstReach.spec (arg body : KExpr .anon) (d : UInt64) :
    SubstReach arg body d (substSpec body arg d) := by
  cases body <;> exact .inr (.inl rfl)

end KExpr

/-- Run equation for a composed `InternM` action lifted into the walker
    (the `lift` call inside `substCached`'s `var` arm): it acts on the
    intern table alone and leaves the walker's scratch untouched. -/
private theorem run_liftIntern_bind {α} (x : InternM .anon (KExpr .anon))
    (f : KExpr .anon → WalkM .anon α) (it : InternTable .anon)
    (sc : Scratch .anon) :
    (liftInternW x >>= f) (it, sc) = f (x it).1 ((x it).2, sc) := rfl

/-- `LiftScratchInv` generalized over the pure spec: every memo entry is
    the spec image of a support witness carrying the key's address, at
    the key's depth. -/
def WalkScratchInv (S : KExpr .anon → Prop)
    (spec : KExpr .anon → UInt64 → KExpr .anon) (sc : Scratch .anon) : Prop :=
  ∀ (a : Address) (c : UInt64) (r : KExpr .anon), sc[(a, c)]? = some r →
    ∃ w, S w ∧ w.addr = a ∧ r = spec w c

theorem WalkScratchInv.empty (S : KExpr .anon → Prop)
    (spec : KExpr .anon → UInt64 → KExpr .anon) :
    WalkScratchInv S spec ({} : Scratch .anon) := by
  intro a c r hr
  simp at hr

theorem WalkScratchInv.insert {S : KExpr .anon → Prop}
    {spec : KExpr .anon → UInt64 → KExpr .anon} {sc : Scratch .anon}
    (hsc : WalkScratchInv S spec sc) {e r : KExpr .anon} {c : UInt64}
    (hSe : S e) (hr : r = spec e c) :
    WalkScratchInv S spec (sc.insert (e.addr, c) r) := by
  intro a d v hv
  rw [Std.HashMap.getElem?_insert] at hv
  split at hv
  · next hbeq =>
    cases hv
    cases eq_of_beq hbeq
    exact ⟨e, hSe, rfl, hr⟩
  · exact hsc _ _ _ hv

/-- `LiftPost` generalized over the pure spec: the walker run lands on
    the spec image and every threaded invariant survives. -/
structure WalkPost (S : KExpr .anon → Prop)
    (spec : KExpr .anon → UInt64 → KExpr .anon) (c : UInt64)
    (e : KExpr .anon)
    (out : KExpr .anon × (InternTable .anon × Scratch .anon)) : Prop where
  result : out.1 = spec e c
  wf : out.2.1.WF
  sup : ∀ x, out.2.1.ExprSupport x → S x
  scr : WalkScratchInv S spec out.2.2

/-- Rebuild tail (the `__do_jp` join point) for any walker with the
    intern-then-memoize discipline. -/
private theorem walkPost_jp {S : KExpr .anon → Prop}
    {spec : KExpr .anon → UInt64 → KExpr .anon} {e cand : KExpr .anon}
    {c : UInt64} {it : InternTable .anon} {sc : Scratch .anon}
    (hcf : KExpr.CollisionFree S)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : WalkScratchInv S spec sc)
    (hSe : S e) (hScand : S cand)
    (hcand : cand = spec e c) :
    WalkPost S spec c e
      ((it.internExpr cand).1,
        ((it.internExpr cand).2,
          sc.insert (e.addr, c) (it.internExpr cand).1)) := by
  have hkcf : KExpr.KeyCollisionFree
      fun v => it.ExprSupport v ∨ v = cand :=
    KExpr.keyCollisionFree_anon.mpr
      (hcf.mono fun x hx => hx.elim (hsup x) fun hxe => hxe ▸ hScand)
  have hcanon : (it.internExpr cand).1 = cand := by
    have h := InternTable.internExpr_eraseMeta hwf hkcf
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at h
  refine ⟨?_, hwf.internExpr cand, ?_, ?_⟩
  · show (it.internExpr cand).1 = spec e c
    rw [hcanon, hcand]
  · intro x hx
    rcases InternTable.ExprSupport.of_internExpr hx with h | h
    · exact hsup x h
    · exact h ▸ hScand
  · exact hsc.insert hSe (by rw [hcanon, hcand])

/-- Store-self tail: memoize the node itself and return it, unchanged
    and un-interned. -/
private theorem walkPost_store_self {S : KExpr .anon → Prop}
    {spec : KExpr .anon → UInt64 → KExpr .anon} {e : KExpr .anon}
    {c : UInt64} {it : InternTable .anon} {sc : Scratch .anon}
    (hspec : spec e c = e) (hSe : S e)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : WalkScratchInv S spec sc) :
    WalkPost S spec c e (e, (it, sc.insert (e.addr, c) e)) :=
  ⟨hspec.symm, hwf, hsup, hsc.insert hSe hspec.symm⟩

/-- Fast path (`lbr ≤ depth`): the walker returns its input unchanged,
    which is the spec image by `substSpec_id`. -/
private theorem substPost_fast {S : KExpr .anon → Prop}
    {body arg : KExpr .anon} {depth : UInt64} {it : InternTable .anon}
    {sc : Scratch .anon}
    (hcon : KExpr.Constructed body)
    (hcut : depth.toNat + body.size < UInt64.size)
    (hfast : body.lbr ≤ depth)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : WalkScratchInv S (KExpr.substSpec · arg ·) sc) :
    WalkPost S (KExpr.substSpec · arg ·) depth body
      (substCached body arg depth (it, sc)) := by
  have hrun : substCached body arg depth (it, sc) = (body, (it, sc)) := by
    rw [substCached, if_pos hfast]
    rfl
  rw [hrun]
  exact ⟨(KExpr.substSpec_id hcon hcut hfast).symm, hwf, hsup, hsc⟩

/-- Scratch hit: the stored entry converts to the spec image of the
    current node via collision-freedom on the support. -/
private theorem substPost_hit {S : KExpr .anon → Prop}
    {body arg r : KExpr .anon} {depth : UInt64} {it : InternTable .anon}
    {sc : Scratch .anon}
    (hcf : KExpr.CollisionFree S) (hSe : S body)
    (hfast : ¬ body.lbr ≤ depth)
    (hget : sc[(body.addr, depth)]? = some r)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : WalkScratchInv S (KExpr.substSpec · arg ·) sc) :
    WalkPost S (KExpr.substSpec · arg ·) depth body
      (substCached body arg depth (it, sc)) := by
  have hrun : substCached body arg depth (it, sc) = (r, (it, sc)) := by
    rw [substCached, if_neg hfast, run_pure_bind]
    simp only []
    rw [run_scratchGet_bind, hget]
    rfl
  rw [hrun]
  refine ⟨?_, hwf, hsup, hsc⟩
  obtain ⟨w, hwS, hwaddr, hrspec⟩ := hsc _ _ _ hget
  have hwe : w = body := by
    have h := hcf hwS hSe hwaddr
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at h
  show r = KExpr.substSpec body arg depth
  rw [hrspec, hwe]

/-- **WalkM memo-soundness for `subst`**: under collision-freedom of an
    abstract support `S` covering `SubstReach ∪ intern-support`, the
    memoized, interning walker computes exactly the pure spec. The `var`
    arm at the substitution target composes `lift_spec` — the first
    walker-in-walker composition of the program. -/
theorem substCached_spec {S : KExpr .anon → Prop} {arg : KExpr .anon}
    (hcf : KExpr.CollisionFree S) (hconArg : KExpr.Constructed arg)
    (hargsz : arg.size < UInt64.size)
    {body : KExpr .anon} (hcon : KExpr.Constructed body) :
    ∀ {depth : UInt64} {it : InternTable .anon} {sc : Scratch .anon},
      depth.toNat + body.size < UInt64.size →
      (∀ x, KExpr.SubstReach arg body depth x → S x) →
      it.WF → (∀ x, it.ExprSupport x → S x) →
      WalkScratchInv S (KExpr.substSpec · arg ·) sc →
      WalkPost S (KExpr.substSpec · arg ·) depth body
        (substCached body arg depth (it, sc)) := by
  induction hcon with
  | @var idx name md hidx =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkVar_shape] at hreach ⊢
    by_cases hfast :
        (KExpr.var idx name (KExpr.mkVar idx name md).info).lbr ≤ depth
    · exact substPost_fast (.var hidx) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.var idx name
          (KExpr.mkVar idx name md).info).addr, depth)]? with
      | some r =>
        exact substPost_hit hcf (hreach _ (KExpr.SubstReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        by_cases heq : (idx == depth) = true
        · -- Substitution target: compose the `lift arg depth 0` call.
          rcases hlift : lift arg depth 0 it with ⟨rl, it1⟩
          have postL := lift_spec (S := S) (e := arg) (shift := depth)
            (cutoff := 0) (it := it) hcf hconArg
            (by show 0 + arg.size < UInt64.size; omega)
            (fun x hx => hreach x (.inr (.inr hx)))
            hwf hsup
          rw [hlift] at postL
          have hres : rl = KExpr.liftSpec arg depth 0 := postL.1
          have hwf1 : it1.WF := postL.2.1
          have hsup1 : ∀ x, it1.ExprSupport x → S x := postL.2.2
          have hrun : substCached
              (.var idx name (KExpr.mkVar idx name md).info) arg depth
              (it, sc)
              = ((it1.internExpr rl).1,
                 ((it1.internExpr rl).2,
                  sc.insert ((KExpr.var idx name
                      (KExpr.mkVar idx name md).info).addr, depth)
                    (it1.internExpr rl).1)) := by
            rw [substCached, if_neg hfast, run_pure_bind]
            try simp only []
            rw [run_scratchGet_bind, hget]
            try simp (config := { proj := false }) only []
            try rw [run_pure_bind]
            try simp only []
            rw [if_pos heq]
            rw [run_liftIntern_bind, hlift]
            try simp only []
            rfl
          rw [hrun]
          have hcand : rl = KExpr.substSpec
              (.var idx name (KExpr.mkVar idx name md).info) arg depth := by
            rw [KExpr.substSpec, if_pos heq]
            exact hres
          exact walkPost_jp hcf hwf1 hsup1 hsc
            (hreach _ (KExpr.SubstReach.self ..))
            (hreach _ (.inr (.inl hcand)))
            hcand
        · by_cases hgt : idx > depth
          · -- Above the target: rebuild with the decremented index.
            have hrun : substCached
                (.var idx name (KExpr.mkVar idx name md).info) arg depth
                (it, sc)
                = ((it.internExpr (KExpr.mkVar (idx - 1) name)).1,
                   ((it.internExpr (KExpr.mkVar (idx - 1) name)).2,
                    sc.insert ((KExpr.var idx name
                        (KExpr.mkVar idx name md).info).addr, depth)
                      (it.internExpr (KExpr.mkVar (idx - 1) name)).1)) := by
              rw [substCached, if_neg hfast, run_pure_bind]
              try simp only []
              rw [run_scratchGet_bind, hget]
              try simp (config := { proj := false }) only []
              try rw [run_pure_bind]
              try simp only []
              rw [if_neg heq, if_pos hgt]
              rfl
            rw [hrun]
            have hcand : KExpr.mkVar (idx - 1) name
                = KExpr.substSpec
                    (.var idx name (KExpr.mkVar idx name md).info)
                    arg depth := by
              rw [KExpr.substSpec, if_neg heq, if_pos hgt]
            exact walkPost_jp hcf hwf hsup hsc
              (hreach _ (KExpr.SubstReach.self ..))
              (hreach _ (.inr (.inl hcand)))
              hcand
          · -- Below the target: unreachable once the fast path declined.
            exfalso
            have hfast' : ¬ (idx + 1 ≤ depth) := hfast
            have hne : idx.toNat ≠ depth.toNat := fun h =>
              heq (beq_iff_eq.mpr (UInt64.toNat_inj.mp h))
            have hnlt : ¬ depth.toNat < idx.toNat := fun h =>
              hgt (UInt64.lt_iff_toNat_lt.mpr h)
            have h1 : ¬ (idx.toNat + 1 ≤ depth.toNat) := fun h =>
              hfast' (UInt64.le_iff_toNat_le.mpr (by
                rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt hidx]
                exact h))
            omega
  | @fvar id name md =>
    intro depth it sc hcut hreach hwf hsup hsc
    exact substPost_fast .fvar hcut UInt64.zero_le hwf hsup hsc
  | @sort u md =>
    intro depth it sc hcut hreach hwf hsup hsc
    exact substPost_fast .sort hcut UInt64.zero_le hwf hsup hsc
  | @const id us md =>
    intro depth it sc hcut hreach hwf hsup hsc
    exact substPost_fast .const hcut UInt64.zero_le hwf hsup hsc
  | @app f a md hf ha ihf iha =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkApp_shape] at hreach ⊢
    have hcut' : depth.toNat + (f.size + a.size + 1) < UInt64.size := hcut
    by_cases hfast :
        (KExpr.app f a (KExpr.mkApp f a md).info).lbr ≤ depth
    · exact substPost_fast (.app hf ha) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.app f a
          (KExpr.mkApp f a md).info).addr, depth)]? with
      | some r =>
        exact substPost_hit hcf (hreach _ (KExpr.SubstReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        rcases hrun1 : substCached f arg depth (it, sc) with ⟨rf, it1, sc1⟩
        have post1 := ihf (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : substCached a arg depth (it1, sc1) with ⟨ra, it2, sc2⟩
        have post2 := iha (depth := depth) (it := it1) (sc := sc1)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rf = KExpr.substSpec f arg depth := post1.result
        have hres2 : ra = KExpr.substSpec a arg depth := post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.substSpec · arg ·) sc2 :=
          post2.scr
        have hrun : substCached
            (.app f a (KExpr.mkApp f a md).info) arg depth (it, sc)
            = ((it2.internExpr (KExpr.mkApp rf ra)).1,
               ((it2.internExpr (KExpr.mkApp rf ra)).2,
                sc2.insert ((KExpr.app f a
                    (KExpr.mkApp f a md).info).addr, depth)
                  (it2.internExpr (KExpr.mkApp rf ra)).1)) := by
          rw [substCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkApp rf ra
            = KExpr.substSpec (.app f a (KExpr.mkApp f a md).info)
                arg depth := by
          rw [KExpr.substSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.SubstReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @lam n bi ty body md hty hbody ihty ihbody =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkLam_shape] at hreach ⊢
    have hcut' : depth.toNat + (ty.size + body.size + 1) < UInt64.size :=
      hcut
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut')
    by_cases hfast :
        (KExpr.lam n bi ty body
          (KExpr.mkLam n bi ty body md).info).lbr ≤ depth
    · exact substPost_fast (.lam hty hbody) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.lam n bi ty body
          (KExpr.mkLam n bi ty body md).info).addr, depth)]? with
      | some r =>
        exact substPost_hit hcf (hreach _ (KExpr.SubstReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        rcases hrun1 : substCached ty arg depth (it, sc) with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : substCached body arg (depth + 1) (it1, sc1)
          with ⟨rbody, it2, sc2⟩
        have post2 := ihbody (depth := depth + 1) (it := it1) (sc := sc1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rty = KExpr.substSpec ty arg depth := post1.result
        have hres2 : rbody = KExpr.substSpec body arg (depth + 1) :=
          post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.substSpec · arg ·) sc2 :=
          post2.scr
        have hrun : substCached
            (.lam n bi ty body (KExpr.mkLam n bi ty body md).info)
            arg depth (it, sc)
            = ((it2.internExpr (KExpr.mkLam n bi rty rbody)).1,
               ((it2.internExpr (KExpr.mkLam n bi rty rbody)).2,
                sc2.insert ((KExpr.lam n bi ty body
                    (KExpr.mkLam n bi ty body md).info).addr, depth)
                  (it2.internExpr (KExpr.mkLam n bi rty rbody)).1)) := by
          rw [substCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkLam n bi rty rbody
            = KExpr.substSpec
                (.lam n bi ty body (KExpr.mkLam n bi ty body md).info)
                arg depth := by
          rw [KExpr.substSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.SubstReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @all n bi ty body md hty hbody ihty ihbody =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkAll_shape] at hreach ⊢
    have hcut' : depth.toNat + (ty.size + body.size + 1) < UInt64.size :=
      hcut
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut')
    by_cases hfast :
        (KExpr.all n bi ty body
          (KExpr.mkAll n bi ty body md).info).lbr ≤ depth
    · exact substPost_fast (.all hty hbody) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.all n bi ty body
          (KExpr.mkAll n bi ty body md).info).addr, depth)]? with
      | some r =>
        exact substPost_hit hcf (hreach _ (KExpr.SubstReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        rcases hrun1 : substCached ty arg depth (it, sc) with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : substCached body arg (depth + 1) (it1, sc1)
          with ⟨rbody, it2, sc2⟩
        have post2 := ihbody (depth := depth + 1) (it := it1) (sc := sc1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rty = KExpr.substSpec ty arg depth := post1.result
        have hres2 : rbody = KExpr.substSpec body arg (depth + 1) :=
          post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.substSpec · arg ·) sc2 :=
          post2.scr
        have hrun : substCached
            (.all n bi ty body (KExpr.mkAll n bi ty body md).info)
            arg depth (it, sc)
            = ((it2.internExpr (KExpr.mkAll n bi rty rbody)).1,
               ((it2.internExpr (KExpr.mkAll n bi rty rbody)).2,
                sc2.insert ((KExpr.all n bi ty body
                    (KExpr.mkAll n bi ty body md).info).addr, depth)
                  (it2.internExpr (KExpr.mkAll n bi rty rbody)).1)) := by
          rw [substCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkAll n bi rty rbody
            = KExpr.substSpec
                (.all n bi ty body (KExpr.mkAll n bi ty body md).info)
                arg depth := by
          rw [KExpr.substSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.SubstReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkLet_shape] at hreach ⊢
    have hcut' :
        depth.toNat + (ty.size + val.size + body.size + 1) < UInt64.size :=
      hcut
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut')
    by_cases hfast :
        (KExpr.letE n ty val body nd
          (KExpr.mkLet n ty val body nd md).info).lbr ≤ depth
    · exact substPost_fast (.letE hty hval hbody) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.letE n ty val body nd
          (KExpr.mkLet n ty val body nd md).info).addr, depth)]? with
      | some r =>
        exact substPost_hit hcf (hreach _ (KExpr.SubstReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        rcases hrun1 : substCached ty arg depth (it, sc) with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : substCached val arg depth (it1, sc1)
          with ⟨rval, it2, sc2⟩
        have post2 := ihval (depth := depth) (it := it1) (sc := sc1)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr (.inl hx)))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        rcases hrun3 : substCached body arg (depth + 1) (it2, sc2)
          with ⟨rbody, it3, sc3⟩
        have post3 := ihbody (depth := depth + 1) (it := it2) (sc := sc2)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr (.inr hx)))))
          post2.wf post2.sup post2.scr
        rw [hrun3] at post3
        have hres1 : rty = KExpr.substSpec ty arg depth := post1.result
        have hres2 : rval = KExpr.substSpec val arg depth := post2.result
        have hres3 : rbody = KExpr.substSpec body arg (depth + 1) :=
          post3.result
        have hwf3 : it3.WF := post3.wf
        have hsup3 : ∀ x, it3.ExprSupport x → S x := post3.sup
        have hsc3 : WalkScratchInv S (KExpr.substSpec · arg ·) sc3 :=
          post3.scr
        have hrun : substCached
            (.letE n ty val body nd
              (KExpr.mkLet n ty val body nd md).info) arg depth (it, sc)
            = ((it3.internExpr (KExpr.mkLet n rty rval rbody nd)).1,
               ((it3.internExpr (KExpr.mkLet n rty rval rbody nd)).2,
                sc3.insert ((KExpr.letE n ty val body nd
                    (KExpr.mkLet n ty val body nd md).info).addr, depth)
                  (it3.internExpr (KExpr.mkLet n rty rval rbody nd)).1)) := by
          rw [substCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          try rw [run_bind]
          rw [hrun3]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkLet n rty rval rbody nd
            = KExpr.substSpec
                (.letE n ty val body nd
                  (KExpr.mkLet n ty val body nd md).info) arg depth := by
          rw [KExpr.substSpec, hres1, hres2, hres3]
        exact walkPost_jp hcf hwf3 hsup3 hsc3
          (hreach _ (KExpr.SubstReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @prj id field val md hval ihval =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkPrj_shape] at hreach ⊢
    have hcut' : depth.toNat + (val.size + 1) < UInt64.size := hcut
    by_cases hfast :
        (KExpr.prj id field val
          (KExpr.mkPrj id field val md).info).lbr ≤ depth
    · exact substPost_fast (.prj hval) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.prj id field val
          (KExpr.mkPrj id field val md).info).addr, depth)]? with
      | some r =>
        exact substPost_hit hcf (hreach _ (KExpr.SubstReach.self ..)) hfast
          hget hwf hsup hsc
      | none =>
        rcases hrun1 : substCached val arg depth (it, sc)
          with ⟨rval, it1, sc1⟩
        have post1 := ihval (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr hx)))
          hwf hsup hsc
        rw [hrun1] at post1
        have hres1 : rval = KExpr.substSpec val arg depth := post1.result
        have hwf1 : it1.WF := post1.wf
        have hsup1 : ∀ x, it1.ExprSupport x → S x := post1.sup
        have hsc1 : WalkScratchInv S (KExpr.substSpec · arg ·) sc1 :=
          post1.scr
        have hrun : substCached
            (.prj id field val (KExpr.mkPrj id field val md).info)
            arg depth (it, sc)
            = ((it1.internExpr (KExpr.mkPrj id field rval)).1,
               ((it1.internExpr (KExpr.mkPrj id field rval)).2,
                sc1.insert ((KExpr.prj id field val
                    (KExpr.mkPrj id field val md).info).addr, depth)
                  (it1.internExpr (KExpr.mkPrj id field rval)).1)) := by
          rw [substCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkPrj id field rval
            = KExpr.substSpec
                (.prj id field val (KExpr.mkPrj id field val md).info)
                arg depth := by
          rw [KExpr.substSpec, hres1]
        exact walkPost_jp hcf hwf1 hsup1 hsc1
          (hreach _ (KExpr.SubstReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @nat v blob md =>
    intro depth it sc hcut hreach hwf hsup hsc
    exact substPost_fast .nat hcut UInt64.zero_le hwf hsup hsc
  | @str v blob md =>
    intro depth it sc hcut hreach hwf hsup hsc
    exact substPost_fast .str hcut UInt64.zero_le hwf hsup hsc

/-- **`subst` is the pure spec** (InternM API level). Fresh scratch per
    call, so only the intern-table invariants thread in and out.
    Instantiate `S` with `SubstReach arg body depth ∪ it.ExprSupport`
    (both finite) to discharge `hreach`/`hsup` definitionally. -/
theorem subst_spec {S : KExpr .anon → Prop} {body arg : KExpr .anon}
    {depth : UInt64} {it : InternTable .anon}
    (hcf : KExpr.CollisionFree S)
    (hconBody : KExpr.Constructed body) (hconArg : KExpr.Constructed arg)
    (hcut : depth.toNat + body.size < UInt64.size)
    (hargsz : arg.size < UInt64.size)
    (hreach : ∀ x, KExpr.SubstReach arg body depth x → S x)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x) :
    (subst body arg depth it).1 = KExpr.substSpec body arg depth ∧
    (subst body arg depth it).2.WF ∧
    (∀ x, (subst body arg depth it).2.ExprSupport x → S x) := by
  by_cases hfast : body.lbr ≤ depth
  · have hrun : subst body arg depth it = (body, it) := by
      rw [subst, if_pos hfast]
      rfl
    rw [hrun]
    exact ⟨(KExpr.substSpec_id hconBody hcut hfast).symm, hwf, hsup⟩
  · have post := substCached_spec hcf hconArg hargsz hconBody
      (depth := depth) (it := it) (sc := {}) hcut hreach hwf hsup
      (WalkScratchInv.empty S _)
    have hrun : subst body arg depth it
        = ((substCached body arg depth (it, {})).1,
           (substCached body arg depth (it, {})).2.1) := by
      rw [subst, if_neg hfast]
      rfl
    rw [hrun]
    exact ⟨post.result, post.wf, post.sup⟩

/-! ## The `simulSubst` walker

Same discipline; the `var` arm replaces a RANGE `[depth, depth + n)` of
indices by lifted array elements (`lift substs[i - depth] depth 0`,
composed as in `subst`), and — unlike the single-substitution walker —
memoizes the lift result directly with an early return, skipping the
outer intern tail. Indices at or above `depth + n` shift down by `n`.

The `UInt64` range arithmetic (`depth + n`) forces a combined no-wrap
bound `depth + body.size + substs.size < 2⁶⁴`, which threads through
binder descent exactly like the plain size bound. -/

private theorem toNat_toUInt64 (k : Nat) :
    k.toUInt64.toNat = k % UInt64.size := by
  unfold Nat.toUInt64
  rfl

namespace KExpr

/-- Pure simultaneous substitution: `Var(depth + j) ↦ substs[j]` lifted
    by `depth`, indices ≥ `depth + n` shift down by `n`. Anon-mode spec —
    mirrors `simulSubstCached`'s rebuild arms exactly. -/
def simulSubstSpec (body : KExpr .anon) (substs : Array (KExpr .anon))
    (depth : UInt64) : KExpr .anon :=
  match body with
  | .var i _ _ =>
    if i ≥ depth && i < depth + substs.size.toUInt64 then
      liftSpec substs[(i - depth).toNat]! depth 0
    else if i ≥ depth + substs.size.toUInt64 then
      mkVar (i - substs.size.toUInt64) (anonName (m := .anon))
    else body
  | .app f x _ =>
    mkApp (simulSubstSpec f substs depth) (simulSubstSpec x substs depth)
  | .lam n bi ty inner _ =>
    mkLam n bi (simulSubstSpec ty substs depth)
      (simulSubstSpec inner substs (depth + 1))
  | .all n bi ty inner _ =>
    mkAll n bi (simulSubstSpec ty substs depth)
      (simulSubstSpec inner substs (depth + 1))
  | .letE n ty val inner nd _ =>
    mkLet n (simulSubstSpec ty substs depth)
      (simulSubstSpec val substs depth)
      (simulSubstSpec inner substs (depth + 1)) nd
  | .prj id field val _ => mkPrj id field (simulSubstSpec val substs depth)
  | body => body

/-- The `lbr ≤ depth` fast path is sound: every loose index is below the
    substitution window. -/
theorem simulSubstSpec_id {body : KExpr .anon}
    {substs : Array (KExpr .anon)} {depth : UInt64}
    (hcon : Constructed body)
    (hbig : depth.toNat + body.size + substs.size < UInt64.size)
    (hlbr : body.lbr ≤ depth) :
    simulSubstSpec body substs depth = body := by
  induction hcon generalizing depth with
  | @var idx name md hidx =>
    rw [mkVar_lbr] at hlbr
    have hbig' : depth.toNat + 1 + substs.size < UInt64.size := hbig
    have hle : idx.toNat + 1 ≤ depth.toNat := by
      have h := UInt64.le_iff_toNat_le.mp hlbr
      rwa [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt hidx] at h
    have hsz : substs.size.toUInt64.toNat = substs.size := by
      rw [toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    have hnn : (depth + substs.size.toUInt64).toNat
        = depth.toNat + substs.size := by
      rw [UInt64.toNat_add, hsz]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    have hge : ¬ (idx ≥ depth) := fun h => by
      have := UInt64.le_iff_toNat_le.mp h
      omega
    have hb1 : ¬ ((idx ≥ depth && idx < depth + substs.size.toUInt64)
        = true) := by
      rw [decide_eq_false hge, Bool.false_and]
      exact Bool.false_ne_true
    have hge2 : ¬ (idx ≥ depth + substs.size.toUInt64) := fun h => by
      have := UInt64.le_iff_toNat_le.mp h
      omega
    rw [mkVar_shape, simulSubstSpec, if_neg hb1, if_neg hge2]
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | @app f a md hf ha ihf iha =>
    rw [mkApp_lbr] at hlbr
    rw [mkApp_shape, size] at hbig
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    rw [mkApp_shape, simulSubstSpec,
      ihf (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      iha (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.2)]
    exact mkApp_shape f a md
  | @lam n bi ty body md hty hbody ihty ihbody =>
    rw [mkLam_lbr] at hlbr
    rw [mkLam_shape, size] at hbig
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
    rw [mkLam_shape, simulSubstSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkLam_shape n bi ty body md
  | @all n bi ty body md hty hbody ihty ihbody =>
    rw [mkAll_lbr] at hlbr
    rw [mkAll_shape, size] at hbig
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
    rw [mkAll_shape, simulSubstSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkAll_shape n bi ty body md
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    rw [mkLet_lbr] at hlbr
    rw [mkLet_shape, size] at hbig
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, toNat_max, Nat.max_le, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
    rw [mkLet_shape, simulSubstSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.1.1),
      ihval (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.1.2),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkLet_shape n ty val body nd md
  | @prj id field val md hval ihval =>
    rw [mkPrj_lbr] at hlbr
    rw [mkPrj_shape, size] at hbig
    rw [mkPrj_shape, simulSubstSpec,
      ihval (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig) hlbr]
    exact mkPrj_shape id field val md
  | nat => rfl
  | str => rfl

/-- Everything the `simulSubstCached` walk can touch. At `var` nodes the
    composed lift's footprint enters through the pattern's own index
    (out-of-range indices contribute the harmless `default`-element
    reach — a superset keeps `S` simple and still finite). -/
def SimulSubstReach (substs : Array (KExpr .anon)) :
    KExpr .anon → UInt64 → KExpr .anon → Prop
  | body, d, x =>
    x = body ∨ x = simulSubstSpec body substs d ∨
      match body with
      | .var i _ _ => LiftReach d substs[(i - d).toNat]! 0 x
      | .app f a _ =>
        SimulSubstReach substs f d x ∨ SimulSubstReach substs a d x
      | .lam _ _ ty inner _ =>
        SimulSubstReach substs ty d x ∨
          SimulSubstReach substs inner (d + 1) x
      | .all _ _ ty inner _ =>
        SimulSubstReach substs ty d x ∨
          SimulSubstReach substs inner (d + 1) x
      | .letE _ ty val inner _ _ =>
        SimulSubstReach substs ty d x ∨ SimulSubstReach substs val d x ∨
          SimulSubstReach substs inner (d + 1) x
      | .prj _ _ val _ => SimulSubstReach substs val d x
      | _ => False

theorem SimulSubstReach.self (substs : Array (KExpr .anon))
    (body : KExpr .anon) (d : UInt64) :
    SimulSubstReach substs body d body := by
  cases body <;> exact .inl rfl

theorem SimulSubstReach.spec (substs : Array (KExpr .anon))
    (body : KExpr .anon) (d : UInt64) :
    SimulSubstReach substs body d (simulSubstSpec body substs d) := by
  cases body <;> exact .inr (.inl rfl)

end KExpr

/-- Fast path (`lbr ≤ depth`). -/
private theorem simulPost_fast {S : KExpr .anon → Prop}
    {body : KExpr .anon} {substs : Array (KExpr .anon)} {depth : UInt64}
    {it : InternTable .anon} {sc : Scratch .anon}
    (hcon : KExpr.Constructed body)
    (hbig : depth.toNat + body.size + substs.size < UInt64.size)
    (hfast : body.lbr ≤ depth)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : WalkScratchInv S (KExpr.simulSubstSpec · substs ·) sc) :
    WalkPost S (KExpr.simulSubstSpec · substs ·) depth body
      (simulSubstCached body substs depth (it, sc)) := by
  have hrun : simulSubstCached body substs depth (it, sc)
      = (body, (it, sc)) := by
    rw [simulSubstCached, if_pos hfast]
    rfl
  rw [hrun]
  exact ⟨(KExpr.simulSubstSpec_id hcon hbig hfast).symm, hwf, hsup, hsc⟩

/-- Scratch hit. -/
private theorem simulPost_hit {S : KExpr .anon → Prop}
    {body r : KExpr .anon} {substs : Array (KExpr .anon)} {depth : UInt64}
    {it : InternTable .anon} {sc : Scratch .anon}
    (hcf : KExpr.CollisionFree S) (hSe : S body)
    (hfast : ¬ body.lbr ≤ depth)
    (hget : sc[(body.addr, depth)]? = some r)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : WalkScratchInv S (KExpr.simulSubstSpec · substs ·) sc) :
    WalkPost S (KExpr.simulSubstSpec · substs ·) depth body
      (simulSubstCached body substs depth (it, sc)) := by
  have hrun : simulSubstCached body substs depth (it, sc)
      = (r, (it, sc)) := by
    rw [simulSubstCached, if_neg hfast, run_pure_bind]
    simp only []
    rw [run_scratchGet_bind, hget]
    rfl
  rw [hrun]
  refine ⟨?_, hwf, hsup, hsc⟩
  obtain ⟨w, hwS, hwaddr, hrspec⟩ := hsc _ _ _ hget
  have hwe : w = body := by
    have h := hcf hwS hSe hwaddr
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at h
  show r = KExpr.simulSubstSpec body substs depth
  rw [hrspec, hwe]

/-- **WalkM memo-soundness for `simulSubst`**: the memoized, interning
    walker computes exactly the pure spec, composing `lift_spec` at
    every in-range `var` and memoizing that result via the early-return
    path (no re-intern — the lift already interned it). -/
theorem simulSubstCached_spec {S : KExpr .anon → Prop}
    {substs : Array (KExpr .anon)}
    (hcf : KExpr.CollisionFree S)
    (hconS : ∀ k, k < substs.size → KExpr.Constructed substs[k]!)
    (hszS : ∀ k, k < substs.size → substs[k]!.size < UInt64.size)
    {body : KExpr .anon} (hcon : KExpr.Constructed body) :
    ∀ {depth : UInt64} {it : InternTable .anon} {sc : Scratch .anon},
      depth.toNat + body.size + substs.size < UInt64.size →
      (∀ x, KExpr.SimulSubstReach substs body depth x → S x) →
      it.WF → (∀ x, it.ExprSupport x → S x) →
      WalkScratchInv S (KExpr.simulSubstSpec · substs ·) sc →
      WalkPost S (KExpr.simulSubstSpec · substs ·) depth body
        (simulSubstCached body substs depth (it, sc)) := by
  induction hcon with
  | @var idx name md hidx =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkVar_shape] at hreach ⊢
    by_cases hfast :
        (KExpr.var idx name (KExpr.mkVar idx name md).info).lbr ≤ depth
    · exact simulPost_fast (.var hidx) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.var idx name
          (KExpr.mkVar idx name md).info).addr, depth)]? with
      | some r =>
        exact simulPost_hit hcf (hreach _ (KExpr.SimulSubstReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        have hbig' : depth.toNat + 1 + substs.size < UInt64.size := hbig
        have hsz : substs.size.toUInt64.toNat = substs.size := by
          rw [toNat_toUInt64]
          exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
        have hnn : (depth + substs.size.toUInt64).toNat
            = depth.toNat + substs.size := by
          rw [UInt64.toNat_add, hsz]
          exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
        have hfast' : ¬ (idx + 1 ≤ depth) := hfast
        have hgei : depth.toNat ≤ idx.toNat := by
          have h1 : ¬ (idx.toNat + 1 ≤ depth.toNat) := fun h =>
            hfast' (UInt64.le_iff_toNat_le.mpr (by
              rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt hidx]
              exact h))
          omega
        by_cases hin :
            (idx ≥ depth && idx < depth + substs.size.toUInt64) = true
        · -- In range: compose the lift, memoize it, early-return.
          have hlt : idx.toNat < depth.toNat + substs.size := by
            have h2 := (Bool.and_eq_true_iff.mp hin).2
            have h3 := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true h2)
            omega
          have hk : (idx - depth).toNat < substs.size := by
            rw [UInt64.toNat_sub_of_le idx depth
              (UInt64.le_iff_toNat_le.mpr hgei)]
            omega
          rcases hlift : lift substs[(idx - depth).toNat]! depth 0 it
            with ⟨rl, it1⟩
          have postL := lift_spec (S := S)
            (e := substs[(idx - depth).toNat]!) (shift := depth)
            (cutoff := 0) (it := it) hcf (hconS _ hk)
            (by show 0 + substs[(idx - depth).toNat]!.size < UInt64.size
                have := hszS _ hk
                omega)
            (fun x hx => hreach x (.inr (.inr hx)))
            hwf hsup
          rw [hlift] at postL
          have hres : rl
              = KExpr.liftSpec substs[(idx - depth).toNat]! depth 0 :=
            postL.1
          have hwf1 : it1.WF := postL.2.1
          have hsup1 : ∀ x, it1.ExprSupport x → S x := postL.2.2
          have hrun : simulSubstCached
              (.var idx name (KExpr.mkVar idx name md).info) substs depth
              (it, sc)
              = (rl, (it1, sc.insert ((KExpr.var idx name
                  (KExpr.mkVar idx name md).info).addr, depth) rl)) := by
            rw [simulSubstCached, if_neg hfast, run_pure_bind]
            try simp only []
            rw [run_scratchGet_bind, hget]
            try simp (config := { proj := false }) only []
            try rw [run_pure_bind]
            try simp only []
            rw [if_pos hin]
            rw [run_liftIntern_bind, hlift]
            try simp only []
            rfl
          rw [hrun]
          have hcand : rl = KExpr.simulSubstSpec
              (.var idx name (KExpr.mkVar idx name md).info)
              substs depth := by
            rw [KExpr.simulSubstSpec, if_pos hin]
            exact hres
          exact ⟨hcand, hwf1, hsup1,
            hsc.insert (hreach _ (KExpr.SimulSubstReach.self ..)) hcand⟩
        · by_cases hge2 : idx ≥ depth + substs.size.toUInt64
          · -- Above the window: rebuild with the shifted-down index.
            have hrun : simulSubstCached
                (.var idx name (KExpr.mkVar idx name md).info) substs
                depth (it, sc)
                = ((it.internExpr (KExpr.mkVar
                      (idx - substs.size.toUInt64)
                      (anonName (m := .anon)))).1,
                   ((it.internExpr (KExpr.mkVar
                       (idx - substs.size.toUInt64)
                       (anonName (m := .anon)))).2,
                    sc.insert ((KExpr.var idx name
                        (KExpr.mkVar idx name md).info).addr, depth)
                      (it.internExpr (KExpr.mkVar
                        (idx - substs.size.toUInt64)
                        (anonName (m := .anon)))).1)) := by
              rw [simulSubstCached, if_neg hfast, run_pure_bind]
              try simp only []
              rw [run_scratchGet_bind, hget]
              try simp (config := { proj := false }) only []
              try rw [run_pure_bind]
              try simp only []
              rw [if_neg hin, if_pos hge2]
              rfl
            rw [hrun]
            have hcand : KExpr.mkVar (idx - substs.size.toUInt64)
                (anonName (m := .anon))
                = KExpr.simulSubstSpec
                    (.var idx name (KExpr.mkVar idx name md).info)
                    substs depth := by
              rw [KExpr.simulSubstSpec, if_neg hin, if_pos hge2]
            exact walkPost_jp hcf hwf hsup hsc
              (hreach _ (KExpr.SimulSubstReach.self ..))
              (hreach _ (.inr (.inl hcand)))
              hcand
          · -- Between the guards: impossible once the fast path declined.
            exfalso
            have hd : decide (idx ≥ depth) = true :=
              decide_eq_true (UInt64.le_iff_toNat_le.mpr hgei)
            have hnlt : ¬ (idx < depth + substs.size.toUInt64) := fun h =>
              hin (by rw [hd, decide_eq_true h]; rfl)
            have hgen : depth.toNat + substs.size ≤ idx.toNat := by
              have h1 : ¬ (idx.toNat
                  < (depth + substs.size.toUInt64).toNat) := fun h =>
                hnlt (UInt64.lt_iff_toNat_lt.mpr h)
              omega
            exact hge2 (UInt64.le_iff_toNat_le.mpr (by rw [hnn]; omega))
  | @fvar id name md =>
    intro depth it sc hbig hreach hwf hsup hsc
    exact simulPost_fast .fvar hbig UInt64.zero_le hwf hsup hsc
  | @sort u md =>
    intro depth it sc hbig hreach hwf hsup hsc
    exact simulPost_fast .sort hbig UInt64.zero_le hwf hsup hsc
  | @const id us md =>
    intro depth it sc hbig hreach hwf hsup hsc
    exact simulPost_fast .const hbig UInt64.zero_le hwf hsup hsc
  | @app f a md hf ha ihf iha =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkApp_shape] at hreach ⊢
    have hbig' :
        depth.toNat + (f.size + a.size + 1) + substs.size < UInt64.size :=
      hbig
    by_cases hfast :
        (KExpr.app f a (KExpr.mkApp f a md).info).lbr ≤ depth
    · exact simulPost_fast (.app hf ha) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.app f a
          (KExpr.mkApp f a md).info).addr, depth)]? with
      | some r =>
        exact simulPost_hit hcf (hreach _ (KExpr.SimulSubstReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : simulSubstCached f substs depth (it, sc)
          with ⟨rf, it1, sc1⟩
        have post1 := ihf (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : simulSubstCached a substs depth (it1, sc1)
          with ⟨ra, it2, sc2⟩
        have post2 := iha (depth := depth) (it := it1) (sc := sc1)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rf = KExpr.simulSubstSpec f substs depth :=
          post1.result
        have hres2 : ra = KExpr.simulSubstSpec a substs depth :=
          post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.simulSubstSpec · substs ·)
            sc2 := post2.scr
        have hrun : simulSubstCached
            (.app f a (KExpr.mkApp f a md).info) substs depth (it, sc)
            = ((it2.internExpr (KExpr.mkApp rf ra)).1,
               ((it2.internExpr (KExpr.mkApp rf ra)).2,
                sc2.insert ((KExpr.app f a
                    (KExpr.mkApp f a md).info).addr, depth)
                  (it2.internExpr (KExpr.mkApp rf ra)).1)) := by
          rw [simulSubstCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkApp rf ra
            = KExpr.simulSubstSpec (.app f a (KExpr.mkApp f a md).info)
                substs depth := by
          rw [KExpr.simulSubstSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.SimulSubstReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @lam n bi ty body md hty hbody ihty ihbody =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkLam_shape] at hreach ⊢
    have hbig' :
        depth.toNat + (ty.size + body.size + 1) + substs.size
          < UInt64.size := hbig
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    by_cases hfast :
        (KExpr.lam n bi ty body
          (KExpr.mkLam n bi ty body md).info).lbr ≤ depth
    · exact simulPost_fast (.lam hty hbody) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.lam n bi ty body
          (KExpr.mkLam n bi ty body md).info).addr, depth)]? with
      | some r =>
        exact simulPost_hit hcf (hreach _ (KExpr.SimulSubstReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : simulSubstCached ty substs depth (it, sc)
          with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : simulSubstCached body substs (depth + 1) (it1, sc1)
          with ⟨rbody, it2, sc2⟩
        have post2 := ihbody (depth := depth + 1) (it := it1) (sc := sc1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rty = KExpr.simulSubstSpec ty substs depth :=
          post1.result
        have hres2 : rbody = KExpr.simulSubstSpec body substs (depth + 1) :=
          post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.simulSubstSpec · substs ·)
            sc2 := post2.scr
        have hrun : simulSubstCached
            (.lam n bi ty body (KExpr.mkLam n bi ty body md).info)
            substs depth (it, sc)
            = ((it2.internExpr (KExpr.mkLam n bi rty rbody)).1,
               ((it2.internExpr (KExpr.mkLam n bi rty rbody)).2,
                sc2.insert ((KExpr.lam n bi ty body
                    (KExpr.mkLam n bi ty body md).info).addr, depth)
                  (it2.internExpr (KExpr.mkLam n bi rty rbody)).1)) := by
          rw [simulSubstCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkLam n bi rty rbody
            = KExpr.simulSubstSpec
                (.lam n bi ty body (KExpr.mkLam n bi ty body md).info)
                substs depth := by
          rw [KExpr.simulSubstSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.SimulSubstReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @all n bi ty body md hty hbody ihty ihbody =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkAll_shape] at hreach ⊢
    have hbig' :
        depth.toNat + (ty.size + body.size + 1) + substs.size
          < UInt64.size := hbig
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    by_cases hfast :
        (KExpr.all n bi ty body
          (KExpr.mkAll n bi ty body md).info).lbr ≤ depth
    · exact simulPost_fast (.all hty hbody) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.all n bi ty body
          (KExpr.mkAll n bi ty body md).info).addr, depth)]? with
      | some r =>
        exact simulPost_hit hcf (hreach _ (KExpr.SimulSubstReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : simulSubstCached ty substs depth (it, sc)
          with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : simulSubstCached body substs (depth + 1) (it1, sc1)
          with ⟨rbody, it2, sc2⟩
        have post2 := ihbody (depth := depth + 1) (it := it1) (sc := sc1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rty = KExpr.simulSubstSpec ty substs depth :=
          post1.result
        have hres2 : rbody = KExpr.simulSubstSpec body substs (depth + 1) :=
          post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.simulSubstSpec · substs ·)
            sc2 := post2.scr
        have hrun : simulSubstCached
            (.all n bi ty body (KExpr.mkAll n bi ty body md).info)
            substs depth (it, sc)
            = ((it2.internExpr (KExpr.mkAll n bi rty rbody)).1,
               ((it2.internExpr (KExpr.mkAll n bi rty rbody)).2,
                sc2.insert ((KExpr.all n bi ty body
                    (KExpr.mkAll n bi ty body md).info).addr, depth)
                  (it2.internExpr (KExpr.mkAll n bi rty rbody)).1)) := by
          rw [simulSubstCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkAll n bi rty rbody
            = KExpr.simulSubstSpec
                (.all n bi ty body (KExpr.mkAll n bi ty body md).info)
                substs depth := by
          rw [KExpr.simulSubstSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.SimulSubstReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkLet_shape] at hreach ⊢
    have hbig' :
        depth.toNat + (ty.size + val.size + body.size + 1) + substs.size
          < UInt64.size := hbig
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    by_cases hfast :
        (KExpr.letE n ty val body nd
          (KExpr.mkLet n ty val body nd md).info).lbr ≤ depth
    · exact simulPost_fast (.letE hty hval hbody) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.letE n ty val body nd
          (KExpr.mkLet n ty val body nd md).info).addr, depth)]? with
      | some r =>
        exact simulPost_hit hcf (hreach _ (KExpr.SimulSubstReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : simulSubstCached ty substs depth (it, sc)
          with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : simulSubstCached val substs depth (it1, sc1)
          with ⟨rval, it2, sc2⟩
        have post2 := ihval (depth := depth) (it := it1) (sc := sc1)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inr (.inl hx)))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        rcases hrun3 : simulSubstCached body substs (depth + 1) (it2, sc2)
          with ⟨rbody, it3, sc3⟩
        have post3 := ihbody (depth := depth + 1) (it := it2) (sc := sc2)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inr (.inr hx)))))
          post2.wf post2.sup post2.scr
        rw [hrun3] at post3
        have hres1 : rty = KExpr.simulSubstSpec ty substs depth :=
          post1.result
        have hres2 : rval = KExpr.simulSubstSpec val substs depth :=
          post2.result
        have hres3 : rbody = KExpr.simulSubstSpec body substs (depth + 1) :=
          post3.result
        have hwf3 : it3.WF := post3.wf
        have hsup3 : ∀ x, it3.ExprSupport x → S x := post3.sup
        have hsc3 : WalkScratchInv S (KExpr.simulSubstSpec · substs ·)
            sc3 := post3.scr
        have hrun : simulSubstCached
            (.letE n ty val body nd
              (KExpr.mkLet n ty val body nd md).info) substs depth (it, sc)
            = ((it3.internExpr (KExpr.mkLet n rty rval rbody nd)).1,
               ((it3.internExpr (KExpr.mkLet n rty rval rbody nd)).2,
                sc3.insert ((KExpr.letE n ty val body nd
                    (KExpr.mkLet n ty val body nd md).info).addr, depth)
                  (it3.internExpr
                    (KExpr.mkLet n rty rval rbody nd)).1)) := by
          rw [simulSubstCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          try rw [run_bind]
          rw [hrun3]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkLet n rty rval rbody nd
            = KExpr.simulSubstSpec
                (.letE n ty val body nd
                  (KExpr.mkLet n ty val body nd md).info)
                substs depth := by
          rw [KExpr.simulSubstSpec, hres1, hres2, hres3]
        exact walkPost_jp hcf hwf3 hsup3 hsc3
          (hreach _ (KExpr.SimulSubstReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @prj id field val md hval ihval =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkPrj_shape] at hreach ⊢
    have hbig' :
        depth.toNat + (val.size + 1) + substs.size < UInt64.size := hbig
    by_cases hfast :
        (KExpr.prj id field val
          (KExpr.mkPrj id field val md).info).lbr ≤ depth
    · exact simulPost_fast (.prj hval) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.prj id field val
          (KExpr.mkPrj id field val md).info).addr, depth)]? with
      | some r =>
        exact simulPost_hit hcf (hreach _ (KExpr.SimulSubstReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : simulSubstCached val substs depth (it, sc)
          with ⟨rval, it1, sc1⟩
        have post1 := ihval (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr hx)))
          hwf hsup hsc
        rw [hrun1] at post1
        have hres1 : rval = KExpr.simulSubstSpec val substs depth :=
          post1.result
        have hwf1 : it1.WF := post1.wf
        have hsup1 : ∀ x, it1.ExprSupport x → S x := post1.sup
        have hsc1 : WalkScratchInv S (KExpr.simulSubstSpec · substs ·)
            sc1 := post1.scr
        have hrun : simulSubstCached
            (.prj id field val (KExpr.mkPrj id field val md).info)
            substs depth (it, sc)
            = ((it1.internExpr (KExpr.mkPrj id field rval)).1,
               ((it1.internExpr (KExpr.mkPrj id field rval)).2,
                sc1.insert ((KExpr.prj id field val
                    (KExpr.mkPrj id field val md).info).addr, depth)
                  (it1.internExpr (KExpr.mkPrj id field rval)).1)) := by
          rw [simulSubstCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkPrj id field rval
            = KExpr.simulSubstSpec
                (.prj id field val (KExpr.mkPrj id field val md).info)
                substs depth := by
          rw [KExpr.simulSubstSpec, hres1]
        exact walkPost_jp hcf hwf1 hsup1 hsc1
          (hreach _ (KExpr.SimulSubstReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @nat v blob md =>
    intro depth it sc hbig hreach hwf hsup hsc
    exact simulPost_fast .nat hbig UInt64.zero_le hwf hsup hsc
  | @str v blob md =>
    intro depth it sc hbig hreach hwf hsup hsc
    exact simulPost_fast .str hbig UInt64.zero_le hwf hsup hsc

/-- **`simulSubst` is the pure spec** (InternM API level). -/
theorem simulSubst_spec {S : KExpr .anon → Prop} {body : KExpr .anon}
    {substs : Array (KExpr .anon)} {depth : UInt64}
    {it : InternTable .anon}
    (hcf : KExpr.CollisionFree S)
    (hconBody : KExpr.Constructed body)
    (hconS : ∀ k, k < substs.size → KExpr.Constructed substs[k]!)
    (hszS : ∀ k, k < substs.size → substs[k]!.size < UInt64.size)
    (hbig : depth.toNat + body.size + substs.size < UInt64.size)
    (hreach : ∀ x, KExpr.SimulSubstReach substs body depth x → S x)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x) :
    (simulSubst body substs depth it).1
      = KExpr.simulSubstSpec body substs depth ∧
    (simulSubst body substs depth it).2.WF ∧
    (∀ x, (simulSubst body substs depth it).2.ExprSupport x → S x) := by
  by_cases hfast : body.lbr ≤ depth
  · have hrun : simulSubst body substs depth it = (body, it) := by
      rw [simulSubst, if_pos hfast]
      rfl
    rw [hrun]
    exact ⟨(KExpr.simulSubstSpec_id hconBody hbig hfast).symm, hwf, hsup⟩
  · have post := simulSubstCached_spec hcf hconS hszS hconBody
      (depth := depth) (it := it) (sc := {}) hbig hreach hwf hsup
      (WalkScratchInv.empty S _)
    have hrun : simulSubst body substs depth it
        = ((simulSubstCached body substs depth (it, {})).1,
           (simulSubstCached body substs depth (it, {})).2.1) := by
      rw [simulSubst, if_neg hfast]
      rfl
    rw [hrun]
    exact ⟨post.result, post.wf, post.sup⟩

/-! ## The `instantiateRev` walker

`simulSubst`'s shape with a pure in-range arm: the replacement is read
directly off the array in reverse order (`Var(depth) ↦ fvars[n-1]`, …)
with no lifting — replacements are fvar-shaped and closed — and no
interning (array elements are already interned). The reach set
therefore needs no lift footprint: the in-range result IS the spec
image, already covered by the spec disjunct. -/

namespace KExpr

/-- Pure reverse instantiation. Anon-mode spec — mirrors
    `instantiateRevCached`'s rebuild arms exactly. -/
def instantiateRevSpec (body : KExpr .anon) (fvars : Array (KExpr .anon))
    (depth : UInt64) : KExpr .anon :=
  match body with
  | .var i _ _ =>
    if i ≥ depth && i < depth + fvars.size.toUInt64 then
      fvars[(fvars.size.toUInt64 - 1 - (i - depth)).toNat]!
    else if i ≥ depth + fvars.size.toUInt64 then
      mkVar (i - fvars.size.toUInt64) (anonName (m := .anon))
    else body
  | .app f x _ =>
    mkApp (instantiateRevSpec f fvars depth)
      (instantiateRevSpec x fvars depth)
  | .lam n bi ty inner _ =>
    mkLam n bi (instantiateRevSpec ty fvars depth)
      (instantiateRevSpec inner fvars (depth + 1))
  | .all n bi ty inner _ =>
    mkAll n bi (instantiateRevSpec ty fvars depth)
      (instantiateRevSpec inner fvars (depth + 1))
  | .letE n ty val inner nd _ =>
    mkLet n (instantiateRevSpec ty fvars depth)
      (instantiateRevSpec val fvars depth)
      (instantiateRevSpec inner fvars (depth + 1)) nd
  | .prj id field val _ =>
    mkPrj id field (instantiateRevSpec val fvars depth)
  | body => body

/-- The `lbr ≤ depth` fast path is sound. -/
theorem instantiateRevSpec_id {body : KExpr .anon}
    {fvars : Array (KExpr .anon)} {depth : UInt64}
    (hcon : Constructed body)
    (hbig : depth.toNat + body.size + fvars.size < UInt64.size)
    (hlbr : body.lbr ≤ depth) :
    instantiateRevSpec body fvars depth = body := by
  induction hcon generalizing depth with
  | @var idx name md hidx =>
    rw [mkVar_lbr] at hlbr
    have hbig' : depth.toNat + 1 + fvars.size < UInt64.size := hbig
    have hle : idx.toNat + 1 ≤ depth.toNat := by
      have h := UInt64.le_iff_toNat_le.mp hlbr
      rwa [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt hidx] at h
    have hsz : fvars.size.toUInt64.toNat = fvars.size := by
      rw [toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    have hnn : (depth + fvars.size.toUInt64).toNat
        = depth.toNat + fvars.size := by
      rw [UInt64.toNat_add, hsz]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    have hge : ¬ (idx ≥ depth) := fun h => by
      have := UInt64.le_iff_toNat_le.mp h
      omega
    have hb1 : ¬ ((idx ≥ depth && idx < depth + fvars.size.toUInt64)
        = true) := by
      rw [decide_eq_false hge, Bool.false_and]
      exact Bool.false_ne_true
    have hge2 : ¬ (idx ≥ depth + fvars.size.toUInt64) := fun h => by
      have := UInt64.le_iff_toNat_le.mp h
      omega
    rw [mkVar_shape, instantiateRevSpec, if_neg hb1, if_neg hge2]
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | @app f a md hf ha ihf iha =>
    rw [mkApp_lbr] at hlbr
    rw [mkApp_shape, size] at hbig
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    rw [mkApp_shape, instantiateRevSpec,
      ihf (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      iha (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.2)]
    exact mkApp_shape f a md
  | @lam n bi ty body md hty hbody ihty ihbody =>
    rw [mkLam_lbr] at hlbr
    rw [mkLam_shape, size] at hbig
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
    rw [mkLam_shape, instantiateRevSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkLam_shape n bi ty body md
  | @all n bi ty body md hty hbody ihty ihbody =>
    rw [mkAll_lbr] at hlbr
    rw [mkAll_shape, size] at hbig
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
    rw [mkAll_shape, instantiateRevSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkAll_shape n bi ty body md
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    rw [mkLet_lbr] at hlbr
    rw [mkLet_shape, size] at hbig
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, toNat_max, Nat.max_le, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
    rw [mkLet_shape, instantiateRevSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.1.1),
      ihval (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr hmax.1.2),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig)
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkLet_shape n ty val body nd md
  | @prj id field val md hval ihval =>
    rw [mkPrj_lbr] at hlbr
    rw [mkPrj_shape, size] at hbig
    rw [mkPrj_shape, instantiateRevSpec,
      ihval (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig) hlbr]
    exact mkPrj_shape id field val md
  | nat => rfl
  | str => rfl

/-- The empty-array fast path is sound: with `n = 0` the range guard is
    vacuous and the shift-down arm rebuilds `Var(i - 0) = Var(i)` (the
    anon-mode metadata fields are all `Unit`, so the rebuild is the
    original node). -/
theorem instantiateRevSpec_empty {body : KExpr .anon}
    {fvars : Array (KExpr .anon)} {depth : UInt64}
    (hcon : Constructed body) (hemp : fvars.size = 0) :
    instantiateRevSpec body fvars depth = body := by
  induction hcon generalizing depth with
  | @var idx name md hidx =>
    have hsz : fvars.size.toUInt64 = 0 := by rw [hemp]; rfl
    rw [mkVar_shape, instantiateRevSpec, hsz, UInt64.add_zero]
    have hb1 : ¬ ((idx ≥ depth && idx < depth) = true) := fun h => by
      have h12 := Bool.and_eq_true_iff.mp h
      have hge := UInt64.le_iff_toNat_le.mp (of_decide_eq_true h12.1)
      have hlt := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true h12.2)
      omega
    rw [if_neg hb1]
    by_cases hge : idx ≥ depth
    · rw [if_pos hge, UInt64.sub_zero idx]
      exact (mkVar_shape idx name md).symm ▸ rfl
    · rw [if_neg hge]
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | @app f a md hf ha ihf iha =>
    rw [mkApp_shape, instantiateRevSpec, ihf (depth := depth),
      iha (depth := depth)]
    exact mkApp_shape f a md
  | @lam n bi ty body md hty hbody ihty ihbody =>
    rw [mkLam_shape, instantiateRevSpec, ihty (depth := depth),
      ihbody (depth := depth + 1)]
    exact mkLam_shape n bi ty body md
  | @all n bi ty body md hty hbody ihty ihbody =>
    rw [mkAll_shape, instantiateRevSpec, ihty (depth := depth),
      ihbody (depth := depth + 1)]
    exact mkAll_shape n bi ty body md
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    rw [mkLet_shape, instantiateRevSpec, ihty (depth := depth),
      ihval (depth := depth), ihbody (depth := depth + 1)]
    exact mkLet_shape n ty val body nd md
  | @prj id field val md hval ihval =>
    rw [mkPrj_shape, instantiateRevSpec, ihval (depth := depth)]
    exact mkPrj_shape id field val md
  | nat => rfl
  | str => rfl

/-- Everything the `instantiateRevCached` walk can touch. The `var` arm
    needs no extra footprint: its in-range result is the spec image. -/
def InstRevReach (fvars : Array (KExpr .anon)) :
    KExpr .anon → UInt64 → KExpr .anon → Prop
  | body, d, x =>
    x = body ∨ x = instantiateRevSpec body fvars d ∨
      match body with
      | .app f a _ =>
        InstRevReach fvars f d x ∨ InstRevReach fvars a d x
      | .lam _ _ ty inner _ =>
        InstRevReach fvars ty d x ∨ InstRevReach fvars inner (d + 1) x
      | .all _ _ ty inner _ =>
        InstRevReach fvars ty d x ∨ InstRevReach fvars inner (d + 1) x
      | .letE _ ty val inner _ _ =>
        InstRevReach fvars ty d x ∨ InstRevReach fvars val d x ∨
          InstRevReach fvars inner (d + 1) x
      | .prj _ _ val _ => InstRevReach fvars val d x
      | _ => False

theorem InstRevReach.self (fvars : Array (KExpr .anon))
    (body : KExpr .anon) (d : UInt64) :
    InstRevReach fvars body d body := by
  cases body <;> exact .inl rfl

theorem InstRevReach.spec (fvars : Array (KExpr .anon))
    (body : KExpr .anon) (d : UInt64) :
    InstRevReach fvars body d (instantiateRevSpec body fvars d) := by
  cases body <;> exact .inr (.inl rfl)

end KExpr

/-- Fast path (`lbr ≤ depth`). -/
private theorem instRevPost_fast {S : KExpr .anon → Prop}
    {body : KExpr .anon} {fvars : Array (KExpr .anon)} {depth : UInt64}
    {it : InternTable .anon} {sc : Scratch .anon}
    (hcon : KExpr.Constructed body)
    (hbig : depth.toNat + body.size + fvars.size < UInt64.size)
    (hfast : body.lbr ≤ depth)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : WalkScratchInv S (KExpr.instantiateRevSpec · fvars ·) sc) :
    WalkPost S (KExpr.instantiateRevSpec · fvars ·) depth body
      (instantiateRevCached body fvars depth (it, sc)) := by
  have hrun : instantiateRevCached body fvars depth (it, sc)
      = (body, (it, sc)) := by
    rw [instantiateRevCached, if_pos hfast]
    rfl
  rw [hrun]
  exact ⟨(KExpr.instantiateRevSpec_id hcon hbig hfast).symm, hwf, hsup, hsc⟩

/-- Scratch hit. -/
private theorem instRevPost_hit {S : KExpr .anon → Prop}
    {body r : KExpr .anon} {fvars : Array (KExpr .anon)} {depth : UInt64}
    {it : InternTable .anon} {sc : Scratch .anon}
    (hcf : KExpr.CollisionFree S) (hSe : S body)
    (hfast : ¬ body.lbr ≤ depth)
    (hget : sc[(body.addr, depth)]? = some r)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : WalkScratchInv S (KExpr.instantiateRevSpec · fvars ·) sc) :
    WalkPost S (KExpr.instantiateRevSpec · fvars ·) depth body
      (instantiateRevCached body fvars depth (it, sc)) := by
  have hrun : instantiateRevCached body fvars depth (it, sc)
      = (r, (it, sc)) := by
    rw [instantiateRevCached, if_neg hfast, run_pure_bind]
    simp only []
    rw [run_scratchGet_bind, hget]
    rfl
  rw [hrun]
  refine ⟨?_, hwf, hsup, hsc⟩
  obtain ⟨w, hwS, hwaddr, hrspec⟩ := hsc _ _ _ hget
  have hwe : w = body := by
    have h := hcf hwS hSe hwaddr
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at h
  show r = KExpr.instantiateRevSpec body fvars depth
  rw [hrspec, hwe]

/-- **WalkM memo-soundness for `instantiateRev`**. -/
theorem instantiateRevCached_spec {S : KExpr .anon → Prop}
    {fvars : Array (KExpr .anon)}
    (hcf : KExpr.CollisionFree S)
    {body : KExpr .anon} (hcon : KExpr.Constructed body) :
    ∀ {depth : UInt64} {it : InternTable .anon} {sc : Scratch .anon},
      depth.toNat + body.size + fvars.size < UInt64.size →
      (∀ x, KExpr.InstRevReach fvars body depth x → S x) →
      it.WF → (∀ x, it.ExprSupport x → S x) →
      WalkScratchInv S (KExpr.instantiateRevSpec · fvars ·) sc →
      WalkPost S (KExpr.instantiateRevSpec · fvars ·) depth body
        (instantiateRevCached body fvars depth (it, sc)) := by
  induction hcon with
  | @var idx name md hidx =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkVar_shape] at hreach ⊢
    by_cases hfast :
        (KExpr.var idx name (KExpr.mkVar idx name md).info).lbr ≤ depth
    · exact instRevPost_fast (.var hidx) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.var idx name
          (KExpr.mkVar idx name md).info).addr, depth)]? with
      | some r =>
        exact instRevPost_hit hcf (hreach _ (KExpr.InstRevReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        have hbig' : depth.toNat + 1 + fvars.size < UInt64.size := hbig
        have hsz : fvars.size.toUInt64.toNat = fvars.size := by
          rw [toNat_toUInt64]
          exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
        have hnn : (depth + fvars.size.toUInt64).toNat
            = depth.toNat + fvars.size := by
          rw [UInt64.toNat_add, hsz]
          exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
        have hfast' : ¬ (idx + 1 ≤ depth) := hfast
        have hgei : depth.toNat ≤ idx.toNat := by
          have h1 : ¬ (idx.toNat + 1 ≤ depth.toNat) := fun h =>
            hfast' (UInt64.le_iff_toNat_le.mpr (by
              rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt hidx]
              exact h))
          omega
        by_cases hin :
            (idx ≥ depth && idx < depth + fvars.size.toUInt64) = true
        · -- In range: pure array read, memoize, early-return.
          have hrun : instantiateRevCached
              (.var idx name (KExpr.mkVar idx name md).info) fvars depth
              (it, sc)
              = (fvars[(fvars.size.toUInt64 - 1 - (idx - depth)).toNat]!,
                 (it, sc.insert ((KExpr.var idx name
                     (KExpr.mkVar idx name md).info).addr, depth)
                   fvars[(fvars.size.toUInt64 - 1
                     - (idx - depth)).toNat]!)) := by
            rw [instantiateRevCached, if_neg hfast, run_pure_bind]
            try simp only []
            rw [run_scratchGet_bind, hget]
            try simp (config := { proj := false }) only []
            try rw [run_pure_bind]
            try simp only []
            rw [if_pos hin]
            rfl
          rw [hrun]
          have hcand :
              fvars[(fvars.size.toUInt64 - 1 - (idx - depth)).toNat]!
              = KExpr.instantiateRevSpec
                  (.var idx name (KExpr.mkVar idx name md).info)
                  fvars depth := by
            rw [KExpr.instantiateRevSpec, if_pos hin]
          exact ⟨hcand, hwf, hsup,
            hsc.insert (hreach _ (KExpr.InstRevReach.self ..)) hcand⟩
        · by_cases hge2 : idx ≥ depth + fvars.size.toUInt64
          · -- Above the window: rebuild with the shifted-down index.
            have hrun : instantiateRevCached
                (.var idx name (KExpr.mkVar idx name md).info) fvars
                depth (it, sc)
                = ((it.internExpr (KExpr.mkVar
                      (idx - fvars.size.toUInt64)
                      (anonName (m := .anon)))).1,
                   ((it.internExpr (KExpr.mkVar
                       (idx - fvars.size.toUInt64)
                       (anonName (m := .anon)))).2,
                    sc.insert ((KExpr.var idx name
                        (KExpr.mkVar idx name md).info).addr, depth)
                      (it.internExpr (KExpr.mkVar
                        (idx - fvars.size.toUInt64)
                        (anonName (m := .anon)))).1)) := by
              rw [instantiateRevCached, if_neg hfast, run_pure_bind]
              try simp only []
              rw [run_scratchGet_bind, hget]
              try simp (config := { proj := false }) only []
              try rw [run_pure_bind]
              try simp only []
              rw [if_neg hin, if_pos hge2]
              rfl
            rw [hrun]
            have hcand : KExpr.mkVar (idx - fvars.size.toUInt64)
                (anonName (m := .anon))
                = KExpr.instantiateRevSpec
                    (.var idx name (KExpr.mkVar idx name md).info)
                    fvars depth := by
              rw [KExpr.instantiateRevSpec, if_neg hin, if_pos hge2]
            exact walkPost_jp hcf hwf hsup hsc
              (hreach _ (KExpr.InstRevReach.self ..))
              (hreach _ (.inr (.inl hcand)))
              hcand
          · -- Between the guards: impossible once the fast path declined.
            exfalso
            have hd : decide (idx ≥ depth) = true :=
              decide_eq_true (UInt64.le_iff_toNat_le.mpr hgei)
            have hnlt : ¬ (idx < depth + fvars.size.toUInt64) := fun h =>
              hin (by rw [hd, decide_eq_true h]; rfl)
            have hgen : depth.toNat + fvars.size ≤ idx.toNat := by
              have h1 : ¬ (idx.toNat
                  < (depth + fvars.size.toUInt64).toNat) := fun h =>
                hnlt (UInt64.lt_iff_toNat_lt.mpr h)
              omega
            exact hge2 (UInt64.le_iff_toNat_le.mpr (by rw [hnn]; omega))
  | @fvar id name md =>
    intro depth it sc hbig hreach hwf hsup hsc
    exact instRevPost_fast .fvar hbig UInt64.zero_le hwf hsup hsc
  | @sort u md =>
    intro depth it sc hbig hreach hwf hsup hsc
    exact instRevPost_fast .sort hbig UInt64.zero_le hwf hsup hsc
  | @const id us md =>
    intro depth it sc hbig hreach hwf hsup hsc
    exact instRevPost_fast .const hbig UInt64.zero_le hwf hsup hsc
  | @app f a md hf ha ihf iha =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkApp_shape] at hreach ⊢
    have hbig' :
        depth.toNat + (f.size + a.size + 1) + fvars.size < UInt64.size :=
      hbig
    by_cases hfast :
        (KExpr.app f a (KExpr.mkApp f a md).info).lbr ≤ depth
    · exact instRevPost_fast (.app hf ha) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.app f a
          (KExpr.mkApp f a md).info).addr, depth)]? with
      | some r =>
        exact instRevPost_hit hcf (hreach _ (KExpr.InstRevReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : instantiateRevCached f fvars depth (it, sc)
          with ⟨rf, it1, sc1⟩
        have post1 := ihf (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : instantiateRevCached a fvars depth (it1, sc1)
          with ⟨ra, it2, sc2⟩
        have post2 := iha (depth := depth) (it := it1) (sc := sc1)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rf = KExpr.instantiateRevSpec f fvars depth :=
          post1.result
        have hres2 : ra = KExpr.instantiateRevSpec a fvars depth :=
          post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.instantiateRevSpec · fvars ·)
            sc2 := post2.scr
        have hrun : instantiateRevCached
            (.app f a (KExpr.mkApp f a md).info) fvars depth (it, sc)
            = ((it2.internExpr (KExpr.mkApp rf ra)).1,
               ((it2.internExpr (KExpr.mkApp rf ra)).2,
                sc2.insert ((KExpr.app f a
                    (KExpr.mkApp f a md).info).addr, depth)
                  (it2.internExpr (KExpr.mkApp rf ra)).1)) := by
          rw [instantiateRevCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkApp rf ra
            = KExpr.instantiateRevSpec
                (.app f a (KExpr.mkApp f a md).info) fvars depth := by
          rw [KExpr.instantiateRevSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.InstRevReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @lam n bi ty body md hty hbody ihty ihbody =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkLam_shape] at hreach ⊢
    have hbig' :
        depth.toNat + (ty.size + body.size + 1) + fvars.size
          < UInt64.size := hbig
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    by_cases hfast :
        (KExpr.lam n bi ty body
          (KExpr.mkLam n bi ty body md).info).lbr ≤ depth
    · exact instRevPost_fast (.lam hty hbody) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.lam n bi ty body
          (KExpr.mkLam n bi ty body md).info).addr, depth)]? with
      | some r =>
        exact instRevPost_hit hcf (hreach _ (KExpr.InstRevReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : instantiateRevCached ty fvars depth (it, sc)
          with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : instantiateRevCached body fvars (depth + 1)
          (it1, sc1) with ⟨rbody, it2, sc2⟩
        have post2 := ihbody (depth := depth + 1) (it := it1) (sc := sc1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rty = KExpr.instantiateRevSpec ty fvars depth :=
          post1.result
        have hres2 : rbody = KExpr.instantiateRevSpec body fvars
            (depth + 1) := post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.instantiateRevSpec · fvars ·)
            sc2 := post2.scr
        have hrun : instantiateRevCached
            (.lam n bi ty body (KExpr.mkLam n bi ty body md).info)
            fvars depth (it, sc)
            = ((it2.internExpr (KExpr.mkLam n bi rty rbody)).1,
               ((it2.internExpr (KExpr.mkLam n bi rty rbody)).2,
                sc2.insert ((KExpr.lam n bi ty body
                    (KExpr.mkLam n bi ty body md).info).addr, depth)
                  (it2.internExpr (KExpr.mkLam n bi rty rbody)).1)) := by
          rw [instantiateRevCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkLam n bi rty rbody
            = KExpr.instantiateRevSpec
                (.lam n bi ty body (KExpr.mkLam n bi ty body md).info)
                fvars depth := by
          rw [KExpr.instantiateRevSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.InstRevReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @all n bi ty body md hty hbody ihty ihbody =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkAll_shape] at hreach ⊢
    have hbig' :
        depth.toNat + (ty.size + body.size + 1) + fvars.size
          < UInt64.size := hbig
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    by_cases hfast :
        (KExpr.all n bi ty body
          (KExpr.mkAll n bi ty body md).info).lbr ≤ depth
    · exact instRevPost_fast (.all hty hbody) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.all n bi ty body
          (KExpr.mkAll n bi ty body md).info).addr, depth)]? with
      | some r =>
        exact instRevPost_hit hcf (hreach _ (KExpr.InstRevReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : instantiateRevCached ty fvars depth (it, sc)
          with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : instantiateRevCached body fvars (depth + 1)
          (it1, sc1) with ⟨rbody, it2, sc2⟩
        have post2 := ihbody (depth := depth + 1) (it := it1) (sc := sc1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rty = KExpr.instantiateRevSpec ty fvars depth :=
          post1.result
        have hres2 : rbody = KExpr.instantiateRevSpec body fvars
            (depth + 1) := post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.instantiateRevSpec · fvars ·)
            sc2 := post2.scr
        have hrun : instantiateRevCached
            (.all n bi ty body (KExpr.mkAll n bi ty body md).info)
            fvars depth (it, sc)
            = ((it2.internExpr (KExpr.mkAll n bi rty rbody)).1,
               ((it2.internExpr (KExpr.mkAll n bi rty rbody)).2,
                sc2.insert ((KExpr.all n bi ty body
                    (KExpr.mkAll n bi ty body md).info).addr, depth)
                  (it2.internExpr (KExpr.mkAll n bi rty rbody)).1)) := by
          rw [instantiateRevCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkAll n bi rty rbody
            = KExpr.instantiateRevSpec
                (.all n bi ty body (KExpr.mkAll n bi ty body md).info)
                fvars depth := by
          rw [KExpr.instantiateRevSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.InstRevReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkLet_shape] at hreach ⊢
    have hbig' :
        depth.toNat + (ty.size + val.size + body.size + 1) + fvars.size
          < UInt64.size := hbig
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
    by_cases hfast :
        (KExpr.letE n ty val body nd
          (KExpr.mkLet n ty val body nd md).info).lbr ≤ depth
    · exact instRevPost_fast (.letE hty hval hbody) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.letE n ty val body nd
          (KExpr.mkLet n ty val body nd md).info).addr, depth)]? with
      | some r =>
        exact instRevPost_hit hcf (hreach _ (KExpr.InstRevReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : instantiateRevCached ty fvars depth (it, sc)
          with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : instantiateRevCached val fvars depth (it1, sc1)
          with ⟨rval, it2, sc2⟩
        have post2 := ihval (depth := depth) (it := it1) (sc := sc1)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inr (.inl hx)))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        rcases hrun3 : instantiateRevCached body fvars (depth + 1)
          (it2, sc2) with ⟨rbody, it3, sc3⟩
        have post3 := ihbody (depth := depth + 1) (it := it2) (sc := sc2)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr (.inr (.inr hx)))))
          post2.wf post2.sup post2.scr
        rw [hrun3] at post3
        have hres1 : rty = KExpr.instantiateRevSpec ty fvars depth :=
          post1.result
        have hres2 : rval = KExpr.instantiateRevSpec val fvars depth :=
          post2.result
        have hres3 : rbody = KExpr.instantiateRevSpec body fvars
            (depth + 1) := post3.result
        have hwf3 : it3.WF := post3.wf
        have hsup3 : ∀ x, it3.ExprSupport x → S x := post3.sup
        have hsc3 : WalkScratchInv S (KExpr.instantiateRevSpec · fvars ·)
            sc3 := post3.scr
        have hrun : instantiateRevCached
            (.letE n ty val body nd
              (KExpr.mkLet n ty val body nd md).info) fvars depth (it, sc)
            = ((it3.internExpr (KExpr.mkLet n rty rval rbody nd)).1,
               ((it3.internExpr (KExpr.mkLet n rty rval rbody nd)).2,
                sc3.insert ((KExpr.letE n ty val body nd
                    (KExpr.mkLet n ty val body nd md).info).addr, depth)
                  (it3.internExpr
                    (KExpr.mkLet n rty rval rbody nd)).1)) := by
          rw [instantiateRevCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          try rw [run_bind]
          rw [hrun3]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkLet n rty rval rbody nd
            = KExpr.instantiateRevSpec
                (.letE n ty val body nd
                  (KExpr.mkLet n ty val body nd md).info)
                fvars depth := by
          rw [KExpr.instantiateRevSpec, hres1, hres2, hres3]
        exact walkPost_jp hcf hwf3 hsup3 hsc3
          (hreach _ (KExpr.InstRevReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @prj id field val md hval ihval =>
    intro depth it sc hbig hreach hwf hsup hsc
    rw [KExpr.mkPrj_shape] at hreach ⊢
    have hbig' :
        depth.toNat + (val.size + 1) + fvars.size < UInt64.size := hbig
    by_cases hfast :
        (KExpr.prj id field val
          (KExpr.mkPrj id field val md).info).lbr ≤ depth
    · exact instRevPost_fast (.prj hval) hbig hfast hwf hsup hsc
    · cases hget : sc[((KExpr.prj id field val
          (KExpr.mkPrj id field val md).info).addr, depth)]? with
      | some r =>
        exact instRevPost_hit hcf (hreach _ (KExpr.InstRevReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : instantiateRevCached val fvars depth (it, sc)
          with ⟨rval, it1, sc1⟩
        have post1 := ihval (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hbig')
          (fun x hx => hreach x (.inr (.inr hx)))
          hwf hsup hsc
        rw [hrun1] at post1
        have hres1 : rval = KExpr.instantiateRevSpec val fvars depth :=
          post1.result
        have hwf1 : it1.WF := post1.wf
        have hsup1 : ∀ x, it1.ExprSupport x → S x := post1.sup
        have hsc1 : WalkScratchInv S (KExpr.instantiateRevSpec · fvars ·)
            sc1 := post1.scr
        have hrun : instantiateRevCached
            (.prj id field val (KExpr.mkPrj id field val md).info)
            fvars depth (it, sc)
            = ((it1.internExpr (KExpr.mkPrj id field rval)).1,
               ((it1.internExpr (KExpr.mkPrj id field rval)).2,
                sc1.insert ((KExpr.prj id field val
                    (KExpr.mkPrj id field val md).info).addr, depth)
                  (it1.internExpr (KExpr.mkPrj id field rval)).1)) := by
          rw [instantiateRevCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkPrj id field rval
            = KExpr.instantiateRevSpec
                (.prj id field val (KExpr.mkPrj id field val md).info)
                fvars depth := by
          rw [KExpr.instantiateRevSpec, hres1]
        exact walkPost_jp hcf hwf1 hsup1 hsc1
          (hreach _ (KExpr.InstRevReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @nat v blob md =>
    intro depth it sc hbig hreach hwf hsup hsc
    exact instRevPost_fast .nat hbig UInt64.zero_le hwf hsup hsc
  | @str v blob md =>
    intro depth it sc hbig hreach hwf hsup hsc
    exact instRevPost_fast .str hbig UInt64.zero_le hwf hsup hsc

/-- **`instantiateRev` is the pure spec** (InternM API level, depth 0).
    The `fvars.isEmpty` fast path is covered by
    `instantiateRevSpec_empty`, the `lbr == 0` one by the `_id` lemma. -/
theorem instantiateRev_spec {S : KExpr .anon → Prop} {body : KExpr .anon}
    {fvars : Array (KExpr .anon)} {it : InternTable .anon}
    (hcf : KExpr.CollisionFree S)
    (hconBody : KExpr.Constructed body)
    (hbig : body.size + fvars.size < UInt64.size)
    (hreach : ∀ x, KExpr.InstRevReach fvars body 0 x → S x)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x) :
    (instantiateRev body fvars it).1
      = KExpr.instantiateRevSpec body fvars 0 ∧
    (instantiateRev body fvars it).2.WF ∧
    (∀ x, (instantiateRev body fvars it).2.ExprSupport x → S x) := by
  by_cases hfast : (fvars.isEmpty || body.lbr == 0) = true
  · have hrun : instantiateRev body fvars it = (body, it) := by
      rw [instantiateRev, if_pos hfast]
      rfl
    rw [hrun]
    refine ⟨?_, hwf, hsup⟩
    show body = KExpr.instantiateRevSpec body fvars 0
    rcases Bool.or_eq_true_iff.mp hfast with hemp | h0
    · exact (KExpr.instantiateRevSpec_empty hconBody
        (eq_of_beq (hemp : (fvars.size == 0) = true))).symm
    · exact (KExpr.instantiateRevSpec_id hconBody
        (by show 0 + body.size + fvars.size < UInt64.size; omega)
        (by rw [eq_of_beq h0]; exact UInt64.zero_le)).symm
  · have post := instantiateRevCached_spec hcf hconBody
      (depth := 0) (it := it) (sc := {})
      (by show 0 + body.size + fvars.size < UInt64.size; omega)
      hreach hwf hsup (WalkScratchInv.empty S _)
    have hrun : instantiateRev body fvars it
        = ((instantiateRevCached body fvars 0 (it, {})).1,
           (instantiateRevCached body fvars 0 (it, {})).2.1) := by
      rw [instantiateRev, if_neg hfast]
      rfl
    rw [hrun]
    exact ⟨post.result, post.wf, post.sup⟩

/-! ## The `abstractFVars` walker

The inverse of `instantiateRev`: listed fvars become bound variables
(`fvar(id) ↦ Var(depth + pos[id])`), other loose bvars shift up by `n`.
Two shape novelties: the fast guard also requires `!hasFVars` (so the
`_id` lemma carries a `hasFVars = false` coherence hypothesis, pushed
through children by the `mk*_hasFVars` equations), and the `fvar` arm
interns inside the arm with an early return — which lands on exactly
the `walkPost_jp` tuple.

The theorem is stated against an arbitrary position map `pos`; the
API-level lemma characterizing the `pos`-building fold in
`abstractFVars` is deferred until a consumer (the whnf soundness
layer) fixes the shape it needs. -/

private theorem bool_or_eq_false {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | false => exact ⟨rfl, h⟩
  | true => exact Bool.noConfusion h

namespace KExpr

@[simp] theorem mkVar_hasFVars (idx : UInt64) (name : m.F Name) (md) :
    (mkVar idx name md).hasFVars = false := rfl

@[simp] theorem mkFVar_hasFVars (id : FVarId) (name : m.F Name) (md) :
    (mkFVar id name md).hasFVars = true := rfl

@[simp] theorem mkSort_hasFVars (u : KUniv m) (md) :
    (mkSort u md).hasFVars = false := rfl

@[simp] theorem mkConst_hasFVars (id : KId m) (us : Array (KUniv m)) (md) :
    (mkConst id us md).hasFVars = false := rfl

@[simp] theorem mkApp_hasFVars (f a : KExpr m) (md) :
    (mkApp f a md).hasFVars = (f.hasFVars || a.hasFVars) := rfl

@[simp] theorem mkLam_hasFVars (n : m.F Name) (bi : m.F Lean.BinderInfo)
    (ty body : KExpr m) (md) :
    (mkLam n bi ty body md).hasFVars
      = (ty.hasFVars || body.hasFVars) := rfl

@[simp] theorem mkAll_hasFVars (n : m.F Name) (bi : m.F Lean.BinderInfo)
    (ty body : KExpr m) (md) :
    (mkAll n bi ty body md).hasFVars
      = (ty.hasFVars || body.hasFVars) := rfl

@[simp] theorem mkLet_hasFVars (n : m.F Name) (ty val body : KExpr m)
    (nd : Bool) (md) :
    (mkLet n ty val body nd md).hasFVars
      = (ty.hasFVars || val.hasFVars || body.hasFVars) := rfl

@[simp] theorem mkPrj_hasFVars (id : KId m) (field : UInt64)
    (val : KExpr m) (md) :
    (mkPrj id field val md).hasFVars = val.hasFVars := rfl

@[simp] theorem mkNat_hasFVars (v : Nat) (blob : Address) (md) :
    (mkNat (m := m) v blob md).hasFVars = false := rfl

@[simp] theorem mkStr_hasFVars (v : String) (blob : Address) (md) :
    (mkStr (m := m) v blob md).hasFVars = false := rfl

/-- Pure fvar abstraction. Anon-mode spec — mirrors
    `abstractFVarsCached`'s rebuild arms exactly. -/
def abstractFVarsSpec (body : KExpr .anon)
    (pos : Std.HashMap FVarId UInt64) (n depth : UInt64) : KExpr .anon :=
  match body with
  | .fvar id _ _ =>
    match pos[id]? with
    | some p => mkVar (depth + p) (anonName (m := .anon))
    | none => body
  | .var i name _ => if i ≥ depth then mkVar (i + n) name else body
  | .app f x _ =>
    mkApp (abstractFVarsSpec f pos n depth) (abstractFVarsSpec x pos n depth)
  | .lam nm bi ty inner _ =>
    mkLam nm bi (abstractFVarsSpec ty pos n depth)
      (abstractFVarsSpec inner pos n (depth + 1))
  | .all nm bi ty inner _ =>
    mkAll nm bi (abstractFVarsSpec ty pos n depth)
      (abstractFVarsSpec inner pos n (depth + 1))
  | .letE nm ty val inner nd _ =>
    mkLet nm (abstractFVarsSpec ty pos n depth)
      (abstractFVarsSpec val pos n depth)
      (abstractFVarsSpec inner pos n (depth + 1)) nd
  | .prj id field val _ => mkPrj id field (abstractFVarsSpec val pos n depth)
  | body => body

/-- The `!hasFVars && lbr ≤ depth` fast path is sound: no fvars to
    abstract and no loose index to shift. -/
theorem abstractFVarsSpec_id {body : KExpr .anon}
    {pos : Std.HashMap FVarId UInt64} {n depth : UInt64}
    (hcon : Constructed body)
    (hcut : depth.toNat + body.size < UInt64.size)
    (hnofv : body.hasFVars = false)
    (hlbr : body.lbr ≤ depth) :
    abstractFVarsSpec body pos n depth = body := by
  induction hcon generalizing depth with
  | @var idx name md hidx =>
    rw [mkVar_lbr] at hlbr
    have hle : idx.toNat + 1 ≤ depth.toNat := by
      have h := UInt64.le_iff_toNat_le.mp hlbr
      rwa [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt hidx] at h
    have hngt : ¬ (idx ≥ depth) := fun h => by
      have := UInt64.le_iff_toNat_le.mp h
      omega
    rw [mkVar_shape, abstractFVarsSpec, if_neg hngt]
  | @fvar id name md =>
    exact Bool.noConfusion (hnofv : (true : Bool) = false)
  | sort => rfl
  | const => rfl
  | @app f a md hf ha ihf iha =>
    rw [mkApp_lbr] at hlbr
    rw [mkApp_hasFVars] at hnofv
    rw [mkApp_shape, size] at hcut
    have hor := bool_or_eq_false hnofv
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    rw [mkApp_shape, abstractFVarsSpec,
      ihf (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut) hor.1
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      iha (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut) hor.2
        (UInt64.le_iff_toNat_le.mpr hmax.2)]
    exact mkApp_shape f a md
  | @lam nm bi ty body md hty hbody ihty ihbody =>
    rw [mkLam_lbr] at hlbr
    rw [mkLam_hasFVars] at hnofv
    rw [mkLam_shape, size] at hcut
    have hor := bool_or_eq_false hnofv
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkLam_shape, abstractFVarsSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut) hor.1
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut) hor.2
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkLam_shape nm bi ty body md
  | @all nm bi ty body md hty hbody ihty ihbody =>
    rw [mkAll_lbr] at hlbr
    rw [mkAll_hasFVars] at hnofv
    rw [mkAll_shape, size] at hcut
    have hor := bool_or_eq_false hnofv
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkAll_shape, abstractFVarsSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut) hor.1
        (UInt64.le_iff_toNat_le.mpr hmax.1),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut) hor.2
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkAll_shape nm bi ty body md
  | @letE nm ty val body nd md hty hval hbody ihty ihval ihbody =>
    rw [mkLet_lbr] at hlbr
    rw [mkLet_hasFVars] at hnofv
    rw [mkLet_shape, size] at hcut
    have hor1 := bool_or_eq_false hnofv
    have hor2 := bool_or_eq_false hor1.1
    have hmax := UInt64.le_iff_toNat_le.mp hlbr
    rw [toNat_max, toNat_max, Nat.max_le, Nat.max_le] at hmax
    have hsat := toNat_le_sat1_add_one body.lbr
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut)
    rw [mkLet_shape, abstractFVarsSpec,
      ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut) hor2.1
        (UInt64.le_iff_toNat_le.mpr hmax.1.1),
      ihval (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut) hor2.2
        (UInt64.le_iff_toNat_le.mpr hmax.1.2),
      ihbody (depth := depth + 1)
        (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut) hor1.2
        (UInt64.le_iff_toNat_le.mpr (by rw [hc1]; omega))]
    exact mkLet_shape nm ty val body nd md
  | @prj id field val md hval ihval =>
    rw [mkPrj_lbr] at hlbr
    rw [mkPrj_hasFVars] at hnofv
    rw [mkPrj_shape, size] at hcut
    rw [mkPrj_shape, abstractFVarsSpec,
      ihval (depth := depth) (Nat.lt_of_le_of_lt (by omega) hcut) hnofv
        hlbr]
    exact mkPrj_shape id field val md
  | nat => rfl
  | str => rfl

/-- Everything the `abstractFVarsCached` walk can touch. Both leaf
    rewrites (`fvar` hits and shifted `var`s) are the spec image, so no
    extra footprint is needed. -/
def AbstractReach (pos : Std.HashMap FVarId UInt64) (n : UInt64) :
    KExpr .anon → UInt64 → KExpr .anon → Prop
  | body, d, x =>
    x = body ∨ x = abstractFVarsSpec body pos n d ∨
      match body with
      | .app f a _ =>
        AbstractReach pos n f d x ∨ AbstractReach pos n a d x
      | .lam _ _ ty inner _ =>
        AbstractReach pos n ty d x ∨ AbstractReach pos n inner (d + 1) x
      | .all _ _ ty inner _ =>
        AbstractReach pos n ty d x ∨ AbstractReach pos n inner (d + 1) x
      | .letE _ ty val inner _ _ =>
        AbstractReach pos n ty d x ∨ AbstractReach pos n val d x ∨
          AbstractReach pos n inner (d + 1) x
      | .prj _ _ val _ => AbstractReach pos n val d x
      | _ => False

theorem AbstractReach.self (pos : Std.HashMap FVarId UInt64) (n : UInt64)
    (body : KExpr .anon) (d : UInt64) :
    AbstractReach pos n body d body := by
  cases body <;> exact .inl rfl

theorem AbstractReach.spec (pos : Std.HashMap FVarId UInt64) (n : UInt64)
    (body : KExpr .anon) (d : UInt64) :
    AbstractReach pos n body d (abstractFVarsSpec body pos n d) := by
  cases body <;> exact .inr (.inl rfl)

end KExpr

/-- Fast path (`!hasFVars && lbr ≤ depth`). -/
private theorem absPost_fast {S : KExpr .anon → Prop} {body : KExpr .anon}
    {pos : Std.HashMap FVarId UInt64} {n depth : UInt64}
    {it : InternTable .anon} {sc : Scratch .anon}
    (hcon : KExpr.Constructed body)
    (hcut : depth.toNat + body.size < UInt64.size)
    (hfast : (!body.hasFVars && decide (body.lbr ≤ depth)) = true)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : WalkScratchInv S (KExpr.abstractFVarsSpec · pos n ·) sc) :
    WalkPost S (KExpr.abstractFVarsSpec · pos n ·) depth body
      (abstractFVarsCached body pos n depth (it, sc)) := by
  have hrun : abstractFVarsCached body pos n depth (it, sc)
      = (body, (it, sc)) := by
    rw [abstractFVarsCached, if_pos hfast]
    rfl
  rw [hrun]
  have h12 := Bool.and_eq_true_iff.mp hfast
  have hnofv : body.hasFVars = false := by
    cases hb : body.hasFVars with
    | false => rfl
    | true =>
      rw [hb] at h12
      exact Bool.noConfusion h12.1
  exact ⟨(KExpr.abstractFVarsSpec_id hcon hcut hnofv
    (of_decide_eq_true h12.2)).symm, hwf, hsup, hsc⟩

/-- Scratch hit. -/
private theorem absPost_hit {S : KExpr .anon → Prop} {body r : KExpr .anon}
    {pos : Std.HashMap FVarId UInt64} {n depth : UInt64}
    {it : InternTable .anon} {sc : Scratch .anon}
    (hcf : KExpr.CollisionFree S) (hSe : S body)
    (hfast : ¬ (!body.hasFVars && decide (body.lbr ≤ depth)) = true)
    (hget : sc[(body.addr, depth)]? = some r)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → S x)
    (hsc : WalkScratchInv S (KExpr.abstractFVarsSpec · pos n ·) sc) :
    WalkPost S (KExpr.abstractFVarsSpec · pos n ·) depth body
      (abstractFVarsCached body pos n depth (it, sc)) := by
  have hrun : abstractFVarsCached body pos n depth (it, sc)
      = (r, (it, sc)) := by
    rw [abstractFVarsCached, if_neg hfast, run_pure_bind]
    simp only []
    rw [run_scratchGet_bind, hget]
    rfl
  rw [hrun]
  refine ⟨?_, hwf, hsup, hsc⟩
  obtain ⟨w, hwS, hwaddr, hrspec⟩ := hsc _ _ _ hget
  have hwe : w = body := by
    have h := hcf hwS hSe hwaddr
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at h
  show r = KExpr.abstractFVarsSpec body pos n depth
  rw [hrspec, hwe]

/-- **WalkM memo-soundness for `abstractFVars`** (walker level, against
    an arbitrary position map). -/
theorem abstractFVarsCached_spec {S : KExpr .anon → Prop}
    {pos : Std.HashMap FVarId UInt64} {n : UInt64}
    (hcf : KExpr.CollisionFree S)
    {body : KExpr .anon} (hcon : KExpr.Constructed body) :
    ∀ {depth : UInt64} {it : InternTable .anon} {sc : Scratch .anon},
      depth.toNat + body.size < UInt64.size →
      (∀ x, KExpr.AbstractReach pos n body depth x → S x) →
      it.WF → (∀ x, it.ExprSupport x → S x) →
      WalkScratchInv S (KExpr.abstractFVarsSpec · pos n ·) sc →
      WalkPost S (KExpr.abstractFVarsSpec · pos n ·) depth body
        (abstractFVarsCached body pos n depth (it, sc)) := by
  induction hcon with
  | @var idx name md hidx =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkVar_shape] at hreach ⊢
    by_cases hfast :
        (!(KExpr.var idx name (KExpr.mkVar idx name md).info).hasFVars
          && decide ((KExpr.var idx name
            (KExpr.mkVar idx name md).info).lbr ≤ depth)) = true
    · exact absPost_fast (.var hidx) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.var idx name
          (KExpr.mkVar idx name md).info).addr, depth)]? with
      | some r =>
        exact absPost_hit hcf (hreach _ (KExpr.AbstractReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        by_cases hge : idx ≥ depth
        · -- Loose index: rebuild shifted up by `n`.
          have hrun : abstractFVarsCached
              (.var idx name (KExpr.mkVar idx name md).info) pos n depth
              (it, sc)
              = ((it.internExpr (KExpr.mkVar (idx + n) name)).1,
                 ((it.internExpr (KExpr.mkVar (idx + n) name)).2,
                  sc.insert ((KExpr.var idx name
                      (KExpr.mkVar idx name md).info).addr, depth)
                    (it.internExpr (KExpr.mkVar (idx + n) name)).1)) := by
            rw [abstractFVarsCached, if_neg hfast, run_pure_bind]
            try simp only []
            rw [run_scratchGet_bind, hget]
            try simp (config := { proj := false }) only []
            try rw [run_pure_bind]
            try simp only []
            rw [if_pos hge]
            rfl
          rw [hrun]
          have hcand : KExpr.mkVar (idx + n) name
              = KExpr.abstractFVarsSpec
                  (.var idx name (KExpr.mkVar idx name md).info)
                  pos n depth := by
            rw [KExpr.abstractFVarsSpec, if_pos hge]
          exact walkPost_jp hcf hwf hsup hsc
            (hreach _ (KExpr.AbstractReach.self ..))
            (hreach _ (.inr (.inl hcand)))
            hcand
        · -- Below `depth`: unreachable once the fast path declined
          -- (a `var` node has no fvars, so the guard was just `lbr`).
          exfalso
          have hfast' : ¬ (decide (idx + 1 ≤ depth) = true) := hfast
          have hnle : ¬ (idx + 1 ≤ depth) := fun h =>
            hfast' (decide_eq_true h)
          have hgei : depth.toNat ≤ idx.toNat := by
            have h1 : ¬ (idx.toNat + 1 ≤ depth.toNat) := fun h =>
              hnle (UInt64.le_iff_toNat_le.mpr (by
                rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt hidx]
                exact h))
            omega
          exact hge (UInt64.le_iff_toNat_le.mpr hgei)
  | @fvar id name md =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkFVar_shape] at hreach ⊢
    by_cases hfast :
        (!(KExpr.fvar id name (KExpr.mkFVar id name md).info).hasFVars
          && decide ((KExpr.fvar id name
            (KExpr.mkFVar id name md).info).lbr ≤ depth)) = true
    · exact absurd (hfast : (false : Bool) = true) Bool.false_ne_true
    · cases hget : sc[((KExpr.fvar id name
          (KExpr.mkFVar id name md).info).addr, depth)]? with
      | some r =>
        exact absPost_hit hcf (hreach _ (KExpr.AbstractReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        cases hpos : pos[id]? with
        | some p =>
          -- Listed fvar: intern the new bound variable, memoize it.
          have hrun : abstractFVarsCached
              (.fvar id name (KExpr.mkFVar id name md).info) pos n depth
              (it, sc)
              = ((it.internExpr (KExpr.mkVar (depth + p)
                    (anonName (m := .anon)))).1,
                 ((it.internExpr (KExpr.mkVar (depth + p)
                     (anonName (m := .anon)))).2,
                  sc.insert ((KExpr.fvar id name
                      (KExpr.mkFVar id name md).info).addr, depth)
                    (it.internExpr (KExpr.mkVar (depth + p)
                      (anonName (m := .anon)))).1)) := by
            rw [abstractFVarsCached, if_neg hfast, run_pure_bind]
            try simp only []
            rw [run_scratchGet_bind, hget]
            try simp (config := { proj := false }) only []
            try rw [run_pure_bind]
            try simp only []
            rw [hpos]
            try simp only []
            rfl
          rw [hrun]
          have hcand : KExpr.mkVar (depth + p) (anonName (m := .anon))
              = KExpr.abstractFVarsSpec
                  (.fvar id name (KExpr.mkFVar id name md).info)
                  pos n depth := by
            rw [KExpr.abstractFVarsSpec, hpos]
          exact walkPost_jp hcf hwf hsup hsc
            (hreach _ (KExpr.AbstractReach.self ..))
            (hreach _ (.inr (.inl hcand)))
            hcand
        | none =>
          -- Unlisted fvar: passes through, memoized as itself.
          have hrun : abstractFVarsCached
              (.fvar id name (KExpr.mkFVar id name md).info) pos n depth
              (it, sc)
              = (.fvar id name (KExpr.mkFVar id name md).info,
                 (it, sc.insert ((KExpr.fvar id name
                     (KExpr.mkFVar id name md).info).addr, depth)
                   (.fvar id name (KExpr.mkFVar id name md).info))) := by
            rw [abstractFVarsCached, if_neg hfast, run_pure_bind]
            try simp only []
            rw [run_scratchGet_bind, hget]
            try simp (config := { proj := false }) only []
            try rw [run_pure_bind]
            try simp only []
            rw [hpos]
            try simp only []
            rfl
          rw [hrun]
          exact walkPost_store_self
            (by rw [KExpr.abstractFVarsSpec, hpos])
            (hreach _ (KExpr.AbstractReach.self ..)) hwf hsup hsc
  | @sort u md =>
    intro depth it sc hcut hreach hwf hsup hsc
    exact absPost_fast .sort hcut
      (decide_eq_true (p := (KExpr.mkSort u md).lbr ≤ depth)
        UInt64.zero_le)
      hwf hsup hsc
  | @const id us md =>
    intro depth it sc hcut hreach hwf hsup hsc
    exact absPost_fast .const hcut
      (decide_eq_true (p := (KExpr.mkConst id us md).lbr ≤ depth)
        UInt64.zero_le)
      hwf hsup hsc
  | @app f a md hf ha ihf iha =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkApp_shape] at hreach ⊢
    have hcut' : depth.toNat + (f.size + a.size + 1) < UInt64.size := hcut
    by_cases hfast :
        (!(KExpr.app f a (KExpr.mkApp f a md).info).hasFVars
          && decide ((KExpr.app f a
            (KExpr.mkApp f a md).info).lbr ≤ depth)) = true
    · exact absPost_fast (.app hf ha) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.app f a
          (KExpr.mkApp f a md).info).addr, depth)]? with
      | some r =>
        exact absPost_hit hcf (hreach _ (KExpr.AbstractReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : abstractFVarsCached f pos n depth (it, sc)
          with ⟨rf, it1, sc1⟩
        have post1 := ihf (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : abstractFVarsCached a pos n depth (it1, sc1)
          with ⟨ra, it2, sc2⟩
        have post2 := iha (depth := depth) (it := it1) (sc := sc1)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rf = KExpr.abstractFVarsSpec f pos n depth :=
          post1.result
        have hres2 : ra = KExpr.abstractFVarsSpec a pos n depth :=
          post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.abstractFVarsSpec · pos n ·)
            sc2 := post2.scr
        have hrun : abstractFVarsCached
            (.app f a (KExpr.mkApp f a md).info) pos n depth (it, sc)
            = ((it2.internExpr (KExpr.mkApp rf ra)).1,
               ((it2.internExpr (KExpr.mkApp rf ra)).2,
                sc2.insert ((KExpr.app f a
                    (KExpr.mkApp f a md).info).addr, depth)
                  (it2.internExpr (KExpr.mkApp rf ra)).1)) := by
          rw [abstractFVarsCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkApp rf ra
            = KExpr.abstractFVarsSpec
                (.app f a (KExpr.mkApp f a md).info) pos n depth := by
          rw [KExpr.abstractFVarsSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.AbstractReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @lam nm bi ty body md hty hbody ihty ihbody =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkLam_shape] at hreach ⊢
    have hcut' : depth.toNat + (ty.size + body.size + 1) < UInt64.size :=
      hcut
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut')
    by_cases hfast :
        (!(KExpr.lam nm bi ty body
            (KExpr.mkLam nm bi ty body md).info).hasFVars
          && decide ((KExpr.lam nm bi ty body
            (KExpr.mkLam nm bi ty body md).info).lbr ≤ depth)) = true
    · exact absPost_fast (.lam hty hbody) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.lam nm bi ty body
          (KExpr.mkLam nm bi ty body md).info).addr, depth)]? with
      | some r =>
        exact absPost_hit hcf (hreach _ (KExpr.AbstractReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : abstractFVarsCached ty pos n depth (it, sc)
          with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : abstractFVarsCached body pos n (depth + 1)
          (it1, sc1) with ⟨rbody, it2, sc2⟩
        have post2 := ihbody (depth := depth + 1) (it := it1) (sc := sc1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rty = KExpr.abstractFVarsSpec ty pos n depth :=
          post1.result
        have hres2 : rbody = KExpr.abstractFVarsSpec body pos n
            (depth + 1) := post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.abstractFVarsSpec · pos n ·)
            sc2 := post2.scr
        have hrun : abstractFVarsCached
            (.lam nm bi ty body (KExpr.mkLam nm bi ty body md).info)
            pos n depth (it, sc)
            = ((it2.internExpr (KExpr.mkLam nm bi rty rbody)).1,
               ((it2.internExpr (KExpr.mkLam nm bi rty rbody)).2,
                sc2.insert ((KExpr.lam nm bi ty body
                    (KExpr.mkLam nm bi ty body md).info).addr, depth)
                  (it2.internExpr (KExpr.mkLam nm bi rty rbody)).1)) := by
          rw [abstractFVarsCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkLam nm bi rty rbody
            = KExpr.abstractFVarsSpec
                (.lam nm bi ty body (KExpr.mkLam nm bi ty body md).info)
                pos n depth := by
          rw [KExpr.abstractFVarsSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.AbstractReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @all nm bi ty body md hty hbody ihty ihbody =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkAll_shape] at hreach ⊢
    have hcut' : depth.toNat + (ty.size + body.size + 1) < UInt64.size :=
      hcut
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut')
    by_cases hfast :
        (!(KExpr.all nm bi ty body
            (KExpr.mkAll nm bi ty body md).info).hasFVars
          && decide ((KExpr.all nm bi ty body
            (KExpr.mkAll nm bi ty body md).info).lbr ≤ depth)) = true
    · exact absPost_fast (.all hty hbody) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.all nm bi ty body
          (KExpr.mkAll nm bi ty body md).info).addr, depth)]? with
      | some r =>
        exact absPost_hit hcf (hreach _ (KExpr.AbstractReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : abstractFVarsCached ty pos n depth (it, sc)
          with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : abstractFVarsCached body pos n (depth + 1)
          (it1, sc1) with ⟨rbody, it2, sc2⟩
        have post2 := ihbody (depth := depth + 1) (it := it1) (sc := sc1)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr hx))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        have hres1 : rty = KExpr.abstractFVarsSpec ty pos n depth :=
          post1.result
        have hres2 : rbody = KExpr.abstractFVarsSpec body pos n
            (depth + 1) := post2.result
        have hwf2 : it2.WF := post2.wf
        have hsup2 : ∀ x, it2.ExprSupport x → S x := post2.sup
        have hsc2 : WalkScratchInv S (KExpr.abstractFVarsSpec · pos n ·)
            sc2 := post2.scr
        have hrun : abstractFVarsCached
            (.all nm bi ty body (KExpr.mkAll nm bi ty body md).info)
            pos n depth (it, sc)
            = ((it2.internExpr (KExpr.mkAll nm bi rty rbody)).1,
               ((it2.internExpr (KExpr.mkAll nm bi rty rbody)).2,
                sc2.insert ((KExpr.all nm bi ty body
                    (KExpr.mkAll nm bi ty body md).info).addr, depth)
                  (it2.internExpr (KExpr.mkAll nm bi rty rbody)).1)) := by
          rw [abstractFVarsCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkAll nm bi rty rbody
            = KExpr.abstractFVarsSpec
                (.all nm bi ty body (KExpr.mkAll nm bi ty body md).info)
                pos n depth := by
          rw [KExpr.abstractFVarsSpec, hres1, hres2]
        exact walkPost_jp hcf hwf2 hsup2 hsc2
          (hreach _ (KExpr.AbstractReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @letE nm ty val body nd md hty hval hbody ihty ihval ihbody =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkLet_shape] at hreach ⊢
    have hcut' :
        depth.toNat + (ty.size + val.size + body.size + 1) < UInt64.size :=
      hcut
    have hc1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hcut')
    by_cases hfast :
        (!(KExpr.letE nm ty val body nd
            (KExpr.mkLet nm ty val body nd md).info).hasFVars
          && decide ((KExpr.letE nm ty val body nd
            (KExpr.mkLet nm ty val body nd md).info).lbr ≤ depth)) = true
    · exact absPost_fast (.letE hty hval hbody) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.letE nm ty val body nd
          (KExpr.mkLet nm ty val body nd md).info).addr, depth)]? with
      | some r =>
        exact absPost_hit hcf (hreach _ (KExpr.AbstractReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : abstractFVarsCached ty pos n depth (it, sc)
          with ⟨rty, it1, sc1⟩
        have post1 := ihty (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inl hx))))
          hwf hsup hsc
        rw [hrun1] at post1
        rcases hrun2 : abstractFVarsCached val pos n depth (it1, sc1)
          with ⟨rval, it2, sc2⟩
        have post2 := ihval (depth := depth) (it := it1) (sc := sc1)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr (.inl hx)))))
          post1.wf post1.sup post1.scr
        rw [hrun2] at post2
        rcases hrun3 : abstractFVarsCached body pos n (depth + 1)
          (it2, sc2) with ⟨rbody, it3, sc3⟩
        have post3 := ihbody (depth := depth + 1) (it := it2) (sc := sc2)
          (by rw [hc1]; exact Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr (.inr (.inr hx)))))
          post2.wf post2.sup post2.scr
        rw [hrun3] at post3
        have hres1 : rty = KExpr.abstractFVarsSpec ty pos n depth :=
          post1.result
        have hres2 : rval = KExpr.abstractFVarsSpec val pos n depth :=
          post2.result
        have hres3 : rbody = KExpr.abstractFVarsSpec body pos n
            (depth + 1) := post3.result
        have hwf3 : it3.WF := post3.wf
        have hsup3 : ∀ x, it3.ExprSupport x → S x := post3.sup
        have hsc3 : WalkScratchInv S (KExpr.abstractFVarsSpec · pos n ·)
            sc3 := post3.scr
        have hrun : abstractFVarsCached
            (.letE nm ty val body nd
              (KExpr.mkLet nm ty val body nd md).info) pos n depth
            (it, sc)
            = ((it3.internExpr (KExpr.mkLet nm rty rval rbody nd)).1,
               ((it3.internExpr (KExpr.mkLet nm rty rval rbody nd)).2,
                sc3.insert ((KExpr.letE nm ty val body nd
                    (KExpr.mkLet nm ty val body nd md).info).addr, depth)
                  (it3.internExpr
                    (KExpr.mkLet nm rty rval rbody nd)).1)) := by
          rw [abstractFVarsCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          try rw [run_bind]
          rw [hrun2]
          try simp only []
          try rw [run_bind]
          rw [hrun3]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkLet nm rty rval rbody nd
            = KExpr.abstractFVarsSpec
                (.letE nm ty val body nd
                  (KExpr.mkLet nm ty val body nd md).info)
                pos n depth := by
          rw [KExpr.abstractFVarsSpec, hres1, hres2, hres3]
        exact walkPost_jp hcf hwf3 hsup3 hsc3
          (hreach _ (KExpr.AbstractReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @prj id field val md hval ihval =>
    intro depth it sc hcut hreach hwf hsup hsc
    rw [KExpr.mkPrj_shape] at hreach ⊢
    have hcut' : depth.toNat + (val.size + 1) < UInt64.size := hcut
    by_cases hfast :
        (!(KExpr.prj id field val
            (KExpr.mkPrj id field val md).info).hasFVars
          && decide ((KExpr.prj id field val
            (KExpr.mkPrj id field val md).info).lbr ≤ depth)) = true
    · exact absPost_fast (.prj hval) hcut hfast hwf hsup hsc
    · cases hget : sc[((KExpr.prj id field val
          (KExpr.mkPrj id field val md).info).addr, depth)]? with
      | some r =>
        exact absPost_hit hcf (hreach _ (KExpr.AbstractReach.self ..))
          hfast hget hwf hsup hsc
      | none =>
        rcases hrun1 : abstractFVarsCached val pos n depth (it, sc)
          with ⟨rval, it1, sc1⟩
        have post1 := ihval (depth := depth) (it := it) (sc := sc)
          (Nat.lt_of_le_of_lt (by omega) hcut')
          (fun x hx => hreach x (.inr (.inr hx)))
          hwf hsup hsc
        rw [hrun1] at post1
        have hres1 : rval = KExpr.abstractFVarsSpec val pos n depth :=
          post1.result
        have hwf1 : it1.WF := post1.wf
        have hsup1 : ∀ x, it1.ExprSupport x → S x := post1.sup
        have hsc1 : WalkScratchInv S (KExpr.abstractFVarsSpec · pos n ·)
            sc1 := post1.scr
        have hrun : abstractFVarsCached
            (.prj id field val (KExpr.mkPrj id field val md).info)
            pos n depth (it, sc)
            = ((it1.internExpr (KExpr.mkPrj id field rval)).1,
               ((it1.internExpr (KExpr.mkPrj id field rval)).2,
                sc1.insert ((KExpr.prj id field val
                    (KExpr.mkPrj id field val md).info).addr, depth)
                  (it1.internExpr (KExpr.mkPrj id field rval)).1)) := by
          rw [abstractFVarsCached, if_neg hfast, run_pure_bind]
          try simp only []
          rw [run_scratchGet_bind, hget]
          try simp (config := { proj := false }) only []
          try rw [run_pure_bind]
          try simp only []
          rw [run_bind, hrun1]
          try simp only []
          rfl
        rw [hrun]
        have hcand : KExpr.mkPrj id field rval
            = KExpr.abstractFVarsSpec
                (.prj id field val (KExpr.mkPrj id field val md).info)
                pos n depth := by
          rw [KExpr.abstractFVarsSpec, hres1]
        exact walkPost_jp hcf hwf1 hsup1 hsc1
          (hreach _ (KExpr.AbstractReach.self ..))
          (hreach _ (.inr (.inl hcand)))
          hcand
  | @nat v blob md =>
    intro depth it sc hcut hreach hwf hsup hsc
    exact absPost_fast .nat hcut
      (decide_eq_true (p := (KExpr.mkNat v blob md).lbr ≤ depth)
        UInt64.zero_le)
      hwf hsup hsc
  | @str v blob md =>
    intro depth it sc hcut hreach hwf hsup hsc
    exact absPost_fast .str hcut
      (decide_eq_true (p := (KExpr.mkStr v blob md).lbr ≤ depth)
        UInt64.zero_le)
      hwf hsup hsc

/-! ### `Constructed`-closure of the pure specs

Walker outputs feed later walker calls (the whnf/infer soundness
layers chain `subst` after `lift`
after `instantiateRev` …) whose masters require `Constructed` inputs.
Each spec preserves `Constructed` under a no-wrap budget for the indices
it can create: an up-shifted `var` index is bounded through the input's
`lbr`, and the `lbr + size + shift` budget is preserved under binder
descent (`lbr` grows by at most one per binder via `sat1` while `size`
shrinks by at least two). Down-shifts (`i - 1`, `i - n`) need no budget —
they only lower the index. No cutoff/depth well-formedness is assumed
beyond the budget: guards merely select arms, and every arm's output is
`Constructed` under the budget (a semantically wrong arm selection is
the masters' concern, not closure's). -/

namespace KExpr

theorem Constructed.liftSpec {e : KExpr .anon} (hcon : Constructed e) :
    ∀ {shift cutoff : UInt64},
      e.lbr.toNat + e.size + shift.toNat < UInt64.size →
      Constructed (liftSpec e shift cutoff) := by
  induction hcon with
  | @var idx name md hidx =>
    intro shift cutoff hb
    rw [mkVar_lbr] at hb
    have hb1 : (idx + 1).toNat = idx.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt hidx
    have hsz := size_pos (mkVar idx name md)
    rw [mkVar_shape, KExpr.liftSpec]
    split
    · refine .var ?_
      have hns : (idx + shift).toNat = idx.toNat + shift.toNat := by
        rw [UInt64.toNat_add]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hb)
      omega
    · rw [← mkVar_shape]
      exact .var hidx
  | fvar => intro _ _ _; exact .fvar
  | sort => intro _ _ _; exact .sort
  | const => intro _ _ _; exact .const
  | @app f a md hf ha ihf iha =>
    intro shift cutoff hb
    rw [mkApp_lbr] at hb
    rw [mkApp_shape, size] at hb
    rw [toNat_max] at hb
    have hszf := size_pos f
    have hsza := size_pos a
    rw [mkApp_shape, KExpr.liftSpec]
    exact .app (ihf (by omega)) (iha (by omega))
  | @lam n bi ty body md hty hbody ihty ihbody =>
    intro shift cutoff hb
    rw [mkLam_lbr] at hb
    rw [mkLam_shape, size] at hb
    rw [toNat_max] at hb
    have hsat := toNat_le_sat1_add_one body.lbr
    have hszty := size_pos ty
    have hszbody := size_pos body
    rw [mkLam_shape, KExpr.liftSpec]
    exact .lam (ihty (by omega)) (ihbody (by omega))
  | @all n bi ty body md hty hbody ihty ihbody =>
    intro shift cutoff hb
    rw [mkAll_lbr] at hb
    rw [mkAll_shape, size] at hb
    rw [toNat_max] at hb
    have hsat := toNat_le_sat1_add_one body.lbr
    have hszty := size_pos ty
    have hszbody := size_pos body
    rw [mkAll_shape, KExpr.liftSpec]
    exact .all (ihty (by omega)) (ihbody (by omega))
  | @letE n ty val body nd md hty hval hbody ihty ihval ihbody =>
    intro shift cutoff hb
    rw [mkLet_lbr] at hb
    rw [mkLet_shape, size] at hb
    rw [toNat_max, toNat_max] at hb
    have hsat := toNat_le_sat1_add_one body.lbr
    have hszty := size_pos ty
    have hszval := size_pos val
    have hszbody := size_pos body
    rw [mkLet_shape, KExpr.liftSpec]
    exact .letE (ihty (by omega)) (ihval (by omega)) (ihbody (by omega))
  | @prj id field val md hval ihval =>
    intro shift cutoff hb
    rw [mkPrj_lbr] at hb
    rw [mkPrj_shape, size] at hb
    have hszval := size_pos val
    rw [mkPrj_shape, KExpr.liftSpec]
    exact .prj (ihval (by omega))
  | nat => intro _ _ _; exact .nat
  | str => intro _ _ _; exact .str

theorem Constructed.substSpec {body arg : KExpr .anon}
    (hbody : Constructed body) (harg : Constructed arg) :
    ∀ {depth : UInt64},
      arg.lbr.toNat + arg.size + depth.toNat + body.size < UInt64.size →
      Constructed (substSpec body arg depth) := by
  induction hbody with
  | @var idx name md hidx =>
    intro depth hb
    have hsz := size_pos (mkVar idx name md)
    rw [mkVar_shape, KExpr.substSpec]
    split
    · exact harg.liftSpec (by omega)
    · split
      · next hgt =>
        refine .var ?_
        have hgt' := UInt64.lt_iff_toNat_lt.mp hgt
        have hsub : (idx - 1).toNat = idx.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le idx 1 (UInt64.le_iff_toNat_le.mpr (by
            rw [show (1 : UInt64).toNat = 1 from rfl]; omega))]
          rfl
        omega
      · rw [← mkVar_shape]
        exact .var hidx
  | fvar => intro _ _; exact .fvar
  | sort => intro _ _; exact .sort
  | const => intro _ _; exact .const
  | @app f a md hf ha ihf iha =>
    intro depth hb
    rw [mkApp_shape, size] at hb
    have hszf := size_pos f
    have hsza := size_pos a
    rw [mkApp_shape, KExpr.substSpec]
    exact .app (ihf (by omega)) (iha (by omega))
  | @lam n bi ty inner md hty hinner ihty ihinner =>
    intro depth hb
    rw [mkLam_shape, size] at hb
    have hszty := size_pos ty
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hb)
    rw [mkLam_shape, KExpr.substSpec]
    exact .lam (ihty (by omega)) (ihinner (by rw [hd1]; omega))
  | @all n bi ty inner md hty hinner ihty ihinner =>
    intro depth hb
    rw [mkAll_shape, size] at hb
    have hszty := size_pos ty
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hb)
    rw [mkAll_shape, KExpr.substSpec]
    exact .all (ihty (by omega)) (ihinner (by rw [hd1]; omega))
  | @letE n ty val inner nd md hty hval hinner ihty ihval ihinner =>
    intro depth hb
    rw [mkLet_shape, size] at hb
    have hszty := size_pos ty
    have hszval := size_pos val
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hb)
    rw [mkLet_shape, KExpr.substSpec]
    exact .letE (ihty (by omega)) (ihval (by omega))
      (ihinner (by rw [hd1]; omega))
  | @prj id field val md hval ihval =>
    intro depth hb
    rw [mkPrj_shape, size] at hb
    have hszval := size_pos val
    rw [mkPrj_shape, KExpr.substSpec]
    exact .prj (ihval (by omega))
  | nat => intro _ _; exact .nat
  | str => intro _ _; exact .str

theorem Constructed.simulSubstSpec {body : KExpr .anon}
    (hbody : Constructed body) {substs : Array (KExpr .anon)}
    (hsub : ∀ k, k < substs.size → Constructed substs[k]!) :
    ∀ {depth : UInt64},
      depth.toNat + body.size + substs.size < UInt64.size →
      (∀ k, k < substs.size →
        substs[k]!.lbr.toNat + substs[k]!.size + depth.toNat + body.size
          < UInt64.size) →
      Constructed (simulSubstSpec body substs depth) := by
  induction hbody with
  | @var idx name md hidx =>
    intro depth hw hbnd
    have hsz := size_pos (mkVar idx name md)
    have hszn : substs.size.toUInt64.toNat = substs.size := by
      rw [toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hw)
    have hdw : (depth + substs.size.toUInt64).toNat
        = depth.toNat + substs.size := by
      rw [UInt64.toNat_add, hszn]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hw)
    rw [mkVar_shape, KExpr.simulSubstSpec]
    split
    · next hguard =>
      obtain ⟨hge, hlt⟩ := Bool.and_eq_true_iff.mp hguard
      have hge' : depth.toNat ≤ idx.toNat :=
        UInt64.le_iff_toNat_le.mp (of_decide_eq_true hge)
      have hlt' : idx.toNat < depth.toNat + substs.size := by
        have h := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true hlt)
        rwa [hdw] at h
      have hsubt : (idx - depth).toNat = idx.toNat - depth.toNat :=
        UInt64.toNat_sub_of_le idx depth (UInt64.le_iff_toNat_le.mpr hge')
      have hk : (idx - depth).toNat < substs.size := by omega
      exact (hsub _ hk).liftSpec (by have := hbnd _ hk; omega)
    · split
      · next hge2 =>
        refine .var ?_
        have hge2' : substs.size ≤ idx.toNat := by
          have h := UInt64.le_iff_toNat_le.mp hge2
          rw [hdw] at h
          omega
        have hsub2 : (idx - substs.size.toUInt64).toNat
            = idx.toNat - substs.size := by
          rw [UInt64.toNat_sub_of_le idx substs.size.toUInt64
            (UInt64.le_iff_toNat_le.mpr (by rw [hszn]; omega)), hszn]
        omega
      · rw [← mkVar_shape]
        exact .var hidx
  | fvar => intro _ _ _; exact .fvar
  | sort => intro _ _ _; exact .sort
  | const => intro _ _ _; exact .const
  | @app f a md hf ha ihf iha =>
    intro depth hw hbnd
    rw [mkApp_shape, size] at hw
    have hszf := size_pos f
    have hsza := size_pos a
    rw [mkApp_shape, KExpr.simulSubstSpec]
    exact .app
      (ihf (by omega) (fun k hk => by
        have h := hbnd k hk; rw [mkApp_shape, size] at h; omega))
      (iha (by omega) (fun k hk => by
        have h := hbnd k hk; rw [mkApp_shape, size] at h; omega))
  | @lam n bi ty inner md hty hinner ihty ihinner =>
    intro depth hw hbnd
    rw [mkLam_shape, size] at hw
    have hszty := size_pos ty
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hw)
    rw [mkLam_shape, KExpr.simulSubstSpec]
    exact .lam
      (ihty (by omega) (fun k hk => by
        have h := hbnd k hk; rw [mkLam_shape, size] at h; omega))
      (ihinner (by rw [hd1]; omega)
        (fun k hk => by
          have h := hbnd k hk; rw [mkLam_shape, size] at h
          rw [hd1]; omega))
  | @all n bi ty inner md hty hinner ihty ihinner =>
    intro depth hw hbnd
    rw [mkAll_shape, size] at hw
    have hszty := size_pos ty
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hw)
    rw [mkAll_shape, KExpr.simulSubstSpec]
    exact .all
      (ihty (by omega) (fun k hk => by
        have h := hbnd k hk; rw [mkAll_shape, size] at h; omega))
      (ihinner (by rw [hd1]; omega)
        (fun k hk => by
          have h := hbnd k hk; rw [mkAll_shape, size] at h
          rw [hd1]; omega))
  | @letE n ty val inner nd md hty hval hinner ihty ihval ihinner =>
    intro depth hw hbnd
    rw [mkLet_shape, size] at hw
    have hszty := size_pos ty
    have hszval := size_pos val
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hw)
    rw [mkLet_shape, KExpr.simulSubstSpec]
    exact .letE
      (ihty (by omega) (fun k hk => by
        have h := hbnd k hk; rw [mkLet_shape, size] at h; omega))
      (ihval (by omega) (fun k hk => by
        have h := hbnd k hk; rw [mkLet_shape, size] at h; omega))
      (ihinner (by rw [hd1]; omega)
        (fun k hk => by
          have h := hbnd k hk; rw [mkLet_shape, size] at h
          rw [hd1]; omega))
  | @prj id field val md hval ihval =>
    intro depth hw hbnd
    rw [mkPrj_shape, size] at hw
    have hszval := size_pos val
    rw [mkPrj_shape, KExpr.simulSubstSpec]
    exact .prj
      (ihval (by omega) (fun k hk => by
        have h := hbnd k hk; rw [mkPrj_shape, size] at h; omega))
  | nat => intro _ _ _; exact .nat
  | str => intro _ _ _; exact .str

theorem Constructed.instantiateRevSpec {body : KExpr .anon}
    (hbody : Constructed body) {fvars : Array (KExpr .anon)}
    (hfv : ∀ k, k < fvars.size → Constructed fvars[k]!) :
    ∀ {depth : UInt64},
      depth.toNat + body.size + fvars.size < UInt64.size →
      Constructed (instantiateRevSpec body fvars depth) := by
  induction hbody with
  | @var idx name md hidx =>
    intro depth hw
    have hsz := size_pos (mkVar idx name md)
    have hszn : fvars.size.toUInt64.toNat = fvars.size := by
      rw [toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hw)
    have hdw : (depth + fvars.size.toUInt64).toNat
        = depth.toNat + fvars.size := by
      rw [UInt64.toNat_add, hszn]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hw)
    rw [mkVar_shape, KExpr.instantiateRevSpec]
    split
    · next hguard =>
      obtain ⟨hge, hlt⟩ := Bool.and_eq_true_iff.mp hguard
      have hge' : depth.toNat ≤ idx.toNat :=
        UInt64.le_iff_toNat_le.mp (of_decide_eq_true hge)
      have hlt' : idx.toNat < depth.toNat + fvars.size := by
        have h := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true hlt)
        rwa [hdw] at h
      have hsubt : (idx - depth).toNat = idx.toNat - depth.toNat :=
        UInt64.toNat_sub_of_le idx depth (UInt64.le_iff_toNat_le.mpr hge')
      have h1s : (1 : UInt64) ≤ fvars.size.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, hszn,
          show (1 : UInt64).toNat = 1 from rfl]
        omega
      have hs1 : (fvars.size.toUInt64 - 1).toNat = fvars.size - 1 := by
        rw [UInt64.toNat_sub_of_le fvars.size.toUInt64 1 h1s, hszn]
        rfl
      have hle2 : idx - depth ≤ fvars.size.toUInt64 - 1 := by
        rw [UInt64.le_iff_toNat_le, hsubt, hs1]
        omega
      have hfin : (fvars.size.toUInt64 - 1 - (idx - depth)).toNat
          = fvars.size - 1 - (idx.toNat - depth.toNat) := by
        rw [UInt64.toNat_sub_of_le (fvars.size.toUInt64 - 1) (idx - depth)
          hle2, hs1, hsubt]
      have hk : (fvars.size.toUInt64 - 1 - (idx - depth)).toNat
          < fvars.size := by omega
      exact hfv _ hk
    · split
      · next hge2 =>
        refine .var ?_
        have hsub2 : (idx - fvars.size.toUInt64).toNat
            = idx.toNat - fvars.size := by
          have h := UInt64.le_iff_toNat_le.mp hge2
          rw [hdw] at h
          rw [UInt64.toNat_sub_of_le idx fvars.size.toUInt64
            (UInt64.le_iff_toNat_le.mpr (by rw [hszn]; omega)), hszn]
        omega
      · rw [← mkVar_shape]
        exact .var hidx
  | fvar => intro _ _; exact .fvar
  | sort => intro _ _; exact .sort
  | const => intro _ _; exact .const
  | @app f a md hf ha ihf iha =>
    intro depth hw
    rw [mkApp_shape, size] at hw
    have hszf := size_pos f
    have hsza := size_pos a
    rw [mkApp_shape, KExpr.instantiateRevSpec]
    exact .app (ihf (by omega)) (iha (by omega))
  | @lam n bi ty inner md hty hinner ihty ihinner =>
    intro depth hw
    rw [mkLam_shape, size] at hw
    have hszty := size_pos ty
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hw)
    rw [mkLam_shape, KExpr.instantiateRevSpec]
    exact .lam (ihty (by omega)) (ihinner (by rw [hd1]; omega))
  | @all n bi ty inner md hty hinner ihty ihinner =>
    intro depth hw
    rw [mkAll_shape, size] at hw
    have hszty := size_pos ty
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hw)
    rw [mkAll_shape, KExpr.instantiateRevSpec]
    exact .all (ihty (by omega)) (ihinner (by rw [hd1]; omega))
  | @letE n ty val inner nd md hty hval hinner ihty ihval ihinner =>
    intro depth hw
    rw [mkLet_shape, size] at hw
    have hszty := size_pos ty
    have hszval := size_pos val
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hw)
    rw [mkLet_shape, KExpr.instantiateRevSpec]
    exact .letE (ihty (by omega)) (ihval (by omega))
      (ihinner (by rw [hd1]; omega))
  | @prj id field val md hval ihval =>
    intro depth hw
    rw [mkPrj_shape, size] at hw
    have hszval := size_pos val
    rw [mkPrj_shape, KExpr.instantiateRevSpec]
    exact .prj (ihval (by omega))
  | nat => intro _ _; exact .nat
  | str => intro _ _; exact .str

theorem Constructed.abstractFVarsSpec {body : KExpr .anon}
    (hbody : Constructed body) {pos : Std.HashMap FVarId UInt64}
    {n : UInt64}
    (hpos : ∀ (id : FVarId) (p : UInt64),
      pos[id]? = some p → p.toNat < n.toNat) :
    ∀ {depth : UInt64},
      body.lbr.toNat + body.size + depth.toNat + n.toNat < UInt64.size →
      Constructed (abstractFVarsSpec body pos n depth) := by
  induction hbody with
  | @fvar id name md =>
    intro depth hb
    have hsz := size_pos (mkFVar id name md)
    rw [mkFVar_shape, KExpr.abstractFVarsSpec]
    cases hp : pos[id]? with
    | some p =>
      refine .var ?_
      have hpn := hpos _ _ hp
      have hdp : (depth + p).toNat = depth.toNat + p.toNat := by
        rw [UInt64.toNat_add]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hb)
      omega
    | none =>
      rw [← mkFVar_shape]
      exact .fvar
  | @var idx name md hidx =>
    intro depth hb
    rw [mkVar_lbr] at hb
    have hb1 : (idx + 1).toNat = idx.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt hidx
    have hsz := size_pos (mkVar idx name md)
    rw [mkVar_shape, KExpr.abstractFVarsSpec]
    split
    · refine .var ?_
      have hin : (idx + n).toNat = idx.toNat + n.toNat := by
        rw [UInt64.toNat_add]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hb)
      omega
    · rw [← mkVar_shape]
      exact .var hidx
  | sort => intro _ _; exact .sort
  | const => intro _ _; exact .const
  | @app f a md hf ha ihf iha =>
    intro depth hb
    rw [mkApp_lbr] at hb
    rw [mkApp_shape, size] at hb
    rw [toNat_max] at hb
    have hszf := size_pos f
    have hsza := size_pos a
    rw [mkApp_shape, KExpr.abstractFVarsSpec]
    exact .app (ihf (by omega)) (iha (by omega))
  | @lam nm bi ty inner md hty hinner ihty ihinner =>
    intro depth hb
    rw [mkLam_lbr] at hb
    rw [mkLam_shape, size] at hb
    rw [toNat_max] at hb
    have hsat := toNat_le_sat1_add_one inner.lbr
    have hszty := size_pos ty
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hb)
    rw [mkLam_shape, KExpr.abstractFVarsSpec]
    exact .lam (ihty (by omega)) (ihinner (by rw [hd1]; omega))
  | @all nm bi ty inner md hty hinner ihty ihinner =>
    intro depth hb
    rw [mkAll_lbr] at hb
    rw [mkAll_shape, size] at hb
    rw [toNat_max] at hb
    have hsat := toNat_le_sat1_add_one inner.lbr
    have hszty := size_pos ty
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hb)
    rw [mkAll_shape, KExpr.abstractFVarsSpec]
    exact .all (ihty (by omega)) (ihinner (by rw [hd1]; omega))
  | @letE nm ty val inner nd md hty hval hinner ihty ihval ihinner =>
    intro depth hb
    rw [mkLet_lbr] at hb
    rw [mkLet_shape, size] at hb
    rw [toNat_max, toNat_max] at hb
    have hsat := toNat_le_sat1_add_one inner.lbr
    have hszty := size_pos ty
    have hszval := size_pos val
    have hszin := size_pos inner
    have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hb)
    rw [mkLet_shape, KExpr.abstractFVarsSpec]
    exact .letE (ihty (by omega)) (ihval (by omega))
      (ihinner (by rw [hd1]; omega))
  | @prj id field val md hval ihval =>
    intro depth hb
    rw [mkPrj_lbr] at hb
    rw [mkPrj_shape, size] at hb
    have hszval := size_pos val
    rw [mkPrj_shape, KExpr.abstractFVarsSpec]
    exact .prj (ihval (by omega))
  | nat => intro _ _; exact .nat
  | str => intro _ _; exact .str

end KExpr

end Ix.Tc
