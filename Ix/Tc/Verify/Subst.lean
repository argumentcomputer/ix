import Ix.Tc.Subst
import Ix.Tc.Verify.Expr

/-!
# Subst slice: `lift`/`subst` walkers against pure specs

M2 of plans/tc-verify-roadmap.md, second layer: WalkM memo-soundness —
the `(addr, depth)`-keyed cache pattern proven in its simplest (pure
StateM) home before it recurs in every kernel cache (risk R1's
validation site).

Scope decision (recorded): the walker theorems are stated for
**`m = .anon`** — the v1 checking kernel's mode, where `internKey =
addr` (one collision-freedom domain serves the memo and the intern
table) and `eraseMeta` is the identity, so soundness is EXACT equality
with the spec, not equality up to erasure. Meta-mode intern transparency
is a separate `metaAddr`-collision obligation with no bearing on what
the checker accepts; it stays out of scope until a consumer needs it.

The composability answer to R1: each theorem's collision-freedom
hypothesis quantifies over an abstract support `S` that the caller can
instantiate with the FINITE, spec-determined set
`LiftReach ∪ (initial intern support)` — the walk only ever compares,
stores, or interns members of that set, and intern-table growth stays
inside it. No constructor-closure (which would force an infinite,
pigeonhole-false support) is ever required.

Side conditions: `Constructed` (expressions built by the smart
constructors, with the `var`-index no-wrap bound folded into the `var`
rule) and M1-style UInt64 no-wrap bounds (`cutoff.toNat + e.size <
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
    binder-descent `cutoff + 1`s (M1-style no-wrap threading); the
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
    rw [mkVar_shape, liftSpec]
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
collision-freedom hypothesis composable (R1): no closure under
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

/-- **WalkM memo-soundness for `lift`** — the R1 validation. Under
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

end Ix.Tc
