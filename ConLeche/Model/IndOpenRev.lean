module

public import ConLeche.Model.IndTransport
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Verify.Denote.OpenRevDenote
import ConLeche.Model.Annot.BitInst
public section

/-!
# The nested pin bridge, at the reading (task #161, IND TIER part 7)

`Verify/Denote/OpenRevDenote.lean`'s two denote laws and
`Install/IndNestedS.lean`'s `pinCrossS`, transposed to `denoteMeta`.

This is the **object bridge** the part-6 probe's diagnosis called for.
The checker's certificate is about `pinsP` — the stored pin
*instantiated at the public recursor frame's openers*, at the frame
depth — and `RecRuleLaw`'s repaired conjunct is about
`instRevChain zs vpa`, with `vpa` the pin's reading through
`openRev 0 rP`.  Those are two different `AnnotTerm`s, related by an
order-reversing renaming of the frame's variables, and nothing but the
`openRev` pair identifies them:

* `Rules.denoteMeta_openRev_base` and `Rules.denoteMeta_openRev` —
  **already in the tree**, landed with the ι row and living since the
  task #305 closing in `Model/Rules/IotaSoundKit.lean`.  The
  part-6 seal's "the consumer's bridge is the `denoteMeta` mirror of the
  `denote_openRev` pair" was already paid for; this file spends it;
* `instSeqAV_instRevChain`, `instSeqAV_eq_self_of_bvarsBelow`, `padHit`
  and `nestedChain` — the reverse chain rides the fired spine.  v1
  pads the spine with `dummyPropT`; the reading tier pads with `.prf`,
  generic in the padding element, because the reading tier's
  padding has TWO obligations where v1's `dummyPropT` had one: it must
  inhabit its `.sort 0` context slot **and** be graded, since the
  producer's `wellDenotedV_instSeq` charges every spine element a grading.
  The producer's choice is `.eqE (.sort 0) (.sort 0)` —
  `eqv_mem_univ` and a `True` grading.  (`.prf` fails the first:
  `pt_not_mem_univZero`.)
* `pinCross` — the composite, `pinCrossS` at the reading.

The boundedness currency is the one systematic delta: v1 states
`Term.bvarsBelow` of the value, the reading tier states it of the
value's **erasure** (`AnnotTerm.liftN_eq_self` / `AnnotTerm.inst_eq_self`
are keyed there), and `denoteMeta_erase` + `denote_bvarsBelow` produce
it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

universe w

variable {acval : Name → (Name → Nat) → AnnotTerm} {cval : TConstVal}
variable {env : Env} {φ : Name → Nat}

/-! ## `instSeq` corollaries at bounded readings -/

open ConLeche.Semantics.AnnotTerm in
/-- A reading with only low bound variables passes an `instSeq`
untouched (`Term.instSeq_eq_self_of_bvarsBelow`), at the erasure's
boundedness. -/
theorem instSeqAV_eq_self_of_bvarsBelow :
    ∀ (vs : List AnnotTerm) (t : Nat) {X : AnnotTerm} {m : Nat},
      Term.bvarsBelow m X.erase → m + vs.length ≤ t + 1 →
      ConLeche.Model.AnnotTerm.instSeq vs t X = X
  | [], _, _, _, _, _ => rfl
  | a :: vs, t, X, m, hb, h => by
    show ConLeche.Model.AnnotTerm.instSeq vs (t - 1) (X.inst a t) = _
    rw [AnnotTerm.inst_eq_self X
      (Term.bvarsBelow.mono (by simp only [List.length_cons] at h; omega)
        hb) a]
    cases t with
    | zero =>
      obtain rfl : vs = [] := by
        simp only [List.length_cons] at h
        exact List.eq_nil_of_length_eq_zero (by omega)
      rfl
    | succ t' =>
      exact instSeqAV_eq_self_of_bvarsBelow vs t' hb (by
        simp only [List.length_cons] at h; omega)

open ConLeche.Semantics.AnnotTerm in
/-- **`instSeq` through a reverse-instantiation chain**
(`Term.instSeq_instRevChain`), with no side conditions. -/
theorem instSeqAV_instRevChain :
    ∀ (bs : List AnnotTerm) (X : AnnotTerm) (vs : List AnnotTerm) (t : Nat),
      vs.length ≤ t + 1 →
      ConLeche.Model.AnnotTerm.instSeq vs t
          (ConLeche.Model.AnnotTerm.instRevChain bs X)
        = ConLeche.Model.AnnotTerm.instRevChain
            (bs.map (ConLeche.Model.AnnotTerm.instSeq vs t))
            (ConLeche.Model.AnnotTerm.instSeq vs (t + bs.length) X)
  | [], X, vs, t, _ => rfl
  | b :: bs, X, vs, t, h => by
    show ConLeche.Model.AnnotTerm.instSeq vs t
        (ConLeche.Model.AnnotTerm.instRevChain bs
          (X.inst (liftN bs.length b 0) 0)) = _
    rw [instSeqAV_instRevChain bs _ vs t h,
      instSeqAV_inst0 vs (t + bs.length) X _ (by omega),
      instSeqAV_liftN0 vs t bs.length b h]
    show ConLeche.Model.AnnotTerm.instRevChain (List.map _ bs) _ = _
    rw [show (b :: bs).map (ConLeche.Model.AnnotTerm.instSeq vs t)
        = ConLeche.Model.AnnotTerm.instSeq vs t b
            :: bs.map (ConLeche.Model.AnnotTerm.instSeq vs t) from rfl]
    show _ = ConLeche.Model.AnnotTerm.instRevChain
      (bs.map (ConLeche.Model.AnnotTerm.instSeq vs t)) _
    rw [show (bs.map (ConLeche.Model.AnnotTerm.instSeq vs t)).length
        = bs.length from by simp]
    simp only [List.length_cons]
    rfl

open ConLeche.Semantics.AnnotTerm in
/-- A padded fired spine resolves a frame variable to its slot's
reading (`padHit`), with `.prf` as the padding element. -/
theorem padHit {K : Nat} (q : AnnotTerm) :
    ∀ (n p : Nat) (vals : List AnnotTerm), p < n →
    vals.length = n → n ≤ K →
    ConLeche.Model.AnnotTerm.instSeq
        (vals ++ List.replicate (K - n) q) (K - 1)
        (.bvar (K - 1 - p))
      = vals.getD p default := by
  intro n p vals hp hvl hn
  have hlenT : (vals ++ List.replicate (K - n) q).length
      = K := by
    simp only [List.length_append, List.length_replicate, hvl]
    omega
  have hidx : (vals ++ List.replicate (K - n)
      q)[(vals ++ List.replicate (K - n)
        q).length - 1 - (K - 1 - p)]?
      = some (vals.getD p default) := by
    rw [hlenT, show K - 1 - (K - 1 - p) = p from by omega,
      List.getElem?_append_left (by omega),
      List.getElem?_eq_getElem (by omega : p < vals.length)]
    simp [List.getD, List.getElem?_eq_getElem
      (by omega : p < vals.length)]
  have h1 := instSeqAV_bvar_hit
    (vals ++ List.replicate (K - n) q) 0
    (K - 1 - p) (vals.getD p default) hidx (by omega)
  simp only [Nat.zero_add] at h1
  rw [hlenT] at h1
  rw [h1, ConLeche.Semantics.AnnotTerm.liftN_zero]

open ConLeche.Semantics.AnnotTerm in
/-- **The chain identity at the reading** (`nestedChain`): a pin's
frame reading under any fired spine that starts with the prefix
readings is the canonical reverse chain at those readings. -/
theorem nestedChain {rP cnF : Nat} {xs : List AnnotTerm} (q : AnnotTerm)
    (hxstakelen : (xs.take rP).length = rP) :
    ∀ (vals : List AnnotTerm) (n : Nat) (wp : AnnotTerm),
    vals.length = n → n ≤ rP + cnF → rP ≤ n →
    vals.take rP = xs.take rP →
    Term.bvarsBelow rP wp.erase →
    ConLeche.Model.AnnotTerm.instSeq
      (vals ++ List.replicate (rP + cnF - n) q)
      (rP + cnF - 1)
      (ConLeche.Model.AnnotTerm.instRevChain ((List.range rP).map fun j =>
        AnnotTerm.bvar (rP + cnF - 1 - j)) wp)
      = ConLeche.Model.AnnotTerm.instRevChain (xs.take rP) wp := by
  have hpadhit := padHit (K := rP + cnF) q
  intro vals n wp hvl hn hrn hpre hbv
  rw [instSeqAV_instRevChain _ _ _ _ (by
      simp only [List.length_append, List.length_replicate, hvl]
      omega),
    List.length_map, List.length_range,
    instSeqAV_eq_self_of_bvarsBelow _ _ hbv (by
      simp only [List.length_append, List.length_replicate, hvl]
      omega),
    List.map_map]
  congr 1
  conv => rhs; rw [show xs.take rP = (List.range rP).map
    (fun j => (xs.take rP).getD j default) from by
      conv => lhs; rw [← List.map_id (xs.take rP)]
      rw [← map_range_getD (xs.take rP) id, hxstakelen]
      simp only [id_eq]]
  refine List.map_congr_left fun j hj => ?_
  have hjr : j < rP := List.mem_range.mp hj
  show ConLeche.Model.AnnotTerm.instSeq (vals ++ List.replicate
      (rP + cnF - n) q) (rP + cnF - 1)
      (.bvar (rP + cnF - 1 - j)) = _
  rw [hpadhit n j vals (by omega) hvl hn, ← hpre]
  simp only [List.getD]
  rw [List.getElem?_take_of_lt hjr]

/-- A reading spine, built positionally (`DenoteSpine.of_getElem`). -/
theorem DenoteMetaSpine.of_getD {d : Nat} :
    ∀ (as : List Expr) (vs : List AnnotTerm), as.length = vs.length →
      (∀ q, q < as.length →
        denoteMeta acval env φ d (as.getD q default)
          = some (vs.getD q default)) →
      DenoteMetaSpine acval env φ d as vs := by
  intro as
  induction as with
  | nil =>
    intro vs hlen _
    obtain rfl : vs = [] := (List.length_eq_zero_iff.mp hlen.symm)
    exact .nil
  | cons a as ih =>
    intro vs hlen hget
    match vs, hlen with
    | v :: vs', hlen =>
    refine .cons ?_ (ih vs' (by simpa using hlen) ?_)
    · have h0 := hget 0 (by simp)
      simpa using h0
    · intro q hq
      have h1 := hget (q + 1) (by simpa using hq)
      simpa using h1

/-! ## The composite -/

set_option maxHeartbeats 1600000 in
/-- **`pinCross`'s reading direction** (task #161 part 9): the
`openRev` reading `RecRuleLaw`'s repaired conjunct *existentially
quantifies* comes from the instantiated pin's own reading, which is
the object the checker's certificate is about.

The composite below takes the `openRev` reading as a premise and
produces the instantiated one; the consumer (`iotaRuleNested`) has
the instantiated one — the `TypedListW` row's own denotation, read
through `denoteP_isSome_of_denote` — and needs the `openRev` one.  The
same two laws run backwards: `Rules.denoteMeta_openRev` presents the
instantiated reading as an `Option.map` of the `openRev` one, so the
former being `some` forces the latter. -/
theorem pinOpenRevReads
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ)
    (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {rP cnF : Nat}
    {os : List Expr} (hoslen : os.length = rP)
    (hshape : ∀ (i : Nat) (x : Expr), os[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hwsOs : ∀ x ∈ os, Expr.WScoped (rP + cnF) x)
    (hbOs : ∀ x ∈ os, x.looseBVarsBounded 0 = true)
    {p : Expr} (hpw : p.hasFvar = false)
    (hpb : p.looseBVarsBounded rP = true)
    {w0 : AnnotTerm}
    (hw0 : denoteMeta acval env φ (rP + cnF)
      (Expr.instSpine os (rP - 1) p) = some w0) :
    ∃ vpa, denoteMeta acval env φ rP (openRev 0 rP p) = some vpa := by
  have hbvslen : ((List.range rP).map
      (fun j => AnnotTerm.bvar (rP + cnF - 1 - j))).length = rP := by
    rw [List.length_map, List.length_range]
  have hsp : DenoteMetaSpine acval env φ (rP + cnF) os
      ((List.range rP).map (fun j => AnnotTerm.bvar (rP + cnF - 1 - j))) := by
    refine DenoteMetaSpine.of_getD os _ (by rw [hoslen, hbvslen]) ?_
    intro q hq
    rw [hoslen] at hq
    rcases hx : os[q]? with _ | x
    · rw [List.getElem?_eq_none_iff, hoslen] at hx
      omega
    obtain ⟨ty, rfl⟩ := hshape q x hx
    have h1 : os.getD q default = Expr.fvar q ty := by
      rw [List.getD, hx]
      rfl
    have h2 : ((List.range rP).map
        (fun j => AnnotTerm.bvar (rP + cnF - 1 - j))).getD q default
        = AnnotTerm.bvar (rP + cnF - 1 - q) := by
      rw [List.getD, List.getElem?_map, List.getElem?_range hq]
      rfl
    rw [h1, h2]
    exact denoteMeta_fvar acval (rP + cnF) q ty
  have hkey := Rules.denoteMeta_openRev (acval := acval) (env := env) (φ := φ)
    hacl hainst os (e := p) (d := rP + cnF)
    (fun a ha => ⟨hwsOs a ha, hbOs a ha⟩)
    (Expr.fvarsBelow_of_fvarLeaves (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hpw] at hl
      exact nomatch hl))
    (by rw [hoslen]; exact hpb) hsp
  rw [hoslen] at hkey
  have hbase := Rules.denoteMeta_openRev_base (acval := acval) (cval := cval)
    (env := env) (φ := φ) hacl hlink hcl hpw hpb (rP + cnF)
  rw [hbase] at hkey
  rw [Expr.instSpine_eq_instSeq] at hw0
  rw [hw0] at hkey
  rcases hv : denoteMeta acval env φ rP (openRev 0 rP p) with _ | vpa
  · rw [hv] at hkey
    exact nomatch hkey
  · exact ⟨vpa, rfl⟩

set_option maxHeartbeats 1600000 in
/-- **The nested pin bridge, at the reading** (`pinCrossS`): a stored
pin, instantiated at a frame's prefix openers and read at the frame
depth, instantiates along the padded fired prefix to the pin's own
canonical reading applied in reverse along that prefix.

Stated at an arbitrary opener spine `os` of length `rP` (v1 states it
at the *statement* frame and bakes in the renaming); the producer
spends it at the **public** frame `fvsP`, which is where the checker's
`checkAnnotList`/`checkTypedList` certificates on `pinsP` live
(`Inductives/Modeled.lean:282`).

The fired spine is likewise arbitrary (task #161 part 8, kit
generalization — the exposure is `indBottomNested`, the lemma's
second caller): any `vals` of length `n ∈ [rP, rP + cnF]` whose prefix
is `zs`, padded to the frame's width.  The producer spends it at
`n = rP` (all padding), the nested bottom at `n = rP + cnF` (no
padding, `vals` the fired statement spine).  `nestedChain` was
already generic in exactly this way; only `pinCross`'s own statement
had baked the producer's instance in. -/
theorem pinCross
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ)
    (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {rP cnF : Nat} (q : AnnotTerm)
    {os : List Expr} (hoslen : os.length = rP)
    (hshape : ∀ (i : Nat) (x : Expr), os[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hwsOs : ∀ x ∈ os, Expr.WScoped (rP + cnF) x)
    (hbOs : ∀ x ∈ os, x.looseBVarsBounded 0 = true)
    {p : Expr} (hpw : p.hasFvar = false)
    (hpb : p.looseBVarsBounded rP = true)
    {vpa : AnnotTerm}
    (hvpden : denoteMeta acval env φ rP (openRev 0 rP p) = some vpa)
    {zs : List AnnotTerm} (hzslen : zs.length = rP)
    {vals : List AnnotTerm} {n : Nat} (hvalslen : vals.length = n)
    (hrPn : rP ≤ n) (hn : n ≤ rP + cnF)
    (hvalspre : vals.take rP = zs) :
    ∃ w0, denoteMeta acval env φ (rP + cnF)
        (Expr.instSpine os (rP - 1) p) = some w0 ∧
      ConLeche.Model.AnnotTerm.instSeq
          (vals ++ List.replicate (rP + cnF - n) q) (rP + cnF - 1) w0
        = ConLeche.Model.AnnotTerm.instRevChain zs vpa := by
  -- the frame's prefix openers read to the canonical bvar spine
  have hbvslen : ((List.range rP).map
      (fun j => AnnotTerm.bvar (rP + cnF - 1 - j))).length = rP := by
    rw [List.length_map, List.length_range]
  have hsp : DenoteMetaSpine acval env φ (rP + cnF) os
      ((List.range rP).map (fun j => AnnotTerm.bvar (rP + cnF - 1 - j))) := by
    refine DenoteMetaSpine.of_getD os _ (by rw [hoslen, hbvslen]) ?_
    intro q hq
    rw [hoslen] at hq
    rcases hx : os[q]? with _ | x
    · rw [List.getElem?_eq_none_iff, hoslen] at hx
      omega
    obtain ⟨ty, rfl⟩ := hshape q x hx
    have h1 : os.getD q default = Expr.fvar q ty := by
      rw [List.getD, hx]
      rfl
    have h2 : ((List.range rP).map
        (fun j => AnnotTerm.bvar (rP + cnF - 1 - j))).getD q default
        = AnnotTerm.bvar (rP + cnF - 1 - q) := by
      rw [List.getD, List.getElem?_map, List.getElem?_range hq]
      rfl
    rw [h1, h2]
    exact denoteMeta_fvar acval (rP + cnF) q ty
  -- the instantiation, read through the reverse opening
  have hkey := Rules.denoteMeta_openRev (acval := acval) (env := env) (φ := φ)
    hacl hainst os (e := p) (d := rP + cnF)
    (fun a ha => ⟨hwsOs a ha, hbOs a ha⟩)
    (Expr.fvarsBelow_of_fvarLeaves (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hpw] at hl
      exact nomatch hl))
    (by rw [hoslen]; exact hpb) hsp
  rw [hoslen] at hkey
  -- the opened reading is base-independent
  have hbase := Rules.denoteMeta_openRev_base (acval := acval) (cval := cval)
    (env := env) (φ := φ) hacl hlink hcl hpw hpb (rP + cnF)
  rw [hbase, hvpden] at hkey
  simp only [Option.map_some] at hkey
  refine ⟨_, by rw [Expr.instSpine_eq_instSeq]; exact hkey, ?_⟩
  -- the chain rides the fired spine
  have hbv : Term.bvarsBelow rP vpa.erase := by
    refine denote_bvarsBelow (cval := cval) (env := env) (φ := φ) hcl
      rP (openRev 0 rP p) ?_ ?_ (denoteMeta_erase hlink rP _ hvpden)
    · have h := openRev_WScoped (d := 0)
        (Expr.WScoped.of_not_hasFvar hpw) rP
      rwa [Nat.zero_add] at h
    · exact openRev_bounded rP 0 (by simpa using hpb)
  have hchain := nestedChain (rP := rP) (cnF := cnF) (xs := zs) q
    (by rw [List.take_of_length_le (Nat.le_of_eq hzslen)]; exact hzslen)
    vals n vpa hvalslen hn hrPn
    (by rw [hvalspre, List.take_of_length_le (Nat.le_of_eq hzslen)]) hbv
  rw [List.take_of_length_le (Nat.le_of_eq hzslen)] at hchain
  exact hchain

end ConLeche.Model
