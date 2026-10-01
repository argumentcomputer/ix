module

public import ConLeche.Model.Inductives.FixRecReadDefs
public import ConLeche.Verify.Inductives.FixRec
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitRename
public section

/-!
# The generated recursive recursor's readings (task #188)

`ConLeche/Model/Inductives/SumRecRead.lean` with the inductive hypotheses:
the generated recursive recursor type reads to the Π-tower over
`fixRecDataAV` and rule `j` to the λ-tower over `fixRuleDataAV`
(`ConLeche/Model/Inductives/FixRecReadDefs.lean`).

The one genuinely new reading is the `ih` binder's domain
`∀ a⃗, motive e⃗_i(a⃗) (f_i a⃗)`.  A recursive field's own telescope and
its domain's index expressions are read at the constructor's OWN
opening — the parameters, the `i` earlier fields, then the telescope's
own openers (`FieldReadAt`, off `CtorReadR` by `fieldReadAt_of`) —
while the recursor's frame puts the fields `o` slots higher (the
motive and the earlier minors sit between) and `nF - i + l` binders
above.  Moving between the two frames is `Expr.shiftFrom` iterated
(`denoteMeta_instSeq_shift`), twice: once to insert the fields and the
earlier hypotheses below the field's own frame, once to insert the
`o` extras between the parameters and the fields — precisely
`ihIdxAtM`'s two lifts, the telescope's openers staying innermost
(task #202).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## Reading through an inserted block of variables -/

/-- **`denoteMeta_shiftFrom`, iterated**: inserting `o` fresh variable
slots at index `p` lifts the reading by `o` at the cut `d - p`. -/
theorem denoteMeta_shiftFromN {acval : Name → (Name → Nat) → AnnotTerm}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {p : Nat} :
    ∀ (o : Nat) {e : Expr} {d : Nat}, p ≤ d → Expr.WScoped d e →
      denoteMeta acval env φ (d + o) (Expr.shiftFromN p o e)
        = (denoteMeta acval env φ d e).map (AnnotTerm.liftN o · (d - p))
  | 0, e, d, _, _ => by
    show denoteMeta acval env φ (d + 0) e = _
    rw [Nat.add_zero]
    cases denoteMeta acval env φ d e with
    | none => rfl
    | some v => simp only [Option.map_some, AnnotTerm.liftN_zero]
  | o + 1, e, d, hpd, hw => by
    show denoteMeta acval env φ (d + (o + 1)) (Expr.shiftFrom p (Expr.shiftFromN p o e)) = _
    rw [show d + (o + 1) = d + o + 1 from by omega,
      denoteMeta_shiftFrom hacl _ (d + o) (by omega) (Expr.WScoped_shiftFromN o hw),
      denoteMeta_shiftFromN hacl o hpd hw]
    cases denoteMeta acval env φ d e with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Option.some.injEq]
      exact AVExprSubst.liftN_liftN_absorb v (by omega) (by omega) 1

/-- **A closed expression at a shifted opening.**  `A` opens it at the
variables `0 … A.length - 1`; `B` opens it at the same variables with
those at or above `p` moved `o` slots up.  The reading moves with
them: it is lifted by `o` at the cut `d - p`. -/
theorem denoteMeta_instSeq_shift {m : EnvModel V env} {ψ : Name → Nat} {p o d t : Nat}
    {e : Expr} (hef : e.hasFvar = false)
    {A B : List Expr} (hlen : A.length = B.length) (hpd : p ≤ d)
    (hAw : ∀ (k : Nat) (x : Expr), A[k]? = some x → Expr.WScoped d x)
    (hAB : ∀ (k : Nat) (a b : Expr), A[k]? = some a → B[k]? = some b →
      ∃ (ia : Nat) (tya tyb : Expr),
        a = Expr.fvar ia tya ∧ b = Expr.fvar (if ia < p then ia else ia + o) tyb)
    {E : AnnotTerm}
    (hE : denoteMeta m.acval env ψ d (Expr.instSeq A t e) = some E) :
    denoteMeta m.acval env ψ (d + o) (Expr.instSeq B t e) = some (E.liftN o (d - p)) := by
  have hAcl : ∀ x ∈ A, Expr.WScoped d x := fun x hx => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    exact hAw q x hq
  have hw : Expr.WScoped d (Expr.instSeq A t e) :=
    Expr.instSeq_WScoped A t hAcl (Expr.WScoped.of_not_hasFvar hef)
  have hshift := denoteMeta_shiftFromN (acval := m.acval) (env := env) (φ := ψ)
    m.acval_closed (p := p) o hpd hw
  rw [hE, Option.map_some, Expr.shiftFromN_instSeq p o A t e,
    Expr.shiftFromN_eq_self_of_not_hasFvar o hef] at hshift
  have herased : Expr.ErasedEq (Expr.instSeq (A.map (Expr.shiftFromN p o)) t e)
      (Expr.instSeq B t e) := by
    refine Expr.instSeq_erasedEq_args _ _ t (Expr.ErasedEq.rfl e) ?_ (by simp [hlen])
    intro k a₁ a₂ ha₁ ha₂
    rw [List.getElem?_map] at ha₁
    cases hA : A[k]? with
    | none => rw [hA] at ha₁; exact nomatch ha₁
    | some a =>
      rw [hA, Option.map_some, Option.some.injEq] at ha₁
      obtain ⟨ia, tya, tyb, rfl, hb⟩ := hAB k a a₂ hA ha₂
      obtain ⟨ty', hsh⟩ := Expr.shiftFromN_fvar p o ia tya
      rw [← ha₁, hsh, hb]
      exact Eq.refl _
  rw [denoteMeta_erasedEq herased (d + o)] at hshift
  exact hshift

/-! ## Spine bookkeeping -/

/-- A read spine, re-read entry by entry at another frame. -/
theorem DenoteMetaSpine.map_map {acval : Name → (Name → Nat) → AnnotTerm} {d d' : Nat}
    {f g : Expr → Expr} {h : AnnotTerm → AnnotTerm} :
    ∀ {as : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d (as.map f) vs →
      (∀ (a : Expr) (v : AnnotTerm), a ∈ as → denoteMeta acval env φ d (f a) = some v →
        denoteMeta acval env φ d' (g a) = some (h v)) →
      DenoteMetaSpine acval env φ d' (as.map g) (vs.map h)
  | [], vs, hsp, _ => by
    cases hsp
    exact .nil
  | a :: as, vs, hsp, hfg => by
    rw [List.map_cons] at hsp
    cases hsp with
    | cons hd htl =>
      exact .cons (hfg a _ List.mem_cons_self hd)
        (DenoteMetaSpine.map_map htl fun x v hx hv => hfg x v (List.mem_cons_of_mem _ hx) hv)

/-- A pointwise-read mapped spine. -/
theorem DenoteMetaSpine.of_map {α : Type} {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {f : α → Expr} {g : α → AnnotTerm} :
    ∀ (l : List α), (∀ a ∈ l, denoteMeta acval env φ d (f a) = some (g a)) →
      DenoteMetaSpine acval env φ d (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h =>
    .cons (h a List.mem_cons_self)
      (DenoteMetaSpine.of_map l fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## Frames of the same variables -/

/-- Two frames of the same variables read an expression the same: the
variables' annotations do not matter (`denoteMeta_erasedEq`). -/
theorem denoteMeta_instSeq_congr {m : EnvModel V env} {ψ : Name → Nat} {d t : Nat} {e : Expr}
    {L L' : List Expr} (hlen : L.length = L'.length)
    (hidx : ∀ (k : Nat) (a b : Expr), L[k]? = some a → L'[k]? = some b →
      ∃ (q : Nat) (ty ty' : Expr), a = Expr.fvar q ty ∧ b = Expr.fvar q ty') :
    denoteMeta m.acval env ψ d (Expr.instSeq L t e)
      = denoteMeta m.acval env ψ d (Expr.instSeq L' t e) := by
  refine denoteMeta_erasedEq (Expr.instSeq_erasedEq_args L L' t (Expr.ErasedEq.rfl e) ?_ hlen) d
  intro k a b ha hb
  obtain ⟨q, ty, ty', rfl, rfl⟩ := hidx k a b ha hb
  exact Eq.refl _

/-- A frame of the variables `0 … D-1` is the canonical opening. -/
theorem denoteMeta_instSeq_canon {m : EnvModel V env} {ψ : Name → Nat} {d t D : Nat} {e : Expr}
    {L : List Expr} (hlen : L.length = D)
    (hidx : ∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty) :
    denoteMeta m.acval env ψ d (Expr.instSeq L t e)
      = denoteMeta m.acval env ψ d (Expr.instSeq (openFvars 0 D) t e) := by
  refine denoteMeta_instSeq_congr (by simp [hlen]) ?_
  intro k a b ha hb
  obtain ⟨ty, rfl⟩ := hidx k a ha
  have hk : k < D := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp ha).1
  rw [openFvars_getElem? hk, Nat.zero_add] at hb
  obtain rfl := (Option.some.inj hb).symm
  exact ⟨k, ty, _, rfl, rfl⟩

/-- A canonical opening's variables are scoped. -/
theorem openFvars_WScoped {base k d : Nat} (h : base + k ≤ d) :
    ∀ (q : Nat) (x : Expr), (openFvars base k)[q]? = some x → Expr.WScoped d x := by
  intro q x hq
  have hqk : q < k := by
    rcases Nat.lt_or_ge q k with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none (by simp; omega)] at hq
      exact nomatch hq
  rw [openFvars_getElem? hqk] at hq
  obtain rfl := (Option.some.inj hq).symm
  simp only [Expr.WScoped]
  exact ⟨by omega, trivial⟩

/-! ## The `ih` binders' index expressions -/

/-- A Π-tower's binders and body inherit its closedness and its
loose-bvar bound (each binder under the earlier ones). -/
theorem Expr.piBinders_props : ∀ (e : Expr) (c : Nat), e.hasFvar = false →
    e.looseBVarsBounded c = true →
    (∀ (k : Nat) (b : Expr × BinderMeta), (e.piBinders).1[k]? = some b →
        b.1.hasFvar = false ∧ b.1.looseBVarsBounded (c + k) = true) ∧
      (e.piBinders).2.hasFvar = false ∧
      (e.piBinders).2.looseBVarsBounded (c + (e.piBinders).1.length) = true
  | .forallE ty bd mt, c, hf, hb => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hk, hbf, hbb⟩ := Expr.piBinders_props bd (c + 1) hf.2 hb.2
    rw [Expr.piBinders_forallE]
    refine ⟨?_, hbf, ?_⟩
    · intro k b hbk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hbk
        subst hbk
        exact ⟨hf.1, by rw [Nat.add_zero]; exact hb.1⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hbk
        obtain ⟨h1, h2⟩ := hk k b hbk
        exact ⟨h1, by rw [show c + (k + 1) = c + 1 + k from by omega]; exact h2⟩
    · simp only [List.length_cons]
      rw [show c + ((bd.piBinders).1.length + 1) = c + 1 + (bd.piBinders).1.length from by omega]
      exact hbb
  | .bvar _, _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .fvar .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .sort _, _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .const .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .app .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .lam .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .letE .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .lit _, _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .proj .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩

/-- A field's own telescope and the index expressions of its domain
inherit the constructor type's closedness and their frames' loose-bvar
bounds (the telescope's binder `k` under the `k` earlier ones, the
index expressions under the whole telescope). -/
theorem structFieldTele_props {cty : Expr} {nP nF i : Nat}
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF) :
    (∀ (k : Nat) (b : Expr × BinderMeta),
        (ConLeche.structFieldTeleOf cty nP nF i)[k]? = some b →
        b.1.hasFvar = false ∧ b.1.looseBVarsBounded (nP + i + k) = true) ∧
      ∀ e ∈ ConLeche.structFieldIdxOf cty nP nF i,
        e.hasFvar = false ∧
          e.looseBVarsBounded (nP + i + (ConLeche.structFieldTeleOf cty nP nF i).length) = true := by
  obtain ⟨⟨cbs, cbody⟩, hs⟩ := Option.isSome_iff_exists.mp hstripC
  have hlenbs : cbs.length = nP + nF := Expr.stripPis_length _ hs
  obtain ⟨b, hb⟩ : ∃ b, cbs[nP + i]? = some b :=
    ⟨cbs[nP + i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hbd : cbs.getD (nP + i) default = b := by
    rw [List.getD_eq_getElem?_getD, hb]
    rfl
  have hbf : b.1.hasFvar = false :=
    (ConLeche.stripPis_not_hasFvar _ hs hCf).1 b (List.mem_of_getElem? hb)
  have hbb : b.1.looseBVarsBounded (nP + i) = true := by
    have := ConLeche.stripPis_binder_bounded (nP + nF) hs hCb (nP + i) b hb
    rwa [Nat.zero_add] at this
  have htele : ConLeche.structFieldTeleOf cty nP nF i = (b.1.piBinders).1 := by
    unfold ConLeche.structFieldTeleOf
    rw [hs]
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
  have hidx : ConLeche.structFieldIdxOf cty nP nF i = (b.1.piBinders).2.getAppArgs.drop nP := by
    unfold ConLeche.structFieldIdxOf
    rw [hs]
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
  obtain ⟨hk, hpf, hpb⟩ := Expr.piBinders_props b.1 (nP + i) hbf hbb
  rw [htele, hidx]
  refine ⟨hk, ?_⟩
  intro e he
  have hmem : e ∈ (b.1.piBinders).2.getAppArgs := List.mem_of_mem_drop he
  exact ⟨ConLeche.hasFvar_getAppArgs hpf e hmem, ConLeche.looseBVarsBounded_getAppArgs hpb e hmem⟩

/-- **`structIdxAt`, instantiated at the recursor's frame under the
field's own telescope** — `ConLeche.instSeq_structIdxAt` with the
telescope's `j` openers below the frame (task #202). -/
theorem instSeq_structIdxAtM (P X F I A : List Expr) {nP o nF l i j : Nat} {e : Expr}
    (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF) (hI : I.length = l)
    (hA : A.length = j)
    (hclP : ∀ a ∈ P, a.looseBVarsBounded 0 = true)
    (hclF : ∀ a ∈ F, a.looseBVarsBounded 0 = true)
    (hi : i ≤ nF) (heb : e.looseBVarsBounded (nP + i + j) = true) :
    Expr.instSeq (P ++ X ++ F ++ I ++ A) (nP + o + nF + l + j - 1)
        (ConLeche.structIdxAt nF o i l j e)
      = Expr.instSeq (P ++ F.take i ++ A) (nP + i + j - 1) e := by
  have hl1 : (P ++ X ++ F ++ I).length = nP + o + nF + l := by
    simp [hP, hX, hF, hI]
    omega
  have hl2 : (P ++ F.take i).length = nP + i := by
    simp [hP, hF]
    omega
  have hcore : Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l + j - 1)
      (ConLeche.structIdxAt nF o i l j e)
      = Expr.instSeq (P ++ F.take i) (nP + i + j - 1) e := by
    unfold ConLeche.structIdxAt
    have hq : (e.liftLooseBVars (nF - i + l) j).looseBVarsBounded
        (P.length + (nF + l + j)) = true := by
      have := Expr.looseBVarsBounded_liftLooseBVars (nF - i + l) e (b := nP + i + j) (c := j) heb
      exact Expr.looseBVarsBounded_mono (by rw [hP]; omega) this
    have h1 : Expr.instSeq (P ++ X) (nP + o + nF + l + j - 1)
        ((e.liftLooseBVars (nF - i + l) j).liftLooseBVars o (nF + l + j))
        = Expr.instSeq P (nP + nF + l + j - 1) (e.liftLooseBVars (nF - i + l) j) := by
      have h := ConLeche.instSeq_liftLooseBVars_mid P X (c := nF + l + j) hclP hq
      rw [hP, hX] at h
      rw [show nP + o + nF + l + j - 1 = nP + o + (nF + l + j) - 1 from by omega,
        show nP + nF + l + j - 1 = nP + (nF + l + j) - 1 from by omega]
      exact h
    have hsplit : P ++ X ++ F ++ I = (P ++ X) ++ (F ++ I) := by simp
    have hsplit2 : P ++ (F ++ I) = (P ++ F.take i) ++ (F.drop i ++ I) := by
      rw [List.append_assoc, ← List.append_assoc (F.take i), List.take_append_drop]
    have hlen2 : (F.drop i ++ I).length = nF - i + l := by simp [hF, hI]
    have hcl2 : ∀ a ∈ P ++ F.take i, a.looseBVarsBounded 0 = true := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact hclP a h
      · exact hclF a (List.mem_of_mem_take h)
    have h2 : Expr.instSeq (P ++ (F ++ I)) (nP + nF + l + j - 1)
        (e.liftLooseBVars (nF - i + l) j)
        = Expr.instSeq (P ++ F.take i) (nP + i + j - 1) e := by
      rw [hsplit2]
      have := ConLeche.instSeq_liftLooseBVars_mid (P ++ F.take i) (F.drop i ++ I) (c := j) hcl2
        (by rw [hl2]; exact heb)
      rw [hl2, hlen2] at this
      rw [show nP + nF + l + j - 1 = nP + i + (nF - i + l) + j - 1 from by omega]
      exact this
    rw [hsplit, Expr.instSeq_append (P ++ X) (F ++ I)]
    show Expr.instSeq (F ++ I) (nP + o + nF + l + j - 1 - (P ++ X).length)
        (Expr.instSeq (P ++ X) (nP + o + nF + l + j - 1)
          ((e.liftLooseBVars (nF - i + l) j).liftLooseBVars o (nF + l + j))) = _
    rw [h1, show (P ++ X).length = nP + o from by simp [hP, hX],
      show nP + o + nF + l + j - 1 - (nP + o) = nP + nF + l + j - 1 - P.length from by
        rw [hP]; omega,
      ← Expr.instSeq_append P (F ++ I), h2]
  rw [Expr.instSeq_append (P ++ X ++ F ++ I) A, Expr.instSeq_append (P ++ F.take i) A, hcore,
    hl1, hl2]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hAnil : A = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hAnil
    rfl
  · rw [show nP + o + nF + l + j - 1 - (nP + o + nF + l) = nP + i + j - 1 - (nP + i) from by omega]

set_option maxHeartbeats 1600000 in
/-- **A recursive field's expression at the recursor's frame.**  The
constructor reads it at its own opening (the parameters, the `i`
earlier fields, then the `j` openers of the field's own telescope);
the frame `p⃗ x⃗ f⃗ ih⃗ a⃗` reads it at the same variables with the fields
`o` slots higher and `nF - i + l` binders below — the telescope's own
openers staying innermost — which is `ihIdxAtM`. -/
theorem denoteMeta_ihIdxAtM {m : EnvModel V env} {ψ : Name → Nat} {nP nF o l i j : Nat}
    {e : Expr} {E : AnnotTerm} (hef : e.hasFvar = false)
    (heb : e.looseBVarsBounded (nP + i + j) = true) (hi : i ≤ nF)
    {S : List Expr} (hS : S.length = nP + i)
    (hidxS : ∀ (k : Nat) (x : Expr), S[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    {P X F I : List Expr} (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF)
    (hI : I.length = l)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty)
    (hE : denoteMeta m.acval env ψ (nP + i + j)
      (Expr.instSeq (S ++ openFvars (nP + i) j) (nP + i + j - 1) e) = some E) :
    denoteMeta m.acval env ψ (nP + o + nF + l + j)
        (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l) j)
          (nP + o + nF + l + j - 1) (ConLeche.structIdxAt nF o i l j e))
      = some (ihIdxAtM nF o i l j E) := by
  have hclP : ∀ a ∈ P, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxP q a hq
    rfl
  have hclF : ∀ a ∈ F, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxF q a hq
    rfl
  -- the source frame, canonically
  have hidxSA : ∀ (k : Nat) (x : Expr), (S ++ openFvars (nP + i) j)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    by_cases hk : k < nP + i
    · rw [List.getElem?_append_left (by rw [hS]; exact hk)] at hx
      exact hidxS k x hx
    · rw [List.getElem?_append_right (by rw [hS]; omega), hS] at hx
      have hlt : k - (nP + i) < j := by
        rcases Nat.lt_or_ge (k - (nP + i)) j with h | h
        · exact h
        · rw [List.getElem?_eq_none (by rw [openFvars_length]; omega)] at hx
          exact nomatch hx
      rw [openFvars_getElem? hlt] at hx
      obtain rfl := (Option.some.inj hx).symm
      exact ⟨.sort .zero, by congr 1; omega⟩
  have hlenSA : (S ++ openFvars (nP + i) j).length = nP + i + j := by
    rw [List.length_append, hS, openFvars_length]
  rw [denoteMeta_instSeq_canon hlenSA hidxSA] at hE
  have hlenA : (openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j).length = nP + i + j := by
    rw [List.length_append, openFvars_length, openFvars_length]
  have hlenB : (openFvars 0 nP ++ openFvars (nP + o) i ++ openFvars (nP + o + nF + l) j).length
      = nP + i + j := by
    rw [List.length_append, List.length_append, openFvars_length, openFvars_length,
      openFvars_length]
  have hlenPF : (P ++ F.take i).length = nP + i := by
    rw [List.length_append, hP, List.length_take, hF]
    omega
  have hlenTgt : (P ++ F.take i ++ openFvars (nP + o + nF + l) j).length = nP + i + j := by
    rw [List.length_append, hlenPF, openFvars_length]
  -- the fields and the hypotheses, inserted between the field's frame and its telescope
  have hcorr1 : ∀ (k : Nat) (a b : Expr), (openFvars 0 (nP + i + j))[k]? = some a →
      (openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j)[k]? = some b →
      ∃ (ia : Nat) (tya tyb : Expr),
        a = Expr.fvar ia tya ∧
          b = Expr.fvar (if ia < nP + i then ia else ia + (nF - i + l)) tyb := by
    intro k a b ha hb
    have hka : k < nP + i + j := by
      rcases Nat.lt_or_ge k (nP + i + j) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [openFvars_length]; omega)] at ha
        exact nomatch ha
    rw [openFvars_getElem? hka, Nat.zero_add] at ha
    obtain rfl := (Option.some.inj ha).symm
    by_cases hk : k < nP + i
    · rw [List.getElem?_append_left (by rw [openFvars_length]; omega), openFvars_getElem? hk,
        Nat.zero_add] at hb
      obtain rfl := (Option.some.inj hb).symm
      refine ⟨k, Expr.sort Level.zero, Expr.sort Level.zero, rfl, ?_⟩
      rw [if_pos hk]
    · rw [List.getElem?_append_right (by rw [openFvars_length]; omega), openFvars_length,
        openFvars_getElem? (show k - (nP + i) < j from by omega)] at hb
      obtain rfl := (Option.some.inj hb).symm
      refine ⟨k, Expr.sort Level.zero, Expr.sort Level.zero, rfl, ?_⟩
      rw [if_neg hk]
      congr 1
      omega
  have hshift1 := denoteMeta_instSeq_shift (m := m) (ψ := ψ) (p := nP + i) (o := nF - i + l)
    (d := nP + i + j) (t := nP + i + j - 1) (A := openFvars 0 (nP + i + j))
    (B := openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j) hef
    (by rw [openFvars_length, List.length_append, openFvars_length, openFvars_length])
    (by omega) (openFvars_WScoped (by omega)) hcorr1 hE
  rw [show nP + i + j + (nF - i + l) = nP + nF + l + j from by omega,
    show nP + i + j - (nP + i) = j from by omega] at hshift1
  -- the extras, inserted between the parameters and the fields
  have hcorr2 : ∀ (k : Nat) (a b : Expr),
      (openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j)[k]? = some a →
      (openFvars 0 nP ++ openFvars (nP + o) i ++ openFvars (nP + o + nF + l) j)[k]? = some b →
      ∃ (ia : Nat) (tya tyb : Expr),
        a = Expr.fvar ia tya ∧ b = Expr.fvar (if ia < nP then ia else ia + o) tyb := by
    intro k a b ha hb
    have hka : k < nP + i + j := by
      rcases Nat.lt_or_ge k (nP + i + j) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hlenA]; omega)] at ha
        exact nomatch ha
    by_cases hk : k < nP + i
    · rw [List.getElem?_append_left (by rw [openFvars_length]; omega), openFvars_getElem? hk,
        Nat.zero_add] at ha
      obtain rfl := (Option.some.inj ha).symm
      rw [List.getElem?_append_left
        (by rw [List.length_append, openFvars_length, openFvars_length]; omega)] at hb
      by_cases hk2 : k < nP
      · rw [List.getElem?_append_left (by rw [openFvars_length]; omega), openFvars_getElem? hk2,
          Nat.zero_add] at hb
        obtain rfl := (Option.some.inj hb).symm
        refine ⟨k, Expr.sort Level.zero, Expr.sort Level.zero, rfl, ?_⟩
        rw [if_pos hk2]
      · rw [List.getElem?_append_right (by rw [openFvars_length]; omega), openFvars_length,
          openFvars_getElem? (show k - nP < i from by omega)] at hb
        obtain rfl := (Option.some.inj hb).symm
        refine ⟨k, Expr.sort Level.zero, Expr.sort Level.zero, rfl, ?_⟩
        rw [if_neg hk2]
        congr 1
        omega
    · rw [List.getElem?_append_right (by rw [openFvars_length]; omega), openFvars_length,
        openFvars_getElem? (show k - (nP + i) < j from by omega)] at ha
      obtain rfl := (Option.some.inj ha).symm
      rw [List.getElem?_append_right
          (by rw [List.length_append, openFvars_length, openFvars_length]; omega),
        List.length_append, openFvars_length, openFvars_length,
        openFvars_getElem? (show k - (nP + i) < j from by omega)] at hb
      obtain rfl := (Option.some.inj hb).symm
      refine ⟨nP + nF + l + (k - (nP + i)), Expr.sort Level.zero, Expr.sort Level.zero, rfl, ?_⟩
      rw [if_neg (show ¬ nP + nF + l + (k - (nP + i)) < nP from by omega)]
      congr 1
      omega
  have hAw2 : ∀ (k : Nat) (x : Expr),
      (openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j)[k]? = some x →
      Expr.WScoped (nP + nF + l + j) x := by
    intro k x hx
    have hka : k < nP + i + j := by
      rcases Nat.lt_or_ge k (nP + i + j) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hlenA]; omega)] at hx
        exact nomatch hx
    by_cases hk : k < nP + i
    · rw [List.getElem?_append_left (by rw [openFvars_length]; omega)] at hx
      exact openFvars_WScoped (d := nP + nF + l + j) (by omega) k x hx
    · rw [List.getElem?_append_right (by rw [openFvars_length]; omega)] at hx
      exact openFvars_WScoped (d := nP + nF + l + j) (by omega) _ x hx
  have hshift2 := denoteMeta_instSeq_shift (m := m) (ψ := ψ) (p := nP) (o := o)
    (d := nP + nF + l + j) (t := nP + i + j - 1)
    (A := openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j)
    (B := openFvars 0 nP ++ openFvars (nP + o) i ++ openFvars (nP + o + nF + l) j) hef
    (by rw [hlenA, hlenB]) (by omega) hAw2 hcorr2 hshift1
  rw [show nP + nF + l + j + o = nP + o + nF + l + j from by omega,
    show nP + nF + l + j - nP = nF + l + j from by omega] at hshift2
  -- the frame, spelled at the recursor's own variables
  have hcorr3 : ∀ (k : Nat) (a b : Expr),
      (P ++ F.take i ++ openFvars (nP + o + nF + l) j)[k]? = some a →
      (openFvars 0 nP ++ openFvars (nP + o) i ++ openFvars (nP + o + nF + l) j)[k]? = some b →
      ∃ (q : Nat) (ty ty' : Expr), a = Expr.fvar q ty ∧ b = Expr.fvar q ty' := by
    intro k a b ha hb
    have hka : k < nP + i + j := by
      rcases Nat.lt_or_ge k (nP + i + j) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hlenTgt]; omega)] at ha
        exact nomatch ha
    by_cases hk : k < nP + i
    · rw [List.getElem?_append_left (by rw [hlenPF]; omega)] at ha
      rw [List.getElem?_append_left
        (by rw [List.length_append, openFvars_length, openFvars_length]; omega)] at hb
      by_cases hk2 : k < nP
      · rw [List.getElem?_append_left (by rw [hP]; omega)] at ha
        rw [List.getElem?_append_left (by rw [openFvars_length]; omega), openFvars_getElem? hk2,
          Nat.zero_add] at hb
        obtain ⟨ty, rfl⟩ := hidxP k a ha
        obtain rfl := (Option.some.inj hb).symm
        exact ⟨k, ty, _, rfl, rfl⟩
      · rw [List.getElem?_append_right (by rw [hP]; omega), hP] at ha
        rw [List.getElem?_append_right (by rw [openFvars_length]; omega), openFvars_length,
          openFvars_getElem? (show k - nP < i from by omega)] at hb
        have ha' : F[k - nP]? = some a := by
          rw [← ha, List.getElem?_take, if_pos (show k - nP < i from by omega)]
        obtain ⟨ty, rfl⟩ := hidxF (k - nP) a ha'
        obtain rfl := (Option.some.inj hb).symm
        exact ⟨nP + o + (k - nP), ty, Expr.sort Level.zero, rfl, rfl⟩
    · rw [List.getElem?_append_right (by rw [hlenPF]; omega), hlenPF,
        openFvars_getElem? (show k - (nP + i) < j from by omega)] at ha
      obtain rfl := (Option.some.inj ha).symm
      rw [List.getElem?_append_right
          (by rw [List.length_append, openFvars_length, openFvars_length]; omega),
        List.length_append, openFvars_length, openFvars_length,
        openFvars_getElem? (show k - (nP + i) < j from by omega)] at hb
      obtain rfl := (Option.some.inj hb).symm
      exact ⟨_, _, _, rfl, rfl⟩
  rw [instSeq_structIdxAtM P X F I (openFvars (nP + o + nF + l) j) hP hX hF hI
    (openFvars_length _ _) hclP hclF hi heb,
    denoteMeta_instSeq_congr (L := P ++ F.take i ++ openFvars (nP + o + nF + l) j)
      (L' := openFvars 0 nP ++ openFvars (nP + o) i ++ openFvars (nP + o + nF + l) j)
      (by rw [hlenTgt, hlenB]) hcorr3]
  exact hshift2

set_option maxHeartbeats 1600000 in
/-- **A recursive field's index expressions at the recursor's frame**,
spine-wise. -/
theorem denoteMetaSpine_ihIdx {m : EnvModel V env} {ψ : Name → Nat}
    {nP nF o l i j : Nat} {cty : Expr} {Eis : List AnnotTerm}
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF)
    (hj : j = (ConLeche.structFieldTeleOf cty nP nF i).length)
    {S : List Expr} (hS : S.length = nP + i)
    (hidxS : ∀ (k : Nat) (x : Expr), S[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (heis : DenoteMetaSpine m.acval env ψ (nP + i + j)
      ((ConLeche.structFieldIdxOf cty nP nF i).map
        (Expr.instSeq (S ++ openFvars (nP + i) j) (nP + i + j - 1))) Eis)
    {P X F I : List Expr}
    (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF) (hI : I.length = l)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty) :
    DenoteMetaSpine m.acval env ψ (nP + o + nF + l + j)
      ((ConLeche.structFieldIdxOf cty nP nF i).map
        (fun e => Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l) j)
          (nP + o + nF + l + j - 1) (ConLeche.structIdxAt nF o i l j e)))
      (Eis.map (ihIdxAtM nF o i l j)) := by
  refine DenoteMetaSpine.map_map heis ?_
  intro e E he hE
  obtain ⟨hef, heb⟩ := (structFieldTele_props hCf hCb hstripC hi).2 e he
  exact denoteMeta_ihIdxAtM hef (by rw [hj]; exact heb) (Nat.le_of_lt hi) hS hidxS hP hX hF hI
    hidxP hidxF hE

/-! ## The recursor's frame, variable by variable -/

/-- The frame `p⃗ x⃗ f⃗ ih⃗` is opened at the variables `0 … ` in order. -/
theorem frameIdx {P X F I : List Expr} {nP o nF : Nat}
    (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxX : ∀ (k : Nat) (x : Expr), X[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty)
    (hidxI : ∀ (k : Nat) (x : Expr), I[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + nF + k) ty) :
    ∀ (k : Nat) (x : Expr), (P ++ X ++ F ++ I)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
  intro k x hx
  by_cases h1 : k < nP + o + nF
  · rw [List.getElem?_append_left (by simp [hP, hX, hF]; omega)] at hx
    by_cases h2 : k < nP + o
    · rw [List.getElem?_append_left (by simp [hP, hX]; omega)] at hx
      by_cases h3 : k < nP
      · rw [List.getElem?_append_left (by rw [hP]; omega)] at hx
        exact hidxP k x hx
      · rw [List.getElem?_append_right (by rw [hP]; omega), hP] at hx
        obtain ⟨ty, hy⟩ := hidxX (k - nP) x hx
        exact ⟨ty, by rw [hy]; congr 1; omega⟩
    · rw [List.getElem?_append_right (by simp [hP, hX]; omega)] at hx
      simp only [List.length_append, hP, hX] at hx
      obtain ⟨ty, hy⟩ := hidxF (k - (nP + o)) x hx
      exact ⟨ty, by rw [hy]; congr 1; omega⟩
  · rw [List.getElem?_append_right (by simp [hP, hX, hF]; omega)] at hx
    simp only [List.length_append, hP, hX, hF] at hx
    obtain ⟨ty, hy⟩ := hidxI (k - (nP + o + nF)) x hx
    exact ⟨ty, by rw [hy]; congr 1; omega⟩

/-! ## Telescopes, read binderwise -/

/-- `structTeleAt` keeps the telescope's length. -/
theorem structTeleAt_length (nF o i l : Nat) (pw : PropWhen) (tele : List (Expr × BinderMeta)) :
    (ConLeche.structTeleAt nF o i l pw tele).length = tele.length := by
  unfold ConLeche.structTeleAt
  rw [List.length_map, List.length_range]

/-- `structTeleAt`'s binder `k`: the telescope's own, its domain moved
to the `ih` binder's frame, its datum the elimination regime's (task
#202 A2). -/
theorem structTeleAt_getElem? {nF o i l k : Nat} {pw : PropWhen} {tele : List (Expr × BinderMeta)}
    {b : Expr × BinderMeta} (hb : tele[k]? = some b) :
    (ConLeche.structTeleAt nF o i l pw tele)[k]?
      = some (ConLeche.structIdxAt nF o i l k b.1, ⟨pw⟩) := by
  have hk : k < tele.length := (List.getElem?_eq_some_iff.mp hb).1
  unfold ConLeche.structTeleAt
  rw [List.getElem?_map,
    List.getElem?_eq_getElem (show k < (List.range tele.length).length from by
      rw [List.length_range]; exact hk), List.getElem_range]
  simp only [Option.map_some, List.getD_eq_getElem?_getD, hb, Option.getD_some]

/-- `ihTeleAtGo`'s entry `q`: the datum's, its expression moved. -/
theorem ihTeleAtGo_getElem? (nF o i l : Nat) :
    ∀ (k : Nat) (tl : List (Nat × Nat × AnnotTerm)) (q : Nat),
      (ihTeleAtGo nF o i l k tl)[q]?
        = (tl[q]?).map fun d => (d.1, d.2.1, ihIdxAtM nF o i l (k + q) d.2.2)
  | _, [], _ => rfl
  | k, d :: tl, 0 => by simp [ihTeleAtGo]
  | k, d :: tl, q + 1 => by
    simp only [ihTeleAtGo, List.getElem?_cons_succ]
    rw [ihTeleAtGo_getElem? nF o i l (k + 1) tl q]
    congr 2
    funext d'
    rw [show k + 1 + q = k + (q + 1) from by omega]

/-! ## Π- and λ-towers over a frame -/

/-- The telescope's openers, re-associated: its first opener is the
frame's last variable. -/
theorem denoteMeta_frame_cons {m : EnvModel V env} {ψ : Name → Nat} {L : List Expr} {D : Nat}
    (hL : L.length = D)
    (hidxL : ∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (ty₀ : Expr) (k t dd : Nat) (e : Expr) :
    denoteMeta m.acval env ψ dd
        (Expr.instSeq (L ++ [Expr.fvar D ty₀] ++ openFvars (D + 1) k) t e)
      = denoteMeta m.acval env ψ dd (Expr.instSeq (L ++ openFvars D (k + 1)) t e) := by
  have hlen1 : (L ++ [Expr.fvar D ty₀]).length = D + 1 := by
    rw [List.length_append, hL, List.length_singleton]
  refine denoteMeta_instSeq_congr ?_ ?_
  · rw [List.length_append, hlen1, openFvars_length, List.length_append, hL, openFvars_length]
    omega
  · intro q a b ha hb
    rw [openFvars_succ] at hb
    by_cases hq : q < D
    · rw [List.getElem?_append_left (by rw [hlen1]; omega),
        List.getElem?_append_left (by rw [hL]; omega)] at ha
      rw [List.getElem?_append_left (by rw [hL]; omega)] at hb
      obtain rfl : a = b := Option.some.inj (ha.symm.trans hb)
      obtain ⟨ty, rfl⟩ := hidxL q a ha
      exact ⟨q, ty, ty, rfl, rfl⟩
    · by_cases hq2 : q = D
      · subst hq2
        rw [List.getElem?_append_left (by rw [hlen1]; omega),
          List.getElem?_append_right (by rw [hL]; omega), hL, Nat.sub_self] at ha
        rw [List.getElem?_append_right (by rw [hL]; omega), hL, Nat.sub_self] at hb
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
        subst ha
        subst hb
        exact ⟨q, ty₀, Expr.sort Level.zero, rfl, rfl⟩
      · rw [List.getElem?_append_right (by rw [hlen1]; omega), hlen1,
          show q - (D + 1) = q - D - 1 from by omega] at ha
        rw [List.getElem?_append_right (by rw [hL]; omega), hL,
          show q - D = (q - D - 1) + 1 from by omega, List.getElem?_cons_succ] at hb
        obtain rfl : a = b := Option.some.inj (ha.symm.trans hb)
        have hlt : q - D - 1 < k := by
          rcases Nat.lt_or_ge (q - D - 1) k with h | h
          · exact h
          · rw [List.getElem?_eq_none (by rw [openFvars_length]; omega)] at ha
            exact nomatch ha
        rw [openFvars_getElem? hlt] at ha
        obtain rfl := (Option.some.inj ha).symm
        exact ⟨D + 1 + (q - D - 1), Expr.sort Level.zero, Expr.sort Level.zero, rfl, rfl⟩

set_option maxHeartbeats 1600000 in
/-- **A Π-tower over a frame reads to the Π-tower of the readings**:
binder `k` read under the `k` earlier openers, the body under all. -/
theorem denoteMeta_instSeq_mkPisOf {m : EnvModel V env} {ψ : Name → Nat} :
    ∀ (tele : List (Expr × BinderMeta)) (tl : List (Nat × Nat × AnnotTerm)) (body : Expr)
      (B : AnnotTerm) (L : List Expr) (D : Nat), L.length = D →
      (∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty) →
      tl.length = tele.length →
      (∀ (k : Nat) (b : Expr × BinderMeta) (p : Nat × Nat × AnnotTerm),
        tele[k]? = some b → tl[k]? = some p →
        p.1 = 0 ∧ p.2.1 = pwBit ψ b.2.pw ∧
          denoteMeta m.acval env ψ (D + k)
            (Expr.instSeq (L ++ openFvars D k) (D + k - 1) b.1) = some p.2.2) →
      denoteMeta m.acval env ψ (D + tele.length)
          (Expr.instSeq (L ++ openFvars D tele.length) (D + tele.length - 1) body) = some B →
      denoteMeta m.acval env ψ D (Expr.instSeq L (D - 1) (Expr.mkPisOf tele body))
        = some (mkPisAV tl B)
  | [], tl, body, B, L, D, _, _, hlen, _, hbody => by
    obtain rfl : tl = [] := List.eq_nil_of_length_eq_zero hlen
    rw [List.length_nil, Nat.add_zero, openFvars_zero, List.append_nil] at hbody
    exact hbody
  | (ty, mt) :: tele, tl, body, B, L, D, hL, hidxL, hlen, hbinders, hbody => by
    cases tl with
    | nil => simp at hlen
    | cons p tl' =>
    obtain ⟨hp1, hp2, hpty⟩ := hbinders 0 (ty, mt) p rfl rfl
    rw [Nat.add_zero, openFvars_zero, List.append_nil] at hpty
    have hnil : L = [] ∨ D - 1 + 1 = D := by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · left
        exact List.eq_nil_of_length_eq_zero (by omega)
      · right
        omega
    have hlenL' : (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]).length = D + 1 := by
      rw [List.length_append, hL, List.length_singleton]
    have hidxL' : ∀ (k : Nat) (x : Expr),
        (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)])[k]? = some x →
        ∃ ty', x = Expr.fvar k ty' := by
      intro k x hx
      by_cases hk : k < D
      · rw [List.getElem?_append_left (by rw [hL]; omega)] at hx
        exact hidxL k x hx
      · rw [List.getElem?_append_right (by rw [hL]; omega), hL] at hx
        have hk0 : k - D = 0 := by
          rcases Nat.lt_or_ge (k - D) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by rw [List.length_singleton]; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨_, by congr 1; omega⟩
    have hIH := denoteMeta_instSeq_mkPisOf tele tl' body B
      (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]) (D + 1) hlenL' hidxL'
      (by simpa using hlen)
      (fun k b p' hb hp => by
        obtain ⟨h1, h2, h3⟩ := hbinders (k + 1) b p' (by simpa using hb) (by simpa using hp)
        refine ⟨h1, h2, ?_⟩
        rw [denoteMeta_frame_cons hL hidxL (Expr.instSeq L (D - 1) ty) k (D + 1 + k - 1)
            (D + 1 + k) b.1,
          show D + 1 + k = D + (k + 1) from by omega]
        exact h3)
      (by
        rw [denoteMeta_frame_cons hL hidxL (Expr.instSeq L (D - 1) ty) tele.length
            (D + 1 + tele.length - 1) (D + 1 + tele.length) body,
          show D + 1 + tele.length = D + (tele.length + 1) from by omega]
        exact hbody)
    rw [Nat.add_sub_cancel] at hIH
    have hY : (Expr.instSeq L D (Expr.mkPisOf tele body)).instantiate1
        (Expr.fvar D (Expr.instSeq L (D - 1) ty)) 0
        = Expr.instSeq (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]) D
            (Expr.mkPisOf tele body) := by
      rw [Expr.instSeq_append L [Expr.fvar D (Expr.instSeq L (D - 1) ty)], hL, Nat.sub_self]
      rfl
    show denoteMeta m.acval env ψ D
      (Expr.instSeq L (D - 1) (.forallE ty (Expr.mkPisOf tele body) mt)) = _
    rw [Expr.instSeq_forallE L (D - 1) _ _ _ (by omega),
      instSeq_idx_congr (sp := L) (t := D - 1 + 1) (t' := D) (Expr.mkPisOf tele body) hnil,
      denoteMeta_forallE, hpty, hY, hIH]
    show some (AnnotTerm.pi 0 (pwBit ψ mt.pw) p.2.2 (mkPisAV tl' B)) = some (mkPisAV (p :: tl') B)
    rw [show mkPisAV (p :: tl') B = AnnotTerm.pi p.1 p.2.1 p.2.2 (mkPisAV tl' B) from rfl, hp1, hp2]

set_option maxHeartbeats 1600000 in
/-- **A λ-tower over a frame reads to the λ-tower of the readings.** -/
theorem denoteMeta_instSeq_mkLamsOf {m : EnvModel V env} {ψ : Name → Nat} :
    ∀ (tele : List (Expr × BinderMeta)) (tl : List (Nat × AnnotTerm)) (body : Expr)
      (B : AnnotTerm) (L : List Expr) (D : Nat), L.length = D →
      (∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty) →
      tl.length = tele.length →
      (∀ (k : Nat) (b : Expr × BinderMeta) (p : Nat × AnnotTerm),
        tele[k]? = some b → tl[k]? = some p →
        p.1 = pwBit ψ b.2.pw ∧
          denoteMeta m.acval env ψ (D + k)
            (Expr.instSeq (L ++ openFvars D k) (D + k - 1) b.1) = some p.2) →
      denoteMeta m.acval env ψ (D + tele.length)
          (Expr.instSeq (L ++ openFvars D tele.length) (D + tele.length - 1) body) = some B →
      denoteMeta m.acval env ψ D (Expr.instSeq L (D - 1) (Expr.mkLamsOf tele body))
        = some (mkLamsAV tl B)
  | [], tl, body, B, L, D, _, _, hlen, _, hbody => by
    obtain rfl : tl = [] := List.eq_nil_of_length_eq_zero hlen
    rw [List.length_nil, Nat.add_zero, openFvars_zero, List.append_nil] at hbody
    exact hbody
  | (ty, mt) :: tele, tl, body, B, L, D, hL, hidxL, hlen, hbinders, hbody => by
    cases tl with
    | nil => simp at hlen
    | cons p tl' =>
    obtain ⟨hp1, hpty⟩ := hbinders 0 (ty, mt) p rfl rfl
    rw [Nat.add_zero, openFvars_zero, List.append_nil] at hpty
    have hnil : L = [] ∨ D - 1 + 1 = D := by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · left
        exact List.eq_nil_of_length_eq_zero (by omega)
      · right
        omega
    have hlenL' : (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]).length = D + 1 := by
      rw [List.length_append, hL, List.length_singleton]
    have hidxL' : ∀ (k : Nat) (x : Expr),
        (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)])[k]? = some x →
        ∃ ty', x = Expr.fvar k ty' := by
      intro k x hx
      by_cases hk : k < D
      · rw [List.getElem?_append_left (by rw [hL]; omega)] at hx
        exact hidxL k x hx
      · rw [List.getElem?_append_right (by rw [hL]; omega), hL] at hx
        have hk0 : k - D = 0 := by
          rcases Nat.lt_or_ge (k - D) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by rw [List.length_singleton]; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨_, by congr 1; omega⟩
    have hIH := denoteMeta_instSeq_mkLamsOf tele tl' body B
      (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]) (D + 1) hlenL' hidxL'
      (by simpa using hlen)
      (fun k b p' hb hp => by
        obtain ⟨h1, h3⟩ := hbinders (k + 1) b p' (by simpa using hb) (by simpa using hp)
        refine ⟨h1, ?_⟩
        rw [denoteMeta_frame_cons hL hidxL (Expr.instSeq L (D - 1) ty) k (D + 1 + k - 1)
            (D + 1 + k) b.1,
          show D + 1 + k = D + (k + 1) from by omega]
        exact h3)
      (by
        rw [denoteMeta_frame_cons hL hidxL (Expr.instSeq L (D - 1) ty) tele.length
            (D + 1 + tele.length - 1) (D + 1 + tele.length) body,
          show D + 1 + tele.length = D + (tele.length + 1) from by omega]
        exact hbody)
    rw [Nat.add_sub_cancel] at hIH
    have hY : (Expr.instSeq L D (Expr.mkLamsOf tele body)).instantiate1
        (Expr.fvar D (Expr.instSeq L (D - 1) ty)) 0
        = Expr.instSeq (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]) D
            (Expr.mkLamsOf tele body) := by
      rw [Expr.instSeq_append L [Expr.fvar D (Expr.instSeq L (D - 1) ty)], hL, Nat.sub_self]
      rfl
    show denoteMeta m.acval env ψ D
      (Expr.instSeq L (D - 1) (.lam ty (Expr.mkLamsOf tele body) mt)) = _
    rw [ConLeche.instSeq_lam L (D - 1) _ _ _ (by omega),
      instSeq_idx_congr (sp := L) (t := D - 1 + 1) (t' := D) (Expr.mkLamsOf tele body) hnil,
      denoteMeta_lam, hpty, hY, hIH]
    show some (AnnotTerm.lam (pwBit ψ mt.pw) p.2 (mkLamsAV tl' B)) = some (mkLamsAV (p :: tl') B)
    rw [show mkLamsAV (p :: tl') B = AnnotTerm.lam p.1 p.2 (mkLamsAV tl' B) from rfl, hp1]

set_option maxHeartbeats 1600000 in
/-- **A Π-tower over a frame, read**: the reading is the Π-tower of
the binders' readings over the body's. -/
theorem denoteMeta_instSeq_mkPisOf_inv {m : EnvModel V env} {ψ : Name → Nat} :
    ∀ (tele : List (Expr × BinderMeta)) (body : Expr) (L : List Expr) (D : Nat)
      (ea : AnnotTerm), L.length = D →
      (∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty) →
      denoteMeta m.acval env ψ D (Expr.instSeq L (D - 1) (Expr.mkPisOf tele body)) = some ea →
      ∃ (tl : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
        ea = mkPisAV tl B ∧ tl.length = tele.length ∧
        (∀ (k : Nat) (b : Expr × BinderMeta) (p : Nat × Nat × AnnotTerm),
          tele[k]? = some b → tl[k]? = some p →
          p.1 = 0 ∧ p.2.1 = pwBit ψ b.2.pw ∧
            denoteMeta m.acval env ψ (D + k)
              (Expr.instSeq (L ++ openFvars D k) (D + k - 1) b.1) = some p.2.2) ∧
        denoteMeta m.acval env ψ (D + tele.length)
          (Expr.instSeq (L ++ openFvars D tele.length) (D + tele.length - 1) body) = some B
  | [], body, L, D, ea, _, _, hread => by
    refine ⟨[], ea, rfl, rfl, ?_, ?_⟩
    · intro k b p hb _
      exact nomatch hb
    · rw [List.length_nil, Nat.add_zero, openFvars_zero, List.append_nil]
      exact hread
  | (ty, mt) :: tele, body, L, D, ea, hL, hidxL, hread => by
    have hnil : L = [] ∨ D - 1 + 1 = D := by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · left
        exact List.eq_nil_of_length_eq_zero (by omega)
      · right
        omega
    rw [show Expr.mkPisOf ((ty, mt) :: tele) body
        = .forallE ty (Expr.mkPisOf tele body) mt from rfl,
      Expr.instSeq_forallE L (D - 1) _ _ _ (by omega),
      instSeq_idx_congr (sp := L) (t := D - 1 + 1) (t' := D) (Expr.mkPisOf tele body) hnil]
      at hread
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hread
    have hlenL' : (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]).length = D + 1 := by
      rw [List.length_append, hL, List.length_singleton]
    have hidxL' : ∀ (k : Nat) (x : Expr),
        (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)])[k]? = some x →
        ∃ ty', x = Expr.fvar k ty' := by
      intro k x hx
      by_cases hk : k < D
      · rw [List.getElem?_append_left (by rw [hL]; omega)] at hx
        exact hidxL k x hx
      · rw [List.getElem?_append_right (by rw [hL]; omega), hL] at hx
        have hk0 : k - D = 0 := by
          rcases Nat.lt_or_ge (k - D) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by rw [List.length_singleton]; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨_, by congr 1; omega⟩
    have hY : (Expr.instSeq L D (Expr.mkPisOf tele body)).instantiate1
        (Expr.fvar D (Expr.instSeq L (D - 1) ty)) 0
        = Expr.instSeq (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]) D
            (Expr.mkPisOf tele body) := by
      rw [Expr.instSeq_append L [Expr.fvar D (Expr.instSeq L (D - 1) ty)], hL, Nat.sub_self]
      rfl
    rw [hY] at hba
    obtain ⟨tl, B, rfl, hlen, hbinders, hbody⟩ :=
      denoteMeta_instSeq_mkPisOf_inv tele body _ (D + 1) ba hlenL' hidxL' hba
    refine ⟨(0, pwBit ψ mt.pw, ta) :: tl, B, rfl, by simp [hlen], ?_, ?_⟩
    · intro k b p hb hp
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hp
        subst hb
        subst hp
        refine ⟨rfl, rfl, ?_⟩
        rw [Nat.add_zero, openFvars_zero, List.append_nil]
        exact hta
      | succ k =>
        simp only [List.getElem?_cons_succ] at hb hp
        obtain ⟨h1, h2, h3⟩ := hbinders k b p hb hp
        refine ⟨h1, h2, ?_⟩
        rw [show D + (k + 1) = D + 1 + k from by omega,
          ← denoteMeta_frame_cons hL hidxL (Expr.instSeq L (D - 1) ty) k (D + 1 + k - 1)
            (D + 1 + k) b.1]
        exact h3
    · rw [List.length_cons, show D + (tele.length + 1) = D + 1 + tele.length from by omega,
        ← denoteMeta_frame_cons hL hidxL (Expr.instSeq L (D - 1) ty) tele.length
          (D + 1 + tele.length - 1) (D + 1 + tele.length) body]
      exact hbody

/-! ## The `ih` binders -/

/-- **What a recursive field contributes to the readings**: its own
telescope's binders, read at the constructor's frame (the parameters,
the `i` earlier fields, the telescope's own openers), are the datum's
entries — bits included — and its domain's index expressions, read
under the whole telescope, are the field's readings (task #202; a
finitary field: the telescope is empty and this is the old
`eisRead`). -/
@[expose] def FieldReadAt {env : Env} (m : EnvModel V env) (ψ : Name → Nat) (nP nF i : Nat) (cty : Expr)
    (fvs0 : List Expr) (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) : Prop :=
  tl.length = (ConLeche.structFieldTeleOf cty nP nF i).length ∧
  (∀ (k : Nat) (b : Expr × BinderMeta) (p : Nat × Nat × AnnotTerm),
    (ConLeche.structFieldTeleOf cty nP nF i)[k]? = some b → tl[k]? = some p →
    p.1 = 0 ∧ p.2.1 = pwBit ψ b.2.pw ∧
      denoteMeta m.acval env ψ (nP + i + k)
          (Expr.instSeq (fvs0.take (nP + i) ++ openFvars (nP + i) k) (nP + i + k - 1) b.1)
        = some p.2.2) ∧
  DenoteMetaSpine m.acval env ψ (nP + i + tl.length)
    ((ConLeche.structFieldIdxOf cty nP nF i).map
      (Expr.instSeq (fvs0.take (nP + i) ++ openFvars (nP + i) tl.length)
        (nP + i + tl.length - 1))) Eis

set_option maxHeartbeats 1600000 in
/-- **A recursive field's readings, off the constructor's reading
premise.**  The field's domain reads to its entry (`fieldRead`), which
is the Π-tower over the datum's telescope of the family at the
parameters and the field's index readings (`recEntry`); peeling the
tower at the raw binder's own `∀`-binders (`teleLen`) gives the
telescope binderwise, and inverting the body's application spine
(`fieldArity`) the index expressions. -/
theorem fieldReadAt_of {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {c : Name × Nat × Expr × List Nat} {cd : CtorDatumR}
    (hc : CtorReadR m ψ T lps nP nIdx c cd) {i : Nat} (hi : i ∈ c.2.2.2)
    {fvs0 : List Expr} {crest : Expr}
    (hop0 : openPisAtFvars (nP + c.2.1) c.2.2.1 0 = some (fvs0, crest)) :
    FieldReadAt m ψ nP c.2.1 i c.2.2.1 fvs0 (cd.2.2.2.2.2.2.getD i [])
      (cd.2.2.2.2.2.1.getD i []) := by
  obtain ⟨cbs, es, hst, hlenes⟩ := hc.resid
  have hiF : i < c.2.1 := hc.recIdxBnd i hi
  obtain ⟨hlen0, hidx0, hcl0, hw0⟩ := opening_vars hop0 hc.hasFvar
  obtain ⟨x, hx⟩ : ∃ x, fvs0[nP + i]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlen0]; omega)⟩
  obtain ⟨b, hb⟩ : ∃ b, cbs[nP + i]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by rw [ConLeche.Expr.stripPis_length _ hst]; omega)⟩
  have hbd : cbs.getD (nP + i) default = b := by
    rw [List.getD_eq_getElem?_getD, hb]
    rfl
  have htele : ConLeche.structFieldTeleOf c.2.2.1 nP c.2.1 i = (b.1.piBinders).1 := by
    unfold ConLeche.structFieldTeleOf
    rw [hst]
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
  have hidxOf : ConLeche.structFieldIdxOf c.2.2.1 nP c.2.1 i
      = (b.1.piBinders).2.getAppArgs.drop nP := by
    unfold ConLeche.structFieldIdxOf
    rw [hst]
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
  have hS : (fvs0.take (nP + i)).length = nP + i := by
    rw [List.length_take, hlen0]
    omega
  have hidxS : ∀ (k : Nat) (y : Expr), (fvs0.take (nP + i))[k]? = some y →
      ∃ ty, y = Expr.fvar k ty := by
    intro k y hy
    have hk : k < nP + i := by
      rcases Nat.lt_or_ge k (nP + i) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hS]; omega)] at hy
        exact nomatch hy
    rw [List.getElem?_take, if_pos hk] at hy
    exact hidx0 k y hy
  have hread := hc.fieldRead i hi fvs0 crest hop0 x hx
  rw [hc.recEntry i hi, openPisAtFvars_fvarTypeD (nP + c.2.1) hop0 hst (nP + i) b x hb hx,
    ← Expr.mkPisOf_piBinders b.1] at hread
  obtain ⟨tl₀, B, heq, hlen₀, hbind, hbody⟩ :=
    denoteMeta_instSeq_mkPisOf_inv (b.1.piBinders).1 (b.1.piBinders).2 (fvs0.take (nP + i))
      (nP + i) _ hS hidxS hread
  have hlenTl : (cd.2.2.2.2.2.2.getD i []).length = (b.1.piBinders).1.length := by
    rw [← htele]
    exact (hc.teleLen i hi).symm
  obtain ⟨rfl, rfl⟩ := mkPisAV_inj (by rw [hlenTl, hlen₀]) heq
  refine ⟨by rw [htele, hlenTl], ?_, ?_⟩
  · intro k b' p hb' hp
    rw [htele] at hb'
    exact hbind k b' p hb' hp
  · rw [← hlenTl] at hbody
    have harity := hc.fieldArity i hi cbs _ hst
    rw [hbd] at harity
    rw [← Expr.mkAppN_getApp (b.1.piBinders).2, Expr.instSeq_mkAppN] at hbody
    obtain ⟨fa, vs, hfa, hsp, hval⟩ := denoteMeta_mkAppN_inv hbody
    have hlenvs : vs.length = nP + nIdx := by
      rw [← hsp.length, List.length_map]
      exact harity
    have hlenPE : (paramBvarsAt nP (nP + i + (cd.2.2.2.2.2.2.getD i []).length)
        ++ cd.2.2.2.2.2.1.getD i []).length = nP + nIdx := by
      rw [List.length_append, paramBvarsAt, List.length_map, List.length_range,
        hc.eisLen i hi]
    obtain ⟨-, hvs⟩ := mkAppN_inj_args hval (by rw [hlenPE, hlenvs])
    rw [← List.take_append_drop nP ((b.1.piBinders).2.getAppArgs), List.map_append] at hsp
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.append_inv hsp
    have hlen1 : vs₁.length = nP := by
      rw [← hsp₁.length, List.length_map, List.length_take, harity]
      omega
    obtain ⟨-, rfl⟩ := List.append_inj hvs
      (by rw [hlen1, paramBvarsAt, List.length_map, List.length_range])
    rw [hidxOf]
    exact hsp₂

set_option maxHeartbeats 3200000 in
/-- **The `ih` binder's domain** for recursive field `i` at ih
position `l`, instantiated at the recursor's frame, reads to
`ihDomAV`: the field's telescope moved binderwise (`denoteMeta_ihIdxAtM`
at each binder), then the motive at the field's index readings and the
field applied to the telescope's own variables. -/
theorem denoteMeta_ihDom {m : EnvModel V env} {ψ : Name → Nat} {nP nF o l i : Nat} {pw : PropWhen}
    {cty : Expr}
    {fvs0 : List Expr} {crest : Expr} {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF) (ho : 0 < o)
    (hfr : FieldReadAt m ψ nP nF i cty fvs0 tl Eis)
    {P X F I : List Expr} (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF)
    (hI : I.length = l)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxX : ∀ (k : Nat) (x : Expr), X[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty)
    (hidxI : ∀ (k : Nat) (x : Expr), I[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + nF + k) ty) :
    denoteMeta m.acval env ψ (nP + o + nF + l)
        (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1)
          (Expr.mkPisOf (ConLeche.structTeleAt nF o i l pw (ConLeche.structFieldTeleOf cty nP nF i))
            (Expr.mkAppN (.bvar (nF + o - 1 + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
              ((ConLeche.structFieldIdxOf cty nP nF i).map
                  (ConLeche.structIdxAt nF o i l (ConLeche.structFieldTeleOf cty nP nF i).length) ++
                [Expr.mkAppN (.bvar (nF - 1 - i + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
                  (ConLeche.structTeleVars (ConLeche.structFieldTeleOf cty nP nF i).length)]))))
      = some (ihDomAV nF o i l (rebit (pwBit ψ pw) tl) Eis) := by
  obtain ⟨hlenTl, hbind, hspSrc⟩ := hfr
  obtain ⟨hlen0, hidx0, hcl0, hw0⟩ := opening_vars hop0 hCf
  have hS : (fvs0.take (nP + i)).length = nP + i := by
    rw [List.length_take, hlen0]
    omega
  have hidxS : ∀ (k : Nat) (x : Expr), (fvs0.take (nP + i))[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    have hk : k < nP + i := by
      rcases Nat.lt_or_ge k (nP + i) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hS]; omega)] at hx
        exact nomatch hx
    rw [List.getElem?_take, if_pos hk] at hx
    exact hidx0 k x hx
  have hprops := structFieldTele_props hCf hCb hstripC hi
  have hlenL : (P ++ X ++ F ++ I).length = nP + o + nF + l := by
    rw [List.length_append, List.length_append, List.length_append, hP, hX, hF, hI]
  have hLidx := frameIdx hP hX hF hidxP hidxX hidxF hidxI
  -- the frame under the telescope's openers
  have hlenLA : (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
      (ConLeche.structFieldTeleOf cty nP nF i).length).length
      = nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length := by
    rw [List.length_append, hlenL, openFvars_length]
  have hidxLA : ∀ (k : Nat) (x : Expr),
      (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
        (ConLeche.structFieldTeleOf cty nP nF i).length)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    by_cases hk : k < nP + o + nF + l
    · rw [List.getElem?_append_left (by rw [hlenL]; omega)] at hx
      exact hLidx k x hx
    · rw [List.getElem?_append_right (by rw [hlenL]; omega), hlenL] at hx
      have hlt : k - (nP + o + nF + l) < (ConLeche.structFieldTeleOf cty nP nF i).length := by
        rcases Nat.lt_or_ge (k - (nP + o + nF + l))
          (ConLeche.structFieldTeleOf cty nP nF i).length with h | h
        · exact h
        · rw [List.getElem?_eq_none (by rw [openFvars_length]; omega)] at hx
          exact nomatch hx
      rw [openFvars_getElem? hlt] at hx
      obtain rfl := (Option.some.inj hx).symm
      exact ⟨.sort .zero, by congr 1; omega⟩
  have hclLA : ∀ a ∈ P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
      (ConLeche.structFieldTeleOf cty nP nF i).length, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxLA q a hq
    rfl
  have hbvarA : ∀ q : Nat, q < nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length →
      denoteMeta m.acval env ψ (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length)
          (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
              (ConLeche.structFieldTeleOf cty nP nF i).length)
            (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1) (Expr.bvar q))
        = some (AnnotTerm.bvar q) := by
    intro q hq
    have hb := Expr.instSeq_bvar (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
      (ConLeche.structFieldTeleOf cty nP nF i).length)
      (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1) q hclLA (by omega)
      (by rw [hlenLA]; omega)
    obtain ⟨ty, hy⟩ := hidxLA _ _ hb
    rw [hy, denoteMeta_fvar,
      show nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1 -
        (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1 - q) = q from by omega]
  unfold ihDomAV
  rw [rebit_length, hlenTl]
  refine denoteMeta_instSeq_mkPisOf _ (ihTeleAtR nF o i l (rebit (pwBit ψ pw) tl)) _ _ (P ++ X ++ F ++ I)
    (nP + o + nF + l) hlenL hLidx
    (by rw [ihTeleAtR_length, rebit_length, structTeleAt_length, hlenTl]) ?_ ?_
  · -- the telescope, binderwise
    intro k b p hb hp
    have hk : k < (ConLeche.structFieldTeleOf cty nP nF i).length := by
      rw [← structTeleAt_length nF o i l pw (ConLeche.structFieldTeleOf cty nP nF i)]
      exact (List.getElem?_eq_some_iff.mp hb).1
    obtain ⟨b₀, hb₀⟩ : ∃ b₀, (ConLeche.structFieldTeleOf cty nP nF i)[k]? = some b₀ :=
      ⟨_, List.getElem?_eq_getElem hk⟩
    rw [structTeleAt_getElem? (pw := pw) hb₀] at hb
    obtain rfl := (Option.some.inj hb).symm
    obtain ⟨d, hd⟩ : ∃ d, tl[k]? = some d := ⟨_, List.getElem?_eq_getElem (by rw [hlenTl]; exact hk)⟩
    rw [ihTeleAtR, ihTeleAtGo_getElem? nF o i l 0 _ k, rebit, List.getElem?_map, hd] at hp
    simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hp
    obtain rfl := hp.symm
    obtain ⟨h1, -, h3⟩ := hbind k b₀ d hb₀ hd
    obtain ⟨hef, heb⟩ := hprops.1 k b₀ hb₀
    exact ⟨h1, rfl, denoteMeta_ihIdxAtM hef heb (Nat.le_of_lt hi) hS hidxS hP hX hF hI hidxP hidxF h3⟩
  · -- the motive at the field's readings and the field at its telescope
    rw [structTeleAt_length nF o i l pw (ConLeche.structFieldTeleOf cty nP nF i)]
    have hspI := denoteMetaSpine_ihIdx (m := m) (ψ := ψ) (o := o) (l := l) hCf hCb hstripC hi rfl
      hS hidxS (by rw [hlenTl] at hspSrc; exact hspSrc) hP hX hF hI hidxP hidxF
    have hfieldApp : denoteMeta m.acval env ψ
        (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length)
          (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
              (ConLeche.structFieldTeleOf cty nP nF i).length)
            (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1)
            (Expr.mkAppN (.bvar (nF - 1 - i + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
              (ConLeche.structTeleVars (ConLeche.structFieldTeleOf cty nP nF i).length)))
        = some (AnnotTerm.mkAppN
            (.bvar (nF - 1 - i + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
            (teleVarsAV (ConLeche.structFieldTeleOf cty nP nF i).length)) := by
      rw [Expr.instSeq_mkAppN]
      refine denoteMeta_mkAppN ?_ (hbvarA _ (by omega))
      unfold ConLeche.structTeleVars teleVarsAV
      rw [List.map_map]
      simp only [Function.comp_def]
      exact DenoteMetaSpine.of_map (List.range (ConLeche.structFieldTeleOf cty nP nF i).length)
        (fun k hk => hbvarA _ (by rw [List.mem_range] at hk; omega))
    rw [Expr.instSeq_mkAppN, List.map_append, List.map_map, List.map_cons, List.map_nil]
    simp only [Function.comp_def]
    rw [denoteMeta_mkAppN (hspI.append (.cons hfieldApp .nil)) (hbvarA _ (by omega))]

set_option maxHeartbeats 1600000 in
/-- **The `ih` binders' `∀`-tower** reads to `ihPisAV`, the body read
under all of them. -/
theorem denoteMeta_ihPis {m : EnvModel V env} {ψ : Name → Nat} {nP nF o : Nat} {pw : PropWhen}
    {cty : Expr} {Eiss : List (List AnnotTerm)} {tls : List (List (Nat × Nat × AnnotTerm))}
    {fvs0 : List Expr} {crest : Expr}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (ho : 0 < o)
    {P X F : List Expr} (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxX : ∀ (k : Nat) (x : Expr), X[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty) :
    ∀ (is : List Nat) (l : Nat) (body : Expr) (I : List Expr),
      (∀ i ∈ is, i < nF) →
      (∀ i ∈ is, FieldReadAt m ψ nP nF i cty fvs0 (tls.getD i []) (Eiss.getD i [])) →
      I.length = l →
      (∀ (k : Nat) (x : Expr), I[k]? = some x →
        ∃ ty, x = Expr.fvar (nP + o + nF + k) ty) →
      ∃ I' : List Expr, I'.length = l + is.length ∧
        (∀ (k : Nat) (x : Expr), I'[k]? = some x →
          ∃ ty, x = Expr.fvar (nP + o + nF + k) ty) ∧
        denoteMeta m.acval env ψ (nP + o + nF + l)
            (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1)
              (ConLeche.structIhPis nF o pw (ConLeche.structFieldTeleOf cty nP nF)
                (ConLeche.structFieldIdxOf cty nP nF) is l body))
          = (denoteMeta m.acval env ψ (nP + o + nF + l + is.length)
              (Expr.instSeq (P ++ X ++ F ++ I') (nP + o + nF + l + is.length - 1) body)).map
              (ihPisAV nF o (pwBit ψ pw) tls Eiss is l) := by
  intro is
  induction is with
  | nil =>
    intro l body I _ _ hlenI hidxI
    refine ⟨I, by simp [hlenI], hidxI, ?_⟩
    simp only [ConLeche.structIhPis, List.length_nil, Nat.add_zero, ihPisAV]
    cases denoteMeta m.acval env ψ (nP + o + nF + l)
      (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1) body) <;> rfl
  | cons i is ihs =>
    intro l body I hlt heis hlenI hidxI
    have hiF : i < nF := hlt i List.mem_cons_self
    have hlenL : (P ++ X ++ F ++ I).length = nP + o + nF + l := by
      rw [List.length_append, List.length_append, List.length_append, hP, hX, hF, hlenI]
    have hdom := denoteMeta_ihDom (pw := pw) hop0 hCf hCb hstripC hiF ho (heis i List.mem_cons_self) hP hX hF
      hlenI hidxP hidxX hidxF hidxI
    have hann : ∀ (ann rest : Expr) (dd : Nat),
        denoteMeta m.acval env ψ dd
            (rest.instantiate1
              (Expr.fvar (nP + o + nF + l) ann) 0)
          = denoteMeta m.acval env ψ dd
              (rest.instantiate1
                (Expr.fvar (nP + o + nF + l) (.sort .zero)) 0) := by
      intro ann rest dd
      exact denoteMeta_erasedEq (Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl rest)
        (show Expr.ErasedEq (Expr.fvar (nP + o + nF + l) ann)
          (Expr.fvar (nP + o + nF + l) (.sort .zero)) from rfl)) dd
    simp only [ConLeche.structIhPis]
    rw [Expr.instSeq_forallE (P ++ X ++ F ++ I) (nP + o + nF + l - 1) _ _ _
        (by rw [hlenL]; omega),
      show nP + o + nF + l - 1 + 1 = nP + o + nF + l from by omega,
      denoteMeta_forallE, hdom, hann]
    generalize hfv : Expr.fvar (nP + o + nF + l) (Expr.sort Level.zero) = ifv
    have hY : ∀ rest : Expr,
        (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l) rest).instantiate1 ifv 0
          = Expr.instSeq (P ++ X ++ F ++ (I ++ [ifv])) (nP + o + nF + l) rest := by
      intro rest
      rw [show P ++ X ++ F ++ (I ++ [ifv]) = (P ++ X ++ F ++ I) ++ [ifv] from by simp,
        Expr.instSeq_append (P ++ X ++ F ++ I) [ifv], hlenL, Nat.sub_self]
      rfl
    have hidxI' : ∀ (k : Nat) (x : Expr), (I ++ [ifv])[k]? = some x →
        ∃ ty, x = Expr.fvar (nP + o + nF + k) ty := by
      intro k x hx
      by_cases hk : k < I.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxI k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - I.length = 0 := by
          rcases Nat.lt_or_ge (k - I.length) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by simp; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        have hkl : k = l := by omega
        subst hkl
        exact ⟨_, hfv.symm⟩
    obtain ⟨I', hlenI'', hidxI'', hread⟩ := ihs (l + 1) body (I ++ [ifv])
      (fun i' hi' => hlt i' (List.mem_cons_of_mem _ hi'))
      (fun i' hi' => heis i' (List.mem_cons_of_mem _ hi'))
      (by simp [hlenI]) hidxI'
    refine ⟨I', by rw [hlenI'']; simp; omega, hidxI'', ?_⟩
    rw [show nP + o + nF + (l + 1) - 1 = nP + o + nF + l from by omega,
      show nP + o + nF + (l + 1) + is.length = nP + o + nF + l + (i :: is).length from by
        simp; omega] at hread
    rw [hY, show nP + o + nF + l + 1 = nP + o + nF + (l + 1) from by omega, hread]
    cases denoteMeta m.acval env ψ (nP + o + nF + l + (i :: is).length)
      (Expr.instSeq (P ++ X ++ F ++ I') (nP + o + nF + l + (i :: is).length - 1) body) with
    | none => rfl
    | some v => rfl

/-! ## Reading at a deeper frame -/

/-- A closed expression opened at the variables `0 … L.length - 1`
reads the same at every deeper frame, up to the lift: the variables'
annotations do not matter (`denoteMeta_erasedEq`), so `denoteMeta_lift`
applies at the canonical opening. -/
theorem denoteMeta_instSeq_lift {m : EnvModel V env} {ψ : Name → Nat} {d d' t : Nat}
    {e : Expr} (hef : e.hasFvar = false) {L : List Expr}
    (hidxL : ∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hlenL : L.length ≤ d) (hdd : d ≤ d') {E : AnnotTerm}
    (hE : denoteMeta m.acval env ψ d (Expr.instSeq L t e) = some E) :
    denoteMeta m.acval env ψ d' (Expr.instSeq L t e) = some (E.liftN (d' - d) 0) := by
  obtain ⟨L₀, hlen₀, hidx₀⟩ : ∃ L₀ : List Expr, L₀.length = L.length ∧
      ∀ (k : Nat) (x : Expr), L₀[k]? = some x →
        x = Expr.fvar k (.sort .zero) := by
    refine ⟨(List.range L.length).map fun k => Expr.fvar k (.sort .zero),
      by simp, ?_⟩
    intro k x hx
    rcases Nat.lt_or_ge k L.length with hk | hk
    · rw [List.getElem?_map,
        List.getElem?_eq_getElem (show k < (List.range L.length).length from by simp [hk]),
        List.getElem_range] at hx
      exact (Option.some.inj hx).symm
    · rw [List.getElem?_eq_none (by simp; omega)] at hx
      exact nomatch hx
  have herased : Expr.ErasedEq (Expr.instSeq L t e) (Expr.instSeq L₀ t e) := by
    refine Expr.instSeq_erasedEq_args _ _ t (Expr.ErasedEq.rfl e) ?_ (by rw [hlen₀])
    intro k a₁ a₂ ha₁ ha₂
    obtain ⟨ty, rfl⟩ := hidxL k a₁ ha₁
    rw [hidx₀ k a₂ ha₂]
    exact Eq.refl _
  have hw : Expr.WScoped d (Expr.instSeq L₀ t e) := by
    refine Expr.instSeq_WScoped _ _ ?_ (Expr.WScoped.of_not_hasFvar hef)
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    have hq' : q < L.length := by
      rcases Nat.lt_or_ge q L.length with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hlen₀]; omega)] at hq
        exact nomatch hq
    rw [hidx₀ q x hq]
    simp only [Expr.WScoped]
    exact ⟨by omega, trivial⟩
  rw [denoteMeta_erasedEq herased d] at hE
  rw [denoteMeta_erasedEq herased d', denoteMeta_lift m.acval_closed hw d' hdd, hE, Option.map_some]

/-! ## The recursive minor premise -/

set_option maxHeartbeats 3200000 in
/-- **The recursive minor premise at offset `o`**, instantiated at the
parameters and the `o` extras, reads to `minorAVAtR`: the sum route's
reading (`denoteP_minorAt`) with the `ih` binders (`denoteMeta_ihPis`)
between the fields and the conclusion, which is therefore read one
frame lower and lifted (`denoteMeta_instSeq_lift`). -/
theorem denoteMeta_minorAtR {m : EnvModel V env} {ψ : Name → Nat} {T C : Name} {lps : List Name}
    {ciT ci : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    (hfC : env.find? C = some ci) (hlpsC : ci.toConstantVal.levelParams = lps)
    {nP nF nIdx : Nat} {pw : PropWhen} {cty mty : Expr} {extras : List Expr}
    {recIdx : List Nat} {Eiss : List (List AnnotTerm)}
    {tls : List (List (Nat × Nat × AnnotTerm))}
    (hmin : ConLeche.structMinorTyR C lps nP nF extras.length pw cty recIdx = some mty)
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hresid : ∃ (cbs : List (Expr × BinderMeta)) (es : List Expr),
      cty.stripPis (nP + nF)
        = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (ConLeche.structPsAt nF nP ++ es)) ∧
      es.length = nIdx)
    {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm}
    (hCread : denoteMeta m.acval env ψ 0 cty
      = some (mkPisAV ds (AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es))))
    (hlenD : ds.length = nP + nF) (hlenE : Es.length = nIdx)
    (hrecBnd : ∀ i ∈ recIdx, i < nF)
    (hfr : ∀ i ∈ recIdx, ∀ (fvs : List Expr) (rest : Expr),
      openPisAtFvars (nP + nF) cty 0 = some (fvs, rest) →
      FieldReadAt m ψ nP nF i cty fvs (tls.getD i []) (Eiss.getD i []))
    {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a)
    (ho : 0 < extras.length)
    (hidxE : ∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) :
    denoteMeta m.acval env ψ (nP + extras.length)
        (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty)
      = some (minorAVAtR m C ψ nP nF (pwBit ψ pw) extras.length ds Es recIdx tls Eiss) := by
  obtain ⟨cbs, fbs, crest0, res, hsC, hsF, hrep⟩ := ConLeche.structMinorTyR_unfold hmin
  obtain ⟨cbs', es, hsAll, hlenes⟩ := hresid
  have hstripC : (cty.stripPis (nP + nF)).isSome = true := by rw [hsAll]; rfl
  have hres : res = Expr.mkAppN (.const T (lps.map .param)) (ConLeche.structPsAt nF nP ++ es) := by
    have := (ConLeche.stripPis_append nP hsC hsF).symm.trans hsAll
    exact (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj this).2
  subst hres
  have hargs : ((Expr.mkAppN (.const T (lps.map .param))
      (ConLeche.structPsAt nF nP ++ es)).getAppArgs).drop nP = es := by
    rw [Expr.getAppArgs_mkAppN, show (Expr.const T (lps.map .param)).getAppArgs = [] from rfl,
      List.nil_append, List.drop_left' (by simp [ConLeche.structPsAt])]
  rw [hargs] at hrep
  have hesMem : ∀ e ∈ es, e ∈ (Expr.mkAppN (.const T (lps.map .param))
      (ConLeche.structPsAt nF nP ++ es)).getAppArgs := by
    intro e he
    rw [Expr.getAppArgs_mkAppN]
    exact List.mem_append_right _ (List.mem_append_right _ he)
  have hes : ∀ e ∈ es, e.looseBVarsBounded (nP + nF) = true := by
    intro e he
    have hb := Expr.stripPis_body_bounded (nP + nF) hsAll hCb
    rw [Nat.zero_add] at hb
    exact ConLeche.looseBVarsBounded_getAppArgs hb e (hesMem e he)
  have hesF : ∀ e ∈ es, e.hasFvar = false := fun e he =>
    ConLeche.hasFvar_getAppArgs (ConLeche.stripPis_not_hasFvar (nP + nF) hsAll hCf).2 e (hesMem e he)
  have hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxT q a hq
    rfl
  have hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxE q a hq
    rfl
  have hcb0 : crest0.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsC hCb
    rwa [Nat.zero_add] at this
  have hmin' := ConLeche.replacePisPw_instSeq (tfvs ++ extras) (nP + extras.length - 1)
    (by simp [hlenT]; omega) hrep
  rw [ConLeche.instSeq_minorTele tfvs extras hlenT hclT hcb0] at hmin'
  obtain ⟨hcread, hcw, hcstrip⟩ := ctorResidual hCf hCread hlenD hsC hstripC hlenT hidxT hspW
  obtain ⟨xFvs, xrest, hopX⟩ := openPisAtFvars_of_stripPis_isSome nF (nP + extras.length) hcstrip
  have hcreadO := ctorResidual_read_lift hcread hcw hlenD extras.length
  have hstX : stripPisAV nF (mkPisAV (liftDoms extras.length 0 (ds.drop nP))
      ((AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN extras.length nF))
      = some (liftDoms extras.length 0 (ds.drop nP),
          (AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN extras.length nF) := by
    have := stripPisAV_mkPisAV (liftDoms extras.length 0 (ds.drop nP))
      ((AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN extras.length nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have hminor := denoteMeta_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nF hmin' hopX
    hcreadO hstX
  obtain ⟨hlenX, hidxX, hclX⟩ := opening_vars_at hopX
  obtain ⟨mfv, hhead⟩ : ∃ mfv, extras[0]? = some mfv := ⟨_, List.getElem?_eq_getElem ho⟩
  obtain ⟨tyM, rfl⟩ := hidxE 0 mfv hhead
  rw [Nat.add_zero] at hhead
  -- the frame, as one instantiation sequence
  have hcomb : ∀ Y : Expr,
      Expr.instSeq xFvs (nF - 1)
          (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1 + nF) Y)
        = Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + extras.length + nF - 1) Y := by
    intro Y
    rw [Expr.instSeq_append (tfvs ++ extras) xFvs,
      show (tfvs ++ extras).length = nP + extras.length from by simp [hlenT],
      show nP + extras.length + nF - 1 - (nP + extras.length) = nF - 1 from by omega,
      show nP + extras.length + nF - 1 = nP + extras.length - 1 + nF from by omega]
  rw [hcomb] at hminor
  have hidx3 : ∀ (k : Nat) (x : Expr), (tfvs ++ extras ++ xFvs)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    have h := frameIdx (I := ([] : List Expr)) hlenT rfl hlenX hidxT hidxE hidxX
      (by intro k x hx; simp at hx)
    simpa using h
  have hcl3 : ∀ a ∈ tfvs ++ extras ++ xFvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidx3 q a hq
    rfl
  have hlen3 : (tfvs ++ extras ++ xFvs).length = nP + extras.length + nF := by
    simp [hlenT, hlenX]
    omega
  -- the conclusion, at the field frame
  have hcore : denoteMeta m.acval env ψ (nP + extras.length + nF)
      (Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + extras.length + nF - 1)
        (Expr.mkAppN (.bvar (nF + extras.length - 1))
          (es.map (Expr.liftLooseBVars extras.length nF) ++
            [ConLeche.structCtorSpineAt C lps extras.length nP nF])))
      = some (AnnotTerm.mkAppN (.bvar (nF + extras.length - 1))
          ((Es.map fun E => E.liftN extras.length nF) ++
            [AnnotTerm.mkAppN (m.acval C ψ)
              (paramBvarsAt nP (nP + extras.length + nF) ++ fieldBvars nF)])) := by
    rw [← hcomb, ConLeche.instSeq_minorBodyI_at tfvs extras xFvs hlenT hlenX hclT hclE hclX hhead hes]
    have hspI := denoteMetaSpine_idxArgs_lift hfT hlpsT (o := extras.length) hsF hlenT hlenX hclT
      hidxX hcreadO hlenD hlenE hlenes
    have hspine := denoteMeta_famSpine_at (m := m) (ψ := ψ) hfC hlpsC (o := extras.length) hlenT
      hlenX hidxT hidxX
    rw [denoteMeta_mkAppN (hspI.append (.cons hspine .nil)) (by rw [denoteMeta_fvar]),
      show nP + extras.length + nF - 1 - nP = nF + extras.length - 1 from by omega]
  -- the conclusion is closed and bounded by the field frame
  have hcoreF : (Expr.mkAppN (Expr.bvar (nF + extras.length - 1))
      (es.map (Expr.liftLooseBVars extras.length nF) ++
        [ConLeche.structCtorSpineAt C lps extras.length nP nF])).hasFvar = false := by
    refine ConLeche.hasFvar_mkAppN _ _ rfl ?_
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      rw [ConLeche.hasFvar_liftLooseBVars]
      exact hesF e he
    · rw [List.mem_singleton] at h
      subst h
      refine ConLeche.hasFvar_mkAppN _ _ rfl ?_
      intro y hy
      rcases List.mem_append.mp hy with h1 | h1
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h1
        rfl
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h1
        rfl
  have hcoreB : (Expr.mkAppN (Expr.bvar (nF + extras.length - 1))
      (es.map (Expr.liftLooseBVars extras.length nF) ++
        [ConLeche.structCtorSpineAt C lps extras.length nP nF])).looseBVarsBounded
      (nP + extras.length + nF) = true := by
    refine ConLeche.looseBVarsBounded_mkAppN (by simp [Expr.looseBVarsBounded]; omega) ?_
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      have hb := Expr.looseBVarsBounded_liftLooseBVars extras.length e (b := nP + nF)
        (c := nF) (hes e he)
      exact Expr.looseBVarsBounded_mono (by omega) hb
    · rw [List.mem_singleton] at h
      subst h
      unfold ConLeche.structCtorSpineAt
      refine ConLeche.looseBVarsBounded_mkAppN rfl ?_
      intro y hy
      rcases List.mem_append.mp hy with h1 | h1
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h1
        have : k < nP := by simpa [ConLeche.structPsAt] using hk
        simp [Expr.looseBVarsBounded]
        omega
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h1
        have : k < nF := by simpa using hk
        simp [Expr.looseBVarsBounded]
        omega
  -- the `ih` binders
  obtain ⟨fvs0, crest00, hop0⟩ := openPisAtFvars_of_stripPis_isSome (nP + nF) 0 hstripC
  obtain ⟨I', hlenI', hidxI', hIH⟩ := denoteMeta_ihPis (m := m) (ψ := ψ) (pw := pw) (Eiss := Eiss)
    (tls := tls) hop0 hCf hCb hstripC ho hlenT rfl hlenX hidxT hidxE hidxX recIdx 0
    ((Expr.mkAppN (Expr.bvar (nF + extras.length - 1))
      (es.map (Expr.liftLooseBVars extras.length nF) ++
        [ConLeche.structCtorSpineAt C lps extras.length nP nF])).liftLooseBVars recIdx.length 0)
    [] hrecBnd (fun i hi => hfr i hi fvs0 crest00 hop0) rfl
    (by intro k x hx; simp at hx)
  simp only [List.append_nil, Nat.add_zero, Nat.zero_add] at hIH hlenI'
  -- the conclusion, under the `ih` binders
  have hcoreR : denoteMeta m.acval env ψ (nP + extras.length + nF + recIdx.length)
      (Expr.instSeq (tfvs ++ extras ++ xFvs ++ I') (nP + extras.length + nF + recIdx.length - 1)
        ((Expr.mkAppN (Expr.bvar (nF + extras.length - 1))
          (es.map (Expr.liftLooseBVars extras.length nF) ++
            [ConLeche.structCtorSpineAt C lps extras.length nP nF])).liftLooseBVars
          recIdx.length 0))
      = some ((AnnotTerm.mkAppN (.bvar (nF + extras.length - 1))
          ((Es.map fun E => E.liftN extras.length nF) ++
            [AnnotTerm.mkAppN (m.acval C ψ)
              (paramBvarsAt nP (nP + extras.length + nF) ++ fieldBvars nF)])).liftN
          recIdx.length 0) := by
    have hmid := ConLeche.instSeq_liftLooseBVars_mid (tfvs ++ extras ++ xFvs) I' (c := 0) hcl3
      (by rw [hlen3, Nat.add_zero]; exact hcoreB)
    rw [hlen3, hlenI', Nat.add_zero, Nat.add_zero] at hmid
    rw [hmid]
    have hlift := denoteMeta_instSeq_lift (m := m) (ψ := ψ) hcoreF hidx3 (Nat.le_of_eq hlen3)
      (show nP + extras.length + nF ≤ nP + extras.length + nF + recIdx.length from by omega) hcore
    rw [show nP + extras.length + nF + recIdx.length - (nP + extras.length + nF)
      = recIdx.length from by omega] at hlift
    exact hlift
  rw [hminor, hIH, hcoreR, Option.map_some, Option.map_some]
  rfl

/-! ## The minors' telescopes -/

set_option maxHeartbeats 1600000 in
/-- **The `∀`-telescope of recursive minors** reads to the Π-tower over
`fixMinorsData`, the body read under the motive and all minors. -/
theorem denoteMeta_minorsPisR {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {ciT : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    {nP nIdx : Nat} {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR}
      {body mins : Expr} {extras : List Expr},
      CtorReadsR m ψ T lps nP nIdx ctors cds →
      ConLeche.structMinorsPisR lps nP pw ctors extras.length body = some mins →
      0 < extras.length →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) →
      ∃ extras' : List Expr, extras'.length = ctors.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) ∧
        denoteMeta m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mins)
          = (denoteMeta m.acval env ψ (nP + extras.length + ctors.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + ctors.length - 1) body)).map
              (mkPisAV (fixMinorsData m ψ nP (pwBit ψ pw) cds extras.length))
  | [], cds, body, mins, extras, hcr, hmin, _, hidxE => by
    cases hcr with
    | nil =>
    refine ⟨extras, by simp, hidxE, ?_⟩
    rw [ConLeche.structMinorsPisR_nil hmin]
    simp only [List.length_nil, Nat.add_zero, fixMinorsData]
    cases denoteMeta m.acval env ψ (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) body) <;> rfl
  | (C, nF, cty, recIdx) :: cs, cds, body, mins, extras, hcr, hmin, ho, hidxE => by
    cases hcr with
    | @cons _ cd _ cds' hc hcs =>
    obtain ⟨C', nF', ds, Es, recIdx', Eiss, tls⟩ := cd
    have hC' : C = C' := hc.name.symm
    have hnF' : nF = nF' := hc.nF.symm
    have hrI : recIdx' = recIdx := hc.recIdx
    subst hC' hnF' hrI
    obtain ⟨ci, hfC, hlpsC⟩ := hc.find
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := ConLeche.structMinorsPisR_cons hmin
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    rw [Expr.instSeq_forallE (tfvs ++ extras) (nP + extras.length - 1) _ _ _ (by omega),
      show nP + extras.length - 1 + 1 = nP + extras.length from by omega,
      denoteMeta_forallE,
      denoteMeta_minorAtR hfT hlpsT hfC hlpsC hmty hc.hasFvar hc.bounded hc.resid hc.read hc.len
        hc.lenE hc.recIdxBnd (fun i hi fvs rest hop => fieldReadAt_of hc hi hop) hlenT hidxT
        hspW ho hidxE]
    generalize hmk : Expr.fvar (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty) = mkfv
    have hY : (Expr.instSeq (tfvs ++ extras) (nP + extras.length) rest).instantiate1 mkfv 0
        = Expr.instSeq (tfvs ++ (extras ++ [mkfv])) (nP + (extras ++ [mkfv]).length - 1) rest := by
      rw [← List.append_assoc, Expr.instSeq_append (tfvs ++ extras) [mkfv], hlenTE,
        List.length_append, List.length_singleton,
        show nP + (extras.length + 1) - 1 = nP + extras.length from by omega, Nat.sub_self]
      rfl
    have hidxE' : ∀ (k : Nat) (x : Expr), (extras ++ [mkfv])[k]? = some x →
        ∃ ty, x = Expr.fvar (nP + k) ty := by
      intro k x hx
      by_cases hk : k < extras.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxE k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - extras.length = 0 := by
          rcases Nat.lt_or_ge (k - extras.length) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by simp; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        refine ⟨Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty, ?_⟩
        rw [← hmk]
        congr 1
        omega
    have hrest' : ConLeche.structMinorsPisR lps nP pw cs (extras ++ [mkfv]).length body
        = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteMeta_minorsPisR hfT hlpsT hlenT hidxT hspW hcs hrest' (by simp) hidxE'
    rw [show nP + extras.length + 1 = nP + (extras ++ [mkfv]).length from by simp; omega, hY, hread]
    refine ⟨extras', by simp [hlenE']; omega, hidxE'', ?_⟩
    have harith : nP + (extras.length + 1) + cs.length = nP + extras.length + (cs.length + 1) := by
      omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, harith]
    cases denoteMeta m.acval env ψ (nP + extras.length + (cs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (cs.length + 1) - 1) body) <;> rfl

set_option maxHeartbeats 1600000 in
/-- **The `λ`-telescope of recursive minors** reads to the λ-tower over
`fixMinorsData`'s domains, the body read under the motive and all
minors. -/
theorem denoteMeta_minorsLamsR {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {ciT : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    {nP nIdx : Nat} {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR}
      {body mins : Expr} {extras : List Expr},
      CtorReadsR m ψ T lps nP nIdx ctors cds →
      ConLeche.structMinorsLamsR lps nP pw ctors extras.length body = some mins →
      0 < extras.length →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) →
      ∃ extras' : List Expr, extras'.length = ctors.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) ∧
        denoteMeta m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mins)
          = (denoteMeta m.acval env ψ (nP + extras.length + ctors.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + ctors.length - 1) body)).map
              (mkLamsAV ((fixMinorsData m ψ nP (pwBit ψ pw) cds extras.length).map
                fun d => (d.2.1, d.2.2)))
  | [], cds, body, mins, extras, hcr, hmin, _, hidxE => by
    cases hcr with
    | nil =>
    refine ⟨extras, by simp, hidxE, ?_⟩
    rw [ConLeche.structMinorsLamsR_nil hmin]
    simp only [List.length_nil, Nat.add_zero, fixMinorsData, List.map_nil]
    cases denoteMeta m.acval env ψ (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) body) <;> rfl
  | (C, nF, cty, recIdx) :: cs, cds, body, mins, extras, hcr, hmin, ho, hidxE => by
    cases hcr with
    | @cons _ cd _ cds' hc hcs =>
    obtain ⟨C', nF', ds, Es, recIdx', Eiss, tls⟩ := cd
    have hC' : C = C' := hc.name.symm
    have hnF' : nF = nF' := hc.nF.symm
    have hrI : recIdx' = recIdx := hc.recIdx
    subst hC' hnF' hrI
    obtain ⟨ci, hfC, hlpsC⟩ := hc.find
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := ConLeche.structMinorsLamsR_cons hmin
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    rw [ConLeche.instSeq_lam (tfvs ++ extras) (nP + extras.length - 1) _ _ _ (by omega),
      show nP + extras.length - 1 + 1 = nP + extras.length from by omega,
      denoteMeta_lam,
      denoteMeta_minorAtR hfT hlpsT hfC hlpsC hmty hc.hasFvar hc.bounded hc.resid hc.read hc.len
        hc.lenE hc.recIdxBnd (fun i hi fvs rest hop => fieldReadAt_of hc hi hop) hlenT hidxT
        hspW ho hidxE]
    generalize hmk : Expr.fvar (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty) = mkfv
    have hY : (Expr.instSeq (tfvs ++ extras) (nP + extras.length) rest).instantiate1 mkfv 0
        = Expr.instSeq (tfvs ++ (extras ++ [mkfv])) (nP + (extras ++ [mkfv]).length - 1) rest := by
      rw [← List.append_assoc, Expr.instSeq_append (tfvs ++ extras) [mkfv], hlenTE,
        List.length_append, List.length_singleton,
        show nP + (extras.length + 1) - 1 = nP + extras.length from by omega, Nat.sub_self]
      rfl
    have hidxE' : ∀ (k : Nat) (x : Expr), (extras ++ [mkfv])[k]? = some x →
        ∃ ty, x = Expr.fvar (nP + k) ty := by
      intro k x hx
      by_cases hk : k < extras.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxE k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - extras.length = 0 := by
          rcases Nat.lt_or_ge (k - extras.length) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by simp; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        refine ⟨Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty, ?_⟩
        rw [← hmk]
        congr 1
        omega
    have hrest' : ConLeche.structMinorsLamsR lps nP pw cs (extras ++ [mkfv]).length body
        = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteMeta_minorsLamsR hfT hlpsT hlenT hidxT hspW hcs hrest' (by simp) hidxE'
    rw [show nP + extras.length + 1 = nP + (extras ++ [mkfv]).length from by simp; omega, hY, hread]
    refine ⟨extras', by simp [hlenE']; omega, hidxE'', ?_⟩
    have harith : nP + (extras.length + 1) + cs.length = nP + extras.length + (cs.length + 1) := by
      omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, harith]
    cases denoteMeta m.acval env ψ (nP + extras.length + (cs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (cs.length + 1) - 1) body) <;> rfl

/-! ## The generated type -/

set_option maxHeartbeats 3200000 in
/-- **The generated recursive recursor type reads to the Π-tower over
`fixRecDataAV`** with the core `motive ı⃗ t`. -/
theorem denoteMeta_structRecTyR {m : EnvModel V env} {ψ : Name → Nat} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nIdx : Nat} {ciT : ConstantInfo}
    (hfT : env.find? T = some ciT) (hlpsT : ciT.toConstantVal.levelParams = lps)
    {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR}
    (hcr : CtorReadsR m ψ T lps nP nIdx ctors cds)
    {tty recTy : Expr}
    (hgen : ConLeche.structRecTyR T lps elim large nP nIdx tty ctors = some recTy)
    (hTf : tty.hasFvar = false) (hTb : tty.looseBVarsBounded 0 = true)
    (hstripT : (tty.stripPis (nP + nIdx)).isSome = true)
    {tfvs : List Expr} {trest : Expr} (hopT : openPisAtFvars nP tty 0 = some (tfvs, trest))
    {ppsAll : List (Nat × Nat × AnnotTerm)} {w : Nat}
    (hTread : denoteMeta m.acval env ψ 0 tty = some (mkPisAV ppsAll (.sort w)))
    (hlenP : ppsAll.length = nP + nIdx) :
    denoteMeta m.acval env ψ 0 recTy
      = some (mkPisAV (fixRecDataAV m T ψ nP nIdx (ConLeche.structElimLevel elim large)
            (ppsAll.take nP) (ppsAll.drop nP) cds)
          (recConcAV cds.length nIdx)) := by
  obtain ⟨tbs, itele, motiveTy, major, minors, hsT, hmot, hmaj, hmin, hrec⟩ :=
    ConLeche.structRecTyR_unfold hgen
  obtain ⟨hlenT, hidxT, hclT, hspW⟩ := opening_vars hopT hTf
  have hlenC : cds.length = ctors.length := hcr.length_eq
  generalize hn : ctors.length = n at hmaj hmin hlenC
  generalize hℓ : ConLeche.structElimLevel elim large = ℓ at hrec hmaj hmin hmot ⊢
  generalize hpw : Level.zeronessOf ℓ = pw at hrec hmaj hmin ⊢
  have hnil : tfvs = [] ∨ nP - 1 + 1 = nP := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  -- the parameter prefix
  have hst : stripPisAV nP (mkPisAV ppsAll (.sort w))
      = some (ppsAll.take nP, mkPisAV (ppsAll.drop nP) (.sort w)) :=
    stripPisAV_mkPisAV_take nP ppsAll _ (by omega)
  rw [denoteMeta_replacePisPw nP hrec hopT hTread hst, Nat.zero_add]
  -- the motive binder, instantiated at the parameters
  rw [Expr.instSeq_forallE tfvs (nP - 1) _ _ _ (by omega),
    instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1) (t' := nP) minors hnil]
  have hmotive := denoteMeta_motiveI hfT hlpsT hsT hmot hTf hstripT hTread hlenP hlenT hidxT hspW
  rw [denoteMeta_forallE, hmotive]
  -- the minors, at the motive's variable
  generalize hmfv : (Expr.fvar nP
    (Expr.instSeq tfvs (nP - 1) motiveTy)) = mfv
  have hX : (Expr.instSeq tfvs nP minors).instantiate1 mfv 0
      = Expr.instSeq (tfvs ++ [mfv]) nP minors := by
    rw [Expr.instSeq_append, hlenT, Nat.sub_self]
    rfl
  have hidxE : ∀ (k : Nat) (x : Expr), [mfv][k]? = some x →
      ∃ ty, x = Expr.fvar (nP + k) ty := by
    intro k x hx
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨_, by rw [← hmfv, Nat.add_zero]⟩
    | succ k => simp at hx
  have hmin' : ConLeche.structMinorsPisR lps nP pw ctors [mfv].length major = some minors := by
    rw [List.length_singleton]; exact hmin
  obtain ⟨extras', hlenE', hidxE', hread⟩ :=
    denoteMeta_minorsPisR hfT hlpsT hlenT hidxT hspW hcr hmin' (by simp) hidxE
  rw [hn, List.length_singleton] at hlenE' hread
  rw [Nat.add_sub_cancel] at hread
  rw [hX, hread]
  -- the index telescope, under the motive and the minors
  have hclE' : ∀ a ∈ extras', a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxE' q a hq
    rfl
  have hclTE : ∀ a ∈ tfvs ++ extras', a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclT a h
    · exact hclE' a h
  have hlenTE : (tfvs ++ extras').length = nP + 1 + n := by simp [hlenT, hlenE']; omega
  obtain ⟨mfv', hhead⟩ : ∃ x, extras'[0]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨tyM, rfl⟩ := hidxE' 0 mfv' hhead
  rw [Nat.add_zero] at hhead
  have htb0 : itele.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsT hTb; rwa [Nat.zero_add] at this
  have hmaj' := ConLeche.replacePisPw_instSeq (tfvs ++ extras') (nP + 1 + n - 1)
    (by rw [hlenTE]; omega) hmaj
  have hres := ConLeche.instSeq_minorTele tfvs extras' hlenT hclT htb0
  rw [hlenE', show nP + (n + 1) - 1 = nP + 1 + n - 1 from by omega] at hres
  rw [hres] at hmaj'
  obtain ⟨htread, htw, htstrip⟩ := ctorResidual hTf hTread hlenP hsT hstripT hlenT hidxT hspW
  obtain ⟨ifvs, irest, hopI⟩ := openPisAtFvars_of_stripPis_isSome nIdx (nP + 1 + n) htstrip
  have htreadN : denoteMeta m.acval env ψ (nP + 1 + n) (Expr.instSeq tfvs (nP - 1) itele)
      = some (mkPisAV (liftDoms (n + 1) 0 (ppsAll.drop nP)) (.sort w)) := by
    have := ctorResidual_read_lift htread htw hlenP (n + 1)
    rwa [show nP + (n + 1) = nP + 1 + n from by omega, AnnotTerm.liftN_sort] at this
  have hstI : stripPisAV nIdx (mkPisAV (liftDoms (n + 1) 0 (ppsAll.drop nP)) (.sort w))
      = some (liftDoms (n + 1) 0 (ppsAll.drop nP), .sort w) := by
    have := stripPisAV_mkPisAV (liftDoms (n + 1) 0 (ppsAll.drop nP)) (AnnotTerm.sort w)
    rwa [liftDoms_length, List.length_drop, hlenP, Nat.add_sub_cancel_left] at this
  have hmajR := denoteMeta_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nIdx hmaj' hopI
    htreadN hstI
  obtain ⟨hlenI, hidxI, hclI⟩ := opening_vars_at hopI
  -- the major and the conclusion, instantiated
  have hnilI : ifvs = [] ∨ nIdx - 1 + 1 = nIdx := by
    rcases Nat.eq_zero_or_pos nIdx with h0 | hpos
    · left; rw [h0] at hlenI; exact List.eq_nil_of_length_eq_zero hlenI
    · right; omega
  have hdom1 : Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx)
      (ConLeche.structFamI T lps nP nIdx (n + 1) 0)
      = Expr.mkAppN (.const T (lps.map .param))
          (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)) := by
    unfold ConLeche.structFamI
    rw [Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      show nP + 1 + n - 1 + nIdx = (0 + (n + 1) + nIdx) + nP - 1 from by omega,
      ConLeche.map_instSeq_structPsAt (tfvs ++ extras') (0 + (n + 1) + nIdx) nP hclTE
        (by rw [hlenTE]; omega),
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      structPsAt_zero, ConLeche.map_instSeq_fieldBvars_above (tfvs ++ extras') _ nIdx
        (by rw [hlenTE]; omega)]
  have hcod1 : Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx + 1)
      (Expr.mkAppN (.bvar (nIdx + n + 1)) (ConLeche.structPsAt 1 nIdx ++ [.bvar 0]))
      = Expr.mkAppN (.fvar nP tyM) (ConLeche.structPsAt 1 nIdx ++ [.bvar 0]) := by
    have hhead' : Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx + 1)
        (.bvar (nIdx + n + 1)) = Expr.fvar nP tyM := by
      have := Expr.instSeq_bvar (tfvs ++ extras') (nP + 1 + n - 1 + nIdx + 1) (nIdx + n + 1)
        hclTE (by omega) (by rw [hlenTE]; omega)
      rw [show nP + 1 + n - 1 + nIdx + 1 - (nIdx + n + 1) = nP from by omega,
        List.getElem?_append_right (by omega), hlenT, Nat.sub_self, hhead] at this
      exact (Option.some.inj this).symm
    rw [Expr.instSeq_mkAppN, hhead', List.map_append]
    congr 2
    · refine (List.map_congr_left ?_).trans (List.map_id _)
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      exact ConLeche.instSeq_bvar_lt _ _ _ (by rw [hlenTE]; omega)
    · simp only [List.map_cons, List.map_nil]
      rw [ConLeche.instSeq_bvar_lt _ _ _ (by rw [hlenTE]; omega)]
  have hdom2 : Expr.instSeq ifvs (nIdx - 1) (Expr.mkAppN (.const T (lps.map .param))
      (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)))
      = Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs) := by
    rw [Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      map_instSeq_closed ifvs (nIdx - 1) hclT,
      ConLeche.map_instSeq_fieldBvars ifvs nIdx hclI hlenI]
  have hcod2 : Expr.instSeq ifvs (nIdx - 1 + 1)
      (Expr.mkAppN (.fvar nP tyM) (ConLeche.structPsAt 1 nIdx ++ [.bvar 0]))
      = Expr.mkAppN (.fvar nP tyM) (ifvs ++ [.bvar 0]) := by
    rw [instSeq_idx_congr (sp := ifvs) (t := nIdx - 1 + 1) (t' := nIdx) _ hnilI,
      Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := Expr.fvar nP tyM) rfl,
      List.map_append, map_instSeq_structPsAt_one ifvs nIdx hclI hlenI]
    simp only [List.map_cons, List.map_nil]
    rw [ConLeche.instSeq_bvar_lt ifvs _ 0 (by omega)]
  have hbody : Expr.instSeq ifvs (nIdx - 1) (Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx)
      (.forallE (ConLeche.structFamI T lps nP nIdx (n + 1) 0)
        (Expr.mkAppN (.bvar (nIdx + n + 1)) (ConLeche.structPsAt 1 nIdx ++ [.bvar 0]))
        ⟨pw⟩))
      = .forallE (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))
          (Expr.mkAppN (.fvar nP tyM) (ifvs ++ [.bvar 0])) ⟨pw⟩ := by
    rw [Expr.instSeq_forallE (tfvs ++ extras') (nP + 1 + n - 1 + nIdx) _ _ _
        (by rw [hlenTE]; omega), hdom1, hcod1,
      Expr.instSeq_forallE ifvs (nIdx - 1) _ _ _ (by omega), hdom2, hcod2]
  rw [hbody] at hmajR
  -- the major's reading
  have hspine := denoteMeta_famSpine_at (m := m) (ψ := ψ) hfT hlpsT (o := 1 + n) hlenT hlenI hidxT
    (fun k x hx => by rw [show nP + (1 + n) + k = nP + 1 + n + k from by omega]; exact hidxI k x hx)
  rw [show nP + (1 + n) + nIdx = nP + 1 + n + nIdx from by omega] at hspine
  have hconc : denoteMeta m.acval env ψ (nP + 1 + n + nIdx + 1)
      ((Expr.mkAppN (.fvar nP tyM) (ifvs ++ [.bvar 0])).instantiate1
        (.fvar (nP + 1 + n + nIdx)
          (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))) 0)
      = some (recConcAV n nIdx) := by
    rw [Expr.mkAppN_instantiate1, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [Expr.instantiate1_eq_self (e := Expr.fvar nP tyM) rfl,
      map_instantiate1_closed hclI]
    simp +decide only [Expr.instantiate1, ↓reduceIte]
    have hspI : DenoteMetaSpine m.acval env ψ (nP + 1 + n + nIdx + 1) ifvs (idxVarsAV nIdx 1) := by
      have := denoteMetaSpine_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + 1 + n + nIdx + 1)
        ifvs (nP + 1 + n) hidxI
      rw [hlenI] at this
      have he : ((List.range nIdx).map fun k =>
          AnnotTerm.bvar (nP + 1 + n + nIdx + 1 - 1 - (nP + 1 + n + k))) = idxVarsAV nIdx 1 := by
        unfold idxVarsAV
        apply List.map_congr_left
        intro k _
        congr 1
        omega
      rwa [he] at this
    rw [denoteMeta_mkAppN (hspI.append (.cons (denoteMeta_fvar _ _ _ _) .nil)) (denoteMeta_fvar _ _ _ _),
      show nP + 1 + n + nIdx + 1 - 1 - nP = 1 + nIdx + n from by omega,
      show nP + 1 + n + nIdx + 1 - 1 - (nP + 1 + n + nIdx) = 0 from by omega,
      AnnotTerm.mkAppN_append_one]
    rfl
  have hpi : denoteMeta m.acval env ψ (nP + 1 + n + nIdx)
      (.forallE (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))
        (Expr.mkAppN (.fvar nP tyM) (ifvs ++ [.bvar 0])) ⟨pw⟩)
      = some (.pi 0 (pwBit ψ pw) (majorAVAt m T ψ nP nIdx n) (recConcAV n nIdx)) := by
    rw [denoteMeta_forallE, hspine, hconc]
    rfl
  rw [hpi, Option.map_some] at hmajR
  rw [hmajR]
  -- assembly
  subst hpw
  rw [← hlenC]
  unfold fixRecDataAV majorAVAt
  rw [mkPisAV_append, mkPisAV_append, mkPisAV_append, mkPisAV_append, hlenC]
  rfl

/-! ## The rule's core -/

set_option maxHeartbeats 3200000 in
/-- **The `ih` application in a rule** for recursive field `i`,
instantiated at the rule's frame, reads to `ihAppAV`: the field's
telescope as a λ-tower (`denoteMeta_ihIdxAtM` at each binder), then the
recursor's leaf at the block's variables, the field's index readings
and the field applied to the telescope's own variables. -/
theorem denoteMeta_ihApp {m : EnvModel V env} {ψ : Name → Nat} {nP nF n i : Nat} {pw : PropWhen}
    {cty : Expr} {recC : Name} {rlps : List Name} {ciR : ConstantInfo}
    (hfR : env.find? recC = some ciR) (hlpsR : ciR.toConstantVal.levelParams = rlps)
    {fvs0 : List Expr} {crest : Expr} {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF)
    (hfr : FieldReadAt m ψ nP nF i cty fvs0 tl Eis)
    {P X F : List Expr} (hP : P.length = nP) (hX : X.length = n + 1) (hF : F.length = nF)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxX : ∀ (k : Nat) (x : Expr), X[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + (n + 1) + k) ty) :
    denoteMeta m.acval env ψ (nP + 1 + n + nF)
        (Expr.instSeq (P ++ X ++ F) (nP + n + nF)
          (ConLeche.structIhApp recC (rlps.map .param) pw nP n nF i
            (ConLeche.structFieldTeleOf cty nP nF i) (ConLeche.structFieldIdxOf cty nP nF i)))
      = some (ihAppAV (m.acval recC ψ) nP n nF i (rebit (pwBit ψ pw) tl) Eis) := by
  obtain ⟨hlenTl, hbind, hspSrc⟩ := hfr
  obtain ⟨hlen0, hidx0, hcl0, hw0⟩ := opening_vars hop0 hCf
  have hS : (fvs0.take (nP + i)).length = nP + i := by
    rw [List.length_take, hlen0]
    omega
  have hidxS : ∀ (k : Nat) (x : Expr), (fvs0.take (nP + i))[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    have hk : k < nP + i := by
      rcases Nat.lt_or_ge k (nP + i) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hS]; omega)] at hx
        exact nomatch hx
    rw [List.getElem?_take, if_pos hk] at hx
    exact hidx0 k x hx
  have hprops := structFieldTele_props hCf hCb hstripC hi
  have hlenL : (P ++ X ++ F).length = nP + 1 + n + nF := by
    rw [List.length_append, List.length_append, hP, hX, hF]
    omega
  have hLidx : ∀ (k : Nat) (x : Expr), (P ++ X ++ F)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    have h := frameIdx (I := ([] : List Expr)) hP hX hF hidxP hidxX hidxF
      (by intro k x hx; simp at hx)
    simpa using h
  -- the frame under the telescope's openers
  have hlenLA : (P ++ X ++ F ++ openFvars (nP + 1 + n + nF)
      (ConLeche.structFieldTeleOf cty nP nF i).length).length
      = nP + 1 + n + nF + (ConLeche.structFieldTeleOf cty nP nF i).length := by
    rw [List.length_append, hlenL, openFvars_length]
  have hidxLA : ∀ (k : Nat) (x : Expr),
      (P ++ X ++ F ++ openFvars (nP + 1 + n + nF)
        (ConLeche.structFieldTeleOf cty nP nF i).length)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    by_cases hk : k < nP + 1 + n + nF
    · rw [List.getElem?_append_left (by rw [hlenL]; omega)] at hx
      exact hLidx k x hx
    · rw [List.getElem?_append_right (by rw [hlenL]; omega), hlenL] at hx
      have hlt : k - (nP + 1 + n + nF) < (ConLeche.structFieldTeleOf cty nP nF i).length := by
        rcases Nat.lt_or_ge (k - (nP + 1 + n + nF))
          (ConLeche.structFieldTeleOf cty nP nF i).length with h | h
        · exact h
        · rw [List.getElem?_eq_none (by rw [openFvars_length]; omega)] at hx
          exact nomatch hx
      rw [openFvars_getElem? hlt] at hx
      obtain rfl := (Option.some.inj hx).symm
      exact ⟨.sort .zero, by congr 1; omega⟩
  have hclLA : ∀ a ∈ P ++ X ++ F ++ openFvars (nP + 1 + n + nF)
      (ConLeche.structFieldTeleOf cty nP nF i).length, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxLA q a hq
    rfl
  have hbvarA : ∀ q : Nat, q < nP + 1 + n + nF + (ConLeche.structFieldTeleOf cty nP nF i).length →
      denoteMeta m.acval env ψ (nP + 1 + n + nF + (ConLeche.structFieldTeleOf cty nP nF i).length)
          (Expr.instSeq (P ++ X ++ F ++ openFvars (nP + 1 + n + nF)
              (ConLeche.structFieldTeleOf cty nP nF i).length)
            (nP + 1 + n + nF + (ConLeche.structFieldTeleOf cty nP nF i).length - 1) (Expr.bvar q))
        = some (AnnotTerm.bvar q) := by
    intro q hq
    have hb := Expr.instSeq_bvar (P ++ X ++ F ++ openFvars (nP + 1 + n + nF)
      (ConLeche.structFieldTeleOf cty nP nF i).length)
      (nP + 1 + n + nF + (ConLeche.structFieldTeleOf cty nP nF i).length - 1) q hclLA (by omega)
      (by rw [hlenLA]; omega)
    obtain ⟨ty, hy⟩ := hidxLA _ _ hb
    rw [hy, denoteMeta_fvar,
      show nP + 1 + n + nF + (ConLeche.structFieldTeleOf cty nP nF i).length - 1 -
        (nP + 1 + n + nF + (ConLeche.structFieldTeleOf cty nP nF i).length - 1 - q) = q from by omega]
  have hidxF' : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + (n + 1) + k) ty := hidxF
  -- the frame, as the `ih` lemmas spell it
  have hframe : ∀ (k : Nat) (t dd : Nat) (e : Expr),
      denoteMeta m.acval env ψ dd
          (Expr.instSeq (P ++ X ++ F ++ ([] : List Expr) ++
            openFvars (nP + (n + 1) + nF + 0) k) t e)
        = denoteMeta m.acval env ψ dd
            (Expr.instSeq (P ++ X ++ F ++ openFvars (nP + 1 + n + nF) k) t e) := by
    intro k t dd e
    rw [List.append_nil, show nP + (n + 1) + nF + 0 = nP + 1 + n + nF from by omega]
  unfold ConLeche.structIhApp ihAppAV
  rw [rebit_length, hlenTl, show nP + n + nF = nP + 1 + n + nF - 1 from by omega]
  refine denoteMeta_instSeq_mkLamsOf _ _ _ _ (P ++ X ++ F) (nP + 1 + n + nF) hlenL hLidx
    (by rw [List.length_map, ihTeleAtR_length, rebit_length, structTeleAt_length, hlenTl]) ?_ ?_
  · -- the telescope, binderwise
    intro k b p hb hp
    have hk : k < (ConLeche.structFieldTeleOf cty nP nF i).length := by
      rw [← structTeleAt_length nF (n + 1) i 0 pw (ConLeche.structFieldTeleOf cty nP nF i)]
      exact (List.getElem?_eq_some_iff.mp hb).1
    obtain ⟨b₀, hb₀⟩ : ∃ b₀, (ConLeche.structFieldTeleOf cty nP nF i)[k]? = some b₀ :=
      ⟨_, List.getElem?_eq_getElem hk⟩
    rw [structTeleAt_getElem? (pw := pw) hb₀] at hb
    obtain rfl := (Option.some.inj hb).symm
    obtain ⟨d, hd⟩ : ∃ d, tl[k]? = some d :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenTl]; exact hk)⟩
    rw [List.getElem?_map, ihTeleAtR, ihTeleAtGo_getElem? nF (n + 1) i 0 0 _ k, rebit,
      List.getElem?_map, hd] at hp
    simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hp
    obtain rfl := hp.symm
    obtain ⟨-, -, h3⟩ := hbind k b₀ d hb₀ hd
    obtain ⟨hef, heb⟩ := hprops.1 k b₀ hb₀
    refine ⟨rfl, ?_⟩
    rw [← hframe k (nP + 1 + n + nF + k - 1) (nP + 1 + n + nF + k),
      show nP + 1 + n + nF + k = nP + (n + 1) + nF + 0 + k from by omega]
    exact denoteMeta_ihIdxAtM (o := n + 1) (l := 0) (I := ([] : List Expr)) hef heb
      (Nat.le_of_lt hi) hS hidxS hP hX hF rfl hidxP hidxF' h3
  · -- the recursor's leaf at the block's variables, the readings and the field
    rw [structTeleAt_length nF (n + 1) i 0 pw (ConLeche.structFieldTeleOf cty nP nF i)]
    have hspI := denoteMetaSpine_ihIdx (m := m) (ψ := ψ) (o := n + 1) (l := 0)
      (I := ([] : List Expr)) hCf hCb hstripC hi rfl hS hidxS
      (by rw [hlenTl] at hspSrc; exact hspSrc) hP hX hF rfl hidxP hidxF'
    rw [List.append_nil, show nP + (n + 1) + nF + 0 = nP + 1 + n + nF from by omega] at hspI
    have hfieldApp : denoteMeta m.acval env ψ
        (nP + 1 + n + nF + (ConLeche.structFieldTeleOf cty nP nF i).length)
          (Expr.instSeq (P ++ X ++ F ++ openFvars (nP + 1 + n + nF)
              (ConLeche.structFieldTeleOf cty nP nF i).length)
            (nP + 1 + n + nF + (ConLeche.structFieldTeleOf cty nP nF i).length - 1)
            (Expr.mkAppN (.bvar (nF - 1 - i + (ConLeche.structFieldTeleOf cty nP nF i).length))
              (ConLeche.structTeleVars (ConLeche.structFieldTeleOf cty nP nF i).length)))
        = some (AnnotTerm.mkAppN
            (.bvar (nF - 1 - i + (ConLeche.structFieldTeleOf cty nP nF i).length))
            (teleVarsAV (ConLeche.structFieldTeleOf cty nP nF i).length)) := by
      rw [Expr.instSeq_mkAppN]
      refine denoteMeta_mkAppN ?_ (hbvarA _ (by omega))
      unfold ConLeche.structTeleVars teleVarsAV
      rw [List.map_map]
      simp only [Function.comp_def]
      exact DenoteMetaSpine.of_map (List.range (ConLeche.structFieldTeleOf cty nP nF i).length)
        (fun k hk => hbvarA _ (by rw [List.mem_range] at hk; omega))
    have hpre : DenoteMetaSpine m.acval env ψ
        (nP + 1 + n + nF + (ConLeche.structFieldTeleOf cty nP nF i).length)
        ((ConLeche.structRecPrefixAt nP n nF (ConLeche.structFieldTeleOf cty nP nF i).length).map
          (Expr.instSeq (P ++ X ++ F ++ openFvars (nP + 1 + n + nF)
              (ConLeche.structFieldTeleOf cty nP nF i).length)
            (nP + 1 + n + nF + (ConLeche.structFieldTeleOf cty nP nF i).length - 1)))
        (recPrefixBvarsM nP n nF (ConLeche.structFieldTeleOf cty nP nF i).length) := by
      unfold ConLeche.structRecPrefixAt recPrefixBvarsM
      rw [List.map_append, List.map_append]
      refine DenoteMetaSpine.append (DenoteMetaSpine.append ?_ ?_) ?_
      · unfold ConLeche.structPsAt paramBvarsAt
        rw [List.map_map]
        simp only [Function.comp_def]
        have hcong : ((List.range nP).map fun k =>
              AnnotTerm.bvar (nP + nF + n + 1 + (ConLeche.structFieldTeleOf cty nP nF i).length - 1 - k))
            = (List.range nP).map fun k => AnnotTerm.bvar
              ((ConLeche.structFieldTeleOf cty nP nF i).length + nF + n + 1 + nP - 1 - k) := by
          refine List.map_congr_left ?_
          intro k hk
          rw [List.mem_range] at hk
          congr 1
          omega
        rw [hcong]
        exact DenoteMetaSpine.of_map (List.range nP)
          (fun k hk => hbvarA _ (by rw [List.mem_range] at hk; omega))
      · rw [List.map_cons, List.map_nil,
          show nF + n + (ConLeche.structFieldTeleOf cty nP nF i).length
            = (ConLeche.structFieldTeleOf cty nP nF i).length + nF + n from by omega]
        exact .cons (hbvarA _ (by omega)) .nil
      · rw [List.map_map]
        simp only [Function.comp_def]
        have hcong : ((List.range n).map fun l =>
              AnnotTerm.bvar (nF + n - 1 - l + (ConLeche.structFieldTeleOf cty nP nF i).length))
            = (List.range n).map fun l => AnnotTerm.bvar
              ((ConLeche.structFieldTeleOf cty nP nF i).length + nF + n - 1 - l) := by
          refine List.map_congr_left ?_
          intro l hl
          rw [List.mem_range] at hl
          congr 1
          omega
        rw [hcong]
        exact DenoteMetaSpine.of_map (List.range n)
          (fun l hl => hbvarA _ (by rw [List.mem_range] at hl; omega))
    rw [Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (e := Expr.const recC (rlps.map .param)) rfl,
      List.map_append, List.map_append, List.map_map, List.map_cons, List.map_nil]
    simp only [Function.comp_def]
    rw [denoteMeta_mkAppN ((hpre.append hspI).append (.cons hfieldApp .nil))
      (by rw [denoteMeta_const hfR (by rw [hlpsR]; simp), hlpsR, Level.substFn_param_self])]


/-- The recursor's leading spine `p⃗ motive m⃗` in a rule, as one
`bvar` list: the parameters, the motive and the minors are the frame's
first `nP + n + 1` variables. -/
theorem recPrefixBvars_eq (nP n nF : Nat) :
    recPrefixBvars nP n nF
      = (List.range (nP + n + 1)).map fun k => AnnotTerm.bvar (nP + n + nF - k) := by
  have hlA : (paramBvarsAt nP (nP + nF + n + 1)).length = nP := by simp [paramBvarsAt]
  have hlAB : (paramBvarsAt nP (nP + nF + n + 1) ++ [AnnotTerm.bvar (nF + n)]).length = nP + 1 := by
    simp [paramBvarsAt]
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map]
  by_cases hk : k < nP + n + 1
  · rw [List.getElem?_eq_getElem (show k < (List.range (nP + n + 1)).length from by simp; omega),
      List.getElem_range, Option.map_some]
    unfold recPrefixBvars
    by_cases hkp : k < nP
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      simp only [paramBvarsAt, List.getElem?_map,
        List.getElem?_eq_getElem (show k < (List.range nP).length from by simp; omega),
        List.getElem_range, Option.map_some, Option.some.injEq]
      congr 1
      omega
    · by_cases hkm : k = nP
      · subst hkm
        rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega), hlA,
          Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        congr 1
        omega
      · rw [List.getElem?_append_right (by omega), hlAB]
        simp only [List.getElem?_map,
          List.getElem?_eq_getElem
            (show k - (nP + 1) < (List.range n).length from by simp; omega),
          List.getElem_range, Option.map_some, Option.some.injEq]
        congr 1
        omega
  · have hlR : (recPrefixBvars nP n nF).length = nP + n + 1 := by
      simp only [recPrefixBvars, paramBvarsAt, List.length_append, List.length_map,
        List.length_range, List.length_singleton]
      omega
    rw [List.getElem?_eq_none (by rw [hlR]; omega),
      List.getElem?_eq_none (show (List.range (nP + n + 1)).length ≤ k from by simp; omega)]
    rfl

set_option maxHeartbeats 3200000 in
/-- **Rule `j`'s core at a recursive block**: minor `j` at the field
variables and the inductive hypotheses, read at the full frame under
the motive and `n` minors. -/
theorem denoteMeta_ruleCoreR {m : EnvModel V env} {ψ : Name → Nat} {pw : PropWhen}
    {recC : Name} {rlps : List Name} {ciR : ConstantInfo}
    (hfR : env.find? recC = some ciR) (hlpsR : ciR.toConstantVal.levelParams = rlps)
    {nP nF n j : Nat} {cty : Expr} {recIdx : List Nat} {Eiss : List (List AnnotTerm)}
    {tls : List (List (Nat × Nat × AnnotTerm))}
    {fvs0 : List Expr} {crest00 : Expr}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest00))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true)
    (hrecBnd : ∀ i ∈ recIdx, i < nF)
    (hfr : ∀ i ∈ recIdx, FieldReadAt m ψ nP nF i cty fvs0 (tls.getD i []) (Eiss.getD i []))
    {tfvs extras xFvs : List Expr}
    (hlenT : tfvs.length = nP) (hlenE : extras.length = n + 1) (hlenX : xFvs.length = nF)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxE : ∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty)
    (hidxX : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + 1 + n + k) ty)
    (hj : j < n) :
    denoteMeta m.acval env ψ (nP + 1 + n + nF)
        (Expr.instSeq xFvs (nF - 1) (Expr.instSeq (tfvs ++ extras) (nP + n + nF)
          (ConLeche.structRuleBodyR recC (rlps.map .param) pw nP n nF j recIdx
            (ConLeche.structFieldTeleOf cty nP nF) (ConLeche.structFieldIdxOf cty nP nF))))
      = some (fixRuleCoreAV (pwBit ψ pw) (m.acval recC ψ) nP nF n j recIdx tls Eiss) := by
  have hidxX' : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + (n + 1) + k) ty := by
    intro k x hx
    obtain ⟨ty, hy⟩ := hidxX k x hx
    exact ⟨ty, by rw [hy]; congr 1; omega⟩
  have hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxT q a hq
    rfl
  have hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxE q a hq
    rfl
  have hlenTE : (tfvs ++ extras).length = nP + (n + 1) := by simp [hlenT, hlenE]
  have hcombR : ∀ Y : Expr,
      Expr.instSeq xFvs (nF - 1) (Expr.instSeq (tfvs ++ extras) (nP + n + nF) Y)
        = Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + n + nF) Y := by
    intro Y
    rw [Expr.instSeq_append (tfvs ++ extras) xFvs, hlenTE,
      show nP + n + nF - (nP + (n + 1)) = nF - 1 from by omega]
  have hLidx : ∀ (k : Nat) (x : Expr), (tfvs ++ extras ++ xFvs)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    have h := frameIdx (I := ([] : List Expr)) hlenT hlenE hlenX hidxT hidxE hidxX'
      (by intro k x hx; simp at hx)
    simpa using h
  have hclL : ∀ a ∈ tfvs ++ extras ++ xFvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hLidx q a hq
    rfl
  have hlenL : (tfvs ++ extras ++ xFvs).length = nP + 1 + n + nF := by
    simp [hlenT, hlenE, hlenX]
    omega
  have hbvar : ∀ q : Nat, q < nP + 1 + n + nF →
      denoteMeta m.acval env ψ (nP + 1 + n + nF)
          (Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + n + nF) (Expr.bvar q))
        = some (AnnotTerm.bvar q) := by
    intro q hq
    have hb := Expr.instSeq_bvar (tfvs ++ extras ++ xFvs) (nP + n + nF) q hclL
      (by omega) (by rw [hlenL]; omega)
    obtain ⟨ty, hy⟩ := hLidx _ _ hb
    rw [hy, denoteMeta_fvar,
      show nP + 1 + n + nF - 1 - (nP + n + nF - q) = q from by omega]
  have hpremap : (ConLeche.structRecPrefixAt nP n nF 0).map
      (Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + n + nF)) = tfvs ++ extras := by
    rw [show (Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + n + nF))
        = (fun a => Expr.instSeq xFvs (nF - 1)
            (Expr.instSeq (tfvs ++ extras) (nP + n + nF) a)) from by
      funext a; rw [hcombR]]
    exact ConLeche.map_instSeq_structRecPrefixAt tfvs extras xFvs hlenT hlenE hlenX hclT hclE
  have hpre : DenoteMetaSpine m.acval env ψ (nP + 1 + n + nF) (tfvs ++ extras)
      (recPrefixBvars nP n nF) := by
    have h := denoteMetaSpine_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + 1 + n + nF)
      (tfvs ++ extras) 0 (fun k x hx => by
        have hklt : k < (tfvs ++ extras).length := by
          rcases Nat.lt_or_ge k (tfvs ++ extras).length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hx
            exact nomatch hx
        obtain ⟨ty, hy⟩ := hLidx k x (by
          rw [List.getElem?_append_left hklt]
          exact hx)
        exact ⟨ty, by rw [hy, Nat.zero_add]⟩)
    have he : ((List.range (tfvs ++ extras).length).map fun k =>
        AnnotTerm.bvar (nP + 1 + n + nF - 1 - (0 + k))) = recPrefixBvars nP n nF := by
      rw [recPrefixBvars_eq, hlenTE,
        show nP + (n + 1) = nP + n + 1 from by omega]
      apply List.map_congr_left
      intro k _
      congr 1
      omega
    rwa [he] at h
  have hihApp : ∀ i ∈ recIdx,
      denoteMeta m.acval env ψ (nP + 1 + n + nF)
          (Expr.instSeq (tfvs ++ extras ++ xFvs) (nP + n + nF)
            (ConLeche.structIhApp recC (rlps.map .param) pw nP n nF i
              (ConLeche.structFieldTeleOf cty nP nF i) (ConLeche.structFieldIdxOf cty nP nF i)))
        = some (ihAppAV (m.acval recC ψ) nP n nF i (rebit (pwBit ψ pw) (tls.getD i []))
            (Eiss.getD i [])) := by
    intro i hi
    exact denoteMeta_ihApp hfR hlpsR hop0 hCf hCb hstripC (hrecBnd i hi) (hfr i hi) hlenT hlenE
      hlenX hidxT hidxE hidxX'
  rw [hcombR]
  unfold ConLeche.structRuleBodyR fixRuleCoreAV
  rw [Expr.instSeq_mkAppN, List.map_append, List.map_map, List.map_map]
  simp only [Function.comp_def]
  rw [denoteMeta_mkAppN
    ((DenoteMetaSpine.of_map (List.range nF)
        (fun k _ => hbvar (nF - 1 - k) (by omega))).append
      (DenoteMetaSpine.of_map recIdx (fun i hi => hihApp i hi)))
    (hbvar (nF + n - 1 - j) (by omega))]
  rfl

/-! ## The generated rule -/

set_option maxHeartbeats 3200000 in
/-- **Rule `j` reads to the λ-tower over `fixRuleDataAV`** at
constructor `j`'s data, with the core `minor_j f⃗ ih⃗`. -/
theorem denoteMeta_structRecRhsR {m : EnvModel V env} {ψ : Name → Nat} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nIdx j : Nat} {ciT : ConstantInfo}
    (hfT : env.find? T = some ciT) (hlpsT : ciT.toConstantVal.levelParams = lps)
    {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR}
    (hcr : CtorReadsR m ψ T lps nP nIdx ctors cds)
    {recC : Name} {rlps : List Name} {ciR : ConstantInfo}
    (hfR : env.find? recC = some ciR) (hlpsR : ciR.toConstantVal.levelParams = rlps)
    {tty rhs : Expr}
    (hgen : ConLeche.structRecRhsR T lps elim large nP nIdx tty ctors recC (rlps.map .param) j
      = some rhs)
    (hTf : tty.hasFvar = false)
    (hstripT : (tty.stripPis (nP + nIdx)).isSome = true)
    {tfvs : List Expr} {trest : Expr} (hopT : openPisAtFvars nP tty 0 = some (tfvs, trest))
    {ppsAll : List (Nat × Nat × AnnotTerm)} {w : Nat}
    (hTread : denoteMeta m.acval env ψ 0 tty = some (mkPisAV ppsAll (.sort w)))
    (hlenP : ppsAll.length = nP + nIdx)
    {C : Name} {nF : Nat} {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm}
    {recIdx : List Nat} {Eiss : List (List AnnotTerm)}
    {tls : List (List (Nat × Nat × AnnotTerm))}
    (hjd : cds[j]? = some (C, nF, ds, Es, recIdx, Eiss, tls)) :
    denoteMeta m.acval env ψ 0 rhs
      = some (mkLamsAV (fixRuleDataAV m T ψ nP nIdx (ConLeche.structElimLevel elim large)
            (ppsAll.take nP) (ppsAll.drop nP) cds ds)
          (fixRuleCoreAV (pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel elim large)))
            (m.acval recC ψ) nP nF cds.length j recIdx tls Eiss)) := by
  obtain ⟨C₀, nF₀, cty, recIdx₀, tbs, cbs, itele, motiveTy, crest0, inner, minors, hj, hsT,
    hmot, hsC, hinner, hmin, hr⟩ := ConLeche.structRecRhsR_unfold hgen
  obtain ⟨cd, hjd', hc⟩ := hcr.getElem? hj
  obtain ⟨rfl⟩ := Option.some.inj (hjd'.symm.trans hjd)
  have hC0 : C = C₀ := hc.name
  have hnF0 : nF = nF₀ := hc.nF
  have hrI0 : recIdx = recIdx₀ := hc.recIdx
  subst hC0 hnF0 hrI0
  have hCread := hc.read
  have hlenD : ds.length = nP + nF := hc.len
  have hCb : cty.looseBVarsBounded 0 = true := hc.bounded
  have hCf : cty.hasFvar = false := hc.hasFvar
  have hstripC : (cty.stripPis (nP + nF)).isSome = true := by
    obtain ⟨cbs0, es0, hs0, -⟩ := hc.resid
    rw [hs0]
    rfl
  obtain ⟨hlenT, hidxT, hclT, hspW⟩ := opening_vars hopT hTf
  have hlenC : cds.length = ctors.length := hcr.length_eq
  have hjn : j < ctors.length := (List.getElem?_eq_some_iff.mp hj).1
  generalize hn : ctors.length = n at hinner hlenC hjn
  generalize hℓ : ConLeche.structElimLevel elim large = ℓ at hr hmin hinner hmot ⊢
  generalize hpw : Level.zeronessOf ℓ = pw at hr hmin hinner ⊢
  have hnil : tfvs = [] ∨ nP - 1 + 1 = nP := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  have hst : stripPisAV nP (mkPisAV ppsAll (.sort w))
      = some (ppsAll.take nP, mkPisAV (ppsAll.drop nP) (.sort w)) :=
    stripPisAV_mkPisAV_take nP ppsAll _ (by omega)
  rw [denoteMeta_pisToLamsPw nP hr hopT hTread hst, Nat.zero_add]
  rw [ConLeche.instSeq_lam tfvs (nP - 1) _ _ _ (by omega),
    instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1) (t' := nP) minors hnil]
  have hmotive := denoteMeta_motiveI hfT hlpsT hsT hmot hTf hstripT hTread hlenP hlenT hidxT hspW
  rw [denoteMeta_lam, hmotive]
  generalize hmfv : (Expr.fvar nP
    (Expr.instSeq tfvs (nP - 1) motiveTy)) = mfv
  have hX : (Expr.instSeq tfvs nP minors).instantiate1 mfv 0
      = Expr.instSeq (tfvs ++ [mfv]) nP minors := by
    rw [Expr.instSeq_append, hlenT, Nat.sub_self]
    rfl
  have hidxE : ∀ (k : Nat) (x : Expr), [mfv][k]? = some x →
      ∃ ty, x = Expr.fvar (nP + k) ty := by
    intro k x hx
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨_, by rw [← hmfv, Nat.add_zero]⟩
    | succ k => simp at hx
  have hmin' : ConLeche.structMinorsLamsR lps nP pw ctors [mfv].length inner = some minors := by
    rw [List.length_singleton]; exact hmin
  obtain ⟨extras', hlenE', hidxE', hread⟩ :=
    denoteMeta_minorsLamsR hfT hlpsT hlenT hidxT hspW hcr hmin' (by simp) hidxE
  rw [hn, List.length_singleton] at hlenE' hread
  rw [Nat.add_sub_cancel] at hread
  rw [hX, hread]
  have hclE' : ∀ a ∈ extras', a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxE' q a hq
    rfl
  have hlenTE : (tfvs ++ extras').length = nP + 1 + n := by simp [hlenT, hlenE']; omega
  have hcb0 : crest0.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsC hCb
    rwa [Nat.zero_add] at this
  have hinner' := ConLeche.pisToLamsPw_instSeq (tfvs ++ extras') (nP + 1 + n - 1)
    (by rw [hlenTE]; omega) hinner
  have hres := ConLeche.instSeq_minorTele tfvs extras' hlenT hclT hcb0
  rw [hlenE', show nP + (n + 1) - 1 = nP + 1 + n - 1 from by omega] at hres
  rw [hres] at hinner'
  obtain ⟨hcread, hcw, hcstrip⟩ := ctorResidual hCf hCread hlenD hsC hstripC hlenT hidxT hspW
  obtain ⟨xFvs, xrest, hopX⟩ := openPisAtFvars_of_stripPis_isSome nF (nP + 1 + n) hcstrip
  have hcreadN : denoteMeta m.acval env ψ (nP + 1 + n) (Expr.instSeq tfvs (nP - 1) crest0)
      = some (mkPisAV (liftDoms (n + 1) 0 (ds.drop nP))
          ((AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF)) := by
    have := ctorResidual_read_lift hcread hcw hlenD (n + 1)
    rwa [show nP + (n + 1) = nP + 1 + n from by omega] at this
  have hstX : stripPisAV nF (mkPisAV (liftDoms (n + 1) 0 (ds.drop nP))
      ((AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF))
      = some (liftDoms (n + 1) 0 (ds.drop nP),
          (AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF) := by
    have := stripPisAV_mkPisAV (liftDoms (n + 1) 0 (ds.drop nP))
      ((AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have hinnerR := denoteMeta_pisToLamsPw (acval := m.acval) (env := env) (φ := ψ) nF hinner' hopX
    hcreadN hstX
  obtain ⟨hlenX, hidxX, hclX⟩ := opening_vars_at hopX
  obtain ⟨fvs0, crest00, hop0⟩ := openPisAtFvars_of_stripPis_isSome (nP + nF) 0 hstripC
  rw [show nP + 1 + n - 1 + nF = nP + n + nF from by omega,
    denoteMeta_ruleCoreR hfR hlpsR hop0 hCf hCb hstripC hc.recIdxBnd
      (fun i hi => fieldReadAt_of hc hi hop0) hlenT hlenE' hlenX hidxT hidxE' hidxX hjn,
    Option.map_some] at hinnerR
  rw [hinnerR]
  subst hpw
  rw [← hlenC]
  unfold fixRuleDataAV
  rw [List.map_append, List.map_append, List.map_append, mkLamsAV_append, mkLamsAV_append,
    mkLamsAV_append, rebit_map_lam, rebit_map_lam, hlenC]
  rfl

end ConLeche.Model
