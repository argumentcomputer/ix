import IxVMRefinement.FamilyAlias.UnitFree

/-! # The recursion scan finds a modeled block's nested occurrence

`KernelWhnf::struct_is_rec` (Lean's block-level `is_rec`) scans each constructor's field
domains, after the parameters, for a constant at a member's address (`se_scan_fields`); a `let`
counts as recursive. The dispatch's scan (`ctors_nested`) finds, at a modeled block of one
inductive, a nested occurrence after a constructor's parameters. Where the walk's return-type
check gives that constructor's type, after its parameters and fields, a constant applied to atoms
(`modeledCtor_trees`), the occurrence is in a field domain, which then mentions a member: the
recursion scan answers `1` there.

* `ScanTree.peelTol`, `ScanTree.fieldsScan`: the recursion scan on a term's shape;
* `nestedN_true_mentions`, `nestedN_spine_ne_true`, `fieldsScan_of_nested`, `ctorAnswer_true`:
  the pure part;
* `se_peel_tol_tree`, `se_scan_fields_tree`, `scan_ctors_tree`: the runs of the recursion scan on
  terms of a given shape, at an answer other than `1`. -/

namespace IxVM.Refinement.Route

/-! ## The recursion scan on a term's shape -/

/-- The term after at most `n` leading `∀` nodes (`se_peel_tol`). -/
def ScanTree.peelTol : Nat → ScanTree → ScanTree
  | 0, T => T
  | n + 1, .all _ b => ScanTree.peelTol n b
  | _ + 1, .atom => .atom
  | _ + 1, .const a => .const a
  | _ + 1, .app f x => .app f x
  | _ + 1, .lam t b => .lam t b
  | _ + 1, .letE t v b => .letE t v b
  | _ + 1, .proj x => .proj x

/-- **The field scan** (`se_scan_fields`): some leading `∀` domain mentions `M`, or the chain
ends in a `let`. -/
def ScanTree.fieldsScan (M : List _root_.Address) : ScanTree → Bool
  | .all t b => t.mentions M || ScanTree.fieldsScan M b
  | .letE _ _ _ => true
  | .atom => false
  | .const _ => false
  | .app _ _ => false
  | .lam _ _ => false
  | .proj _ => false

end IxVM.Refinement.Route

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Core
open IxVM.Refinement.Route

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem peelTol_of_peel : ∀ (n : Nat) {T B : ScanTree}, T.peel n = some B → T.peelTol n = B
  | 0, T, B, h => by
    simp only [ScanTree.peel, Option.some.injEq] at h
    exact h
  | n + 1, .all _ b, B, h => peelTol_of_peel n (T := b) h
  | _ + 1, .atom, _, h | _ + 1, .const _, _, h | _ + 1, .app _ _, _, h | _ + 1, .lam _ _, _, h
  | _ + 1, .letE _ _ _, _, h | _ + 1, .proj _, _, h => by simp [ScanTree.peel] at h

theorem peel_add : ∀ (a b : Nat) {T B : ScanTree}, T.peel a = some B →
    T.peel (a + b) = B.peel b
  | 0, b, T, B, h => by
    simp only [ScanTree.peel, Option.some.injEq] at h
    subst h
    simp
  | a + 1, b, .all _ t, B, h => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    exact peel_add a b (T := t) h
  | _ + 1, _, .atom, _, h | _ + 1, _, .const _, _, h | _ + 1, _, .app _ _, _, h
  | _ + 1, _, .lam _ _, _, h | _ + 1, _, .letE _ _ _, _, h | _ + 1, _, .proj _, _, h => by
    simp [ScanTree.peel] at h

/-! ## A nested occurrence mentions a member -/

theorem mentions_of_arg {M : List _root_.Address} :
    ∀ (T X : ScanTree), X ∈ T.args → X.mentions M = true → T.mentions M = true
  | .app f x, X, hX, hm => by
    simp only [ScanTree.args, List.mem_append, List.mem_singleton] at hX
    rcases hX with hX | rfl
    · simp [ScanTree.mentions, mentions_of_arg f X hX hm]
    · simp [ScanTree.mentions, hm]
  | .atom, _, hX, _ | .const _, _, hX, _ | .lam _ _, _, hX, _ | .all _ _, _, hX, _
  | .letE _ _ _, _, hX, _ | .proj _, _, hX, _ => by simp [ScanTree.args] at hX

theorem mentions_of_head {M : List _root_.Address} :
    ∀ T : ScanTree, T.head.mentions M = true → T.mentions M = true
  | .app f x, hm => by
    simp only [ScanTree.head] at hm
    simp [ScanTree.mentions, mentions_of_head f hm]
  | .atom, hm | .const _, hm | .lam _ _, hm | .all _ _, hm | .letE _ _ _, hm | .proj _, hm => hm

theorem orElse_eq_true {o₁ o₂ : Option Bool} (h : orElse o₁ o₂ = some true) :
    o₁ = some true ∨ o₂ = some true := by
  rcases o₁ with _ | _ | _
  · cases h
  · exact Or.inr h
  · exact Or.inl rfl

theorem foldr_orElse_true {α : Type} (f : α → Option Bool) :
    ∀ l : List α, (l.map f).foldr orElse (some false) = some true → ∃ x ∈ l, f x = some true
  | [], h => by cases h
  | x :: l, h => by
    rw [List.map_cons, List.foldr_cons] at h
    rcases orElse_eq_true h with h1 | h2
    · exact ⟨x, List.mem_cons_self, h1⟩
    · obtain ⟨y, hy, hfy⟩ := foldr_orElse_true f l h2
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- **A term on which the scan answers `1` mentions a member.** -/
theorem nestedN_true_mentions (isInd : _root_.Address → Option Bool) (M : List _root_.Address) :
    ∀ (n : Nat) (T : ScanTree), nestedN isInd M n T = some true → T.mentions M = true := by
  intro n
  induction n with
  | zero => intro T h; cases h
  | succ n ih =>
    intro T h
    cases T with
    | atom => cases h
    | const a => cases h
    | lam t b =>
      have key : nestedN isInd M (n + 1) (.lam t b) =
          orElse (nestedN isInd M n t) (nestedN isInd M n b) := rfl
      rw [key] at h
      rcases orElse_eq_true h with h1 | h2
      · simp [ScanTree.mentions, ih t h1]
      · simp [ScanTree.mentions, ih b h2]
    | all t b =>
      have key : nestedN isInd M (n + 1) (.all t b) =
          orElse (nestedN isInd M n t) (nestedN isInd M n b) := rfl
      rw [key] at h
      rcases orElse_eq_true h with h1 | h2
      · simp [ScanTree.mentions, ih t h1]
      · simp [ScanTree.mentions, ih b h2]
    | letE t v b =>
      have key : nestedN isInd M (n + 1) (.letE t v b) =
          orElse (nestedN isInd M n t)
            (orElse (nestedN isInd M n v) (nestedN isInd M n b)) := rfl
      rw [key] at h
      rcases orElse_eq_true h with h1 | h2
      · simp [ScanTree.mentions, ih t h1]
      · rcases orElse_eq_true h2 with h3 | h4
        · simp [ScanTree.mentions, ih v h3]
        · simp [ScanTree.mentions, ih b h4]
    | proj x =>
      have key : nestedN isInd M (n + 1) (.proj x) = nestedN isInd M n x := rfl
      rw [key] at h
      exact ih x h
    | app f x =>
      have key : nestedN isInd M (n + 1) (.app f x) =
          orElse (hereOf isInd M (ScanTree.app f x).head
            ((ScanTree.app f x).args.any fun A => A.mentions M)
            (nestedN isInd M n (ScanTree.app f x).head))
            (((ScanTree.app f x).args.map (nestedN isInd M n)).foldr orElse (some false)) := rfl
      rw [key] at h
      rcases orElse_eq_true h with h1 | h2
      · unfold hereOf at h1
        cases hc : (ScanTree.app f x).head.constAddr? with
        | none =>
          rw [hc] at h1
          exact mentions_of_head _ (ih _ h1)
        | some a =>
          rw [hc] at h1
          change hereConst isInd a (memB M a)
            ((ScanTree.app f x).args.any fun A => A.mentions M) = some true at h1
          cases ha : ((ScanTree.app f x).args.any fun A => A.mentions M) with
          | true =>
            obtain ⟨X, hX, hXm⟩ := List.any_eq_true.mp ha
            exact mentions_of_arg _ X hX hXm
          | false =>
            rw [ha] at h1
            cases hm : memB M a
            · rw [hm] at h1
              cases h1
            · rw [hm] at h1
              cases h1
      · obtain ⟨X, hX, hXn⟩ := foldr_orElse_true (nestedN isInd M n) _ h2
        exact mentions_of_arg _ X hX (ih X hXn)

/-- **The scan never answers `1` on a constant applied to atoms**, at any depth. -/
theorem nestedN_spine_ne_true (isInd : _root_.Address → Option Bool) (M : List _root_.Address)
    {S : ScanTree} (hhd : ∃ a, S.head = .const a) (hargs : ∀ X ∈ S.args, X = .atom) :
    ∀ n, nestedN isInd M n S ≠ some true := by
  intro n hn
  have hm := nestedN_true_mentions isInd M n S hn
  cases n with
  | zero => cases hn
  | succ n =>
    cases S with
    | atom => cases hn
    | const a => cases hn
    | lam t b =>
      obtain ⟨a, ha⟩ := hhd
      cases ha
    | all t b =>
      obtain ⟨a, ha⟩ := hhd
      cases ha
    | letE t v b =>
      obtain ⟨a, ha⟩ := hhd
      cases ha
    | proj x =>
      obtain ⟨a, ha⟩ := hhd
      cases ha
    | app f x =>
      obtain ⟨a, ha⟩ := hhd
      have key : nestedN isInd M (n + 1) (.app f x) =
          orElse (hereOf isInd M (ScanTree.app f x).head
            ((ScanTree.app f x).args.any fun A => A.mentions M)
            (nestedN isInd M n (ScanTree.app f x).head))
            (((ScanTree.app f x).args.map (nestedN isInd M n)).foldr orElse (some false)) := rfl
      rw [key] at hn
      rcases orElse_eq_true hn with h1 | h2
      · have hany : ((ScanTree.app f x).args.any fun A => A.mentions M) = false := by
          rw [List.any_eq_false]
          intro A hA
          rw [hargs A hA]
          exact Bool.false_ne_true
        unfold hereOf at h1
        rw [ha, hany] at h1
        change hereConst isInd a (memB M a) false = some true at h1
        cases hmb : memB M a
        · rw [hmb] at h1
          cases h1
        · rw [hmb] at h1
          cases h1
      · obtain ⟨X, hX, hXn⟩ := foldr_orElse_true (nestedN isInd M n) _ h2
        rw [hargs X hX] at hXn
        cases n with
        | zero => cases hXn
        | succ n => cases hXn

/-- **Where the scan answers `1` on a chain of `∀`s ending in a constant applied to atoms, the
field scan answers `1`**: the occurrence is in a domain. -/
theorem fieldsScan_of_nested (isInd : _root_.Address → Option Bool) (M : List _root_.Address)
    {S : ScanTree} (hhd : ∃ a, S.head = .const a) (hargs : ∀ X ∈ S.args, X = .atom) :
    ∀ (k n : Nat) (B : ScanTree), B.peel k = some S → nestedN isInd M n B = some true →
      B.fieldsScan M = true := by
  intro k
  induction k with
  | zero =>
    intro n B hp hn
    simp only [ScanTree.peel, Option.some.injEq] at hp
    subst hp
    exact absurd hn (nestedN_spine_ne_true isInd M hhd hargs n)
  | succ k ih =>
    intro n B hp hn
    cases B with
    | all t b =>
      cases n with
      | zero => cases hn
      | succ n =>
        have key : nestedN isInd M (n + 1) (.all t b) =
            orElse (nestedN isInd M n t) (nestedN isInd M n b) := rfl
        rw [key] at hn
        rcases orElse_eq_true hn with h1 | h2
        · simp [ScanTree.fieldsScan, nestedN_true_mentions isInd M n t h1]
        · simp [ScanTree.fieldsScan, ih n b hp h2]
    | atom => simp [ScanTree.peel] at hp
    | const _ => simp [ScanTree.peel] at hp
    | app _ _ => simp [ScanTree.peel] at hp
    | lam _ _ => simp [ScanTree.peel] at hp
    | letE _ _ _ => simp [ScanTree.peel] at hp
    | proj _ => simp [ScanTree.peel] at hp

theorem exprTree_of_some {refs M : List _root_.Address} {sharing : List Ixon.Expr}
    {e : Ixon.Expr} {T : ScanTree} (h : exprTree? refs M sharing e = some T) :
    ExprTree refs M sharing 4294967295 e T := by
  unfold exprTree? at h
  split at h
  · rename_i hex
    rw [← Option.some.inj h]
    exact Classical.choose_spec hex
  · cases h

/-- **A constructor the scan answers `1` at**: its stored type has a shape, its parameters peel,
and the scan answers `1` on the rest. -/
theorem ctorAnswer_true {isInd : _root_.Address → Option Bool} {M refs : List _root_.Address}
    {sharing : List Ixon.Expr} {ct : Ixon.Constructor}
    (h : ctorAnswer isInd M refs sharing ct = some true) :
    ∃ T Bd, ExprTree refs M sharing 4294967295 ct.typ T ∧ T.peel ct.params.toNat = some Bd ∧
      nestedN isInd M Bd.size Bd = some true := by
  unfold ctorAnswer at h
  split at h
  · cases h
  · rename_i T hT
    split at h
    · cases h
    · rename_i Bd hBd
      unfold ctorBody at h
      split at h
      · exact ⟨T, Bd, exprTree_of_some hT, hBd, h⟩
      · cases h

/-! ## The recursion scan's runs on terms of a given shape -/

/-- **`se_peel_tol` on a term of shape `T`**: the term after at most `n` leading `∀`s. -/
theorem se_peel_tol_tree :
    ∀ (k : Nat) {T : ScanTree} {ty r : SourceValue F} {p : F} {h h' : Heap F}
      {cs : List (Call F)},
      ZMod.val p = k → TreeAt h ty T →
      ObsFn Obs.W "KernelWhnf::se_peel_tol" [ty, .field p] h r h' cs →
      TreeAt h r (T.peelTol k) ∧ h' = h := by
  intro k
  induction k with
  | zero =>
    intro T ty r p h h' cs hk hT ev
    have hp : p = 0 := (ZMod.val_eq_zero p).mp hk
    subst hp
    rcases Obs.«KernelWhnf::se_peel_tol».obs ev with
      ⟨-, rfl, rfl, -⟩ | ⟨_, _, _, _, _, hne, _, _, _, _⟩ | ⟨_, hne, _, _, _, _, _⟩
    · exact ⟨hT, rfl⟩
    · exact absurd rfl hne
    · exact absurd rfl hne
  | succ k ih =>
    intro T ty r p h h' cs hk hT ev
    have hp0 : p ≠ 0 := fun e => by
      rw [e, ZMod.val_zero] at hk
      omega
    have hT0 := hT
    rcases Obs.«KernelWhnf::se_peel_tol».obs ev with
      ⟨hv, -, -, -⟩ | ⟨w42, x_body, w43, cs62, v66, hne, ld34, op87, ev64, -⟩ |
      ⟨v23, hne, ld34, hne90, rfl, rfl, -⟩
    · exact absurd (Value.field.inj hv) hp0
    · obtain ⟨Tt, Tb, rfl, -, hb⟩ := hT.all_inv ld34
      have hv := NatAux.sub_ok op87
      subst hv
      have hk' : ZMod.val (p - 1) = k := by
        have := Lib.val_sub_one hp0
        omega
      exact ih hk' hb ev64
    · refine ⟨?_, rfl⟩
      cases hT with
      | all hl _ _ =>
        rw [hl] at ld34
        injection ld34 with hv
        exact (hne90 _ rfl hv.symm).elim
      | bvar _ => exact hT0
      | srt _ => exact hT0
      | lit _ => exact hT0
      | const _ _ => exact hT0
      | app _ _ _ => exact hT0
      | lam _ _ _ => exact hT0
      | letE _ _ _ _ => exact hT0
      | proj _ _ => exact hT0

/-- **`se_scan_fields` on a term of shape `T`, at an answer other than `1`**: no leading domain
mentions a member and the chain does not end in a `let`. -/
theorem se_scan_fields_tree {ms : List Bytes.Address} :
    ∀ (T : ScanTree) {ty xs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      TreeAt h ty T → RepList addrListEnum RepAddr h ms xs →
      ObsFn Obs.W "KernelWhnf::se_scan_fields" [ty, xs] h r h' cs → r ≠ .field 1 →
      T.fieldsScan (ms.map ixAddr) = false := by
  intro T
  induction T with
  | all t b iht ihb =>
    intro ty xs r h h' cs hT hms ev hr
    rcases Obs.«KernelWhnf::se_scan_fields».obs ev with
      ⟨x_dom, x_body, w20, m37, cs48, ld12, ev50, he71, he72, hc73⟩ |
      ⟨x_dom, x_body, w20, v36, m37, cs48, cs81, ld12, ev50, hne74, ev83, hc100⟩ |
      ⟨w108, w109, w110, ld12, he126, he127, hc128⟩ |
      ⟨v1, ld12, hne101, hne129, he133, he134, hc135⟩
    · exact absurd he71 hr
    · obtain ⟨Tt, Tb, he, hTt, hTb⟩ := hT.all_inv ld12
      injection he with e1 e2
      subst e1 e2
      have c1 := se_mentions_exact (ms := ms) _ (Nat.le_refl _) hTt hms ev50
      have m1 := bit_ne_one (by rw [← c1]; exact hne74)
      have e1 := ev50.heap_extends
      have hb := ihb (hTb.mono e1) (se_addrs_mono e1 hms) ev83 hr
      simp [ScanTree.fieldsScan, m1, hb]
    · exact absurd he126 hr
    · cases hT with
      | all hl _ _ =>
        rw [hl] at ld12
        injection ld12 with hv
        exact (hne101 _ rfl hv.symm).elim
  | letE t v b _ _ _ =>
    intro ty xs r h h' cs hT hms ev hr
    rcases Obs.«KernelWhnf::se_scan_fields».obs ev with
      ⟨x_dom, x_body, w20, m37, cs48, ld12, ev50, he71, he72, hc73⟩ |
      ⟨x_dom, x_body, w20, v36, m37, cs48, cs81, ld12, ev50, hne74, ev83, hc100⟩ |
      ⟨w108, w109, w110, ld12, he126, he127, hc128⟩ |
      ⟨v1, ld12, hne101, hne129, he133, he134, hc135⟩
    · exact absurd he71 hr
    · cases hT with
      | letE hl _ _ _ =>
        rw [hl] at ld12
        injection ld12 with hv
        injection hv with _ htag _
        exact absurd htag (by decide)
    · exact absurd he126 hr
    · cases hT with
      | letE hl _ _ _ =>
        rw [hl] at ld12
        injection ld12 with hv
        exact (hne129 _ rfl hv.symm).elim
  | atom => intros; rfl
  | const _ => intros; rfl
  | app _ _ _ _ => intros; rfl
  | lam _ _ _ _ => intros; rfl
  | proj _ _ => intros; rfl

/-- **`struct_scan_ctors` read slot by slot, on the loaded types' shapes**: an answer other than
`1` means every slot `j + t` was loaded by an observed `Ingress::get_ci_cprj`, and the loaded
type, of whatever shape, has a field scan answering `0` after `p` binders. -/
theorem scan_ctors_tree (K : Nat) :
    ∀ {blk xs r : SourceValue F} {i n p j : F} {h h' : Heap F} {calls : List (Call F)}
      {ms : List Bytes.Address},
      ZMod.val (n - j) = K →
      ObsFn Obs.W "KernelWhnf::struct_scan_ctors" [blk, .field i, .field n, .field p, xs, .field j]
        h r h' calls →
      RepList addrListEnum RepAddr h ms xs → r ≠ .field 1 →
      ∀ t < K, ∃ (h1 h2 : Heap F) (ptr : SourceValue F) (cs1 : List (Call F))
        (nl ty : SourceValue F) (rest : List (SourceValue F)),
        Heap.Extends h h1 ∧
        ObsFn Obs.W "Ingress::get_ci_cprj" [blk, .field i, .field (j + (t : F))] h1 ptr h2 cs1 ∧
        (∀ x ∈ cs1, x ∈ calls) ∧
        loadValue h2 ptr = .ok (.construct Core.kciEnum "Ctor" (nl :: ty :: rest)) ∧
        ∀ T, TreeAt h2 ty T → (T.peelTol (ZMod.val p)).fieldsScan (ms.map ixAddr) = false := by
  induction K with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t ht; exact absurd ht (Nat.not_lt_zero _)
  | succ K ihK =>
    intro blk xs r i n p j h h' calls ms hK ev hms hr
    rcases Obs.«KernelWhnf::struct_scan_ctors».obs ev with
      ⟨op17, he24, he25, hc26⟩ |
      ⟨v1, m32, p39, cs45, w88, x_cty, w89, w90, w91, w92, w93, w94, v135, m136, cs146, m166,
        cs177, op17, hne27, ev47, ld41, ev148, ev179, he200, he201, hc202⟩ |
      ⟨v1, m32, p39, cs45, w88, x_cty, w89, w90, w91, w92, w93, w94, v135, m136, cs146, v165,
        m166, cs177, cs210, v218, op17, hne27, ev47, ld41, ev148, ev179, hne203, op267, ev212,
        hc269⟩ |
      ⟨v1, v31, m32, p39, cs45, op17, hne27, ev47, ld41, hne270, he274, he275, hc276⟩
    · have h0 : n - j = 0 := (NatAux.field_inj (NatAux.sub_ok op17)).symm
      rw [h0, ZMod.val_zero] at hK
      exact absurd hK (Nat.succ_ne_zero K).symm
    · exact absurd he200 hr
    · have hv := NatAux.sub_ok op17
      subst hv
      have hnj : n - j ≠ 0 := fun e => hne27 (by rw [e])
      have hv2 := NatAux.add_ok op267
      subst hv2 hc269
      have e1 := ObsFn.heap_extends ev47
      have e1' := ObsFn.heap_extends ev148
      have e2 := ObsFn.heap_extends ev179
      have hK' : ZMod.val (n - (j + 1)) = K := by
        have hs := Lib.val_sub_one hnj
        rw [show n - (j + 1) = n - j - 1 by ring]
        omega
      have hrec := ihK hK' ev212 (se_addrs_mono (e1.trans (e1'.trans e2)) hms) hr
      intro t ht
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · refine ⟨h, m32, p39, cs45, w88, x_cty, [w89, w90, w91, w92, w93, w94],
          Heap.Extends.refl _, ?_, fun x hx => by simp [hx], ld41, ?_⟩
        · simpa using ev47
        · intro T hT
          obtain ⟨hTP, hm⟩ := se_peel_tol_tree (ZMod.val p) rfl hT ev148
          subst hm
          exact se_scan_fields_tree _ hTP (se_addrs_mono e1 hms) ev179 hne203
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        obtain ⟨h1, h2, ptr, cs1, nl, ty, rest, eh1, evc, hsub, ldc, hfc⟩ :=
          hrec t' (by omega)
        refine ⟨h1, h2, ptr, cs1, nl, ty, rest, (e1.trans (e1'.trans e2)).trans eh1, ?_,
          fun x hx => by simp [hsub x hx], ldc, hfc⟩
        have e : j + ((t' + 1 : Nat) : F) = j + 1 + (t' : F) := by push_cast; ring
        rw [e]
        exact evc
    · exact absurd he274 hr

end IxVM.Refinement.Typing.FamilyAlias
