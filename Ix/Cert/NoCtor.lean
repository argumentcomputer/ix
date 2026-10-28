import Ix.Cert.Admits
import Ix.CompileCert.MutualInductiveReading
import IxC.Kernel.Semantics.Bridge.DeclRun
import Ix.Cert.LowerDistinct

/-! # No constructor of a Source-accepted family occurs in its types (N-READS, N4 (b))

`inductive_reads` reads a standalone family's types with only the inductive as
its self, so it asks that no constructor of the family occur in them
(`InductiveReading.NoCtorIn`). That is a fact of Source acceptance, through
IxC's route-independent shape guard on every accepted `.indDecl`
(`Ix.Kernel.Semantics.checkDecl_noCtor`), and of the ingress, which carries the
sources' constants to their keys:

* `convertInductive_entries`: every member and constructor of a converted group
  has an entry under its key, with a conversion of its type;
* `lowerInductive_decl`, `lowerAll_mem`: the ingress's output holds the
  group's `indDecl` (`blockOf`), with canonical levels (`canonInfo_ind`,
  `canonInfo_ctor`, which keep the constants: `mentionsConst_mapLevels`);
* `acceptsRef_decl`: the reference fold checked that declaration at its prefix;
* `noCtorIn_of_ingress`: a conversion that mentions no constructor key has a
  source that mentions no constructor (no injectivity: a source name equal to a
  constructor's has its key);
* `noCtor_of_checkSourceWith`, `inductive_reads_sourceAccepts`: so `inductive_reads`
  holds of a Source-accepted closure with its `NoCtorIn` premises discharged;
  the family's name related to its key (R13's half) stays. -/

namespace Ix.Cert.NoCtor

open Ix.LeanIngress
open Ix.CompileCert.SourceConstructorPositions
open Ix.CompileCert.Loop (forIn_inv_array)

/-- An entry of a converted block: its key is the source constant's key and its
type a conversion of the source constant's type. -/
def Entry (item : Numbering × Ix.Expr) (name : Ix.Name)
    (e : Ix.Kernel.Reader.CVal .source × Nat × Nat) : Prop :=
  e.1.name = ingressKey name ∧ Converts item e.1.type

/-- The constructor loop's invariant, with the entries it has written: the items
left start with the remaining constructors' items, every entry of the class
before the loop is kept, and every processed constructor has its entry. -/
def EntriesInner (its : List (Numbering × Ix.Expr)) (cs : List Ix.ConstructorVal)
    (more : List (Numbering × Ix.Expr)) (base : List (Ix.Kernel.Reader.CVal .source × Nat × Nat))
    (pre : List Ix.ConstructorVal)
    (s : Nat × Array (Ix.Kernel.Reader.CVal .source × Nat × Nat) × List (Ix.Kernel.Reader.CName .source)) :
    Prop :=
  its.drop s.1 = (cs.drop pre.length).map ctorItem ++ more ∧ (∀ e ∈ base, e ∈ s.2.1.toList) ∧
    ∀ c ∈ pre, ∃ e ∈ s.2.1.toList, Entry (ctorItem c) c.cnst.name e

/-- The constructor classes' loop invariant, with the entries. -/
def EntriesOuter (its : List (Numbering × Ix.Expr)) (full : List (Array Ix.ConstructorVal))
    (more : List (Numbering × Ix.Expr)) (pre : List (Array Ix.ConstructorVal))
    (s : Nat × Array (Ix.Kernel.Reader.CVal .source × Nat × Nat) ×
      Array (List (Ix.Kernel.Reader.CName .source))) : Prop :=
  its.drop s.1 = ctorItems (full.drop pre.length) ++ more ∧
    ∀ cs ∈ pre, ∀ c ∈ cs.toList, ∃ e ∈ s.2.1.toList, Entry (ctorItem c) c.cnst.name e

/-- The type loop's invariant: the cursor is the number of types processed, and
every processed type has its entry. -/
def EntriesTypes (pre : List Ix.InductiveVal) (s : Nat × Array (Ix.Kernel.Reader.CVal .source × Nat × Nat)) :
    Prop :=
  s.1 = pre.length ∧ ∀ v ∈ pre, ∃ e ∈ s.2.toList,
    Entry (({ names := v.cnst.levelParams } : Numbering), v.cnst.type) v.cnst.name e

theorem converts_left {A B C : Array (Numbering × Ix.Expr)} {ks : Array (Ix.Kernel.Reader.CExpr .source)}
    (converted : List.Forall₂ Converts (A ++ B ++ C).toList ks.toList) {j : Nat} {a : Numbering × Ix.Expr}
    (h : A.toList[j]? = some a) : Converts a ks[j]! := by
  have at_ : (A ++ B ++ C).toList[j]? = some a := by
    rw [Array.toList_append, Array.toList_append, List.append_assoc,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
    exact h
  obtain ⟨k, found, conv⟩ := forall₂_getElem? converted at_
  rw [getElem!_of_toList found]
  exact conv

theorem drop_left_items {A B C : Array (Numbering × Ix.Expr)} :
    (A ++ B ++ C).toList.drop A.size = B.toList ++ C.toList := by
  rw [Array.toList_append, Array.toList_append, List.append_assoc, List.drop_left' (by simp)]

/-- The items `convertInductive` converts, as a list: their conversions, the
constructors' items after the types', and a type's item at its position. -/
theorem items_facts {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {C : Array (Numbering × Ix.Expr)} {ks : Array (Ix.Kernel.Reader.CExpr .source)}
    (converted : List.Forall₂ Converts
      (types.map (fun v => (({ names := v.cnst.levelParams } : Numbering), v.cnst.type)) ++
        ctors.flatMap (fun x => x.map ctorItem) ++ C).toList ks.toList) :
    ∃ (items more : List (Numbering × Ix.Expr)), List.Forall₂ Converts items ks.toList ∧
      items.drop types.size = ctorItems ctors.toList ++ more ∧
      ∀ (j : Nat) (v : Ix.InductiveVal), types.toList[j]? = some v →
        items[j]? = some (({ names := v.cnst.levelParams } : Numbering), v.cnst.type) := by
  refine ⟨_, C.toList, converted, ?_, ?_⟩
  · rw [show types.size = (types.map (fun (v : Ix.InductiveVal) => (({ names := v.cnst.levelParams } : Numbering),
        v.cnst.type))).size by simp, drop_left_items]
    simp [ctorItems, Array.toList_flatMap]
  · intro j v found
    have bound : j < types.size := by
      have := (List.getElem?_eq_some_iff.mp found).1
      simpa using this
    rw [Array.toList_append, Array.toList_append, List.append_assoc,
      List.getElem?_append_left (by simpa using bound), Array.toList_map, List.getElem?_map, found]
    rfl

/-- **The entries of a converted inductive block**: every member of the group
has an entry among the block's types, and every constructor one among its
constructors, under the member's key with a conversion of its type. -/
theorem convertInductive_entries (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal))
    (recs : Array Ix.RecursorVal) (conv : Converted) (ran : convertInductive types ctors recs = .ok conv) :
    ∃ rb : Ix.Kernel.Reader.BlockRead .source, conv = .inductive rb ∧
      (∀ v ∈ types.toList, ∃ e ∈ rb.types.toList,
        Entry (({ names := v.cnst.levelParams } : Numbering), v.cnst.type) v.cnst.name e) ∧
      (∀ cs ∈ ctors.toList, ∀ c ∈ cs.toList, ∃ e ∈ rb.ctors.toList, Entry (ctorItem c) c.cnst.name e) := by
  unfold convertInductive at ran
  split at ran
  · simp only at ran
    split at ran
    · cases ran
    · split at ran
      · obtain ⟨ks, convertedEq, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
        obtain ⟨its, more, converted, layout, typesAt⟩ := items_facts (exprsOf_spec convertedEq)
        obtain ⟨s₁, typesLoop, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
        obtain ⟨s₂, ctorsLoop, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
        obtain ⟨s₃, _, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
        simp only [pure, Except.pure, Except.ok.injEq] at rest
        subst rest
        have typesInv := forIn_inv_array EntriesTypes _ types (fun pre v post st r whole holds stepped => by
            obtain ⟨cursor, done⟩ := holds
            simp only [pure, Except.pure, Except.ok.injEq] at stepped
            subst stepped
            refine ⟨_, rfl, by simp [cursor], ?_⟩
            intro v' present
            rcases List.mem_append.mp present with old | new
            · obtain ⟨e, inside, entry⟩ := done v' old
              exact ⟨e, by simp [inside], entry⟩
            · rw [List.mem_singleton.mp new]
              refine ⟨_, Array.mem_toList_iff.mpr Array.mem_push_self, rfl, ?_⟩
              have at_ := typesAt st.1 v (by rw [cursor, ← whole]; simp)
              obtain ⟨k, found, conv⟩ := forall₂_getElem? converted at_
              show Converts _ ks[st.1]!
              rw [getElem!_of_toList found]
              exact conv)
          ⟨rfl, fun v present => by cases present⟩ typesLoop
        have outer := forIn_inv_array (EntriesOuter its ctors.toList more) _ ctors (by
            intro pre cs post st r whole holds stepped
            obtain ⟨cursor, doneAll⟩ := holds
            rw [drop_of_append whole] at cursor
            obtain ⟨inner, innerLoop, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok stepped
            simp only [pure, Except.pure, Except.ok.injEq] at returned
            subst returned
            have innerInv := forIn_inv_array
              (EntriesInner its cs.toList (ctorItems post ++ more) st.2.1.toList) _ cs (by
                intro pre' c post' st' r' whole' holds' stepped'
                obtain ⟨cursor', kept, doneInner⟩ := holds'
                rw [drop_of_append whole', List.map_cons, List.cons_append] at cursor'
                obtain ⟨at_, next⟩ := drop_cons cursor'
                split at stepped'
                · simp only [pure, Except.pure, Except.ok.injEq] at stepped'
                  subst stepped'
                  refine ⟨_, rfl, ?_, ?_, ?_⟩
                  · show its.drop (st'.1 + 1) = _
                    rw [next, List.length_append, List.length_singleton, ← List.drop_drop,
                      drop_of_append whole']
                    rfl
                  · intro e inside
                    exact Array.mem_toList_iff.mpr (Array.mem_push_of_mem _ (Array.mem_toList_iff.mp (kept e inside)))
                  · intro c' present
                    rcases List.mem_append.mp present with old | new
                    · obtain ⟨e, inside, entry⟩ := doneInner c' old
                      exact ⟨e, Array.mem_toList_iff.mpr (Array.mem_push_of_mem _ (Array.mem_toList_iff.mp inside)),
                        entry⟩
                    · rw [List.mem_singleton.mp new]
                      refine ⟨_, Array.mem_toList_iff.mpr Array.mem_push_self, rfl, ?_⟩
                      obtain ⟨k, found, conv⟩ := forall₂_getElem? converted at_
                      show Converts _ ks[st'.1]!
                      rw [getElem!_of_toList found]
                      exact conv
                · cases stepped')
              ⟨by rw [cursor]; simp [ctorItems], fun e inside => inside, fun c present => by cases present⟩
              innerLoop
            refine ⟨_, rfl, ?_, ?_⟩
            · show its.drop inner.1 = ctorItems (ctors.toList.drop (pre ++ [cs]).length) ++ more
              rw [innerInv.1, List.drop_length, List.map_nil, List.nil_append, List.length_append,
                List.length_singleton, ← List.drop_drop, drop_of_append whole]
              rfl
            · intro cs' present c inside
              rcases List.mem_append.mp present with old | new
              · obtain ⟨e, eIn, entry⟩ := doneAll cs' old c inside
                exact ⟨e, innerInv.2.1 e eIn, entry⟩
              · rw [List.mem_singleton.mp new] at inside
                exact innerInv.2.2 c inside)
          ⟨by show its.drop s₁.1 = _; rw [typesInv.1, Array.length_toList, layout]; rfl,
            fun cs present => by cases present⟩ ctorsLoop
        exact ⟨_, rfl, typesInv.2, outer.2⟩
      · cases ran
  · cases ran

/-! ## The reference fold accepts each declaration at its prefix -/

theorem foldlM_step_ok {α β ε : Type} {f : α → β → Except ε α} :
    ∀ {l : List β} {a r : α}, l.foldlM f a = .ok r → ∀ d ∈ l, ∃ x y, f x d = .ok y
  | [], _, _, _, d, hd => by cases hd
  | b :: l, a, r, h, d, hd => by
    rw [List.foldlM_cons] at h
    cases hb : f a b with
    | error e => simp [hb, bind, Except.bind] at h
    | ok a' =>
      simp only [hb, bind, Except.bind] at h
      rcases List.mem_cons.mp hd with rfl | later
      · exact ⟨a, a', hb⟩
      · exact foldlM_step_ok h d later

/-- **A reference accept checks each of its declarations**, at some fuel, from
the environment before it. -/
theorem acceptsRef_decl {md : Ix.Kernel.Mode} {μ : Ix.Kernel.CheckMode} {ev : Ix.Kernel.Evidences md}
    {ds : List (Ix.Kernel.Declaration md)} {env : Ix.Kernel.Env md}
    (h : Ix.Kernel.Cached.AcceptsRef μ ev ds env) {d : Ix.Kernel.Declaration md} (hd : d ∈ ds) :
    ∃ F e e₂, Ix.Kernel.checkDecl μ (Ix.Kernel.fueledOps μ F) ev e d = .ok e₂ := by
  obtain ⟨F, hF⟩ := h
  unfold Ix.Kernel.checkDeclsPure at hF
  obtain ⟨x, y, step⟩ := foldlM_step_ok hF d hd
  exact ⟨F, x, y, step⟩

/-! ## Canonical levels keep the constants -/

theorem mentionsConst_mapLevels (f : Ix.Kernel.Level → Ix.Kernel.Level) (T : Ix.Kernel.Key .source) :
    ∀ e : Ix.Kernel.Expr .source, (mapLevels f e).mentionsConst T = e.mentionsConst T := by
  intro e
  induction e with
  | bvar => rfl
  | fvar _ t ih => simp only [mapLevels, Ix.Kernel.Expr.mentionsConst, ih]
  | sort => rfl
  | const => rfl
  | app a b iha ihb => simp only [mapLevels, Ix.Kernel.Expr.mentionsConst, iha, ihb]
  | lam t b _ iht ihb => simp only [mapLevels, Ix.Kernel.Expr.mentionsConst, iht, ihb]
  | forallE t b _ iht ihb => simp only [mapLevels, Ix.Kernel.Expr.mentionsConst, iht, ihb]
  | letE t v b _ iht ihv ihb => simp only [mapLevels, Ix.Kernel.Expr.mentionsConst, iht, ihv, ihb]
  | lit => rfl
  | proj _ _ e ih => simp only [mapLevels, Ix.Kernel.Expr.mentionsConst, ih]

theorem canonExprM_run (lps : List Ix.Kernel.LevelParam) (e : Ix.Kernel.Expr .source) :
    ((canonExprM lps e).run' {} : Ix.Kernel.Expr .source) = mapLevels (canonLevelIn lps) e := by
  have := (mapLevelsGo_spec (f := canonLevelIn lps) e (memo := {}) (by
    intro k v found
    simp at found)).1
  exact this

/-- `canonInfo` of a type former or constructor: the same name, the type in
canonical levels. -/
theorem canonInfo_ind (cv : Ix.Kernel.ConstantVal .source) (caps : Ix.Kernel.IndCaps .source) :
    canonInfo (.indInfo cv caps) =
      .indInfo { cv with type := mapLevels (canonLevelIn cv.levelParams) cv.type } caps := by
  simp only [canonInfo, canonInfo.go, canonValM]
  rw [← canonExprM_run]
  rfl

theorem canonInfo_ctor (cv : Ix.Kernel.ConstantVal .source) (nP nF : Nat) :
    canonInfo (.ctorInfo cv nP nF) =
      .ctorInfo { cv with type := mapLevels (canonLevelIn cv.levelParams) cv.type } nP nF := by
  simp only [canonInfo, canonInfo.go, canonValM]
  rw [← canonExprM_run]
  rfl

/-! ## The conversion keeps the constants -/

theorem withContract_mentions {c : Ix.SemanticContract.Contract} {e : Ix.Expr} {x y : Ix.Kernel.Expr .source}
    (h : withContract c e x = .ok y) : ∀ T : Ix.Kernel.Key .source, y.mentionsConst T = x.mentionsConst T := by
  intro T
  unfold withContract at h
  split at h <;> first
    | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
    | cases h

theorem ingressMData_mentions {d : Array (Ix.Name × Ix.DataValue)} {e : Ix.Expr}
    {x : Except ExprError (Ix.Kernel.Expr .source)} {y : Ix.Kernel.Expr .source}
    (h : ingressMData d e x = .ok y) :
    ∃ k, x = .ok k ∧ ∀ T : Ix.Kernel.Key .source, y.mentionsConst T = k.mentionsConst T := by
  unfold ingressMData at h
  split at h
  · cases hr : (Ix.SemanticContract.read d).mapError ExprError.contract with
    | error err => simp [hr, bind, Except.bind] at h
    | ok c =>
      simp only [hr, bind, Except.bind] at h
      cases hx : x with
      | error err => simp [hx] at h
      | ok k =>
        simp only [hx] at h
        exact ⟨k, rfl, withContract_mentions h⟩
  · exact ⟨y, h, fun _ => rfl⟩

/-- **No constructor in the conversion, none in the source**: a source term
whose conversion mentions none of the constructors' keys mentions none of the
constructors. -/
theorem noCtorIn_of_ingress {σ : Ix.Name → Ix.Kernel.LevelParam} {C : Array Ix.ConstructorVal} :
    ∀ {e : Ix.Expr} {k : Ix.Kernel.Expr .source}, ingressExpr σ e = .ok k →
      (∀ c ∈ C.toList, k.mentionsConst (ingressKey c.cnst.name) = false) →
      Ix.CompileCert.InductiveReading.NoCtorIn C e := by
  intro e
  induction e with
  | const n us _ =>
    intro k h absent
    simp only [ingressExpr, bind, Except.bind] at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro c present same
      have := absent c present
      simp [Ix.Kernel.Expr.mentionsConst, same] at this
  | app f a _ ihf iha =>
    intro k h absent
    cases hf : ingressExpr σ f with
    | error err => simp [ingressExpr, hf, bind, Except.bind] at h
    | ok kf =>
      cases ha : ingressExpr σ a with
      | error err => simp [ingressExpr, hf, ha, bind, Except.bind] at h
      | ok ka =>
        simp only [ingressExpr, hf, ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Ix.Kernel.Expr.mentionsConst, Bool.or_eq_false_iff] at absent
        exact ⟨ihf hf fun c p => (absent c p).1, iha ha fun c p => (absent c p).2⟩
  | lam _ t b _ _ iht ihb =>
    intro k h absent
    cases ht : ingressExpr σ t with
    | error err => simp [ingressExpr, ht, bind, Except.bind] at h
    | ok kt =>
      cases hb : ingressExpr σ b with
      | error err => simp [ingressExpr, ht, hb, bind, Except.bind] at h
      | ok kb =>
        simp only [ingressExpr, ht, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Ix.Kernel.Expr.mentionsConst, Bool.or_eq_false_iff] at absent
        exact ⟨iht ht fun c p => (absent c p).1, ihb hb fun c p => (absent c p).2⟩
  | forallE _ t b _ _ iht ihb =>
    intro k h absent
    cases ht : ingressExpr σ t with
    | error err => simp [ingressExpr, ht, bind, Except.bind] at h
    | ok kt =>
      cases hb : ingressExpr σ b with
      | error err => simp [ingressExpr, ht, hb, bind, Except.bind] at h
      | ok kb =>
        simp only [ingressExpr, ht, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Ix.Kernel.Expr.mentionsConst, Bool.or_eq_false_iff] at absent
        exact ⟨iht ht fun c p => (absent c p).1, ihb hb fun c p => (absent c p).2⟩
  | letE _ t v b _ _ iht ihv ihb =>
    intro k h absent
    cases ht : ingressExpr σ t with
    | error err => simp [ingressExpr, ht, bind, Except.bind] at h
    | ok kt =>
      cases hv : ingressExpr σ v with
      | error err => simp [ingressExpr, ht, hv, bind, Except.bind] at h
      | ok kv =>
        cases hb : ingressExpr σ b with
        | error err => simp [ingressExpr, ht, hv, hb, bind, Except.bind] at h
        | ok kb =>
          simp only [ingressExpr, ht, hv, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [Ix.Kernel.Expr.mentionsConst, Bool.or_eq_false_iff] at absent
          exact ⟨iht ht fun c p => (absent c p).1.1, ihv hv fun c p => (absent c p).1.2,
            ihb hb fun c p => (absent c p).2⟩
  | mdata d e _ ih =>
    intro k h absent
    rw [ingressExpr_mdata] at h
    obtain ⟨k', inner, same⟩ := ingressMData_mentions h
    exact ih inner fun c p => by rw [← same]; exact absent c p
  | proj n i e _ ih =>
    intro k h absent
    cases he : ingressExpr σ e with
    | error err => simp [ingressExpr, he, bind, Except.bind] at h
    | ok ke =>
      simp only [ingressExpr, he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [Ix.Kernel.Expr.mentionsConst, Bool.or_eq_false_iff] at absent
      exact ih he fun c p => (absent c p).2
  | _ => intro _ _ _; trivial

/-! ## The ingress lowers the block to its declaration -/

/-- The constants of an inductive block's `indDecl`: its type formers, then its
constructors, then its recursors. -/
def blockOf {md : Ix.Kernel.Mode} (rb : Ix.Kernel.Reader.BlockRead md)
    (recInfos : List (Ix.Kernel.ConstantInfo md)) : List (Ix.Kernel.ConstantInfo md) :=
  (rb.types.toList.map fun (cv, _, _) => Ix.Kernel.ConstantInfo.indInfo cv {}) ++
    (rb.ctors.toList.map fun (cv, nP, nF) => Ix.Kernel.ConstantInfo.ctorInfo cv nP nF) ++ recInfos

theorem mem_blockOf_type {md : Ix.Kernel.Mode} {rb : Ix.Kernel.Reader.BlockRead md}
    {recInfos : List (Ix.Kernel.ConstantInfo md)} {entry : Ix.Kernel.Reader.CVal md × Nat × Nat}
    (h : entry ∈ rb.types.toList) : Ix.Kernel.ConstantInfo.indInfo entry.1 {} ∈ blockOf rb recInfos :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨entry, h, rfl⟩))

theorem mem_blockOf_ctor {md : Ix.Kernel.Mode} {rb : Ix.Kernel.Reader.BlockRead md}
    {recInfos : List (Ix.Kernel.ConstantInfo md)} {entry : Ix.Kernel.Reader.CVal md × Nat × Nat}
    (h : entry ∈ rb.ctors.toList) :
    Ix.Kernel.ConstantInfo.ctorInfo entry.1 entry.2.1 entry.2.2 ∈ blockOf rb recInfos :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨entry, h, rfl⟩))

/-- The recursors of an inductive block's `indDecl`, as `lowerInductive` builds them. -/
def recInfosOf {md : Ix.Kernel.Mode} (rb : Ix.Kernel.Reader.BlockRead md) : List (Ix.Kernel.ConstantInfo md) :=
  rb.recs.toList.map fun (cv, r, rules) =>
    .recInfo cv (r.params + r.motives + r.minors + r.indices) (r.params + r.motives + r.minors) rules

theorem mem_blockOf_rec {md : Ix.Kernel.Mode} {rb : Ix.Kernel.Reader.BlockRead md}
    {entry : Ix.Kernel.Reader.CVal md × Ix.Kernel.Reader.RecCounts × List (Ix.Kernel.RecRule md)}
    (h : entry ∈ rb.recs.toList) :
    ∃ mI rP, Ix.Kernel.ConstantInfo.recInfo entry.1 mI rP entry.2.2 ∈ blockOf rb (recInfosOf rb) :=
  ⟨_, _, List.mem_append_right _ (List.mem_map.mpr ⟨entry, h, rfl⟩)⟩

/-- **A lowered inductive block declares its `indDecl`** (`blockOf`, with its recursors). -/
theorem lowerInductive_decl {md : Ix.Kernel.Mode} {st : Ix.Kernel.Reader.State md}
    {rb : Ix.Kernel.Reader.BlockRead md} {r : Ix.Kernel.Reader.Read md}
    (h : Ix.Kernel.Reader.lowerInductive st rb = .ok r) :
    Ix.Kernel.Declaration.indDecl (blockOf rb (recInfosOf rb)) rb.numParams ∈ r.decls := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  replace h := LowerDistinct.lowerInductiveDecls_of_ok h
  unfold Ix.Kernel.Reader.lowerInductiveDecls at h
  dsimp only at h
  generalize Ix.Kernel.Frontend.InModel.generate _ _ = gen at h
  generalize Ix.Kernel.Frontend.InModel.wants _ = wants at h
  generalize Ix.Kernel.Frontend.projRecOwners _ _ _ _ = owners at h
  split at h
  all_goals generalize (_ != 0) = nested at h
  all_goals cases nested
  all_goals try (obtain ⟨_, _, h⟩ := Ix.Sharing.Verify.except_bind_eq_ok h)
  all_goals cases wants
  all_goals cases gen
  all_goals (cases h <;> first
    | exact Array.mem_push_self
    | exact Array.mem_toList_iff.mp (List.mem_singleton_self _))

/-- A loop in `Except` that only yields and keeps what it collects, run to
success: everything the start collected is in the result, and every element's
step ran, from some state, to a state whose collection is in the result. -/
theorem forIn_kept {α σ β ε : Type} (get : σ → Array β) {f : α → σ → Except ε (ForInStep σ)}
    (grows : ∀ a s t, f a s = .ok t → ∃ s', t = .yield s' ∧ ∀ x ∈ get s, x ∈ get s') :
    ∀ (l : List α) (b r : σ), forIn l b f = .ok r →
      (∀ x ∈ get b, x ∈ get r) ∧ ∀ a ∈ l, ∃ s s', f a s = .ok (.yield s') ∧ ∀ x ∈ get s', x ∈ get r := by
  intro l
  induction l with
  | nil =>
    intro b r h
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fun x hx => hx, fun a ha => by cases ha⟩
  | cons a l ih =>
    intro b r h
    rw [List.forIn_cons] at h
    cases ha : f a b with
    | error e => simp [ha, bind, Except.bind] at h
    | ok t =>
      obtain ⟨s', rfl, keep⟩ := grows a b t ha
      simp only [ha, bind, Except.bind] at h
      obtain ⟨keep', each⟩ := ih s' r h
      refine ⟨fun x hx => keep' x (keep x hx), fun a' ha' => ?_⟩
      rcases List.mem_cons.mp ha' with rfl | later
      · exact ⟨b, s', ha, keep'⟩
      · exact each a' later

/-- **A successful lowering holds every scheduled group's lowered
declarations**, with canonical levels. -/
theorem lowerAll_mem {st : Ix.Kernel.Reader.State .source} {g : Graph}
    {sched : Array (Nat × Except Ix.Kernel.Reader.ReadError Converted)}
    {r : Ix.Kernel.Reader.State .source × Array (Ix.Kernel.Reader.CDecl .source)}
    (h : lowerAll st g sched = .ok r) {gi : Nat} {c : Converted} (hc : (gi, .ok c) ∈ sched) :
    ∃ st₀ rd, lower st₀ c = .ok rd ∧ ∀ d ∈ rd.decls, canonDecl d ∈ r.2 := by
  unfold lowerAll at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i r' hr
    cases h
    rw [← Array.forIn_toList] at hr
    obtain ⟨k, hk, hsk⟩ := Array.getElem_of_mem hc
    have mem : ((gi, Except.ok c), k) ∈ sched.zipIdx.toList := by
      rw [Array.toList_zipIdx]
      exact List.mem_zipIdx_iff_getElem?.mpr (by simp [hk, hsk])
    obtain ⟨-, each⟩ := forIn_kept (fun s => s.2) (by
        intro a s t hs
        obtain ⟨⟨gi', c'⟩, i⟩ := a
        cases c' with
        | error e => simp [Except.mapError] at hs
        | ok conv =>
          simp only [Except.mapError] at hs
          split at hs
          · cases hs
          · cases hs
            exact ⟨_, rfl, fun x hx => Array.mem_append_left _ hx⟩) _ _ _ hr
    obtain ⟨s, s', step, kept⟩ := each _ mem
    simp only [Except.mapError] at step
    split at step
    · cases step
    · rename_i rd hrd
      cases step
      have hl : lower s.1 c = .ok rd := by
        cases hl : lower s.1 c with
        | error e => rw [hl] at hrd; cases hrd
        | ok v => rw [hl] at hrd; cases hrd; rfl
      refine ⟨s.1, rd, hl, fun d hd => kept _ (Array.mem_append_right _ (Array.mem_map_of_mem hd))⟩

/-! ## Source acceptance: no constructor of a family in its types -/

open Ix.CompileCert.InductiveReading (NoCtorIn) in
/-- **No constructor of a Source-accepted family occurs in the family's types**
(N-READS, N4 (b)): the ingress lowers the family's block to one `indDecl` whose
type formers and constructors carry the sources' keys and their types'
conversions (`convertInductive_entries`, `lowerInductive_decl`,
`lowerAll_mem`); the reference fold checked it at its prefix
(`checkSource_refines_ref`, `acceptsRef_decl`), so its declared shape held
(`Ix.Kernel.Semantics.checkDecl_noCtor`, IxC's route-independent guard): no constructor
key occurs in a former's or constructor's type, and so, through the
conversion, no constructor in the source's types (`noCtorIn_of_ingress`). The
set theory is a hypothesis of the fold's refinement, not of the statement's
meaning. -/
theorem noCtor_of_checkSourceWith (V : Type w) [Ix.Kernel.SetTheory V] {pre : Ix.Kernel.Reader.Prelude .source}
    {ev : Ix.Kernel.Evidences .source} {sub : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    (accepted : checkSourceWith pre ev sub blocks = .ok kenv) {n : Ix.Name} {first : Ix.InductiveVal}
    (stored : (n, Ix.ConstantInfo.inductInfo first) ∈ sub.consts.toList) (head : first.all[0]? = some n)
    {source : Ix.InductiveVal} (member : source.cnst.name ∈ first.all.toList)
    (found : sub.consts.get? source.cnst.name = some (.inductInfo source))
    (constructors : Array Ix.ConstructorVal)
    (looked : List.Forall₂ (fun n c => sub.consts.get? n = some (.ctorInfo c)) source.ctors.toList
      constructors.toList) :
    NoCtorIn constructors source.cnst.type ∧ ∀ ctor ∈ constructors.toList, NoCtorIn constructors ctor.cnst.type := by
  obtain ⟨decls, hingress, hc⟩ := checkSourceWith_reading accepted
  have href := Ix.Kernel.Cached.checkDecls_refines_ref V rfl hc
  obtain ⟨cands, memG⟩ := Ix.Cert.Admits.mem_groupsOf sub blocks stored head
  obtain ⟨gi, hlt, hgi⟩ := Array.getElem_of_mem memG
  have hlt' : gi < (graph sub blocks).groups.size := by rw [graph_groups]; exact hlt
  obtain ⟨c, hsched⟩ := scheduleOf_complete (graph sub blocks) hlt'
  unfold leanIngress at hingress
  simp only [bind, Except.bind, pure, Except.pure] at hingress
  split at hingress
  · cases hingress
  rename_i r hr
  cases hingress
  obtain ⟨conv, hconv⟩ := lowerAll_ok hr _ hsched
  simp only at hconv
  subst hconv
  have hconverted := scheduleOf_converted hsched rfl
  rw [graph_converted] at hconverted
  have hconv' : convert (inductiveGroup sub first cands) = .ok conv := by
    rw [← hgi]
    simpa [hlt] using hconverted
  rcases inductiveGroup_cases sub first cands with ⟨names, e, invalid⟩ | ⟨types, ctors, recs, layout⟩
  · rw [invalid] at hconv'
    cases hconv'
  rw [layout] at hconv'
  obtain ⟨rb, rfl, typeEntries, ctorEntries⟩ := convertInductive_entries types ctors recs conv hconv'
  obtain ⟨st₀, rd, hlow, kept⟩ := lowerAll_mem hr hsched
  have hdecl := lowerInductive_decl hlow
  generalize recInfosOf _ = recInfos at hdecl
  have inPrepared := Ix.Kernel.Frontend.mem_preparePrelude (pre := pre.ix) (kept _ hdecl)
  obtain ⟨F, e, e₂, checked⟩ := acceptsRef_decl href (Array.mem_toList_iff.mpr inPrepared)
  -- the family's members and constructors in the group
  obtain ⟨members, classes⟩ := inductiveGroup_spec sub first cands types ctors recs layout
  obtain ⟨v, memberIn, recorded⟩ := forall₂_mem members member
  obtain ⟨present, _⟩ := memberValue_some recorded
  rw [found] at present
  cases present
  obtain ⟨cs, classIn, classed⟩ := forall₂_mem classes memberIn
  obtain ⟨l, listed, rfl⟩ := Option.map_eq_some_iff.mp classed
  have recordedCtors := (ctorsValue_forall₂ sub source.cnst.name).mp listed
  rw [Array.toList_zipIdx] at recordedCtors
  obtain ⟨same, _⟩ := ctors_agree sub source.cnst.name source.ctors.toList 0 recordedCtors looked
  have ctorIn : ∀ ctor ∈ constructors.toList, ctor ∈ (List.toArray l).toList := by
    intro ctor inside
    rw [same] at inside
    simpa using inside
  -- every constructor's key is a constructor name of the checked block
  have keyIn : ∀ ctor ∈ constructors.toList, ingressKey ctor.cnst.name ∈ Ix.Kernel.indCtorNames
      ((blockOf rb recInfos).map canonInfo) := by
    intro ctor inside
    obtain ⟨entry, entryIn, named, _⟩ := ctorEntries _ classIn ctor (ctorIn ctor inside)
    unfold Ix.Kernel.indCtorNames
    refine List.mem_filterMap.mpr ⟨canonInfo (.ctorInfo entry.1 entry.2.1 entry.2.2), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨_, mem_blockOf_ctor entryIn, rfl⟩
    · rw [canonInfo_ctor]
      simp [named]
  -- a type of the block mentions no constructor key
  have absent : ∀ entry, (entry ∈ rb.types.toList ∨ entry ∈ rb.ctors.toList) →
      ∀ ctor ∈ constructors.toList, entry.1.type.mentionsConst (ingressKey ctor.cnst.name) = false := by
    intro entry entryIn ctor inside
    rw [← mentionsConst_mapLevels (canonLevelIn entry.1.levelParams)]
    refine Ix.Kernel.Semantics.checkDecl_noCtor (cv := { entry.1 with
      type := mapLevels (canonLevelIn entry.1.levelParams) entry.1.type }) checked (keyIn ctor inside) ?_
    rcases entryIn with typeIn | ctorIn'
    · exact .inl ⟨{}, List.mem_map.mpr ⟨_, mem_blockOf_type typeIn, canonInfo_ind _ _⟩⟩
    · exact .inr ⟨entry.2.1, entry.2.2, List.mem_map.mpr ⟨_, mem_blockOf_ctor ctorIn', canonInfo_ctor _ _ _⟩⟩
  refine ⟨?_, fun ctor inside => ?_⟩
  · obtain ⟨entry, entryIn, _, τ, conv⟩ := typeEntries source memberIn
    exact noCtorIn_of_ingress conv (absent entry (.inl entryIn))
  · obtain ⟨entry, entryIn, _, τ, conv⟩ := ctorEntries _ classIn ctor (ctorIn ctor inside)
    exact noCtorIn_of_ingress conv (absent entry (.inr entryIn))

/-! ## `inductive_reads` from Source acceptance -/

section Reading

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.InductiveReading
open Ix.Kernel (Mode LevelParam ConstRef)
open Ix.Kernel.Reader
open Ix.Sharing.Verify (BlockWireTablesWF BlockResultCodecWF)

variable {md : Mode} (cx : Ctx md) (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam)
  (bindings : Bindings)

/-- **A compiled standalone inductive of a Source-accepted closure is read back
as its source** (N-READS, N4 (b)): `inductive_reads` with its Source premises
(safety, constructor positions, telescopes: R12, through N1's admission) and
its "no constructor occurs" premises (`noCtor_of_checkSourceWith`) discharged by
Source acceptance of `sub`. What stays: the family's own name related to its
key (`selfKey`, R13's half), the reader's index and keys, the compile
context's agreement with `sub` on the constructor names, and the state the
block starts from. -/
theorem inductive_reads_sourceAccepts (V : Type w) [Ix.Kernel.SetTheory V]
    {condense : Ix.Environment → Ix.CondensedBlocks} {env : Ix.Environment} {roots : List Ix.Name}
    {sub : Ix.Environment} {envS : Ix.Kernel.Env .source} (accepted : SourceAccepts condense env roots sub envS)
    (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names)
    {n : Ix.Name} {first : Ix.InductiveVal} (stored : (n, Ix.ConstantInfo.inductInfo first) ∈ sub.consts.toList)
    (head : first.all[0]? = some n) (source : Ix.InductiveVal)
    (member : source.cnst.name ∈ first.all.toList)
    (sourceFound : sub.consts.get? source.cnst.name = some (.inductInfo source))
    (agree : ∀ n ∈ source.ctors.toList, context.1.env.get? n = sub.consts.get? n)
    (constructors : Array Ix.ConstructorVal) {before after : BlockState} {output : BlockResult}
    (found : (rawRun (lookupInductiveConstructors source)
      (EmissionDispatch.singletonContext source.cnst.name context) before).1 = .ok constructors)
    (state : State md) {shape : BlockShape} (indexed : cx.index.blocks[output.blockAddr]? = some shape)
    (order : shape.order = #[0]) {key : CName md} (keyed : cx.memberKey (.member output.blockAddr 0) = .ok key)
    (ctorKey : Nat → CName md)
    (ctorKeyed : ∀ j, j < constructors.size → cx.memberKey (.ctor output.blockAddr 0 j) = .ok (ctorKey j))
    (selfKey : names source.cnst.name key)
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after)) :
    BlockResultCodecWF output ∧ ProjectionLayout.InductiveLayout source constructors output ∧
      ∃ type ctorTypes, related names σ source source.cnst.type type ∧
        List.Forall₂ (related names σ source) (constructors.toList.map (·.cnst.type)) ctorTypes ∧
        readRecord (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block =
          readRecursors (ExpressionRead.withBlockBlobs cx after) (List.range source.cnst.levelParams.size)
              shape.recs >>= fun recs =>
            lowerInductive state (sourceBlock key ctorKey type ctorTypes source constructors recs) := by
  obtain ⟨cs, looked, rfl⟩ := collect_lookups (EmissionDispatch.singletonContext source.cnst.name context) free
    source.ctors.toList #[] before _ found
  have looked' : List.Forall₂ (fun n c => sub.consts.get? n = some (.ctorInfo c)) source.ctors.toList
      (#[] ++ cs.toArray).toList := by
    simpa using forall₂_mono_mem looked fun n inside c resolved => (agree n inside).symm.trans resolved
  obtain ⟨_, _, bundled⟩ := checkSourceBundled_with accepted.2
  obtain ⟨typeNoCtor, ctorNoCtor⟩ :=
    noCtor_of_checkSourceWith V bundled stored head member sourceFound _ looked'
  exact inductive_reads_source cx names σ bindings context free aligned external
    (Ix.Cert.Admits.admits_of_sourceAccepts accepted stored head) source member sourceFound agree _ found state
    indexed order keyed ctorKey ctorKeyed selfKey typeNoCtor ctorNoCtor clean wire ran

end Reading

end Ix.Cert.NoCtor
