import Ix.Cert.EvidenceCheck
import Ix.Cert.Composition
import Ix.Cert.ReadingKeys
import Ix.Cert.ReaderClosureKeys
import Ix.Cert.ReaderUnits
import Ix.Cert.ReaderKeys
import Ix.Cert.SourceNames
import Ix.Cert.Evidence
import IxC.Kernel.Verify.Frontend.Prepare
import IxC.Kernel.Verify.Rename.Installs

/-! # The role table's evidence passes where quotient Source's does

On a compiled closure that quotient Source accepts, the reader's evidence
(`Ix.Kernel.Reader.evidenceOf` in the closure's reading context) gates every operation the
run installs as quotient Source's evidence renamed onto the artifact does, so the run is
accepted under it too (`evidenceTransfer`).

* **Context** (`keyAt_closure`, `blob_closure`, `store_closure`): in the closure's reading
  context, an address the evidence check vouches for (`Ix.Cert.EvidenceCheck.Agree`)
  reads as it does over the artifact's whole store, where it lies in the closure or the
  reader's fallback resolves it.
* **The gates** (`CoversOn`, `acceptsRef_coversOn`): a run reads its evidence only at the
  names it installs, so evidence that passes every gate of those names passes the run.
* **Equal at the installed operations**: an operation the run installs lies in the
  closure (`roleKey_origin`, through the reader's lowering), so its records read as the
  bundle's proofs, renamed (`Ix.Cert.EvidenceReading.evidenceValue_of_bundle`), and the two
  evidences have the same entries there, up to the theorems' keys (`strip`). -/

namespace Ix.Cert.EvidenceTransfer

open Ix.Kernel Ix.Kernel.Reader Ix.RoleEvidence Ix.Cert.EvidenceReading Ix.Cert.EvidenceCheck

/-! ## The closure's reading context -/

section Context

variable {ixe : Ixon.Env} {tA : RoleTable} {preA : Prelude .anon} {order : List Address}

/-- The closure context's store: the closure's records, then the fallback. -/
theorem closure_store (a : Address) :
    (Ix.Cert.closureContext ixe tA preA order).store a =
      ((Ix.Cert.Stream.decodedOf ixe order).lookup a <|> fallbackStore preA a) := by
  change ((recordMap (Ix.Cert.Stream.decodedOf ixe order).toArray)[a]? <|>
      ((recordMap (preA.records ++ preA.evidence))[a]? <|> none)) = _
  rw [Ix.Cert.ReaderClosureKeys.recordMap_get]
  simp [fallbackStore]

theorem decodedOf_lookup (a : Address) :
    (Ix.Cert.Stream.decodedOf ixe order).lookup a =
      if a ∈ order then Ix.Cert.recordAt ixe a else none := by
  induction order with
  | nil => simp [Ix.Cert.Stream.decodedOf]
  | cons b order ih =>
    rw [Ix.Cert.Stream.decodedOf_cons]
    by_cases hab : a = b
    · subst hab
      cases hr : Ix.Cert.recordAt ixe a with
      | none =>
        simp only [hr, Option.map_none, Option.toList_none, List.nil_append, ih, List.mem_cons, true_or,
          ↓reduceIte]
        split <;> simp
      | some c => simp
    · have hne : (a == b) = false := beq_eq_false_iff_ne.mpr hab
      cases hr : Ix.Cert.recordAt ixe b with
      | none => simp [ih, hab]
      | some c => simp [List.lookup_cons, hne, ih, hab]

/-- **On the closure, the closure context's store is the artifact's.** -/
theorem store_order {a : Address} (h : a ∈ order) :
    (Ix.Cert.closureContext ixe tA preA order).store a = fullStore ixe preA a := by
  rw [closure_store, decodedOf_lookup]
  simp only [h, ↓reduceIte, fullStore]

/-- Off the closure, the closure context's store is the fallback. -/
theorem store_off {a : Address} (h : a ∉ order) :
    (Ix.Cert.closureContext ixe tA preA order).store a = fallbackStore preA a := by
  rw [closure_store, decodedOf_lookup]
  simp [h]

/-- **The closure context's store is in the artifact's**, where the artifact holds every
fallback record it holds identically. -/
theorem store_sub (hfb : ∀ a c c', fallbackStore preA a = some c → Ix.Cert.recordAt ixe a = some c' → c' = c)
    {a : Address} {c : Ixon.Constant} (h : (Ix.Cert.closureContext ixe tA preA order).store a = some c) :
    fullStore ixe preA a = some c := by
  by_cases ho : a ∈ order
  · rwa [store_order ho] at h
  · rw [store_off ho] at h
    unfold fullStore
    cases hr : Ix.Cert.recordAt ixe a with
    | none => simpa using h
    | some c' => simp [hfb a c c' h hr]

/-- **The fallback is in the closure context's store**, under the same condition. -/
theorem fallback_sub (hfb : ∀ a c c', fallbackStore preA a = some c → Ix.Cert.recordAt ixe a = some c' → c' = c)
    {a : Address} {c : Ixon.Constant} (h : fallbackStore preA a = some c) :
    (Ix.Cert.closureContext ixe tA preA order).store a = some c := by
  by_cases ho : a ∈ order
  · rw [store_order ho]
    unfold fullStore
    cases hr : Ix.Cert.recordAt ixe a with
    | none => simpa using h
    | some c' => simp [hfb a c c' h hr]
  · rw [store_off ho, h]

end Context

/-! ## Resolution under stores that agree -/

/-- A reference resolves alike in a larger store. -/
theorem resolve_mono {s₁ s₂ : Store} (hs : ∀ a c, s₁ a = some c → s₂ a = some c) {x : Address}
    {R : ConstRef Address} (h : resolve s₁ x = some R) : resolve s₂ x = some R := by
  unfold resolve at h ⊢
  cases h1 : s₁ x with
  | none => rw [h1] at h; cases h
  | some c =>
    rw [h1] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    rw [hs x c h1]
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases hi : c.info with
    | defn _ | recr _ | axio _ | quot _ => simpa [resolveSource, hi] using h
    | muts _ => simp [resolveSource, hi] at h
    | dPrj p | iPrj p | rPrj p | cPrj p =>
      simp only [resolveSource, hi] at h ⊢
      cases hb : s₁ p.block with
      | none => simp [hb] at h
      | some cb =>
        rw [hs p.block cb hb]
        simpa [hb] using h

/-- A record's reference resolves alike in two stores that agree at the record and at
its block. -/
theorem resolve_congr {s₁ s₂ : Store} {x : Address} {c : Ixon.Constant} (h1 : s₁ x = some c)
    (h2 : s₂ x = some c) (hb : s₁ (Ix.Cert.ownerOf x c) = s₂ (Ix.Cert.ownerOf x c)) :
    resolve s₁ x = resolve s₂ x := by
  unfold resolve
  rw [h1, h2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases hi : c.info with
  | defn _ | recr _ | axio _ | quot _ | muts _ => simp [resolveSource, hi]
  | dPrj p | iPrj p | rPrj p | cPrj p =>
    simp only [Ix.Cert.ownerOf, hi] at hb
    simp only [resolveSource, hi, hb]

/-- The role bindings at a reference: the first bound role whose address resolves to it. -/
theorem bindings_get (store : Store) (t : RoleTable) (R : ConstRef Address) :
    (bindingsOf (md := .anon) store t).names[R]? =
      (t.bound.toList.find? (fun e => resolve store e.2 == some R)).map (fun e => Key.role e.1) := by
  rw [Ix.Cert.ReaderKeys.bindingsOf_eq]
  suffices ∀ (l : List (Role × Address)) (m : Std.HashMap (ConstRef Address) (CName .anon)),
      (l.foldl (Ix.Cert.ReaderKeys.bindingStep store) m)[R]? =
        (m[R]? <|> (l.find? (fun e => resolve store e.2 == some R)).map (fun e => Key.role e.1)) by
    simpa using this t.bound.toList {}
  intro l
  induction l with
  | nil => intro m; simp
  | cons e l ih =>
    intro m
    simp only [List.foldl_cons, List.find?_cons]
    rw [ih]
    unfold Ix.Cert.ReaderKeys.bindingStep
    cases hr : resolve store e.2 with
    | none =>
      have : (none == some R) = false := rfl
      simp [this]
    | some R' =>
      by_cases hR : R' = R
      · subst hR
        have hc : m.contains R' = (m[R']?).isSome := Std.HashMap.contains_eq_isSome_getElem?
        cases hk : m[R']? with
        | some k =>
          rw [hk] at hc
          simp [hc, hk]
        | none =>
          rw [hk] at hc
          simp [hc]
      · have hne : (some R' == some R) = false := by simp [hR]
        by_cases hm : m.contains R'
        · simp [hm, hne]
        · simp only [hm, Bool.false_eq_true, ↓reduceIte, hne, Bool.false_eq_true]
          rw [Std.HashMap.getElem?_insert]
          have : (R' == R) = false := beq_eq_false_iff_ne.mpr hR
          simp [this]

theorem find?_congr {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.find?_cons, h a (List.mem_cons_self ..)]
    rw [find?_congr l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- **A cited address keys alike in the closure context and over the artifact's store**:
where it resolves to `R` in both, the closure context's store is in the artifact's, and
no bound role address but itself resolves to `R` over the artifact's store. -/
theorem keyOfAddress_closure {cs full : Store} (hsub : ∀ a c, cs a = some c → full a = some c)
    {t : RoleTable} {x : Address} {R : ConstRef Address} (hcs : resolve cs x = some R)
    (hfull : resolve full x = some R) (huniq : ∀ e ∈ t.bound.toList, resolve full e.2 = some R → e.2 = x) :
    keyOfAddress cs (bindingsOf (md := .anon) cs t) x = keyOfAddress full (bindingsOf (md := .anon) full t) x := by
  have hnames : (bindingsOf (md := .anon) cs t).names[R]? = (bindingsOf (md := .anon) full t).names[R]? := by
    rw [bindings_get, bindings_get]
    congr 1
    apply find?_congr
    intro e he
    by_cases hf : resolve full e.2 = some R
    · have hx := huniq e he hf
      rw [hx] at hf ⊢
      simp [hcs, hf]
    · have hc : ¬ resolve cs e.2 = some R := fun h => hf (resolve_mono hsub h)
      rw [beq_eq_false_iff_ne.mpr hc, beq_eq_false_iff_ne.mpr hf]
  unfold keyOfAddress
  rw [hcs, hfull]
  simp only [bind, Option.bind, hnames]


/-! ## The gates a run reads -/

section Gates

variable {md : Mode}

/-- **`ev'` passes every evidence gate `ev` passes at the keys `K`.** -/
structure CoversOn (ops : (CheckerOps md) (CheckM md)) (ev ev' : Evidences md) (K : Key md → Prop) :
    Prop where
  defeq : ∀ c, K c → evidenceDefeqOk ev c = true → evidenceDefeqOk ev' c = true
  divMod : ∀ env env2 c, K c → checkDivModEvidence ops ev env env2 c = .ok () →
    checkDivModEvidence ops ev' env env2 c = .ok ()

/-- **One declaration**: a check that succeeds under `ev` succeeds under an `ev'` covering
it at the declaration's names. -/
theorem checkDecl_coversOn {mode : CheckMode} {ops : (CheckerOps md) (CheckM md)}
    {ev ev' : Evidences md} {K : Key md → Prop} (h : CoversOn ops ev ev' K) {env env' : Env md}
    {d : Declaration md} (hK : ∀ k ∈ d.names, K k)
    (hd : checkDecl mode ops ev env d = .ok env') : checkDecl mode ops ev' env d = .ok env' := by
  cases d with
  | defnDecl cv value hint =>
    have hKc : K cv.name := hK cv.name (by simp [Declaration.names])
    simp only [checkDecl] at hd ⊢
    cases h1 : checkConstantVal ops env cv with
    | error e => rw [h1] at hd; cases hd
    | ok cv' =>
      have hname : cv'.name = cv.name := (Ix.Kernel.checkConstantVal_post (ops := ops) env cv cv' h1).1
      have hK' : K cv'.name := hname ▸ hKc
      rw [h1] at hd
      simp only [bind, Except.bind] at hd ⊢
      cases h2 : checkDefnVal ops env cv' value hint with
      | error e => rw [h2] at hd; cases hd
      | ok env2 =>
        rw [h2] at hd
        simp only at hd ⊢
        have disjoint := Ix.Cert.Evidence.natNames_disjoint (md := md) cv'.name
        by_cases hn : natOpNames.contains cv'.name = true
        · have hm : natDivModNames.contains cv'.name = false := by
            cases e : natDivModNames.contains cv'.name
            · rfl
            · exact absurd ⟨hn, e⟩ disjoint
          have hev : evidenceDefeqOk ev cv'.name = true := by
            cases e : evidenceDefeqOk ev cv'.name
            · simp only [hn, hm, e] at hd; cases hd
            · rfl
          simpa only [hn, hm, hev, h.defeq _ hK' hev, ↓reduceIte, Bool.false_eq_true] using hd
        · by_cases hm : natDivModNames.contains cv'.name = true
          · cases e : checkDivModEvidence ops ev env env2 cv'.name with
            | error err => simp only [hn, hm, e] at hd; cases hd
            | ok u =>
              cases u
              simpa only [hn, hm, e, h.divMod _ _ _ hK' e, ↓reduceIte, Bool.false_eq_true] using hd
          · simpa only [hn, hm, ↓reduceIte, Bool.false_eq_true] using hd
  | _ => exact hd

theorem foldlM_coversOn {mode : CheckMode} {ops : (CheckerOps md) (CheckM md)}
    {ev ev' : Evidences md} {K : Key md → Prop} (h : CoversOn ops ev ev' K) :
    ∀ (ds : List (Declaration md)) (env₀ env : Env md), (∀ d ∈ ds, ∀ k ∈ d.names, K k) →
      ds.foldlM (checkDecl mode ops ev) env₀ = .ok env →
        ds.foldlM (checkDecl mode ops ev') env₀ = .ok env
  | [], _, _, _, hd => hd
  | d :: ds, env₀, env, hK, hd => by
    simp only [List.foldlM_cons, bind, Except.bind] at hd ⊢
    cases e : checkDecl mode ops ev env₀ d with
    | error err => rw [e] at hd; cases hd
    | ok env₁ =>
      rw [e] at hd
      rw [checkDecl_coversOn h (hK d (List.mem_cons_self ..)) e]
      exact foldlM_coversOn h ds env₁ env (fun d' hd' => hK d' (List.mem_cons_of_mem _ hd')) hd

/-- **Reference acceptance moves to evidence covering it at the names the run installs.** -/
theorem acceptsRef_coversOn {μ : CheckMode} {ev ev' : Evidences md} {ds : List (Declaration md)}
    {env : Env md} (h : ∀ F, CoversOn (fueledOps μ F) ev ev' (fun c => ∃ d ∈ ds, c ∈ d.names))
    (hd : Cached.AcceptsRef μ ev ds env) : Cached.AcceptsRef μ ev' ds env := by
  obtain ⟨F, hF⟩ := hd
  exact ⟨F, foldlM_coversOn (h F) ds _ _ (fun d hd k hk => ⟨d, hd, hk⟩) hF⟩

/-! ## The gates' views of the evidence -/

/-- An entry with its theorem's key forgotten. -/
def strip : Evidence (Key md × Ix.Kernel.Expr md) → Evidence (Ix.Kernel.Expr md)
  | .defeq => .defeq
  | .proof (_, v) => .proof v

theorem all_defeqKind_strip (l : List (Evidence (Key md × Ix.Kernel.Expr md))) (b : Bool) :
    (l.map strip).all (·.isDefeqKind b) = l.all (·.isDefeqKind b) := by
  rw [List.all_map]
  congr 1
  funext e
  cases e with
  | defeq => rfl
  | proof kv => rfl

theorem mapM_congr_strip {β : Type} {f : Evidence (Key md × Ix.Kernel.Expr md) → Option β}
    (hf : ∀ e₁ e₂, strip e₁ = strip e₂ → f e₁ = f e₂) :
    ∀ (l₁ l₂ : List (Evidence (Key md × Ix.Kernel.Expr md))), l₁.map strip = l₂.map strip →
      l₁.mapM f = l₂.mapM f
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | e₁ :: l₁, e₂ :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.mapM_cons, hf e₁ e₂ h.1, mapM_congr_strip hf l₁ l₂ h.2]

/-- **The gates read a role's entries only up to the theorems' keys.** -/
theorem gates_of_strip {ev ev' : Evidences md} {c : Key md}
    (h : ∀ r, opRole? c = some r → (ev.of r).map strip = (ev'.of r).map strip) :
    evidenceDefeqOk ev c = evidenceDefeqOk ev' c ∧ evidenceProofs ev c = evidenceProofs ev' c := by
  unfold evidenceDefeqOk evidenceProofs
  cases hr : opRole? c with
  | none => exact ⟨rfl, rfl⟩
  | some r =>
    have hs := h r hr
    have hl : (ev.of r).length = (ev'.of r).length := by
      rw [← List.length_map (f := strip), hs, List.length_map]
    refine ⟨?_, ?_⟩
    · simp only [hl]
      rw [← all_defeqKind_strip, hs, all_defeqKind_strip]
    · simp only [hl]
      split
      · exact mapM_congr_strip (fun e₁ e₂ he => by
          cases e₁ <;> cases e₂ <;> simp_all [strip]) _ _ hs
      · rfl

theorem checkDivMod_of_strip {ops : (CheckerOps md) (CheckM md)} {ev ev' : Evidences md} {c : Key md}
    (h : ∀ r, opRole? c = some r → (ev.of r).map strip = (ev'.of r).map strip) (env env2 : Env md) :
    checkDivModEvidence ops ev env env2 c = checkDivModEvidence ops ev' env env2 c := by
  unfold checkDivModEvidence
  rw [(gates_of_strip h).2]

/-- **Evidence with the same entries at the operations of `K`, up to the theorems' keys,
covers there.** -/
theorem coversOn_of_strip {ops : (CheckerOps md) (CheckM md)} {ev ev' : Evidences md} {K : Key md → Prop}
    (h : ∀ c r, K c → opRole? c = some r → (ev.of r).map strip = (ev'.of r).map strip) :
    CoversOn ops ev ev' K where
  defeq c hc hd := by rw [← (gates_of_strip (h c · hc)).1]; exact hd
  divMod env env2 c hc hd := by rw [← checkDivMod_of_strip (h c · hc) env env2]; exact hd

end Gates


/-! ## Blobs -/

/-- One step of a first-wins map. -/
def firstStep {β : Type} (m : Std.HashMap Address β) (p : Address × β) : Std.HashMap Address β :=
  if m.contains p.1 then m else m.insert p.1 p.2

theorem firstFold_get {β : Type} (xs : List (Address × β)) (m : Std.HashMap Address β) (a : Address) :
    (xs.foldl firstStep m)[a]? = (m[a]? <|> xs.lookup a) := by
  induction xs generalizing m with
  | nil => simp
  | cons p xs ih =>
    rw [List.foldl_cons, ih, List.lookup_cons]
    cases h : m[a]? with
    | some c =>
      have hk : (firstStep m p)[a]? = some c := by
        unfold firstStep
        split
        · exact h
        · rw [Std.HashMap.getElem?_insert]
          split
          · rename_i hc he
            have he : p.1 = a := beq_iff_eq.mp he
            subst he
            have : m.contains p.1 = true := by
              rw [Std.HashMap.contains_eq_isSome_getElem?, h]; rfl
            exact absurd this hc
          · exact h
      rw [hk]; rfl
    | none =>
      by_cases he : p.1 = a
      · rcases p with ⟨a', c⟩
        dsimp only at he
        subst a'
        have hc : m.contains a = false := by rw [Std.HashMap.contains_eq_isSome_getElem?, h]; rfl
        simp [firstStep, hc]
      · have ha : (a == p.1) = false := beq_eq_false_iff_ne.mpr (Ne.symm he)
        have hp : (p.1 == a) = false := beq_eq_false_iff_ne.mpr he
        unfold firstStep
        split <;> simp [Std.HashMap.getElem?_insert, hp, ha, h]

theorem lookup_eq_find {β : Type} : ∀ (xs : List (Address × β)) (a : Address),
    xs.lookup a = (xs.find? (·.1 == a)).map (·.2)
  | [], _ => rfl
  | (b, v) :: xs, a => by
    rw [List.lookup_cons, List.find?_cons]
    by_cases h : a = b
    · subst h; simp
    · have h1 : (a == b) = false := beq_eq_false_iff_ne.mpr h
      have h2 : (b == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
      simp only [h1, h2]
      exact lookup_eq_find xs a

/-- **A cited blob reads alike in the closure context**: the artifact's, if it has one
there, and otherwise the fallback's first. -/
theorem blob_closure {ixe : Ixon.Env} {tA : RoleTable} {preA : Prelude .anon} {order : List Address}
    {x : Address} {bs : ByteArray} (hixe : ixe.blobs.get? x = none ∨ ixe.blobs.get? x = some bs)
    (hfirst : firstBlob preA.blobs x = some bs) :
    (Ix.Cert.closureContext ixe tA preA order).blob x = some bs := by
  change ((Ix.Cert.blobsOf ixe order ++ preA.blobs).foldl firstStep {})[x]? = some bs
  rw [firstFold_get, lookup_eq_find, List.find?_append]
  simp only [Std.HashMap.getElem?_empty]
  cases hf : (Ix.Cert.blobsOf ixe order).find? (·.1 == x) with
  | some e =>
    obtain ⟨y, v⟩ := e
    have hy0 := List.find?_some hf
    have hy : y = x := beq_iff_eq.mp hy0
    subst hy
    have hmem := List.mem_of_find?_eq_some hf
    unfold Ix.Cert.blobsOf at hmem
    have hm := (List.mem_filter.mp hmem).1
    have hget : ixe.blobs.get? y = some v := by
      rw [Std.HashMap.get?_eq_getElem?]
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm
    rcases hixe with hn | hs
    · rw [hn] at hget; cases hget
    · rw [hs] at hget; cases hget; rfl
  | none =>
    simp only [Option.none_or]
    unfold firstBlob at hfirst
    exact hfirst

/-! ## The evidence lists -/

theorem find?_map_fst {α β : Type} {F : Role × α → Role × β} {r : Role} {l : List (Role × α)}
    (hF : ∀ p, (F p).1 = p.1) : (l.map F).find? (·.1 == r) = (l.find? (·.1 == r)).map F := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.find?_cons, hF]
    split
    · rfl
    · exact ih

/-- The reader's resolution of one table entry (`evidenceOf`'s). -/
def readEntry (cx : Ctx .anon) (st : State .anon) : Evidence Address →
    Option (Evidence (CName .anon × CExpr .anon))
  | .defeq => some .defeq
  | .proof a => (evidenceValue? cx st a).map .proof

/-- The bundle's reading of one table entry (`expectedOf`'s). -/
def bundleEntry (b : Bundle) : Evidence Address → Option (Evidence (CName .source × CExpr .source))
  | .defeq => some .defeq
  | .proof a => do
    let c ← bundleRecord b a
    let n ← b.names[a]?
    let p ← (b.proofOf c).toOption
    pure (.proof (ofLeanName n, p))

/-- One entry renamed onto the representatives (`evidenceSubst`'s). -/
def substEntry (ρ : Ix.LeanIngress.FiberMap) :
    Evidence (CName .source × CExpr .source) → Evidence (CName .source × CExpr .source)
  | .defeq => .defeq
  | .proof (k, p) => .proof (Ix.LeanIngress.Key.subst ρ k, Ix.LeanIngress.Expr.substKeys ρ p)

/-- The reader's evidence at a role: the table's entries, each proof resolved. -/
theorem evidenceOf_of (cx : Ctx .anon) (st : State .anon) (t : RoleTable) (r : Role) :
    (evidenceOf cx st t).of r = ((tableOf t r).mapM (readEntry cx st)).getD [] := by
  unfold evidenceOf Evidences.of tableOf
  rw [find?_map_fst]
  · cases t.evidence.toList.find? (·.1 == r) with
    | none => rfl
    | some p => rfl
  · intro p; rfl

theorem expectedOf_eq (b : Bundle) (t : RoleTable) (r : Role) :
    expectedOf b t r = (tableOf t r).mapM (bundleEntry b) := by
  unfold expectedOf
  rfl

/-- Quotient Source's evidence at a role, renamed onto the representatives. -/
theorem evidenceSubst_of (ρ : Ix.LeanIngress.FiberMap) (ev : Evidences .source) (r : Role) :
    (Ix.LeanIngress.evidenceSubst ρ ev).of r = (ev.of r).map (substEntry ρ) := by
  unfold Ix.LeanIngress.evidenceSubst Evidences.of
  rw [find?_map_fst]
  · cases ev.find? (·.1 == r) with
    | none => rfl
    | some p => rfl
  · intro p; rfl

/-- **At a role whose proof records read as the bundle's proofs, renamed, the two evidences
have the same entries up to the theorems' keys.** -/
theorem strip_eq {cx : Ctx .anon} {st : State .anon} {b : Bundle}
    {ρ : Ix.LeanIngress.FiberMap} {f : Mode.Id .source → Mode.Id .anon} :
    ∀ (l : List (Evidence Address)) (evr : List (Evidence (CName .source × CExpr .source))),
      l.mapM (bundleEntry b) = some evr →
      (∀ a, Evidence.proof a ∈ l → ∀ c p, bundleRecord b a = some c → b.proofOf c = .ok p →
        ∃ k, evidenceValue? cx st a = some (k, renameExpr ρ f p)) →
      ∃ evr', l.mapM (readEntry cx st) = some evr' ∧
        evr'.map strip = ((evr.map (substEntry ρ)).map (Evidence.mapKeys f)).map strip
  | [], evr, h, _ => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | e :: l, evr, h, hread => by
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases he : bundleEntry b e with
    | none => rw [he] at h; cases h
    | some x =>
      rw [he] at h
      simp only at h
      cases hl : l.mapM (bundleEntry b) with
      | none => rw [hl] at h; cases h
      | some evl =>
        rw [hl] at h
        simp only [pure, Option.some.injEq] at h
        subst h
        obtain ⟨evr', h1, h2⟩ := strip_eq l evl hl (fun a ha => hread a (List.mem_cons_of_mem _ ha))
        cases e with
        | defeq =>
          simp only [bundleEntry, Option.some.injEq] at he
          subst he
          refine ⟨.defeq :: evr', ?_, ?_⟩
          · simp only [List.mapM_cons, readEntry, bind, Option.bind, h1, pure]
          · simp only [List.map_cons, h2]; rfl
        | proof a =>
          cases hc : bundleRecord b a with
          | none => simp [bundleEntry, hc] at he
          | some c =>
            cases hn : b.names[a]? with
            | none => simp [bundleEntry, hc, hn] at he
            | some n =>
              cases hp : b.proofOf c with
              | error err => simp [bundleEntry, hc, hn, hp, Except.toOption] at he
              | ok p =>
                simp [bundleEntry, hc, hn, hp, Except.toOption] at he
                subst he
                obtain ⟨k, hk⟩ := hread a (List.mem_cons_self ..) c p hc hp
                refine ⟨.proof (k, renameExpr ρ f p) :: evr', ?_, ?_⟩
                · simp only [List.mapM_cons, readEntry, bind, Option.bind, hk, Option.map_some, h1, pure]
                · simp only [List.map_cons, h2]; rfl


/-! ## The operations a run installs lie in the closure -/

section Origin

variable {md : Mode}

open Ix.Cert.ReaderUnits in
/-- A read inductive block is its lowering's result. -/
theorem readInductive_lower {cx : Ctx md} {st : State md} {owner : Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} {r : Read md} (h : readInductive cx st owner c ms = .ok r) :
    ∃ st' rb, lowerInductive st' rb = .ok r := by
  unfold readInductive at h
  split at h
  · dsimp only at h
    rcases ite_ok h with h | h
    · split at h
      · rcases ite_ok h with h | h
        · exact (fail_bind h).elim
        · rcases ite_ok h with h | h
          · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
            obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
            obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
            exact ⟨_, _, h⟩
          · exact (fail_bind h).elim
      · exact (throw_ok h).elim
    · exact (fail_bind h).elim
  · exact (throw_ok h).elim

open Ix.Cert.ReaderUnits in
/-- **A record's generated prefix is generated**: only an inductive block's lowering
generates declarations, and its generated ones are (`lowerInductive_generated`). -/
theorem readRecord_generated {cx : Ctx md} {st : State md} {owner : Address} {c : Ixon.Constant}
    {r : Read md} (h : readRecord cx st owner c = .ok r) :
    ∀ d ∈ r.decls.toList.take r.generated, d.isGenerated = true := by
  unfold readRecord at h
  split at h
  case h_1 | h_2 | h_3 | h_4 =>
    dsimp only at h
    rcases ite_ok h with h | h
    · exact (fail_bind h).elim
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp
  case h_5 =>
    obtain ⟨⟨decl, rw⟩, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  case h_6 =>
    dsimp only at h
    rcases ite_ok h with h | h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp
    · exact (fail_bind h).elim
  case h_7 =>
    dsimp only at h
    rcases ite_ok h with h | h
    · exact (fail_bind h).elim
    · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp
  case h_8 =>
    obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  case h_9 =>
    dsimp only at h
    rcases ite_ok h with h | h
    · rcases ite_ok h with h | h
      · exact (fail_bind h).elim
      · obtain ⟨_, _, hl⟩ := readInductive_lower h
        exact Ix.Cert.SourceNames.lowerInductive_generated hl
    · rcases ite_ok h with h | h
      · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp
      · rcases ite_ok h with h | h
        · split at h
          · exact (fail_bind h).elim
          · split at h
            · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              simp
            · exact (throw_ok h).elim
        · exact (throw_ok h).elim

/-- A member key that is a role's comes from the role bindings. -/
theorem memberKey_role {cx : Ctx md} {ref : ConstRef Address} {s : Role}
    (h : cx.memberKey ref = .ok (Key.role s)) : ∃ q : ConstRef Address, cx.roles.names[q]? = some (Key.role (md := md) s) := by
  unfold Ctx.memberKey at h
  cases hn : cx.roles.names[ref]? with
  | some k =>
    rw [hn] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨ref, by rw [hn, h]⟩
  | none =>
    rw [hn] at h
    simp only [bind, Except.bind] at h
    cases ha : cx.addressOf ref with
    | error e => rw [ha] at h; cases h
    | ok a =>
      rw [ha] at h
      simp only at h
      cases hb : cx.keys.byAddress[a]? with
      | some k =>
        rw [hb] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hs := cx.keys.byAddress_sound a _ hb
        unfold keyOfAddress at hs
        cases hr : resolve cx.store a with
        | none => simp [hr] at hs
        | some R =>
          simp only [hr, Option.bind_eq_bind, Option.bind_some] at hs
          cases hR : cx.roles.names[R]? with
          | some k' =>
            rw [hR] at hs
            exact ⟨R, by rw [hR]; exact hs⟩
          | none =>
            rw [hR] at hs
            cases hi : Mode.addressId? md a <;> simp [hi] at hs
      | none =>
        rw [hb] at h
        cases hi : Mode.addressId? md a <;>
          simp [hi, declined, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h

/-- **A role's key among a stream's declarations comes from the role bindings.** -/
theorem roleKey_origin {cx : Ctx md} {st st' : State md} {records : List (Address × Ixon.Constant)}
    {out : Array (CDecl md)} (h : StreamRead cx st records st' out) {d : CDecl md} (hd : d ∈ out)
    {s : Role} (hs : Key.role s ∈ d.names) : ∃ q : ConstRef Address, cx.roles.names[q]? = some (Key.role (md := md) s) := by
  obtain ⟨rs, hall, flat⟩ := Ix.Cert.ReaderUnits.stream_lowerings h
  have hd' : d ∈ (rs.map fun r => r.decls.toList).flatten := by
    rw [← flat]; exact Array.mem_toList_iff.mpr hd
  obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
  obtain ⟨x, -, st₀, hread⟩ := Ix.Cert.FallbackStore.forall₂_mem_right hall r hr
  have gen := readRecord_generated hread
  rcases Ix.Cert.ReaderUnits.readRecord_lowering hread with ⟨-, hk⟩ | ⟨gens, d', hdecls, hg, hk⟩
  · obtain ⟨ref, -, hm⟩ := hk d hdl _ hs
    exact memberKey_role hm
  · rw [hdecls] at hdl
    rcases List.mem_append.mp hdl with hgen | hlast
    · exfalso
      have hgd : d.isGenerated = true := gen d (by rw [hdecls, hg, List.take_left]; exact hgen)
      unfold Declaration.isGenerated at hgd
      have := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hgd).2) _ hs
      cases this
    · rw [List.mem_singleton] at hlast
      subst hlast
      obtain ⟨ref, -, hm⟩ := hk _ hs
      exact memberKey_role hm

end Origin

/-- An operation's key is its role's. -/
theorem opRole_some {md : Mode} {c : Key md} {r : Role} (h : opRole? c = some r) :
    c = .role r ∧ r ∈ opRoles := by
  cases c with
  | id i => simp [opRole?] at h
  | aux k d => simp [opRole?] at h
  | role s =>
    cases s <;> simp [opRole?] at h <;> (subst h; exact ⟨rfl, by decide⟩)

/-- **The prelude declares only prelude roles.** -/
theorem prelude_names {md : Mode} {t : RoleTable} {pre : Prelude md} (h : preludeFor t = .ok pre)
    {d : Declaration md} (hd : d ∈ pre.ix.decls.toList) {k : Key md} (hk : k ∈ d.names) :
    ∃ s, k = .role s ∧ s ∈ preludeShape.flatten := by
  unfold preludeFor at h
  obtain ⟨pre', hr, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  obtain ⟨u, hs, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  unfold checkPreludeShape at hs
  dsimp only at hs
  split at hs
  · rename_i heq
    have he := beq_iff_eq.mp heq
    have hm : d.names ∈ pre'.ix.decls.toList.map (·.names) := List.mem_map.mpr ⟨d, hd, rfl⟩
    rw [he] at hm
    obtain ⟨rs, hrs, hnr⟩ := List.mem_map.mp hm
    rw [← hnr] at hk
    obtain ⟨s, hs', rfl⟩ := List.mem_map.mp hk
    exact ⟨s, rfl, List.mem_flatten.mpr ⟨rs, hrs, hs'⟩⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at hs

/-- No operation is a prelude role. -/
theorem op_not_prelude {r : Role} (hr : r ∈ opRoles) : r ∉ preludeShape.flatten := by
  revert r
  decide


/-! ## The transfer -/

/-- The closure context's role bindings are its store's. -/
theorem closure_roles {ixe : Ixon.Env} {tA : RoleTable} {preA : Prelude .anon} {order : List Address} :
    (Ix.Cert.closureContext ixe tA preA order).roles =
      bindingsOf (Ix.Cert.closureContext ixe tA preA order).store tA := rfl

theorem store_of_resolve {s : Store} {x : Address} {R : ConstRef Address} (h : resolve s x = some R) :
    ∃ c, s x = some c := by
  unfold resolve at h
  cases hs : s x with
  | none => simp [hs] at h
  | some c => exact ⟨c, rfl⟩

theorem compiledReach_trans {ixe : Ixon.Env} {S : Address → Prop} {a : Address}
    (ha : Ix.Cert.CompiledReach ixe S a) :
    ∀ {x}, Ix.Cert.CompiledReach ixe (· = a) x → Ix.Cert.CompiledReach ixe S x := by
  intro x hx
  induction hx with
  | seed hs _ => subst hs; exact ha
  | step _ e ih => exact .step ih e
  | ground _ e ih => exact .ground ih e
  | recursor _ e ih => exact .recursor ih e

/-- **The role table's evidence passes where quotient Source's does** (the obligation
`Ix.Cert.Obligation.EvidenceTransfer`). -/
theorem evidenceTransfer : Ix.Cert.Obligation.EvidenceTransfer := by
  intro env roots sub ixe failures t envQ pre ds b binding tA preA order st' decls envR P hpre prepared hb
    hbind hadm hprelude corder reads streams runR
  have same : tA = t := Ix.Cert.ReadingKeys.admitBinding_default P.table hbind hadm
  subst same
  have checked : tA.check = .ok () := Ix.Cert.defaultTable_check P.table
  have agree : Agree ixe tA b tA preA := P.quotient P.table b binding tA preA hb hbind hadm hprelude
  apply acceptsRef_coversOn _ runR
  intro F
  apply coversOn_of_strip
  rintro c r ⟨d, hd, hc⟩ hr
  obtain ⟨rfl, hop⟩ := opRole_some hr
  rw [← streams] at hd
  obtain ⟨extra, hextra, hperm⟩ := Ix.Kernel.Frontend.preparePrelude_perm preA.ix decls
  rcases List.mem_append.mp (hperm.mem_iff.mp hd) with hdec | hpd
  · -- the operation is read from the closure
    obtain ⟨q, hq⟩ := roleKey_origin reads (Array.mem_toList_iff.mp hdec) hc
    obtain ⟨A, hbound, hres⟩ := Ix.Cert.ReaderKeys.bindings_role_origin _ tA hq
    have haddr : tA.addressOf? r = some A := Ix.Cert.ReadingKeys.addressOf_of_bound checked hbound
    have hfbA : fallbackStore preA A = none := agree.opAddr r hop A haddr
    have hstoreA : ∃ cA, (Ix.Cert.closureContext ixe tA preA order).store A = some cA :=
      store_of_resolve hres
    obtain ⟨cA, hcA⟩ := hstoreA
    have hAo : A ∈ order := by
      by_contra hno
      rw [store_off hno, hfbA] at hcA
      cases hcA
    have hrecA : (Ix.Cert.recordAt ixe A).isSome := by
      rw [store_order hAo] at hcA
      unfold fullStore at hcA
      cases hra : Ix.Cert.recordAt ixe A with
      | none => rw [hra] at hcA; simp [hfbA] at hcA
      | some _ => rfl
    have hreachA : Ix.Cert.CompiledReach ixe (Ix.Cert.Seed ixe sub) A := (corder.complete A).mp hAo
    -- the two evidences at the operation
    rw [Ix.Kernel.Evidences.mapKeys_of]
    unfold Ix.Cert.sourceEvidence
    rw [evidenceSubst_of, evidenceOf_of]
    have hexp := agree.shape r hop
    rw [expectedOf_eq] at hexp
    obtain ⟨evr', h1, h2⟩ := strip_eq (cx := Ix.Cert.closureContext ixe tA preA order) (st := st')
      (ρ := Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap tA))
      (f := Ix.LeanIngress.evAddr ixe b) _ _ hexp (by
        intro a ha cr p hcr hp
        have hpa : a ∈ proofAddrs tA r := List.mem_filterMap.mpr ⟨_, ha, rfl⟩
        obtain ⟨cr', dr, p', T, hcr', hdr, hthm, hfb, -, hp', hT, hproj, hcited, hblobs⟩ :=
          agree.records r hop A haddr hrecA a hpa
        rw [hcr] at hcr'
        cases hcr'
        rw [hp] at hp'
        cases hp'
        refine evidenceValue_of_bundle (fallback_sub agree.fallback hfb) hdr hthm ?_ ?_ hp hT hproj
        · intro x n hx hn
          obtain ⟨R, hfull, hkfull, huniq, hreach⟩ := hcited x hx n hn
          have hcs : resolve (Ix.Cert.closureContext ixe tA preA order).store x = some R := by
            rcases hreach with hin | hfbx
            · obtain ⟨hcr, hrx⟩ := hin A haddr
              have hxS := compiledReach_trans hreachA hcr
              have hxo : x ∈ order := (corder.complete x).mpr hxS
              obtain ⟨rx, hrx'⟩ := Option.isSome_iff_exists.mp hrx
              have e1 : (Ix.Cert.closureContext ixe tA preA order).store x = some rx := by
                rw [store_order hxo]; simp [fullStore, hrx']
              have e2 : fullStore ixe preA x = some rx := by simp [fullStore, hrx']
              rw [resolve_congr e1 e2 ?_]
              · exact hfull
              · by_cases hown : Ix.Cert.ownerOf x rx = x
                · rw [hown, e1, e2]
                · have hedge : Ix.Cert.RecordEdge ixe x (Ix.Cert.ownerOf x rx) :=
                    ⟨rx, hrx', .inl ⟨rfl, hown⟩⟩
                  exact store_order ((corder.complete _).mpr (.step hxS hedge))
            · exact resolve_mono (fun a c h => fallback_sub agree.fallback h) hfbx
          apply Ix.Kernel.Reader.Ctx.keyAt_eq_ok.mpr
          rw [closure_roles, keyOfAddress_closure (fun a c h => store_sub agree.fallback h) hcs hfull huniq]
          exact hkfull
        · intro x bs hx hbs
          obtain ⟨hixe, hfirst⟩ := hblobs x hx bs hbs
          exact blob_closure hixe hfirst)
    rw [h1]
    exact h2.symm
  · -- a prelude declaration names no operation
    exfalso
    obtain ⟨s, hs, hmem⟩ := prelude_names hprelude (hextra d hpd) hc
    cases hs
    exact op_not_prelude hop hmem

end Ix.Cert.EvidenceTransfer

/-- info: 'Ix.Cert.EvidenceTransfer.evidenceTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.EvidenceTransfer.evidenceTransfer
