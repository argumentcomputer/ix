import Ix.LeanIngress.Rename
import IxC.Kernel.Verify.Frontend.InModelProjRec
import IxC.Kernel.Verify.Frontend.InModelMutualRename
import IxC.Kernel.Ixon.Prelude

/-! # The committed prelude read at both modes agrees under every renaming

Quotient Source reads the committed prelude in Source mode, the Ixon reader in anonymous
mode (`Ix.Kernel.Reader.preludeFor`). Both readings name only roles, so a renaming of
input names changes neither. This module states that as a check on anonymous data,
decided at run time on the pinned configuration (`preludeAgreeB`): the Source reading's
declarations and reader state name no input (`Key.goodB` at no name), and the anonymous
reading's are the Source reading's with names erased (`eraseId`, a constant renaming).
It then lifts the check to every renaming (`preludeAgree_decls`, `preludeAgree_state`),
through congruence lemmas: a renaming acts on a term that names no input as every other
renaming does.

Nothing universally quantified is decided at run time: the check reads two concrete
readings, and the lift is a theorem. -/

namespace Ix.Cert.PreludeAgree

open Ix.Kernel Ix.Kernel.Reader
open Ix.Kernel.Frontend (ProjRecOwner)
open Ix.Kernel.Frontend.InModel (BlockRec IndTypeRec IndCtorRec IndRecRec)

/-! ## Renamings agree on what names no input -/

section Congr

variable {md md' : Mode} {P : KeyScope md} {f g : md.Id → md'.Id}

theorem key_map_congr (hfg : ∀ i, P i → f i = g i) : ∀ {k : Key md}, k.Good P → k.map f = k.map g
  | .id i, h => by simp only [Key.map]; rw [hfg i h]
  | .role _, _ => rfl
  | .aux k _, h => by simp only [Key.map]; rw [key_map_congr hfg (k := k) h]

theorem expr_mapKeys_congr (hfg : ∀ i, P i → f i = g i) : ∀ (e : Ix.Kernel.Expr md), e.Good P → e.mapKeys f = e.mapKeys g
  | .bvar _, _ => rfl
  | .fvar _ t, h => by simp only [Ix.Kernel.Expr.mapKeys]; rw [expr_mapKeys_congr hfg t h]
  | .sort _, _ => rfl
  | .const _ _, h => by simp only [Ix.Kernel.Expr.mapKeys]; rw [key_map_congr hfg h]
  | .app a b, h => by
    simp only [Ix.Kernel.Expr.mapKeys]; rw [expr_mapKeys_congr hfg a h.1, expr_mapKeys_congr hfg b h.2]
  | .lam t b _, h => by
    simp only [Ix.Kernel.Expr.mapKeys]; rw [expr_mapKeys_congr hfg t h.1, expr_mapKeys_congr hfg b h.2]
  | .forallE t b _, h => by
    simp only [Ix.Kernel.Expr.mapKeys]; rw [expr_mapKeys_congr hfg t h.1, expr_mapKeys_congr hfg b h.2]
  | .letE t v b _, h => by
    simp only [Ix.Kernel.Expr.mapKeys]
    rw [expr_mapKeys_congr hfg t h.1, expr_mapKeys_congr hfg v h.2.1, expr_mapKeys_congr hfg b h.2.2]
  | .lit _, _ => rfl
  | .proj _ _ e, h => by
    simp only [Ix.Kernel.Expr.mapKeys]; rw [key_map_congr hfg h.1, expr_mapKeys_congr hfg e h.2]

theorem exprs_map_congr (hfg : ∀ i, P i → f i = g i) {es : List (Ix.Kernel.Expr md)} (h : ∀ e ∈ es, e.Good P) :
    es.map (Ix.Kernel.Expr.mapKeys f) = es.map (Ix.Kernel.Expr.mapKeys g) :=
  List.map_congr_left fun e he => expr_mapKeys_congr hfg e (h e he)

theorem cval_mapKeys_congr (hfg : ∀ i, P i → f i = g i) {cv : Ix.Kernel.ConstantVal md} (h : cv.Good P) :
    cv.mapKeys f = cv.mapKeys g := by
  obtain ⟨n, l, t⟩ := cv
  simp only [Ix.Kernel.ConstantVal.mapKeys]
  rw [key_map_congr hfg h.1, expr_mapKeys_congr hfg t h.2]

theorem rule_mapKeys_congr (hfg : ∀ i, P i → f i = g i) {r : RecRule md} (h : r.Good P) :
    r.mapKeys f = r.mapKeys g := by
  obtain ⟨hc, hfire, hr⟩ := h
  have hfire' : r.fire.mapKeys f = r.fire.mapKeys g := by
    cases hk : r.fire with
    | inert => rfl
    | plain => rfl
    | nested lvls pins =>
      rw [hk] at hfire
      simp only [RecRuleFire.mapKeys]
      rw [exprs_map_congr hfg hfire]
  simp only [RecRule.mapKeys]
  rw [key_map_congr hfg hc, hfire', expr_mapKeys_congr hfg _ hr]

theorem rules_map_congr (hfg : ∀ i, P i → f i = g i) {rs : List (RecRule md)} (h : ∀ r ∈ rs, r.Good P) :
    rs.map (RecRule.mapKeys f) = rs.map (RecRule.mapKeys g) :=
  List.map_congr_left fun r hr => rule_mapKeys_congr hfg (h r hr)

theorem caps_mapKeys_congr (hfg : ∀ i, P i → f i = g i) {c : IndCaps md} (h : c.Good P) :
    c.mapKeys f = c.mapKeys g := by
  simp only [IndCaps.mapKeys]
  congr 1
  cases hk : c.etaCtor with
  | none => rfl
  | some k => simp only [Option.map_some]; rw [key_map_congr hfg (h k hk)]

theorem cinfo_mapKeys_congr (hfg : ∀ i, P i → f i = g i) {c : Ix.Kernel.ConstantInfo md} (h : c.Good P) :
    c.mapKeys f = c.mapKeys g := by
  cases c with
  | axiomInfo v => simp only [Ix.Kernel.ConstantInfo.mapKeys]; rw [cval_mapKeys_congr hfg h]
  | defnInfo v e _ =>
    simp only [Ix.Kernel.ConstantInfo.mapKeys]; rw [cval_mapKeys_congr hfg h.1, expr_mapKeys_congr hfg e h.2]
  | thmInfo v e =>
    simp only [Ix.Kernel.ConstantInfo.mapKeys]; rw [cval_mapKeys_congr hfg h.1, expr_mapKeys_congr hfg e h.2]
  | indInfo v caps =>
    simp only [Ix.Kernel.ConstantInfo.mapKeys]
    rw [cval_mapKeys_congr hfg h.1, caps_mapKeys_congr hfg h.2]
  | ctorInfo v _ _ => simp only [Ix.Kernel.ConstantInfo.mapKeys]; rw [cval_mapKeys_congr hfg h]
  | recInfo v _ _ rules =>
    simp only [Ix.Kernel.ConstantInfo.mapKeys]; rw [cval_mapKeys_congr hfg h.1, rules_map_congr hfg h.2]
  | projInfo tbl =>
    simp only [Ix.Kernel.ConstantInfo.mapKeys]
    congr 1
    obtain ⟨hs, hc, hb⟩ := h
    simp only [ProjTable.mapKeys]
    rw [key_map_congr hfg hs, key_map_congr hfg hc]
    congr 1
    exact Array.map_congr_left fun e he => expr_mapKeys_congr hfg e (hb e he)

theorem decl_mapKeys_congr (hfg : ∀ i, P i → f i = g i) {d : Ix.Kernel.Declaration md} (h : d.Good P) :
    d.mapKeys f = d.mapKeys g := by
  cases d with
  | axiomDecl v => simp only [Ix.Kernel.Declaration.mapKeys]; rw [cval_mapKeys_congr hfg h]
  | defnDecl v e _ =>
    simp only [Ix.Kernel.Declaration.mapKeys]; rw [cval_mapKeys_congr hfg h.1, expr_mapKeys_congr hfg e h.2]
  | thmDecl v e =>
    simp only [Ix.Kernel.Declaration.mapKeys]; rw [cval_mapKeys_congr hfg h.1, expr_mapKeys_congr hfg e h.2]
  | opaqueDecl v e =>
    simp only [Ix.Kernel.Declaration.mapKeys]; rw [cval_mapKeys_congr hfg h.1, expr_mapKeys_congr hfg e h.2]
  | basisDecl _ => rfl
  | indDecl block _ =>
    simp only [Ix.Kernel.Declaration.mapKeys]
    rw [List.map_congr_left fun c hc => cinfo_mapKeys_congr hfg (h c hc)]
  | quotDecl _ v => simp only [Ix.Kernel.Declaration.mapKeys]; rw [cval_mapKeys_congr hfg h]

theorem block_mapKeys_congr (hfg : ∀ i, P i → f i = g i) {b : BlockRec md} (h : b.Good P) :
    b.mapKeys f = b.mapKeys g := by
  obtain ⟨ht, hc, hr⟩ := h
  simp only [BlockRec.mapKeys]
  congr 1
  · refine List.map_congr_left fun t htm => ?_
    obtain ⟨hcv, hks⟩ := ht t htm
    simp only [IndTypeRec.mapKeys]
    rw [cval_mapKeys_congr hfg hcv, List.map_congr_left fun k hk => key_map_congr hfg (hks k hk)]
  · refine List.map_congr_left fun c hcm => ?_
    simp only [IndCtorRec.mapKeys]
    rw [cval_mapKeys_congr hfg (hc c hcm)]
  · refine List.map_congr_left fun r hrm => ?_
    obtain ⟨hcv, hrs⟩ := hr r hrm
    simp only [IndRecRec.mapKeys]
    rw [cval_mapKeys_congr hfg hcv, rules_map_congr hfg hrs]

theorem owner_mapKeys_congr (hfg : ∀ i, P i → f i = g i) {o : ProjRecOwner md} (h : o.Good P) :
    o.mapKeys f = o.mapKeys g := by
  obtain ⟨hT, hc, hr, ht⟩ := h
  simp only [ProjRecOwner.mapKeys]
  rw [key_map_congr hfg hT, key_map_congr hfg hc, key_map_congr hfg hr, expr_mapKeys_congr hfg _ ht]

end Congr

/-! ## The check on anonymous data -/

/-- **Names erased**: the constant renaming of Source names into anonymous ones. -/
def eraseId : Mode.Id .source → Mode.Id .anon := fun _ => default

/-- No input name passes. -/
def noId : Ix.Kernel.Name → Bool := fun _ => false

/-- The scope of no input name. -/
abbrev NoIds : KeyScope .source := KeyScope.ofId fun n => noId n = true

theorem noIds_vacuous {f g : Mode.Id .source → Mode.Id .anon} : ∀ i, NoIds i → f i = g i :=
  fun _ h => by simp [NoIds, noId] at h

/-- A renaming of a key that names no input is injective onto it: only that key renames
to its image. -/
theorem key_map_eq_good {f : Mode.Id .source → Mode.Id .anon} {k k' : Key .source} (h' : k'.Good NoIds) :
    k.map f = k'.map f → k = k' := by
  induction k' generalizing k with
  | id i => simp [NoIds, noId] at h'
  | role r =>
    intro he
    cases k with
    | id _ => cases he
    | role _ => cases he; rfl
    | aux _ _ => cases he
  | aux b d ih =>
    intro he
    cases k with
    | id _ => cases he
    | role _ => cases he
    | aux kb kd =>
      simp only [Key.map, Key.aux.injEq] at he
      rw [ih h' he.1, he.2]

/-- A term names no input. -/
def exprOk (e : Ix.Kernel.Expr .source) : Bool := (Ix.LeanIngress.Expr.goodBGo noId {} e).1

theorem exprOk_good {e : Ix.Kernel.Expr .source} (h : exprOk e = true) : e.Good NoIds :=
  (Ix.LeanIngress.Expr.goodBGo_spec e Ix.LeanIngress.GoodSeen.empty).2 h

/-- A header names no input. -/
def cvalOk (cv : Ix.Kernel.ConstantVal .source) : Bool := Ix.LeanIngress.Key.goodB noId cv.name && exprOk cv.type

theorem cvalOk_good {cv : Ix.Kernel.ConstantVal .source} (h : cvalOk cv = true) : cv.Good NoIds := by
  obtain ⟨hn, ht⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨Ix.LeanIngress.Key.goodB_spec hn, exprOk_good ht⟩

/-- A recursor rule names no input. -/
def ruleOk (r : RecRule .source) : Bool :=
  Ix.LeanIngress.Key.goodB noId r.ctor && exprOk r.rhs &&
    match r.fire with
    | .nested _ pins => pins.all exprOk
    | _ => true

theorem ruleOk_good {r : RecRule .source} (h : ruleOk r = true) : r.Good NoIds := by
  simp only [ruleOk, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hr⟩, hf⟩ := h
  refine ⟨Ix.LeanIngress.Key.goodB_spec hc, ?_, exprOk_good hr⟩
  cases hk : r.fire with
  | inert => trivial
  | plain => trivial
  | nested lvls pins =>
    rw [hk] at hf
    exact fun e he => exprOk_good (List.all_eq_true.mp hf e he)

/-- A parsed block names no input. -/
def blockOk (b : BlockRec .source) : Bool :=
  b.types.all (fun t => cvalOk t.cv && t.ctors.all (Ix.LeanIngress.Key.goodB noId)) &&
    b.ctors.all (fun c => cvalOk c.cv) && b.recs.all (fun r => cvalOk r.cv && r.rules.all ruleOk)

theorem blockOk_good {b : BlockRec .source} (h : blockOk b = true) : b.Good NoIds := by
  simp only [blockOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨ht, hc⟩, hr⟩ := h
  refine ⟨fun t htm => ?_, fun c hcm => cvalOk_good (hc c hcm), fun r hrm => ?_⟩
  · obtain ⟨hcv, hks⟩ := ht t htm
    exact ⟨cvalOk_good hcv, fun k hk => Ix.LeanIngress.Key.goodB_spec (hks k hk)⟩
  · obtain ⟨hcv, hrs⟩ := hr r hrm
    exact ⟨cvalOk_good hcv, fun x hx => ruleOk_good (hrs x hx)⟩

/-- A projection owner names no input. -/
def ownerOk (o : ProjRecOwner .source) : Bool :=
  Ix.LeanIngress.Key.goodB noId o.T && Ix.LeanIngress.Key.goodB noId o.ctor &&
    Ix.LeanIngress.Key.goodB noId o.recName && exprOk o.recType

theorem ownerOk_good {o : ProjRecOwner .source} (h : ownerOk o = true) : o.Good NoIds := by
  simp only [ownerOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hT, hc⟩, hr⟩, ht⟩ := h
  exact ⟨Ix.LeanIngress.Key.goodB_spec hT, Ix.LeanIngress.Key.goodB_spec hc,
    Ix.LeanIngress.Key.goodB_spec hr, exprOk_good ht⟩

/-- **One field of the two reader states agrees, names erased**: every Source entry's key and
value name no input, the anonymous field holds the erased entry at the erased key, and every
anonymous key is an erased Source key. -/
def fieldAgreeB {α β : Type} [BEq β] (mS : Std.HashMap (Key .source) α) (mA : Std.HashMap (Key .anon) β)
    (ok : α → Bool) (erase : α → β) : Bool :=
  mS.toList.all (fun p => Ix.LeanIngress.Key.goodB noId p.1 && ok p.2 && mA[p.1.map eraseId]? == some (erase p.2)) &&
    mA.toList.all (fun q => mS.toList.any fun p => p.1.map eraseId == q.1)

/-- **The two reader states agree, names erased**, field by field. -/
def stateAgreeB (stS : State .source) (stA : State .anon) : Bool :=
  fieldAgreeB stS.constTypes stA.constTypes (fun v => exprOk v.2) (fun v => (v.1, v.2.mapKeys eraseId)) &&
    fieldAgreeB stS.heights stA.heights (fun _ => true) id &&
    fieldAgreeB stS.indBlocks stA.indBlocks blockOk (BlockRec.mapKeys eraseId) &&
    fieldAgreeB stS.projOwners stA.projOwners ownerOk (ProjRecOwner.mapKeys eraseId) &&
    fieldAgreeB stS.projLevels stA.projLevels (fun _ => true) id

/-- **The two prelude readings agree, names erased**: the Source reading's declarations name
no input, the anonymous reading's are them with names erased, and so are the states. -/
def preludeAgreeB (preS : Prelude .source) (preA : Prelude .anon) : Bool :=
  Ix.LeanIngress.declsGoodB noId preS.ix.decls &&
    preA.ix.decls == preS.ix.decls.map (Ix.Kernel.Declaration.mapKeys eraseId) &&
    stateAgreeB preS.state preA.state

/-! ## The lift to every renaming -/

/-- **A field that agrees, names erased, agrees under every renaming.** -/
theorem fieldAgree_lift {α β : Type} [BEq β] [LawfulBEq β] {mS : Std.HashMap (Key .source) α}
    {mA : Std.HashMap (Key .anon) β} {ok : α → Bool} {erase : α → β}
    (h : fieldAgreeB mS mA ok erase = true) (ren : (Mode.Id .source → Mode.Id .anon) → α → β)
    (hren : ∀ f v, ok v = true → ren f v = erase v) (f : Mode.Id .source → Mode.Id .anon) :
    (∀ k : Key .source, mA[k.map f]? = (mS[k]?).map (ren f)) ∧ ∀ kA b, mA[kA]? = some b → ∃ k : Key .source, kA = k.map f := by
  simp only [fieldAgreeB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨hS, hA⟩ := h
  have entry : ∀ (k : Key .source) (v : α), mS[k]? = some v → ((k.Good NoIds ∧ ok v = true) ∧ mA[k.map eraseId]? = some (erase v)) := by
    intro k v hk
    have := hS (k, v) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hk)
    exact ⟨⟨Ix.LeanIngress.Key.goodB_spec this.1.1, this.1.2⟩, this.2⟩
  have renamed : ∀ k : Key .source, k.Good NoIds → k.map f = k.map eraseId := fun k hk => key_map_congr noIds_vacuous hk
  have back : ∀ (kA : Key .anon) (b : β), mA[kA]? = some b →
      ∃ (k : Key .source) (v : α), mS[k]? = some v ∧ k.map eraseId = kA := by
    intro kA b hb
    obtain ⟨⟨k, v⟩, hmem, he⟩ := hA (kA, b) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hb)
    exact ⟨k, v, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem, he⟩
  refine ⟨fun k => ?_, fun kA b hb => ?_⟩
  · cases hk : mS[k]? with
    | some v =>
      obtain ⟨⟨hg, hok⟩, hA'⟩ := entry k v hk
      rw [renamed k hg, hA', Option.map_some, hren f v hok]
    | none =>
      cases hb : mA[k.map f]? with
      | none => rfl
      | some b =>
        obtain ⟨k', v', hk', he⟩ := back _ b hb
        obtain ⟨⟨hg', -⟩, -⟩ := entry k' v' hk'
        rw [← renamed k' hg'] at he
        have := key_map_eq_good hg' he.symm
        subst this
        rw [hk] at hk'
        cases hk'
  · obtain ⟨k, v, hk, he⟩ := back kA b hb
    obtain ⟨⟨hg, -⟩, -⟩ := entry k v hk
    exact ⟨k, by rw [← he, renamed k hg]⟩

/-- **A renaming of reader states**: at every key, the renamed entry, and no other key. -/
structure StateRen (f : Mode.Id .source → Mode.Id .anon) (stS : State .source) (stA : State .anon) : Prop where
  types : ∀ k : Key .source, stA.constTypes[k.map f]? = (stS.constTypes[k]?).map fun v => (v.1, v.2.mapKeys f)
  typesOnly : ∀ kA b, stA.constTypes[kA]? = some b → ∃ k : Key .source, kA = k.map f
  heights : ∀ k : Key .source, stA.heights[k.map f]? = stS.heights[k]?
  heightsOnly : ∀ kA b, stA.heights[kA]? = some b → ∃ k : Key .source, kA = k.map f
  blocks : ∀ k : Key .source, stA.indBlocks[k.map f]? = (stS.indBlocks[k]?).map (BlockRec.mapKeys f)
  blocksOnly : ∀ kA b, stA.indBlocks[kA]? = some b → ∃ k : Key .source, kA = k.map f
  owners : ∀ k : Key .source, stA.projOwners[k.map f]? = (stS.projOwners[k]?).map (ProjRecOwner.mapKeys f)
  ownersOnly : ∀ kA b, stA.projOwners[kA]? = some b → ∃ k : Key .source, kA = k.map f
  levels : ∀ k : Key .source, stA.projLevels[k.map f]? = stS.projLevels[k]?
  levelsOnly : ∀ kA b, stA.projLevels[kA]? = some b → ∃ k : Key .source, kA = k.map f

/-- **The two prelude readings' states are renamings of each other under every renaming.** -/
theorem preludeAgree_state {preS : Prelude .source} {preA : Prelude .anon}
    (h : preludeAgreeB preS preA = true) (f : Mode.Id .source → Mode.Id .anon) :
    StateRen f preS.state preA.state := by
  simp only [preludeAgreeB, stateAgreeB, Bool.and_eq_true] at h
  obtain ⟨-, ⟨⟨⟨⟨hT, hH⟩, hB⟩, hO⟩, hL⟩⟩ := h
  obtain ⟨types, typesOnly⟩ := fieldAgree_lift hT (fun f v => (v.1, v.2.mapKeys f))
    (fun f v hv => by rw [expr_mapKeys_congr noIds_vacuous v.2 (exprOk_good hv)]) f
  obtain ⟨heights, heightsOnly⟩ := fieldAgree_lift hH (fun _ v => v) (fun _ _ _ => rfl) f
  obtain ⟨blocks, blocksOnly⟩ := fieldAgree_lift hB (fun f b => BlockRec.mapKeys f b)
    (fun f b hb => block_mapKeys_congr noIds_vacuous (blockOk_good hb)) f
  obtain ⟨owners, ownersOnly⟩ := fieldAgree_lift hO (fun f o => ProjRecOwner.mapKeys f o)
    (fun f o ho => owner_mapKeys_congr noIds_vacuous (ownerOk_good ho)) f
  obtain ⟨levels, levelsOnly⟩ := fieldAgree_lift hL (fun _ v => v) (fun _ _ _ => rfl) f
  exact ⟨types, typesOnly, fun k => by rw [heights k, Option.map_id'], heightsOnly, blocks, blocksOnly,
    owners, ownersOnly, fun k => by rw [levels k, Option.map_id'], levelsOnly⟩

/-- **The two prelude readings' declarations are renamings of each other under every
renaming.** -/
theorem preludeAgree_decls {preS : Prelude .source} {preA : Prelude .anon}
    (h : preludeAgreeB preS preA = true) (f : Mode.Id .source → Mode.Id .anon) :
    preA.ix.decls = preS.ix.decls.map (Ix.Kernel.Declaration.mapKeys f) := by
  simp only [preludeAgreeB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hgood, hdecls⟩, -⟩ := h
  rw [hdecls]
  exact Array.map_congr_left fun d hd =>
    (decl_mapKeys_congr noIds_vacuous (Ix.LeanIngress.declsGoodB_good hgood d hd)).symm

end Ix.Cert.PreludeAgree
