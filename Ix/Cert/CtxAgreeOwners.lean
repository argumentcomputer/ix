import Ix.Cert.CtxAgreeProj
import IxC.Kernel.Verify.Rename.Ind3

/-! # Projection owners under a scoped injective renaming

The owner constructor uses two recognition gates and a candidate selection
loop. `structShape_mapKeys` and `structPartsCore_isSome_mapKeys` preserve the
direct-structure gate; the existing nativeParts?_map handles the native gate.
Recursion flags, constructor lookup and recursor positions are preserved,
so `ownersOf_mapKeys` transports exactly the list lowerInductive constructs.
`lowerInductive_owners_mapKeys` exposes the result at successful lowerings.

This closes the owner-construction obligation left by CtxAgreeProj. It does
not derive whole-stream ProjectionAgree or target prefix preservation, and
adds no final compiler-correctness premise.
-/

namespace Ix.Cert.CtxAgree

open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Frontend

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}

private theorem boolAnd_congr {a b c d : Bool} (h : a = b) (h' : c = d) :
    (a && c) = (b && d) := by cases h; cases h'; rfl

private theorem if_isSome_congr {α β : Type} {p q : Bool} {a : Option α} {b : Option β}
    (h : p = q) (hab : a.isSome = b.isSome) :
    (if p then a else none).isSome = (if q then b else none).isSome := by
  cases h
  cases p
  · rfl
  · exact hab

theorem structShape_mapKeys (hf : InjOn f P) {T C : Key md} (hT : T.Good P) (hC : C.Good P)
    (lps : List LevelParam) (elim : LevelParam) (large : Bool) (nP nF : Nat)
    {tty cty rty : CExpr md} (hct : cty.Good P) (hrt : rty.Good P) :
    structShape (T.map f) (C.map f) lps elim large nP nF
      (tty.mapKeys f) (cty.mapKeys f) (rty.mapKeys f) =
      structShape T C lps elim large nP nF tty cty rty := by
  unfold structShape
  simp only [Expr.stripPis_mapKeys]
  cases ht : tty.stripPis nP with
  | none => rfl
  | some p =>
    obtain ⟨tbs, tbody⟩ := p
    cases tbody <;> try rfl
    case sort s =>
      cases hc : cty.stripPis (nP + nF) with
      | none => rfl
      | some p =>
        obtain ⟨cbs, cbody⟩ := p
        cases hr : rty.stripPis (nP + 3) with
        | none => rfl
        | some p =>
          obtain ⟨rbs, rbody⟩ := p
          have hcb := (Expr.stripPis_good hct hc).2
          obtain ⟨hrbs, hrb⟩ := Expr.stripPis_good hrt hr
          simp only [Expr.mapTele, Option.map_some, Expr.mapKeys]
          rw [structFam_map, Expr.mapKeys_beq hf hcb (structFam_good hT _ _ _)]
          have result : (rbody.mapKeys f == (.app (.bvar 2) (.bvar 0) : CExpr md')) =
              (rbody == (.app (.bvar 2) (.bvar 0) : CExpr md)) := by
            simpa only [Expr.mapKeys] using Expr.mapKeys_beq hf hrb
              (show (.app (.bvar 2) (.bvar 0) : CExpr md).Good P from ⟨trivial, trivial⟩)
          rw [result]
          have motive :
              (match (Expr.mapBinders f rbs)[nP]? with
              | some (.forallE mmaj (.sort s') _, _) =>
                (if large then s' == Ix.Kernel.Level.param elim else s' == Ix.Kernel.Level.zero) &&
                  mmaj == structFam (T.map f) lps nP 0
              | _ => false) =
              (match rbs[nP]? with
              | some (.forallE mmaj (.sort s') _, _) =>
                (if large then s' == Ix.Kernel.Level.param elim else s' == Ix.Kernel.Level.zero) &&
                  mmaj == structFam T lps nP 0
              | _ => false) := by
            simp only [Expr.mapBinders, List.getElem?_map]
            cases hm : rbs[nP]? with
            | none => rfl
            | some p =>
              obtain ⟨expr, annotation⟩ := p
              have hg := hrbs _ (List.mem_of_getElem? hm)
              cases expr <;> try rfl
              case forallE dom body m =>
                cases body <;> try rfl
                case sort s =>
                  simp only [Expr.mapKeys, Option.map_some]
                  rw [structFam_map, Expr.mapKeys_beq hf hg.1 (structFam_good hT _ _ _)]
          have minor :
              (match (Expr.mapBinders f rbs)[nP + 1]? with
              | some (mindom, _) => match mindom.stripPis nF with
                | some (_, mbody) => mbody == Ix.Kernel.Expr.app (.bvar nF) (structCtorSpine (C.map f) lps nP nF)
                | none => false
              | none => false) =
              (match rbs[nP + 1]? with
              | some (mindom, _) => match mindom.stripPis nF with
                | some (_, mbody) => mbody == Ix.Kernel.Expr.app (.bvar nF) (structCtorSpine C lps nP nF)
                | none => false
              | none => false) := by
            simp only [Expr.mapBinders, List.getElem?_map]
            cases hm : rbs[nP + 1]? with
            | none => rfl
            | some p =>
              obtain ⟨dom, annotation⟩ := p
              have hg := hrbs _ (List.mem_of_getElem? hm)
              simp only [Option.map_some, Expr.stripPis_mapKeys]
              cases hp : dom.stripPis nF with
              | none => rfl
              | some p =>
                obtain ⟨bs, body⟩ := p
                have hb := (Expr.stripPis_good hg hp).2
                simp only [Option.map_some, Expr.mapTele]
                rw [structCtorSpine_map]
                exact Expr.mapKeys_beq hf hb
                  (show (Ix.Kernel.Expr.app (.bvar nF) (structCtorSpine C lps nP nF) : CExpr md).Good P from
                    ⟨trivial, structCtorSpine_good hC _ _ _⟩)
          apply boolAnd_congr
          · apply boolAnd_congr
            · apply boolAnd_congr
              · rfl
              · exact motive
            · exact minor
          · simp only [Expr.mapBinders, List.getElem?_map]
            cases hm : rbs[nP + 2]? with
            | none => rfl
            | some p =>
              obtain ⟨dom, annotation⟩ := p
              have hg := hrbs _ (List.mem_of_getElem? hm)
              simp only [Option.map_some]
              rw [structFam_map, Expr.mapKeys_beq hf hg (structFam_good hT _ _ _)]

theorem structRuleBody_good (nF : Nat) : (structRuleBody (md := md) nF).Good P := by
  exact Expr.Good.mkAppN trivial (goodList_bvars _ _)

theorem structPartsCore_three (hf : InjOn f P) {cvT cvC cvR : CVal md} (caps : IndCaps md)
    (nP nF mI rP : Nat) {rule : Ix.Kernel.RecRule md}
    (hT : cvT.Good P) (hC : cvC.Good P) (hR : cvR.Good P) (hRule : rule.Good P) :
    (structPartsCore? ([.indInfo cvT caps, .ctorInfo cvC nP nF, .recInfo cvR mI rP [rule]].map
      (ConstantInfo.mapKeys f))).isSome =
    (structPartsCore? [.indInfo cvT caps, .ctorInfo cvC nP nF, .recInfo cvR mI rP [rule]]).isSome := by
  have ruleBody :
      (match (rule.rhs.mapKeys f).stripLams (nP + 2 + nF) with
      | some (_, body) => body == structRuleBody nF
      | none => false) =
      (match rule.rhs.stripLams (nP + 2 + nF) with
      | some (_, body) => body == structRuleBody nF
      | none => false) := by
    rw [Expr.stripLams_mapKeys]
    cases h : rule.rhs.stripLams (nP + 2 + nF) with
    | none => rfl
    | some p =>
      obtain ⟨bs, body⟩ := p
      have hb := (Expr.stripLams_good hRule.2.2 h).2
      simp only [Option.map_some, Expr.mapTele]
      rw [← structRuleBody_mapKeys (f := f) nF]
      exact Expr.mapKeys_beq hf hb (structRuleBody_good nF)
  have shape : ∀ lps elim large,
      structShape (cvT.name.map f) (cvC.name.map f) lps elim large nP nF
        (cvT.type.mapKeys f) (cvC.type.mapKeys f) (cvR.type.mapKeys f) =
      structShape cvT.name cvC.name lps elim large nP nF cvT.type cvC.type cvR.type :=
    fun lps elim large => structShape_mapKeys hf hT.1 hC.1 lps elim large nP nF hC.2 hR.2
  simp only [List.map_cons, List.map_nil, ConstantInfo.mapKeys]
  unfold structPartsCore?
  simp only [ConstantVal.mapKeys, RecRule.mapKeys, reservedBasisNames_contains_map,
    Key.map_beq hf hRule.1 hC.1]
  apply if_isSome_congr
  · exact boolAnd_congr rfl ruleBody
  · rw [Expr.stripPis_mapKeys]
    cases hty : cvT.type.stripPis nP with
    | none => rfl
    | some p =>
      obtain ⟨bs, body⟩ := p
      cases body <;> try rfl
      case sort s =>
        simp only [Option.map_some, Expr.mapTele, Expr.mapKeys, shape]
        repeat' (first | rfl | split)

/-- The owner gate needs only whether direct structure recognition succeeds;
its record payload need not be added to the transport interface. -/
theorem structPartsCore_isSome_mapKeys (hf : InjOn f P) {block : List (CInfo md)}
    (good : ∀ c ∈ block, c.Good P) :
    (structPartsCore? (block.map (ConstantInfo.mapKeys f))).isSome = (structPartsCore? block).isSome := by
  cases block with
  | nil => rfl
  | cons first rest =>
    cases first <;> try rfl
    case indInfo cvT caps =>
      cases rest with
      | nil => rfl
      | cons second rest =>
        cases second <;> try rfl
        case ctorInfo cvC nP nF =>
          cases rest with
          | nil => rfl
          | cons third rest =>
            cases third <;> try rfl
            case recInfo cvR mI rP rules =>
              cases rest with
              | cons =>
                cases rules with
                | nil => rfl
                | cons rule rest => cases rest <;> rfl
              | nil =>
                cases rules with
                | nil => rfl
                | cons rule rest =>
                  cases rest with
                  | cons => rfl
                  | nil =>
                    have hT := (good (.indInfo cvT caps) (by simp)).1
                    have hC := good (.ctorInfo cvC nP nF) (by simp)
                    have hR := good (.recInfo cvR mI rP [rule]) (by simp)
                    exact structPartsCore_three hf caps nP nF mI rP hT hC hR.1
                      (hR.2 rule (List.mem_singleton_self _))

private abbrev OwnerType (md : Mode) :=
  Key md × List LevelParam × CExpr md × Nat × Nat × List (Key md) × Bool
private abbrev OwnerCtor (md : Mode) := Key md × Nat × CExpr md
private abbrev OwnerRec (md : Mode) := Key md × List LevelParam × CExpr md × Nat × Nat

private def ownerTypeMap (f : md.Id → md'.Id) (x : OwnerType md) : OwnerType md' :=
  (x.1.map f, x.2.1, x.2.2.1.mapKeys f, x.2.2.2.1, x.2.2.2.2.1,
    x.2.2.2.2.2.1.map (Key.map f), x.2.2.2.2.2.2)
private def ownerCtorMap (f : md.Id → md'.Id) (x : OwnerCtor md) : OwnerCtor md' :=
  (x.1.map f, x.2.1, x.2.2.mapKeys f)
private def ownerRecMap (f : md.Id → md'.Id) (x : OwnerRec md) : OwnerRec md' :=
  (x.1.map f, x.2.1, x.2.2.1.mapKeys f, x.2.2.2.1, x.2.2.2.2)
private def OwnerTypeGood (P : KeyScope md) (x : OwnerType md) : Prop :=
  x.1.Good P ∧ x.2.2.1.Good P ∧ ∀ k ∈ x.2.2.2.2.2.1, k.Good P
private def OwnerCtorGood (P : KeyScope md) (x : OwnerCtor md) : Prop :=
  x.1.Good P ∧ x.2.2.Good P

private theorem boolOr_congr {a b c d : Bool} (h : a = b) (h' : c = d) :
    (a || c) = (b || d) := by cases h; cases h'; rfl

private def ownersRecursive (types : List (OwnerType md)) (ctors : List (OwnerCtor md)) : Bool :=
  types.any (·.2.2.2.2.2.2) || ctors.any fun (_, _, cty) =>
    (stripPisAll cty).1.any fun (d, _) => (types.map (·.1)).any fun n => occursConstFast n d

private theorem ownersRecursive_map (hf : InjOn f P)
    {types : List (OwnerType md)} {ctors : List (OwnerCtor md)}
    (ht : ∀ x ∈ types, OwnerTypeGood P x) (hc : ∀ x ∈ ctors, OwnerCtorGood P x) :
    ownersRecursive (types.map (ownerTypeMap f)) (ctors.map (ownerCtorMap f)) =
      ownersRecursive types ctors := by
  unfold ownersRecursive
  simp only [List.any_map]
  apply boolOr_congr rfl
  refine any_congr fun x hx => ?_
  obtain ⟨C, nF, cty⟩ := x
  have cgood := (hc _ hx).2
  simp only [Function.comp_def, ownerCtorMap, ownerTypeMap]
  rw [stripPisAll_mapKeys]
  simp only [Expr.mapTele, Expr.mapBinders, List.any_map, Function.comp_def]
  refine any_congr fun b hb => any_congr fun t hmem => ?_
  rw [occursConstFast_eq, occursConstFast_eq,
    occursConst_mapKeys hf (ht t hmem).1 ((stripPisAll_good cgood).1 b hb)]

private theorem ownerCtors_find_map (hf : InjOn f P) {C : Key md} (hC : C.Good P)
    {ctors : List (OwnerCtor md)} (hc : ∀ x ∈ ctors, OwnerCtorGood P x) :
    ((ctors.map (ownerCtorMap f)).find? (·.1 == C.map f)) =
      (ctors.find? (·.1 == C)).map (ownerCtorMap f) := by
  induction ctors with
  | nil => rfl
  | cons x xs ih =>
    have hx := (hc x List.mem_cons_self).1
    simp only [List.map_cons, List.find?_cons, ownerCtorMap]
    rw [Key.map_beq hf hx hC]
    split
    · rfl
    · exact ih (fun y hy => hc y (List.mem_cons_of_mem _ hy))

private def ownerCandidate (ctors : List (OwnerCtor md)) (recs : List (OwnerRec md))
    (x : OwnerType md × Nat) : Option (ProjRecOwner md) := do
  let (T, lps, tty, nP, nI, cs, _) := x.1
  let [C] := cs | none
  guard (nI == 0)
  let (_, .sort s) ← tty.stripPis nP | none
  guard (Ix.Kernel.Level.isEquiv s .zero != some true)
  let (_, nF, _) ← ctors.find? (·.1 == C)
  let (rn, rlps, rty, nM, nm) ← recs[x.2]?
  guard (rlps.length == lps.length + 1)
  pure ⟨T, lps, nP, C, nF, rn, rlps, rty, nM, nm⟩

private theorem ownerCandidate_map (hf : InjOn f P) {ctors : List (OwnerCtor md)}
    (hc : ∀ x ∈ ctors, OwnerCtorGood P x) (recs : List (OwnerRec md))
    (x : OwnerType md × Nat) (hx : OwnerTypeGood P x.1) :
    ownerCandidate (ctors.map (ownerCtorMap f)) (recs.map (ownerRecMap f)) (ownerTypeMap f x.1, x.2) =
      (ownerCandidate ctors recs x).map (ProjRecOwner.mapKeys f) := by
  obtain ⟨⟨T, lps, tty, nP, nI, cs, recursive⟩, m⟩ := x
  unfold ownerCandidate
  simp only [ownerTypeMap]
  cases cs with
  | nil => rfl
  | cons C rest =>
    cases rest with
    | cons => rfl
    | nil =>
      have hC : C.Good P := hx.2.2 C (List.mem_singleton_self _)
      by_cases hi : (nI == 0) = true
      · simp only [List.map_cons, List.map_nil, guard, hi, ↓reduceIte, pure, bind, Option.bind]
        rw [Expr.stripPis_mapKeys]
        cases ht : tty.stripPis nP with
        | none => rfl
        | some p =>
          obtain ⟨bs, body⟩ := p
          cases body <;> try rfl
          case sort s =>
            simp only [Option.map_some, Expr.mapTele, Expr.mapKeys]
            by_cases hs : (Ix.Kernel.Level.isEquiv s .zero != some true) = true
            · simp only [hs, ↓reduceIte]
              rw [ownerCtors_find_map hf hC hc]
              cases found : ctors.find? (·.1 == C) with
              | none => rfl
              | some p =>
                obtain ⟨name, nF, cty⟩ := p
                simp only [Option.map_some, ownerCtorMap]
                rw [List.getElem?_map]
                cases recFound : recs[m]? with
                | none => rfl
                | some p =>
                  obtain ⟨rn, rlps, rty, nM, nm⟩ := p
                  simp only [Option.map_some, ownerRecMap]
                  by_cases hl : (rlps.length == lps.length + 1) = true
                  · simp only [hl, ↓reduceIte]; rfl
                  · simp only [hl]; rfl
            · simp only [hs]; rfl
      · simp only [List.map_cons, List.map_nil, guard, hi, pure, bind, Option.bind]
        rfl

private theorem filterMap_congrOn {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMap_cons, List.filterMap_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem projRecOwners_eq (block : List (CInfo md)) (types : List (OwnerType md))
    (ctors : List (OwnerCtor md)) (recs : List (OwnerRec md)) :
    projRecOwners block types ctors recs =
      if (structPartsCore? block).isSome && !ownersRecursive types ctors then []
      else if (nativeParts? ((types.head?.map (·.2.2.2.1)).getD 0) block).isSome then []
      else types.zipIdx.filterMap (ownerCandidate ctors recs) := rfl

private theorem ownerParams_map (types : List (OwnerType md)) :
    (((types.map (ownerTypeMap f)).head?).map (·.2.2.2.1)).getD 0 =
      (types.head?.map (·.2.2.2.1)).getD 0 := by
  cases types <;> rfl

private theorem projRecOwners_mapKeys (hf : InjOn f P) {block : List (CInfo md)}
    (hb : ∀ c ∈ block, c.Good P) {types : List (OwnerType md)} {ctors : List (OwnerCtor md)}
    (ht : ∀ x ∈ types, OwnerTypeGood P x) (hc : ∀ x ∈ ctors, OwnerCtorGood P x)
    (recs : List (OwnerRec md)) :
    projRecOwners (block.map (ConstantInfo.mapKeys f)) (types.map (ownerTypeMap f))
      (ctors.map (ownerCtorMap f)) (recs.map (ownerRecMap f)) =
      (projRecOwners block types ctors recs).map (ProjRecOwner.mapKeys f) := by
  rw [projRecOwners_eq, projRecOwners_eq, structPartsCore_isSome_mapKeys hf hb,
    ownersRecursive_map hf ht hc, ownerParams_map, nativeParts?_map hf _ hb, Option.isSome_map]
  split
  · rfl
  · split
    · rfl
    · rw [List.zipIdx_map, List.filterMap_map, List.map_filterMap]
      apply filterMap_congrOn
      intro x hx
      exact ownerCandidate_map hf hc recs x (ht x.1 (List.fst_mem_of_mem_zipIdx hx))

/-- The owner list built from a good block is renamed with the block. Both
recognition gates, recursion tests, and indexed candidate selection agree. -/
theorem ownersOf_mapKeys (hf : InjOn f P) {rb : BlockRead md} (hg : rb.Good P) :
    ownersOf (rb.mapKeys f) = (ownersOf rb).map (ProjRecOwner.mapKeys f) := by
  let block : List (CInfo md) := rb.types.toList.map (fun (cv, _, _) => .indInfo cv {}) ++
    rb.ctors.toList.map (fun (cv, nP, nF) => .ctorInfo cv nP nF) ++
    rb.recs.toList.map fun (cv, r, rules) =>
      .recInfo cv (r.params + r.motives + r.minors + r.indices) (r.params + r.motives + r.minors) rules
  let types : List (OwnerType md) := rb.types.toList.zip rb.ctorNames.toList |>.map fun ((cv, nP, nIdx), cs) =>
    (cv.name, cv.levelParams, cv.type, nP, nIdx, cs, isRecOf rb)
  let ctors : List (OwnerCtor md) := rb.ctors.toList.map fun (cv, _, nF) => (cv.name, nF, cv.type)
  let recs : List (OwnerRec md) := rb.recs.toList.map fun (cv, r, _) =>
    (cv.name, cv.levelParams, cv.type, r.motives, r.minors)
  have hb : ∀ c ∈ block, c.Good P := by
    intro c hc
    simp only [block, List.mem_append, List.mem_map] at hc
    rcases hc with (⟨⟨cv, nP, nI⟩, member, rfl⟩ | ⟨⟨cv, nP, nF⟩, member, rfl⟩) |
      ⟨⟨cv, counts, rules⟩, member, rfl⟩
    · exact ⟨hg.1 _ member, by simp [IndCaps.Good]⟩
    · exact hg.2.1 _ member
    · exact hg.2.2.2 _ member
  have ht : ∀ x ∈ types, OwnerTypeGood P x := by
    intro x hx
    simp only [types, List.mem_map] at hx
    obtain ⟨⟨⟨cv, nP, nI⟩, cs⟩, member, rfl⟩ := hx
    have hcv := hg.1 _ (List.of_mem_zip member).1
    exact ⟨hcv.1, hcv.2, hg.2.2.1 cs (List.of_mem_zip member).2⟩
  have hc : ∀ x ∈ ctors, OwnerCtorGood P x := by
    intro x hx
    simp only [ctors, List.mem_map] at hx
    obtain ⟨⟨cv, nP, nF⟩, member, rfl⟩ := hx
    exact hg.2.1 _ member
  have transported := projRecOwners_mapKeys hf hb ht hc recs
  unfold ownersOf
  simp only [isRecOf_mapKeys hf hg]
  simpa only [block, types, ctors, recs, BlockRead.mapKeys, Array.toList_map,
    List.map_append, List.map_map, List.zip_map, Function.comp_def,
    ownerTypeMap, ownerCtorMap, ownerRecMap, ConstantInfo.mapKeys, ConstantVal.mapKeys,
    IndCaps.mapKeys, Option.map_none, Prod.map] using transported

/-- Successful corresponding lowerings return corresponding owner lists;
this discharges the owner-construction part of per-unit agreement. -/
theorem lowerInductive_owners_mapKeys (hf : InjOn f P) {rb : BlockRead md} (hg : rb.Good P)
    {stS : State md} {stA : State md'} {rS : Read md} {rA : Read md'}
    (source : lowerInductive stS rb = .ok rS)
    (target : lowerInductive stA (rb.mapKeys f) = .ok rA) :
    rA.owners = rS.owners.map (ProjRecOwner.mapKeys f) := by
  rw [lowerInductive_owners target, lowerInductive_owners source, ownersOf_mapKeys hf hg]

end Ix.Cert.CtxAgree
