import IxCC.Src.Relevance.Proof.P1.Cases
import IxCC.Src.Relevance.Proof.P1.Basic

/-! # P1, relevance preservation: a recursor fired (F2, F3)

The case of the core at an ordinary recursor (`CaseF2`, `IxCC.Src.Relevance.Proof.P1.Cases`): the
rule body's evaluation has its precondition (`frame_F2`). The parameter, motive and minor slots are
the recursor's own arguments (`FireOk`; a marker meets an irrelevant rule λ by `SortCoherent` (d),
no recursor parameter being written erased); the field slots are the forced major's fields
(`Post` of its `force`): kept ones `Live`, a marker at a field not written erased by (d), and a
marker at a field its constructor writes erased shielded in the body, passed only to the minor the
rule dispatches (`Canonical.forwards`), which ignores it (`MinorsIgnore`), the value having its
constructor's field count (`MarkersPlaced.count`) and its constructor being the rule's
(`Canonical.rules`, `ShapeOk.ctorUnique`). F3 (subsingleton ι, `case_F3`, `frame_F3`) is the same with
rule 0 and no major forced: the field slots are the recursor's index arguments or the marker, and the
record of rule 0's constructor comes from `Canonical.subRecords` (the twelfth route's check), the
slot count from `Canonical.subsingletonFields`. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src
open Check Check.Canonical

variable {p : Program} {ann : Ann} {ch : Checked}

/-- The minor a rule dispatches: its body's head variable, bound at a minor position. -/
theorem ruleDispatch_some {r : CId} {rule : Rule} {jm : Nat} {sf kk : Bool} {lv np nmot nmin ni : Nat}
    {ind : CId} {rules : List Rule} {ty : Term}
    (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty))
    (h : ruleDispatch p r rule = some jm) :
    ∃ body hv, peelLamsN (np + nmot + nmin + rule.fields) rule.rhs = some body ∧
      body.spineL.1 = .var hv ∧ hv < np + nmot + nmin + rule.fields ∧
      np + nmot ≤ np + nmot + nmin + rule.fields - 1 - hv ∧
      np + nmot + nmin + rule.fields - 1 - hv < np + nmot + nmin ∧
      jm = np + nmot + nmin + rule.fields - 1 - hv - (np + nmot) := by
  unfold ruleDispatch at h
  rw [hd] at h
  simp only at h
  split at h
  · rename_i body hbody
    split at h
    · rename_i hv hhead
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact ⟨body, hv, hbody, hhead, hc.1.1, hc.1.2, hc.2, h.symm⟩
      · cases h
    · cases h
  · cases h

theorem headArity_recr {r : CId} {sf kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Rule} {ty : Term} (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty)) :
    p.headArity (.recr r) = np + nmot + nmin + ni + 1 := by
  simp [Program.headArity, hd, Decl.recArity]

/-- The result of a recursor fired at `k + 1` is its chosen rule body's value. -/
theorem fire_recr_ok {k : Nat} {r : CId} {ls : Levels} {args : List Slot} {sf kk : Bool}
    {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term} {kind : RecKind} {v : Value}
    (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty))
    (hk : (p.table.recKindOf r).map (·.atLevels ls) = some kind)
    (h : fire p (k + 1) (.recr r) ls args = .ok v) :
    ∃ j fields rule body, recChosen p k ls np nmot nmin ni ind kind args = .ok (j, fields) ∧
      rules[j]? = some rule ∧
      peelLams (args.take (np + nmot + nmin) ++ fields).length rule.rhs = some body ∧
      eval p k ls (args.take (np + nmot + nmin) ++ fields).reverse body = .ok v := by
  have e : fire p (k + 1) (.recr r) ls args =
      (match recChosen p k ls np nmot nmin ni ind kind args with
       | .ok (j, fields) =>
         match rules[j]? with
         | some rule =>
           match peelLams (args.take (np + nmot + nmin) ++ fields).length rule.rhs with
           | some body => eval p k ls (args.take (np + nmot + nmin) ++ fields).reverse body
           | none => .stuck
         | none => .stuck
       | .timeout => .timeout
       | .resource r => .resource r
       | .trap => .trap
       | .stuck => .stuck) := by
    rw [fire]
    simp only [hd, hk]
    rfl
  rw [e] at h
  cases hc : recChosen p k ls np nmot nmin ni ind kind args with
  | ok jf =>
    obtain ⟨j, fields⟩ := jf
    rw [hc] at h
    simp only at h
    cases hr : rules[j]? with
    | none => rw [hr] at h; cases h
    | some rule =>
      rw [hr] at h
      simp only at h
      cases hb : peelLams (args.take (np + nmot + nmin) ++ fields).length rule.rhs with
      | none => rw [hb] at h; cases h
      | some body =>
        rw [hb] at h
        exact ⟨j, fields, rule, body, by first | rfl | exact hc, by first | rfl | exact hr, by first | rfl | exact hb, h⟩
  | _ => rw [hc] at h; cases h

/-! ## F2 -/

/-- The rule body's evaluation at an F2 activation has its precondition. -/
theorem frame_F2 (hf : Facts p ann ch) (hs : ShapeOk p) {k : Nat} {r : CId} {ls : Levels}
    {args : List Slot} (hfire : FireOk p ann ch (.recr r) ls args)
    (hcoh : SortCoherent p ann (.fire (k + 1) (.recr r) ls args))
    {sf kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty))
    (hk : (p.table.recKindOf r).map (·.atLevels ls) = some .ordinary)
    {j : Nat} {fields : List Slot}
    (hch : recChosen p k ls np nmot nmin ni ind .ordinary args = .ok (j, fields))
    {rule : Rule} (hrule : rules[j]? = some rule) {body : Term}
    (hpeel : peelLams (args.take (np + nmot + nmin) ++ fields).length rule.rhs = some body)
    (hmajor : Post p ann ch (.force k (args.getD (np + nmot + nmin + ni) default))) :
    Frame p ann ch ls (args.take (np + nmot + nmin) ++ fields).reverse body ∧ WholeTerm p body := by
  obtain ⟨hsp, q, hag, hinst⟩ := hfire.inst.1 r rfl
  have hreached : r ∈ ch.reached := hf.reached (r, q) hinst
  have hres := resolve_none_of_recr hsp
  have harity : args.length = np + nmot + nmin + ni + 1 := by
    rw [hfire.arity]; exact headArity_recr hd
  have hpre_len : (args.take (np + nmot + nmin)).length = np + nmot + nmin := by
    simp only [List.length_take]; omega
  have hkey : TermKey.rule r j ∈ p.runtimeKeys r := by
    simp only [Program.runtimeKeys, hres, hd, List.mem_map, List.mem_range]
    exact ⟨j, (List.getElem?_eq_some_iff.1 hrule).1, rfl⟩
  have htm : p.termOf (.rule r j) = some rule.rhs := by simp [Program.termOf, hd, hrule]
  have htc : TermC p ann q [] rule.rhs := ruleTermC hf hinst hsp hd hrule
  have hts : TermS p ann (lvlsOf p r) q [] rule.rhs := (hf.wa.insts (r, q) hinst).terms _ hkey _ htm
  -- the major
  obtain ⟨major, hfm, hsel⟩ : ∃ major, force p k (args.getD (np + nmot + nmin + ni) default) = .ok major ∧
      p.selectRule ind np major = some (j, fields) := by
    simp only [recChosen] at hch
    cases hfm : force p k (args.getD (np + nmot + nmin + ni) default) with
    | ok major =>
      rw [hfm] at hch
      simp only at hch
      cases hsel : p.selectRule ind np major with
      | none => rw [hsel] at hch; cases hch
      | some jf =>
        rw [hsel] at hch
        simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hch
        exact ⟨major, rfl, by rw [hsel, hch]⟩
    | _ => rw [hfm] at hch; cases hch
  have hmj := hmajor major hfm
  -- (d)
  have hsort : ∀ n s, (args.take (np + nmot + nmin) ++ fields)[n]? = some s → MarkerSlot s →
      ¬ RecSlotErased p ty (np + nmot + nmin) .ordinary rule n →
      ∃ b, (lamRels rule.rhs)[n]? = some b ∧ b.irrAt ls = true := by
    intro n s h1 h2 h3
    have hd' := hcoh sf kk lv np nmot nmin ni ind rules ty .ordinary j fields rule hd hk hch hrule
    exact hd' n s h1 h2 (by rwa [hpre_len])
  have hnotRSE : ∀ n, (n < np + nmot + nmin ∨ fieldWrittenErased p rule.ctor (n - (np + nmot + nmin)) = false) →
      ¬ RecSlotErased p ty (np + nmot + nmin) .ordinary rule n := by
    rintro n hn (⟨hlt, he⟩ | ⟨hle, hw⟩ | ⟨w, srcs, i, hk', -⟩)
    · exact recr_no_erased hf hreached hsp hd n he
    · rcases hn with hn | hn
      · omega
      · rw [hn] at hw; cases hw
    · cases hk'
  -- the frame
  generalize hS : args.take (np + nmot + nmin) ++ fields = S at hpeel hsort ⊢
  have hlen := lamRels_length_of_peel _ _ _ hpeel
  have hbody := termC_peel _ _ _ [] hpeel htc
  simp only [List.append_nil] at hbody
  have hSlen : S.length = np + nmot + nmin + fields.length := by
    rw [← hS, List.length_append, hpre_len]
  refine ⟨⟨q, ((lamRels rule.rhs).take S.length).reverse, hag, ?_, ?_, ?_, Or.inl hbody⟩,
    wholeTerm_of_termC hbody⟩
  · -- EnvOk
    refine ⟨by simp only [List.length_reverse, List.length_take]; omega, ?_⟩
    intro x s b hx hb hrel hm hnsh
    obtain ⟨hxlt, hsx⟩ := rev_get hx
    have hbx : (lamRels rule.rhs)[S.length - 1 - x]? = some b := by
      obtain ⟨hxlt', hb'⟩ := rev_get hb
      have htl : ((lamRels rule.rhs).take S.length).length = S.length := by
        simp only [List.length_take]; omega
      rw [htl, List.getElem?_take_of_lt (by omega)] at hb'
      exact hb'
    obtain ⟨n, hn⟩ : ∃ n, n = S.length - 1 - x := ⟨_, rfl⟩
    rw [← hn] at hsx hbx
    -- a marker slot whose position is not written erased contradicts (d)
    have hnomark : MarkerSlot s → ¬ RecSlotErased p ty (np + nmot + nmin) .ordinary rule n →
        False := by
      intro hms hn
      obtain ⟨b', hb', hirr⟩ := hsort _ s hsx hms hn
      rw [hbx] at hb'
      cases hb'
      rw [hrel] at hirr
      cases hirr
    by_cases hpre : n < np + nmot + nmin
    · -- a parameter, motive or minor slot
      have hsa : args[n]? = some s := by
        rw [← hS, List.getElem?_append_left (by omega), List.getElem?_take_of_lt hpre] at hsx
        exact hsx
      by_cases hms : MarkerSlot s
      · exact (hnomark hms (hnotRSE _ (Or.inl hpre))).elim
      · exact hfire.live _ s hsa (fun h => hms h.2)
    · -- a field slot
      have hfs : fields[n - (np + nmot + nmin)]? = some s := by
        rw [← hS, List.getElem?_append_right (by omega), hpre_len] at hsx
        exact hsx
      cases major with
      | lit m =>
        have hmem : s ∈ fields := List.mem_iff_getElem?.2 ⟨_, hfs⟩
        simp only [Program.selectRule] at hsel
        split at hsel
        · split at hsel
          · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
            rw [← hsel.2] at hmem
            cases hmem
          · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
            rw [← hsel.2, List.mem_singleton] at hmem
            subst hmem
            exact .val (.lit _) (fun _ _ _ he => nomatch he)
        · cases hsel
      | con c lsv ps fs =>
        have hlive : Live p ann ch (.con c lsv ps fs) := hmj.1 rfl
        obtain ⟨sf', lv', np', nf', ty', hdc, rfl⟩ : ∃ sf' lv' np' nf' ty',
            p.decl? c = some (.ctor sf' lv' ind j np' nf' ty') ∧ fields = fs.map .val := by
          simp only [Program.selectRule] at hsel
          cases hdc : p.decl? c with
          | none => rw [hdc] at hsel; cases hsel
          | some d =>
            rw [hdc] at hsel
            cases d with
            | ctor sf' lv' ind' cidx np' nf' ty' =>
              simp only at hsel
              split at hsel
              · rename_i hcond
                simp only [Option.some.injEq, Prod.mk.injEq] at hsel
                simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                obtain ⟨rfl, rfl⟩ := hsel
                obtain ⟨rfl, -⟩ := hcond
                exact ⟨sf', lv', np', nf', ty', rfl, rfl⟩
              · cases hsel
            | _ => simp at hsel
        obtain ⟨i, hi⟩ : ∃ i, i = n - (np + nmot + nmin) := ⟨_, rfl⟩
        rw [← hi] at hfs
        rw [List.getElem?_map] at hfs
        cases hv : fs[i]? with
        | none => rw [hv] at hfs; cases hfs
        | some v =>
          rw [hv] at hfs
          simp only [Option.map_some, Option.some.injEq] at hfs
          subst hfs
          cases hlive with
          | con hread hwhole hplaced =>
            cases hvi : v.isIrr
            · exact .val (hread i v hv (Or.inr hvi)) (hwhole i v hv)
            · -- a marker field
              have hms : MarkerSlot (.val v) := by
                cases v <;> simp [Value.isIrr] at hvi
                exact ⟨_, _, _, rfl⟩
              -- the rule's constructor is the value's
              obtain ⟨shape, hshape, hrecr, -, -, hmin⟩ := elimShape_recr_minors hres hd
              obtain ⟨sf2, lv2, np2, ty2, hdr⟩ :=
                (hf.canon.rules r hreached shape hshape) sf kk lv np nmot nmin ni ind rules ty
                  (by rw [hrecr]; exact hd) j rule hrule
              have hcc : c = rule.ctor := hs.ctorUnique _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdc hdr
              subst hcc
              by_cases hwe : fieldWrittenErased p rule.ctor i = true
              · -- written erased: shielded by the dispatched minor
                exfalso
                apply hnsh
                -- the value's field count is the rule's
                have hcount := hplaced.count i v hv hvi hwe _ _ _ _ _ _ _ hdr
                -- the record of the constructor
                have hrd : ReadsField p ann ch rule.ctor lsv i = false := by
                  cases hrf : ReadsField p ann ch rule.ctor lsv i
                  · rfl
                  · have := live_not_irr (hread i v hv (Or.inl hrf))
                    rw [hvi] at this; cases this
                obtain ⟨kr, hkr⟩ : ∃ kr, ann.ctorRel? rule.ctor = some kr := by
                  simp only [ReadsField, hdr, Checked.keeps, Checked.keepsP] at hrd
                  cases hck : ch.ctorRel? rule.ctor with
                  | none => rw [hck] at hrd; cases hrd
                  | some kr =>
                    refine ⟨kr, ?_⟩
                    simp only [Checked.ctorRel?, hf.wa.ctors] at hck
                    exact hck
                obtain ⟨sf3, lv3, ind3, cidx3, np3, nf3, ty3, hdr3, hkrlen, -⟩ :=
                  hf.canon.ctors rule.ctor kr hkr
                rw [hdr] at hdr3
                simp only [Option.some.injEq, Decl.ctor.injEq] at hdr3
                obtain ⟨-, -, -, -, -, rfl, -⟩ := hdr3
                have hcf : ctorFields p rule = rule.fields := by simp [ctorFields, hdr]
                have hilt : i < rule.fields := by
                  have := (List.getElem?_eq_some_iff.1 hv).1
                  omega
                obtain ⟨-, body', jm, hpeelN, hdisp, hhead, hargs⟩ :=
                  hf.canon.forwards r hreached sf kk lv np nmot nmin ni ind rules ty hd j rule hrule
                    i (by rw [hcf]; exact hilt) hwe
                have hbb : body' = body := by
                  rw [← peelLams_eq_peelLamsN] at hpeelN
                  have : S.length = np + nmot + nmin + rule.fields := by
                    rw [hSlen, List.length_map, hcount]
                  rw [this] at hpeel
                  rw [hpeel] at hpeelN
                  exact (Option.some.inj hpeelN).symm
                subst hbb
                have hx : x = rule.fields - 1 - i := by
                  have : S.length = np + nmot + nmin + rule.fields := by
                    rw [hSlen, List.length_map, hcount]
                  omega
                subst hx
                obtain ⟨body2, hv2, hpeel2, hhd2, hvlt, hvge, hvlt2, hjm⟩ := ruleDispatch_some hd hdisp
                rw [hpeelN] at hpeel2
                cases hpeel2
                -- the head's slot is the dispatched minor's
                have hSlen' : S.length = np + nmot + nmin + rule.fields := by
                  rw [hSlen, List.length_map, hcount]
                have hmpos : S.length - 1 - hv2 = np + nmot + jm := by omega
                obtain ⟨sm, hsm⟩ : ∃ sm, args[np + nmot + jm]? = some sm :=
                  ⟨_, List.getElem?_eq_getElem (by omega)⟩
                have hρh : (S.reverse)[hv2]? = some sm := by
                  rw [List.getElem?_reverse (by omega), hmpos, ← hS,
                    List.getElem?_append_left (by omega), List.getElem?_take_of_lt (by omega)]
                  exact hsm
                have hig : IgnoresSlot sm i := by
                  refine hfire.minors r shape rfl hshape (np + nmot + jm) jm j
                    ((hmin _ _ _).2 ⟨rule, hrule, hdisp, rfl⟩) sm hsm rule.ctor kr.fields ?_ i
                    (by omega) hwe
                  rw [hrecr]
                  simp [ruleCtorFields, hd, hrule, hkr]
                obtain ⟨mm, a, hma, hmx⟩ := mentionsVar_arg hm hhead
                rcases hargs mm a hma with ⟨hmm, ha⟩ | hno
                · refine ⟨hv2, i, sm, hhd2, ?_, hρh, hig, ⟨a, hmm ▸ hma, ha⟩, ?_⟩
                  · intro heq
                    rw [hhd2] at hhead
                    simp [mentionsVar, heq] at hhead
                  · intro m' a' hm' hne
                    rcases hargs m' a' hm' with ⟨h1, -⟩ | h2
                    · exact absurd h1 hne
                    · exact h2
                · rw [hno] at hmx; cases hmx
              · exact (hnomark hms (hnotRSE _ (Or.inr (by rw [← hi]; simpa using hwe)))).elim
      | _ => simp [Program.selectRule] at hsel
  · -- RefsHandled
    intro x hx
    exact refsHandled_runtime hf hinst hkey htm x (refs_peel _ _ _ _ hpeel hts x hx)
  · exact univsOk_peel _ _ _ hpeel ((hf.canon.univs r hreached).1 _ hkey _ htm)

/-- F2. -/
theorem case_F2 : CaseF2 p ann ch := by
  intro k r ls args sf kk lv np nmot nmin ni ind rules ty hd hk hf hs hpre hcoh ih
  have hfire : FireOk p ann ch (.recr r) ls args := hpre
  have harity : args.length = np + nmot + nmin + ni + 1 := by
    rw [hfire.arity]; exact headArity_recr hd
  -- the major's force has its precondition
  have hpm : Pre p ann ch (.force k (args.getD (np + nmot + nmin + ni) default)) := by
    have hm : args[np + nmot + nmin + ni]? = some (args.getD (np + nmot + nmin + ni) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    by_cases hms : MarkerSlot (args.getD (np + nmot + nmin + ni) default)
    · exact Or.inr hms
    · exact Or.inl (hfire.live _ _ hm (fun h => hms h.2))
  have hmajor := (ih _ (.single (Step.recMajor hd hk)) hpm).1
  have hframe : ∀ {j fields rule body}, recChosen p k ls np nmot nmin ni ind .ordinary args = .ok (j, fields) →
      rules[j]? = some rule →
      peelLams (args.take (np + nmot + nmin) ++ fields).length rule.rhs = some body →
      Frame p ann ch ls (args.take (np + nmot + nmin) ++ fields).reverse body ∧ WholeTerm p body :=
    fun hch hrule hpeel => frame_F2 hf hs hfire hcoh hd hk hch hrule hpeel hmajor
  refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
  · obtain ⟨j, fields, rule, body, hch, hrule, hpeel, hev⟩ := fire_recr_ok hd hk hv
    obtain ⟨hfr, hwt⟩ := hframe hch hrule hpeel
    have hpost := (ih _ (.single (Step.recRule hd hk hch hrule hpeel)) hfr).1 v hev
    exact ⟨hpost.1, hpost.2 hwt⟩
  · cases hst with
    | recMajor hd' hk' =>
      rw [hd] at hd'
      simp only [Option.some.injEq, Decl.recr.injEq] at hd'
      obtain ⟨-, -, -, rfl, rfl, rfl, rfl, -, -, -⟩ := hd'
      exact hpm
    | recRule hd' hk' hch hrule hpeel =>
      rw [hd] at hd'
      simp only [Option.some.injEq, Decl.recr.injEq] at hd'
      obtain ⟨-, -, -, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hd'
      rw [hk] at hk'
      simp only [Option.some.injEq] at hk'
      subst hk'
      exact (hframe hch hrule hpeel).1

/-! ## F3 -/

/-- The rule body's evaluation at an F3 activation has its precondition. The parameter, motive and
minor slots are the recursor's own arguments (as F2); the field slots are the recursor's index
arguments (`LiveSlot` unless a marker) or the marker; a marker at a field not written erased meets
an irrelevant rule λ by `SortCoherent` (d) (an index slot written erased is no position of a reached
recursor, `recr_no_erased`); a marker at a field written erased is shielded in the body, passed only
to the minor the rule dispatches (`Canonical.forwards`), which ignores it (`MinorsIgnore`), the
record of rule 0's constructor from `Canonical.subRecords`, the slot count from
`Canonical.subsingletonFields` and `Canonical.rules`. -/
theorem frame_F3 (hf : Facts p ann ch) {k : Nat} {r : CId} {ls : Levels}
    {args : List Slot} (hfire : FireOk p ann ch (.recr r) ls args)
    (hcoh : SortCoherent p ann (.fire (k + 1) (.recr r) ls args))
    {sf kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty)) {w : PropWhen}
    {srcs : List FieldSrc}
    (hk : (p.table.recKindOf r).map (·.atLevels ls) = some (.subsingleton w srcs))
    {j : Nat} {fields : List Slot}
    (hch : recChosen p k ls np nmot nmin ni ind (.subsingleton w srcs) args = .ok (j, fields))
    {rule : Rule} (hrule : rules[j]? = some rule) {body : Term}
    (hpeel : peelLams (args.take (np + nmot + nmin) ++ fields).length rule.rhs = some body) :
    Frame p ann ch ls (args.take (np + nmot + nmin) ++ fields).reverse body ∧ WholeTerm p body := by
  obtain ⟨hsp, q, hag, hinst⟩ := hfire.inst.1 r rfl
  have hreached : r ∈ ch.reached := hf.reached (r, q) hinst
  have hres := resolve_none_of_recr hsp
  have harity : args.length = np + nmot + nmin + ni + 1 := by
    rw [hfire.arity]; exact headArity_recr hd
  have hpre_len : (args.take (np + nmot + nmin)).length = np + nmot + nmin := by
    simp only [List.length_take]; omega
  have hkey : TermKey.rule r j ∈ p.runtimeKeys r := by
    simp only [Program.runtimeKeys, hres, hd, List.mem_map, List.mem_range]
    exact ⟨j, (List.getElem?_eq_some_iff.1 hrule).1, rfl⟩
  have htm : p.termOf (.rule r j) = some rule.rhs := by simp [Program.termOf, hd, hrule]
  have htc : TermC p ann q [] rule.rhs := ruleTermC hf hinst hsp hd hrule
  have hts : TermS p ann (lvlsOf p r) q [] rule.rhs := (hf.wa.insts (r, q) hinst).terms _ hkey _ htm
  -- the choice: rule 0, the fields from the index slots
  have hfields : fields = srcs.map fun
      | .index i => ((args.drop (np + nmot + nmin)).take ni).getD i (Slot.irrNone ls)
      | .proof => Slot.irrNone ls := by
    simp only [recChosen, Sem.Result.ok.injEq, Prod.mk.injEq] at hch
    exact hch.2.symm
  have hj0 : j = 0 := by
    simp only [recChosen, Sem.Result.ok.injEq, Prod.mk.injEq] at hch
    exact hch.1.symm
  subst hj0
  -- the raw kind
  have hraw : p.table.recKindOf r = some (.subsingleton w srcs) := by
    cases hr : p.table.recKindOf r with
    | none => rw [hr] at hk; cases hk
    | some k0 =>
      rw [hr] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      cases k0 with
      | subsingleton w0 srcs0 =>
        simp only [RecKind.atLevels] at hk
        split at hk
        · exact hk ▸ rfl
        · cases hk
      | _ => simp [RecKind.atLevels] at hk
  obtain ⟨shape, hshape, hrecr, -, -, hmin⟩ := elimShape_recr_minors hres hd
  -- rule 0's constructor: its declaration (`Canonical.rules`) and its record (`Canonical.subRecords`)
  obtain ⟨sf2, lv2, np2, ty2, hdr⟩ :=
    (hf.canon.rules r hreached shape hshape) sf kk lv np nmot nmin ni ind rules ty
      (by rw [hrecr]; exact hd) 0 rule hrule
  have hsrcs : srcs.length = rule.fields := by
    have h := hf.canon.subsingletonFields r hreached shape hshape sf kk lv np nmot nmin ni ind rules ty
      w srcs rule (by rw [hrecr]; exact hd) (by rw [hrecr]; exact hraw) hrule
    rw [h]
    simp [ctorFields, hdr]
  have hflen : fields.length = rule.fields := by rw [hfields, List.length_map, hsrcs]
  -- (d)
  have hsort : ∀ n s, (args.take (np + nmot + nmin) ++ fields)[n]? = some s → MarkerSlot s →
      ¬ RecSlotErased p ty (np + nmot + nmin) (.subsingleton w srcs) rule n →
      ∃ b, (lamRels rule.rhs)[n]? = some b ∧ b.irrAt ls = true := by
    intro n s h1 h2 h3
    have hd' := hcoh sf kk lv np nmot nmin ni ind rules ty (.subsingleton w srcs) 0 fields rule hd hk hch hrule
    exact hd' n s h1 h2 (by rwa [hpre_len])
  have hnotRSE : ∀ n, (n < np + nmot + nmin ∨ fieldWrittenErased p rule.ctor (n - (np + nmot + nmin)) = false) →
      ¬ RecSlotErased p ty (np + nmot + nmin) (.subsingleton w srcs) rule n := by
    rintro n hn (⟨hlt, he⟩ | ⟨hle, hw⟩ | ⟨w', srcs', i, -, hle, -, he⟩)
    · exact recr_no_erased hf hreached hsp hd n he
    · rcases hn with hn | hn
      · omega
      · rw [hn] at hw; cases hw
    · exact recr_no_erased hf hreached hsp hd _ he
  -- the frame
  generalize hS : args.take (np + nmot + nmin) ++ fields = S at hpeel hsort ⊢
  have hlen := lamRels_length_of_peel _ _ _ hpeel
  have hbody := termC_peel _ _ _ [] hpeel htc
  simp only [List.append_nil] at hbody
  have hSlen : S.length = np + nmot + nmin + rule.fields := by
    rw [← hS, List.length_append, hpre_len, hflen]
  refine ⟨⟨q, ((lamRels rule.rhs).take S.length).reverse, hag, ?_, ?_, ?_, Or.inl hbody⟩,
    wholeTerm_of_termC hbody⟩
  · -- EnvOk
    refine ⟨by simp only [List.length_reverse, List.length_take]; omega, ?_⟩
    intro x s b hx hb hrel hm hnsh
    obtain ⟨hxlt, hsx⟩ := rev_get hx
    have hbx : (lamRels rule.rhs)[S.length - 1 - x]? = some b := by
      obtain ⟨hxlt', hb'⟩ := rev_get hb
      have htl : ((lamRels rule.rhs).take S.length).length = S.length := by
        simp only [List.length_take]; omega
      rw [htl, List.getElem?_take_of_lt (by omega)] at hb'
      exact hb'
    obtain ⟨n, hn⟩ : ∃ n, n = S.length - 1 - x := ⟨_, rfl⟩
    rw [← hn] at hsx hbx
    have hnomark : MarkerSlot s → ¬ RecSlotErased p ty (np + nmot + nmin) (.subsingleton w srcs) rule n →
        False := by
      intro hms hn
      obtain ⟨b', hb', hirr⟩ := hsort _ s hsx hms hn
      rw [hbx] at hb'
      cases hb'
      rw [hrel] at hirr
      cases hirr
    by_cases hpre : n < np + nmot + nmin
    · -- a parameter, motive or minor slot
      have hsa : args[n]? = some s := by
        rw [← hS, List.getElem?_append_left (by omega), List.getElem?_take_of_lt hpre] at hsx
        exact hsx
      by_cases hms : MarkerSlot s
      · exact (hnomark hms (hnotRSE _ (Or.inl hpre))).elim
      · exact hfire.live _ s hsa (fun h => hms h.2)
    · -- a field slot
      obtain ⟨i, hi⟩ : ∃ i, i = n - (np + nmot + nmin) := ⟨_, rfl⟩
      have hfs : fields[i]? = some s := by
        rw [← hS, List.getElem?_append_right (by omega), hpre_len, ← hi] at hsx
        exact hsx
      by_cases hms : MarkerSlot s
      · by_cases hwe : fieldWrittenErased p rule.ctor i = true
        · -- written erased: shielded by the dispatched minor
          exfalso
          apply hnsh
          obtain ⟨kr, hkr⟩ := Option.isSome_iff_exists.1
            (hf.canon.subRecords r hreached shape hshape w srcs sf kk lv np nmot nmin ni ind rules ty
              rule (by rw [hrecr]; exact hraw) (by rw [hrecr]; exact hd) hrule)
          have hcf : ctorFields p rule = rule.fields := by simp [ctorFields, hdr]
          have hilt : i < rule.fields := by
            have := (List.getElem?_eq_some_iff.1 hfs).1
            omega
          obtain ⟨-, body', jm, hpeelN, hdisp, hhead, hargs⟩ :=
            hf.canon.forwards r hreached sf kk lv np nmot nmin ni ind rules ty hd 0 rule hrule
              i (by rw [hcf]; exact hilt) hwe
          have hbb : body' = body := by
            rw [← peelLams_eq_peelLamsN] at hpeelN
            rw [hSlen] at hpeel
            rw [hpeel] at hpeelN
            exact (Option.some.inj hpeelN).symm
          subst hbb
          have hx : x = rule.fields - 1 - i := by omega
          subst hx
          obtain ⟨body2, hv2, hpeel2, hhd2, hvlt, hvge, hvlt2, hjm⟩ := ruleDispatch_some hd hdisp
          rw [hpeelN] at hpeel2
          cases hpeel2
          have hmpos : S.length - 1 - hv2 = np + nmot + jm := by omega
          obtain ⟨sm, hsm⟩ : ∃ sm, args[np + nmot + jm]? = some sm :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have hρh : (S.reverse)[hv2]? = some sm := by
            rw [List.getElem?_reverse (by omega), hmpos, ← hS,
              List.getElem?_append_left (by omega), List.getElem?_take_of_lt (by omega)]
            exact hsm
          have hig : IgnoresSlot sm i := by
            refine hfire.minors r shape rfl hshape (np + nmot + jm) jm 0
              ((hmin _ _ _).2 ⟨rule, hrule, hdisp, rfl⟩) sm hsm rule.ctor kr.fields ?_ i ?_ hwe
            · rw [hrecr]
              simp [ruleCtorFields, hd, hrule, hkr]
            · obtain ⟨sf3, lv3, ind3, cidx3, np3, nf3, ty3, hdr3, hkrlen, -⟩ := hf.canon.ctors rule.ctor kr hkr
              rw [hdr] at hdr3
              simp only [Option.some.injEq, Decl.ctor.injEq] at hdr3
              obtain ⟨-, -, -, -, -, rfl, -⟩ := hdr3
              omega
          obtain ⟨mm, a, hma, hmx⟩ := mentionsVar_arg hm hhead
          rcases hargs mm a hma with ⟨hmm, ha⟩ | hno
          · refine ⟨hv2, i, sm, hhd2, ?_, hρh, hig, ⟨a, hmm ▸ hma, ha⟩, ?_⟩
            · intro heq
              rw [hhd2] at hhead
              simp [mentionsVar, heq] at hhead
            · intro m' a' hm' hne
              rcases hargs m' a' hm' with ⟨h1, -⟩ | h2
              · exact absurd h1 hne
              · exact h2
          · rw [hno] at hmx; cases hmx
        · exact (hnomark hms (hnotRSE _ (Or.inr (by rw [← hi]; simpa using hwe)))).elim
      · -- an index argument of the recursor
        rw [hfields, List.getElem?_map] at hfs
        cases hsrc : srcs[i]? with
        | none => rw [hsrc] at hfs; cases hfs
        | some src =>
          rw [hsrc] at hfs
          simp only [Option.map_some, Option.some.injEq] at hfs
          cases src with
          | proof => exact (hms (by rw [← hfs]; exact ⟨_, _, _, rfl⟩)).elim
          | index i' =>
            simp only at hfs
            rw [List.getD_eq_getElem?_getD] at hfs
            cases hai : ((args.drop (np + nmot + nmin)).take ni)[i']? with
            | none => rw [hai] at hfs; exact (hms (by rw [← hfs]; exact ⟨_, _, _, rfl⟩)).elim
            | some s' =>
              rw [hai] at hfs
              simp only [Option.getD_some] at hfs
              subst hfs
              have hlt : i' < ni := by
                have := (List.getElem?_eq_some_iff.1 hai).1
                simp only [List.length_take, List.length_drop] at this
                omega
              rw [List.getElem?_take_of_lt hlt, List.getElem?_drop] at hai
              exact hfire.live _ s' hai (fun h => hms h.2)
  · -- RefsHandled
    intro x hx
    exact refsHandled_runtime hf hinst hkey htm x (refs_peel _ _ _ _ hpeel hts x hx)
  · exact univsOk_peel _ _ _ hpeel ((hf.canon.univs r hreached).1 _ hkey _ htm)

/-- F3. -/
theorem case_F3 : CaseF3 p ann ch := by
  intro k r ls args sf kk lv np nmot nmin ni ind rules ty w srcs hd hk hf _ hpre hcoh ih
  have hfire : FireOk p ann ch (.recr r) ls args := hpre
  have hframe : ∀ {j fields rule body},
      recChosen p k ls np nmot nmin ni ind (.subsingleton w srcs) args = .ok (j, fields) →
      rules[j]? = some rule →
      peelLams (args.take (np + nmot + nmin) ++ fields).length rule.rhs = some body →
      Frame p ann ch ls (args.take (np + nmot + nmin) ++ fields).reverse body ∧ WholeTerm p body :=
    fun hch hrule hpeel => frame_F3 hf hfire hcoh hd hk hch hrule hpeel
  refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
  · obtain ⟨j, fields, rule, body, hch, hrule, hpeel, hev⟩ := fire_recr_ok hd hk hv
    obtain ⟨hfr, hwt⟩ := hframe hch hrule hpeel
    have hpost := (ih _ (.single (Step.recRule hd hk hch hrule hpeel)) hfr).1 v hev
    exact ⟨hpost.1, hpost.2 hwt⟩
  · cases hst with
    | recMajor hd' hk' =>
      rw [hd] at hd'
      simp only [Option.some.injEq, Decl.recr.injEq] at hd'
      obtain ⟨-, -, -, -, -, -, -, -, -, -⟩ := hd'
      rw [hk] at hk'
      simp at hk'
    | recRule hd' hk' hch hrule hpeel =>
      rw [hd] at hd'
      simp only [Option.some.injEq, Decl.recr.injEq] at hd'
      obtain ⟨-, -, -, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hd'
      rw [hk] at hk'
      simp only [Option.some.injEq] at hk'
      subst hk'
      exact (hframe hch hrule hpeel).1

end IxCC.Src.Relevance.Proof.P1
