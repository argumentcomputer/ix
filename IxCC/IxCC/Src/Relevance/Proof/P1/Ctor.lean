import IxCC.Src.Relevance.Proof.P1.Cases
import IxCC.Src.Relevance.Proof.P1.Basic

/-! # P1, relevance preservation: constructor values (E6, F1, F7, F8)

The cases of the core (`IxCC.Src.Relevance.Proof.P1.Cases`) that build or read a constructor value.
E6 (`case_proj`): a projection's field is `Live` where it is read (`Live.con`), and a marker there
would be at a field written erased (`SortCoherent` (f)), which C3 refuses at the projection
(`TermC.proj` against `field_erased_dropped`). F1 (`case_ctor`): each field is its argument forced,
`Live` unless the argument is a marker at a position the constructor ignores, where the field is
dropped at the value's levels (`Canonical.ctorRecords`, `CtorCanon`), and the value has the
constructor's field count (`MarkersPlaced.count`). F7 (`case_quotMk`): the element is `Live` unless
`Quot.mk`'s parameter 2 is irrelevant there, and a reached `Quot.mk` reads its element
(`Canonical.reads`, hence `MarkersPlaced.quotElem`). F8 (`case_quotLift`): `Quot.lift`'s function
is read (`Canonical.minorsRead`), so it forces to a `Live`, `Whole` value; the element fits it
(`Live.con` of the quotient, or a marker it ignores by `SortCoherent` (e), the element not being
written erased by `MarkersPlaced.quotElem`). P1 is not proved. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src
open Check Check.Canonical
open IxCC.Lam.Erase.Proof (Agree)

variable {p : Program} {ann : Ann} {ch : Checked}

/-! ## Shared facts (to Basic) -/

/-- `TransGen` from one step before a chain. (to Basic) -/
theorem tg_head {α : Type} {r : α → α → Prop} {a b c : α} (h : r a b)
    (h' : Relation.TransGen r b c) : Relation.TransGen r a c := by
  induction h' with
  | single hbc => exact .tail (.single h) hbc
  | tail _ hcd ih => exact .tail ih hcd

/-- A member of a list's suffix is a member of the list. (to Basic) -/
theorem mem_of_mem_drop' {α : Type} {n : Nat} {l : List α} {a : α} (h : a ∈ l.drop n) : a ∈ l := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_drop] at hi
  exact List.mem_iff_getElem?.2 ⟨_, hi⟩

/-- Concrete levels agree with their own profile. (to Basic) -/
theorem agree_profileOf (ls : Levels) : Agree ls (profileOf ls) := by
  intro i
  simp only [profileOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ls[i]? <;> rfl

/-- A field class read from a position class is dropped where the position is irrelevant.
(to Basic) -/
theorem ofRel_dropWhen (r : Rel) : (FieldClass.ofRel r).dropWhen = r.irrWhen := by
  cases r <;> rfl

/-- The checked constructor records are the annotation's. (to Basic) -/
theorem ch_ctorRel (hf : Facts p ann ch) (k : CId) : ch.ctorRel? k = ann.ctorRel? k := by
  show ch.ctors.get? k = ann.ctors.get? k
  rw [hf.wa.ctors]

/-- A field written erased is a constructor's. (to Basic) -/
theorem decl_of_fieldWrittenErased {c : CId} {i : Nat} (h : fieldWrittenErased p c i = true) :
    ∃ sf lv ind cidx np nf ty, p.decl? c = some (.ctor sf lv ind cidx np nf ty) := by
  cases hdc : p.decl? c with
  | none => simp [fieldWrittenErased, hdc] at h
  | some d =>
    cases d with
    | ctor sf lv ind cidx np nf ty => exact ⟨_, _, _, _, _, _, _, rfl⟩
    | _ => simp [fieldWrittenErased, hdc] at h

/-- A quotient constructor is a `Quot.mk` declaration. (to Basic) -/
theorem decl_of_isQuotCtor {c : CId} (h : p.isQuotCtor c = true) :
    ∃ lv ty, p.decl? c = some (.quot .ctor lv ty) := by
  cases hd : p.decl? c with
  | none => simp [Program.isQuotCtor, hd] at h
  | some d =>
    cases d with
    | quot kd lv ty =>
      cases kd with
      | ctor => exact ⟨lv, ty, rfl⟩
      | _ => simp [Program.isQuotCtor, hd] at h
    | _ => simp [Program.isQuotCtor, hd] at h

/-- A constant whose δ head is `Quot.mk` is a `Quot.mk` declaration. (to Basic) -/
theorem decl_of_quotMk {c c' : CId} (hsp : specialHead? p c = some (.quotMk c')) :
    ∃ lv ty, p.decl? c = some (.quot .ctor lv ty) := by
  cases hr : p.table.resolveOf c with
  | some e =>
    unfold specialHead? at hsp
    rw [hr] at hsp
    cases e <;> simp at hsp
  | none =>
    unfold specialHead? at hsp
    rw [hr] at hsp
    cases hd : p.decl? c with
    | none => rw [hd] at hsp; simp at hsp
    | some d =>
      rw [hd] at hsp
      cases d with
      | quot kd lv ty =>
        cases kd with
        | ctor => exact ⟨lv, ty, rfl⟩
        | _ => simp at hsp
      | _ => simp at hsp

/-- An eliminator one of whose rules is for a constructor writing a field erased has
`erasedMinors`. (to Basic) -/
theorem erasedMinors_true {shape : ElimShape} {sf kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Rule} {ty : Term}
    (hd : p.decl? shape.recr = some (.recr sf kk lv np nmot nmin ni ind rules ty))
    {rule : Rule} (hmem : rule ∈ rules) {sf' : Bool} {lv' : Nat} {ind' : CId} {cidx' np' nf' : Nat}
    {ty' : Term} (hdc : p.decl? rule.ctor = some (.ctor sf' lv' ind' cidx' np' nf' ty')) {i : Nat}
    (hi : i < nf') (hwe : fieldWrittenErased p rule.ctor i = true) : erasedMinors p shape = true := by
  unfold erasedMinors
  rw [hd]
  simp only [List.any_eq_true]
  refine ⟨rule, hmem, ?_⟩
  rw [hdc]
  simp only [List.any_eq_true, List.mem_range]
  exact ⟨i, hi, hwe⟩

/-- A `Whole` partial application's head meets no minor over a field written erased, so the
per-minor fact holds of any arguments. (to Basic) -/
theorem minorsIgnore_of_whole (hf : Facts p ann ch) {h : Head} {ls : Levels} {args args' : List Slot}
    (hw : Whole p (.pap h ls args)) : MinorsIgnore p ann h args' := by
  intro c shape hc hsh pos j kidx _ s _ k fields hrcf i hi hwe
  exfalso
  have hem := hw h ls args rfl c shape hc hsh
  cases hd : p.decl? shape.recr with
  | none => simp [ruleCtorFields, hd] at hrcf
  | some d =>
    cases d with
    | recr sf kk lv np nmot nmin ni ind rules ty =>
      cases hr : rules[kidx]? with
      | none => simp [ruleCtorFields, hd, hr] at hrcf
      | some rule =>
        cases hkr : ann.ctorRel? rule.ctor with
        | none => simp [ruleCtorFields, hd, hr, hkr] at hrcf
        | some kr =>
          simp [ruleCtorFields, hd, hr, hkr] at hrcf
          obtain ⟨rfl, rfl⟩ := hrcf
          obtain ⟨sf', lv', ind', cidx', np', nf', ty', hdc, hlen, -⟩ := hf.canon.ctors rule.ctor kr hkr
          have := erasedMinors_true hd (List.mem_iff_getElem?.2 ⟨kidx, hr⟩) hdc (by omega) hwe
          rw [hem] at this
          cases this
    | _ => simp [ruleCtorFields, hd] at hrcf

/-- `forceAll` returning: one value per slot, each its slot's `force`, a call the `forceAll`
makes. (to Basic) -/
theorem forceAll_ok_get {k : Nat} (ss : List Slot) : ∀ {vs : List Value}, forceAll p k ss = .ok vs →
    vs.length = ss.length ∧ ∀ (i : Nat) (v : Value), vs[i]? = some v → ∃ s, ss[i]? = some s ∧ force p k s = .ok v ∧
      Relation.TransGen (Step p) (.forceAll k ss) (.force k s) := by
  induction ss with
  | nil =>
    intro vs h
    simp only [forceAll, Sem.Result.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i v hv => by simp at hv⟩
  | cons s rest ih =>
    intro vs h
    cases hs : force p k s with
    | ok v0 =>
      cases hr : forceAll p k rest with
      | ok vs0 =>
        simp only [forceAll, hs, hr, Sem.Result.ok.injEq] at h
        subst h
        obtain ⟨hlen, hget⟩ := ih hr
        refine ⟨by simp [hlen], fun i v hv => ?_⟩
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
          subst hv
          exact ⟨s, rfl, hs, .single Step.allForce⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hv
          obtain ⟨s', hs', hf', htg⟩ := hget i v hv
          exact ⟨s', by simpa using hs', hf', tg_head (Step.allForceRest hs) htg⟩
      | _ => simp [forceAll, hs, hr] at h
    | _ => simp [forceAll, hs] at h

/-- A `LiveSlot` forces to a `Live` value at any `force` call the evaluation of `c` makes: a
by-name slot's value is its evaluation's, whose precondition the slot carries. (to Basic) -/
theorem force_live {c : Call} (ih : Below p ann ch c) {k : Nat} {s : Slot} {v : Value}
    (hpath : Relation.TransGen (Step p) c (.force k s)) (hs : LiveSlot p ann ch s)
    (hv : force p k s = .ok v) : Live p ann ch v := by
  cases hs with
  | val hl _ =>
    simp only [force, Sem.Result.ok.injEq] at hv
    subst hv
    exact hl
  | name q bs hag htok henv =>
    cases k with
    | zero => simp [force] at hv
    | succ k =>
      simp only [force] at hv
      have hpre : Frame p ann ch _ _ _ := ⟨q, bs, hag, henv, htok.refs, htok.univs, Or.inl htok.c⟩
      exact ((ih _ (hpath.tail Step.forceName) hpre).1 v hv).1

/-- A constructor ignoring argument `np + i` at `ls` does not read field `i` of a value built at
`ls`: the record's field class is the parameter class (`CtorCanon`), dropped at `profileOf ls`,
which agrees with `ls`. -/
theorem readsField_ctor_false (hf : Facts p ann ch) {c : CId} (hr : c ∈ ch.reached)
    {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Term}
    (hdc : p.decl? c = some (.ctor sf lv ind cidx np nf ty)) {ls : Levels} {i : Nat}
    (hig : HeadIgnores ann (.ctor c) ls (np + i)) : ReadsField p ann ch c ls i = false := by
  obtain ⟨c0, cr, r, hc0, hcr, hpr, hirr⟩ := hig
  simp only [headConst?, Option.some.injEq] at hc0
  rw [← hc0] at hcr
  obtain ⟨kr, hkr⟩ : ∃ kr, ann.ctorRel? c = some kr :=
    Option.isSome_iff_exists.1 (hf.canon.ctorRecords c hr _ _ _ _ _ _ _ hdc)
  obtain ⟨sf', lv', ind', cidx', np', nf', ty', hdc', -, -, hfields, -⟩ := hf.canon.ctors c kr hkr
  rw [hdc] at hdc'
  cases hdc'
  have hkf : kr.fields[i]? = some (FieldClass.ofRel r) := by
    rw [← hfields cr hcr, List.getElem?_map, List.getElem?_drop, hpr] <;> rfl
  have hirrP : r.irrWhen.holdsP (profileOf ls) = true := by
    have := (agree_profileOf ls).irr r
    simp only [Rel.irrP] at this
    rw [this]
    exact hirr
  simp only [ReadsField, hdc, Checked.keeps, Checked.keepsP, ch_ctorRel hf, hkr, hkf,
    FieldClass.dropP, ofRel_dropWhen, hirrP, Bool.not_true]

/-! ## E6 -/

/-- E6: the child's precondition is the projection's, and the field is `Live` where it is read; a
marker read would be at a field written erased (`SortCoherent` (f)), which `TermC.proj` refuses. -/
theorem case_proj : CaseProj p ann ch := by
  intro k ls ρ s i e hf _ hpre hcoh ih
  obtain ⟨q, bs, hag, henv, hrefs, huniv, hc⟩ := hpre
  have htc : TermC p ann q bs (.proj s i e) := by
    rcases hc with ht | ⟨more, -, hsp, -⟩ | ⟨c, us, he, -⟩
    · exact ht
    · cases hsp with
      | head _ _ ht => exact ht
    · cases he
  obtain ⟨hdrop, hte⟩ : (∀ k rel cls, onlyCtor? p s = some k → ann.ctorRel? k = some rel →
      rel.fields[i]? = some cls → cls.alwaysDropped = false) ∧ TermC p ann q bs e := by
    cases htc with
    | proj h1 h2 => exact ⟨h1, h2⟩
  have hpe : Frame p ann ch ls ρ e := by
    obtain ⟨hlen, hlive⟩ := henv
    refine ⟨q, bs, hag, EnvOk.mk hlen (fun x sl r hx hr hirr hm _ =>
      hlive x sl r hx hr hirr (show mentionsVar x (.proj s i e) = true from hm) ?_), hrefs, huniv,
      Or.inl hte⟩
    rintro ⟨h, n, s', hh, -⟩
    have hsp : (Term.proj s i e).spineL.1 = .proj s i e := rfl
    rw [hsp] at hh
    cases hh
  have hpostE := (ih _ (.single Step.proj) hpe).1
  refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
  · cases he : eval p k ls ρ e with
    | ok v0 =>
      have hpf : p.projectField s i v0 = .ok v := by
        simp only [eval, he] at hv
        exact hv
      have hlv0 := (hpostE v0 he).1
      cases v0 with
      | con cv lsv ps fs =>
        cases hds : p.decl? s with
        | none => simp [Program.projectField, hds] at hpf
        | some d =>
          cases d with
          | induct a1 a2 a3 a4 a5 ctors =>
            cases ctors with
            | nil => simp [Program.projectField, hds] at hpf
            | cons c0 rest =>
              cases rest with
              | cons _ _ => simp [Program.projectField, hds] at hpf
              | nil =>
                by_cases hc : c0 = cv
                · have hfs : fs[i]? = some v := by
                    cases hfi : fs[i]? with
                    | none => simp [Program.projectField, hds, hc, hfi, Sem.Result.ofOption] at hpf
                    | some w =>
                      simp [Program.projectField, hds, hc, hfi, Sem.Result.ofOption] at hpf
                      simp [hpf]
                  have hoc : onlyCtor? p s = some cv := by
                    rw [← hc]
                    simp [onlyCtor?, hds]
                  cases hlv0 with
                  | con hread hwhole _ =>
                    refine ⟨?_, fun _ => hwhole i v hfs⟩
                    cases hvi : v.isIrr with
                    | false => exact hread i v hfs (Or.inr hvi)
                    | true =>
                      cases hrf : ReadsField p ann ch cv lsv i with
                      | true => exact hread i v hfs (Or.inl hrf)
                      | false =>
                        exfalso
                        have hwe : fieldWrittenErased p cv i = true := hcoh cv lsv ps fs v he hfs hvi
                        obtain ⟨sf, lv, ind, cidx, np, nf, ty, hdc⟩ := decl_of_fieldWrittenErased hwe
                        obtain ⟨kr, hkr⟩ : ∃ kr, ann.ctorRel? cv = some kr := by
                          cases hck : ann.ctorRel? cv with
                          | none =>
                            simp [ReadsField, hdc, Checked.keeps, Checked.keepsP, ch_ctorRel hf, hck]
                              at hrf
                          | some kr => exact ⟨kr, rfl⟩
                        obtain ⟨cls, hcls, hdr⟩ := field_erased_dropped (hf.canon.ctors cv kr hkr) hwe
                        have := hdrop cv kr cls hoc hkr hcls
                        rw [hdr] at this
                        cases this
                · simp [Program.projectField, hds, hc] at hpf
          | _ => simp [Program.projectField, hds] at hpf
      | _ => simp [Program.projectField] at hpf
    | _ => simp [eval, he] at hv
  · cases hst with
    | proj => exact hpe

/-! ## F1 -/

/-- F1: each field is its argument forced; a marker field the value reads would be a `LiveSlot`'s
force (never a marker) or an argument the constructor ignores (a field dropped at the value's
levels). The pinned `Nat` constructors give literals. -/
theorem case_ctor : CaseCtor p ann ch := by
  intro k c ls args hf _ hpre _ ih
  have hfire : FireOk p ann ch (.ctor c) ls args := hpre
  obtain ⟨-, q, -, hinst⟩ := hfire.inst.1 c rfl
  have hreached : c ∈ ch.reached := hf.reached (c, q) hinst
  have hslot : ∀ s ∈ args, LiveSlot p ann ch s ∨ MarkerSlot s := by
    intro s hs
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hs
    by_cases hm : MarkerSlot s
    · exact Or.inr hm
    · exact Or.inl (hfire.live j s hj (fun h => hm h.2))
  refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
  · cases hdc : p.decl? c with
    | none => simp [fire, hdc] at hv
    | some d =>
      cases d with
      | ctor sf lv ind cidx np nf ty =>
        have hstep : Step p (.fire k (.ctor c) ls args) (.forceAll k (args.drop np)) :=
          Step.ctorArgs hdc
        have hpostA := (ih _ (.single hstep) (fun s hs => hslot s (mem_of_mem_drop' hs))).1
        cases hfa : forceAll p k (args.drop np) with
        | ok fields =>
          have hfs := hpostA fields hfa
          obtain ⟨hlen, hget⟩ := forceAll_ok_get _ hfa
          simp only [fire, hdc, hfa] at hv
          split at hv
          · cases hv
            exact ⟨.lit 0, fun _ _ _ he => nomatch he⟩
          · split at hv
            · split at hv
              · cases hv
                exact ⟨.lit _, fun _ _ _ he => nomatch he⟩
              · cases hv
            · cases hv
              refine ⟨Live.con ?_ ?_ ⟨?_, ?_⟩, fun _ _ _ he => nomatch he⟩
              · intro i w hw hrd
                obtain ⟨s, hs, hfw, hpath⟩ := hget i w hw
                cases hwi : w.isIrr with
                | false => exact (hfs w (List.mem_iff_getElem?.2 ⟨i, hw⟩)).1 hwi
                | true =>
                  rcases hrd with hrd | hrd
                  · have hsa : args[np + i]? = some s := by
                      rw [List.getElem?_drop] at hs
                      exact hs
                    by_cases hig : HeadIgnores ann (.ctor c) ls (np + i) ∧ MarkerSlot s
                    · rw [readsField_ctor_false hf hreached hdc hig.1] at hrd
                      cases hrd
                    · exact force_live ih (tg_head hstep hpath) (hfire.live _ s hsa hig) hfw
                  · rw [hwi] at hrd
                    cases hrd
              · intro i w hw
                exact (hfs w (List.mem_iff_getElem?.2 ⟨i, hw⟩)).2
              · intro i w _ _ _ sf' lv' ind' cidx' np' nf' ty' hdc'
                rw [hdc] at hdc'
                cases hdc'
                rw [hlen, List.length_drop, hfire.arity]
                simp [Program.headArity, hdc]
              · intro w _ _ lv' ty' hdq
                rw [hdc] at hdq
                cases hdq
        | _ => simp [fire, hdc, hfa] at hv
      | _ => simp [fire, hdc] at hv
  · cases hst with
    | ctorArgs _ => exact fun s hs => hslot s (mem_of_mem_drop' hs)

/-! ## F7 -/

/-- F7: the element is its argument forced, `Live` unless `Quot.mk` ignores it at the levels; a
reached `Quot.mk` reads its element (`Canonical.reads`), so it does not write it erased. -/
theorem case_quotMk : CaseQuotMk p ann ch := by
  intro k c ls args hf _ hpre _ ih
  have hfire : FireOk p ann ch (.quotMk c) ls args := hpre
  obtain ⟨hsp, q, -, hinst⟩ := hfire.inst.1 c rfl
  have hreached : c ∈ ch.reached := hf.reached (c, q) hinst
  obtain ⟨lvq, tyq, hdq⟩ := decl_of_quotMk hsp
  have h2 : 2 ∉ erasedParams tyq := by
    intro h
    have e := hf.canon.reads c hreached (.quotMk c) _ hsp hdq 2 h
    simp [readsAt, headReadsWith, headArityOf] at e
  have harity : args.length = 3 := hfire.arity
  obtain ⟨α, r, a, rfl⟩ : ∃ α r a, args = [α, r, a] := by
    rcases args with _ | ⟨α, _ | ⟨r, _ | ⟨a, _ | ⟨x, rest⟩⟩⟩⟩ <;> simp at harity
    exact ⟨α, r, a, rfl⟩
  have hpa : Pre p ann ch (.force k a) := by
    by_cases hm : MarkerSlot a
    · exact Or.inr hm
    · exact Or.inl (hfire.live 2 a rfl (fun h => hm h.2))
  have hpostA := (ih _ (.single Step.mkArg) hpa).1
  refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
  · cases hfa : force p k a with
    | ok w =>
      simp only [fire, hfa, Sem.Result.ok.injEq] at hv
      subst hv
      have hw := hpostA w hfa
      refine ⟨Live.con ?_ ?_ ⟨?_, ?_⟩, fun _ _ _ he => nomatch he⟩
      · intro i w' hw' hrd
        cases i with
        | succ i => simp at hw'
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw'
          subst hw'
          cases hwi : w.isIrr with
          | false => exact hw.1 hwi
          | true =>
            rcases hrd with hrd | hrd
            · by_cases hig : HeadIgnores ann (.quotMk c) ls 2 ∧ MarkerSlot a
              · exfalso
                obtain ⟨c0, cr, r0, hc0, hcr, hpr, hirr⟩ := hig.1
                simp only [headConst?, Option.some.injEq] at hc0
                rw [← hc0] at hcr
                simp [ReadsField, hdq, hcr, hpr, hirr] at hrd
              · exact force_live ih (.single Step.mkArg) (hfire.live 2 a rfl hig) hfa
            · rw [hwi] at hrd
              cases hrd
      · intro i w' hw'
        cases i with
        | succ i => simp at hw'
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw'
          subst hw'
          exact hw.2
      · intro i w' _ _ hwe
        simp [fieldWrittenErased, hdq] at hwe
      · intro w' _ _ lv ty hd'
        rw [hdq] at hd'
        cases hd'
        exact h2
    | _ => simp [fire, hfa] at hv
  · cases hst with
    | mkArg => exact hpa

/-! ## F8 -/

/-- `Quot.lift` fired at `k + 1` returns its function applied to the quotient's element. -/
theorem fire_quotLift_ok {k : Nat} {c : CId} {ls : Levels} {α r β f h q : Slot} {v : Value}
    (hv : fire p (k + 1) (.quotLift c) ls [α, r, β, f, h, q] = .ok v) :
    ∃ c' l' ps a fv, force p k q = .ok (.con c' l' ps [a]) ∧ p.isQuotCtor c' = true ∧
      force p k f = .ok fv ∧ apply p k fv (.val a) = .ok v := by
  cases hq : force p k q with
  | ok vq =>
    cases vq with
    | con c' l' ps fs =>
      cases fs with
      | nil => simp [fire, hq] at hv
      | cons a rest =>
        cases rest with
        | cons _ _ => simp [fire, hq] at hv
        | nil =>
          cases hqc : p.isQuotCtor c' with
          | false => simp [fire, hq, hqc] at hv
          | true =>
            cases hff : force p k f with
            | ok fv =>
              simp only [fire, hq, hqc, hff, ↓reduceIte] at hv
              exact ⟨c', l', ps, a, fv, rfl, hqc, rfl, hv⟩
            | _ => simp [fire, hq, hqc, hff] at hv
    | _ => simp [fire, hq] at hv
  | _ => simp [fire, hq] at hv

/-- F8: the function is read (`Canonical.minorsRead`), so it forces to a `Live`, `Whole` value;
the element fits it: `Live` from the quotient's `Live.con`, or a marker the function ignores
(`SortCoherent` (e)), its `Quot.mk` not writing it erased (`MarkersPlaced.quotElem`). -/
theorem case_quotLift : CaseQuotLift p ann ch := by
  intro k c ls args hf _ hpre hcoh ih
  have hfire : FireOk p ann ch (.quotLift c) ls args := hpre
  obtain ⟨hsp, q0, hag, hinst⟩ := hfire.inst.1 c rfl
  have harity : args.length = 6 := hfire.arity
  obtain ⟨α, r, β, f, h, qs, rfl⟩ : ∃ α r β f h qs, args = [α, r, β, f, h, qs] := by
    rcases args with _ | ⟨α, _ | ⟨r, _ | ⟨β, _ | ⟨f, _ | ⟨h, _ | ⟨qs, _ | ⟨x, rest⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at harity
    exact ⟨α, r, β, f, h, qs, rfl⟩
  -- the function is read at the instance
  have hflive : LiveSlot p ann ch f := by
    refine hfire.live 3 f rfl ?_
    rintro ⟨⟨c0, cr, r0, hc0, hcr, hpr, hirr⟩, -⟩
    simp only [headConst?, Option.some.injEq] at hc0
    rw [← hc0] at hcr
    have happ : appliedAt p c 3 = true := by simp [appliedAt, hsp]
    have h1 := hf.canon.minorsRead (c, q0) hinst cr hcr 3 r0 happ hpr
    rw [hag.irr] at h1
    rw [h1] at hirr
    cases hirr
  cases k with
  | zero =>
    refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
    · simp [fire] at hv
    · cases hst
  | succ k =>
    have hpq : Pre p ann ch (.force k qs) := by
      by_cases hm : MarkerSlot qs
      · exact Or.inr hm
      · exact Or.inl (hfire.live 5 qs rfl (fun h => hm h.2))
    have hpf : Pre p ann ch (.force k f) := Or.inl hflive
    have hpostQ := (ih _ (.single Step.liftQuot) hpq).1
    have happly : ∀ c' l' ps a fv, force p k qs = .ok (.con c' l' ps [a]) → p.isQuotCtor c' = true →
        force p k f = .ok fv → Pre p ann ch (.apply k fv (.val a)) ∧ Whole p fv := by
      intro c' l' ps a fv hq hqc hfv
      have hstF : Step p (.fire (k + 1) (.quotLift c) ls [α, r, β, f, h, qs]) (.force k f) :=
        Step.liftFun hq hqc
      have hlfv : Live p ann ch fv := force_live ih (.single hstF) hflive hfv
      have hwfv : Whole p fv := ((ih _ (.single hstF) hpf).1 fv hfv).2
      have hlq : Live p ann ch (.con c' l' ps [a]) := (hpostQ _ hq).1 rfl
      refine ⟨⟨hlfv, ?_⟩, hwfv⟩
      cases hlq with
      | con hread hwhole hplaced =>
        cases hai : a.isIrr with
        | false =>
          have hla : LiveSlot p ann ch (.val a) := .val (hread 0 a rfl (Or.inr hai)) (hwhole 0 a rfl)
          cases fv with
          | clo b d body ρ' l2 => exact fun _ => hla
          | pap h' l2 args' => exact ⟨fun _ => hla, minorsIgnore_of_whole hf hwfv⟩
          | _ => trivial
        | true =>
          have hig : IgnoresNext ann fv := by
            obtain ⟨lvq, tyq, hdq⟩ := decl_of_isQuotCtor hqc
            refine hcoh c' l' ps a fv hq hqc hfv hai ?_
            rintro ⟨d, hd, h2⟩
            rw [hdq] at hd
            cases hd
            exact hplaced.quotElem a rfl hai lvq tyq hdq h2
          cases fv with
          | clo b d body ρ' l2 =>
            intro hrel
            simp only [IgnoresNext] at hig
            rw [hig] at hrel
            cases hrel
          | pap h' l2 args' =>
            refine ⟨fun hn => absurd ⟨hig, ?_⟩ hn, minorsIgnore_of_whole hf hwfv⟩
            cases a with
            | irr t ρa la => exact ⟨t, ρa, la, rfl⟩
            | _ => simp [Value.isIrr] at hai
          | _ => trivial
    refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
    · obtain ⟨c', l', ps, a, fv, hq, hqc, hfv, hap⟩ := fire_quotLift_ok hv
      obtain ⟨hpa, hwfv⟩ := happly c' l' ps a fv hq hqc hfv
      have hpost := (ih _ (.single (Step.liftApply hq hqc hfv)) hpa).1 v hap
      exact ⟨hpost.1, hpost.2 hwfv⟩
    · cases hst with
      | liftQuot => exact hpq
      | liftFun _ _ => exact hpf
      | liftApply hq hqc hfv => exact (happly _ _ _ _ _ hq hqc hfv).1

end IxCC.Src.Relevance.Proof.P1
