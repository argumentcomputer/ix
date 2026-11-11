import IxCC.Anf.Proof.Defun.Translate

/-! # P8's output is well scoped when its input is

`wellScoped_run`: for an input whose globals lie below its size, a
well-scoped input gives a well-scoped output. The input's globals are
translated (`tr_ws`); the dispatchers are well scoped over their callee and
arguments (`dispatcher_ws`: every alternative's key is a closure key with its
source's captures and supplied arguments as fields, its calls name the
source's global with its captures and arity, or the dispatcher of the
remaining arity); the lifted functions are by the walk (`globalsGo_lws`). The
keys of the output's globals are distinct (the input's by its scoping, the
dispatchers' by arity, the lifted functions' by `sources_keys`, and the three
kinds apart since no input global is keyed `lam` or `dispatch`), as are the
table's (the closure keys by `rows_nodup`, and no input row is a closure key);
the roots stay in range, and the pinned constructors keep their arities, since
none is a closure key (`checkInput_ok`). -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

/-! ## The closure keys in the table -/

theorem find?_of_nodup {α β : Type} [BEq β] [LawfulBEq β] {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x : α}, x ∈ l → l.find? (fun y => f y == f x) = some x
  | [], _, _, hx => absurd hx List.not_mem_nil
  | y :: l, hn, x, hx => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hx with rfl | hx
    · exact List.find?_cons_of_pos (by simp)
    · have hne : f y ≠ f x := fun he => hn.1 (by rw [he]; exact List.mem_map.2 ⟨x, hx, rfl⟩)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact find?_of_nodup hn.2 hx

theorem rows_mem : ∀ {srcs : List Source} {t : Nat} {r : Lam.CtorInfo}, r ∈ rows srcs t →
    ∃ s ∈ srcs, ∃ j, j < s.arity ∧ r.key = .clo s.key j ∧ r.arity = s.caps + j
  | [], _, _, h => absurd h List.not_mem_nil
  | s :: ss, t, r, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
      exact ⟨s, List.mem_cons_self, j, List.mem_range.1 hj, rfl, rfl⟩
    · obtain ⟨s', hs', j, hj, hk, ha⟩ := rows_mem h
      exact ⟨s', List.mem_cons_of_mem _ hs', j, hj, hk, ha⟩

theorem mem_rows : ∀ {srcs : List Source} (t : Nat) {s : Source}, s ∈ srcs → ∀ {j : Nat}, j < s.arity →
    ∃ tag, ({ key := .clo s.key j, tag, arity := s.caps + j } : Lam.CtorInfo) ∈ rows srcs t
  | [], _, _, h, _, _ => absurd h List.not_mem_nil
  | s' :: ss, t, s, h, j, hj => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨t + j, List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)⟩
    · obtain ⟨tag, htag⟩ := mem_rows (t + s'.arity) h hj
      exact ⟨tag, List.mem_append_right _ htag⟩

/-- The closure keys of sources with distinct keys are distinct. -/
theorem rows_nodup : ∀ {srcs : List Source} (t : Nat), (srcs.map (·.key)).Nodup →
    ((rows srcs t).map (·.key)).Nodup
  | [], _, _ => List.nodup_nil
  | s :: ss, t, hn => by
    rw [List.map_cons, List.nodup_cons] at hn
    unfold rows
    rw [List.map_append, List.nodup_append, List.map_map]
    refine ⟨nodup_map_of_inj (fun a b h => ?_) List.nodup_range, rows_nodup _ hn.2, fun a ha b hb hab => ?_⟩
    · simp only [Function.comp, Key.CtorKey.clo.injEq] at h
      exact h.2
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hb
      obtain ⟨s', hs', j', -, hk, -⟩ := rows_mem hr
      simp only [Function.comp, hk, Key.CtorKey.clo.injEq] at hab
      exact hn.1 (hab.1 ▸ List.mem_map.2 ⟨s', hs', rfl⟩)

/-! ## The output's signature -/

theorem assemble_ctor? (P : Program) (gs : List (GlobalId × GDef)) (acc : Acc) (c : Key.CtorKey) :
    (assemble P gs acc).ctor? c = (P.ctor? c).or ((rows (sources P acc) 0).find? (·.key == c)) := by
  unfold assemble Program.ctor?
  exact List.find?_append

/-- A constructor that is no closure key has, in the output, the arity it had. -/
theorem assemble_ctorArity_src {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {c : Key.CtorKey}
    (hc : closureKey c = false) : (assemble P gs acc).sig.ctorArity? c = P.sig.ctorArity? c := by
  show ((assemble P gs acc).ctor? c).map (·.arity) = (P.ctor? c).map (·.arity)
  rw [assemble_ctor?]
  have : (rows (sources P acc) 0).find? (·.key == c) = none := by
    rw [List.find?_eq_none]
    intro r hr he
    obtain ⟨s, -, j, -, hk, -⟩ := rows_mem hr
    rw [beq_iff_eq, hk] at he
    rw [← he] at hc
    cases hc
  rw [this]
  cases P.ctor? c <;> rfl

/-- **What scoping reads from P8's output**, for an input whose globals lie
below its size and whose constructor table keys are distinct. -/
theorem sigOk_ran {P : Program} (hwf : ∀ g gd, P.global? g = some gd → g < P.size)
    {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId} (hr : Ran P gs acc parents) :
    SigOk (setting P gs acc) where
  ctor c n h := by
    show ((assemble P gs acc).ctor? c).map (·.arity) = some n
    rw [assemble_ctor?]
    show ((P.ctor? c).or _).map _ = some n
    cases hc : P.ctor? c with
    | none => change (P.ctor? c).map (·.arity) = some n at h; rw [hc] at h; cases h
    | some r => change (P.ctor? c).map (·.arity) = some n at h; rw [hc] at h; exact h
  arity g n h := by
    change (P.global? g).map (·.arity) = some n at h
    cases hg : P.global? g with
    | none => rw [hg] at h; cases h
    | some gd =>
      rw [hg] at h
      obtain ⟨gd', a, a', hq, hgl, -⟩ := assemble_old hr (hwf g gd hg) hg
      show ((assemble P gs acc).global? g).map (·.arity) = some n
      rw [hq, ← h]
      simp only [Option.map_some, GDef.arity, global_ps hgl]
  size := by
    show P.size ≤ liftBase P acc + acc.lifted.length
    unfold liftBase
    omega
  clo s hs j hj := by
    obtain ⟨tag, hm⟩ := mem_rows 0 hs hj
    have hnd := rows_nodup 0 (sources_keys hr)
    have hfind := find?_of_nodup hnd hm
    show ((assemble P gs acc).ctor? _).map (·.arity) = _
    rw [assemble_ctor?]
    have hP : P.ctor? (.clo s.key j) = none := by
      unfold Program.ctor?
      rw [List.find?_eq_none]
      intro r hr0 he
      rw [beq_iff_eq] at he
      have := (checkInput_ok hr.input).2.1 r hr0
      rw [he] at this
      cases this
    rw [hP]
    exact congrArg (Option.map (·.arity)) hfind
  disp m h1 h2 := by
    show ((assemble P gs acc).global? (dispId P.size m)).map (·.arity) = some (m + 1)
    rw [assemble_disp hr h1 h2]
    simp [GDef.arity, dispatcher]

/-! ## The dispatchers are well scoped -/

theorem wsList_append {Γ : Nat} : ∀ {as bs : List Atom}, Atom.WSList Γ as → Atom.WSList Γ bs →
    Atom.WSList Γ (as ++ bs)
  | [], _, _, hb => hb
  | _ :: _, _, ha, hb => ⟨ha.1, wsList_append ha.2 hb⟩

theorem wsList_downFrom {Γ : Nat} : ∀ (top count : Nat), (count = 0 ∨ top < Γ) →
    Atom.WSList Γ (downFrom top count)
  | _, 0, _ => trivial
  | top, c + 1, h => by
    rw [downFrom_succ]
    rcases h with h | h
    · cases h
    · exact ⟨h, wsList_downFrom (top - 1) c (.inr (by omega))⟩

theorem downFrom_length (top count : Nat) : (downFrom top count).length = count := by
  simp [downFrom]

theorem altsWS_append {S : Sig} {Γ : Nat} {Δ : List Nat} : ∀ {as bs : List Alt}, Exp.AltsWS S Γ Δ as →
    Exp.AltsWS S Γ Δ bs → Exp.AltsWS S Γ Δ (as ++ bs)
  | [], _, _, hb => hb
  | .mk _ _ _ :: _, _, ha, hb => ⟨ha.1, ha.2.1, altsWS_append ha.2.2 hb⟩

theorem altKeys_append : ∀ (as bs : List Alt), altKeys (as ++ bs) = altKeys as ++ altKeys bs
  | [], _ => rfl
  | .mk _ _ _ :: as, bs => by simp only [List.cons_append, altKeys, altKeys_append as bs]

theorem altKeys_dispAlts (size m : Nat) : ∀ (srcs : List Source) (t : Nat),
    altKeys (dispAlts size m srcs) = (rows srcs t).map (·.key)
  | [], _ => rfl
  | s :: ss, t => by
    simp only [dispAlts, rows, altKeys_append, List.map_append, altKeys_dispAlts size m ss (t + s.arity)]
    congr 1
    generalize List.range s.arity = js
    induction js with
    | nil => rfl
    | cons j js ih => simp only [List.map_cons, altKeys, ih]

section

variable {X : Setting} (hS : SigOk X)
  (hsrc : ∀ s ∈ X.srcs, X.Q.sig.arity? s.id = some (s.caps + s.arity))
include hS hsrc

theorem altBody_ws {s : Source} (hs : s ∈ X.srcs) {j m : Nat} (hj : j < s.arity) (h1 : 1 ≤ m) (h2 : m ≤ X.M) :
    (altBody X.P.size s j m).WS X.Q.sig (m + 1 + (s.caps + j)) [] := by
  have hF : ∀ c, c ≤ s.caps + j → Atom.WSList (m + 1 + (s.caps + j)) (downFrom (s.caps + j - 1) c) :=
    fun c hc => wsList_downFrom _ _ (by omega)
  have hA : Atom.WSList (m + 1 + (s.caps + j)) (downFrom (s.caps + j + m - 1) m) :=
    wsList_downFrom _ _ (by omega)
  have hfs := hF (s.caps + j) (Nat.le_refl _)
  unfold altBody
  dsimp only
  split
  · rename_i hm
    refine ⟨⟨?_, ?_, wsList_append hfs hA⟩, by show 0 < _; omega⟩
    · rw [hsrc s hs, List.length_append, downFrom_length, downFrom_length]
      congr 1
      omega
    · intro he
      have := congrArg List.length he
      simp only [List.length_append, downFrom_length, List.length_nil] at this
      omega
  · split
    · rename_i hm hlt
      refine ⟨⟨?_, wsList_append hfs hA⟩, by show 0 < _; omega⟩
      rw [hS.clo s hs (j + m) (by omega), List.length_append, downFrom_length, downFrom_length]
      congr 1
      omega
    · rename_i hm hlt
      have hr : s.arity - j ≤ m := by omega
      refine ⟨⟨?_, ?_, wsList_append hfs ?_⟩, ⟨?_, ?_, ?_, ?_⟩, by show 0 < _; omega⟩
      · rw [hsrc s hs, List.length_append, downFrom_length, List.length_take, downFrom_length]
        congr 1
        omega
      · intro he
        have := congrArg List.length he
        simp only [List.length_append, downFrom_length, List.length_take, List.length_nil] at this
        omega
      · rw [downFrom_take _ _ _ hr]
        exact wsList_downFrom _ _ (by omega)
      · have := hS.disp (m - (s.arity - j)) (by omega) (by omega)
        rw [Setting.dispId] at this
        rw [this, List.length_cons, List.length_map, List.length_drop, downFrom_length]
      · exact List.cons_ne_nil _ _
      · show 0 < _
        omega
      · rw [downFrom_drop _ _ _ hr, downFrom_map_shift _ _ (by omega)]
        exact wsList_downFrom _ _ (by omega)

theorem keyAlts_ws {s : Source} (hs : s ∈ X.srcs) {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ X.M) :
    ∀ js : List Nat, (∀ j ∈ js, j < s.arity) →
      Exp.AltsWS X.Q.sig (m + 1) [] (js.map fun j => Alt.mk (.clo s.key j) (s.caps + j) (altBody X.P.size s j m))
  | [], _ => trivial
  | j :: js, h => ⟨hS.clo s hs j (h j List.mem_cons_self), altBody_ws hS hsrc hs (h j List.mem_cons_self) h1 h2,
      keyAlts_ws hs h1 h2 js fun j' hj' => h j' (List.mem_cons_of_mem _ hj')⟩

theorem dispAlts_ws {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ X.M) :
    ∀ srcs : List Source, (∀ s ∈ srcs, s ∈ X.srcs) → Exp.AltsWS X.Q.sig (m + 1) [] (dispAlts X.P.size m srcs)
  | [], _ => trivial
  | s :: ss, h => altsWS_append
      (keyAlts_ws hS hsrc (h s List.mem_cons_self) h1 h2 _ fun _ hj => List.mem_range.1 hj)
      (dispAlts_ws h1 h2 ss fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))

/-- **A dispatcher is well scoped** over its callee and arguments. -/
theorem dispatcher_ws (hk : (X.srcs.map (·.key)).Nodup) {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ X.M) :
    (dispatcher X.P.size X.srcs m).body.WS X.Q.sig (m + 1) [] :=
  ⟨Nat.lt_succ_self m, dispAlts_ws hS hsrc h1 h2 X.srcs fun _ h => h,
    by rw [altKeys_dispAlts _ _ _ 0]; exact rows_nodup 0 hk, trivial⟩

end

/-! ## The output is well scoped -/

theorem globalsGo_lws {X : Setting} {accF : Acc} (hF : Final X accF) (hS : SigOk X) :
    ∀ (l : List (GlobalId × GDef)) (acc : Acc) (parents : List GlobalId) (out : List (GlobalId × GDef))
    {gs : List (GlobalId × GDef)} {PF : List GlobalId},
    (∀ p ∈ l, Exp.WS X.P.sig p.2.ps.length [] p.2.body) → LWS X acc →
    globalsGo X.P l acc parents out = .ok (gs, accF, PF) → LWS X accF
  | [], _, _, _, _, _, _, hl, h => by
    simp only [globalsGo, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact hl
  | (g, gd) :: rest, acc, parents, out, gs, PF, hws, hl, h => by
    simp only [globalsGo] at h
    cases hg : Defun.global X.P g gd acc with
    | error e => simp only [hg] at h; cases h
    | ok r =>
      obtain ⟨gd', acc1⟩ := r
      simp only [hg] at h
      have := (global_tr hF hg (globalsGo_le rest _ _ _ h)).2.2 hS (hws _ List.mem_cons_self) hl
      exact globalsGo_lws hF hS rest acc1 _ _ (fun p hp => hws p (List.mem_cons_of_mem _ hp)) this h

theorem globalsGo_key {P : Program} : ∀ (l : List (GlobalId × GDef)) (acc : Acc) (parents : List GlobalId)
    (out : List (GlobalId × GDef)) {gs : List (GlobalId × GDef)} {accF : Acc} {PF : List GlobalId},
    (∀ g gd', (g, gd') ∈ out → ∃ gd, P.global? g = some gd ∧ gd'.key = gd.key) →
    (∀ g gd, (g, gd) ∈ l → P.global? g = some gd) →
    globalsGo P l acc parents out = .ok (gs, accF, PF) →
    ∀ g gd', (g, gd') ∈ gs → ∃ gd, P.global? g = some gd ∧ gd'.key = gd.key
  | [], _, _, out, gs, _, _, hout, _, h => by
    simp only [globalsGo, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    intro g gd' hx
    exact hout g gd' (List.mem_reverse.1 hx)
  | (g, gd) :: rest, acc, parents, out, gs, accF, PF, hout, hl, h => by
    simp only [globalsGo] at h
    cases hg : Defun.global P g gd acc with
    | error e => simp only [hg] at h; cases h
    | ok r =>
      obtain ⟨gd', acc1⟩ := r
      simp only [hg] at h
      refine globalsGo_key rest acc1 _ ((g, gd') :: out) (fun g₁ gd₁ hx => ?_)
        (fun g₁ gd₁ hx => hl g₁ gd₁ (List.mem_cons_of_mem _ hx)) h
      rcases List.mem_cons.1 hx with he | hx
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨gd, hl _ _ List.mem_cons_self, ?_⟩
        simp only [Defun.global] at hg
        obtain ⟨⟨body, acc2⟩, -, hg⟩ := bind_ok hg
        dsimp only at hg
        obtain ⟨hq1, -⟩ := Prod.mk.inj (pure_ok hg)
        rw [← hq1]
      · exact hout g₁ gd₁ hx

theorem numbered_map_snd {α β : Type} (f : α → β) : ∀ (k : Nat) (xs : List α),
    (numbered k xs).map (fun p => f p.2) = xs.map f
  | _, [] => rfl
  | k, x :: xs => by simp only [numbered, List.map_cons, numbered_map_snd f (k + 1) xs]

theorem numbered_get {α : Type} : ∀ (k : Nat) (xs : List α) (i : Nat), k ≤ i → i < k + xs.length →
    ∃ x, (i, x) ∈ numbered k xs
  | _, [], _, h1, h2 => absurd h2 (by simp only [List.length_nil, Nat.add_zero]; omega)
  | k, x :: xs, i, h1, h2 => by
    by_cases hi : i = k
    · exact ⟨x, by rw [hi]; exact List.mem_cons_self⟩
    · obtain ⟨y, hy⟩ := numbered_get (k + 1) xs i (by omega) (by simp only [List.length_cons] at h2; omega)
      exact ⟨y, List.mem_cons_of_mem _ hy⟩

/-- An entry of the output's global map, as `assemble` lists it. -/
theorem assemble_cases {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {g : GlobalId} {gd : GDef}
    (h : (assemble P gs acc).global? g = some gd) :
    (g, gd) ∈ gs ∨ (∃ i, i < acc.maxApp ∧ g = P.size + i ∧ gd = dispatcher P.size (sources P acc) (i + 1)) ∨
      ((g, gd.key) ∈ (liftedAt P acc).map (fun p => (p.1, p.2.key))) := by
  have hm := ofList_mem h
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · exact .inl hm
  · obtain ⟨i, hi, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    exact .inr (.inl ⟨i, List.mem_range.1 hi, he.1.symm, he.2.symm⟩)
  · obtain ⟨⟨i, l⟩, hli, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .inr (.inr (List.mem_map.2 ⟨(i, l), hli, rfl⟩))

theorem nodup_map_of_fst {α β : Type} {f : Nat × α → β} :
    ∀ {l : List (Nat × α)}, (l.map (·.1)).Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → a.1 = b.1) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hn, h => by
    rw [List.map_cons, List.nodup_cons] at hn ⊢
    refine ⟨fun hm => ?_, nodup_map_of_fst hn.2 fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy)⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.1 hm
    have := h b (List.mem_cons_of_mem _ hb) a List.mem_cons_self he
    exact hn.1 (by rw [← this]; exact List.mem_map.2 ⟨b, hb, rfl⟩)

/-- **The output is well scoped when the input is**, for an input whose
globals lie below its size. -/
theorem wellScoped_ran {P : Program} (hwf : ∀ g gd, P.global? g = some gd → g < P.size) (hws : WellScoped P)
    {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId} (hr : Ran P gs acc parents) :
    WellScoped (assemble P gs acc) := by
  have hS := sigOk_ran hwf hr
  have hF := final_ran hr
  have hk := sources_keys hr
  have hsrc : ∀ s ∈ (setting P gs acc).srcs, (setting P gs acc).Q.sig.arity? s.id = some (s.caps + s.arity) := by
    intro s hs
    obtain ⟨gd, hgd, hps⟩ := sources_global hr hs
    show ((assemble P gs acc).global? s.id).map (·.arity) = _
    rw [hgd, ← hps]
    rfl
  have hlws : LWS (setting P gs acc) acc :=
    globalsGo_lws hF hS P.globalList {} [] [] (fun p hp => by
      obtain ⟨hlt, hgd⟩ := mem_globalList.1 hp
      obtain ⟨gd, hgd', hb⟩ := hws.globals p.1 hlt
      rw [hgd] at hgd'
      cases hgd'
      exact hb) (fun _ h => absurd h List.not_mem_nil) hr.walk
  obtain ⟨hres, hclo, hkn⟩ := checkInput_ok hr.input
  obtain ⟨hlift, hfrom⟩ := ran_lifted_keys hr
  refine ⟨fun g hg => ?_, ?_, ?_, fun r hr' => ?_, ?_⟩
  · -- every global below the size, with a well-scoped body
    by_cases h1 : g < P.size
    · obtain ⟨gd, hgd, hb⟩ := hws.globals g h1
      obtain ⟨gd', a, a', hq, hgl, hle⟩ := assemble_old hr h1 hgd
      obtain ⟨hps, htr, -⟩ := global_tr hF hgl hle
      refine ⟨gd', hq, ?_⟩
      rw [hps]
      exact tr_ws hS htr hb
    · by_cases h2 : g < P.size + acc.maxApp
      · have hm1 : 1 ≤ g - P.size + 1 := by omega
        have hm2 : g - P.size + 1 ≤ acc.maxApp := by omega
        have hid : dispId P.size (g - P.size + 1) = g := by
          show P.size + (g - P.size + 1) - 1 = g
          omega
        have := assemble_disp hr hm1 hm2
        rw [hid] at this
        refine ⟨_, this, ?_⟩
        have hd := dispatcher_ws hS hsrc hk hm1 hm2
        have hlen : (dispatcher P.size (sources P acc) (g - P.size + 1)).ps.length = g - P.size + 1 + 1 := by
          simp [dispatcher]
        rw [hlen]
        exact hd
      · have hsz : g < liftBase P acc + acc.lifted.reverse.length := by
          rw [List.length_reverse]; exact hg
        obtain ⟨l, hl⟩ := numbered_get (liftBase P acc) acc.lifted.reverse g (by unfold liftBase; omega) hsz
        refine ⟨l.toGDef, assemble_lifted hr hl, ?_⟩
        have := hlws l (List.mem_reverse.1 (mem_numbered hl).1)
        have hlen : l.toGDef.ps.length = l.ncaps + l.ps.length := by simp [Lifted.toGDef]
        rw [hlen]
        exact this
  · -- distinct global keys
    apply nodup_map_of_fst (globalList_ids_nodup _)
    intro ⟨g, gd⟩ ha ⟨g', gd'⟩ hb hab
    dsimp only at hab ⊢
    have hga := (mem_globalList.1 ha).2
    have hgb := (mem_globalList.1 hb).2
    have hgs := globalsGo_key P.globalList {} [] [] (by simp) (fun g gd hx => (mem_globalList.1 hx).2) hr.walk
    have hliftKey : ∀ {i : GlobalId} {k : Key.GKey}, (i, k) ∈ (liftedAt P acc).map (fun p => (p.1, p.2.key)) →
        ∃ K j, k = .lam K [j] := fun hm => by
      obtain ⟨⟨i, l⟩, hli, he⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at he
      rw [← he.2]
      obtain ⟨_, -, gd0, -, j, hj⟩ := hfrom l.key (List.mem_map.2 ⟨l, List.mem_reverse.1 (mem_numbered hli).1, rfl⟩)
      exact ⟨gd0.key, j, hj⟩
    have hold : ∀ {g : GlobalId} {gd : GDef}, (g, gd) ∈ gs → reservedKey gd.key = false ∧
        ∃ gd0, P.global? g = some gd0 ∧ g < P.size ∧ gd.key = gd0.key := fun hm => by
      obtain ⟨gd0, hg0, hk0⟩ := hgs _ _ hm
      have hlt := hwf _ _ hg0
      refine ⟨?_, gd0, hg0, hlt, hk0⟩
      rw [hk0]
      exact hres _ (mem_globalList.2 ⟨hlt, hg0⟩)
    rcases assemble_cases hga with hm | ⟨i, hi, rfl, rfl⟩ | hm <;>
      rcases assemble_cases hgb with hm' | ⟨i', hi', rfl, rfl⟩ | hm'
    · obtain ⟨-, gd0, hg0, hlt, hk0⟩ := hold hm
      obtain ⟨-, gd0', hg0', hlt', hk0'⟩ := hold hm'
      have := eq_of_nodup_map hws.keys (mem_globalList.2 ⟨hlt, hg0⟩) (mem_globalList.2 ⟨hlt', hg0'⟩)
        (by dsimp only; rw [← hk0, ← hk0']; exact hab)
      exact (Prod.mk.inj this).1
    · have := (hold hm).1
      rw [hab] at this
      cases this
    · obtain ⟨K, j, hk'⟩ := hliftKey hm'
      have := (hold hm).1
      rw [hab, hk'] at this
      cases this
    · have := (hold hm').1
      rw [← hab] at this
      cases this
    · simp only [dispatcher, Key.GKey.dispatch.injEq] at hab
      rw [show i = i' by omega]
    · obtain ⟨K, j, hk'⟩ := hliftKey hm'
      rw [hk'] at hab
      cases hab
    · obtain ⟨K, j, hk'⟩ := hliftKey hm
      have := (hold hm').1
      rw [← hab, hk'] at this
      cases this
    · obtain ⟨K, j, hk'⟩ := hliftKey hm
      rw [hk'] at hab
      cases hab
    · have hnd : (((liftedAt P acc).map (fun p => (p.1, p.2.key))).map (·.2)).Nodup := by
        rw [List.map_map]
        show ((liftedAt P acc).map (fun p => p.2.key)).Nodup
        unfold liftedAt
        rw [numbered_map_snd (fun l : Lifted => l.key), List.map_reverse]
        exact (List.reverse_perm _).nodup_iff.2 hlift
      have := eq_of_nodup_map hnd hm hm' hab
      exact (Prod.mk.inj this).1
  · -- distinct constructor keys
    show ((P.ctors ++ rows (sources P acc) 0).map (·.key)).Nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨hws.ctorKeys, rows_nodup 0 hk, fun a ha b hb hab => ?_⟩
    obtain ⟨r, hr0, rfl⟩ := List.mem_map.1 ha
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hb
    obtain ⟨s, -, j, -, hk', -⟩ := rows_mem hr'
    have := hclo r hr0
    rw [hab, hk'] at this
    cases this
  · -- roots
    show r < liftBase P acc + acc.lifted.length
    exact Nat.lt_of_lt_of_le (hws.roots r hr') (by unfold liftBase; omega)
  · -- the pinned constructors
    have hP := hws.known
    have hsig : ∀ c, closureKey c = false →
        (assemble P gs acc).sig.ctorArity? c = P.sig.ctorArity? c := fun c hc => assemble_ctorArity_src hc
    show knownConsistent P.known (assemble P gs acc).sig = true
    unfold knownClosure at hkn
    unfold knownConsistent at hP ⊢
    cases h0 : P.known.natZero <;> cases h1 : P.known.natSucc <;> cases h2 : P.known.boolFalse <;>
      cases h3 : P.known.boolTrue <;> simp_all

/-- **`wellScoped_run`**: P8's output is well scoped when its input is, for an
input whose globals lie below its size. -/
theorem wellScoped_run {P Q : Program} (hwf : ∀ g gd, P.global? g = some gd → g < P.size) (hws : WellScoped P)
    (h : run P = .ok Q) : WellScoped Q := by
  obtain ⟨gs, acc, parents, hr, rfl⟩ := run_ran h
  exact wellScoped_ran hwf hws hr

end IxCC.Anf.Defun.Proof
