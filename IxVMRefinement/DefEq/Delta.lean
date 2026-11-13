import IxVMRefinement.DefEq.Basic

/-! # Step lemmas of `KernelDefEq`: lazy δ

The loop (`lazy_delta_loop`) and its steps return the inputs or reducts of them
(`Specs.DefEq.LoopResult`): every exit `(0, a, b)` is `Red.refl`; a δ step (`delta_unfold`:
`Red.delta`, or `Red.deltaThm` with `EnvFacts.thmTyped`, under the spine by `Red.appFn`) and the
head normalization after it (`whnf_nd`) chain by `Red.trans`, and a tag other than `0` returned on
reducts is carried back to the inputs by `DefEq.redBoth`. The loaded constants only select
(`is_defn_or_thm`, `delta_rank`): each unfolding reloads its head.

`delta_unfold` takes its second arm only where `red_unfold`'s tag is not `0`; its generated path
does not record that, so its paths are read off its derivation here (`delta_unfold_obs`). -/

namespace IxVM.Refinement.Core.DefEqAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq DefEqList)

set_option linter.unusedVariables false

/-! ## Pairs, triples and lazy-δ results -/

private theorem tuple2_inj {a b c d : SourceValue F}
    (h : (.tuple [a, b] : SourceValue F) = .tuple [c, d]) : a = c ∧ b = d := by
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at h
  exact h

private theorem tuple3_inj {a b c d e f : SourceValue F}
    (h : (.tuple [a, b, c] : SourceValue F) = .tuple [d, e, f]) : a = d ∧ b = e ∧ c = f := by
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at h
  exact h

/-- Tags `0` and `1` differ. -/
private theorem tag_contra {r x y : SourceValue F} (h0 : r = .tuple [.field 0, y])
    (h1 : r = .tuple [.field 1, x]) : False :=
  field_one_ne_zero (tuple2_inj (h1.symm.trans h0)).1

/-- **A lazy-δ result returning the inputs**: its tag, where not `0`, comes with `DefEq`. -/
theorem loopResult_same {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h' : Heap F}
    {t a b : SourceValue F} {A B : KExpr} (hA : c.tm d Γ h' A a) (hB : c.tm d Γ h' B b)
    (hd : t ≠ .field 0 → DefEq c.env d A B) :
    Specs.DefEq.LoopResult c d Γ h' (.tuple [t, a, b]) A B := by
  intro tag fa fb hr
  obtain ⟨rfl, rfl, rfl⟩ := tuple3_inj hr
  exact ⟨A, B, hA, hB, .refl, .refl, hd⟩

/-- **The exit `(0, a, b)`**: the inputs, unreduced. -/
theorem loopResult_zero {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h h' : Heap F}
    {a b : SourceValue F} {A B : KExpr} (ext : Heap.Extends h h') (hA : c.tm d Γ h A a)
    (hB : c.tm d Γ h B b) : Specs.DefEq.LoopResult c d Γ h' (.tuple [.field 0, a, b]) A B :=
  loopResult_same (Tm.mono ext hA) (Tm.mono ext hB) fun ht => absurd rfl ht

/-- **A lazy-δ result on reducts is one on the originals** (`Red.trans`, `DefEq.redBoth`). -/
theorem loopResult_red {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h' : Heap F} {r : SourceValue F}
    {A B A' B' : KExpr} (hl : Specs.DefEq.LoopResult c d Γ h' r A' B')
    (ha : Red c.env d A A') (hb : Red c.env d B B') :
    Specs.DefEq.LoopResult c d Γ h' r A B := by
  intro tag fa fb hr
  obtain ⟨FA, FB, hFA, hFB, hra, hrb, hd⟩ := hl tag fa fb hr
  exact ⟨FA, FB, hFA, hFB, .trans ha hra, .trans hb hrb, fun ht => .redBoth ha hb (hd ht)⟩

/-! ## Loaded constants -/

/-- A loaded `Thm` represents a stored theorem. -/
theorem ciRep_thm_inv {κ : _root_.Address → KKey} {h : Heap F} {nl ty val : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h (.construct kciEnum "Thm" [nl, ty, val]) ci) : ∃ cv V, ci = .thmInfo cv V := by
  generalize hv : (Value.construct kciEnum "Thm" [nl, ty, val] : SourceValue F) = v at r
  cases r
  case thm => exact ⟨_, _, rfl⟩
  all_goals (injection hv with _ hc _; exact absurd hc (by decide))

/-! ## `delta_unfold`'s paths -/

/-- `red_unfold`'s tag is a field. -/
theorem red_unfold_tag {v l : SourceValue F} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn W "KernelWhnf::red_unfold" [v, l] h r h' calls) :
    ∃ (t : F) (x : SourceValue F), r = .tuple [.field t, x] := by
  cases Obs.«KernelWhnf::red_unfold».obs ev <;> (subst_vars; exact ⟨_, _, rfl⟩)

/-- Matching a list of patterns one pattern further. -/
theorem matchListWith_cons_some {A : Type}
    {f : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {p : A} {ps : List A} {v : SourceValue F} {vs : List (SourceValue F)}
    {b1 b2 : Environment F Nat} (h1 : f p v = .ok (some b1))
    (h2 : Aiur.Generic.SourceSemantics.matchListWith f ps vs = .ok (some b2)) :
    Aiur.Generic.SourceSemantics.matchListWith f (p :: ps) (v :: vs) = .ok (some (b1 ++ b2)) := by
  simp [Aiur.Generic.SourceSemantics.matchListWith, h1, h2, bind, Except.bind, pure, Except.pure]

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- A pair the pattern `(0, _)` does not match has a first component other than `0`. -/
theorem tag_ne_zero_of_none {world : Aiur.Generic.SourceSemantics.World F}
    {types : Aiur.Generic.SourceSemantics.Types} {heap : Heap F} {w x : SourceValue F}
    (h : world.matchPattern types heap (.tuple [.literal 0, .wildcard]) (.tuple [w, x]) =
      .ok none) :
    w ≠ .field 0 := by
  intro hw
  subst hw
  have h1 : world.matchPattern types heap (.literal (0 : F)) (.field 0) = .ok (some []) := by
    rw [MatchesConst.literal (world := world) (types := types) (0 : F) heap (.field 0),
      ite_eq_left rfl]
  have e := matchListWith_cons_some (f := world.matchPattern types heap) h1
    (matchListWith_cons_some (f := world.matchPattern types heap)
    (matchPattern_wildcard (world := world) (types := types) x heap)
    (rfl : Aiur.Generic.SourceSemantics.matchListWith (world.matchPattern types heap) [] [] =
      .ok (some [])))
  rw [matchPattern_tuple] at h
  split at h
  · rename_i hlen
    first | exact absurd hlen (by decide) | simp at hlen
  · rw [e] at h
    first | cases h | simp at h

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
/-- **The paths of `KernelDefEq::delta_unfold`**, read off its derivation: the input back with
tag `0`, or a constant head whose `red_unfold` tag is not `0`, with `apply_spine`'s term and
tag `1`. -/
theorem delta_unfold_obs {x_e : SourceValue F} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn W "KernelDefEq::delta_unfold" [x_e] h r h' calls) :
    r = .tuple [.field 0, x_e] ∨
    ∃ (m2 : Heap F) (cs13 : List (Call F)) (x_head x_spine x_addr x_lvls : SourceValue F)
      (m70 : Heap F) (cs81 : List (Call F)) (v84 : SourceValue F) (m87 : Heap F)
      (p92 : SourceValue F) (cs98 : List (Call F)) (w161 x_body v175 : SourceValue F)
      (m184 : Heap F) (cs192 : List (Call F)),
      ObsFn W "KernelTypes::collect_spine" [x_e] h (.tuple [x_head, x_spine]) m2 cs13 ∧
      loadValue m2 x_head =
        .ok (.construct "KernelTypes::KExprNode" "Const" [x_addr, x_lvls]) ∧
      ObsFn W "Ingress::get_ci" [x_addr] m2 p92 m87 cs98 ∧
      loadValue m87 p92 = .ok v84 ∧
      ObsFn W "KernelWhnf::red_unfold" [v84, x_lvls] m87 (.tuple [w161, x_body]) m70 cs81 ∧
      w161 ≠ .field 0 ∧
      r = .tuple [.field 1, v175] ∧
      ObsFn W "KernelWhnf::apply_spine" [x_body, x_spine] m70 v175 m184 cs192 ∧
      h' = m184 ∧
      calls = ((⟨"KernelTypes::collect_spine", [x_e], h⟩ : Call F) ::
        (cs13 ++ ((⟨"Ingress::get_ci", [x_addr], m2⟩ : Call F) ::
        (cs98 ++ ((⟨"KernelWhnf::red_unfold", [v84, x_lvls], m87⟩ : Call F) ::
        (cs81 ++ ((⟨"KernelWhnf::apply_spine", [x_body, x_spine], m70⟩ : Call F) ::
        cs192))))))) := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelDefEq.delta_unfold.lookup
    (by simp [IxVM.KernelDefEq.delta_unfold, ControlLower.hasControl]) ev
  simp only [IxVM.KernelDefEq.delta_unfold] at d0
  obtain ⟨v1, m2, bs3, body4, c5, c6, d7, sel8, d9, rfl⟩ := d0.matchValue_inv
  obtain ⟨vs10, m11, c12, cs13, a14, ev15, rfl⟩ := d7.call_inv
  rw [instanceName_plain_some] at ev15
  obtain ⟨v16, vs17, m18, c19, c20, rfl, d21, a22, rfl⟩ := a14.cons_inv
  obtain ⟨l23, rfl, rfl⟩ := d21.var_inv
  simp at l23
  subst l23
  obtain ⟨rfl, rfl, rfl⟩ := a22.nil_inv
  rcases selectArm_cons_inv sel8 with ⟨mt24, rfl⟩ | ⟨nm25, sel26⟩
  · obtain ⟨vs27, hv28, -, ml29⟩ := matchPattern_tuple_inv mt24
    subst hv28
    obtain ⟨x_head, vs30, b31, b32, rfl, mt33, ml34, rfl⟩ := matchListWith_cons_inv ml29
    obtain rfl := matchPattern_bind_inv mt33
    obtain ⟨x_spine, vs35, b36, b37, rfl, mt38, ml39, rfl⟩ := matchListWith_cons_inv ml34
    obtain rfl := matchPattern_bind_inv mt38
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml39
    obtain ⟨v40, m41, bs42, body43, c44, c45, d46, sel47, d48, rfl⟩ := d9.matchValue_inv
    obtain ⟨p49, d50, ld51⟩ := d46.load_inv
    obtain ⟨l52, rfl, rfl⟩ := d50.var_inv
    simp at l52
    subst l52
    rcases selectArm_cons_inv sel47 with ⟨mt53, rfl⟩ | ⟨nm54, sel55⟩
    · obtain ⟨vs56, hv57, -, ml58⟩ := matchPattern_construct_inv mt53
      rw [IxVM.Refinement.Obs.Names.n14861064886094815840] at hv57
      subst hv57
      obtain ⟨x_addr, vs59, b60, b61, rfl, mt62, ml63, rfl⟩ := matchListWith_cons_inv ml58
      obtain rfl := matchPattern_bind_inv mt62
      obtain ⟨x_lvls, vs64, b65, b66, rfl, mt67, ml68, rfl⟩ := matchListWith_cons_inv ml63
      obtain rfl := matchPattern_bind_inv mt67
      obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml68
      obtain ⟨v69, m70, bs71, body72, c73, c74, d75, sel76, d77, rfl⟩ := d48.matchValue_inv
      obtain ⟨vs78, m79, c80, cs81, a82, ev83, rfl⟩ := d75.call_inv
      rw [instanceName_plain_some] at ev83
      obtain ⟨v84, vs86, m87, c88, c89, rfl, d90, a91, rfl⟩ := a82.cons_inv
      obtain ⟨p92, d93, ld94⟩ := d90.load_inv
      obtain ⟨vs95, m96, c97, cs98, a99, ev100, rfl⟩ := d93.call_inv
      rw [instanceName_plain_some] at ev100
      obtain ⟨v101, vs102, m103, c104, c105, rfl, d106, a107, rfl⟩ := a99.cons_inv
      obtain ⟨l108, rfl, rfl⟩ := d106.var_inv
      simp at l108
      subst l108
      obtain ⟨rfl, rfl, rfl⟩ := a107.nil_inv
      obtain ⟨v85, vs109, m110, c111, c112, rfl, d113, a114, rfl⟩ := a91.cons_inv
      obtain ⟨l115, rfl, rfl⟩ := d113.var_inv
      simp at l115
      subst l115
      obtain ⟨rfl, rfl, rfl⟩ := a114.nil_inv
      rcases selectArm_cons_inv sel76 with ⟨mt116, rfl⟩ | ⟨nm117, sel118⟩
      · obtain ⟨vs119, hv120, -, ml121⟩ := matchPattern_tuple_inv mt116
        subst hv120
        obtain ⟨w122, vs124, b125, b126, rfl, mt127, ml128, rfl⟩ := matchListWith_cons_inv ml121
        obtain ⟨hv129, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 0) mt127
        subst hv129
        obtain ⟨w123, vs130, b131, b132, rfl, mt133, ml134, rfl⟩ := matchListWith_cons_inv ml128
        obtain rfl := matchPattern_wildcard_inv mt133
        obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml134
        obtain ⟨vs135, a136, rfl⟩ := d77.tuple_inv
        obtain ⟨v137, vs140, m141, c142, c143, rfl, d144, a145, rfl⟩ := a136.cons_inv
        obtain ⟨rfl, rfl, rfl⟩ := d144.literal_inv
        obtain ⟨v138, vs146, m147, c148, c149, rfl, d150, a151, rfl⟩ := a145.cons_inv
        obtain ⟨l152, rfl, rfl⟩ := d150.var_inv
        simp at l152
        subst l152
        obtain ⟨rfl, rfl, rfl⟩ := a151.nil_inv
        exact .inl rfl
      · rcases selectArm_cons_inv sel118 with ⟨mt155, rfl⟩ | ⟨nm156, sel157⟩
        · obtain ⟨vs158, hv159, -, ml160⟩ := matchPattern_tuple_inv mt155
          subst hv159
          obtain ⟨w161, vs162, b163, b164, rfl, mt165, ml166, rfl⟩ := matchListWith_cons_inv ml160
          obtain rfl := matchPattern_wildcard_inv mt165
          obtain ⟨x_body, vs167, b168, b169, rfl, mt170, ml171, rfl⟩ := matchListWith_cons_inv ml166
          obtain rfl := matchPattern_bind_inv mt170
          obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml171
          have hne := tag_ne_zero_of_none nm117
          obtain ⟨vs172, a173, rfl⟩ := d77.tuple_inv
          obtain ⟨v174, vs177, m178, c179, c180, rfl, d181, a182, rfl⟩ := a173.cons_inv
          obtain ⟨rfl, rfl, rfl⟩ := d181.literal_inv
          obtain ⟨v175, vs183, m184, c185, c186, rfl, d187, a188, rfl⟩ := a182.cons_inv
          obtain ⟨vs189, m190, c191, cs192, a193, ev194, rfl⟩ := d187.call_inv
          rw [instanceName_plain_some] at ev194
          obtain ⟨v195, vs197, m198, c199, c200, rfl, d201, a202, rfl⟩ := a193.cons_inv
          obtain ⟨l203, rfl, rfl⟩ := d201.var_inv
          simp at l203
          subst l203
          obtain ⟨v196, vs204, m205, c206, c207, rfl, d208, a209, rfl⟩ := a202.cons_inv
          obtain ⟨l210, rfl, rfl⟩ := d208.var_inv
          simp at l210
          subst l210
          obtain ⟨rfl, rfl, rfl⟩ := a209.nil_inv
          obtain ⟨rfl, rfl, rfl⟩ := a188.nil_inv
          exact .inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ev15, ld51, ev100, ld94,
            ev83,
            hne, rfl, ev194, rfl, (by first | rfl | simp only [List.append_assoc, List.cons_append,
              List.nil_append, List.append_nil, instanceName_plain_none, instanceName_plain_some])⟩
        · have hne213 := matchPattern_tuple_none (by trivial) nm156
          exact (selectArm_nil_inv sel157).elim
    · have hne214 := matchPattern_construct_none (by trivial) nm54
      simp only [IxVM.Refinement.Obs.Names.n14861064886094815840] at hne214
      rcases selectArm_cons_inv sel55 with ⟨mt215, rfl⟩ | ⟨nm216, sel217⟩
      · obtain rfl := matchPattern_wildcard_inv mt215
        obtain ⟨vs218, a219, rfl⟩ := d48.tuple_inv
        obtain ⟨v220, vs223, m224, c225, c226, rfl, d227, a228, rfl⟩ := a219.cons_inv
        obtain ⟨rfl, rfl, rfl⟩ := d227.literal_inv
        obtain ⟨v221, vs229, m230, c231, c232, rfl, d233, a234, rfl⟩ := a228.cons_inv
        obtain ⟨l235, rfl, rfl⟩ := d233.var_inv
        simp at l235
        subst l235
        obtain ⟨rfl, rfl, rfl⟩ := a234.nil_inv
        exact .inl rfl
      · exact (matchPattern_wildcard_none nm216).elim
  · have hne238 := matchPattern_tuple_none (by trivial) nm25
    exact (selectArm_nil_inv sel26).elim

end IxVM.Refinement.Core.DefEqAux

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq DefEqList)
open DefEqAux

set_option linter.unusedVariables false

/-! ## Selecting by the loaded constant -/

/-- `KernelDefEq::is_defn_or_thm`: `1` at a `Defn` or `Thm` value, which represents a definition
or a theorem; `0` otherwise. -/
theorem is_defn_or_thm_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::is_defn_or_thm" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.is_defn_or_thm c args h r h' calls := by
  intro v hargs
  subst hargs
  rcases Obs.«KernelDefEq::is_defn_or_thm».obs ev with
    ⟨w17, w18, w19, w20, w21, hv15, he47, he48, hc49⟩ |
    ⟨w57, w58, w59, hne50, hv55, he75, he76, hc77⟩ |
    ⟨hne50, hne78, he82, he83, hc84⟩
  · subst hv15
    refine ⟨he48, fun _ ci hci => .inl ?_⟩
    obtain ⟨cv, V, hn, rfl, -, -⟩ := CIRep.defn_inv hci
    exact ⟨cv, V, hn, rfl⟩
  · subst hv55
    exact ⟨he76, fun _ ci hci => .inr (ciRep_thm_inv hci)⟩
  · exact ⟨he83, fun hne => absurd he82 hne⟩

/-- `KernelDefEq::delta_rank`: a `Defn` value's hint field, else `0`. -/
theorem delta_rank_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::delta_rank" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.delta_rank c args h r h' calls := by
  intro v hargs
  subst hargs
  rcases Obs.«KernelDefEq::delta_rank».obs ev with
    ⟨w17, w18, w19, w20, x_hint, hv15, he47, he48, hc49⟩ | ⟨hne50, he54, he55, hc56⟩
  · subst hv15 he47
    exact ⟨he48, .inl ⟨w17, w18, w19, w20, rfl⟩⟩
  · exact ⟨he55, .inr he54⟩

/-- `KernelDefEq::head_addr`: at a constant head, its address (the image is that constant
applied to the spine, `collect_spine`). -/
theorem head_addr_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::head_addr" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.head_addr c args h r h' calls := by
  intro e hargs good p tag hr htag d Γ E hE
  subst hargs
  rcases Obs.«KernelDefEq::head_addr».obs ev with
    ⟨m2, cs13, x_head, w30, x_addr, w60, ev15, ld52, he75, he89, hc90⟩ |
    ⟨m2, cs13, x_head, w30, v41, m101, ev15, ld52, hne91, he99, hm109, he118, hc119⟩
  · subst he75 he89 hc90
    obtain ⟨rfl, -⟩ := tuple2_inj hr
    obtain ⟨hd, sp, H, As, he1, hH, hAs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev15 e rfl (good.sub fun x hx => by simp [hx]) d Γ 0 E hE
    obtain ⟨rfl, rfl⟩ := tuple2_inj he1
    obtain ⟨a, us, rfl, ha, -⟩ := hH.const_of_load ld52
    exact ⟨a, us, As, ha, rfl⟩
  · subst he99
    obtain ⟨-, rfl⟩ := tuple2_inj hr
    exact absurd rfl htag

/-! ## One δ step -/

/-- `KernelDefEq::delta_unfold`: at a constant head, the stored definition's value
(`Red.delta`) or the stored theorem's (`Red.deltaThm`, with `EnvFacts.thmTyped`) at the head's
levels, applied to the spine. -/
theorem delta_unfold_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::delta_unfold" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.delta_unfold c args h r h' calls := by
  intro e hargs good d Γ E hE x hr
  subst hargs
  rcases delta_unfold_obs ev with h0 |
    ⟨m2, cs13, x_head, x_spine, x_addr, x_lvls, m70, cs81, v84, m87, p92, cs98, w161, x_body,
      v175, m184, cs192, ev15, ld51, ev100, ld94, ev83, hw, hr', ev194, hh', hcalls⟩
  · exact (tag_contra h0 hr).elim
  subst hr' hh' hcalls
  obtain ⟨-, rfl⟩ := tuple2_inj hr
  have e1 := ObsFn.heap_extends ev100
  have e2 := ObsFn.heap_extends ev83
  obtain ⟨hd, sp, H, As, he1, hH, hAs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls) ev15
    e rfl (good.sub fun x hx => by simp [hx]) d Γ 0 E hE
  obtain ⟨rfl, rfl⟩ := tuple2_inj he1
  obtain ⟨a, us, rfl, ha, hus⟩ := hH.const_of_load ld51
  obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev100 x_addr a rfl
    (good.sub fun x hx => by simp [hx]) ha
  rw [ld94] at hld
  injection hld with hv
  subst hv
  obtain ⟨t, xb, htag⟩ := red_unfold_tag ev83
  obtain ⟨rfl, rfl⟩ := tuple2_inj htag
  have ht : t ≠ 0 := fun h0 => hw (by rw [h0])
  have hres : ∀ V', c.tmc m70 V' x_body →
      c.tmk d Γ 0 h' (Ix.Kernel.Expr.mkAppN V' As) v175 := fun V' hV' =>
    ih.get (.whnf .apply_spine) (by lt_calls) ev194 x_body x_spine rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 V' As (hV' d Γ) (tml_mono (e1.trans e2) hAs)
  rcases ih.get (.whnf .red_unfold) (by lt_calls) ev83 _ x_lvls rfl
      (good.sub fun x hx => by simp [hx]) ci us hci (LvListRep.mono e1 hus) t x_body rfl ht with
    ⟨-, cv, V, hn, rfl, hlen, hbody⟩ | ⟨-, cv, V, rfl, hlen, hbody⟩
  · exact ⟨_, hres _ hbody, .delta (unfold_const_mkAppN As hfind hlen)⟩
  · obtain ⟨hf, hb, vt, s, u, hinf, hdef, hinfs, hred, hzero⟩ := hc.env.thmTyped _ cv V hfind
    exact ⟨_, hres _ hbody, red_mkAppN_fn As
      (Ix.Kernel.Rules.Red.deltaThm hfind hlen hf hb hinf hdef hinfs hred hzero)⟩

/-- `KernelDefEq::try_unfold_head`: at a definition or theorem, one δ step (`delta_unfold`),
head-normalized (`whnf_nd`). -/
theorem try_unfold_head_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_unfold_head" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_unfold_head c args h r h' calls := by
  intro rc e v types hargs good hrc d Γ htypes E hE x hr
  subst hargs
  rcases Obs.«KernelDefEq::try_unfold_head».obs ev with
    ⟨w17, w18, w19, w20, w21, m48, cs59, x_e2, v91, m100, cs108, hv15, ev61, he92, ev110, he135,
      hc136⟩ |
    ⟨w17, w18, w19, w20, w21, v47, m48, cs59, hv15, ev61, he144, he158, hc159⟩ |
    ⟨w167, w168, w169, m186, cs197, x_e2, v229, m238, cs246, hne160, hv165, ev199, he230, ev248,
      he273, hc274⟩ |
    ⟨w167, w168, w169, v185, m186, cs197, hne160, hv165, ev199, he282, he296, hc297⟩ |
    ⟨hne160, hne298, he306, he320, hc321⟩
  · subst he92 he135 hc136
    obtain ⟨-, rfl⟩ := tuple2_inj hr
    have e0 := ObsFn.heap_extends ev61
    obtain ⟨E2, hE2, hred⟩ := ih.get (.defEq .delta_unfold) (by lt_calls) ev61 e rfl
      (good.sub fun x hx => by simp [hx]) d Γ E hE x_e2 rfl
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev110 rc x_e2 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) E2 hE2
    exact ⟨E', hE', .trans hred hred'⟩
  · exact (tag_contra he144 hr).elim
  · subst he230 he273 hc274
    obtain ⟨-, rfl⟩ := tuple2_inj hr
    have e0 := ObsFn.heap_extends ev199
    obtain ⟨E2, hE2, hred⟩ := ih.get (.defEq .delta_unfold) (by lt_calls) ev199 e rfl
      (good.sub fun x hx => by simp [hx]) d Γ E hE x_e2 rfl
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev248 rc x_e2 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) E2 hE2
    exact ⟨E', hE', .trans hred hred'⟩
  · exact (tag_contra he282 hr).elim
  · exact (tag_contra he306 hr).elim

/-- `KernelDefEq::try_unfold_proj_app`: at a projection-headed spine, `whnf_nd`'s reduct, or,
where that is still projection-headed, the spine with the projection's scrutinee unfolded one
δ step (`Red.projArg` under `Red.appFn`). -/
theorem try_unfold_proj_app_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_unfold_proj_app" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_unfold_proj_app c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE x hr
  subst hargs
  rcases Obs.«KernelDefEq::try_unfold_proj_app».obs ev with
    ⟨m2, cs13, x_head, x_spine, x_struct_addr, x_fidx, x_inner, v74, m75, cs85, m113, cs124,
      x_reduced_head, w141, w171, w172, w173, m190, cs201, x_inner2, m231, v272, m281, cs289,
      ev15, ld51, ev87, ev126, ld163, ev203, hm241, he273, ev291, he308, hc309⟩ |
    ⟨m2, cs13, x_head, x_spine, x_struct_addr, x_fidx, x_inner, v74, m75, cs85, m113, cs124,
      x_reduced_head, w141, w171, w172, w173, v189, m190, cs201, ev15, ld51, ev87, ev126, ld163,
      ev203, he317, he331, hc332⟩ |
    ⟨m2, cs13, x_head, x_spine, x_struct_addr, x_fidx, x_inner, v74, m75, cs85, m113, cs124,
      x_reduced_head, w141, v152, ev15, ld51, ev87, ev126, ld163, hne333, he341, he355, hc356⟩ |
    ⟨m2, cs13, x_head, x_spine, v40, ev15, ld51, hne358, he366, he380, hc381⟩
  · subst he273 he308 hc309
    obtain ⟨-, rfl⟩ := tuple2_inj hr
    have e1 := ObsFn.heap_extends ev87
    have e2 := ObsFn.heap_extends ev126
    have e3 := ObsFn.heap_extends ev203
    obtain ⟨hd, sp, H, As, he1, hH, hAs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev15 e rfl (good.sub fun x hx => by simp [hx]) d Γ 0 E hE
    obtain ⟨rfl, rfl⟩ := tuple2_inj he1
    obtain ⟨a, i, Es, rfl, rfl, ha, hEs⟩ := hH.proj_of_load ld51
    obtain ⟨Es2, hEs2, hred⟩ := ih.get (.defEq .delta_unfold) (by lt_calls) ev203 x_inner rfl
      (good.sub fun x hx => by simp [hx]) d Γ Es (Tm.mono (e1.trans e2) hEs) x_inner2 rfl
    have hm : m231 = m190 ++ [.construct kexprEnum "Proj" [x_struct_addr, .field i, x_inner2]] :=
      hm241
    subst hm
    have e4 : Heap.Extends m190
        (m190 ++ [.construct kexprEnum "Proj" [x_struct_addr, .field i, x_inner2]]) :=
      Heap.Extends.snoc _ _
    have ext := e1.trans (e2.trans (e3.trans e4))
    have hP : Tm c.κ d Γ
        (m190 ++ [.construct kexprEnum "Proj" [x_struct_addr, .field i, x_inner2]]) 0
        (.proj (c.κ (ixAddr a)) (ZMod.val i) Es2) (.ptr (.enum kexprEnum) m190.length) :=
      .proj (by simp) (Bytes.repAddressRef_heapMono₂ addrTy ext ha) (Tm.mono e4 hEs2)
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev291 _ x_spine rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As hP (tml_mono ext hAs),
      red_mkAppN_fn As (.projArg hred)⟩
  · exact (tag_contra he317 hr).elim
  · subst he341 he355 hc356
    obtain ⟨-, rfl⟩ := tuple2_inj hr
    have e0 := ObsFn.heap_extends ev15
    have e2 := ObsFn.heap_extends ev126
    obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev87 rc e types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) E
      (Tm.mono e0 hE)
    exact ⟨E', Tm.mono e2 hE', hred⟩
  · exact (tag_contra he366 hr).elim

/-! ## The loop and its steps -/

/-- `KernelDefEq::unfold_a_and_loop`: one δ step on `a`, head-normalized, then the loop. -/
theorem unfold_a_and_loop_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::unfold_a_and_loop" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.unfold_a_and_loop c args h r h' calls := by
  intro rc a b fuel types hargs good hrc d Γ htypes A B hA hB
  subst hargs
  rcases Obs.«KernelDefEq::unfold_a_and_loop».obs ev with
    ⟨m2, cs13, x_a2, v42, m43, cs53, cs83, v89, ev15, ev55, op125, ev85, hc134⟩ |
    ⟨v1, m2, cs13, ev15, he143, he164, hc165⟩
  · subst hc134
    have e0 := ObsFn.heap_extends ev15
    have e1 := ObsFn.heap_extends ev55
    obtain ⟨A2, hA2, hr1⟩ := ih.get (.defEq .delta_unfold) (by lt_calls) ev15 a rfl
      (good.sub fun x hx => by simp [hx]) d Γ A hA x_a2 rfl
    obtain ⟨Aw, hAw, hr2⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev55 rc x_a2 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) A2 hA2
    have ext := e0.trans e1
    exact loopResult_red (ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev85 rc v42 b v89 types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes)
      Aw B hAw (Tm.mono ext hB)) (.trans hr1 hr2) .refl
  · subst he143 he164
    exact loopResult_zero (ObsFn.heap_extends ev15) hA hB

/-- `KernelDefEq::unfold_b_and_loop`: one δ step on `b`, head-normalized, then the loop. -/
theorem unfold_b_and_loop_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::unfold_b_and_loop" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.unfold_b_and_loop c args h r h' calls := by
  intro rc a b fuel types hargs good hrc d Γ htypes A B hA hB
  subst hargs
  rcases Obs.«KernelDefEq::unfold_b_and_loop».obs ev with
    ⟨m2, cs13, x_b2, v42, m43, cs53, cs83, v89, ev15, ev55, op125, ev85, hc134⟩ |
    ⟨v1, m2, cs13, ev15, he143, he164, hc165⟩
  · subst hc134
    have e0 := ObsFn.heap_extends ev15
    have e1 := ObsFn.heap_extends ev55
    obtain ⟨B2, hB2, hr1⟩ := ih.get (.defEq .delta_unfold) (by lt_calls) ev15 b rfl
      (good.sub fun x hx => by simp [hx]) d Γ B hB x_b2 rfl
    obtain ⟨Bw, hBw, hr2⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev55 rc x_b2 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) B2 hB2
    have ext := e0.trans e1
    exact loopResult_red (ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev85 rc a v42 v89 types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes)
      A Bw (Tm.mono ext hA) hBw) .refl (.trans hr1 hr2)
  · subst he143 he164
    exact loopResult_zero (ObsFn.heap_extends ev15) hA hB

/-- `KernelDefEq::unfold_both_and_loop`: one δ step on each side, head-normalized, then the
loop. -/
theorem unfold_both_and_loop_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::unfold_both_and_loop" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.unfold_both_and_loop c args h r h' calls := by
  intro rc a b fuel types hargs good hrc d Γ htypes A B hA hB
  subst hargs
  rcases Obs.«KernelDefEq::unfold_both_and_loop».obs ev with
    ⟨m2, cs13, x_a2, m43, cs54, x_b2, v83, m84, cs94, v121, m122, cs132, cs162, v168, ev15, ev56,
      ev96, ev134, op204, ev164, hc213⟩ |
    ⟨m2, cs13, x_a2, v42, m43, cs54, ev15, ev56, he222, he243, hc244⟩ |
    ⟨v1, m2, cs13, ev15, he253, he274, hc275⟩
  · subst hc213
    have e0 := ObsFn.heap_extends ev15
    have e1 := ObsFn.heap_extends ev56
    have e2 := ObsFn.heap_extends ev96
    have e3 := ObsFn.heap_extends ev134
    obtain ⟨A2, hA2, hra1⟩ := ih.get (.defEq .delta_unfold) (by lt_calls) ev15 a rfl
      (good.sub fun x hx => by simp [hx]) d Γ A hA x_a2 rfl
    obtain ⟨B2, hB2, hrb1⟩ := ih.get (.defEq .delta_unfold) (by lt_calls) ev56 b rfl
      (good.sub fun x hx => by simp [hx]) d Γ B (Tm.mono e0 hB) x_b2 rfl
    have x1 := e0.trans e1
    obtain ⟨Aw, hAw, hra2⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev96 rc x_a2 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ (types_mono x1 htypes) A2
      (Tm.mono e1 hA2)
    have x2 := x1.trans e2
    obtain ⟨Bw, hBw, hrb2⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev134 rc x_b2 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) d Γ (types_mono x2 htypes) B2
      (Tm.mono e2 hB2)
    have x3 := x2.trans e3
    exact loopResult_red (ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev164 rc v83 v121 v168
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x3 hrc) d Γ
      (types_mono x3 htypes) Aw Bw (Tm.mono e3 hAw) hBw) (.trans hra1 hra2) (.trans hrb1 hrb2)
  · subst he222 he243
    exact loopResult_zero ((ObsFn.heap_extends ev15).trans (ObsFn.heap_extends ev56)) hA hB
  · subst he253 he274
    exact loopResult_zero (ObsFn.heap_extends ev15) hA hB

/-- `KernelDefEq::lazy_delta_step_const_const`: both heads constants; unfold the side(s) whose
loaded constant is a definition or a theorem, by rank. -/
theorem lazy_delta_step_const_const_step (c : Ctx) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::lazy_delta_step_const_const" args h r h' calls)
    (ih : IH c calls) : Specs.DefEq.lazy_delta_step_const_const c args h r h' calls := by
  intro rc aa ba a b fuel types hargs good hrc d Γ htypes A B hA hB
  subst hargs
  rcases Obs.«KernelDefEq::lazy_delta_step_const_const».obs ev with
    ⟨v1, m2, p9, cs15, v26, m27, p34, cs40, m52, cs62, m74, cs84, ev17, ld11, ev42, ld36, ev64,
      ev86, he128, he149, hc150⟩ |
    ⟨v1, m2, p9, cs15, v26, m27, p34, cs40, m52, cs62, v73, m74, cs84, cs158, ev17, ld11, ev42,
      ld36, ev64, ev86, hne151, ev160, hc201⟩ |
    ⟨v1, m2, p9, cs15, v26, m27, p34, cs40, v51, m52, cs62, m74, cs84, cs223, ev17, ld11, ev42,
      ld36, ev64, ev86, hne202, ev225, hc266⟩ |
    ⟨v1, m2, p9, cs15, v26, m27, p34, cs40, v51, m52, cs62, v73, m74, cs84, v271, m272, cs282,
      v293, m294, cs304, m316, cs327, cs353, ev17, ld11, ev42, ld36, ev64, ev86, hne202, hne267,
      ev284, ev306, ev329, ev355, hc396⟩ |
    ⟨v1, m2, p9, cs15, v26, m27, p34, cs40, v51, m52, cs62, v73, m74, cs84, v271, m272, cs282,
      v293, m294, cs304, v315, m316, cs327, m402, cs413, cs439, ev17, ld11, ev42, ld36, ev64,
      ev86, hne202, hne267, ev284, ev306, ev329, hne397, ev415, ev441, hc482⟩ |
    ⟨v1, m2, p9, cs15, v26, m27, p34, cs40, v51, m52, cs62, v73, m74, cs84, v271, m272, cs282,
      v293, m294, cs304, v315, m316, cs327, v401, m402, cs413, cs490, ev17, ld11, ev42, ld36,
      ev64, ev86, hne202, hne267, ev284, ev306, ev329, hne397, ev415, hne483, ev492, hc533⟩
  · subst he128 he149
    exact loopResult_zero ((ObsFn.heap_extends ev17).trans ((ObsFn.heap_extends ev42).trans
      ((ObsFn.heap_extends ev64).trans (ObsFn.heap_extends ev86)))) hA hB
  · subst hc201
    have x0 : Heap.Extends h m74 := (ObsFn.heap_extends ev17).trans
      ((ObsFn.heap_extends ev42).trans ((ObsFn.heap_extends ev64).trans
        (ObsFn.heap_extends ev86)))
    exact ih.get (.defEq .unfold_b_and_loop) (by lt_calls) ev160 rc a b fuel types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ (types_mono x0 htypes) A B
      (Tm.mono x0 hA) (Tm.mono x0 hB)
  · subst hc266
    have x0 : Heap.Extends h m74 := (ObsFn.heap_extends ev17).trans
      ((ObsFn.heap_extends ev42).trans ((ObsFn.heap_extends ev64).trans
        (ObsFn.heap_extends ev86)))
    exact ih.get (.defEq .unfold_a_and_loop) (by lt_calls) ev225 rc a b fuel types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ (types_mono x0 htypes) A B
      (Tm.mono x0 hA) (Tm.mono x0 hB)
  · subst hc396
    have x0 : Heap.Extends h m316 := (ObsFn.heap_extends ev17).trans
      ((ObsFn.heap_extends ev42).trans ((ObsFn.heap_extends ev64).trans
        ((ObsFn.heap_extends ev86).trans ((ObsFn.heap_extends ev284).trans
          ((ObsFn.heap_extends ev306).trans (ObsFn.heap_extends ev329))))))
    exact ih.get (.defEq .unfold_a_and_loop) (by lt_calls) ev355 rc a b fuel types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ (types_mono x0 htypes) A B
      (Tm.mono x0 hA) (Tm.mono x0 hB)
  · subst hc482
    have x0 : Heap.Extends h m402 := (ObsFn.heap_extends ev17).trans
      ((ObsFn.heap_extends ev42).trans ((ObsFn.heap_extends ev64).trans
        ((ObsFn.heap_extends ev86).trans ((ObsFn.heap_extends ev284).trans
          ((ObsFn.heap_extends ev306).trans ((ObsFn.heap_extends ev329).trans
            (ObsFn.heap_extends ev415)))))))
    exact ih.get (.defEq .unfold_b_and_loop) (by lt_calls) ev441 rc a b fuel types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ (types_mono x0 htypes) A B
      (Tm.mono x0 hA) (Tm.mono x0 hB)
  · subst hc533
    have x0 : Heap.Extends h m402 := (ObsFn.heap_extends ev17).trans
      ((ObsFn.heap_extends ev42).trans ((ObsFn.heap_extends ev64).trans
        ((ObsFn.heap_extends ev86).trans ((ObsFn.heap_extends ev284).trans
          ((ObsFn.heap_extends ev306).trans ((ObsFn.heap_extends ev329).trans
            (ObsFn.heap_extends ev415)))))))
    exact ih.get (.defEq .unfold_both_and_loop) (by lt_calls) ev492 rc a b fuel types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ (types_mono x0 htypes) A B
      (Tm.mono x0 hA) (Tm.mono x0 hB)

/-- `KernelDefEq::lazy_delta_a_const_b_proj`: unfold the projection-headed `b`, else the
constant head of `a`, then the loop. -/
theorem lazy_delta_a_const_b_proj_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::lazy_delta_a_const_b_proj" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.lazy_delta_a_const_b_proj c args h r h' calls := by
  intro rc aa a b fuel types hargs good hrc d Γ htypes A B hA hB
  subst hargs
  rcases Obs.«KernelDefEq::lazy_delta_a_const_b_proj».obs ev with
    ⟨m2, cs13, x_b2, cs61, v67, ev15, op103, ev63, hc112⟩ |
    ⟨v1, m2, cs13, v116, m117, p124, cs130, m142, cs153, ev15, ev132, ld126, ev155, he173, he194,
      hc195⟩ |
    ⟨v1, m2, cs13, v116, m117, p124, cs130, v141, m142, cs153, m201, cs211, x_aw, cs277, v283,
      ev15, ev132, ld126, ev155, hne196, ev213, op319, ev279, hc328⟩ |
    ⟨v1, m2, cs13, v116, m117, p124, cs130, v141, m142, cs153, v200, m201, cs211, ev15, ev132,
      ld126, ev155, hne196, ev213, he337, he358, hc359⟩
  · subst hc112
    have e0 := ObsFn.heap_extends ev15
    obtain ⟨B2, hB2, hrb⟩ := ih.get (.defEq .try_unfold_proj_app) (by lt_calls) ev15 rc b types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes B hB x_b2 rfl
    exact loopResult_red (ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev63 rc a x_b2 v67 types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes)
      A B2 (Tm.mono e0 hA) hB2) .refl hrb
  · subst he173 he194
    exact loopResult_zero ((ObsFn.heap_extends ev15).trans ((ObsFn.heap_extends ev132).trans
      (ObsFn.heap_extends ev155))) hA hB
  · subst hc328
    have x0 : Heap.Extends h m142 := (ObsFn.heap_extends ev15).trans
      ((ObsFn.heap_extends ev132).trans (ObsFn.heap_extends ev155))
    obtain ⟨Aw, hAw, hra⟩ := ih.get (.defEq .try_unfold_head) (by lt_calls) ev213 rc a v116
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ
      (types_mono x0 htypes) A (Tm.mono x0 hA) x_aw rfl
    have x1 := x0.trans (ObsFn.heap_extends ev213)
    exact loopResult_red (ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev279 rc x_aw b v283
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ
      (types_mono x1 htypes) Aw B hAw (Tm.mono x1 hB)) hra .refl
  · subst he337 he358
    exact loopResult_zero ((ObsFn.heap_extends ev15).trans ((ObsFn.heap_extends ev132).trans
      ((ObsFn.heap_extends ev155).trans (ObsFn.heap_extends ev213)))) hA hB

/-- `KernelDefEq::lazy_delta_b_const_a_proj`: the mirror image. -/
theorem lazy_delta_b_const_a_proj_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::lazy_delta_b_const_a_proj" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.lazy_delta_b_const_a_proj c args h r h' calls := by
  intro rc ba a b fuel types hargs good hrc d Γ htypes A B hA hB
  subst hargs
  rcases Obs.«KernelDefEq::lazy_delta_b_const_a_proj».obs ev with
    ⟨m2, cs13, x_a2, cs61, v67, ev15, op103, ev63, hc112⟩ |
    ⟨v1, m2, cs13, v116, m117, p124, cs130, m142, cs153, ev15, ev132, ld126, ev155, he173, he194,
      hc195⟩ |
    ⟨v1, m2, cs13, v116, m117, p124, cs130, v141, m142, cs153, m201, cs211, x_bw, cs277, v283,
      ev15, ev132, ld126, ev155, hne196, ev213, op319, ev279, hc328⟩ |
    ⟨v1, m2, cs13, v116, m117, p124, cs130, v141, m142, cs153, v200, m201, cs211, ev15, ev132,
      ld126, ev155, hne196, ev213, he337, he358, hc359⟩
  · subst hc112
    have e0 := ObsFn.heap_extends ev15
    obtain ⟨A2, hA2, hra⟩ := ih.get (.defEq .try_unfold_proj_app) (by lt_calls) ev15 rc a types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A hA x_a2 rfl
    exact loopResult_red (ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev63 rc x_a2 b v67 types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes)
      A2 B hA2 (Tm.mono e0 hB)) hra .refl
  · subst he173 he194
    exact loopResult_zero ((ObsFn.heap_extends ev15).trans ((ObsFn.heap_extends ev132).trans
      (ObsFn.heap_extends ev155))) hA hB
  · subst hc328
    have x0 : Heap.Extends h m142 := (ObsFn.heap_extends ev15).trans
      ((ObsFn.heap_extends ev132).trans (ObsFn.heap_extends ev155))
    obtain ⟨Bw, hBw, hrb⟩ := ih.get (.defEq .try_unfold_head) (by lt_calls) ev213 rc b v116
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ
      (types_mono x0 htypes) B (Tm.mono x0 hB) x_bw rfl
    have x1 := x0.trans (ObsFn.heap_extends ev213)
    exact loopResult_red (ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev279 rc a x_bw v283
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ
      (types_mono x1 htypes) A Bw (Tm.mono x1 hA) hBw) .refl hrb
  · subst he337 he358
    exact loopResult_zero ((ObsFn.heap_extends ev15).trans ((ObsFn.heap_extends ev132).trans
      ((ObsFn.heap_extends ev155).trans (ObsFn.heap_extends ev213)))) hA hB

/-- `KernelDefEq::lazy_delta_both_proj`: unfold the projection-headed side(s), then the loop. -/
theorem lazy_delta_both_proj_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::lazy_delta_both_proj" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.lazy_delta_both_proj c args h r h' calls := by
  intro rc a b fuel types hargs good hrc d Γ htypes A B hA hB
  subst hargs
  rcases Obs.«KernelDefEq::lazy_delta_both_proj».obs ev with
    ⟨m2, cs12, m40, cs50, x_a2, x_b2, cs136, v142, ev14, ev52, op178, ev138, hc187⟩ |
    ⟨m2, cs12, v39, m40, cs50, x_a2, cs194, v200, ev14, ev52, op236, ev196, hc245⟩ |
    ⟨v1, m2, cs12, m40, cs50, x_b2, cs280, v286, ev14, ev52, op322, ev282, hc331⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, ev14, ev52, he340, he361, hc362⟩
  · subst hc187
    have e0 := ObsFn.heap_extends ev14
    have e1 := ObsFn.heap_extends ev52
    obtain ⟨A2, hA2, hra⟩ := ih.get (.defEq .try_unfold_proj_app) (by lt_calls) ev14 rc a types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A hA x_a2 rfl
    obtain ⟨B2, hB2, hrb⟩ := ih.get (.defEq .try_unfold_proj_app) (by lt_calls) ev52 rc b types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) B
      (Tm.mono e0 hB) x_b2 rfl
    have x1 := e0.trans e1
    exact loopResult_red (ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev138 rc x_a2 x_b2 v142
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ
      (types_mono x1 htypes) A2 B2 (Tm.mono e1 hA2) hB2) hra hrb
  · subst hc245
    have e0 := ObsFn.heap_extends ev14
    obtain ⟨A2, hA2, hra⟩ := ih.get (.defEq .try_unfold_proj_app) (by lt_calls) ev14 rc a types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A hA x_a2 rfl
    have e1 := ObsFn.heap_extends ev52
    have x1 := e0.trans e1
    exact loopResult_red (ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev196 rc x_a2 b v200
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ
      (types_mono x1 htypes) A2 B (Tm.mono e1 hA2) (Tm.mono x1 hB)) hra .refl
  · subst hc331
    have e0 := ObsFn.heap_extends ev14
    have e1 := ObsFn.heap_extends ev52
    obtain ⟨B2, hB2, hrb⟩ := ih.get (.defEq .try_unfold_proj_app) (by lt_calls) ev52 rc b types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) B
      (Tm.mono e0 hB) x_b2 rfl
    have x1 := e0.trans e1
    exact loopResult_red (ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev282 rc a x_b2 v286
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ
      (types_mono x1 htypes) A B2 (Tm.mono x1 hA) hB2) .refl hrb
  · subst he340 he361
    exact loopResult_zero ((ObsFn.heap_extends ev14).trans (ObsFn.heap_extends ev52)) hA hB

/-- `KernelDefEq::lazy_delta_loop`: out of fuel, the inputs; a decided `Nat` comparison
(`try_def_eq_nat`) on the inputs; otherwise one δ step chosen by the heads. -/
theorem lazy_delta_loop_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::lazy_delta_loop" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.lazy_delta_loop c args h r h' calls := by
  intro rc a b fuel types hargs good hrc d Γ htypes A B hA hB
  subst hargs
  rcases Obs.«KernelDefEq::lazy_delta_loop».obs ev with
    ⟨hv14, he20, he41, hc42⟩ |
    ⟨m48, cs59, x_eq, hne43, ev61, he117, he139, hc140⟩ |
    ⟨v47, m48, cs59, m145, cs155, x_a_addr, m180, cs190, x_b_addr, cs245, hne43, ev61, ev157,
      ev192, ev247, hc304⟩ |
    ⟨v47, m48, cs59, m145, cs155, x_a_addr, m180, cs190, x_b_addr, x_b_is_const, cs312, hne43,
      ev61, ev157, ev192, hne305, ev314, hc363⟩ |
    ⟨v47, m48, cs59, m145, cs155, x_a_addr, x_a_is_const, m180, cs190, x_b_addr, cs385, hne43,
      ev61, ev157, ev192, hne364, ev387, hc436⟩ |
    ⟨v47, m48, cs59, m145, cs155, x_a_addr, x_a_is_const, m180, cs190, x_b_addr, x_b_is_const,
      cs444, hne43, ev61, ev157, ev192, hne364, hne437, ev446, hc487⟩
  · subst he20 he41
    exact loopResult_same hA hB fun ht => absurd rfl ht
  · subst he117 he139 hc140
    have e0 := ObsFn.heap_extends ev61
    exact loopResult_same (Tm.mono e0 hA) (Tm.mono e0 hB) fun ht =>
      ih.get (.defEq .try_def_eq_nat) (by lt_calls) ev61 rc a b types rfl
        (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB x_eq rfl ht
  · subst hc304
    have x0 : Heap.Extends h m180 := (ObsFn.heap_extends ev61).trans
      ((ObsFn.heap_extends ev157).trans (ObsFn.heap_extends ev192))
    exact ih.get (.defEq .lazy_delta_step_const_const) (by lt_calls) ev247 rc x_a_addr x_b_addr
      a b fuel types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ
      (types_mono x0 htypes) A B (Tm.mono x0 hA) (Tm.mono x0 hB)
  · subst hc363
    have x0 : Heap.Extends h m180 := (ObsFn.heap_extends ev61).trans
      ((ObsFn.heap_extends ev157).trans (ObsFn.heap_extends ev192))
    exact ih.get (.defEq .lazy_delta_a_const_b_proj) (by lt_calls) ev314 rc x_a_addr a b fuel
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ
      (types_mono x0 htypes) A B (Tm.mono x0 hA) (Tm.mono x0 hB)
  · subst hc436
    have x0 : Heap.Extends h m180 := (ObsFn.heap_extends ev61).trans
      ((ObsFn.heap_extends ev157).trans (ObsFn.heap_extends ev192))
    exact ih.get (.defEq .lazy_delta_b_const_a_proj) (by lt_calls) ev387 rc x_b_addr a b fuel
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ
      (types_mono x0 htypes) A B (Tm.mono x0 hA) (Tm.mono x0 hB)
  · subst hc487
    have x0 : Heap.Extends h m180 := (ObsFn.heap_extends ev61).trans
      ((ObsFn.heap_extends ev157).trans (ObsFn.heap_extends ev192))
    exact ih.get (.defEq .lazy_delta_both_proj) (by lt_calls) ev446 rc a b fuel types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ (types_mono x0 htypes) A B
      (Tm.mono x0 hA) (Tm.mono x0 hB)

/-! ## Comparing after unfolding the heads -/

/-- `KernelDefEq::try_lazy_delta_app`: both heads constants; unfold each definition or theorem
head and compare what was unfolded with the other side (`DefEq.redBoth`, `redL`, `redR`). -/
theorem try_lazy_delta_app_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_lazy_delta_app" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_lazy_delta_app c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_lazy_delta_app».obs ev with
    ⟨m2, cs12, x_a_addr, m37, cs47, x_b_addr, x_b_is_const, ev14, ev49, he85, he86, hc87⟩ |
    ⟨m2, cs12, x_a_addr, x_a_is_const, m37, cs47, x_b_addr, ev14, ev49, hne88, he106, he107,
      hc108⟩ |
    ⟨m2, cs12, x_a_addr, x_a_is_const, m37, cs47, x_b_addr, x_b_is_const, v113, m114, p121,
      cs127, v138, m139, p146, cs152, m164, cs174, m210, cs220, x_aw, x_bw, cs314, ev14, ev49,
      hne88, hne109, ev129, ld123, ev154, ld148, ev176, ev222, ev316, hc349⟩ |
    ⟨m2, cs12, x_a_addr, x_a_is_const, m37, cs47, x_b_addr, x_b_is_const, v113, m114, p121,
      cs127, v138, m139, p146, cs152, m164, cs174, v209, m210, cs220, x_aw, cs356, ev14, ev49,
      hne88, hne109, ev129, ld123, ev154, ld148, ev176, ev222, ev358, hc391⟩ |
    ⟨m2, cs12, x_a_addr, x_a_is_const, m37, cs47, x_b_addr, x_b_is_const, v113, m114, p121,
      cs127, v138, m139, p146, cs152, m164, cs174, m210, cs220, w399, x_bw, cs442, ev14, ev49,
      hne88, hne109, ev129, ld123, ev154, ld148, ev176, ev222, ev444, hc477⟩ |
    ⟨m2, cs12, x_a_addr, x_a_is_const, m37, cs47, x_b_addr, x_b_is_const, v113, m114, p121,
      cs127, v138, m139, p146, cs152, m164, cs174, v209, m210, cs220, w399, ev14, ev49, hne88,
      hne109, ev129, ld123, ev154, ld148, ev176, ev222, he481, he482, hc483⟩
  · exact absurd he85 hr
  · exact absurd he106 hr
  · subst hc349
    have x0 : Heap.Extends h m139 := (ObsFn.heap_extends ev14).trans
      ((ObsFn.heap_extends ev49).trans ((ObsFn.heap_extends ev129).trans
        (ObsFn.heap_extends ev154)))
    have e4 := ObsFn.heap_extends ev176
    have e5 := ObsFn.heap_extends ev222
    obtain ⟨Aw, hAw, hra⟩ := ih.get (.defEq .try_unfold_head) (by lt_calls) ev176 rc a v113
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ
      (types_mono x0 htypes) A (Tm.mono x0 hA) x_aw rfl
    have x1 := x0.trans e4
    obtain ⟨Bw, hBw, hrb⟩ := ih.get (.defEq .try_unfold_head) (by lt_calls) ev222 rc b v138
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ
      (types_mono x1 htypes) B (Tm.mono x1 hB) x_bw rfl
    have x2 := x1.trans e5
    exact .redBoth hra hrb (ih.get (.defEq .k_is_def_eq) (by lt_calls) ev316 rc x_aw x_bw types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) d Γ (types_mono x2 htypes)
      Aw Bw (Tm.mono e5 hAw) hBw hr)
  · subst hc391
    have x0 : Heap.Extends h m139 := (ObsFn.heap_extends ev14).trans
      ((ObsFn.heap_extends ev49).trans ((ObsFn.heap_extends ev129).trans
        (ObsFn.heap_extends ev154)))
    have e4 := ObsFn.heap_extends ev176
    have e5 := ObsFn.heap_extends ev222
    obtain ⟨Aw, hAw, hra⟩ := ih.get (.defEq .try_unfold_head) (by lt_calls) ev176 rc a v113
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) d Γ
      (types_mono x0 htypes) A (Tm.mono x0 hA) x_aw rfl
    have x2 := (x0.trans e4).trans e5
    exact .redL hra (ih.get (.defEq .k_is_def_eq) (by lt_calls) ev358 rc x_aw b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) d Γ (types_mono x2 htypes) Aw B
      (Tm.mono e5 hAw) (Tm.mono x2 hB) hr)
  · subst hc477
    have x0 : Heap.Extends h m139 := (ObsFn.heap_extends ev14).trans
      ((ObsFn.heap_extends ev49).trans ((ObsFn.heap_extends ev129).trans
        (ObsFn.heap_extends ev154)))
    have e4 := ObsFn.heap_extends ev176
    have e5 := ObsFn.heap_extends ev222
    have x1 := x0.trans e4
    obtain ⟨Bw, hBw, hrb⟩ := ih.get (.defEq .try_unfold_head) (by lt_calls) ev222 rc b v138
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ
      (types_mono x1 htypes) B (Tm.mono x1 hB) x_bw rfl
    have x2 := x1.trans e5
    exact .redR hrb (ih.get (.defEq .k_is_def_eq) (by lt_calls) ev444 rc a x_bw types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) d Γ (types_mono x2 htypes) A Bw
      (Tm.mono x2 hA) hBw hr)
  · exact absurd he481 hr

end IxVM.Refinement.Core
