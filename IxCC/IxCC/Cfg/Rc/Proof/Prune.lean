import IxCC.Cfg.Rc.Prune
import IxCC.Cfg.Rc.Proof.Inline
import IxCC.Src.Proof.NatMap

/-! # Semantic preservation of dead reset/reuse wrapper pruning (`Cfg.Rc.Prune`)

Proves that replacing uncalled `reset`/`resetU`/`reuse`/`reuseU` wrappers with
1-block `.trap` stubs preserves exact execution for every program whose runtime
procedures (`fi ≥ l.sourceCount`) never call into the prunable reuse-wrapper
range `(l.isUniqueProc, l.init + 4 + 4 * l.ctors.length)`, and composes directly
with `Inline.inlineProgram_sim` using the pruned program's own `Lir.fuelFor`. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Prune

open IxCC.Cfg.Rc.Native

/-! ## Callee-set monotonicity and membership -/

private theorem natSet_contains_insert_self (s : Src.NatSet) (k : Nat) :
    (s.insert k).contains k = true := by
  simp [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert_self]

private theorem natSet_contains_insert_mono {s : Src.NatSet} {k g : Nat}
    (h : s.contains g = true) : (s.insert k).contains g = true := by
  by_cases hgk : g = k
  · subst hgk
    exact natSet_contains_insert_self s g
  · simp only [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert_ne _ _ hgk]
    exact h

private theorem stmtCallee_mono {s : Lir.Stmt} {acc : Src.NatSet} {g : Nat}
    (h : acc.contains g = true) : (stmtCallee s acc).contains g = true := by
  cases s with
  | call _ callee _ => exact natSet_contains_insert_mono h
  | _ => exact h

private theorem termCallee_mono {t : Lir.Term} {acc : Src.NatSet} {g : Nat}
    (h : acc.contains g = true) : (termCallee t acc).contains g = true := by
  cases t with
  | tail callee _ => exact natSet_contains_insert_mono h
  | _ => exact h

private theorem foldl_stmtCallee_mono :
    ∀ (ss : List Lir.Stmt) (acc : Src.NatSet) {g : Nat},
      acc.contains g = true → (ss.foldl (fun m s => stmtCallee s m) acc).contains g = true
  | [], _, _, h => h
  | s :: ss, acc, _, h => foldl_stmtCallee_mono ss (stmtCallee s acc) (stmtCallee_mono h)

private theorem blockCallees_mono {b : Lir.Block} {acc : Src.NatSet} {g : Nat}
    (h : acc.contains g = true) : (blockCallees b acc).contains g = true :=
  termCallee_mono (foldl_stmtCallee_mono b.body.toList acc h)

private theorem foldl_blockCallees_mono :
    ∀ (bs : List Lir.Block) (acc : Src.NatSet) {g : Nat},
      acc.contains g = true → (bs.foldl (fun m b => blockCallees b m) acc).contains g = true
  | [], _, _, h => h
  | b :: bs, acc, _, h => foldl_blockCallees_mono bs (blockCallees b acc) (blockCallees_mono h)

private theorem funcCallees_mono {F : Lir.Func} {acc : Src.NatSet} {g : Nat}
    (h : acc.contains g = true) : (funcCallees F acc).contains g = true :=
  foldl_blockCallees_mono F.blocks.toList acc h

private theorem foldl_calledBySources_mono (p : Lir.Program) :
    ∀ (fs : List Nat) (acc : Src.NatSet) {g : Nat},
      acc.contains g = true →
      (fs.foldl (fun m fi => match p.funcs[fi]? with | some F => funcCallees F m | none => m) acc).contains g = true
  | [], _, _, h => h
  | fi :: fs, acc, _, h => by
    simp only [List.foldl_cons]
    cases p.funcs[fi]? with
    | none => exact foldl_calledBySources_mono p fs acc h
    | some F => exact foldl_calledBySources_mono p fs (funcCallees F acc) (funcCallees_mono h)

private theorem foldl_stmtCallee_mem :
    ∀ (ss : List Lir.Stmt) (acc : Src.NatSet) {rs : List Lir.VReg} {g : Nat} {as : List Lir.Arg},
      Lir.Stmt.call rs g as ∈ ss →
      (ss.foldl (fun m s => stmtCallee s m) acc).contains g = true
  | [], _, _, _, _, h => nomatch h
  | s :: ss, acc, rs, g, as, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact foldl_stmtCallee_mono ss (stmtCallee (.call rs g as) acc)
        (natSet_contains_insert_self acc g)
    · exact foldl_stmtCallee_mem ss (stmtCallee s acc) hmem

private theorem blockCallees_mem_call {b : Lir.Block} {acc : Src.NatSet}
    {rs : List Lir.VReg} {g : Nat} {as : List Lir.Arg}
    (h : Lir.Stmt.call rs g as ∈ b.body.toList) :
    (blockCallees b acc).contains g = true :=
  termCallee_mono (foldl_stmtCallee_mem b.body.toList acc h)

private theorem blockCallees_mem_tail {b : Lir.Block} {acc : Src.NatSet}
    {g : Nat} {as : List Lir.Arg} (h : b.term = .tail g as) :
    (blockCallees b acc).contains g = true := by
  simp only [blockCallees, h, termCallee]
  exact natSet_contains_insert_self _ g

private theorem foldl_blockCallees_mem_call :
    ∀ (bs : List Lir.Block) (acc : Src.NatSet) {b : Lir.Block} {rs : List Lir.VReg} {g : Nat} {as : List Lir.Arg},
      b ∈ bs → Lir.Stmt.call rs g as ∈ b.body.toList →
      (bs.foldl (fun m blk => blockCallees blk m) acc).contains g = true
  | [], _, _, _, _, _, hb, _ => nomatch hb
  | blk :: bs, acc, b, rs, g, as, hb, hcall => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hb with rfl | hmem
    · exact foldl_blockCallees_mono bs (blockCallees b acc) (blockCallees_mem_call hcall)
    · exact foldl_blockCallees_mem_call bs (blockCallees blk acc) hmem hcall

private theorem foldl_blockCallees_mem_tail :
    ∀ (bs : List Lir.Block) (acc : Src.NatSet) {b : Lir.Block} {g : Nat} {as : List Lir.Arg},
      b ∈ bs → b.term = .tail g as →
      (bs.foldl (fun m blk => blockCallees blk m) acc).contains g = true
  | [], _, _, _, _, hb, _ => nomatch hb
  | blk :: bs, acc, b, g, as, hb, htail => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hb with rfl | hmem
    · exact foldl_blockCallees_mono bs (blockCallees b acc) (blockCallees_mem_tail htail)
    · exact foldl_blockCallees_mem_tail bs (blockCallees blk acc) hmem htail

private theorem foldl_calledBySources_mem (p : Lir.Program) :
    ∀ (fs : List Nat) (acc : Src.NatSet) {fi : Nat} {F : Lir.Func} {g : Nat},
      fi ∈ fs → p.funcs[fi]? = some F → (∀ m, (funcCallees F m).contains g = true) →
      (fs.foldl (fun m i => match p.funcs[i]? with | some fn => funcCallees fn m | none => m) acc).contains g = true
  | [], _, _, _, _, hfi, _, _ => nomatch hfi
  | idx :: fs, acc, fi, F, g, hfi, hget, hcal => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hfi with rfl | hmem
    · rw [hget]
      exact foldl_calledBySources_mono p fs (funcCallees F acc) (hcal acc)
    · cases p.funcs[idx]? with
      | none => exact foldl_calledBySources_mem p fs acc hmem hget hcal
      | some fn => exact foldl_calledBySources_mem p fs (funcCallees fn acc) hmem hget hcal

theorem calledBySources_mem_call {sourceCount fi : Nat} {p : Lir.Program} {F : Lir.Func}
    {b : Lir.Block} {rs : List Lir.VReg} {g : Nat} {as : List Lir.Arg}
    (hfi : fi < sourceCount) (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (hcall : Lir.Stmt.call rs g as ∈ b.body.toList) :
    (calledBySources sourceCount p).contains g = true :=
  foldl_calledBySources_mem p (List.range sourceCount) .leaf (List.mem_range.mpr hfi) hF
    fun m => foldl_blockCallees_mem_call F.blocks.toList m hb hcall

theorem calledBySources_mem_tail {sourceCount fi : Nat} {p : Lir.Program} {F : Lir.Func}
    {b : Lir.Block} {g : Nat} {as : List Lir.Arg}
    (hfi : fi < sourceCount) (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (htail : b.term = .tail g as) :
    (calledBySources sourceCount p).contains g = true :=
  foldl_calledBySources_mem p (List.range sourceCount) .leaf (List.mem_range.mpr hfi) hF
    fun m => foldl_blockCallees_mem_tail F.blocks.toList m hb htail

/-! ## Lookup and structural lemmas for `pruneUnusedReuse` -/

theorem pruneUnusedReuse_main (l : Layout) (p : Lir.Program) :
    (pruneUnusedReuse l p).main = p.main := rfl

theorem pruneUnusedReuse_size (l : Layout) (p : Lir.Program) :
    (pruneUnusedReuse l p).funcs.size = p.funcs.size := by
  simp [pruneUnusedReuse]

theorem pruneUnusedReuse_get_not_prunable {l : Layout} {p : Lir.Program} {f : Nat}
    (h : isPrunableReuse l f = false) :
    (pruneUnusedReuse l p).funcs[f]? = p.funcs[f]? := by
  simp only [pruneUnusedReuse, Array.getElem?_mapIdx]
  cases hget : p.funcs[f]? with
  | none => simp
  | some F => simp [h]

theorem pruneUnusedReuse_get_le {l : Layout} {p : Lir.Program} {f : Nat}
    (h : f ≤ l.isUniqueProc) :
    (pruneUnusedReuse l p).funcs[f]? = p.funcs[f]? :=
  pruneUnusedReuse_get_not_prunable (by simp [isPrunableReuse]; omega)

theorem pruneUnusedReuse_get_ge {l : Layout} {p : Lir.Program} {f : Nat}
    (h : l.init + 4 + 4 * l.ctors.length ≤ f) :
    (pruneUnusedReuse l p).funcs[f]? = p.funcs[f]? :=
  pruneUnusedReuse_get_not_prunable (by simp [isPrunableReuse]; omega)

theorem pruneUnusedReuse_get_used {l : Layout} {p : Lir.Program} {f : Nat}
    (h : (calledBySources l.sourceCount p).contains f = true) :
    (pruneUnusedReuse l p).funcs[f]? = p.funcs[f]? := by
  simp only [pruneUnusedReuse, Array.getElem?_mapIdx]
  cases hget : p.funcs[f]? with
  | none => simp
  | some F => simp [h]

private theorem foldl_calledBySources_push (p : Lir.Program) (fn : Lir.Func) :
    ∀ (fs : List Nat) (acc : Src.NatSet),
      (∀ fi ∈ fs, fi < p.funcs.size) →
      fs.foldl (fun m fi => match (p.funcs.push fn)[fi]? with | some F => funcCallees F m | none => m) acc =
        fs.foldl (fun m fi => match p.funcs[fi]? with | some F => funcCallees F m | none => m) acc
  | [], _, _ => rfl
  | fi :: fs, acc, hlt => by
    have hfi : fi < p.funcs.size := hlt fi (List.mem_cons_self ..)
    have hrest : ∀ i ∈ fs, i < p.funcs.size := fun i hi => hlt i (List.mem_cons_of_mem fi hi)
    simp only [List.foldl_cons, Array.getElem?_push_lt hfi, Array.getElem?_eq_getElem hfi]
    exact foldl_calledBySources_push p fn fs _ hrest

theorem calledBySources_push {sourceCount : Nat} {p : Lir.Program} {fn : Lir.Func}
    (h : sourceCount ≤ p.funcs.size) :
    calledBySources sourceCount { p with funcs := p.funcs.push fn } =
      calledBySources sourceCount p :=
  foldl_calledBySources_push p fn (List.range sourceCount) .leaf
    fun _ hfi => Nat.lt_of_lt_of_le (List.mem_range.mp hfi) h

theorem pruneUnusedReuse_push {l : Layout} {p : Lir.Program} {fn : Lir.Func}
    (hsrc : l.sourceCount ≤ p.funcs.size)
    (hsize : l.init + 4 + 4 * l.ctors.length ≤ p.funcs.size) :
    pruneUnusedReuse l { p with funcs := p.funcs.push fn } =
      { pruneUnusedReuse l p with funcs := (pruneUnusedReuse l p).funcs.push fn } := by
  have hnp : isPrunableReuse l p.funcs.size = false := by
    simp [isPrunableReuse]; omega
  simp only [pruneUnusedReuse, calledBySources_push hsrc, Array.mapIdx_push, hnp,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-! ## Runtime non-call invariant and exact step equivalence -/

def NoPrunableCallsInFunc (l : Layout) (F : Lir.Func) : Prop :=
  ∀ b ∈ F.blocks.toList,
    (∀ rs g as, Lir.Stmt.call rs g as ∈ b.body.toList → isPrunableReuse l g = false) ∧
    (∀ g as, b.term = .tail g as → isPrunableReuse l g = false)

def NoRuntimeReuseCalls (l : Layout) (p : Lir.Program) : Prop :=
  ∀ fi F, l.sourceCount ≤ fi → p.funcs[fi]? = some F → NoPrunableCallsInFunc l F

theorem NoRuntimeReuseCalls.inlineProgram {l : Layout} {raw : Lir.Program}
    (h : NoRuntimeReuseCalls l raw) : NoRuntimeReuseCalls l (Inline.inlineProgram l raw) := by
  intro fi F hge hget
  rw [Inline.inlineProgram_get_ge l raw hge] at hget
  exact h fi F hge hget

def stmtNotCall : Lir.Stmt → Bool
  | .call .. => false
  | _ => true

def termNotTail : Lir.Term → Bool
  | .tail .. => false
  | _ => true

def funcHasNoCalls (F : Lir.Func) : Bool :=
  F.blocks.toList.all fun b => b.body.toList.all stmtNotCall && termNotTail b.term

theorem noPrunableCalls_of_funcHasNoCalls {l : Layout} {F : Lir.Func}
    (h : funcHasNoCalls F = true) : NoPrunableCallsInFunc l F := by
  intro b hb
  have hblk := List.all_eq_true.mp h b hb
  simp only [Bool.and_eq_true] at hblk
  constructor
  · intro rs g as hcall
    have hs := List.all_eq_true.mp hblk.1 (.call rs g as) hcall
    simp [stmtNotCall] at hs
  · intro g as htail
    rw [htail] at hblk
    simp [termNotTail] at hblk

def GoodState (inl pruned : Lir.Program) (s : Lir.State) : Prop :=
  ∀ fr ∈ s.stack, pruned.funcs[fr.fn]? = inl.funcs[fr.fn]?

private theorem enter_eq_of_get_eq {p₁ p₂ : Lir.Program} {g : Lir.FunId} {vals : List Lir.Word}
    (h : p₁.funcs[g]? = p₂.funcs[g]?) :
    Lir.enter p₁ g vals = Lir.enter p₂ g vals := by
  simp only [Lir.enter, h]

private theorem enter_fn {p : Lir.Program} {g : Lir.FunId} {vals : List Lir.Word}
    {callee : Lir.Frame} (h : Lir.enter p g vals = some callee) :
    callee.fn = g := by
  unfold Lir.enter at h
  cases hf : p.funcs[g]? with
  | none => simp [hf] at h
  | some F =>
    simp only [hf, bind, Option.bind] at h
    cases hb : Lir.bindParams {} F.params vals with
    | none => simp [hb] at h
    | some ρ =>
      simp only [hb, Option.some.injEq] at h
      subst h
      rfl

private theorem takeEdge_good {inl pruned : Lir.Program} {f : Lir.Func}
    {s : Lir.State} {fr : Lir.Frame} {rest : List Lir.Frame} {ρ : Lir.Env} {e : Lir.Edge}
    (hgood : GoodState inl pruned { s with stack := fr :: rest })
    {s' : Lir.State} {chg : Bool}
    (ht : Lir.takeEdge f s fr rest ρ e = .next s' chg) :
    GoodState inl pruned s' := by
  unfold Lir.takeEdge at ht
  cases he : Lir.evalArgs ρ e.args with
  | none => simp [he] at ht
  | some vals =>
    cases hb : f.blocks[e.target]? with
    | none => simp [he, hb] at ht
    | some target =>
      cases hp : Lir.bindParams ρ target.params vals with
      | none => simp [he, hb, hp] at ht
      | some ρ' =>
        simp only [he, hb, hp, Lir.Step.next.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        intro fr' hmem
        rcases List.mem_cons.mp hmem with rfl | hrest
        · exact hgood fr (List.mem_cons_self ..)
        · exact hgood fr' (List.mem_cons_of_mem fr hrest)

theorem pruneUnusedReuse_step {l : Layout} {inl : Lir.Program}
    (hno : NoRuntimeReuseCalls l inl) {s : Lir.State}
    (hgood : GoodState inl (pruneUnusedReuse l inl) s) :
    Lir.step (pruneUnusedReuse l inl) s = Lir.step inl s ∧
    (∀ s' chg, Lir.step inl s = .next s' chg → GoodState inl (pruneUnusedReuse l inl) s') := by
  let pruned := pruneUnusedReuse l inl
  change Lir.step pruned s = Lir.step inl s ∧
    (∀ s' chg, Lir.step inl s = .next s' chg → GoodState inl pruned s')
  cases hstack : s.stack with
  | nil =>
    constructor
    · simp [Lir.step, hstack]
    · intro s' chg hstep; simp [Lir.step, hstack] at hstep
  | cons fr rest =>
    have hfr : pruned.funcs[fr.fn]? = inl.funcs[fr.fn]? :=
      hgood fr (by rw [hstack]; exact List.mem_cons_self ..)
    have hgood' : GoodState inl pruned { s with stack := fr :: rest } := by
      intro x hx; exact hgood x (by rw [hstack]; exact hx)
    cases hF : inl.funcs[fr.fn]? with
    | none =>
      constructor
      · simp [Lir.step, hstack, hfr, hF]
      · intro s' chg hstep; simp [Lir.step, hstack, hF] at hstep
    | some F =>
      cases hb : F.blocks[fr.label]? with
      | none =>
        constructor
        · simp [Lir.step, hstack, hfr, hF, hb]
        · intro s' chg hstep; simp [Lir.step, hstack, hF, hb] at hstep
      | some b =>
        have hbMem : b ∈ F.blocks.toList := by
          rw [← Array.getElem?_toList] at hb
          exact List.mem_of_getElem? hb
        by_cases hpos : fr.pos < b.body.size
        · have hsMem : b.body[fr.pos] ∈ b.body.toList := by
            exact Array.getElem_mem_toList hpos
          cases hstmt : b.body[fr.pos] with
          | call rs g as =>
            have hgEq : pruned.funcs[g]? = inl.funcs[g]? := by
              by_cases hsrc : fr.fn < l.sourceCount
              · exact pruneUnusedReuse_get_used
                  (calledBySources_mem_call hsrc hF hbMem (hstmt ▸ hsMem))
              · exact pruneUnusedReuse_get_not_prunable
                  ((hno fr.fn F (Nat.not_lt.mp hsrc) hF b hbMem).1 rs g as (hstmt ▸ hsMem))
            have hbind : (Lir.evalArgs fr.env as >>= Lir.enter pruned g) =
                (Lir.evalArgs fr.env as >>= Lir.enter inl g) := by
              cases Lir.evalArgs fr.env as with
              | none => rfl
              | some vals => exact enter_eq_of_get_eq hgEq
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hstmt, hbind]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hstmt] at hstep
              cases hev : Lir.evalArgs fr.env as with
              | none => simp [hev] at hstep
              | some vals =>
                simp only [hev, bind, Option.bind] at hstep
                cases hent : Lir.enter inl g vals with
                | none => simp [hent] at hstep
                | some callee =>
                  simp only [hent, Lir.Step.next.injEq] at hstep
                  obtain ⟨rfl, _⟩ := hstep
                  intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx1
                  · rw [enter_fn hent]; exact hgEq
                  · rcases List.mem_cons.mp hx1 with rfl | hx2
                    · exact hfr
                    · exact hgood' x (List.mem_cons_of_mem fr hx2)
          | assign x r =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hstmt]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hstmt] at hstep
              cases hex : (Lir.Stmt.assign x r).exec fr.env s.mem s.ctx with
              | none => simp [hex] at hstep
              | some pm =>
                simp only [hex, Lir.Step.next.injEq] at hstep
                obtain ⟨rfl, _⟩ := hstep
                intro y hy
                rcases List.mem_cons.mp hy with rfl | hrest
                · exact hfr
                · exact hgood' y (List.mem_cons_of_mem fr hrest)
          | limb r1 r2 op =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hstmt]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hstmt] at hstep
              cases hex : (Lir.Stmt.limb r1 r2 op).exec fr.env s.mem s.ctx with
              | none => simp [hex] at hstep
              | some pm =>
                simp only [hex, Lir.Step.next.injEq] at hstep
                obtain ⟨rfl, _⟩ := hstep
                intro y hy
                rcases List.mem_cons.mp hy with rfl | hrest
                · exact hfr
                · exact hgood' y (List.mem_cons_of_mem fr hrest)
          | store w m a =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hstmt]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hstmt] at hstep
              cases hex : (Lir.Stmt.store w m a).exec fr.env s.mem s.ctx with
              | none => simp [hex] at hstep
              | some pm =>
                simp only [hex, Lir.Step.next.injEq] at hstep
                obtain ⟨rfl, _⟩ := hstep
                intro y hy
                rcases List.mem_cons.mp hy with rfl | hrest
                · exact hfr
                · exact hgood' y (List.mem_cons_of_mem fr hrest)
        · cases hterm : b.term with
          | jump e =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hterm] at hstep
              exact takeEdge_good hgood' hstep
          | br c w a b' t e =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hterm] at hstep
              cases ha : a.eval fr.env with
              | none => simp [ha] at hstep
              | some va =>
                cases hb' : b'.eval fr.env with
                | none => simp [ha, hb'] at hstep
                | some vb =>
                  simp only [ha, hb'] at hstep
                  exact takeEdge_good hgood' hstep
          | brOvf o x a b' ok ovf =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hterm] at hstep
              cases ha : a.eval fr.env with
              | none => simp [ha] at hstep
              | some va =>
                cases hb' : b'.eval fr.env with
                | none => simp [ha, hb'] at hstep
                | some vb =>
                  simp only [ha, hb'] at hstep
                  exact takeEdge_good hgood' hstep
          | ret as =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hterm] at hstep
              cases hev : Lir.evalArgs fr.env as with
              | none => simp [hev] at hstep
              | some vals =>
                simp only [hev] at hstep
                cases rest with
                | nil => cases hstep
                | cons caller rest' =>
                  cases hbp : Lir.bindParams caller.env caller.dsts vals with
                  | none => simp [hbp] at hstep
                  | some ρ =>
                    simp only [hbp, Lir.Step.next.injEq] at hstep
                    obtain ⟨rfl, _⟩ := hstep
                    intro y hy
                    rcases List.mem_cons.mp hy with rfl | hrest
                    · exact hgood' caller (List.mem_cons_of_mem fr (List.mem_cons_self ..))
                    · exact hgood' y (List.mem_cons_of_mem fr (List.mem_cons_of_mem caller hrest))
          | tail g as =>
            have hgEq : pruned.funcs[g]? = inl.funcs[g]? := by
              by_cases hsrc : fr.fn < l.sourceCount
              · exact pruneUnusedReuse_get_used
                  (calledBySources_mem_tail hsrc hF hbMem hterm)
              · exact pruneUnusedReuse_get_not_prunable
                  ((hno fr.fn F (Nat.not_lt.mp hsrc) hF b hbMem).2 g as hterm)
            have hbind : (Lir.evalArgs fr.env as >>= Lir.enter pruned g) =
                (Lir.evalArgs fr.env as >>= Lir.enter inl g) := by
              cases Lir.evalArgs fr.env as with
              | none => rfl
              | some vals => exact enter_eq_of_get_eq hgEq
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm, hbind]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hterm] at hstep
              cases hev : Lir.evalArgs fr.env as with
              | none => simp [hev] at hstep
              | some vals =>
                simp only [hev, bind, Option.bind] at hstep
                cases hent : Lir.enter inl g vals with
                | none => simp [hent] at hstep
                | some callee =>
                  simp only [hent, Lir.Step.next.injEq] at hstep
                  obtain ⟨rfl, _⟩ := hstep
                  intro y hy
                  rcases List.mem_cons.mp hy with rfl | hrest
                  · rw [enter_fn hent]; exact hgEq
                  · exact hgood' y (List.mem_cons_of_mem fr hrest)
          | fail r =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep; simp [Lir.step, hstack, hF, hb, hpos, hterm] at hstep
          | trap =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep; simp [Lir.step, hstack, hF, hb, hpos, hterm] at hstep

theorem pruneUnusedReuse_runClocked {l : Layout} {inl : Lir.Program}
    (hno : NoRuntimeReuseCalls l inl) :
    ∀ fuel k s, GoodState inl (pruneUnusedReuse l inl) s →
      Sem.runClocked (Lir.semStep (pruneUnusedReuse l inl)) fuel k s =
        Sem.runClocked (Lir.semStep inl) fuel k s
  | 0, _, _, _ => rfl
  | fuel + 1, k, s, hgood => by
    obtain ⟨hstepEq, hnextGood⟩ := pruneUnusedReuse_step hno hgood
    have hsemEq : Lir.semStep (pruneUnusedReuse l inl) s = Lir.semStep inl s := by
      simp [Lir.semStep, hstepEq]
    unfold Sem.runClocked
    rw [hsemEq]
    cases hs : Lir.semStep inl s with
    | next s' chg =>
      have hgood' := hnextGood s' chg (Lir.semStep_next.mp hs)
      cases chg with
      | false => exact pruneUnusedReuse_runClocked hno fuel k s' hgood'
      | true =>
        cases k with
        | zero => rfl
        | succ k' => exact pruneUnusedReuse_runClocked hno fuel k' s' hgood'
    | done _ => rfl
    | fail _ => rfl
    | trap => rfl
    | stuck => rfl

theorem pruneUnusedReuse_reaches {l : Layout} {inl : Lir.Program}
    (hno : NoRuntimeReuseCalls l inl) {s : Lir.State} {k : Nat} {r : Lir.Outcome}
    (hreach : Sem.Reaches (Lir.semStep inl) s k r)
    (hgood : GoodState inl (pruneUnusedReuse l inl) s) :
    Sem.Reaches (Lir.semStep (pruneUnusedReuse l inl)) s k r := by
  induction hreach with
  | @final s0 _ _ hf =>
    obtain ⟨hstepEq, _⟩ := pruneUnusedReuse_step hno hgood
    have hsemEq : Lir.semStep (pruneUnusedReuse l inl) s0 = Lir.semStep inl s0 := by
      simp [Lir.semStep, hstepEq]
    exact .final (hsemEq.symm ▸ hf)
  | @free s0 _ _ _ hs _ ih =>
    obtain ⟨hstepEq, hnextGood⟩ := pruneUnusedReuse_step hno hgood
    have hsemEq : Lir.semStep (pruneUnusedReuse l inl) s0 = Lir.semStep inl s0 := by
      simp [Lir.semStep, hstepEq]
    exact .free (hsemEq.trans hs) (ih (hnextGood _ false (Lir.semStep_next.mp hs)))
  | @charge s0 _ _ _ hs _ ih =>
    obtain ⟨hstepEq, hnextGood⟩ := pruneUnusedReuse_step hno hgood
    have hsemEq : Lir.semStep (pruneUnusedReuse l inl) s0 = Lir.semStep inl s0 := by
      simp [Lir.semStep, hstepEq]
    exact .charge (hsemEq.trans hs) (ih (hnextGood _ true (Lir.semStep_next.mp hs)))
  | @timeout s0 _ hs =>
    obtain ⟨hstepEq, _⟩ := pruneUnusedReuse_step hno hgood
    have hsemEq : Lir.semStep (pruneUnusedReuse l inl) s0 = Lir.semStep inl s0 := by
      simp [Lir.semStep, hstepEq]
    exact .timeout (hsemEq.trans hs)

/-! ## Composed simulation theorem (`pruneUnusedReuse` ∘ `inlineProgram`) -/

theorem pruneUnusedReuse_inlineProgram_sim {l : Layout} {raw : Lir.Program}
    (hr : Inline.RuntimeFuncs l raw)
    (hno : NoRuntimeReuseCalls l raw)
    (hmain : isPrunableReuse l raw.main = false)
    (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word) :
    Sem.Sim Eq (fun k => k + 12 * Lir.fuelFor (pruneUnusedReuse l (Inline.inlineProgram l raw)) k)
      (fun k => Lir.eval raw k args mem ctx)
      (fun k => Lir.eval (pruneUnusedReuse l (Inline.inlineProgram l raw)) k args mem ctx) := by
  let inl := Inline.inlineProgram l raw
  let pruned := pruneUnusedReuse l inl
  have hnoInl : NoRuntimeReuseCalls l inl := hno.inlineProgram
  have hmainInl : inl.main = raw.main := rfl
  have hmainPruned : pruned.main = raw.main := rfl
  have hmainGet : pruned.funcs[raw.main]? = inl.funcs[raw.main]? :=
    pruneUnusedReuse_get_not_prunable hmain
  obtain ⟨heFwd, _, heNone⟩ := Inline.enter_rel l raw (g := raw.main) (vs := args)
  cases hent : Lir.enter raw raw.main args with
  | none =>
    have hentInl : Lir.enter inl raw.main args = none := heNone.mp hent
    have hentPruned : Lir.enter pruned pruned.main args = none := by
      rw [hmainPruned, enter_eq_of_get_eq hmainGet, hentInl]
    have he1 : ∀ k, Lir.eval raw k args mem ctx = .stuck := fun k => by
      simp [Lir.eval, Lir.State.initial, hent]
    have he2 : ∀ k, Lir.eval pruned k args mem ctx = .stuck := fun k => by
      simp [Lir.eval, Lir.State.initial, hentPruned]
    exact {
      forward := fun k _ => ⟨k, by rw [he1, he2]; exact .stuck⟩
      timeout := fun k hk => by rw [he1] at hk; cases hk }
  | some fr₁ =>
    obtain ⟨fr₂, hentInl, hfr, hdst₁⟩ := heFwd fr₁ hent
    have hentPruned : Lir.enter pruned pruned.main args = some fr₂ := by
      rw [hmainPruned, enter_eq_of_get_eq hmainGet, hentInl]
    let s₁ : Lir.State := { mem, ctx, stack := [fr₁] }
    let s₂ : Lir.State := { mem, ctx, stack := [fr₂] }
    have hinit₁ : Lir.State.initial raw args mem ctx = some s₁ := by
      simp [Lir.State.initial, hent, s₁]
    have hinitPruned : Lir.State.initial pruned args mem ctx = some s₂ := by
      simp [Lir.State.initial, hentPruned, s₂]
    have hruns₁ := Lir.runs_eval hinit₁
    have hrunsPruned := Lir.runs_eval hinitPruned
    have hrel : Inline.StateRel l raw s₁ s₂ :=
      ⟨rfl, rfl, .cons hfr .nil, fun _ _ h => by cases h; exact hdst₁⟩
    have hgood₂ : GoodState inl pruned s₂ := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hnil
      · rw [enter_fn hentInl]; exact hmainGet
      · cases hnil
    exact {
      forward := fun k hk => by
        by_cases hst : Lir.eval raw k args mem ctx = .stuck
        · exact ⟨0, hst ▸ .stuck⟩
        · have hrun : Sem.runClocked (Lir.semStep raw) (Lir.fuelFor raw k) k s₁ =
              Lir.eval raw k args mem ctx := by
            rw [Lir.eval_eq, hinit₁]
          obtain ⟨k', r₂, hreach₂, href⟩ :=
            Inline.forward_run hr (Lir.fuelFor raw k) k s₁ s₂ _ hrel hrun hk hst
          have hreachP := pruneUnusedReuse_reaches hnoInl hreach₂ hgood₂
          exact ⟨k', hrunsPruned.eq hreachP ▸ href⟩
      timeout := fun k hk => by
        by_cases hto : Lir.eval pruned k args mem ctx = .timeout
        · exact .inl hto
        · by_cases hres : ∃ fail, Lir.eval pruned k args mem ctx = .resource fail
          · exact .inr hres
          · have hres' : ∀ fail, Lir.eval pruned k args mem ctx ≠ .resource fail :=
              fun fail h => hres ⟨fail, h⟩
            have hrunP : Sem.runClocked (Lir.semStep pruned) (Lir.fuelFor pruned k) k s₂ =
                Lir.eval pruned k args mem ctx := by
              rw [Lir.eval_eq, hinitPruned]
            have hrunInl : Sem.runClocked (Lir.semStep inl) (Lir.fuelFor pruned k) k s₂ =
                Lir.eval pruned k args mem ctx :=
              (pruneUnusedReuse_runClocked hnoInl (Lir.fuelFor pruned k) k s₂ hgood₂).symm.trans hrunP
            obtain ⟨r₁, hr₁nt, hreach₁⟩ :=
              Inline.backward_run hr (Lir.fuelFor pruned k) k s₁ s₂ _ hrel hrunInl hto hres'
            have hto₁ : Sem.Reaches (Lir.semStep raw) s₁ (k + 12 * Lir.fuelFor pruned k) .timeout :=
              hk ▸ hruns₁ (k + 12 * Lir.fuelFor pruned k)
            exact absurd (hreach₁.det hto₁) hr₁nt }

theorem pruneUnusedReuse_inlineProgram_sim_clock {l : Layout} {raw : Lir.Program}
    (hr : Inline.RuntimeFuncs l raw)
    (hno : NoRuntimeReuseCalls l raw)
    (hmain : isPrunableReuse l raw.main = false)
    (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word)
    {f : Nat → Nat}
    (hf : ∀ k, k + 12 * Lir.fuelFor (pruneUnusedReuse l (Inline.inlineProgram l raw)) k ≤ f k) :
    Sem.Sim Eq f
      (fun k => Lir.eval raw k args mem ctx)
      (fun k => Lir.eval (pruneUnusedReuse l (Inline.inlineProgram l raw)) k args mem ctx) :=
  let hsim := pruneUnusedReuse_inlineProgram_sim hr hno hmain args mem ctx
  { forward := hsim.forward
    timeout := fun k hk => by
      apply hsim.timeout k
      by_cases h0 : Lir.eval raw
          (k + 12 * Lir.fuelFor (pruneUnusedReuse l (Inline.inlineProgram l raw)) k)
          args mem ctx = .timeout
      · exact h0
      · have heq := Lir.eval_mono raw args mem ctx (hf k) h0
        dsimp only at heq
        rw [hk] at heq
        exact absurd heq.symm h0 }

/-! ## Dead runtime wrapper & procedure pruning (`pruneDeadRuntime`) -/

private theorem calledByIndices_mono {p : Lir.Program} {fs : List Nat} {acc : Src.NatSet} {g : Nat}
    (h : acc.contains g = true) : (calledByIndices fs p acc).contains g = true :=
  foldl_calledBySources_mono p fs acc h

private theorem calledByIndices_mem_call {p : Lir.Program} {fs : List Nat} {acc : Src.NatSet}
    {fi : Nat} {F : Lir.Func} {b : Lir.Block} {rs : List Lir.VReg} {g : Nat} {as : List Lir.Arg}
    (hfi : fi ∈ fs) (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (hcall : Lir.Stmt.call rs g as ∈ b.body.toList) :
    (calledByIndices fs p acc).contains g = true :=
  foldl_calledBySources_mem p fs acc hfi hF
    fun m => foldl_blockCallees_mem_call F.blocks.toList m hb hcall

private theorem calledByIndices_mem_tail {p : Lir.Program} {fs : List Nat} {acc : Src.NatSet}
    {fi : Nat} {F : Lir.Func} {b : Lir.Block} {g : Nat} {as : List Lir.Arg}
    (hfi : fi ∈ fs) (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (htail : b.term = .tail g as) :
    (calledByIndices fs p acc).contains g = true :=
  foldl_calledBySources_mem p fs acc hfi hF
    fun m => foldl_blockCallees_mem_tail F.blocks.toList m hb htail

theorem calledRuntimeRoots_mono_base {l : Layout} {p : Lir.Program} {g : Nat}
    (h : (calledRuntimeRootsBase l p).contains g = true) :
    (calledRuntimeRoots l p).contains g = true :=
  calledByIndices_mono h

theorem calledRuntimeRootsBase_mem_source_call {l : Layout} {p : Lir.Program}
    {fi : Nat} {F : Lir.Func} {b : Lir.Block} {rs : List Lir.VReg} {g : Nat} {as : List Lir.Arg}
    (hfi : fi < l.sourceCount) (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (hcall : Lir.Stmt.call rs g as ∈ b.body.toList) :
    (calledRuntimeRootsBase l p).contains g = true :=
  calledByIndices_mono (calledByIndices_mem_call (List.mem_range.mpr hfi) hF hb hcall)

theorem calledRuntimeRootsBase_mem_source_tail {l : Layout} {p : Lir.Program}
    {fi : Nat} {F : Lir.Func} {b : Lir.Block} {g : Nat} {as : List Lir.Arg}
    (hfi : fi < l.sourceCount) (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (htail : b.term = .tail g as) :
    (calledRuntimeRootsBase l p).contains g = true :=
  calledByIndices_mono (calledByIndices_mem_tail (List.mem_range.mpr hfi) hF hb htail)

private theorem mem_reuseRange {l : Layout} {fi : Nat}
    (hlo : l.isUniqueProc < fi) (hhi : fi < l.init + 4 + 4 * l.ctors.length) :
    fi ∈ (List.range (4 * l.ctors.length)).map (fun j => l.init + 4 + j) := by
  rw [List.mem_map]
  refine ⟨fi - (l.init + 4), List.mem_range.mpr ?_, ?_⟩ <;>
    simp [Layout.isUniqueProc] at hlo <;> omega

theorem calledRuntimeRootsBase_mem_reuse_call {l : Layout} {p : Lir.Program}
    {fi : Nat} {F : Lir.Func} {b : Lir.Block} {rs : List Lir.VReg} {g : Nat} {as : List Lir.Arg}
    (hlo : l.isUniqueProc < fi) (hhi : fi < l.init + 4 + 4 * l.ctors.length)
    (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (hcall : Lir.Stmt.call rs g as ∈ b.body.toList) :
    (calledRuntimeRootsBase l p).contains g = true :=
  calledByIndices_mem_call (mem_reuseRange hlo hhi) hF hb hcall

theorem calledRuntimeRootsBase_mem_reuse_tail {l : Layout} {p : Lir.Program}
    {fi : Nat} {F : Lir.Func} {b : Lir.Block} {g : Nat} {as : List Lir.Arg}
    (hlo : l.isUniqueProc < fi) (hhi : fi < l.init + 4 + 4 * l.ctors.length)
    (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (htail : b.term = .tail g as) :
    (calledRuntimeRootsBase l p).contains g = true :=
  calledByIndices_mem_tail (mem_reuseRange hlo hhi) hF hb htail

private theorem mem_liveWrappers {l : Layout} {p : Lir.Program} {fi : Nat}
    (hlo : l.sourceCount ≤ fi) (hhi : fi < l.incProc)
    (hbase : (calledRuntimeRootsBase l p).contains fi = true) :
    fi ∈ ((List.range (2 + l.ctors.length)).map (fun j => l.sourceCount + j)).filter
      (fun idx => (calledRuntimeRootsBase l p).contains idx) := by
  rw [List.mem_filter]
  refine ⟨?_, hbase⟩
  rw [List.mem_map]
  refine ⟨fi - l.sourceCount, List.mem_range.mpr ?_, ?_⟩ <;>
    simp [Layout.incProc] at hhi <;> omega

theorem calledRuntimeRoots_mem_wrapper_call {l : Layout} {p : Lir.Program}
    {fi : Nat} {F : Lir.Func} {b : Lir.Block} {rs : List Lir.VReg} {g : Nat} {as : List Lir.Arg}
    (hlo : l.sourceCount ≤ fi) (hhi : fi < l.incProc)
    (hbase : (calledRuntimeRootsBase l p).contains fi = true)
    (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (hcall : Lir.Stmt.call rs g as ∈ b.body.toList) :
    (calledRuntimeRoots l p).contains g = true :=
  calledByIndices_mem_call (mem_liveWrappers hlo hhi hbase) hF hb hcall

theorem calledRuntimeRoots_mem_wrapper_tail {l : Layout} {p : Lir.Program}
    {fi : Nat} {F : Lir.Func} {b : Lir.Block} {g : Nat} {as : List Lir.Arg}
    (hlo : l.sourceCount ≤ fi) (hhi : fi < l.incProc)
    (hbase : (calledRuntimeRootsBase l p).contains fi = true)
    (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (htail : b.term = .tail g as) :
    (calledRuntimeRoots l p).contains g = true :=
  calledByIndices_mem_tail (mem_liveWrappers hlo hhi hbase) hF hb htail

theorem pruneDeadRuntime_main (l : Layout) (p : Lir.Program) :
    (pruneDeadRuntime l p).main = p.main := rfl

theorem pruneDeadRuntime_funcs_size (l : Layout) (p : Lir.Program) :
    (pruneDeadRuntime l p).funcs.size = p.funcs.size := by
  simp [pruneDeadRuntime]

theorem pruneDeadRuntime_get_not_prunable {l : Layout} {p : Lir.Program} {f : Nat}
    (h : isPrunableDeadRuntime l f = false) :
    (pruneDeadRuntime l p).funcs[f]? = p.funcs[f]? := by
  simp only [pruneDeadRuntime, Array.getElem?_mapIdx]
  cases hget : p.funcs[f]? with
  | none => simp
  | some F => simp [h]

theorem pruneDeadRuntime_get_used {l : Layout} {p : Lir.Program} {f : Nat}
    (h : (calledRuntimeRoots l p).contains f = true) :
    (pruneDeadRuntime l p).funcs[f]? = p.funcs[f]? := by
  simp only [pruneDeadRuntime, Array.getElem?_mapIdx]
  cases hget : p.funcs[f]? with
  | none => simp
  | some F => simp [h]

private theorem calledByIndices_push (p : Lir.Program) (fn : Lir.Func)
    (fs : List Nat) (acc : Src.NatSet) (h : ∀ fi ∈ fs, fi < p.funcs.size) :
    calledByIndices fs { p with funcs := p.funcs.push fn } acc = calledByIndices fs p acc :=
  foldl_calledBySources_push p fn fs acc h

theorem calledRuntimeRootsBase_push {l : Layout} {p : Lir.Program} {fn : Lir.Func}
    (hsize : l.init + 4 + 4 * l.ctors.length ≤ p.funcs.size) :
    calledRuntimeRootsBase l { p with funcs := p.funcs.push fn } =
      calledRuntimeRootsBase l p := by
  have hsrc : ∀ fi ∈ List.range l.sourceCount, fi < p.funcs.size := fun fi hfi => by
    have := List.mem_range.mp hfi
    simp only [Layout.init, Layout.incProc] at hsize; omega
  have hre : ∀ fi ∈ (List.range (4 * l.ctors.length)).map (fun j => l.init + 4 + j),
      fi < p.funcs.size := fun fi hfi => by
    rcases List.mem_map.mp hfi with ⟨j, hj, rfl⟩
    have := List.mem_range.mp hj
    omega
  unfold calledRuntimeRootsBase
  rw [calledByIndices_push p fn _ .leaf hsrc, calledByIndices_push p fn _ _ hre]

theorem calledRuntimeRoots_push {l : Layout} {p : Lir.Program} {fn : Lir.Func}
    (hsize : l.init + 4 + 4 * l.ctors.length ≤ p.funcs.size) :
    calledRuntimeRoots l { p with funcs := p.funcs.push fn } =
      calledRuntimeRoots l p := by
  have hwrap : ∀ fi ∈ ((List.range (2 + l.ctors.length)).map (fun j => l.sourceCount + j)).filter
      (fun idx => (calledRuntimeRootsBase l p).contains idx), fi < p.funcs.size := fun fi hfi => by
    have hmem := (List.mem_filter.mp hfi).1
    rcases List.mem_map.mp hmem with ⟨j, hj, rfl⟩
    have := List.mem_range.mp hj
    simp only [Layout.init, Layout.incProc] at hsize; omega
  unfold calledRuntimeRoots
  rw [calledRuntimeRootsBase_push hsize]
  exact calledByIndices_push p fn _ _ hwrap

theorem isPrunableDeadRuntime_of_gt_isUnique {l : Layout} {i : Nat}
    (h : l.isUniqueProc < i) : isPrunableDeadRuntime l i = false := by
  unfold isPrunableDeadRuntime
  rw [decide_eq_false_iff_not]
  simp only [Layout.isUniqueProc, Layout.init, Layout.decProc, Layout.incProc] at h ⊢
  intro hbad
  rcases hbad with ⟨h1, h2⟩ | h1 | ⟨h1, h2⟩ | h1 <;> omega

theorem isPrunableDeadRuntime_decProc (l : Layout) :
    isPrunableDeadRuntime l l.decProc = false := by
  unfold isPrunableDeadRuntime
  rw [decide_eq_false_iff_not]
  simp only [Layout.isUniqueProc, Layout.init, Layout.decProc, Layout.incProc]
  intro hbad
  rcases hbad with ⟨h1, h2⟩ | h1 | ⟨h1, h2⟩ | h1 <;> omega

theorem isPrunableDeadRuntime_init (l : Layout) :
    isPrunableDeadRuntime l l.init = false := by
  unfold isPrunableDeadRuntime
  rw [decide_eq_false_iff_not]
  simp only [Layout.isUniqueProc, Layout.init, Layout.decProc, Layout.incProc]
  intro hbad
  rcases hbad with ⟨h1, h2⟩ | h1 | ⟨h1, h2⟩ | h1 <;> omega

theorem pruneDeadRuntime_push {l : Layout} {p : Lir.Program} {fn : Lir.Func}
    (hsize : l.init + 4 + 4 * l.ctors.length ≤ p.funcs.size) :
    pruneDeadRuntime l { p with funcs := p.funcs.push fn } =
      { pruneDeadRuntime l p with funcs := (pruneDeadRuntime l p).funcs.push fn } := by
  have hnp : isPrunableDeadRuntime l p.funcs.size = false :=
    isPrunableDeadRuntime_of_gt_isUnique (by simp only [Layout.isUniqueProc]; omega)
  simp only [pruneDeadRuntime, calledRuntimeRoots_push hsize, Array.mapIdx_push, hnp,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-! ### Size bound for `pruneDeadRuntime` -/

def DeadRuntimeSizeBound (l : Layout) (p : Lir.Program) : Prop :=
  ∀ fi F, isPrunableDeadRuntime l fi = true → p.funcs[fi]? = some F → F.size ≤ 256

private theorem pruneStub_size (F : Lir.Func) : (pruneStub F).size = 1 := by
  simp [pruneStub, Lir.Func.size, Lir.Block.size]

private theorem list_sum_le_mul_of_pointwise (c : Nat) :
    ∀ (xs ys : List Nat), xs.length = ys.length →
      (∀ i (hx : i < xs.length) (hy : i < ys.length), xs[i] ≤ c * ys[i]) →
      xs.sum ≤ c * ys.sum
  | [], [], _, _ => by simp
  | x :: xs, y :: ys, hlen, hpt => by
    have h0 : x ≤ c * y := hpt 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
    have hrest : xs.sum ≤ c * ys.sum :=
      list_sum_le_mul_of_pointwise c xs ys (Nat.succ.inj hlen) fun i hx hy =>
        hpt (i + 1) (Nat.succ_lt_succ hx) (Nat.succ_lt_succ hy)
    simp only [List.sum_cons, Nat.mul_add]
    omega

theorem pruneDeadRuntime_size_bound {l : Layout} {p : Lir.Program}
    (hb : DeadRuntimeSizeBound l p) :
    p.size ≤ 256 * (pruneDeadRuntime l p).size := by
  rw [Inline.program_size_eq_sum, Inline.program_size_eq_sum]
  apply list_sum_le_mul_of_pointwise 256
  · simp [pruneDeadRuntime]
  · intro i hx hy
    have hi : i < p.funcs.size := by simpa using hx
    simp only [List.getElem_map, Array.getElem_toList, pruneDeadRuntime, Array.getElem_mapIdx]
    split
    · next hpr =>
      have hpr' : isPrunableDeadRuntime l i = true := (Bool.and_eq_true _ _).mp hpr |>.1
      have hle := hb i p.funcs[i] hpr' (Array.getElem?_eq_getElem hi)
      rw [pruneStub_size]
      omega
    · omega

theorem fuelFor_le_mul_pruneDeadRuntime {l : Layout} {p : Lir.Program}
    (hb : DeadRuntimeSizeBound l p) (k : Nat) :
    Lir.fuelFor p k ≤ 256 * Lir.fuelFor (pruneDeadRuntime l p) k := by
  have hsz := pruneDeadRuntime_size_bound hb
  simp only [Lir.fuelFor]
  have h1 : p.size + 1 ≤ 256 * ((pruneDeadRuntime l p).size + 1) := by omega
  calc (2 * k + 3) * (p.size + 1)
      ≤ (2 * k + 3) * (256 * ((pruneDeadRuntime l p).size + 1)) := Nat.mul_le_mul_left _ h1
    _ = 256 * ((2 * k + 3) * ((pruneDeadRuntime l p).size + 1)) := by
        rw [Nat.mul_left_comm]

/-! ### Exact step and `Lir.eval` preservation for `pruneDeadRuntime` -/

def NoDeadRuntimeCallsInFunc (l : Layout) (F : Lir.Func) : Prop :=
  ∀ b ∈ F.blocks.toList,
    (∀ rs g as, Lir.Stmt.call rs g as ∈ b.body.toList → isPrunableDeadRuntime l g = false) ∧
    (∀ g as, b.term = .tail g as → isPrunableDeadRuntime l g = false)

theorem noDeadRuntimeCalls_of_funcHasNoCalls {l : Layout} {F : Lir.Func}
    (h : funcHasNoCalls F = true) : NoDeadRuntimeCallsInFunc l F := by
  intro b hb
  have hblk := List.all_eq_true.mp h b hb
  simp only [Bool.and_eq_true] at hblk
  constructor
  · intro rs g as hcall
    have hs := List.all_eq_true.mp hblk.1 (.call rs g as) hcall
    simp [stmtNotCall] at hs
  · intro g as htail
    rw [htail] at hblk
    simp [termNotTail] at hblk

def NoDeadRuntimeCalls (l : Layout) (p : Lir.Program) : Prop :=
  ∀ fi F, l.incProc ≤ fi →
    ¬ (l.isUniqueProc < fi ∧ fi < l.init + 4 + 4 * l.ctors.length) →
    p.funcs[fi]? = some F → NoDeadRuntimeCallsInFunc l F

def NoWrapperToWrapperCalls (l : Layout) (p : Lir.Program) : Prop :=
  ∀ fi F, l.sourceCount ≤ fi → fi < l.incProc → p.funcs[fi]? = some F →
    ∀ b ∈ F.blocks.toList,
      (∀ rs g as, Lir.Stmt.call rs g as ∈ b.body.toList → ¬ (l.sourceCount ≤ g ∧ g < l.incProc)) ∧
      (∀ g as, b.term = .tail g as → ¬ (l.sourceCount ≤ g ∧ g < l.incProc))

def LiveRuntimeFn (l : Layout) (p : Lir.Program) (fi : Nat) : Prop :=
  (isPrunableDeadRuntime l fi = false ∨ (calledRuntimeRoots l p).contains fi = true) ∧
  (l.sourceCount ≤ fi ∧ fi < l.incProc → (calledRuntimeRootsBase l p).contains fi = true)

theorem liveRuntimeFn_of_not_prunable {l : Layout} {p : Lir.Program} {fi : Nat}
    (h : isPrunableDeadRuntime l fi = false) : LiveRuntimeFn l p fi := by
  refine ⟨.inl h, fun ⟨hlo, hhi⟩ => ?_⟩
  simp only [isPrunableDeadRuntime, decide_eq_false_iff_not] at h
  exact False.elim (h (.inl ⟨hlo, hhi⟩))

theorem liveRuntimeFn_get {l : Layout} {p : Lir.Program} {fi : Nat}
    (h : LiveRuntimeFn l p fi) :
    (pruneDeadRuntime l p).funcs[fi]? = p.funcs[fi]? := by
  rcases h.1 with hnp | hused
  · exact pruneDeadRuntime_get_not_prunable hnp
  · exact pruneDeadRuntime_get_used hused

def GoodRuntimeState (l : Layout) (p : Lir.Program) (s : Lir.State) : Prop :=
  ∀ fr ∈ s.stack, LiveRuntimeFn l p fr.fn

private theorem takeEdge_goodRuntime {l : Layout} {p : Lir.Program} {f : Lir.Func}
    {s : Lir.State} {fr : Lir.Frame} {rest : List Lir.Frame} {ρ : Lir.Env} {e : Lir.Edge}
    (hgood : GoodRuntimeState l p { s with stack := fr :: rest })
    {s' : Lir.State} {chg : Bool}
    (ht : Lir.takeEdge f s fr rest ρ e = .next s' chg) :
    GoodRuntimeState l p s' := by
  unfold Lir.takeEdge at ht
  cases he : Lir.evalArgs ρ e.args with
  | none => simp [he] at ht
  | some vals =>
    cases hb : f.blocks[e.target]? with
    | none => simp [he, hb] at ht
    | some target =>
      cases hp : Lir.bindParams ρ target.params vals with
      | none => simp [he, hb, hp] at ht
      | some ρ' =>
        simp only [he, hb, hp, Lir.Step.next.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        intro fr' hmem
        rcases List.mem_cons.mp hmem with rfl | hrest
        · exact hgood fr (List.mem_cons_self ..)
        · exact hgood fr' (List.mem_cons_of_mem fr hrest)

private theorem liveRuntimeFn_callee_call {l : Layout} {p : Lir.Program}
    (hno : NoDeadRuntimeCalls l p) (hww : NoWrapperToWrapperCalls l p)
    {fi g : Nat} {F : Lir.Func} {b : Lir.Block} {rs : List Lir.VReg} {as : List Lir.Arg}
    (hlive : LiveRuntimeFn l p fi) (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (hcall : Lir.Stmt.call rs g as ∈ b.body.toList) :
    LiveRuntimeFn l p g := by
  by_cases hsrc : fi < l.sourceCount
  · have hbase := calledRuntimeRootsBase_mem_source_call hsrc hF hb hcall
    exact ⟨.inr (calledRuntimeRoots_mono_base hbase), fun _ => hbase⟩
  · by_cases hwrap : fi < l.incProc
    · have hlo : l.sourceCount ≤ fi := Nat.not_lt.mp hsrc
      have hbase := hlive.2 ⟨hlo, hwrap⟩
      exact ⟨.inr (calledRuntimeRoots_mem_wrapper_call hlo hwrap hbase hF hb hcall),
        fun hg => False.elim ((hww fi F hlo hwrap hF b hb).1 rs g as hcall hg)⟩
    · by_cases hreuse : l.isUniqueProc < fi ∧ fi < l.init + 4 + 4 * l.ctors.length
      · have hbase := calledRuntimeRootsBase_mem_reuse_call hreuse.1 hreuse.2 hF hb hcall
        exact ⟨.inr (calledRuntimeRoots_mono_base hbase), fun _ => hbase⟩
      · exact liveRuntimeFn_of_not_prunable
          ((hno fi F (Nat.not_lt.mp hwrap) hreuse hF b hb).1 rs g as hcall)

private theorem liveRuntimeFn_callee_tail {l : Layout} {p : Lir.Program}
    (hno : NoDeadRuntimeCalls l p) (hww : NoWrapperToWrapperCalls l p)
    {fi g : Nat} {F : Lir.Func} {b : Lir.Block} {as : List Lir.Arg}
    (hlive : LiveRuntimeFn l p fi) (hF : p.funcs[fi]? = some F)
    (hb : b ∈ F.blocks.toList) (htail : b.term = .tail g as) :
    LiveRuntimeFn l p g := by
  by_cases hsrc : fi < l.sourceCount
  · have hbase := calledRuntimeRootsBase_mem_source_tail hsrc hF hb htail
    exact ⟨.inr (calledRuntimeRoots_mono_base hbase), fun _ => hbase⟩
  · by_cases hwrap : fi < l.incProc
    · have hlo : l.sourceCount ≤ fi := Nat.not_lt.mp hsrc
      have hbase := hlive.2 ⟨hlo, hwrap⟩
      exact ⟨.inr (calledRuntimeRoots_mem_wrapper_tail hlo hwrap hbase hF hb htail),
        fun hg => False.elim ((hww fi F hlo hwrap hF b hb).2 g as htail hg)⟩
    · by_cases hreuse : l.isUniqueProc < fi ∧ fi < l.init + 4 + 4 * l.ctors.length
      · have hbase := calledRuntimeRootsBase_mem_reuse_tail hreuse.1 hreuse.2 hF hb htail
        exact ⟨.inr (calledRuntimeRoots_mono_base hbase), fun _ => hbase⟩
      · exact liveRuntimeFn_of_not_prunable
          ((hno fi F (Nat.not_lt.mp hwrap) hreuse hF b hb).2 g as htail)

theorem pruneDeadRuntime_step {l : Layout} {p : Lir.Program}
    (hno : NoDeadRuntimeCalls l p) (hww : NoWrapperToWrapperCalls l p) {s : Lir.State}
    (hgood : GoodRuntimeState l p s) :
    Lir.step (pruneDeadRuntime l p) s = Lir.step p s ∧
    (∀ s' chg, Lir.step p s = .next s' chg → GoodRuntimeState l p s') := by
  let pruned := pruneDeadRuntime l p
  change Lir.step pruned s = Lir.step p s ∧
    (∀ s' chg, Lir.step p s = .next s' chg → GoodRuntimeState l p s')
  cases hstack : s.stack with
  | nil =>
    constructor
    · simp [Lir.step, hstack]
    · intro s' chg hstep; simp [Lir.step, hstack] at hstep
  | cons fr rest =>
    have hfrLive : LiveRuntimeFn l p fr.fn :=
      hgood fr (by rw [hstack]; exact List.mem_cons_self ..)
    have hfr : pruned.funcs[fr.fn]? = p.funcs[fr.fn]? := liveRuntimeFn_get hfrLive
    have hgood' : GoodRuntimeState l p { s with stack := fr :: rest } := by
      intro x hx; exact hgood x (by rw [hstack]; exact hx)
    cases hF : p.funcs[fr.fn]? with
    | none =>
      constructor
      · simp [Lir.step, hstack, hfr, hF]
      · intro s' chg hstep; simp [Lir.step, hstack, hF] at hstep
    | some F =>
      cases hb : F.blocks[fr.label]? with
      | none =>
        constructor
        · simp [Lir.step, hstack, hfr, hF, hb]
        · intro s' chg hstep; simp [Lir.step, hstack, hF, hb] at hstep
      | some b =>
        have hbMem : b ∈ F.blocks.toList := by
          rw [← Array.getElem?_toList] at hb
          exact List.mem_of_getElem? hb
        by_cases hpos : fr.pos < b.body.size
        · have hsMem : b.body[fr.pos] ∈ b.body.toList := Array.getElem_mem_toList hpos
          cases hstmt : b.body[fr.pos] with
          | call rs g as =>
            have hgLive : LiveRuntimeFn l p g :=
              liveRuntimeFn_callee_call hno hww hfrLive hF hbMem (hstmt ▸ hsMem)
            have hgEq : pruned.funcs[g]? = p.funcs[g]? := liveRuntimeFn_get hgLive
            have hbind : (Lir.evalArgs fr.env as >>= Lir.enter pruned g) =
                (Lir.evalArgs fr.env as >>= Lir.enter p g) := by
              cases Lir.evalArgs fr.env as with
              | none => rfl
              | some vals => exact enter_eq_of_get_eq hgEq
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hstmt, hbind]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hstmt] at hstep
              cases hev : Lir.evalArgs fr.env as with
              | none => simp [hev] at hstep
              | some vals =>
                simp only [hev, bind, Option.bind] at hstep
                cases hent : Lir.enter p g vals with
                | none => simp [hent] at hstep
                | some callee =>
                  simp only [hent, Lir.Step.next.injEq] at hstep
                  obtain ⟨rfl, _⟩ := hstep
                  intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx1
                  · rw [enter_fn hent]; exact hgLive
                  · rcases List.mem_cons.mp hx1 with rfl | hx2
                    · exact hfrLive
                    · exact hgood' x (List.mem_cons_of_mem fr hx2)
          | assign x r =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hstmt]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hstmt] at hstep
              cases hex : (Lir.Stmt.assign x r).exec fr.env s.mem s.ctx with
              | none => simp [hex] at hstep
              | some pm =>
                simp only [hex, Lir.Step.next.injEq] at hstep
                obtain ⟨rfl, _⟩ := hstep
                intro y hy
                rcases List.mem_cons.mp hy with rfl | hrest
                · exact hfrLive
                · exact hgood' y (List.mem_cons_of_mem fr hrest)
          | limb r1 r2 op =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hstmt]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hstmt] at hstep
              cases hex : (Lir.Stmt.limb r1 r2 op).exec fr.env s.mem s.ctx with
              | none => simp [hex] at hstep
              | some pm =>
                simp only [hex, Lir.Step.next.injEq] at hstep
                obtain ⟨rfl, _⟩ := hstep
                intro y hy
                rcases List.mem_cons.mp hy with rfl | hrest
                · exact hfrLive
                · exact hgood' y (List.mem_cons_of_mem fr hrest)
          | store w m a =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hstmt]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hstmt] at hstep
              cases hex : (Lir.Stmt.store w m a).exec fr.env s.mem s.ctx with
              | none => simp [hex] at hstep
              | some pm =>
                simp only [hex, Lir.Step.next.injEq] at hstep
                obtain ⟨rfl, _⟩ := hstep
                intro y hy
                rcases List.mem_cons.mp hy with rfl | hrest
                · exact hfrLive
                · exact hgood' y (List.mem_cons_of_mem fr hrest)
        · cases hterm : b.term with
          | jump e =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hterm] at hstep
              exact takeEdge_goodRuntime hgood' hstep
          | br c w a b' t e =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hterm] at hstep
              cases ha : a.eval fr.env with
              | none => simp [ha] at hstep
              | some va =>
                cases hb' : b'.eval fr.env with
                | none => simp [ha, hb'] at hstep
                | some vb =>
                  simp only [ha, hb'] at hstep
                  exact takeEdge_goodRuntime hgood' hstep
          | brOvf o x a b' ok ovf =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hterm] at hstep
              cases ha : a.eval fr.env with
              | none => simp [ha] at hstep
              | some va =>
                cases hb' : b'.eval fr.env with
                | none => simp [ha, hb'] at hstep
                | some vb =>
                  simp only [ha, hb'] at hstep
                  exact takeEdge_goodRuntime hgood' hstep
          | ret as =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hterm] at hstep
              cases hev : Lir.evalArgs fr.env as with
              | none => simp [hev] at hstep
              | some vals =>
                simp only [hev] at hstep
                cases rest with
                | nil => cases hstep
                | cons caller rest' =>
                  cases hbp : Lir.bindParams caller.env caller.dsts vals with
                  | none => simp [hbp] at hstep
                  | some ρ =>
                    simp only [hbp, Lir.Step.next.injEq] at hstep
                    obtain ⟨rfl, _⟩ := hstep
                    intro y hy
                    rcases List.mem_cons.mp hy with rfl | hrest
                    · exact hgood' caller (List.mem_cons_of_mem fr (List.mem_cons_self ..))
                    · exact hgood' y (List.mem_cons_of_mem fr (List.mem_cons_of_mem caller hrest))
          | tail g as =>
            have hgLive : LiveRuntimeFn l p g :=
              liveRuntimeFn_callee_tail hno hww hfrLive hF hbMem hterm
            have hgEq : pruned.funcs[g]? = p.funcs[g]? := liveRuntimeFn_get hgLive
            have hbind : (Lir.evalArgs fr.env as >>= Lir.enter pruned g) =
                (Lir.evalArgs fr.env as >>= Lir.enter p g) := by
              cases Lir.evalArgs fr.env as with
              | none => rfl
              | some vals => exact enter_eq_of_get_eq hgEq
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm, hbind]
            · intro s' chg hstep
              simp only [Lir.step, hstack, hF, hb, hpos, ↓reduceDIte, hterm] at hstep
              cases hev : Lir.evalArgs fr.env as with
              | none => simp [hev] at hstep
              | some vals =>
                simp only [hev, bind, Option.bind] at hstep
                cases hent : Lir.enter p g vals with
                | none => simp [hent] at hstep
                | some callee =>
                  simp only [hent, Lir.Step.next.injEq] at hstep
                  obtain ⟨rfl, _⟩ := hstep
                  intro y hy
                  rcases List.mem_cons.mp hy with rfl | hrest
                  · rw [enter_fn hent]; exact hgLive
                  · exact hgood' y (List.mem_cons_of_mem fr hrest)
          | fail r =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep; simp [Lir.step, hstack, hF, hb, hpos, hterm] at hstep
          | trap =>
            constructor
            · simp only [Lir.step, hstack, hfr, hF, hb, hpos, ↓reduceDIte, hterm]
            · intro s' chg hstep; simp [Lir.step, hstack, hF, hb, hpos, hterm] at hstep

theorem pruneDeadRuntime_reaches {l : Layout} {p : Lir.Program}
    (hno : NoDeadRuntimeCalls l p) (hww : NoWrapperToWrapperCalls l p)
    {s : Lir.State} {k : Nat} {r : Lir.Outcome}
    (hreach : Sem.Reaches (Lir.semStep p) s k r)
    (hgood : GoodRuntimeState l p s) :
    Sem.Reaches (Lir.semStep (pruneDeadRuntime l p)) s k r := by
  induction hreach with
  | @final s0 _ _ hf =>
    obtain ⟨hstepEq, _⟩ := pruneDeadRuntime_step hno hww hgood
    have hsemEq : Lir.semStep (pruneDeadRuntime l p) s0 = Lir.semStep p s0 := by
      simp [Lir.semStep, hstepEq]
    exact .final (hsemEq.symm ▸ hf)
  | @free s0 _ _ _ hs _ ih =>
    obtain ⟨hstepEq, hnextGood⟩ := pruneDeadRuntime_step hno hww hgood
    have hsemEq : Lir.semStep (pruneDeadRuntime l p) s0 = Lir.semStep p s0 := by
      simp [Lir.semStep, hstepEq]
    exact .free (hsemEq.trans hs) (ih (hnextGood _ false (Lir.semStep_next.mp hs)))
  | @charge s0 _ _ _ hs _ ih =>
    obtain ⟨hstepEq, hnextGood⟩ := pruneDeadRuntime_step hno hww hgood
    have hsemEq : Lir.semStep (pruneDeadRuntime l p) s0 = Lir.semStep p s0 := by
      simp [Lir.semStep, hstepEq]
    exact .charge (hsemEq.trans hs) (ih (hnextGood _ true (Lir.semStep_next.mp hs)))
  | @timeout s0 _ hs =>
    obtain ⟨hstepEq, _⟩ := pruneDeadRuntime_step hno hww hgood
    have hsemEq : Lir.semStep (pruneDeadRuntime l p) s0 = Lir.semStep p s0 := by
      simp [Lir.semStep, hstepEq]
    exact .timeout (hsemEq.trans hs)

theorem pruneDeadRuntime_eval_eq {l : Layout} {p : Lir.Program}
    (hno : NoDeadRuntimeCalls l p) (hww : NoWrapperToWrapperCalls l p)
    (hmain : LiveRuntimeFn l p p.main)
    (k : Nat) (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word) :
    Lir.eval (pruneDeadRuntime l p) k args mem ctx = Lir.eval p k args mem ctx := by
  let pruned := pruneDeadRuntime l p
  change Lir.eval pruned k args mem ctx = Lir.eval p k args mem ctx
  have hmainGet : pruned.funcs[p.main]? = p.funcs[p.main]? := liveRuntimeFn_get hmain
  cases hent : Lir.enter p p.main args with
  | none =>
    have hent' : Lir.enter pruned pruned.main args = none := by
      rw [pruneDeadRuntime_main, enter_eq_of_get_eq hmainGet, hent]
    simp [Lir.eval, Lir.State.initial, hent, hent']
  | some fr =>
    have hent' : Lir.enter pruned pruned.main args = some fr := by
      rw [pruneDeadRuntime_main, enter_eq_of_get_eq hmainGet, hent]
    let s : Lir.State := { mem, ctx, stack := [fr] }
    have hinit : Lir.State.initial p args mem ctx = some s := by
      simp [Lir.State.initial, hent, s]
    have hinit' : Lir.State.initial pruned args mem ctx = some s := by
      simp [Lir.State.initial, hent', s]
    have hgood : GoodRuntimeState l p s := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hnil
      · rw [enter_fn hent]; exact hmain
      · cases hnil
    exact (Lir.runs_eval hinit').eq
      (pruneDeadRuntime_reaches hno hww (Lir.runs_eval hinit k) hgood)

theorem pruneDeadRuntime_sim {l : Layout} {p : Lir.Program}
    (hno : NoDeadRuntimeCalls l p) (hww : NoWrapperToWrapperCalls l p)
    (hmain : LiveRuntimeFn l p p.main)
    (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word) :
    Sem.Sim Eq id
      (fun k => Lir.eval p k args mem ctx)
      (fun k => Lir.eval (pruneDeadRuntime l p) k args mem ctx) where
  forward k _ := ⟨k, by
    rw [pruneDeadRuntime_eval_eq hno hww hmain]
    cases Lir.eval p k args mem ctx with
    | ok _ => exact .ok rfl
    | resource r => exact .resource r
    | trap => exact .trap
    | stuck => exact .stuck
    | timeout => exact .timeout⟩
  timeout k hk := .inl ((pruneDeadRuntime_eval_eq hno hww hmain k args mem ctx).trans hk)

end IxCC.Cfg.Rc.Prune
