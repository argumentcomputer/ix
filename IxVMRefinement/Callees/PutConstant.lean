import IxVMRefinement.Callees.TagN
import IxVMRefinement.Obs.IxonSerialize1
import IxVMRefinement.Obs.IxonSerialize2

/-! # `IxonSerialize::put_constant` on projection records

Step lemma for `IxonSerialize::put_constant` at a projection record with empty side tables
(`ProjConstRep`), writing `Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩` in front of `rest`. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ProjAddrAux

theorem repU64_mono {h h' : Heap F} {w : UInt64} {v : SourceValue F}
    (_ : Heap.Extends h h') (hr : RepU64 h w v) : RepU64 h' w v := hr

theorem proj_addr_get {h : Heap F} {b : Bytes.Address} {x_a v1 : SourceValue F}
    (ha : RepAddr h b x_a) (ld : loadValue h x_a = .ok v1)
    (i : Nat) (hi : i < 32) {v : SourceValue F} (hp : projectValue v1 i = .ok v) :
    v = .field (b[i].toNat : F) := by
  obtain ⟨addr, v0, rfl, cell, hv⟩ := ha
  have hv1 : v1 = .tuple (b.toList.map fun c => Value.field (c.toNat : F)) :=
    (Lib.load_ptr_inv cell ld).trans hv
  subst hv1
  have hlt : i < b.toList.length := by rw [Vector.length_toList]; exact hi
  have hget : (b.toList.map fun c => (Value.field (c.toNat : F) : SourceValue F))[i]? =
      some (.field (b[i].toNat : F)) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]
    simp only [Option.map_some, Option.some.injEq, Vector.getElem_toList]
  simp only [projectValue, hget, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hp
  exact hp.symm

theorem put_address_spec {b : Bytes.Address} {x_a x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (ha : RepAddr h b x_a)
    (ev : ObsFn W "IxonSerialize::put_address" [x_a, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((ixAddr b).hash.data.toList ++ rest) r := by
  cases Obs.«IxonSerialize::put_address».obs ev with
  | run v1 m14 v28 m48 v62 m82 v96 m116 v130 m150 v164 m184 v198 m218 v232 m252 v266 m286 v300
      m320 v334 m354 v368 m388 v402 m422 v436 m456 v470 m490 v504 m524 v538 m558 v572 m592 v606
      m626 v640 m660 v674 m694 v708 m728 v742 m762 v776 m796 v810 m830 v844 m864 v878 m898 v912
      m932 v946 m966 v980 m1000 v1014 m1034 v1048 v1075 ld11 hm24 pr38 hm58 pr72 hm92 pr106 hm126
      pr140 hm160 pr174 hm194 pr208 hm228 pr242 hm262 pr276 hm296 pr310 hm330 pr344 hm364 pr378
      hm398 pr412 hm432 pr446 hm466 pr480 hm500 pr514 hm534 pr548 hm568 pr582 hm602 pr616 hm636
      pr650 hm670 pr684 hm704 pr718 hm738 pr752 hm772 pr786 hm806 pr820 hm840 pr854 hm874 pr888
      hm908 pr922 hm942 pr956 hm976 pr990 hm1010 pr1024 hm1044 pr1058 he1071 hm1070 pr1085 _ =>
    have get := proj_addr_get ha ld11
    have s31 := repBytes_cons (get 31 (by omega) pr38)   hrest hm24   rfl
    have s30 := repBytes_cons (get 30 (by omega) pr72)   s31   hm58   rfl
    have s29 := repBytes_cons (get 29 (by omega) pr106)  s30   hm92   rfl
    have s28 := repBytes_cons (get 28 (by omega) pr140)  s29   hm126  rfl
    have s27 := repBytes_cons (get 27 (by omega) pr174)  s28   hm160  rfl
    have s26 := repBytes_cons (get 26 (by omega) pr208)  s27   hm194  rfl
    have s25 := repBytes_cons (get 25 (by omega) pr242)  s26   hm228  rfl
    have s24 := repBytes_cons (get 24 (by omega) pr276)  s25   hm262  rfl
    have s23 := repBytes_cons (get 23 (by omega) pr310)  s24   hm296  rfl
    have s22 := repBytes_cons (get 22 (by omega) pr344)  s23   hm330  rfl
    have s21 := repBytes_cons (get 21 (by omega) pr378)  s22   hm364  rfl
    have s20 := repBytes_cons (get 20 (by omega) pr412)  s21   hm398  rfl
    have s19 := repBytes_cons (get 19 (by omega) pr446)  s20   hm432  rfl
    have s18 := repBytes_cons (get 18 (by omega) pr480)  s19   hm466  rfl
    have s17 := repBytes_cons (get 17 (by omega) pr514)  s18   hm500  rfl
    have s16 := repBytes_cons (get 16 (by omega) pr548)  s17   hm534  rfl
    have s15 := repBytes_cons (get 15 (by omega) pr582)  s16   hm568  rfl
    have s14 := repBytes_cons (get 14 (by omega) pr616)  s15   hm602  rfl
    have s13 := repBytes_cons (get 13 (by omega) pr650)  s14   hm636  rfl
    have s12 := repBytes_cons (get 12 (by omega) pr684)  s13   hm670  rfl
    have s11 := repBytes_cons (get 11 (by omega) pr718)  s12   hm704  rfl
    have s10 := repBytes_cons (get 10 (by omega) pr752)  s11   hm738  rfl
    have s9  := repBytes_cons (get 9  (by omega) pr786)  s10   hm772  rfl
    have s8  := repBytes_cons (get 8  (by omega) pr820)  s9    hm806  rfl
    have s7  := repBytes_cons (get 7  (by omega) pr854)  s8    hm840  rfl
    have s6  := repBytes_cons (get 6  (by omega) pr888)  s7    hm874  rfl
    have s5  := repBytes_cons (get 5  (by omega) pr922)  s6    hm908  rfl
    have s4  := repBytes_cons (get 4  (by omega) pr956)  s5    hm942  rfl
    have s3  := repBytes_cons (get 3  (by omega) pr990)  s4    hm976  rfl
    have s2  := repBytes_cons (get 2  (by omega) pr1024) s3    hm1010 rfl
    have s1  := repBytes_cons (get 1  (by omega) pr1058) s2    hm1044 rfl
    have s0  := repBytes_cons (get 0  (by omega) pr1085) s1    hm1070 he1071
    have hhash : (ixAddr b).hash.data.toList = b.toList := by simp [ixAddr]
    rw [hhash, Lib.vec32_toList b]
    exact s0

theorem put_sharing_nil_spec {x_list x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hl : RepList Specs.Callees.ixExprListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (ev : ObsFn W "IxonSerialize::put_sharing" [x_list, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((tag0Bytes 0).data.toList ++ rest) r := by
  rcases Obs.«IxonSerialize::put_sharing».obs ev with ⟨v1, m2, _, _, v30, m39, _, ev14, ev49, ev28, -⟩
  rw [← Obs.Names.«WordLists::length_u64<&Ixon::Expr>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Expr" [])]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Obs.Names.«Lists::Node<&Ixon::Expr>».symbol]
  obtain ⟨rfl, hm2⟩ := length_u64_nil_spec ev14 hl'
  rw [hm2] at ev49
  cases Obs.«IxonSerialize::put_expr_list».obs ev49 with
  | Nil _ hr hh _ =>
    rw [hr, hh] at ev28
    exact put_tagn0_spec (Lib.repU64_ofNatLT h (m := 0) (by omega)) ev28 hrest
  | Cons _ _ _ _ _ _ _ ld12 _ _ _ _ =>
    obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hl ld12
    cases he

theorem put_refs_nil_spec {x_list x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hl : RepList addrListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (ev : ObsFn W "IxonSerialize::put_refs" [x_list, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((tag0Bytes 0).data.toList ++ rest) r := by
  rcases Obs.«IxonSerialize::put_refs».obs ev with ⟨v1, m2, _, _, v30, m39, _, ev14, ev49, ev28, -⟩
  rw [← Obs.Names.«WordLists::length_u64<&[Field; 32]>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Obs.Names.«Lists::Node<&[Field; 32]>».symbol]
  obtain ⟨rfl, hm2⟩ := length_u64_nil_spec ev14 hl'
  rw [hm2] at ev49
  cases Obs.«IxonSerialize::put_address_list».obs ev49 with
  | Nil _ hr hh _ =>
    rw [hr, hh] at ev28
    exact put_tagn0_spec (Lib.repU64_ofNatLT h (m := 0) (by omega)) ev28 hrest
  | Cons _ _ _ _ _ _ ld12 _ _ _ =>
    obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hl ld12
    cases he

theorem put_univs_nil_spec {x_list x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hl : RepList Specs.Callees.ixUnivListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (ev : ObsFn W "IxonSerialize::put_univs" [x_list, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((tag0Bytes 0).data.toList ++ rest) r := by
  rcases Obs.«IxonSerialize::put_univs».obs ev with ⟨v1, m2, _, _, v30, m39, _, ev14, ev49, ev28, -⟩
  rw [← Obs.Names.«WordLists::length_u64<&Ixon::Univ>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Univ" [])]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Obs.Names.«Lists::Node<&Ixon::Univ>».symbol]
  obtain ⟨rfl, hm2⟩ := length_u64_nil_spec ev14 hl'
  rw [hm2] at ev49
  cases Obs.«IxonSerialize::put_univ_list».obs ev49 with
  | Nil _ hr hh _ =>
    rw [hr, hh] at ev28
    exact put_tagn0_spec (Lib.repU64_ofNatLT h (m := 0) (by omega)) ev28 hrest
  | Cons _ _ _ _ _ _ _ ld12 _ _ _ _ =>
    obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hl ld12
    cases he

theorem put_binders_nil_spec {x_list x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hl : RepList Specs.Callees.ixBinderListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (ev : ObsFn W "IxonSerialize::put_binders" [x_list, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((tag0Bytes 0).data.toList ++ rest) r := by
  rcases Obs.«IxonSerialize::put_binders».obs ev with
    ⟨v1, m2, _, _, v30, m39, _, ev14, ev49, ev28, -⟩
  rw [← Obs.Names.«WordLists::length_u64<Ixon::BinderBlock>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.named "Ixon::BinderBlock" []]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Obs.Names.«Lists::Node<Ixon::BinderBlock>».symbol]
  obtain ⟨rfl, hm2⟩ := length_u64_nil_spec ev14 hl'
  rw [hm2] at ev49
  cases Obs.«IxonSerialize::put_binder_block_list».obs ev49 with
  | Nil _ hr hh _ =>
    rw [hr, hh] at ev28
    exact put_tagn0_spec (Lib.repU64_ofNatLT h (m := 0) (by omega)) ev28 hrest
  | Cons _ _ _ _ _ _ ld12 _ _ _ =>
    obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hl ld12
    cases he

def constructorProjBytes (p : Ixon.ConstructorProj) : ByteArray :=
  tag0Bytes p.idx ++ tag0Bytes p.cidx ++ p.block.hash

def recursorProjBytes (p : Ixon.RecursorProj) : ByteArray :=
  tag0Bytes p.idx ++ p.block.hash

def inductiveProjBytes (p : Ixon.InductiveProj) : ByteArray :=
  tag0Bytes p.idx ++ p.block.hash

def definitionProjBytes (p : Ixon.DefinitionProj) : ByteArray :=
  tag0Bytes p.idx ++ p.block.hash

theorem put_cprj_info_spec {p : Ixon.ConstructorProj} {vi vj bp x_rest r : SourceValue F}
    {b : Bytes.Address} {h h' : Heap F} {calls : List (Call F)} {rest : List UInt8}
    (hvi : RepU64 h p.idx vi) (hvj : RepU64 h p.cidx vj)
    (hb : RepAddr h b bp) (hblk : ixAddr b = p.block)
    (ev : ObsFn W "IxonSerialize::put_constant_info"
      [.construct "Ixon::ConstantInfo" "CPrj"
        [.construct "Ixon::ConstructorProj" "Mk" [vi, vj, bp]], x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((constructorProjBytes p).data.toList ++ rest) r := by
  cases Obs.«IxonSerialize::put_constant_info».obs ev with
  | Defn _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Recr _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Axio _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Quot _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | RPrj _ _ _ _ _ _ hne _ _ _ => exact absurd rfl (hne _ rfl)
  | IPrj _ _ _ _ _ _ hne _ _ _ _ => exact absurd rfl (hne _ rfl)
  | DPrj _ _ _ _ _ _ hne _ _ _ _ _ => exact absurd rfl (hne _ rfl)
  | CPrj x_prj _ _ _ _ _ hv155 ev167 _ =>
    injection hv155 with _ _ hx
    injection hx with hx _
    subst hx
    rcases Obs.«IxonSerialize::put_constructor_proj».obs ev167 with
      ⟨x_idx, x_cidx, x_block, _, v39, m48, _, v60, m69, _, hv15, ev79, ev58, ev37, -⟩
    injection hv15 with _ _ hargs
    injection hargs with ha1 hargs; subst ha1
    injection hargs with ha2 hargs; subst ha2
    injection hargs with ha3 _; subst ha3
    have s1 := put_address_spec hb ev79 hrest
    have s2 := put_tagn0_spec hvj ev58 s1
    have s3 := put_tagn0_spec hvi ev37 s2
    rw [hblk] at s3
    simpa [constructorProjBytes, List.append_assoc]
      using s3

theorem put_rprj_info_spec {p : Ixon.RecursorProj} {vi bp x_rest r : SourceValue F}
    {b : Bytes.Address} {h h' : Heap F} {calls : List (Call F)} {rest : List UInt8}
    (hvi : RepU64 h p.idx vi) (hb : RepAddr h b bp) (hblk : ixAddr b = p.block)
    (ev : ObsFn W "IxonSerialize::put_constant_info"
      [.construct "Ixon::ConstantInfo" "RPrj"
        [.construct "Ixon::RecursorProj" "Mk" [vi, bp]], x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((recursorProjBytes p).data.toList ++ rest) r := by
  cases Obs.«IxonSerialize::put_constant_info».obs ev with
  | Defn _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Recr _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Axio _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Quot _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | CPrj _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | IPrj _ _ _ _ _ _ _ hne _ _ _ => exact absurd rfl (hne _ rfl)
  | DPrj _ _ _ _ _ _ _ hne _ _ _ _ => exact absurd rfl (hne _ rfl)
  | RPrj x_prj _ _ _ _ _ _ hv190 ev202 _ =>
    injection hv190 with _ _ hx
    injection hx with hx _
    subst hx
    rcases Obs.«IxonSerialize::put_recursor_proj».obs ev202 with
      ⟨x_idx, x_block, _, v34, m43, _, hv15, ev53, ev32, -⟩
    injection hv15 with _ _ hargs
    injection hargs with ha1 hargs; subst ha1
    injection hargs with ha2 _; subst ha2
    have s1 := put_address_spec hb ev53 hrest
    have s2 := put_tagn0_spec hvi ev32 s1
    rw [hblk] at s2
    simpa [recursorProjBytes, List.append_assoc]
      using s2

theorem put_iprj_info_spec {p : Ixon.InductiveProj} {vi bp x_rest r : SourceValue F}
    {b : Bytes.Address} {h h' : Heap F} {calls : List (Call F)} {rest : List UInt8}
    (hvi : RepU64 h p.idx vi) (hb : RepAddr h b bp) (hblk : ixAddr b = p.block)
    (ev : ObsFn W "IxonSerialize::put_constant_info"
      [.construct "Ixon::ConstantInfo" "IPrj"
        [.construct "Ixon::InductiveProj" "Mk" [vi, bp]], x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((inductiveProjBytes p).data.toList ++ rest) r := by
  cases Obs.«IxonSerialize::put_constant_info».obs ev with
  | Defn _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Recr _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Axio _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Quot _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | CPrj _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | RPrj _ _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | DPrj _ _ _ _ _ _ _ _ hne _ _ _ => exact absurd rfl (hne _ rfl)
  | IPrj x_prj _ _ _ _ _ _ _ hv225 ev237 _ =>
    injection hv225 with _ _ hx
    injection hx with hx _
    subst hx
    rcases Obs.«IxonSerialize::put_inductive_proj».obs ev237 with
      ⟨x_idx, x_block, _, v34, m43, _, hv15, ev53, ev32, -⟩
    injection hv15 with _ _ hargs
    injection hargs with ha1 hargs; subst ha1
    injection hargs with ha2 _; subst ha2
    have s1 := put_address_spec hb ev53 hrest
    have s2 := put_tagn0_spec hvi ev32 s1
    rw [hblk] at s2
    simpa [inductiveProjBytes, List.append_assoc]
      using s2

theorem put_dprj_info_spec {p : Ixon.DefinitionProj} {vi bp x_rest r : SourceValue F}
    {b : Bytes.Address} {h h' : Heap F} {calls : List (Call F)} {rest : List UInt8}
    (hvi : RepU64 h p.idx vi) (hb : RepAddr h b bp) (hblk : ixAddr b = p.block)
    (ev : ObsFn W "IxonSerialize::put_constant_info"
      [.construct "Ixon::ConstantInfo" "DPrj"
        [.construct "Ixon::DefinitionProj" "Mk" [vi, bp]], x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((definitionProjBytes p).data.toList ++ rest) r := by
  cases Obs.«IxonSerialize::put_constant_info».obs ev with
  | Defn _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Recr _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Axio _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Quot _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | CPrj _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | RPrj _ _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | IPrj _ _ _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | DPrj x_prj _ _ _ _ _ _ _ _ hv260 ev272 _ =>
    injection hv260 with _ _ hx
    injection hx with hx _
    subst hx
    rcases Obs.«IxonSerialize::put_definition_proj».obs ev272 with
      ⟨x_idx, x_block, _, v34, m43, _, hv15, ev53, ev32, -⟩
    injection hv15 with _ _ hargs
    injection hargs with ha1 hargs; subst ha1
    injection hargs with ha2 _; subst ha2
    have s1 := put_address_spec hb ev53 hrest
    have s2 := put_tagn0_spec hvi ev32 s1
    rw [hblk] at s2
    simpa [definitionProjBytes, List.append_assoc]
      using s2

theorem putAddress_writes (a : Address) :
    Writes (Ixon.Serialize.put a) a.hash :=
  putBytes_writes a.hash

theorem arrayPut_empty_writes {α : Type} (putm : α → Ixon.PutM Unit) :
    Writes (do for value in (#[] : Array α) do putm value) ByteArray.empty := by
  have heq : (do for value in (#[] : Array α) do putm value) = (pure () : Ixon.PutM Unit) := by
    rw [← Array.forIn_toList]
    simp
  rw [heq]
  exact Writes.pure

theorem putBinders_empty_writes :
    Writes (Ixon.putBinders #[]) (tag0Bytes 0) := by
  simpa [Ixon.putBinders, tag0Bytes] using
    (putTagN_writes 0 0 0).bind (arrayPut_empty_writes Ixon.putBinderBlock)

theorem serConstant_empty_tables_eq {info : Ixon.ConstantInfo} {binfo : ByteArray}
    (hinfo : Writes (Ixon.putConstantInfo info) binfo) :
    (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩).data.toList =
      binfo.data.toList ++
        (tag0Bytes 0).data.toList ++
        (tag0Bytes 0).data.toList ++
        (tag0Bytes 0).data.toList ++
        (tag0Bytes 0).data.toList := by
  have hwrite : Writes (Ixon.putConstant ⟨info, #[], #[], #[], #[]⟩)
      (binfo ++ tag0Bytes 0 ++ tag0Bytes 0 ++ tag0Bytes 0 ++ tag0Bytes 0) := by
    simpa [Ixon.putConstant, tag0Bytes, ByteArray.append_assoc] using
      hinfo.bind
        ((putTagN_writes 0 0 0).bind
          ((arrayPut_empty_writes Ixon.putExpr).bind
            ((putTagN_writes 0 0 0).bind
              ((arrayPut_empty_writes (Ixon.Serialize.put (α := Address))).bind
                ((putTagN_writes 0 0 0).bind
                  ((arrayPut_empty_writes Ixon.putUniv).bind
                    putBinders_empty_writes))))))
  unfold Ixon.serConstant
  rw [hwrite.runPut]
  simp [List.append_assoc]

theorem putConstantInfo_cPrj_writes (p : Ixon.ConstructorProj) :
    Writes (Ixon.putConstantInfo (.cPrj p))
      (tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_CPRJ ++
        constructorProjBytes p) := by
  have hp : Writes (Ixon.putConstructorProj p) (constructorProjBytes p) := by
    simpa [Ixon.putConstructorProj, constructorProjBytes, tag0Bytes, ByteArray.append_assoc]
      using (putTagN_writes 0 0 p.idx).bind
        ((putTagN_writes 0 0 p.cidx).bind (putAddress_writes p.block))
  simpa [Ixon.putConstantInfo, tag4Bytes, seqRight_eq_bind] using
    (putTagN_writes 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_CPRJ).bind hp

theorem putConstantInfo_rPrj_writes (p : Ixon.RecursorProj) :
    Writes (Ixon.putConstantInfo (.rPrj p))
      (tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_RPRJ ++
        recursorProjBytes p) := by
  have hp : Writes (Ixon.putRecursorProj p) (recursorProjBytes p) := by
    simpa [Ixon.putRecursorProj, recursorProjBytes, tag0Bytes]
      using (putTagN_writes 0 0 p.idx).bind (putAddress_writes p.block)
  simpa [Ixon.putConstantInfo, tag4Bytes, seqRight_eq_bind] using
    (putTagN_writes 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_RPRJ).bind hp

theorem putConstantInfo_iPrj_writes (p : Ixon.InductiveProj) :
    Writes (Ixon.putConstantInfo (.iPrj p))
      (tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ ++
        inductiveProjBytes p) := by
  have hp : Writes (Ixon.putInductiveProj p) (inductiveProjBytes p) := by
    simpa [Ixon.putInductiveProj, inductiveProjBytes, tag0Bytes]
      using (putTagN_writes 0 0 p.idx).bind (putAddress_writes p.block)
  simpa [Ixon.putConstantInfo, tag4Bytes, seqRight_eq_bind] using
    (putTagN_writes 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ).bind hp

theorem putConstantInfo_dPrj_writes (p : Ixon.DefinitionProj) :
    Writes (Ixon.putConstantInfo (.dPrj p))
      (tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_DPRJ ++
        definitionProjBytes p) := by
  have hp : Writes (Ixon.putDefinitionProj p) (definitionProjBytes p) := by
    simpa [Ixon.putDefinitionProj, definitionProjBytes, tag0Bytes]
      using (putTagN_writes 0 0 p.idx).bind (putAddress_writes p.block)
  simpa [Ixon.putConstantInfo, tag4Bytes, seqRight_eq_bind] using
    (putTagN_writes 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_DPRJ).bind hp

theorem put_empty_tables_spec
    {x_sh x_rf x_un x_bd x_rest v99 v78 v57 v42 : SourceValue F}
    {h m108 m87 m66 m43 : Heap F} {c1 c2 c3 c4 : List (Call F)} {rest : List UInt8}
    (hp1 : RepList Specs.Callees.ixExprListEnum (fun _ (_ : Unit) _ => True) h [] x_sh)
    (hp2 : RepList addrListEnum (fun _ (_ : Unit) _ => True) h [] x_rf)
    (hp3 : RepList Specs.Callees.ixUnivListEnum (fun _ (_ : Unit) _ => True) h [] x_un)
    (hp4 : RepList Specs.Callees.ixBinderListEnum (fun _ (_ : Unit) _ => True) h [] x_bd)
    (ev_bd : ObsFn W "IxonSerialize::put_binders" [x_bd, x_rest] h v99 m108 c1)
    (ev_un : ObsFn W "IxonSerialize::put_univs" [x_un, v99] m108 v78 m87 c2)
    (ev_rf : ObsFn W "IxonSerialize::put_refs" [x_rf, v78] m87 v57 m66 c3)
    (ev_sh : ObsFn W "IxonSerialize::put_sharing" [x_sh, v57] m66 v42 m43 c4)
    (hrest : RepBytes h rest x_rest) :
    Heap.Extends h m43 ∧
      RepBytes m43
        ((tag0Bytes 0).data.toList ++
          (tag0Bytes 0).data.toList ++
          (tag0Bytes 0).data.toList ++
          (tag0Bytes 0).data.toList ++ rest) v42 := by
  have e1 := ev_bd.heap_extends
  have e2 := ev_un.heap_extends
  have e3 := ev_rf.heap_extends
  have e4 := ev_sh.heap_extends
  have s_bd := put_binders_nil_spec hp4 ev_bd hrest
  have s_un := put_univs_nil_spec (RepLinkedList.mono (fun _ _ _ _ _ hx => hx) e1 hp3) ev_un s_bd
  have s_rf := put_refs_nil_spec
    (RepLinkedList.mono (fun _ _ _ _ _ hx => hx) (e1.trans e2) hp2) ev_rf s_un
  have s_sh := put_sharing_nil_spec
    (RepLinkedList.mono (fun _ _ _ _ _ hx => hx) (e1.trans (e2.trans e3)) hp1) ev_sh s_rf
  refine ⟨e1.trans (e2.trans (e3.trans e4)), ?_⟩
  simpa [List.append_assoc] using s_sh

theorem projInfoRep_not_nonproj {h : Heap F} {info : Ixon.ConstantInfo} {cn : String}
    {w : SourceValue F} (hcn : cn ≠ "CPrj" ∧ cn ≠ "IPrj" ∧ cn ≠ "RPrj" ∧ cn ≠ "DPrj")
    (hi : Specs.Callees.ProjInfoRep h info (.construct "Ixon::ConstantInfo" cn [w])) : False := by
  cases info <;> simp only [Specs.Callees.ProjInfoRep] at hi
  · rcases hi with ⟨_, _, _, _, he, -⟩; injection he with _ hc _; exact hcn.1 hc
  · rcases hi with ⟨_, _, _, he, -⟩; injection he with _ hc _; exact hcn.2.2.1 hc
  · rcases hi with ⟨_, _, _, he, -⟩; injection he with _ hc _; exact hcn.2.1 hc
  · rcases hi with ⟨_, _, _, he, -⟩; injection he with _ hc _; exact hcn.2.2.2 hc

end ProjAddrAux

/-- `IxonSerialize::put_constant`: serializes a projection record with empty side tables
(`ProjConstRep`) in front of `rest`. -/
theorem put_constant_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "IxonSerialize::put_constant" args h r h' calls) :
    Specs.Callees.put_constant c args h r h' calls := by
  intro cv tl info rest hargs hcv hrest
  subst hargs
  rcases hcv with ⟨iv, p1, p2, p3, p4, rfl, hinfo, hp1, hp2, hp3, hp4⟩
  match Obs.«IxonSerialize::put_constant».obs ev with
  | .Muts (hv15 := hv) .. | .Defn (hv15 := hv) .. | .Recr (hv15 := hv) ..
  | .Axio (hv15 := hv) .. | .Quot (hv15 := hv) .. =>
    injection hv with _ _ hm; injection hm with hi _
    subst hi
    exact (ProjAddrAux.projInfoRep_not_nonproj (by decide) hinfo).elim
  | .CPrj (hv15 := hv) (ev118 := ev118) (ev97 := ev97) (ev76 := ev76) (ev55 := ev55)
      (ev760 := ev760) (ev675 := ev675) .. =>
    injection hv with _ _ hm; injection hm with hi hm
    injection hm with hm1 hm; subst hm1
    injection hm with hm2 hm; subst hm2
    injection hm with hm3 hm; subst hm3
    injection hm with hm4 _; subst hm4
    subst hi
    cases info with
    | cPrj p =>
      rcases hinfo with ⟨vi, vj, bp, b, he, hvi, hvj, hb, hblk⟩
      injection he with _ _ hw; injection hw with hw _; subst hw
      obtain ⟨etab, stab⟩ :=
        ProjAddrAux.put_empty_tables_spec hp1 hp2 hp3 hp4 ev118 ev97 ev76 ev55 hrest
      have sinfo := ProjAddrAux.put_cprj_info_spec
        (ProjAddrAux.repU64_mono etab hvi) (ProjAddrAux.repU64_mono etab hvj)
        (Bytes.repAddressRef_heapMono₂ addrTy etab hb) hblk ev760 stab
      have stag := ProjAddrAux.put_tagn4_const_small (k := 4) (by omega) ev675 sinfo
      rw [ProjAddrAux.serConstant_empty_tables_eq (ProjAddrAux.putConstantInfo_cPrj_writes p)]
      simpa [Ixon.ConstantInfo.CONST_CPRJ, List.append_assoc] using stag
    | rPrj _ | iPrj _ | dPrj _ =>
      rcases hinfo with ⟨_, _, _, he, -⟩; injection he with _ hc _; exact absurd hc (by decide)
    | defn _ | recr _ | axio _ | quot _ | muts _ => exact hinfo.elim
  | .RPrj (hv15 := hv) (ev118 := ev118) (ev97 := ev97) (ev76 := ev76) (ev55 := ev55)
      (ev881 := ev881) (ev796 := ev796) .. =>
    injection hv with _ _ hm; injection hm with hi hm
    injection hm with hm1 hm; subst hm1
    injection hm with hm2 hm; subst hm2
    injection hm with hm3 hm; subst hm3
    injection hm with hm4 _; subst hm4
    subst hi
    cases info with
    | rPrj p =>
      rcases hinfo with ⟨vi, bp, b, he, hvi, hb, hblk⟩
      injection he with _ _ hw; injection hw with hw _; subst hw
      obtain ⟨etab, stab⟩ :=
        ProjAddrAux.put_empty_tables_spec hp1 hp2 hp3 hp4 ev118 ev97 ev76 ev55 hrest
      have sinfo := ProjAddrAux.put_rprj_info_spec
        (ProjAddrAux.repU64_mono etab hvi)
        (Bytes.repAddressRef_heapMono₂ addrTy etab hb) hblk ev881 stab
      have stag := ProjAddrAux.put_tagn4_const_small (k := 5) (by omega) ev796 sinfo
      rw [ProjAddrAux.serConstant_empty_tables_eq (ProjAddrAux.putConstantInfo_rPrj_writes p)]
      simpa [Ixon.ConstantInfo.CONST_RPRJ, List.append_assoc] using stag
    | cPrj _ =>
      rcases hinfo with ⟨_, _, _, _, he, -⟩; injection he with _ hc _; exact absurd hc (by decide)
    | iPrj _ | dPrj _ =>
      rcases hinfo with ⟨_, _, _, he, -⟩; injection he with _ hc _; exact absurd hc (by decide)
    | defn _ | recr _ | axio _ | quot _ | muts _ => exact hinfo.elim
  | .IPrj (hv15 := hv) (ev118 := ev118) (ev97 := ev97) (ev76 := ev76) (ev55 := ev55)
      (ev1002 := ev1002) (ev917 := ev917) .. =>
    injection hv with _ _ hm; injection hm with hi hm
    injection hm with hm1 hm; subst hm1
    injection hm with hm2 hm; subst hm2
    injection hm with hm3 hm; subst hm3
    injection hm with hm4 _; subst hm4
    subst hi
    cases info with
    | iPrj p =>
      rcases hinfo with ⟨vi, bp, b, he, hvi, hb, hblk⟩
      injection he with _ _ hw; injection hw with hw _; subst hw
      obtain ⟨etab, stab⟩ :=
        ProjAddrAux.put_empty_tables_spec hp1 hp2 hp3 hp4 ev118 ev97 ev76 ev55 hrest
      have sinfo := ProjAddrAux.put_iprj_info_spec
        (ProjAddrAux.repU64_mono etab hvi)
        (Bytes.repAddressRef_heapMono₂ addrTy etab hb) hblk ev1002 stab
      have stag := ProjAddrAux.put_tagn4_const_small (k := 6) (by omega) ev917 sinfo
      rw [ProjAddrAux.serConstant_empty_tables_eq (ProjAddrAux.putConstantInfo_iPrj_writes p)]
      simpa [Ixon.ConstantInfo.CONST_IPRJ, List.append_assoc] using stag
    | cPrj _ =>
      rcases hinfo with ⟨_, _, _, _, he, -⟩; injection he with _ hc _; exact absurd hc (by decide)
    | rPrj _ | dPrj _ =>
      rcases hinfo with ⟨_, _, _, he, -⟩; injection he with _ hc _; exact absurd hc (by decide)
    | defn _ | recr _ | axio _ | quot _ | muts _ => exact hinfo.elim
  | .DPrj (hv15 := hv) (ev118 := ev118) (ev97 := ev97) (ev76 := ev76) (ev55 := ev55)
      (ev1123 := ev1123) (ev1038 := ev1038) .. =>
    injection hv with _ _ hm; injection hm with hi hm
    injection hm with hm1 hm; subst hm1
    injection hm with hm2 hm; subst hm2
    injection hm with hm3 hm; subst hm3
    injection hm with hm4 _; subst hm4
    subst hi
    cases info with
    | dPrj p =>
      rcases hinfo with ⟨vi, bp, b, he, hvi, hb, hblk⟩
      injection he with _ _ hw; injection hw with hw _; subst hw
      obtain ⟨etab, stab⟩ :=
        ProjAddrAux.put_empty_tables_spec hp1 hp2 hp3 hp4 ev118 ev97 ev76 ev55 hrest
      have sinfo := ProjAddrAux.put_dprj_info_spec
        (ProjAddrAux.repU64_mono etab hvi)
        (Bytes.repAddressRef_heapMono₂ addrTy etab hb) hblk ev1123 stab
      have stag := ProjAddrAux.put_tagn4_const_small (k := 7) (by omega) ev1038 sinfo
      rw [ProjAddrAux.serConstant_empty_tables_eq (ProjAddrAux.putConstantInfo_dPrj_writes p)]
      simpa [Ixon.ConstantInfo.CONST_DPRJ, List.append_assoc] using stag
    | cPrj _ =>
      rcases hinfo with ⟨_, _, _, _, he, -⟩; injection he with _ hc _; exact absurd hc (by decide)
    | rPrj _ | iPrj _ =>
      rcases hinfo with ⟨_, _, _, he, -⟩; injection he with _ hc _; exact absurd hc (by decide)
    | defn _ | recr _ | axio _ | quot _ | muts _ => exact hinfo.elim

end IxVM.Refinement.Core
