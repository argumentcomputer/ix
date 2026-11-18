import IxVMRefinement.Guard.ClassifierKeys
import IxVMRefinement.Guard.CtorRaw
import Ix.IxVM.Consistency.TableValid
import Ix.IxVM.Consistency.ReadsKeys
import Ix.CompileCert.Loop

/-! # What the raw dictionary reads at a block, and the records reachable from it

The classifier's raw dictionary (`GuardRaw.ofStore`) reads the constructor telescope from the
block record, a declared type or a definition value from the record at the queried address, and
for a projection record from its block. The kernel reader turns a `ref i` node of a record into
the address key of `refs[i]` and a `recur k` node into the key of the record itself (a standalone
record) or of member `k`'s projection record (a block). So every key in an answer is a used
constant reference of a record the dictionary read, the record's own address, or a member's
address of a block it read.

* `convExpr_keysIn`, `memberReader_read_keysIn`, `readRoot_keysIn`: the keys of a reading.
* `BlockReach E B`: the addresses reachable from `B` in `E` by used constant references
  (`usedRefIdxs`), the block of a projection record (`Ix.Cert.ownerOf`) and the projection
  record of a block's member (`memberAddr`).
* `reachStore E B`: the records of `E` at the addresses reachable from `B`, with every blob of
  `E`.
* `keysKept_reachStore`: the dictionary of `reachStore E B` keeps the answers of `E`'s at the
  reachable addresses, and those answers name only reachable addresses.
* `ctorRaw_reachStore`, `ctorRaw_keysIn`: the constructor telescope at `B` is the same over the
  reach store and names only reachable addresses.
-/

namespace IxVM.Refinement.Guard

open IxVM.Consistency
open Ix.Kernel (Expr Key Level)
open Ix.CompileCert.Loop (except_bind_ok)

/-- The address keys of the addresses of `S`. -/
def AddrKeys (S : _root_.Address → Prop) : Key .anon → Prop :=
  fun k => ∃ x, k = .id x ∧ S x

/-! ## The keys of a reading -/

section Reader

open Ix.Kernel.Reader (ECx convExpr MemberReader ReadM CExpr Ctx convUniv)

/-- **A converted expression names only the keys its references and recursive references
read as**, given that the sharing entries before it do. -/
theorem convExpr_keysIn {md : Ix.Kernel.Mode} {ecx : ECx md} {tbl : Array (ReadM (CExpr md))}
    {P : Key md → Prop} {I : Nat → Prop}
    (hkey : ∀ i : UInt64, I i.toNat → ∀ k, ecx.keyAt i = .ok k → P k)
    (hself : ∀ j m k, ecx.self j = some m → m = .ok k → P k)
    (htbl : ∀ m ∈ tbl.toList, ∀ v, m = .ok v → KeysIn P v) :
    ∀ (ie : Ixon.Expr), (∀ i ∈ exprRefIdxs ie, I i) → ∀ {v : CExpr md},
      convExpr ecx tbl ie = .ok v → KeysIn P v
  | .var i, _, v, h => by
    simp only [convExpr, pure, Except.pure, Except.ok.injEq] at h
    subst v
    rw [Expr.mkBvar_eq]
    trivial
  | .sort i, _, v, h => by
    simp only [convExpr] at h
    obtain ⟨l, _, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst v
    trivial
  | .ref i us, hI, v, h => by
    simp only [convExpr] at h
    obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
    obtain ⟨ls, _, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst v
    exact hkey i (hI i.toNat (List.mem_singleton.mpr rfl)) k hk
  | .recur i us, _, v, h => by
    simp only [convExpr] at h
    cases hs : ecx.self i.toNat with
    | none =>
      simp [hs, Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some m =>
      simp only [hs] at h
      obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
      obtain ⟨ls, _, h⟩ := except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst v
      exact hself _ m k hs hk
  | .prj i field x, hI, v, h => by
    simp only [convExpr] at h
    obtain ⟨k, _, h⟩ := except_bind_ok.mp h
    obtain ⟨ev, hv, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst v
    exact convExpr_keysIn hkey hself htbl x (fun j hj => hI j (List.mem_cons_of_mem _ hj)) hv
  | .str i, _, v, h => by
    simp only [convExpr] at h
    obtain ⟨bytes, _, h⟩ := except_bind_ok.mp h
    cases hs : String.fromUTF8? bytes with
    | none =>
      simp [hs, Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some s =>
      simp only [hs, pure, Except.pure, Except.ok.injEq] at h
      subst v
      trivial
  | .nat i, _, v, h => by
    simp only [convExpr] at h
    obtain ⟨n, _, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst v
    trivial
  | .app f a, hI, v, h => by
    simp only [convExpr] at h
    obtain ⟨ef, hf, h⟩ := except_bind_ok.mp h
    obtain ⟨ea, ha, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst v
    exact ⟨convExpr_keysIn hkey hself htbl f (fun j hj => hI j (List.mem_append_left _ hj)) hf,
      convExpr_keysIn hkey hself htbl a (fun j hj => hI j (List.mem_append_right _ hj)) ha⟩
  | .lam t b, hI, v, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst v
    exact ⟨convExpr_keysIn hkey hself htbl t (fun j hj => hI j (List.mem_append_left _ hj)) ht,
      convExpr_keysIn hkey hself htbl b (fun j hj => hI j (List.mem_append_right _ hj)) hb⟩
  | .all t b, hI, v, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst v
    exact ⟨convExpr_keysIn hkey hself htbl t (fun j hj => hI j (List.mem_append_left _ hj)) ht,
      convExpr_keysIn hkey hself htbl b (fun j hj => hI j (List.mem_append_right _ hj)) hb⟩
  | .letE nonDep kind t x b, hI, v, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨ex, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst v
    exact ⟨convExpr_keysIn hkey hself htbl t
        (fun j hj => hI j (List.mem_append_left _ (List.mem_append_left _ hj))) ht,
      convExpr_keysIn hkey hself htbl x
        (fun j hj => hI j (List.mem_append_left _ (List.mem_append_right _ hj))) hx,
      convExpr_keysIn hkey hself htbl b (fun j hj => hI j (List.mem_append_right _ hj)) hb⟩
  | .share i, _, v, h => by
    simp only [convExpr] at h
    cases hget : tbl[i.toNat]? with
    | none =>
      simp [hget, Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some r =>
      simp only [hget] at h
      exact htbl r (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget)) v h

/-- The constant references of a record's sharing entries are used references. -/
theorem sharing_usedRefIdxs (src : Ixon.Constant) :
    ∀ entry ∈ src.sharing.toList, ∀ i ∈ exprRefIdxs entry, i ∈ usedRefIdxs src :=
  fun entry hen _ hi => List.mem_append_left _ (List.mem_flatMap.mpr ⟨entry, hen, hi⟩)

/-- **A record's expression, read by the kernel reader, names only the keys its used references
and its recursive references read as.** -/
theorem memberReader_read_keysIn {cx : Ctx .anon} {src : Ixon.Constant}
    {param : Nat → Ix.Kernel.LevelParam} {self : Nat → Option (ReadM (Key .anon))}
    {P : Key .anon → Prop}
    (hkey : ∀ i ∈ usedRefIdxs src, ∀ x, src.refs[i]? = some x → ∀ k, cx.keyAt x = .ok k → P k)
    (hself : ∀ j m k, self j = some m → m = .ok k → P k)
    {ie : Ixon.Expr} (hI : ∀ i ∈ exprRefIdxs ie, i ∈ usedRefIdxs src) {v : Expr .anon}
    (h : (MemberReader.mk' cx src param self).read ie = .ok v) : KeysIn P v := by
  let ecx : ECx .anon := ⟨cx, src, src.univs.map (convUniv param), self⟩
  have hkey' : ∀ i : UInt64, i.toNat ∈ usedRefIdxs src → ∀ k, ecx.keyAt i = .ok k → P k := by
    intro i hi k hk
    cases hx : src.refs[i.toNat]? with
    | none =>
      simp [ecx, ECx.keyAt, hx, Ix.Kernel.Reader.malformed, throw, throwThe,
        MonadExceptOf.throw] at hk
    | some x =>
      simp only [ecx, ECx.keyAt, hx] at hk
      exact hkey i.toNat hi x hx k hk
  have htbl_fold :
      ∀ (entries : List Ixon.Expr) (tbl : Array (ReadM (CExpr .anon))),
        (∀ entry ∈ entries, ∀ i ∈ exprRefIdxs entry, i ∈ usedRefIdxs src) →
        (∀ m ∈ tbl.toList, ∀ e', m = .ok e' → KeysIn P e') →
        ∀ m ∈ (entries.foldl (fun acc entry => acc.push (convExpr ecx acc entry)) tbl).toList,
          ∀ e', m = .ok e' → KeysIn P e' := by
    intro entries
    induction entries with
    | nil => intro tbl _ hT; exact hT
    | cons entry rest ih =>
      intro tbl hE hT
      refine ih (tbl.push (convExpr ecx tbl entry))
        (fun en hen => hE en (List.mem_cons_of_mem _ hen)) fun m hm e' he' => ?_
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hT m hm e' he'
      · exact convExpr_keysIn (I := fun i => i ∈ usedRefIdxs src) hkey' hself hT entry
          (hE entry (List.mem_cons.mpr (Or.inl rfl))) he'
  have hmk :
      (MemberReader.mk' cx src param self).ecx = ecx ∧
      (MemberReader.mk' cx src param self).tbl =
        src.sharing.toList.foldl (fun acc entry => acc.push (convExpr ecx acc entry)) #[] := by
    simp [MemberReader.mk', ecx, Array.forIn_pure_yield_eq_foldl, Array.mkEmpty,
      ← Array.foldl_toList]
  unfold MemberReader.read at h
  rw [hmk.1, hmk.2] at h
  exact convExpr_keysIn (I := fun i => i ∈ usedRefIdxs src) hkey' hself
    (htbl_fold src.sharing.toList #[] (sharing_usedRefIdxs src) (fun _ hm => nomatch hm)) ie hI h

end Reader

/-- **A dictionary root's reading names only address keys of `S`**, when the record's used
references and its recursive references are in `S` and the root's expression is one whose
constant references are used. -/
theorem readRoot_keysIn {blob : GuardRaw.Blobs} {root : GuardRaw.Root} {e : Expr .anon}
    {S : _root_.Address → Prop}
    (hrefs : ∀ i ∈ usedRefIdxs root.source, ∀ x, root.source.refs[i]? = some x → S x)
    (hself : ∀ j m k, root.self j = some m → m = .ok k → AddrKeys S k)
    (hexpr : ∀ i ∈ exprRefIdxs root.expression, i ∈ usedRefIdxs root.source)
    (h : GuardRaw.readRoot blob root = some e) : KeysIn (AddrKeys S) e := by
  unfold GuardRaw.readRoot at h
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
  apply KeysIn.eraseMeta
  refine memberReader_read_keysIn (cx := readCtx GuardRaw.addressTable blob) ?_ hself hexpr
    (Typing.toOption_eq_some hv)
  intro i hi x hx k hk
  rw [readCtx_keyAt GuardRaw.addressTable_check blob x] at hk
  have hk' : keyOf GuardRaw.addressTable x = k := Except.ok.inj hk
  exact ⟨x, hk'.symm.trans (GuardRaw.addressTable_key x), hrefs i hi x hx⟩

/-! ## The addresses reachable from a block -/

/-- **The addresses reachable from `B` in `E`**: `B`, every used constant reference of a
reachable record, the block of a reachable projection record, and the projection record's
address of every member of a reachable block. -/
inductive BlockReach (E : Ixon.Env) (B : _root_.Address) : _root_.Address → Prop
  | seed : BlockReach E B B
  | used {a x : _root_.Address} {c : Ixon.Constant} {i : Nat} : BlockReach E B a →
      recordOf E a = some c → i ∈ usedRefIdxs c → c.refs[i]? = some x → BlockReach E B x
  | owner {a : _root_.Address} {c : Ixon.Constant} : BlockReach E B a →
      recordOf E a = some c → BlockReach E B (Ix.Cert.ownerOf a c)
  | member {a : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst} {i : Nat}
      {m : Ixon.MutConst} : BlockReach E B a → recordOf E a = some c → c.info = .muts ms →
      ms[i]? = some m → BlockReach E B (memberAddr a i m)

/-- A member selector whose expression's constant references are the member's. -/
def SelectsUsed (sel : Ixon.MutConst → Option (Nat × Nat × Ixon.Expr)) : Prop :=
  ∀ m off nl e, sel m = some (off, nl, e) → ∀ i ∈ exprRefIdxs e, i ∈ mutRefIdxs m

theorem selectsUsed_definitionType : SelectsUsed GuardRaw.definitionType := by
  intro m off nl e h i hi
  cases m
  case defn d =>
    simp only [GuardRaw.definitionType, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact List.mem_append_left _ hi
  all_goals simp [GuardRaw.definitionType] at h

theorem selectsUsed_definitionValue : SelectsUsed GuardRaw.definitionValue := by
  intro m off nl e h i hi
  cases m
  case defn d =>
    simp only [GuardRaw.definitionValue] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact List.mem_append_right _ hi
    · simp at h
  all_goals simp [GuardRaw.definitionValue] at h

theorem selectsUsed_inductiveType : SelectsUsed GuardRaw.inductiveType := by
  intro m off nl e h i hi
  cases m
  case indc ind =>
    simp only [GuardRaw.inductiveType, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact List.mem_append_left _ hi
  all_goals simp [GuardRaw.inductiveType] at h

theorem selectsUsed_recursorType : SelectsUsed GuardRaw.recursorType := by
  intro m off nl e h i hi
  cases m
  case recr rc =>
    simp only [GuardRaw.recursorType, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact List.mem_append_left _ hi
  all_goals simp [GuardRaw.recursorType] at h

theorem selectsUsed_constructorType (j : Nat) : SelectsUsed (GuardRaw.constructorType j) := by
  intro m off nl e h i hi
  cases m
  case indc ind =>
    simp only [GuardRaw.constructorType] at h
    obtain ⟨ct, hct, heq⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, -, rfl⟩ := heq
    exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨ct, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hct), hi⟩)
  all_goals simp [GuardRaw.constructorType] at h

/-- A member's constant references are its block record's used references. -/
theorem mutRefIdxs_used {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hinfo : cb.info = .muts ms) {i : Nat} {m : Ixon.MutConst} (hm : ms[i]? = some m)
    {k : Nat} (hk : k ∈ mutRefIdxs m) : k ∈ usedRefIdxs cb := by
  unfold usedRefIdxs
  rw [hinfo]
  exact List.mem_append_right _
    (List.mem_flatMap.mpr ⟨m, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm), hk⟩)

/-- **A member root of a reachable block reads as reachable keys only.** -/
theorem memberRoot_keysIn {E : Ixon.Env} {B Bk : _root_.Address} (hreach : BlockReach E B Bk)
    {i : Nat} {sel : Ixon.MutConst → Option (Nat × Nat × Ixon.Expr)} (hsel : SelectsUsed sel)
    {root : GuardRaw.Root} (hroot : GuardRaw.memberRoot (recordOf E) Bk i sel = some root)
    {blob : GuardRaw.Blobs} {e : Expr .anon} (h : GuardRaw.readRoot blob root = some e) :
    KeysIn (AddrKeys (BlockReach E B)) e := by
  cases hcb : recordOf E Bk with
  | none => simp [GuardRaw.memberRoot, hcb] at hroot
  | some cb =>
    cases hinfo : cb.info
    case muts ms =>
      cases hm : ms[i]? with
      | none => simp [GuardRaw.memberRoot, hcb, hinfo, hm] at hroot
      | some m =>
        cases hs : sel m with
        | none => simp [GuardRaw.memberRoot, hcb, hinfo, hm, hs] at hroot
        | some y =>
          obtain ⟨off, nl, ex⟩ := y
          simp [GuardRaw.memberRoot, hcb, hinfo, hm, hs] at hroot
          subst hroot
          refine readRoot_keysIn (fun k hk x hx => BlockReach.used hreach hcb hk hx) ?_
            (fun k hk => mutRefIdxs_used hinfo hm (hsel m off nl ex hs k hk)) h
          intro j mm key hj hkey
          simp only [blockSelf] at hj
          obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.mp hj
          have hk' : keyOf GuardRaw.addressTable (memberAddr Bk j m') = key := Except.ok.inj hkey
          exact ⟨memberAddr Bk j m', hk'.symm.trans (GuardRaw.addressTable_key _),
            BlockReach.member hreach hcb hinfo hm'⟩
    all_goals simp [GuardRaw.memberRoot, hcb, hinfo] at hroot

/-- The recursive reference of a standalone record reads as its own address. -/
theorem soloSelf_keysIn {S : _root_.Address → Prop} {a : _root_.Address} (ha : S a) :
    ∀ j m k, soloSelf GuardRaw.addressTable a j = some m → m = .ok k → AddrKeys S k := by
  intro j m k hj hk
  simp only [soloSelf] at hj
  split at hj
  · obtain rfl := Option.some.inj hj
    have hk' : keyOf GuardRaw.addressTable a = k := Except.ok.inj hk
    exact ⟨a, hk'.symm.trans (GuardRaw.addressTable_key a), ha⟩
  · simp at hj

/-- **A declared type the dictionary reads at a reachable address names only reachable keys.** -/
theorem typeRoot_keysIn {E : Ixon.Env} {B a : _root_.Address} (hreach : BlockReach E B a)
    {root : GuardRaw.Root} (hroot : GuardRaw.typeRoot (recordOf E) a = some root)
    {blob : GuardRaw.Blobs} {e : Expr .anon} (h : GuardRaw.readRoot blob root = some e) :
    KeysIn (AddrKeys (BlockReach E B)) e := by
  cases hc : recordOf E a with
  | none => simp [GuardRaw.typeRoot, hc] at hroot
  | some c =>
    have hrefs : ∀ i ∈ usedRefIdxs c, ∀ x, c.refs[i]? = some x → BlockReach E B x :=
      fun i hi x hx => BlockReach.used hreach hc hi hx
    have hown : BlockReach E B (Ix.Cert.ownerOf a c) := BlockReach.owner hreach hc
    cases hinfo : c.info
    case defn d =>
      simp [GuardRaw.typeRoot, hc, hinfo] at hroot
      subst hroot
      refine readRoot_keysIn hrefs (soloSelf_keysIn hreach) ?_ h
      intro k hk
      unfold usedRefIdxs
      rw [hinfo]
      exact List.mem_append_right _ (List.mem_append_left _ hk)
    case recr r =>
      simp [GuardRaw.typeRoot, hc, hinfo] at hroot
      subst hroot
      refine readRoot_keysIn hrefs (soloSelf_keysIn hreach) ?_ h
      intro k hk
      unfold usedRefIdxs
      rw [hinfo]
      exact List.mem_append_right _ (List.mem_append_left _ hk)
    case axio x =>
      simp [GuardRaw.typeRoot, hc, hinfo] at hroot
      subst hroot
      refine readRoot_keysIn hrefs (fun _ _ _ hj => by simp at hj) ?_ h
      intro k hk
      unfold usedRefIdxs
      rw [hinfo]
      exact List.mem_append_right _ hk
    case quot q =>
      simp [GuardRaw.typeRoot, hc, hinfo] at hroot
      subst hroot
      refine readRoot_keysIn hrefs (fun _ _ _ hj => by simp at hj) ?_ h
      intro k hk
      unfold usedRefIdxs
      rw [hinfo]
      exact List.mem_append_right _ hk
    case dPrj p =>
      simp [GuardRaw.typeRoot, hc, hinfo] at hroot
      have hb : BlockReach E B p.block := by simpa [Ix.Cert.ownerOf, hinfo] using hown
      exact memberRoot_keysIn hb selectsUsed_definitionType hroot h
    case iPrj p =>
      simp [GuardRaw.typeRoot, hc, hinfo] at hroot
      have hb : BlockReach E B p.block := by simpa [Ix.Cert.ownerOf, hinfo] using hown
      exact memberRoot_keysIn hb selectsUsed_inductiveType hroot h
    case rPrj p =>
      simp [GuardRaw.typeRoot, hc, hinfo] at hroot
      have hb : BlockReach E B p.block := by simpa [Ix.Cert.ownerOf, hinfo] using hown
      exact memberRoot_keysIn hb selectsUsed_recursorType hroot h
    case cPrj p =>
      simp [GuardRaw.typeRoot, hc, hinfo] at hroot
      have hb : BlockReach E B p.block := by simpa [Ix.Cert.ownerOf, hinfo] using hown
      exact memberRoot_keysIn hb (selectsUsed_constructorType _) hroot h
    case muts ms => simp [GuardRaw.typeRoot, hc, hinfo] at hroot

/-- **A definition value the dictionary reads at a reachable address names only reachable
keys.** -/
theorem valueRoot_keysIn {E : Ixon.Env} {B a : _root_.Address} (hreach : BlockReach E B a)
    {root : GuardRaw.Root} (hroot : GuardRaw.valueRoot (recordOf E) a = some root)
    {blob : GuardRaw.Blobs} {e : Expr .anon} (h : GuardRaw.readRoot blob root = some e) :
    KeysIn (AddrKeys (BlockReach E B)) e := by
  cases hc : recordOf E a with
  | none => simp [GuardRaw.valueRoot, hc] at hroot
  | some c =>
    have hrefs : ∀ i ∈ usedRefIdxs c, ∀ x, c.refs[i]? = some x → BlockReach E B x :=
      fun i hi x hx => BlockReach.used hreach hc hi hx
    have hown : BlockReach E B (Ix.Cert.ownerOf a c) := BlockReach.owner hreach hc
    cases hinfo : c.info
    case defn d =>
      cases hk : d.kind
      case defn =>
        simp [GuardRaw.valueRoot, hc, hinfo, hk] at hroot
        subst hroot
        refine readRoot_keysIn hrefs (soloSelf_keysIn hreach) ?_ h
        intro k hk'
        unfold usedRefIdxs
        rw [hinfo]
        exact List.mem_append_right _ (List.mem_append_right _ hk')
      all_goals simp [GuardRaw.valueRoot, hc, hinfo, hk] at hroot
    case dPrj p =>
      simp [GuardRaw.valueRoot, hc, hinfo] at hroot
      have hb : BlockReach E B p.block := by simpa [Ix.Cert.ownerOf, hinfo] using hown
      exact memberRoot_keysIn hb selectsUsed_definitionValue hroot h
    all_goals simp [GuardRaw.valueRoot, hc, hinfo] at hroot

/-- A dictionary answer names only the keys its root's reading does. -/
theorem answer_keysIn {blob : GuardRaw.Blobs} {r : Option GuardRaw.Root} {us : List Level}
    {e : Expr .anon} {P : Key .anon → Prop}
    (hr : ∀ root, r = some root → ∀ e₀, GuardRaw.readRoot blob root = some e₀ → KeysIn P e₀)
    (h : GuardRaw.answer blob r us = some e) : KeysIn P e := by
  unfold GuardRaw.answer at h
  obtain ⟨root, hroot, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · obtain ⟨e₀, he₀, rfl⟩ := Option.map_eq_some_iff.mp h
    exact KeysIn.instantiateLevelParams _ _ e₀ (hr root hroot e₀ he₀)
  · simp at h

/-! ## The records reachable from a block -/

/-- **The records of `E` at the addresses reachable from `B`**, with every blob of `E`. -/
noncomputable def reachStore (E : Ixon.Env) (B : _root_.Address) : Ixon.Env :=
  { consts := E.consts.filter fun x _ => @decide (BlockReach E B x) (Classical.propDecidable _)
    blobs := E.blobs }

theorem reachStore_consts {E : Ixon.Env} {B a : _root_.Address} {lc : Ixon.LazyConstant} :
    (reachStore E B).consts.get? a = some lc ↔ BlockReach E B a ∧ E.consts.get? a = some lc := by
  show (E.consts.filter fun x _ => @decide (BlockReach E B x)
    (Classical.propDecidable _)).get? a = some lc ↔ _
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter', Std.HashMap.get?_eq_getElem?]
  cases hE : E.consts[a]? with
  | none => simp
  | some v =>
    by_cases hs : BlockReach E B a
    · simp [Option.filter, hs]
    · simp [Option.filter, hs]

/-- At a reachable address the reach store holds what `E` holds. -/
theorem recordOf_reachStore {E : Ixon.Env} {B a : _root_.Address} (h : BlockReach E B a) :
    recordOf (reachStore E B) a = recordOf E a := by
  unfold recordOf
  cases hE : E.consts.get? a with
  | none =>
    cases hR : (reachStore E B).consts.get? a with
    | none => rfl
    | some lc =>
      have := (reachStore_consts.mp hR).2
      rw [hE] at this
      exact absurd this (by simp)
  | some lc => rw [reachStore_consts.mpr ⟨h, hE⟩]

/-- A record of the reach store is a record of `E` at a reachable address. -/
theorem recordOf_of_reachStore {E : Ixon.Env} {B a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf (reachStore E B) a = some c) : BlockReach E B a ∧ recordOf E a = some c := by
  unfold recordOf at h ⊢
  cases hR : (reachStore E B).consts.get? a with
  | none => rw [hR] at h; simp at h
  | some lc =>
    obtain ⟨hr, hE⟩ := reachStore_consts.mp hR
    rw [hR] at h
    rw [hE]
    exact ⟨hr, h⟩

theorem typeRoot_reachStore {E : Ixon.Env} {B a : _root_.Address} (hreach : BlockReach E B a) :
    GuardRaw.typeRoot (recordOf (reachStore E B)) a = GuardRaw.typeRoot (recordOf E) a := by
  unfold GuardRaw.typeRoot
  rw [recordOf_reachStore hreach]
  cases hc : recordOf E a with
  | none => rfl
  | some c =>
    have hb : recordOf (reachStore E B) (Ix.Cert.ownerOf a c) =
        recordOf E (Ix.Cert.ownerOf a c) :=
      recordOf_reachStore (BlockReach.owner hreach hc)
    cases hinfo : c.info <;> simp [Ix.Cert.ownerOf, hinfo] at hb <;>
      simp [GuardRaw.memberRoot, hinfo, hb]

theorem valueRoot_reachStore {E : Ixon.Env} {B a : _root_.Address} (hreach : BlockReach E B a) :
    GuardRaw.valueRoot (recordOf (reachStore E B)) a = GuardRaw.valueRoot (recordOf E) a := by
  unfold GuardRaw.valueRoot
  rw [recordOf_reachStore hreach]
  cases hc : recordOf E a with
  | none => rfl
  | some c =>
    have hb : recordOf (reachStore E B) (Ix.Cert.ownerOf a c) =
        recordOf E (Ix.Cert.ownerOf a c) :=
      recordOf_reachStore (BlockReach.owner hreach hc)
    cases hinfo : c.info <;> simp [Ix.Cert.ownerOf, hinfo] at hb <;>
      simp [GuardRaw.memberRoot, hinfo, hb]

/-- **The dictionary of the reach store keeps the answers of `E`'s at the reachable addresses,
and those answers name only reachable addresses.** -/
theorem keysKept_reachStore (E : Ixon.Env) (B : _root_.Address) :
    KeysKept (AddrKeys (BlockReach E B)) (GuardRaw.ofStore E)
      (GuardRaw.ofStore (reachStore E B)) where
  typeOf := by
    rintro k us e ⟨x, rfl, hx⟩ h
    refine ⟨?_, answer_keysIn (fun root hroot e₀ he₀ => typeRoot_keysIn hx hroot he₀) h⟩
    change GuardRaw.answer _ (GuardRaw.typeRoot (recordOf (reachStore E B)) x) us = some e
    rw [typeRoot_reachStore hx]
    exact h
  valueOf := by
    rintro k us e ⟨x, rfl, hx⟩ h
    refine ⟨?_, answer_keysIn (fun root hroot e₀ he₀ => valueRoot_keysIn hx hroot he₀) h⟩
    change GuardRaw.answer _ (GuardRaw.valueRoot (recordOf (reachStore E B)) x) us = some e
    rw [valueRoot_reachStore hx]
    exact h

/-- **The constructor telescope at `B` is the same over the reach store.** -/
theorem ctorRaw_reachStore (E : Ixon.Env) (B : _root_.Address) (i j : Nat) :
    Guard.ctorRaw (reachStore E B) B i j = Guard.ctorRaw E B i j := by
  unfold Guard.ctorRaw GuardRaw.memberRoot
  rw [recordOf_reachStore BlockReach.seed]
  rfl

/-- **The constructor telescope at `B` names only addresses reachable from `B`.** -/
theorem ctorRaw_keysIn {E : Ixon.Env} {B : _root_.Address} {i j : Nat} {raw : Expr .anon}
    (h : Guard.ctorRaw E B i j = some raw) : KeysIn (AddrKeys (BlockReach E B)) raw := by
  unfold Guard.ctorRaw at h
  obtain ⟨root, hroot, hread⟩ := Option.bind_eq_some_iff.mp h
  exact memberRoot_keysIn BlockReach.seed (selectsUsed_constructorType j) hroot hread

end IxVM.Refinement.Guard
