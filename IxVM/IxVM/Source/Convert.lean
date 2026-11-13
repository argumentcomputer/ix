import Aiur.Modules.Function

/-! # IxVM module `Convert`

Conversion of Ixon constants to the kernel's constant info.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module Convert where

aiur_decls⟦
module Convert {
  -- A record's binder-data blocks as a search tree keyed by `(ekind, eidx, variant)`: a leaf
  -- holds a block's key and its nodes, an inner node the least key of its right subtree.
  enum BinderTreeNode {
      Leaf(Field, Field, Field, Lists::List<Ixon::BinderNode>),
      Node(Field, Field, Field, BinderTree, BinderTree),
      Empty
    }

  type BinderTree = &BinderTreeNode;
}
⟧

def bytes_to_u64_limb := aiur_fn⟦
  fn bytes_to_u64_limb(bytes: Bytes::Stream, acc: UInt64::U64, pos: Field) -> UInt64::U64 {
      match pos {
        8 => {  acc } ,
        _ => {
          match (*(bytes)) {
            Lists::Node::Nil => {  acc } ,
            Lists::Node::Cons(byte, rest) => {
              let [v0, v1, v2, v3, v4, v5, v6, v7] = acc;
              match pos {
                0 => {  bytes_to_u64_limb(rest, [byte, v1, v2, v3, v4, v5, v6, v7], 1) } ,
                1 => {  bytes_to_u64_limb(rest, [v0, byte, v2, v3, v4, v5, v6, v7], 2) } ,
                2 => {  bytes_to_u64_limb(rest, [v0, v1, byte, v3, v4, v5, v6, v7], 3) } ,
                3 => {  bytes_to_u64_limb(rest, [v0, v1, v2, byte, v4, v5, v6, v7], 4) } ,
                4 => {  bytes_to_u64_limb(rest, [v0, v1, v2, v3, byte, v5, v6, v7], 5) } ,
                5 => {  bytes_to_u64_limb(rest, [v0, v1, v2, v3, v4, byte, v6, v7], 6) } ,
                6 => {  bytes_to_u64_limb(rest, [v0, v1, v2, v3, v4, v5, byte, v7], 7) } ,
                _ => {  bytes_to_u64_limb(rest, [v0, v1, v2, v3, v4, v5, v6, byte], 8) } ,
              } } ,
          } } ,
      }
    }
⟧

def skip_bytes := aiur_fn⟦
  fn skip_bytes(bytes: Bytes::Stream, n: Field) -> Bytes::Stream {
      match n {
        0 => {  bytes } ,
        _ => {
          match (*(bytes)) {
            Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
            Lists::Node::Cons(_, rest) => {  skip_bytes(rest, n - 1) } ,
          } } ,
      }
    }
⟧

  -- Nat literal blobs. A blob is canonical when it is Lean's `Nat.toBytesLE n`: `[0]` for 0,
  -- otherwise no trailing zero byte. IxC's reader accepts exactly these (`canonicalNatural`: one
  -- byte, or more than one whose last is not 0) and refuses any other (`ECx.natAt`). A Nat
  -- literal's blob is read in one place, the `Nat` arm of `convert_expr`
  -- (`Ingress::load_verified_blob` has no other caller but the `Str` arm), which refuses the same
  -- blobs (`assert_nat_blob_canonical`) before `bytes_to_limbs` reads the value's minimal
  -- little-endian limbs, so each number has one record spelling.

def assert_nat_blob_canonical := aiur_fn⟦
  fn assert_nat_blob_canonical(bytes: Bytes::Stream) -> () {
      match (*(bytes)) {
        Lists::Node::Nil => {
          assert_eq!(0, 1, "Nat literal: an empty blob");
          () } ,
        Lists::Node::Cons(_, rest) => {
          match (*(rest)) {
            Lists::Node::Nil => {  () } ,
            _ => {  assert_nat_blob_last_nonzero(rest) } ,
          } } ,
      }
    }
⟧

  -- A blob of one or more bytes whose last byte is not 0.

def assert_nat_blob_last_nonzero := aiur_fn⟦
  fn assert_nat_blob_last_nonzero(bytes: Bytes::Stream) -> () {
      let Lists::Node::Cons(byte, rest) = (*(bytes));
      match (*(rest)) {
        Lists::Node::Nil => {
          match UInt8::to_field(byte) {
            0 => {
              assert_eq!(0, 1, "Nat literal: a blob with a trailing zero byte");
              () } ,
            _ => {  () } ,
          } } ,
        _ => {  assert_nat_blob_last_nonzero(rest) } ,
      }
    }
⟧

def bytes_to_limbs := aiur_fn⟦
  fn bytes_to_limbs(bytes: Bytes::Stream) -> KernelTypes::KLimbs {
      let limb = bytes_to_u64_limb(bytes, [UInt8::BYTE_0; 8], 0);
      let rest_bytes = skip_bytes(bytes, 8);
      let rest_limbs = match (*(rest_bytes)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        _ => {  bytes_to_limbs(rest_bytes) } ,
      };
      match (*(rest_limbs)) {
        Lists::Node::Nil => {
          match UInt64::is_zero(limb) {
            1 => {  (&(Lists::Node::Nil)) } ,
            0 => {  (&(Lists::Node::Cons(limb, (&(Lists::Node::Nil))))) } ,
          } } ,
        _ => {  (&(Lists::Node::Cons(limb, rest_limbs))) } ,
      }
    }
⟧

def convert_univ := aiur_fn⟦
  fn convert_univ(u: &Ixon::Univ) -> KernelTypes::KLevel {
      match (*(u)) {
        Ixon::Univ::Zero => {  (&(KernelTypes::KLevelNode::Zero)) } ,
        Ixon::Univ::Succ(inner) => {  (&(KernelTypes::KLevelNode::Succ(convert_univ(inner)))) } ,
        Ixon::Univ::Max(a, b) => {  (&(KernelTypes::KLevelNode::Max(convert_univ(a), convert_univ(b)))) } ,
        Ixon::Univ::IMax(a, b) => {  (&(KernelTypes::KLevelNode::IMax(convert_univ(a), convert_univ(b)))) } ,
        Ixon::Univ::Var(idx) => {  (&(KernelTypes::KLevelNode::Param(UInt64::to_field(idx)))) } ,
      }
    }
⟧

def convert_univ_idxs := aiur_fn⟦
  fn convert_univ_idxs(idxs: Lists::List<UInt64::U64>, univs: Lists::List<&Ixon::Univ>) -> Lists::List<KernelTypes::KLevel> {
      match (*(idxs)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(idx, rest) => {
          let u_ref = Lists::lookup(univs, UInt64::to_field(idx));
          (&(Lists::Node::Cons(convert_univ(u_ref), convert_univ_idxs(rest, univs)))) } ,
      }
    }
⟧

  -- Sharing in bounded form: `sharing` is the record's whole table, and `bound` the number of
  -- entries the expression may refer to. Entry `n` is converted with bound `n`, so it refers only
  -- to entries before it, and entry 0 to none (IxC's `MemberReader.mk'`). An entry is found by
  -- `Lists::drop` on the one table, whose calls all lookups share. (The earlier form converted
  -- entry `n` under `Lists::take(sharing, n)`, a new list per entry: quadratic, review K3-1.)
  --
  -- Binder data. Every `Lam` and `All` node carries its binder datum (the zero-ness of its
  -- codomain sort), read from the record's binder-data section, which the record's address
  -- covers. The data are untrusted: the kernel's rules validate them at `Infer.lam` and
  -- `Infer.forallE`. A block of the section holds the data of one expression of the record, a
  -- root (`ekind` 0, `eidx` the root's number, variant 0) or a sharing entry at one of its
  -- variants (`ekind` 1, `eidx` the entry's index): one node per numbered node of the
  -- expression, in pre-order (type before body, function before argument, a `Let`'s type, value
  -- and body). The numbered nodes are the `Lam` and `All` nodes and the `Share` nodes whose
  -- entry has a binder (through its own shares). A `Share` is not entered: its node names the
  -- variant its entry is converted with, and the entry at that variant is a block of its own.
  -- `binder_table` makes a record's blocks a search tree once per record.
  --
  -- `convert_expr` converts a tree without its data and returns, with the conversion, whether
  -- the tree has a binder (through its shares). A tree without a binder has no numbered node
  -- and needs no datum: its conversion is the one memoized here, shared by all its
  -- occurrences. A tree with a binder is converted by `convert_annotated`, which takes the
  -- nodes of its block from the tree's first numbered node on and returns, with the
  -- conversion, the nodes after the tree's own; for such a tree the first component returned
  -- here is a placeholder, never used, and `convert_expr` does not descend below a binder.

def convert_expr := aiur_fn⟦
  fn convert_expr(
      e: &Ixon::Expr,
      sharing: Lists::List<&Ixon::Expr>,
      bound: Field,
      refs: Lists::List<Bytes::AddressRef>,
      recur_addrs: Lists::List<Bytes::AddressRef>,
      univs: Lists::List<&Ixon::Univ>
    ) -> (KernelTypes::KExpr, Field) {
      match (*(e)) {
        Ixon::Expr::Srt(univ_idx) => {
          let u_ref = Lists::lookup(univs, UInt64::to_field(univ_idx));
          ((&(KernelTypes::KExprNode::Srt(convert_univ(u_ref)))), 0) } ,

        Ixon::Expr::Var(idx) => {
          ((&(KernelTypes::KExprNode::BVar(UInt64::to_field(idx)))), 0) } ,

        Ixon::Expr::Ref(ref_idx, univ_idxs) => {
          let ref_addr = Lists::lookup(refs, UInt64::to_field(ref_idx));
          let levels = convert_univ_idxs(univ_idxs, univs);
          ((&(KernelTypes::KExprNode::Const(ref_addr, levels))), 0) } ,

        Ixon::Expr::Rec(rec_idx, univ_idxs) => {

          let ref_addr = Lists::lookup(recur_addrs, UInt64::to_field(rec_idx));
          let levels = convert_univ_idxs(univ_idxs, univs);
          ((&(KernelTypes::KExprNode::Const(ref_addr, levels))), 0) } ,

        Ixon::Expr::Prj(type_ref_idx, field_idx, inner) => {
          let (ki, bi) = convert_expr(inner, sharing, bound, refs, recur_addrs, univs);
          match bi {
            0 => {
              let type_addr = Lists::lookup(refs, UInt64::to_field(type_ref_idx));
              ((&(KernelTypes::KExprNode::Proj(type_addr, UInt64::to_field(field_idx), ki))), 0) } ,
            _ => {  (ki, 1) } ,
          } } ,

        Ixon::Expr::Str(blob_ref_idx) => {
          let blob_addr = Lists::lookup(refs, UInt64::to_field(blob_ref_idx));
          let bs = Ingress::load_verified_blob(blob_addr);

          KernelNatPrim::utf8_validate(bs);
          ((&(KernelTypes::KExprNode::Lit(KernelTypes::KLiteral::Str(bs)))), 0) } ,

        Ixon::Expr::Nat(blob_ref_idx) => {
          let blob_addr = Lists::lookup(refs, UInt64::to_field(blob_ref_idx));
          let bs = Ingress::load_verified_blob(blob_addr);
          assert_nat_blob_canonical(bs);
          let limbs = bytes_to_limbs(bs);
          ((&(KernelTypes::KExprNode::Lit(KernelTypes::KLiteral::Nat(limbs)))), 0) } ,

        Ixon::Expr::App(f, a) => {
          let (kf, bf) = convert_expr(f, sharing, bound, refs, recur_addrs, univs);
          let (ka, ba) = convert_expr(a, sharing, bound, refs, recur_addrs, univs);
          match bf + ba {
            0 => {  ((&(KernelTypes::KExprNode::App(kf, ka))), 0) } ,
            _ => {  (kf, 1) } ,
          } } ,

        Ixon::Expr::Lam(_, _) => {
          ((&(KernelTypes::KExprNode::BVar(0))), 1) } ,

        Ixon::Expr::All(_, _) => {
          ((&(KernelTypes::KExprNode::BVar(0))), 1) } ,

        Ixon::Expr::Let(_, ty, val, body) => {
          let (kt, bt) = convert_expr(ty, sharing, bound, refs, recur_addrs, univs);
          let (kv, bv) = convert_expr(val, sharing, bound, refs, recur_addrs, univs);
          let (kb, bb) = convert_expr(body, sharing, bound, refs, recur_addrs, univs);
          match (bt + bv) + bb {
            0 => {  ((&(KernelTypes::KExprNode::Let(kt, kv, kb))), 0) } ,
            _ => {  (kt, 1) } ,
          } } ,

        Ixon::Expr::Share(idx) => {
          let n = UInt64::to_field(idx);
          assert_eq!(UInt32::less_than_fields(n, bound), 1, "sharing reference is not to an earlier entry");
          let Lists::Node::Cons(s, _) = (*(Lists::drop(sharing, n)));
          convert_expr(s, sharing, n, refs, recur_addrs, univs) } ,
      }
    }
⟧

  -- The key order, `(ekind, eidx, variant)` lexicographically (`ekind` is 0 or 1).

def binder_key_lt := aiur_fn⟦
  fn binder_key_lt(e1: Field, i1: Field, v1: Field, e2: Field, i2: Field, v2: Field) -> Field {
      match e1 - e2 {
        0 => {
          match i1 - i2 {
            0 => {  UInt32::less_than_fields(v1, v2) } ,
            _ => {  UInt32::less_than_fields(i1, i2) } ,
          } } ,
        _ => {  e2 } ,
      }
    }
⟧

  -- The leaves of a record's blocks, each with its key; the blocks are strictly ascending
  -- (`IxonDeserialize::get_binders` checks it), and so are the leaves.

def binder_leaves := aiur_fn⟦
  fn binder_leaves(blocks: Lists::List<Ixon::BinderBlock>)
      -> Lists::List<(Field, Field, Field, Convert::BinderTree)> {
      match (*(blocks)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(block, rest) => {
          let Ixon::BinderBlock::Mk(ekind, eidx, variant, nodes) = block;
          let i = UInt64::to_field(eidx);
          let v = UInt64::to_field(variant);
          (&(Lists::Node::Cons((ekind, i, v, (&(Convert::BinderTreeNode::Leaf(ekind, i, v, nodes)))),
            binder_leaves(rest)))) } ,
      }
    }
⟧

  -- One level up: adjacent trees joined in pairs, each with its least key.

def binder_pairs := aiur_fn⟦
  fn binder_pairs(level: Lists::List<(Field, Field, Field, Convert::BinderTree)>)
      -> Lists::List<(Field, Field, Field, Convert::BinderTree)> {
      match (*(level)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(x, rest) => {
          match (*(rest)) {
            Lists::Node::Nil => {  level } ,
            Lists::Node::Cons(y, rest2) => {
              let (e1, i1, v1, t1) = x;
              let (e2, i2, v2, t2) = y;
              (&(Lists::Node::Cons((e1, i1, v1, (&(Convert::BinderTreeNode::Node(e2, i2, v2, t1, t2)))),
                binder_pairs(rest2)))) } ,
          } } ,
      }
    }
⟧

def binder_tree_of := aiur_fn⟦
  fn binder_tree_of(level: Lists::List<(Field, Field, Field, Convert::BinderTree)>) -> Convert::BinderTree {
      match (*(level)) {
        Lists::Node::Nil => {  (&(Convert::BinderTreeNode::Empty)) } ,
        Lists::Node::Cons(x, rest) => {
          match (*(rest)) {
            Lists::Node::Nil => {
              let (_, _, _, t) = x;
              t } ,
            _ => {  binder_tree_of(binder_pairs(level)) } ,
          } } ,
      }
    }
⟧

  -- A record's binder-data blocks as a balanced search tree (depth ⌈log₂ n⌉ for n blocks).

def binder_table := aiur_fn⟦
  fn binder_table(blocks: Lists::List<Ixon::BinderBlock>) -> Convert::BinderTree {
      binder_tree_of(binder_leaves(blocks))
    }
⟧

  -- The nodes of the block `(ekind, eidx, variant)`. A missing block is a rejection.

def binder_nodes := aiur_fn⟦
  fn binder_nodes(tree: Convert::BinderTree, ekind: Field, eidx: Field, variant: Field)
      -> Lists::List<Ixon::BinderNode> {
      match (*(tree)) {
        Convert::BinderTreeNode::Leaf(e, i, v, nodes) => {
          assert_eq!(e, ekind, "binder data: no block for an expression with a binder");
          assert_eq!(i, eidx, "binder data: no block for an expression with a binder");
          assert_eq!(v, variant, "binder data: no block for an expression with a binder");
          nodes } ,
        Convert::BinderTreeNode::Node(e, i, v, left, right) => {
          match binder_key_lt(ekind, eidx, variant, e, i, v) {
            1 => {  binder_nodes(left, ekind, eidx, variant) } ,
            0 => {  binder_nodes(right, ekind, eidx, variant) } ,
          } } ,
      }
    }
⟧

  -- A binder's datum as a level: `never ↦ Succ(Zero)`, `ifAllZero [] ↦ Zero`,
  -- `ifAllZero [p₁…pₖ] ↦ Max(Param p₁, Max(…, Param pₖ))`. The undecided sentinel, or a share
  -- node, at a binder is a rejection.

def binder_level := aiur_fn⟦
  fn binder_level(node: Ixon::BinderNode) -> KernelTypes::KLevel {
      match node {
        Ixon::BinderNode::Never(_) => {
          (&(KernelTypes::KLevelNode::Succ((&(KernelTypes::KLevelNode::Zero))))) } ,
        Ixon::BinderNode::Zero(_) => {  (&(KernelTypes::KLevelNode::Zero)) } ,
        Ixon::BinderNode::IfAllZero(params, _) => {  params_level(params) } ,
        Ixon::BinderNode::Undecided(_) => {
          assert_eq!(0, 1, "binder data: an undecided binder");
          (&(KernelTypes::KLevelNode::Zero)) } ,
        Ixon::BinderNode::Share(_) => {
          assert_eq!(0, 1, "binder data: a share node at a binder");
          (&(KernelTypes::KLevelNode::Zero)) } ,
      }
    }
⟧

def params_level := aiur_fn⟦
  fn params_level(params: Lists::List<UInt64::U64>) -> KernelTypes::KLevel {
      let Lists::Node::Cons(p, rest) = (*(params));
      let lp = (&(KernelTypes::KLevelNode::Param(UInt64::to_field(p))));
      match (*(rest)) {
        Lists::Node::Nil => {  lp } ,
        _ => {  (&(KernelTypes::KLevelNode::Max(lp, params_level(rest)))) } ,
      }
    }
⟧

  -- A tree with a binder (through its shares), `nodes` its block's nodes from the tree's first
  -- numbered node on: the conversion, and the nodes after the tree's own. Running out of
  -- nodes, or a node of the wrong kind, is a rejection.

def convert_annotated := aiur_fn⟦
  fn convert_annotated(
      e: &Ixon::Expr,
      sharing: Lists::List<&Ixon::Expr>,
      bound: Field,
      refs: Lists::List<Bytes::AddressRef>,
      recur_addrs: Lists::List<Bytes::AddressRef>,
      univs: Lists::List<&Ixon::Univ>,
      tbl: Convert::BinderTree,
      nodes: Lists::List<Ixon::BinderNode>
    ) -> (KernelTypes::KExpr, Lists::List<Ixon::BinderNode>) {
      match (*(e)) {
        Ixon::Expr::App(f, a) => {
          let (kf, bf) = convert_expr(f, sharing, bound, refs, recur_addrs, univs);
          let (ka, ba) = convert_expr(a, sharing, bound, refs, recur_addrs, univs);
          let (kf2, n1) = match bf {
            0 => {  (kf, nodes) } ,
            _ => {  convert_annotated(f, sharing, bound, refs, recur_addrs, univs, tbl, nodes) } ,
          };
          let (ka2, n2) = match ba {
            0 => {  (ka, n1) } ,
            _ => {  convert_annotated(a, sharing, bound, refs, recur_addrs, univs, tbl, n1) } ,
          };
          ((&(KernelTypes::KExprNode::App(kf2, ka2))), n2) } ,

        Ixon::Expr::Lam(ty, body) => {
          let Lists::Node::Cons(node, n0) = (*(nodes));
          let l = binder_level(node);
          let (kt, bt) = convert_expr(ty, sharing, bound, refs, recur_addrs, univs);
          let (kb, bb) = convert_expr(body, sharing, bound, refs, recur_addrs, univs);
          let (kt2, n1) = match bt {
            0 => {  (kt, n0) } ,
            _ => {  convert_annotated(ty, sharing, bound, refs, recur_addrs, univs, tbl, n0) } ,
          };
          let (kb2, n2) = match bb {
            0 => {  (kb, n1) } ,
            _ => {  convert_annotated(body, sharing, bound, refs, recur_addrs, univs, tbl, n1) } ,
          };
          ((&(KernelTypes::KExprNode::Lam(kt2, kb2, l))), n2) } ,

        Ixon::Expr::All(ty, body) => {
          let Lists::Node::Cons(node, n0) = (*(nodes));
          let l = binder_level(node);
          let (kt, bt) = convert_expr(ty, sharing, bound, refs, recur_addrs, univs);
          let (kb, bb) = convert_expr(body, sharing, bound, refs, recur_addrs, univs);
          let (kt2, n1) = match bt {
            0 => {  (kt, n0) } ,
            _ => {  convert_annotated(ty, sharing, bound, refs, recur_addrs, univs, tbl, n0) } ,
          };
          let (kb2, n2) = match bb {
            0 => {  (kb, n1) } ,
            _ => {  convert_annotated(body, sharing, bound, refs, recur_addrs, univs, tbl, n1) } ,
          };
          ((&(KernelTypes::KExprNode::Forall(kt2, kb2, l))), n2) } ,

        Ixon::Expr::Let(_, ty, val, body) => {
          let (kt, bt) = convert_expr(ty, sharing, bound, refs, recur_addrs, univs);
          let (kv, bv) = convert_expr(val, sharing, bound, refs, recur_addrs, univs);
          let (kb, bb) = convert_expr(body, sharing, bound, refs, recur_addrs, univs);
          let (kt2, n1) = match bt {
            0 => {  (kt, nodes) } ,
            _ => {  convert_annotated(ty, sharing, bound, refs, recur_addrs, univs, tbl, nodes) } ,
          };
          let (kv2, n2) = match bv {
            0 => {  (kv, n1) } ,
            _ => {  convert_annotated(val, sharing, bound, refs, recur_addrs, univs, tbl, n1) } ,
          };
          let (kb2, n3) = match bb {
            0 => {  (kb, n2) } ,
            _ => {  convert_annotated(body, sharing, bound, refs, recur_addrs, univs, tbl, n2) } ,
          };
          ((&(KernelTypes::KExprNode::Let(kt2, kv2, kb2))), n3) } ,

        Ixon::Expr::Prj(type_ref_idx, field_idx, inner) => {
          let type_addr = Lists::lookup(refs, UInt64::to_field(type_ref_idx));
          let (ki, n1) = convert_annotated(inner, sharing, bound, refs, recur_addrs, univs, tbl, nodes);
          ((&(KernelTypes::KExprNode::Proj(type_addr, UInt64::to_field(field_idx), ki))), n1) } ,

        Ixon::Expr::Share(idx) => {
          let n = UInt64::to_field(idx);
          let Lists::Node::Cons(s, _) = (*(Lists::drop(sharing, n)));
          let Lists::Node::Cons(node, n1) = (*(nodes));
          let Ixon::BinderNode::Share(variant) = node;
          let entry_nodes = binder_nodes(tbl, 1, n, UInt64::to_field(variant));
          (convert_block(s, sharing, n, refs, recur_addrs, univs, tbl, entry_nodes), n1) } ,
      }
    }
⟧

  -- A tree with a binder converted with the whole node list of its block: every node is used.

def convert_block := aiur_fn⟦
  fn convert_block(
      e: &Ixon::Expr,
      sharing: Lists::List<&Ixon::Expr>,
      bound: Field,
      refs: Lists::List<Bytes::AddressRef>,
      recur_addrs: Lists::List<Bytes::AddressRef>,
      univs: Lists::List<&Ixon::Univ>,
      tbl: Convert::BinderTree,
      nodes: Lists::List<Ixon::BinderNode>
    ) -> KernelTypes::KExpr {
      let (k, rest) = convert_annotated(e, sharing, bound, refs, recur_addrs, univs, tbl, nodes);
      let Lists::Node::Nil = (*(rest));
      k
    }
⟧

  -- A root expression of a record may refer to every sharing entry. Its bound is the largest
  -- `u32`: `Lists::drop` refuses an index past the table, and a table is shorter than its
  -- record's byte stream, whose length `IxByteStream::read_finite_byte_stream` checks below
  -- 2^32 - 1, so the comparison never refuses an index that `drop` accepts. Root `r` of a
  -- record whose blocks are `tbl` is the block `(0, r)` at variant 0.

def convert_root := aiur_fn⟦
  inline fn convert_root(
      e: &Ixon::Expr,
      sharing: Lists::List<&Ixon::Expr>,
      refs: Lists::List<Bytes::AddressRef>,
      recur_addrs: Lists::List<Bytes::AddressRef>,
      univs: Lists::List<&Ixon::Univ>,
      tbl: Convert::BinderTree, r: Field
    ) -> KernelTypes::KExpr {
      let (k, b) = convert_expr(e, sharing, 4294967295, refs, recur_addrs, univs);
      match b {
        0 => {  k } ,
        _ => {  convert_block(e, sharing, 4294967295, refs, recur_addrs, univs, tbl, binder_nodes(tbl, 0, r, 0)) } ,
      }
    }
⟧

  -- The number of root expressions a block member contributes (its roots are numbered
  -- consecutively across the block): a definition's type and value, an inductive's type
  -- and its constructors' types, a recursor's type and its rules' right-hand sides.

def mut_const_roots := aiur_fn⟦
  fn mut_const_roots(m: Ixon::MutConst) -> Field {
      match m {
        Ixon::MutConst::Defn(_) => {  2 } ,
        Ixon::MutConst::Indc(ind) => {
          match ind {
            Ixon::Inductive::Mk(_, _, _, _, _, ctors) => {  count_ctors(ctors) + 1 } ,
          } } ,
        Ixon::MutConst::Recr(r) => {
          match r {
            Ixon::Recursor::Mk(_, _, _, _, _, _, _, _, rules) => {  Lists::length(rules) + 1 } ,
          } } ,
      }
    }
⟧

  -- The index of member `idx`'s first root in its block.

def muts_root_offset := aiur_fn⟦
  fn muts_root_offset(members: Lists::List<Ixon::MutConst>, idx: Field) -> Field {
      match idx {
        0 => {  0 } ,
        _ => {
          match (*(members)) {
            Lists::Node::Cons(m, rest) => {  mut_const_roots(m) + muts_root_offset(rest, idx - 1) } ,
          } } ,
      }
    }
⟧

def convert_definition := aiur_fn⟦
  fn convert_definition(d: Ixon::Definition, sharing: Lists::List<&Ixon::Expr>,
                              refs: Lists::List<Bytes::AddressRef>, recur_addrs: Lists::List<Bytes::AddressRef>,
                              univs: Lists::List<&Ixon::Univ>, hint: Field,
                              tbl: Convert::BinderTree, base: Field) -> KernelTypes::KConstantInfo {
      match d {
        Ixon::Definition::Mk(kind, safety, _, lvls, typ, value) => {
          let ktyp = convert_root(typ, sharing, refs, recur_addrs, univs, tbl, base);
          let kval = convert_root(value, sharing, refs, recur_addrs, univs, tbl, base + 1);
          let nlvls = UInt64::to_field(lvls);
          match kind {
            Ixon::DefKind::Definition => {
              KernelTypes::KConstantInfo::Defn(nlvls, ktyp, kval, safety, hint) } ,
            Ixon::DefKind::Opaque => {
              let is_unsafe = match safety { Ixon::DefinitionSafety::Unsafe => {  1 } , _ => {  0 } , };
              KernelTypes::KConstantInfo::Opaque(nlvls, ktyp, kval, is_unsafe) } ,
            Ixon::DefKind::Theorem => {
              KernelTypes::KConstantInfo::Thm(nlvls, ktyp, kval) } ,
          } } ,
      }
    }
⟧

def convert_axiom := aiur_fn⟦
  fn convert_axiom(a: Ixon::Axiom, sharing: Lists::List<&Ixon::Expr>,
                         refs: Lists::List<Bytes::AddressRef>, recur_addrs: Lists::List<Bytes::AddressRef>,
                         univs: Lists::List<&Ixon::Univ>, tbl: Convert::BinderTree) -> KernelTypes::KConstantInfo {
      match a {
        Ixon::Axiom::Mk(is_unsafe, lvls, typ) => {
          let ktyp = convert_root(typ, sharing, refs, recur_addrs, univs, tbl, 0);
          KernelTypes::KConstantInfo::Axiom(UInt64::to_field(lvls), ktyp, is_unsafe) } ,
      }
    }
⟧

def convert_quotient := aiur_fn⟦
  fn convert_quotient(q: Ixon::Quotient, sharing: Lists::List<&Ixon::Expr>,
                            refs: Lists::List<Bytes::AddressRef>, recur_addrs: Lists::List<Bytes::AddressRef>,
                            univs: Lists::List<&Ixon::Univ>, tbl: Convert::BinderTree) -> KernelTypes::KConstantInfo {
      match q {
        Ixon::Quotient::Mk(kind, lvls, typ) => {
          let ktyp = convert_root(typ, sharing, refs, recur_addrs, univs, tbl, 0);
          KernelTypes::KConstantInfo::Quot(UInt64::to_field(lvls), ktyp, kind) } ,
      }
    }
⟧

def count_ctors := aiur_fn⟦
  fn count_ctors(cs: Lists::List<Ixon::Constructor>) -> Field {
      match (*(cs)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(_, rest) => {  count_ctors(rest) + 1 } ,
      }
    }
⟧

def ctor_at := aiur_fn⟦
  fn ctor_at(cs: Lists::List<Ixon::Constructor>, cidx: Field) -> Ixon::Constructor {
      match (*(cs)) {
        Lists::Node::Cons(c, rest) => {
          match cidx {
            0 => {  c } ,
            _ => {  ctor_at(rest, cidx - 1) } ,
          } } ,
      }
    }
⟧

def convert_inductive := aiur_fn⟦
  fn convert_inductive(ind: Ixon::Inductive, block_addr: Bytes::AddressRef, ind_idx: Field,
                             sharing: Lists::List<&Ixon::Expr>, refs: Lists::List<Bytes::AddressRef>,
                             recur_addrs: Lists::List<Bytes::AddressRef>,
                             univs: Lists::List<&Ixon::Univ>, tbl: Convert::BinderTree, base: Field) -> KernelTypes::KConstantInfo {
      match ind {
        Ixon::Inductive::Mk(is_unsafe, lvls, params, indices, typ, ctors) => {
          let ktyp = convert_root(typ, sharing, refs, recur_addrs, univs, tbl, base);
          KernelTypes::KConstantInfo::Induct(
            UInt64::to_field(lvls), ktyp,
            UInt64::to_field(params), UInt64::to_field(indices),
            count_ctors(ctors), is_unsafe,
            block_addr, ind_idx) } ,
      }
    }
⟧

def convert_constructor := aiur_fn⟦
  fn convert_constructor(c: Ixon::Constructor, block_addr: Bytes::AddressRef, ind_idx: Field,
                               sharing: Lists::List<&Ixon::Expr>, refs: Lists::List<Bytes::AddressRef>,
                               recur_addrs: Lists::List<Bytes::AddressRef>,
                               univs: Lists::List<&Ixon::Univ>, tbl: Convert::BinderTree, base: Field) -> KernelTypes::KConstantInfo {
      match c {
        Ixon::Constructor::Mk(is_unsafe, lvls, cidx, params, fields, _, typ) => {
          let ktyp = convert_root(typ, sharing, refs, recur_addrs, univs, tbl, base);
          KernelTypes::KConstantInfo::Ctor(
            UInt64::to_field(lvls), ktyp,
            block_addr, ind_idx, UInt64::to_field(cidx),
            UInt64::to_field(params), UInt64::to_field(fields), is_unsafe) } ,
      }
    }
⟧

def convert_rec_rules := aiur_fn⟦
  fn convert_rec_rules(rs: Lists::List<Ixon::RecursorRule>, sharing: Lists::List<&Ixon::Expr>,
                             refs: Lists::List<Bytes::AddressRef>, recur_addrs: Lists::List<Bytes::AddressRef>,
                             univs: Lists::List<&Ixon::Univ>, cidx: Field,
                             tbl: Convert::BinderTree, ridx: Field) -> Lists::List<KernelTypes::KRecRule> {
      match (*(rs)) {
        Lists::Node::Nil => {
          (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(r, rest) => {
          match r {
            Ixon::RecursorRule::Mk(fields, rhs) => {
              let krhs = convert_root(rhs, sharing, refs, recur_addrs, univs, tbl, ridx);
              (&(Lists::Node::Cons(
                KernelTypes::KRecRule::Mk(cidx, UInt64::to_field(fields), krhs),
                convert_rec_rules(rest, sharing, refs, recur_addrs, univs, cidx + 1, tbl, ridx + 1)))) } ,
          } } ,
      }
    }
⟧

def convert_recursor := aiur_fn⟦
  fn convert_recursor(r: Ixon::Recursor, block_addr: Bytes::AddressRef, rec_idx: Field,
                            sharing: Lists::List<&Ixon::Expr>, refs: Lists::List<Bytes::AddressRef>,
                            recur_addrs: Lists::List<Bytes::AddressRef>,
                            univs: Lists::List<&Ixon::Univ>, tbl: Convert::BinderTree, base: Field) -> KernelTypes::KConstantInfo {
      match r {
        Ixon::Recursor::Mk(k, is_unsafe, lvls, params, indices, motives, minors, typ, rules) => {
          -- The type is read with no recursive reference in scope: a recursor's type never
          -- mentions its own family (the kernel checks it before the family is installed); only
          -- its rules call the family's recursors.
          let ktyp = convert_root(typ, sharing, refs, (&(Lists::Node::Nil)), univs, tbl, base);
          let krules = convert_rec_rules(rules, sharing, refs, recur_addrs, univs, 0, tbl, base + 1);
          KernelTypes::KConstantInfo::Rec(
            UInt64::to_field(lvls), ktyp,
            UInt64::to_field(params), UInt64::to_field(indices),
            UInt64::to_field(motives), UInt64::to_field(minors),
            krules, k, is_unsafe,
            block_addr, rec_idx) } ,
      }
    }
⟧

end

end IxVM
