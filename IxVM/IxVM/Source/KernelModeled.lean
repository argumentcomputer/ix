import Aiur.Modules.Function

/-! # IxVM module `KernelModeled`

The modeled route for inductive declarations (decision D7): IxVM checks a mutual or
nested block the way the certified kernel's modeled install does
(`IxC/Kernel/Inductives/Modeled.lean`, `checkModeled`), against a model of the block
that the prover supplies as advice.

* **The route** is a function of the inductive block alone (`block_is_modeled`): two or
  more types, or a syntactic nested occurrence in a constructor. Every other block takes
  the native route (`KernelCheck`), which the kernel's `nativeShape?` recognises: one
  type, one recursor.
* **The advice** is untrusted. It is found by a hint on IO channel 7 keyed by the block's
  address (`read_payload`), and lists the model's records, which are ordinary Ixon
  records loaded from channel 2 under their content address (hash-checked like any
  record). Nothing about it is trusted: `check_family` validates it in full.
* **Coherence.** A hint is unconstrained at each call, so two checks of one block may see
  two payloads. A block's types, constructors and its *whole* recursor family record
  are therefore validated together against one payload (`check_family(block, rec_block)`),
  and a recursor is accepted only through the call for its own family record.
* **Use sites** (`KernelInfer`, `KernelInferOnly`, `KernelWhnf`, `KernelDefEq`) call
  `assert_proj_allowed`, `block_is_modeled` and `fire_ok`: no `.proj`, structure eta or
  unit-like conversion at a member of a modeled block, and the iota step of a modeled
  recursor compares the constructor's parameters and levels with the recursor's
  (`paramsBlind := false`).

Payload layout (bytes; counts are TagN0, addresses 32 bytes):

    rec_block
    nA, A[nA]              -- the advice records: definitions, theorems, native inductive
                           --   blocks and their recursors
    nW, W[nW]              -- outside references, each `addr kind witness`:
                           --   0  a basis role (`basis_role_allowed`)
                           --   1  a member of the block's dependency closure: a path from
                           --      the block (TagN0 count, then TagN0 steps: 0 = projection
                           --      to its block, j + 1 = the record's j-th used reference)
                           --   2  a native recursor of a block in the closure: a path to
                           --      that block; the recursor is checked here
                           --   3  a type or constructor of a block in the closure: a path
                           --      to the block, the member index, 0 (the type) or j + 1
                           --      (constructor j); the block's walk checks its members
    type models            -- one per member of the block, in position order
    ctor models            -- one per constructor, by member then constructor index
    recursor models        -- one per member of the family record, in order
    iota theorems          -- per recursor, one per rule, in rule order

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelModeled where

  -- ## The route

def muts_indc_count := aiur_fn⟦
  fn muts_indc_count(members: Lists::List<Ixon::MutConst>) -> Field {
      match (*(members)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Indc(_) => {  muts_indc_count(rest) + 1 } ,
            _ => {  muts_indc_count(rest) } ,
          } } ,
      }
    }
⟧

def first_indc_pos := aiur_fn⟦
  fn first_indc_pos(members: Lists::List<Ixon::MutConst>, pos: Field) -> (Field, Field) {
      match (*(members)) {
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Indc(ind) => {
              match ind {
                Ixon::Inductive::Mk(_, _, _, _, _, ctors) => {
                  (pos, Lists::length(ctors)) } ,
              } } ,
            _ => {  first_indc_pos(rest, pos + 1) } ,
          } } ,
      }
    }
⟧

  -- The route of an inductive block: 1 (modeled) for two or more types or a nested
  -- occurrence, 0 (native) otherwise; 0 for a record that is not an inductive block.

def block_is_modeled := aiur_fn⟦
  fn block_is_modeled(block: Bytes::AddressRef) -> Field {
      let c = Ingress::load_verified_constant(block);
      match c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              match muts_indc_count(members) {
                0 => {  0 } ,
                1 => {
                  let (pos, n_ctors) = first_indc_pos(members, 0);
                  let mems = Ingress::build_recur_addrs(members, block);
                  ctors_nested(block, pos, n_ctors, mems, 0) } ,
                _ => {  1 } ,
              } } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

  -- Two or more types: the gate the structure-eta and unit-like sites need (a one-type
  -- nested block's structure is recursive, which `KernelWhnf::struct_is_rec`'s scan finds,
  -- and a field-less constructor has no nested occurrence).

def block_is_multi := aiur_fn⟦
  fn block_is_multi(block: Bytes::AddressRef) -> Field {
      let c = Ingress::load_verified_constant(block);
      match c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              match muts_indc_count(members) {
                0 => {  0 } ,
                1 => {  0 } ,
                _ => {  1 } ,
              } } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def ctors_nested := aiur_fn⟦
  fn ctors_nested(block: Bytes::AddressRef, pos: Field, n_ctors: Field,
                  mems: Lists::List<Bytes::AddressRef>, cidx: Field) -> Field {
      match n_ctors - cidx {
        0 => {  0 } ,
        _ => {
          let cci = (*(Ingress::get_ci_cprj(block, pos, cidx)));
          match cci {
            KernelTypes::KConstantInfo::Ctor(_, cty, _, _, _, np, _, _) => {
              let body = KernelCheck::peel_n_foralls(cty, np);
              -- most constructors mention no member: one pass of `se_mentions`, no loads
              let found = match KernelWhnf::se_mentions(body, mems) {
                0 => {  0 } ,
                _ => {  nested_scan(body, mems) } ,
              };
              match found {
                1 => {  1 } ,
                _ => {  ctors_nested(block, pos, n_ctors, mems, cidx + 1) } ,
              } } ,
          } } ,
      }
    }
⟧

  -- Does `e` contain an application `I a⃗` of an inductive `I` outside the block whose
  -- arguments mention a member? Syntactic, as Lean's nested detection is.

def nested_scan := aiur_fn⟦
  fn nested_scan(e: KernelTypes::KExpr, mems: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(e)) {
        KernelTypes::KExprNode::App(_, _) => {
          let (head, args) = KernelTypes::collect_spine(e);
          let here = match (*(head)) {
            KernelTypes::KExprNode::Const(h, _) => {
              match KernelWhnf::se_addr_in(h, mems) {
                1 => {  0 } ,
                _ => {
                  -- the arguments first: `addr_is_inductive` loads the head
                  match nested_mentions(args, mems) {
                    1 => {  addr_is_inductive(h) } ,
                    _ => {  0 } ,
                  } } ,
              } } ,
            _ => {  nested_scan(head, mems) } ,
          };
          match here {
            1 => {  1 } ,
            _ => {  nested_scan_list(args, mems) } ,
          } } ,
        KernelTypes::KExprNode::Lam(t, b) => {
          match nested_scan(t, mems) {
            1 => {  1 } ,
            _ => {  nested_scan(b, mems) } ,
          } } ,
        KernelTypes::KExprNode::Forall(t, b) => {
          match nested_scan(t, mems) {
            1 => {  1 } ,
            _ => {  nested_scan(b, mems) } ,
          } } ,
        KernelTypes::KExprNode::Let(t, v, b) => {
          match nested_scan(t, mems) {
            1 => {  1 } ,
            _ => {
              match nested_scan(v, mems) {
                1 => {  1 } ,
                _ => {  nested_scan(b, mems) } ,
              } } ,
          } } ,
        KernelTypes::KExprNode::Proj(_, _, x) => {  nested_scan(x, mems) } ,
        _ => {  0 } ,
      }
    }
⟧

def nested_scan_list := aiur_fn⟦
  fn nested_scan_list(es: Lists::List<KernelTypes::KExpr>, mems: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(es)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(e, rest) => {
          match nested_scan(e, mems) {
            1 => {  1 } ,
            _ => {  nested_scan_list(rest, mems) } ,
          } } ,
      }
    }
⟧

def nested_mentions := aiur_fn⟦
  fn nested_mentions(es: Lists::List<KernelTypes::KExpr>, mems: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(es)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(e, rest) => {
          match KernelWhnf::se_mentions(e, mems) {
            1 => {  1 } ,
            _ => {  nested_mentions(rest, mems) } ,
          } } ,
      }
    }
⟧

def addr_is_inductive := aiur_fn⟦
  fn addr_is_inductive(a: Bytes::AddressRef) -> Field {
      match (*(Ingress::get_ci(a))) {
        KernelTypes::KConstantInfo::Induct(_, _, _, _, _, _, _, _) => {  1 } ,
        _ => {  0 } ,
      }
    }
⟧

  -- The inductive block a recursor's family eliminates: the block of its first
  -- motive's carrier.

def rec_family_block := aiur_fn⟦
  fn rec_family_block(rec_addr: Bytes::AddressRef) -> Bytes::AddressRef {
      match (*(Ingress::get_ci(rec_addr))) {
        KernelTypes::KConstantInfo::Rec(_, ty, np, _, _, _, _, _, _, _, _) => {
          let after = KernelCheck::peel_n_foralls(ty, np);
          match (*(after)) {
            KernelTypes::KExprNode::Forall(mdom, _) => {
              let carrier = last_binder_dom(mdom);
              let (head, _) = KernelTypes::collect_spine(carrier);
              match (*(head)) {
                KernelTypes::KExprNode::Const(t0, _) => {
                  match (*(Ingress::get_ci(t0))) {
                    KernelTypes::KConstantInfo::Induct(_, _, _, _, _, _, b, _) => {  b } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def last_binder_dom := aiur_fn⟦
  fn last_binder_dom(e: KernelTypes::KExpr) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::Forall(d, b) => {
          match (*(b)) {
            KernelTypes::KExprNode::Forall(_, _) => {  last_binder_dom(b) } ,
            _ => {  d } ,
          } } ,
      }
    }
⟧

  -- ## Use sites

  -- `.proj` is typed only at members of native blocks: the kernel installs no projection
  -- table for a mutual block, and IxVM checks no projection model.

def assert_proj_allowed := aiur_fn⟦
  fn assert_proj_allowed(block: Bytes::AddressRef) -> () {
      assert_eq!(block_is_modeled(block), 0,
        "projection on a member of a mutual or nested block");
      ()
    }
⟧

  -- The structure's constructor, at a native block only: the projection sites call this
  -- in place of `Ingress::get_ci_cprj`, memoized per structure, so the gate adds nothing to
  -- their rows.

def proj_ctor := aiur_fn⟦
  fn proj_ctor(block: Bytes::AddressRef, ind_idx: Field) -> &KernelTypes::KConstantInfo {
      assert_proj_allowed(block);
      Ingress::get_ci_cprj(block, ind_idx, 0)
    }
⟧

def ind_is_modeled := aiur_fn⟦
  fn ind_is_modeled(ind_addr: Bytes::AddressRef) -> Field {
      match (*(Ingress::get_ci(ind_addr))) {
        KernelTypes::KConstantInfo::Induct(_, _, _, _, _, _, b, _) => {  block_is_modeled(b) } ,
        _ => {  0 } ,
      }
    }
⟧

  -- The iota step's comparison at a modeled recursor (`paramsBlind := false`,
  -- `IxC/Kernel/Core.lean` `iotaRec`, `recFireComparands`): the constructor's levels and
  -- parameters are the comparands the recursor's major domain gives, at the redex's
  -- levels and prefix arguments. 1 at a native recursor.

def fire_ok := aiur_fn⟦
  inline fn fire_ok(rc: KernelRoles::RoleCtx, nmot: Field, head: KernelTypes::KExpr,
                    us: Lists::List<KernelTypes::KLevel>, spine: Lists::List<KernelTypes::KExpr>,
                    major: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      match nmot - 1 {
        0 => {  1 } ,
        _ => {  fire_compare(rc, head, us, spine, major, types) } ,
      }
    }
⟧

  -- A recursor with several motives is a modeled family's: a native recursor has one
  -- (`KernelCheck::check_const`), a modeled family two or more (`check_recs`).

def fire_compare := aiur_fn⟦
  fn fire_compare(rc: KernelRoles::RoleCtx, head: KernelTypes::KExpr, us: Lists::List<KernelTypes::KLevel>,
                  spine: Lists::List<KernelTypes::KExpr>, major: KernelTypes::KExpr,
                  types: Lists::List<KernelTypes::KExpr>) -> Field {
      match (*(head)) {
        KernelTypes::KExprNode::Const(raddr, _) => {
          match block_is_modeled(rec_family_block(raddr)) {
            0 => {  1 } ,
            _ => {
              let (_, ilvls, pins, rp) = rec_comparands(raddr);
              let lv = KernelLevels::level_list_inst(ilvls, us);
              let substs = Lists::reverse(Lists::take(spine, rp));
              let pins_i = inst_pins(pins, us, substs);
              let (mh, margs) = KernelTypes::collect_spine(major);
              match (*(mh)) {
                KernelTypes::KExprNode::Const(_, usj) => {
                  match level_list_equal(usj, lv) {
                    0 => {  0 } ,
                    _ => {
                      defeq_list_ok(rc, Lists::take(margs, Lists::length(pins_i)), pins_i, types) } ,
                  } } ,
                _ => {  0 } ,
              } } ,
          } } ,
        _ => {  1 } ,
      }
    }
⟧

def rec_comparands := aiur_fn⟦
  fn rec_comparands(raddr: Bytes::AddressRef)
        -> (Bytes::AddressRef, Lists::List<KernelTypes::KLevel>, Lists::List<KernelTypes::KExpr>, Field) {
      match (*(Ingress::get_ci(raddr))) {
        KernelTypes::KConstantInfo::Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) => {
          let (iaddr, ilvls, pins) = rec_major_pins(ty, np + nmot + nmin, ni);
          (iaddr, ilvls, pins, np + nmot + nmin) } ,
      }
    }
⟧

def inst_pins := aiur_fn⟦
  fn inst_pins(pins: Lists::List<KernelTypes::KExpr>, us: Lists::List<KernelTypes::KLevel>,
               substs: Lists::List<KernelTypes::KExpr>) -> Lists::List<KernelTypes::KExpr> {
      match (*(pins)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(p, rest) => {
          let pl = KernelLevels::expr_inst_levels(p, us);
          (&(Lists::Node::Cons(KernelSubst::expr_inst_many(pl, substs, 0),
                                inst_pins(rest, us, substs)))) } ,
      }
    }
⟧

def level_list_equal := aiur_fn⟦
  fn level_list_equal(a: Lists::List<KernelTypes::KLevel>, b: Lists::List<KernelTypes::KLevel>) -> Field {
      match (*(a)) {
        Lists::Node::Nil => {
          match (*(b)) {
            Lists::Node::Nil => {  1 } ,
            _ => {  0 } ,
          } } ,
        Lists::Node::Cons(x, xr) => {
          match (*(b)) {
            Lists::Node::Nil => {  0 } ,
            Lists::Node::Cons(y, yr) => {
              match KernelLevels::level_equal(x, y) {
                1 => {  level_list_equal(xr, yr) } ,
                _ => {  0 } ,
              } } ,
          } } ,
      }
    }
⟧

def defeq_list_ok := aiur_fn⟦
  fn defeq_list_ok(rc: KernelRoles::RoleCtx, xs: Lists::List<KernelTypes::KExpr>,
                   ys: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> Field {
      match (*(xs)) {
        Lists::Node::Nil => {
          match (*(ys)) {
            Lists::Node::Nil => {  1 } ,
            _ => {  0 } ,
          } } ,
        Lists::Node::Cons(x, xr) => {
          match (*(ys)) {
            Lists::Node::Nil => {  0 } ,
            Lists::Node::Cons(y, yr) => {
              match KernelDefEq::k_is_def_eq(rc, x, y, types) {
                1 => {  defeq_list_ok(rc, xr, yr, types) } ,
                _ => {  0 } ,
              } } ,
          } } ,
      }
    }
⟧

  -- The major premise's carrier, its levels, and its parameter arguments lowered into the
  -- rule-prefix context (`nestedRuleShape`): the domain is `I.{l⃗} a⃗ i⃗` with `i⃗` exactly
  -- the index variables, and no parameter argument mentions an index variable.

def rec_major_pins := aiur_fn⟦
  fn rec_major_pins(ty: KernelTypes::KExpr, rp: Field, ni: Field)
        -> (Bytes::AddressRef, Lists::List<KernelTypes::KLevel>, Lists::List<KernelTypes::KExpr>) {
      let after = KernelCheck::peel_n_foralls(ty, rp + ni);
      match (*(after)) {
        KernelTypes::KExprNode::Forall(dom, _) => {
          let (h, args) = KernelTypes::collect_spine(dom);
          match (*(h)) {
            KernelTypes::KExprNode::Const(iaddr, ilvls) => {
              match (*(Ingress::get_ci(iaddr))) {
                KernelTypes::KConstantInfo::Induct(_, _, inp, ini, _, _, _, _) => {
                  assert_eq!(ini, ni, "recursor index count differs from its major's");
                  assert_eq!(Lists::length(args), inp + ini,
                    "recursor major premise is not its inductive fully applied");
                  assert_index_vars(Lists::drop(args, inp), ni, 0);
                  (iaddr, ilvls, lower_pins(Lists::take(args, inp), ni)) } ,
              } } ,
          } } ,
      }
    }
⟧

def assert_index_vars := aiur_fn⟦
  fn assert_index_vars(args: Lists::List<KernelTypes::KExpr>, ni: Field, i: Field) -> () {
      match ni - i {
        0 => {  () } ,
        _ => {
          let Lists::Node::Cons(a, rest) = (*(args));
          match (*(a)) {
            KernelTypes::KExprNode::BVar(j) => {
              assert_eq!(j, (ni - 1) - i, "recursor major premise: an index argument is not its variable");
              assert_index_vars(rest, ni, i + 1) } ,
          } } ,
      }
    }
⟧

def lower_pins := aiur_fn⟦
  fn lower_pins(ps: Lists::List<KernelTypes::KExpr>, ni: Field) -> Lists::List<KernelTypes::KExpr> {
      match (*(ps)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(p, rest) => {
          assert_eq!(KernelSubst::has_bvar_in_range(p, 0, ni), 0,
            "recursor major premise: a parameter argument mentions an index");
          (&(Lists::Node::Cons(KernelSubst::expr_lower(p, ni, 0), lower_pins(rest, ni)))) } ,
      }
    }
⟧

  -- ## The advice payload

def read_payload := aiur_fn⟦
  fn read_payload(block: Bytes::AddressRef) -> Bytes::Stream {
      let raw = (*(block));
      let (idx, len) = IxVMCompat::io_get_info(7, raw);
      let s = IxByteStream::read_finite_byte_stream(7, idx, len);
      match (*(s)) {
        Lists::Node::Nil => {
          assert_eq!(0, 1, "no model advice for a mutual or nested block");
          s } ,
        _ => {  s } ,
      }
    }
⟧

def get_count := aiur_fn⟦
  fn get_count(s: Bytes::Stream) -> (Field, Bytes::Stream) {
      let (n, s2) = IxonDeserialize::get_tagn0(s);
      (UInt64::to_field(n), s2)
    }
⟧

def get_addrs := aiur_fn⟦
  fn get_addrs(s: Bytes::Stream, n: Field) -> (Lists::List<Bytes::AddressRef>, Bytes::Stream) {
      match n {
        0 => {  ((&(Lists::Node::Nil)), s) } ,
        _ => {
          let (a, s2) = IxonDeserialize::get_address(s);
          let (rest, s3) = get_addrs(s2, n - 1);
          ((&(Lists::Node::Cons(a, rest))), s3) } ,
      }
    }
⟧

  -- ## Outside references of the advice

  -- The basis roles advice may reference: `Nat` and its constructors and recursor, `Eq`,
  -- `Eq.refl`, `Eq.rec`, `PUnit`, `PUnit.unit`, `PUnit.rec`, `String`, `Char`. No axiom.

def basis_role_allowed := aiur_fn⟦
  fn basis_role_allowed(r: Field) -> Field {
      match r {
        0 => {  1 } ,
        1 => {  1 } ,
        2 => {  1 } ,
        3 => {  1 } ,
        8 => {  1 } ,
        9 => {  1 } ,
        10 => {  1 } ,
        11 => {  1 } ,
        12 => {  1 } ,
        13 => {  1 } ,
        37 => {  1 } ,
        39 => {  1 } ,
        _ => {  0 } ,
      }
    }
⟧

def check_witnesses := aiur_fn⟦
  fn check_witnesses(rc: KernelRoles::RoleCtx, block: Bytes::AddressRef, s: Bytes::Stream, n: Field)
        -> (Lists::List<Bytes::AddressRef>, Bytes::Stream) {
      match n {
        0 => {  ((&(Lists::Node::Nil)), s) } ,
        _ => {
          let (x, s2) = IxonDeserialize::get_address(s);
          let (kind, s3) = IxonDeserialize::read_byte(s2);
          let s4 = check_witness(rc, block, x, UInt8::to_field(kind), s3);
          let (rest, s5) = check_witnesses(rc, block, s4, n - 1);
          ((&(Lists::Node::Cons(x, rest))), s5) } ,
      }
    }
⟧

def check_witness := aiur_fn⟦
  fn check_witness(rc: KernelRoles::RoleCtx, block: Bytes::AddressRef, x: Bytes::AddressRef,
                   kind: Field, s: Bytes::Stream) -> Bytes::Stream {
      match kind {
        0 => {
          let r1 = KernelRoles::role_of(rc, x);
          assert_eq!(Fields::is_zero(r1), 0, "model advice: a basis reference is not bound to a role");
          assert_eq!(basis_role_allowed(r1 - 1), 1, "model advice: a reference to a role outside the basis");
          s } ,
        1 => {
          let (n, s2) = get_count(s);
          let (stop, s3) = walk_from_block(block, s2, n);
          assert_eq!(Bytes::address_eq(stop, x), 1, "model advice: a dependency path ends elsewhere");
          s3 } ,
        2 => {
          let (n, s2) = get_count(s);
          let (iblock, s3) = walk_from_block(block, s2, n);
          check_container_rec(rc, x, iblock);
          s3 } ,
        3 => {
          let (n, s2) = get_count(s);
          let (iblock, s3) = walk_from_block(block, s2, n);
          let (idx, s4) = get_count(s3);
          let (c1, s5) = get_count(s4);
          let expected = match c1 {
            0 => {  KernelDefEq::compute_iprj_addr(iblock, idx) } ,
            _ => {  KernelCheck::projection_addr_ctor(idx, c1 - 1, iblock) } ,
          };
          assert_eq!(Bytes::address_eq(expected, x), 1,
            "model advice: a projection witness names another member");
          s5 } ,
      }
    }
⟧

  -- A path of one step or more from the block: what it reaches is in the block's
  -- dependency closure, which by content addressing cannot contain the block.

def walk_from_block := aiur_fn⟦
  fn walk_from_block(block: Bytes::AddressRef, s: Bytes::Stream, n: Field) -> (Bytes::AddressRef, Bytes::Stream) {
      assert_eq!(Fields::is_zero(n), 0, "model advice: an empty dependency path");
      walk_path(block, s, n)
    }
⟧

  -- A path through the dependency closure the claim walk visits from `cur`: step 0 goes
  -- from a projection record to its block, step `j + 1` to the record's `j`-th reference,
  -- which it must use as a constant.

def walk_path := aiur_fn⟦
  fn walk_path(cur: Bytes::AddressRef, s: Bytes::Stream, n: Field) -> (Bytes::AddressRef, Bytes::Stream) {
      match n {
        0 => {  (cur, s) } ,
        _ => {
          let (st, s2) = get_count(s);
          let c = Ingress::load_verified_constant(cur);
          let next = match st {
            0 => {  projection_block(c) } ,
            _ => {
              match c {
                Ixon::Constant::Mk(_, _, refs, _) => {
                  assert_eq!(KernelClaim::g_list_has(KernelClaim::const_idxs_of(c), st - 1), 1,
                    "model advice: a dependency path step uses an unused reference");
                  Lists::lookup(refs, st - 1) } ,
              } } ,
          };
          walk_path(next, s2, n - 1) } ,
      }
    }
⟧

def projection_block := aiur_fn⟦
  fn projection_block(c: Ixon::Constant) -> Bytes::AddressRef {
      match c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::IPrj(p) => {
              match p { Ixon::InductiveProj::Mk(_, b) => {  b } , } } ,
            Ixon::ConstantInfo::CPrj(p) => {
              match p { Ixon::ConstructorProj::Mk(_, _, b) => {  b } , } } ,
            Ixon::ConstantInfo::RPrj(p) => {
              match p { Ixon::RecursorProj::Mk(_, b) => {  b } , } } ,
            Ixon::ConstantInfo::DPrj(p) => {
              match p { Ixon::DefinitionProj::Mk(_, b) => {  b } , } } ,
          } } ,
      }
    }
⟧

  -- A container's recursor the model uses (`pack_j` is the container's recursor at a
  -- constant motive): a recursor of the block `iblock` in the closure, checked here (the
  -- claim walk does not reach it) by its block's own route, native or modeled. Its
  -- references are checked once the payload's witnessed set is known
  -- (`container_recs_refs`).

def check_container_rec := aiur_fn⟦
  fn check_container_rec(rc: KernelRoles::RoleCtx, x: Bytes::AddressRef, iblock: Bytes::AddressRef) -> () {
      assert_eq!(Bytes::address_eq(rec_family_block(x), iblock), 1,
        "model advice: a container recursor of another block");
      KernelClaim::run_check(rc, x);
      ()
    }
⟧

  -- Every recursor among the outside references: its record (the family record, for a
  -- member of one) uses only its block's references, its block's members, members of
  -- the blocks those references project from, and witnessed outside references (the
  -- closure of the modeled block). So none depends on the modeled block.

def container_recs_refs := aiur_fn⟦
  fn container_recs_refs(xs: Lists::List<Bytes::AddressRef>, wset: RBTreeMap::RBTreeMap<Field>) -> () {
      match (*(xs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(x, rest) => {
          let c0 = Ingress::load_verified_constant(x);
          match c0 {
            Ixon::Constant::Mk(info, _, _, _) => {
              match info {
                Ixon::ConstantInfo::Recr(_) => {  container_refs_check(x, c0, wset) } ,
                Ixon::ConstantInfo::RPrj(_) => {
                  container_refs_check(x, Ingress::load_verified_constant(projection_block(c0)), wset) } ,
                _ => {  () } ,
              } } ,
          };
          container_recs_refs(rest, wset) } ,
      }
    }
⟧

def container_refs_check := aiur_fn⟦
  fn container_refs_check(x: Bytes::AddressRef, c: Ixon::Constant, wset: RBTreeMap::RBTreeMap<Field>) -> () {
      let iblock = rec_family_block(x);
      let ib = Ingress::load_verified_constant(iblock);
      match c {
        Ixon::Constant::Mk(_, _, refs, _) => {
          match ib {
            Ixon::Constant::Mk(_, _, irefs, _) => {
              container_refs_ok(refs, KernelClaim::const_idxs_of(c), 0, iblock, irefs,
                                KernelClaim::const_idxs_of(ib), wset) } ,
          } } ,
      }
    }
⟧

def container_refs_ok := aiur_fn⟦
  fn container_refs_ok(refs: Lists::List<Bytes::AddressRef>, used: Lists::List<Field>, i: Field,
                       iblock: Bytes::AddressRef, irefs: Lists::List<Bytes::AddressRef>,
                       iused: Lists::List<Field>, wset: RBTreeMap::RBTreeMap<Field>) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          match KernelClaim::g_list_has(used, i) {
            1 => {
              let ok = match KernelCheck::addr_list_contains(irefs, r) {
                1 => {  1 } ,
                _ => {
                  match is_projection_of(r, iblock) {
                    1 => {  1 } ,
                    _ => {
                      match projection_of_ref_block(r, irefs, iused) {
                        1 => {  1 } ,
                        _ => {  KernelClaim::addr_set_member(r, wset) } ,
                      } } ,
                  } } ,
              };
              assert_eq!(ok, 1, "model advice: a container recursor references outside its block");
              () } ,
            _ => {  () } ,
          };
          container_refs_ok(rest, used, i + 1, iblock, irefs, iused, wset) } ,
      }
    }
⟧

  -- Is `r` a type or constructor of the block one of `irefs` projects from?

def projection_of_ref_block := aiur_fn⟦
  fn projection_of_ref_block(r: Bytes::AddressRef, irefs: Lists::List<Bytes::AddressRef>,
                             iused: Lists::List<Field>) -> Field {
      let c = Ingress::load_verified_constant(r);
      match c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::IPrj(_) => {  ref_projects_from(irefs, iused, 0, projection_block(c)) } ,
            Ixon::ConstantInfo::CPrj(_) => {  ref_projects_from(irefs, iused, 0, projection_block(c)) } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def ref_projects_from := aiur_fn⟦
  fn ref_projects_from(irefs: Lists::List<Bytes::AddressRef>, iused: Lists::List<Field>, i: Field,
                       block: Bytes::AddressRef) -> Field {
      match (*(irefs)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(q, rest) => {
          let hit = match KernelClaim::g_list_has(iused, i) {
            1 => {  is_projection_of(q, block) } ,
            _ => {  0 } ,
          };
          match hit {
            1 => {  1 } ,
            _ => {  ref_projects_from(rest, iused, i + 1, block) } ,
          } } ,
      }
    }
⟧

def is_projection_of := aiur_fn⟦
  fn is_projection_of(r: Bytes::AddressRef, block: Bytes::AddressRef) -> Field {
      let c = Ingress::load_verified_constant(r);
      match c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::IPrj(_) => {  Bytes::address_eq(projection_block(c), block) } ,
            Ixon::ConstantInfo::CPrj(_) => {  Bytes::address_eq(projection_block(c), block) } ,
            Ixon::ConstantInfo::RPrj(_) => {  Bytes::address_eq(projection_block(c), block) } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

  -- ## The advice records

def check_advice_records := aiur_fn⟦
  fn check_advice_records(rc: KernelRoles::RoleCtx, advice: Lists::List<Bytes::AddressRef>,
                          aset: RBTreeMap::RBTreeMap<Field>, wset: RBTreeMap::RBTreeMap<Field>) -> () {
      match (*(advice)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(a, rest) => {
          check_advice_record(rc, a, aset, wset);
          check_advice_records(rc, rest, aset, wset) } ,
      }
    }
⟧

  -- One advice record, as an ordinary declaration of the kinds the modeller emits: a safe
  -- definition, a theorem, a native inductive block or its recursor, or a projection of
  -- an advice block. Every reference it uses is advice, a projection of an advice block,
  -- or a witnessed outside reference.

def check_advice_record := aiur_fn⟦
  fn check_advice_record(rc: KernelRoles::RoleCtx, a: Bytes::AddressRef,
                         aset: RBTreeMap::RBTreeMap<Field>, wset: RBTreeMap::RBTreeMap<Field>) -> () {
      let c = Ingress::load_verified_constant(a);
      match c {
        Ixon::Constant::Mk(info, _, refs, _) => {
          match info {
            Ixon::ConstantInfo::Defn(d) => {
              match d {
                Ixon::Definition::Mk(kind, safety, _, _, _) => {
                  let kind_ok = match kind {
                    Ixon::DefKind::Definition => {
                      match safety {
                        Ixon::DefinitionSafety::Safe => {  1 } ,
                        _ => {  0 } ,
                      } } ,
                    Ixon::DefKind::Theorem => {  1 } ,
                    Ixon::DefKind::Opaque => {  0 } ,
                  };
                  assert_eq!(kind_ok, 1, "model advice: an opaque, unsafe or partial definition");
                  KernelClaim::run_check(rc, a) } ,
              } } ,
            Ixon::ConstantInfo::Recr(r) => {
              match r {
                Ixon::Recursor::Mk(_, is_unsafe, _, _, _, _, _, _, _) => {
                  assert_eq!(is_unsafe, 0, "model advice: an unsafe recursor");
                  () } ,
              };
              assert_eq!(block_is_modeled(rec_family_block(a)), 0,
                "model advice: a recursor of a modeled block");
              KernelClaim::run_check(rc, a) } ,
            Ixon::ConstantInfo::Muts(members) => {
              assert_eq!(muts_indc_count(members), Lists::length(members),
                "model advice: a block that is not inductive");
              assert_eq!(block_is_modeled(a), 0, "model advice: a mutual or nested inductive");
              assert_eq!(muts_all_safe(members), 1, "model advice: an unsafe inductive");
              KernelClaim::check_muts_all(rc, a, members, members, 0) } ,
            Ixon::ConstantInfo::IPrj(_) => {
              assert_eq!(KernelClaim::addr_set_member(projection_block(c), aset), 1,
                "model advice: a projection of a block that is not advice");
              () } ,
            Ixon::ConstantInfo::CPrj(_) => {
              assert_eq!(KernelClaim::addr_set_member(projection_block(c), aset), 1,
                "model advice: a projection of a block that is not advice");
              () } ,
          };
          advice_refs_ok(refs, KernelClaim::const_idxs_of(c), 0, aset, wset) } ,
      }
    }
⟧

def muts_all_safe := aiur_fn⟦
  fn muts_all_safe(members: Lists::List<Ixon::MutConst>) -> Field {
      match (*(members)) {
        Lists::Node::Nil => {  1 } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Indc(ind) => {
              match ind {
                Ixon::Inductive::Mk(is_unsafe, _, _, _, _, _) => {
                  match is_unsafe {
                    0 => {  muts_all_safe(rest) } ,
                    _ => {  0 } ,
                  } } ,
              } } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def advice_refs_ok := aiur_fn⟦
  fn advice_refs_ok(refs: Lists::List<Bytes::AddressRef>, used: Lists::List<Field>, i: Field,
                    aset: RBTreeMap::RBTreeMap<Field>, wset: RBTreeMap::RBTreeMap<Field>) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          match KernelClaim::g_list_has(used, i) {
            1 => {
              let ok = match KernelClaim::addr_set_member(r, aset) {
                1 => {  1 } ,
                _ => {
                  match KernelClaim::addr_set_member(r, wset) {
                    1 => {  1 } ,
                    _ => {  projection_of_advice(r, aset) } ,
                  } } ,
              };
              assert_eq!(ok, 1, "model advice: an unwitnessed outside reference");
              () } ,
            _ => {  () } ,
          };
          advice_refs_ok(rest, used, i + 1, aset, wset) } ,
      }
    }
⟧

def projection_of_advice := aiur_fn⟦
  fn projection_of_advice(r: Bytes::AddressRef, aset: RBTreeMap::RBTreeMap<Field>) -> Field {
      let c = Ingress::load_verified_constant(r);
      match c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::IPrj(_) => {  KernelClaim::addr_set_member(projection_block(c), aset) } ,
            Ixon::ConstantInfo::CPrj(_) => {  KernelClaim::addr_set_member(projection_block(c), aset) } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

  -- ## The family: members against their models

  -- A type or constructor of a modeled block: validated with the recursor family its
  -- payload names.

def check_modeled_block := aiur_fn⟦
  fn check_modeled_block(rc: KernelRoles::RoleCtx, block: Bytes::AddressRef) -> () {
      let (rb, _) = IxonDeserialize::get_address(read_payload(block));
      check_family(rc, block, rb)
    }
⟧

  -- The whole family against one payload: the advice records, then every type,
  -- constructor and recursor against its model (`checkMemberVal`), and every rule
  -- against its `iota_j` theorem (`checkIotaRule`).

def check_family := aiur_fn⟦
  fn check_family(rc: KernelRoles::RoleCtx, block: Bytes::AddressRef, rec_block: Bytes::AddressRef) -> () {
      let s0 = read_payload(block);
      let (rb, s1) = IxonDeserialize::get_address(s0);
      assert_eq!(Bytes::address_eq(rb, rec_block), 1,
        "model advice: the payload names another recursor family");
      let (n_a, s2) = get_count(s1);
      let (advice, s3) = get_addrs(s2, n_a);
      let aset = KernelClaim::addr_set_build(advice, RBTreeMap::RBTreeMap::Nil);
      let (n_w, s4) = get_count(s3);
      let (outside, s5) = check_witnesses(rc, block, s4, n_w);
      let wset = KernelClaim::addr_set_build(outside, RBTreeMap::RBTreeMap::Nil);
      container_recs_refs(outside, wset);
      check_advice_records(rc, advice, aset, wset);
      let bc = Ingress::load_verified_constant(block);
      match bc {
        Ixon::Constant::Mk(binfo, _, _, _) => {
          match binfo {
            Ixon::ConstantInfo::Muts(members) => {
              let n_types = Lists::length(members);
              assert_eq!(muts_indc_count(members), n_types,
                "modeled block: a member that is not an inductive");
              let np = block_nparams(members);
              let type_addrs = Ingress::build_recur_addrs(members, block);
              let (type_models, s6) = get_addrs(s5, n_types);
              let ctor_addrs = block_ctor_addrs(members, block, 0);
              let (ctor_models, s7) = get_addrs(s6, Lists::length(ctor_addrs));
              let rec_addrs = family_recs(rec_block);
              let n_recs = Lists::length(rec_addrs);
              let (rec_models, s8) = get_addrs(s7, n_recs);
              let src = Lists::concat(type_addrs, Lists::concat(ctor_addrs, rec_addrs));
              let dst = Lists::concat(type_models, Lists::concat(ctor_models, rec_models));
              members_val(type_addrs, type_models, src, dst, aset);
              members_val(ctor_addrs, ctor_models, src, dst, aset);
              members_val(rec_addrs, rec_models, src, dst, aset);
              let s9 = check_recs(rc, type_addrs, rec_addrs, rec_models, src, dst, aset, s8,
                                  n_recs, 0, np);
              let Lists::Node::Nil = (*(s9));
              () } ,
          } } ,
      }
    }
⟧

def block_nparams := aiur_fn⟦
  fn block_nparams(members: Lists::List<Ixon::MutConst>) -> Field {
      match (*(members)) {
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Indc(ind) => {
              match ind {
                Ixon::Inductive::Mk(_, _, params, _, _, _) => {
                  let np = UInt64::to_field(params);
                  assert_eq!(nparams_agree(rest, np), 1,
                    "modeled block: types disagree on the parameter count");
                  np } ,
              } } ,
          } } ,
      }
    }
⟧

def nparams_agree := aiur_fn⟦
  fn nparams_agree(members: Lists::List<Ixon::MutConst>, np: Field) -> Field {
      match (*(members)) {
        Lists::Node::Nil => {  1 } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Indc(ind) => {
              match ind {
                Ixon::Inductive::Mk(_, _, params, _, _, _) => {
                  match UInt64::to_field(params) - np {
                    0 => {  nparams_agree(rest, np) } ,
                    _ => {  0 } ,
                  } } ,
              } } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

  -- The constructors' projection addresses, by member then constructor index.

def block_ctor_addrs := aiur_fn⟦
  fn block_ctor_addrs(members: Lists::List<Ixon::MutConst>, block: Bytes::AddressRef, pos: Field)
        -> Lists::List<Bytes::AddressRef> {
      match (*(members)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Indc(ind) => {
              match ind {
                Ixon::Inductive::Mk(_, _, _, _, _, ctors) => {
                  Lists::concat(member_ctor_addrs(block, pos, Lists::length(ctors), 0),
                                block_ctor_addrs(rest, block, pos + 1)) } ,
              } } ,
          } } ,
      }
    }
⟧

def member_ctor_addrs := aiur_fn⟦
  fn member_ctor_addrs(block: Bytes::AddressRef, pos: Field, n: Field, j: Field)
        -> Lists::List<Bytes::AddressRef> {
      match n - j {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {
          (&(Lists::Node::Cons(KernelCheck::projection_addr_ctor(pos, j, block),
                                member_ctor_addrs(block, pos, n, j + 1)))) } ,
      }
    }
⟧

  -- The members of a recursor family record: a `muts` of recursors only, or a singleton
  -- recursor.

def family_recs := aiur_fn⟦
  fn family_recs(rec_block: Bytes::AddressRef) -> Lists::List<Bytes::AddressRef> {
      let c = Ingress::load_verified_constant(rec_block);
      match c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              assert_eq!(muts_recr_count(members), Lists::length(members),
                "modeled recursor family: a member that is not a recursor");
              Ingress::build_recur_addrs(members, rec_block) } ,
            Ixon::ConstantInfo::Recr(_) => {
              (&(Lists::Node::Cons(rec_block, (&(Lists::Node::Nil))))) } ,
          } } ,
      }
    }
⟧

def muts_recr_count := aiur_fn⟦
  fn muts_recr_count(members: Lists::List<Ixon::MutConst>) -> Field {
      match (*(members)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Recr(_) => {  muts_recr_count(rest) + 1 } ,
            _ => {  muts_recr_count(rest) } ,
          } } ,
      }
    }
⟧

def members_val := aiur_fn⟦
  fn members_val(members: Lists::List<Bytes::AddressRef>, models: Lists::List<Bytes::AddressRef>,
                 src: Lists::List<Bytes::AddressRef>, dst: Lists::List<Bytes::AddressRef>,
                 aset: RBTreeMap::RBTreeMap<Field>) -> () {
      match (*(members)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(m, rest) => {
          let Lists::Node::Cons(md, mrest) = (*(models));
          member_val(m, md, src, dst, aset);
          members_val(rest, mrest, src, dst, aset) } ,
      }
    }
⟧

  -- `checkMemberVal`: the model is an advice definition at the member's level count,
  -- whose type is the member's under the block renaming, structurally.

def member_val := aiur_fn⟦
  fn member_val(member: Bytes::AddressRef, model: Bytes::AddressRef,
                src: Lists::List<Bytes::AddressRef>, dst: Lists::List<Bytes::AddressRef>,
                aset: RBTreeMap::RBTreeMap<Field>) -> () {
      assert_eq!(KernelClaim::addr_set_member(model, aset), 1, "model advice: a model that is not advice");
      let (nl, ty) = ci_lvls_type((*(Ingress::get_ci(member))));
      match (*(Ingress::get_ci(model))) {
        KernelTypes::KConstantInfo::Defn(nlm, mty, _, _, _) => {
          assert_eq!(nl, nlm, "model level parameters mismatch");
          assert_eq!(KernelCheck::kexpr_struct_eq(rename(ty, src, dst), mty), 1,
            "model type mismatch");
          () } ,
      }
    }
⟧

def ci_lvls_type := aiur_fn⟦
  fn ci_lvls_type(ci: KernelTypes::KConstantInfo) -> (Field, KernelTypes::KExpr) {
      match ci {
        KernelTypes::KConstantInfo::Induct(nl, ty, _, _, _, _, _, _) => {  (nl, ty) } ,
        KernelTypes::KConstantInfo::Ctor(nl, ty, _, _, _, _, _, _) => {  (nl, ty) } ,
        KernelTypes::KConstantInfo::Rec(nl, ty, _, _, _, _, _, _, _, _, _) => {  (nl, ty) } ,
      }
    }
⟧

  -- The block renaming: every member of the block and of its recursor family to its model.

def rename := aiur_fn⟦
  fn rename(e: KernelTypes::KExpr, src: Lists::List<Bytes::AddressRef>,
            dst: Lists::List<Bytes::AddressRef>) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::Const(a, ls) => {
          (&(KernelTypes::KExprNode::Const(rename_addr(a, src, dst), ls))) } ,
        KernelTypes::KExprNode::App(f, x) => {
          (&(KernelTypes::KExprNode::App(rename(f, src, dst), rename(x, src, dst)))) } ,
        KernelTypes::KExprNode::Lam(t, b) => {
          (&(KernelTypes::KExprNode::Lam(rename(t, src, dst), rename(b, src, dst)))) } ,
        KernelTypes::KExprNode::Forall(t, b) => {
          (&(KernelTypes::KExprNode::Forall(rename(t, src, dst), rename(b, src, dst)))) } ,
        KernelTypes::KExprNode::Let(t, v, b) => {
          (&(KernelTypes::KExprNode::Let(rename(t, src, dst), rename(v, src, dst),
                                          rename(b, src, dst)))) } ,
        KernelTypes::KExprNode::Proj(s, i, x) => {
          (&(KernelTypes::KExprNode::Proj(rename_addr(s, src, dst), i, rename(x, src, dst)))) } ,
        _ => {  e } ,
      }
    }
⟧

def rename_addr := aiur_fn⟦
  fn rename_addr(a: Bytes::AddressRef, src: Lists::List<Bytes::AddressRef>,
                 dst: Lists::List<Bytes::AddressRef>) -> Bytes::AddressRef {
      match (*(src)) {
        Lists::Node::Nil => {  a } ,
        Lists::Node::Cons(f, frest) => {
          let Lists::Node::Cons(t, trest) = (*(dst));
          match Bytes::address_eq(a, f) {
            1 => {  t } ,
            _ => {  rename_addr(a, frest, trest) } ,
          } } ,
      }
    }
⟧

def rename_list := aiur_fn⟦
  fn rename_list(es: Lists::List<KernelTypes::KExpr>, src: Lists::List<Bytes::AddressRef>,
                 dst: Lists::List<Bytes::AddressRef>) -> Lists::List<KernelTypes::KExpr> {
      match (*(es)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(e, rest) => {
          (&(Lists::Node::Cons(rename(e, src, dst), rename_list(rest, src, dst)))) } ,
      }
    }
⟧

  -- ## The family: recursors and their rules

  -- Each member of the family record: no K, the block's parameter count, one motive per
  -- member (a complete family), eliminating motive `k` at position `k`, its first
  -- motives' carriers the block's types in order; then its rules.

def check_recs := aiur_fn⟦
  fn check_recs(rc: KernelRoles::RoleCtx, type_addrs: Lists::List<Bytes::AddressRef>,
                recs: Lists::List<Bytes::AddressRef>, models: Lists::List<Bytes::AddressRef>,
                src: Lists::List<Bytes::AddressRef>, dst: Lists::List<Bytes::AddressRef>,
                aset: RBTreeMap::RBTreeMap<Field>, s: Bytes::Stream,
                n_recs: Field, k: Field, np: Field) -> Bytes::Stream {
      match (*(recs)) {
        Lists::Node::Nil => {  s } ,
        Lists::Node::Cons(r, rest) => {
          let Lists::Node::Cons(rm, mrest) = (*(models));
          match (*(Ingress::get_ci(r))) {
            KernelTypes::KConstantInfo::Rec(nl, ty, rnp, ni, nmot, nmin, rules, kf, _, _, _) => {
              assert_eq!(kf, 0, "modeled recursor declares K");
              assert_eq!(rnp, np, "modeled recursor parameter count differs from its block's");
              assert_eq!(nmot, n_recs, "modeled recursor family record is not one complete family");
              assert_eq!(UInt32::less_than_fields(1, nmot), 1,
                "a modeled recursor family with one motive");
              assert_eq!(UInt32::less_than_fields(Lists::length(type_addrs), nmot + 1), 1,
                "modeled recursor has fewer motives than its block has types");
              check_rec_motive(ty, (((rnp + nmot) + nmin) + ni) + 1, rnp + k);
              check_carriers(ty, rnp, type_addrs);
              let s2 = check_rules(rc, rm, nl, ty, rnp + nmot + nmin, ni, rules, src, dst, aset, s);
              check_recs(rc, type_addrs, rest, mrest, src, dst, aset, s2, n_recs, k + 1, np) } ,
          } } ,
      }
    }
⟧

def check_rec_motive := aiur_fn⟦
  fn check_rec_motive(ty: KernelTypes::KExpr, depth: Field, motive_pos: Field) -> () {
      let body = KernelCheck::peel_n_foralls(ty, depth);
      let (head, _) = KernelTypes::collect_spine(body);
      match (*(head)) {
        KernelTypes::KExprNode::BVar(j) => {
          assert_eq!(j, (depth - 1) - motive_pos, "modeled recursor eliminates another motive");
          () } ,
      }
    }
⟧

def check_carriers := aiur_fn⟦
  fn check_carriers(ty: KernelTypes::KExpr, np: Field, type_addrs: Lists::List<Bytes::AddressRef>) -> () {
      check_carriers_go(KernelCheck::peel_n_foralls(ty, np), type_addrs)
    }
⟧

def check_carriers_go := aiur_fn⟦
  fn check_carriers_go(e: KernelTypes::KExpr, type_addrs: Lists::List<Bytes::AddressRef>) -> () {
      match (*(type_addrs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(t, rest) => {
          match (*(e)) {
            KernelTypes::KExprNode::Forall(mdom, body) => {
              let (head, _) = KernelTypes::collect_spine(last_binder_dom(mdom));
              match (*(head)) {
                KernelTypes::KExprNode::Const(c, _) => {
                  assert_eq!(Bytes::address_eq(c, t), 1,
                    "modeled recursor: a motive's carrier is not the block's type");
                  check_carriers_go(body, rest) } ,
              } } ,
          } } ,
      }
    }
⟧

def check_rules := aiur_fn⟦
  fn check_rules(rc: KernelRoles::RoleCtx, rm: Bytes::AddressRef, nl: Field, ty: KernelTypes::KExpr,
                 rp: Field, ni: Field, rules: Lists::List<KernelTypes::KRecRule>,
                 src: Lists::List<Bytes::AddressRef>, dst: Lists::List<Bytes::AddressRef>,
                 aset: RBTreeMap::RBTreeMap<Field>, s: Bytes::Stream) -> Bytes::Stream {
      let (iaddr, ilvls, pins) = rec_major_pins(ty, rp, ni);
      match (*(Ingress::get_ci(iaddr))) {
        KernelTypes::KConstantInfo::Induct(_, _, inp, _, inct, _, iblock, iidx) => {
          assert_eq!(Lists::length(rules), inct,
            "recursor rule count differs from its major's constructor count");
          check_rules_go(rc, rm, nl, ty, rp, ni, rules, iblock, iidx, inp, ilvls, pins,
                         src, dst, aset, s, 0) } ,
      }
    }
⟧

def check_rules_go := aiur_fn⟦
  fn check_rules_go(rc: KernelRoles::RoleCtx, rm: Bytes::AddressRef, nl: Field, ty: KernelTypes::KExpr,
                    rp: Field, ni: Field, rules: Lists::List<KernelTypes::KRecRule>,
                    iblock: Bytes::AddressRef, iidx: Field, inp: Field,
                    ilvls: Lists::List<KernelTypes::KLevel>, pins: Lists::List<KernelTypes::KExpr>,
                    src: Lists::List<Bytes::AddressRef>, dst: Lists::List<Bytes::AddressRef>,
                    aset: RBTreeMap::RBTreeMap<Field>, s: Bytes::Stream, j: Field) -> Bytes::Stream {
      match (*(rules)) {
        Lists::Node::Nil => {  s } ,
        Lists::Node::Cons(rule, rest) => {
          let (t, s2) = IxonDeserialize::get_address(s);
          match rule {
            KernelTypes::KRecRule::Mk(_, rnf, rhs) => {
              let cprj = KernelCheck::projection_addr_ctor(iidx, j, iblock);
              match (*(Ingress::get_ci(cprj))) {
                KernelTypes::KConstantInfo::Ctor(_, cty, _, _, _, cnp, cnf, _) => {
                  assert_eq!(cnp, inp, "constructor parameter count differs from its inductive's");
                  assert_eq!(rnf, cnf, "rule field count mismatch");
                  check_iota_rule(rc, rm, nl, ty, rp, ni, rhs, cprj, cty, cnp, cnf, ilvls, pins,
                                  t, src, dst, aset) } ,
              } } ,
          };
          check_rules_go(rc, rm, nl, ty, rp, ni, rest, iblock, iidx, inp, ilvls, pins,
                         src, dst, aset, s2, j + 1) } ,
      }
    }
⟧

  -- `checkIotaRule` with `checkIotaThm`/`checkIotaThmN` (`Modeled.lean`), in one form: the
  -- canonical rule's parameter comparands are the prefix variables, a nested rule's the
  -- stored instantiations; both are `pins`, the major domain's parameter arguments.

def check_iota_rule := aiur_fn⟦
  fn check_iota_rule(rc: KernelRoles::RoleCtx, rm: Bytes::AddressRef, nl: Field, ty_r: KernelTypes::KExpr,
                     rp: Field, ni: Field, rhs: KernelTypes::KExpr,
                     cprj: Bytes::AddressRef, cty: KernelTypes::KExpr, cnp: Field, cnf: Field,
                     ilvls: Lists::List<KernelTypes::KLevel>, pins: Lists::List<KernelTypes::KExpr>,
                     t: Bytes::AddressRef,
                     src: Lists::List<Bytes::AddressRef>, dst: Lists::List<Bytes::AddressRef>,
                     aset: RBTreeMap::RBTreeMap<Field>) -> () {
      let mi = rp + ni;
      let d = rp + cnf;
      assert_eq!(Lists::length(pins), cnp, "major premise parameter count");
      -- the stored rule: closed, a λ-telescope over the prefix and the fields, typable
      KernelCheck::validate_expr_well_scoped(rhs, 0, nl);
      let (_, peeled, _) = KernelCheck::peel_n_lams_collect(rhs, d, 0, (&(Lists::Node::Nil)));
      assert_eq!(peeled, d, "rule shape mismatch");
      KernelInfer::k_infer(rc, rhs, (&(Lists::Node::Nil)));
      -- the theorem: an advice theorem at the recursor's levels
      assert_eq!(KernelClaim::addr_set_member(t, aset), 1, "iota theorem is not advice");
      match (*(Ingress::get_ci(t))) {
        KernelTypes::KConstantInfo::Thm(tnl, tty, _) => {
          assert_eq!(tnl, nl, "iota theorem level mismatch");
          let (tbody, ctx) = peel_collect(tty, d, (&(Lists::Node::Nil)));
          let (eqh, targs) = KernelTypes::collect_spine(tbody);
          match (*(eqh)) {
            KernelTypes::KExprNode::Const(eqa, eqls) => {
              assert_eq!(Bytes::address_eq(eqa, KernelRoles::role_addr(rc, KernelRoleSpec::role_eq())), 1,
                "iota statement not an equation");
              let Lists::Node::Cons(ell, eqrest) = (*(eqls));
              let Lists::Node::Nil = (*(eqrest));
              assert_eq!(Lists::length(targs), 3, "iota statement not an equation");
              let alpha = Lists::lookup(targs, 0);
              let lhs = Lists::lookup(targs, 1);
              let rhs_s = Lists::lookup(targs, 2);
              -- the left side: the renamed recursor at its own levels, the prefix variables,
              -- the index arguments, and the constructor at the comparands and the fields
              let (lh, largs) = KernelTypes::collect_spine(lhs);
              let rhead = (&(KernelTypes::KExprNode::Const(rm, KernelCheck::build_param_lvls_range(0, nl, 0))));
              assert_eq!(KernelCheck::kexpr_struct_eq(lh, rhead), 1, "iota statement head mismatch");
              assert_eq!(Lists::length(largs), mi + 1, "iota statement arity mismatch");
              assert_eq!(KernelCheck::spec_params_ptr_eq(Lists::take(largs, rp), bvars_desc(d, rp)), 1,
                "iota statement prefix mismatch");
              let major = Lists::lookup(largs, mi);
              let cren = rename_addr(cprj, src, dst);
              let pins_ren = rename_list(pins, src, dst);
              let pins_d = lift_list(pins_ren, cnf);
              let expected = KernelWhnf::apply_spine((&(KernelTypes::KExprNode::Const(cren, ilvls))),
                Lists::concat(pins_d, bvars_desc(cnf, cnf)));
              assert_eq!(KernelCheck::kexpr_struct_eq(major, expected), 1, "iota statement major mismatch");
              -- the constructor's telescope at the comparands (renamed): its fields and the
              -- canonical index tuple
              let cty_l = KernelLevels::expr_inst_levels(cty, ilvls);
              let crest = inst_params(rename(cty_l, src, dst), pins_ren);
              let (cres, _) = peel_collect(crest, cnf, (&(Lists::Node::Nil)));
              let (chead, cargs) = KernelTypes::collect_spine(cres);
              match (*(chead)) {
                KernelTypes::KExprNode::Const(_, _) => {  () } ,
              };
              assert_eq!(Lists::length(cargs), cnp + ni, "iota constructor indices");
              assert_eq!(defeq_list_ok(rc, Lists::take(Lists::drop(largs, rp), ni), Lists::drop(cargs, cnp), ctx), 1,
                "iota statement index mismatch");
              -- the statement's domains: the renamed recursor's prefix, the constructor's fields
              defeq_tele(rc, tty, rename(ty_r, src, dst), rp, (&(Lists::Node::Nil)));
              defeq_tele(rc, KernelCheck::peel_n_foralls(tty, rp), crest, cnf, Lists::drop(ctx, cnf));
              -- the public side: the comparands inhabit the constructor's parameter domains,
              -- and the rule's λ-domains are the recursor's prefix and the fields
              let (_, ctx_p) = peel_collect(ty_r, rp, (&(Lists::Node::Nil)));
              let crest_p = inst_params_typed(rc, cty_l, pins, ctx_p);
              let (rhs_rp, lctx) = defeq_lam_tele(rc, rhs, ty_r, rp, (&(Lists::Node::Nil)));
              let (_, _) = defeq_lam_tele(rc, rhs_rp, crest_p, cnf, lctx);
              -- the right side: the rule applied to the opened variables
              let rhs_app = KernelWhnf::apply_spine(rename(rhs, src, dst), bvars_desc(d, d));
              assert_eq!(KernelDefEq::k_is_def_eq(rc, rhs_s, rhs_app, ctx), 1, "iota statement mismatch");
              -- both sides inhabit the equation's type slot, the slot the equation's sort
              let tl = KernelInfer::k_infer(rc, lhs, ctx);
              assert_eq!(KernelDefEq::k_is_def_eq(rc, tl, alpha, ctx), 1, "iota statement lhs type");
              let tr = KernelInfer::k_infer(rc, rhs_s, ctx);
              assert_eq!(KernelDefEq::k_is_def_eq(rc, tr, alpha, ctx), 1, "iota statement rhs type");
              let ta = KernelInfer::k_infer(rc, alpha, ctx);
              assert_eq!(KernelDefEq::k_is_def_eq(rc, ta, (&(KernelTypes::KExprNode::Srt(ell))), ctx), 1,
                "iota statement type slot sort");
              () } ,
          } } ,
      }
    }
⟧

  -- Peel `n` leading `∀`s, collecting their domains, innermost first, onto `ctx`.

def peel_collect := aiur_fn⟦
  fn peel_collect(e: KernelTypes::KExpr, n: Field, ctx: Lists::List<KernelTypes::KExpr>)
        -> (KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>) {
      match n {
        0 => {  (e, ctx) } ,
        _ => {
          match (*(e)) {
            KernelTypes::KExprNode::Forall(d, b) => {
              peel_collect(b, n - 1, (&(Lists::Node::Cons(d, ctx)))) } ,
          } } ,
      }
    }
⟧

  -- `[BVar(top - 1), …, BVar(top - n)]`.

def bvars_desc := aiur_fn⟦
  fn bvars_desc(top: Field, n: Field) -> Lists::List<KernelTypes::KExpr> {
      match n {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {
          (&(Lists::Node::Cons((&(KernelTypes::KExprNode::BVar(top - 1))),
                                bvars_desc(top - 1, n - 1)))) } ,
      }
    }
⟧

def lift_list := aiur_fn⟦
  fn lift_list(es: Lists::List<KernelTypes::KExpr>, shift: Field) -> Lists::List<KernelTypes::KExpr> {
      match (*(es)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(e, rest) => {
          (&(Lists::Node::Cons(KernelSubst::expr_lift(e, shift, 0), lift_list(rest, shift)))) } ,
      }
    }
⟧

  -- Instantiate a constructor type's leading parameter binders at `pins`, terms of the
  -- context the result lives in.

def inst_params := aiur_fn⟦
  fn inst_params(e: KernelTypes::KExpr, pins: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(pins)) {
        Lists::Node::Nil => {  e } ,
        Lists::Node::Cons(p, rest) => {
          match (*(e)) {
            KernelTypes::KExprNode::Forall(_, b) => {
              inst_params(KernelSubst::expr_inst1(b, p, 0), rest) } ,
          } } ,
      }
    }
⟧

  -- `inst_params`, checking each comparand against its parameter domain.

def inst_params_typed := aiur_fn⟦
  fn inst_params_typed(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, pins: Lists::List<KernelTypes::KExpr>,
                       ctx: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(pins)) {
        Lists::Node::Nil => {  e } ,
        Lists::Node::Cons(p, rest) => {
          match (*(e)) {
            KernelTypes::KExprNode::Forall(dom, b) => {
              let pt = KernelInfer::k_infer(rc, p, ctx);
              assert_eq!(KernelDefEq::k_is_def_eq(rc, pt, dom, ctx), 1, "nested pin type mismatch");
              inst_params_typed(rc, KernelSubst::expr_inst1(b, p, 0), rest, ctx) } ,
          } } ,
      }
    }
⟧

  -- The first `n` domains of two `∀`-telescopes are pairwise definitionally equal, each
  -- under the first telescope's earlier domains.

def defeq_tele := aiur_fn⟦
  fn defeq_tele(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, n: Field,
                ctx: Lists::List<KernelTypes::KExpr>) -> () {
      match n {
        0 => {  () } ,
        _ => {
          match (*(a)) {
            KernelTypes::KExprNode::Forall(da, ba) => {
              match (*(b)) {
                KernelTypes::KExprNode::Forall(db, bb) => {
                  assert_eq!(KernelDefEq::k_is_def_eq(rc, da, db, ctx), 1, "iota statement domain mismatch");
                  defeq_tele(rc, ba, bb, n - 1, (&(Lists::Node::Cons(da, ctx)))) } ,
              } } ,
          } } ,
      }
    }
⟧

  -- A `λ`-telescope's first `n` domains against a `∀`-telescope's; returns the body and
  -- the extended context.

def defeq_lam_tele := aiur_fn⟦
  fn defeq_lam_tele(rc: KernelRoles::RoleCtx, l: KernelTypes::KExpr, p: KernelTypes::KExpr, n: Field,
                    ctx: Lists::List<KernelTypes::KExpr>) -> (KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>) {
      match n {
        0 => {  (l, ctx) } ,
        _ => {
          match (*(l)) {
            KernelTypes::KExprNode::Lam(dl, bl) => {
              match (*(p)) {
                KernelTypes::KExprNode::Forall(dp, bp) => {
                  assert_eq!(KernelDefEq::k_is_def_eq(rc, dl, dp, ctx), 1, "rule domain mismatch");
                  defeq_lam_tele(rc, bl, bp, n - 1, (&(Lists::Node::Cons(dl, ctx)))) } ,
              } } ,
          } } ,
      }
    }
⟧

end

end IxVM
