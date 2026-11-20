import Aiur.Modules.Function

/-! # IxVM module `KernelModeled`

The modeled route for inductive declarations: IxVM checks a mutual or
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
  `proj_ctor`, `proj_allowed_at`, `block_is_modeled` and `fire_ok`: `.proj` is allowed on
  native blocks and on 1-constructor, 0-index, never-zero-sort members of modeled blocks
  whose projection models are checked by `check_projs`; structure eta and unit-like
  conversion stay restricted to non-recursive native blocks; and the iota step of a modeled
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
    projection models      -- per projection-eligible member (in position order) and per
                           --   field `i`, the pair `(proj_i, proj_i.iota)`

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
        Ixon::Constant::Mk(info, _, _, _, _) => {
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
        Ixon::Constant::Mk(info, _, _, _, _) => {
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
        KernelTypes::KExprNode::Lam(t, b, _) => {
          match nested_scan(t, mems) {
            1 => {  1 } ,
            _ => {  nested_scan(b, mems) } ,
          } } ,
        KernelTypes::KExprNode::Forall(t, b, _) => {
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
            KernelTypes::KExprNode::Forall(mdom, _, _) => {
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
        KernelTypes::KExprNode::Forall(d, b, _) => {
          match (*(b)) {
            KernelTypes::KExprNode::Forall(_, _, _) => {  last_binder_dom(b) } ,
            _ => {  d } ,
          } } ,
      }
    }
⟧

  -- ## Use sites

  -- Legacy gate kept for observation name stability.

def assert_proj_allowed := aiur_fn⟦
  fn assert_proj_allowed(block: Bytes::AddressRef) -> () {
      assert_eq!(block_is_modeled(block), 0,
        "projection on a member of a mutual or nested block");
      ()
    }
⟧

  -- The structure's constructor, at a native block or a projection-eligible member of a
  -- modeled block: the projection sites call this in place of `Ingress::get_ci_cprj`,
  -- memoized per structure.

def proj_ctor := aiur_fn⟦
  fn proj_ctor(block: Bytes::AddressRef, ind_idx: Field) -> &KernelTypes::KConstantInfo {
      assert_eq!(proj_allowed_at(block, ind_idx), 1,
        "projection on a member of a mutual or nested block");
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
        KernelTypes::KExprNode::Forall(dom, _, _) => {
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
  -- `Eq.refl`, `Eq.rec`, `PUnit`, `PUnit.unit`, `PUnit.rec`, the quotient (`Quot`,
  -- `Quot.mk`, `Quot.lift`, `Quot.ind`, `Quot.sound`: function extensionality, along
  -- which the model of a block with a nested occurrence under a binder transports, is a
  -- theorem from them). No other axiom. Each is walked when a validation checks its group,
  -- or is a quotient role; an anchor such as `String` or `Char` is witnessed by a
  -- dependency path instead.

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
        32 => {  1 } ,
        33 => {  1 } ,
        34 => {  1 } ,
        35 => {  1 } ,
        36 => {  1 } ,
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
          -- a witnessed reference is reached through the payload, past every `walk_ctx`
          KernelRoles::assert_in_order(rc, x);
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
          -- the role's record is checked with its closure, as an implicitly used role's is
          -- (`KernelRoles::role_used_implicitly`): under a custom table a basis role may be bound
          -- to any record
          KernelClaim::run_check_transitive(rc, x);
          s } ,
        1 => {
          let (n, s2) = get_count(s);
          let (stop, s3, passed) = walk_from_block(rc, block, s2, n);
          assert_eq!(Bytes::address_eq(stop, x), 1, "model advice: a dependency path ends elsewhere");
          -- a projection the path ends at names a member of its block
          projection_member(x);
          -- and the stop is no block record and is read whatever its kind (a family check nested in
          -- a payload check may be of a block no walk reaches, so nothing else loads it)
          KernelClaim::assert_not_block_ref(x);
          Ingress::get_ci(x);
          assert_covered_past(rc, passed, x);
          s3 } ,
        2 => {
          let (n, s2) = get_count(s);
          let (iblock, s3, passed) = walk_from_block(rc, block, s2, n);
          check_container_rec(rc, x, iblock);
          assert_covered_past(rc, passed, x);
          s3 } ,
        3 => {
          let (n, s2) = get_count(s);
          let (iblock, s3, passed) = walk_from_block(rc, block, s2, n);
          let (idx, s4) = get_count(s3);
          let (c1, s5) = get_count(s4);
          let expected = match c1 {
            0 => {  KernelDefEq::compute_iprj_addr(iblock, idx) } ,
            _ => {  KernelCheck::projection_addr_ctor(idx, c1 - 1, iblock) } ,
          };
          assert_eq!(Bytes::address_eq(expected, x), 1,
            "model advice: a projection witness names another member");
          -- the address is computed from the indices; the record's reading checks that they
          -- name a member (and a constructor) of the block
          Ingress::get_ci(x);
          assert_covered_past(rc, passed, x);
          s5 } ,
      }
    }
⟧

  -- A projection record names a member of its block: its reading (`Ingress::get_ci`) refuses
  -- a missing member, a member of another kind and a missing constructor. Any other record is
  -- left as it is. A witnessed reference or an advice record is admitted with this read, so
  -- that a projection admitted from either set names a member.

def projection_member := aiur_fn⟦
  fn projection_member(x: Bytes::AddressRef) -> () {
      let c = Ingress::load_verified_constant(x);
      match c {
        Ixon::Constant::Mk(info, _, _, _, _) => {
          match info {
            Ixon::ConstantInfo::IPrj(_) => {  Ingress::get_ci(x); () } ,
            Ixon::ConstantInfo::CPrj(_) => {  Ingress::get_ci(x); () } ,
            Ixon::ConstantInfo::RPrj(_) => {  Ingress::get_ci(x); () } ,
            Ixon::ConstantInfo::DPrj(_) => {  Ingress::get_ci(x); () } ,
            _ => {  () } ,
          } } ,
      }
    }
⟧

  -- A path of one step or more from the block: what it reaches is in the block's
  -- dependency closure, which by content addressing cannot contain the block.

def walk_from_block := aiur_fn⟦
  fn walk_from_block(rc: KernelRoles::RoleCtx, block: Bytes::AddressRef, s: Bytes::Stream, n: Field)
        -> (Bytes::AddressRef, Bytes::Stream, Field) {
      assert_eq!(Fields::is_zero(n), 0, "model advice: an empty dependency path");
      walk_path(rc, block, s, n, 0)
    }
⟧

  -- A path through the dependency closure the claim walk visits from `cur`: step 0 goes
  -- from a projection record to its block, step `j + 1` to the record's `j`-th reference,
  -- which it must use as a constant. `passed` is whether the path has reached a covered record (one
  -- bound to a role whose record a validation walks), its stop included.

def walk_path := aiur_fn⟦
  fn walk_path(rc: KernelRoles::RoleCtx, cur: Bytes::AddressRef, s: Bytes::Stream, n: Field,
               passed: Field) -> (Bytes::AddressRef, Bytes::Stream, Field) {
      match n {
        0 => {
          -- the stop counts too: a covered block reached as a container's or a projection's
          -- block by a used-reference step
          let cov = addr_covered(rc, cur);
          (cur, s, passed + cov - passed * cov) } ,
        _ => {
          let (st, s2) = get_count(s);
          let c = Ingress::load_verified_constant(cur);
          let next = match st {
            0 => {  projection_block(c) } ,
            _ => {
              match c {
                Ixon::Constant::Mk(_, _, refs, _, _) => {
                  assert_eq!(KernelClaim::g_list_has(KernelClaim::const_idxs_of(c), st - 1), 1,
                    "model advice: a dependency path step uses an unused reference");
                  Lists::lookup(refs, st - 1) } ,
              } } ,
          };
          let cov = addr_covered(rc, cur);
          walk_path(rc, next, s2, n - 1, passed + cov - passed * cov) } ,
      }
    }
⟧

def projection_block := aiur_fn⟦
  fn projection_block(c: Ixon::Constant) -> Bytes::AddressRef {
      match c {
        Ixon::Constant::Mk(info, _, _, _, _) => {
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
      -- in Lean's logic: not unsafe, as an advice recursor (`check_advice_record`); the native
      -- route's recursor check does not read the flag
      match (*(Ingress::get_ci(x))) {
        KernelTypes::KConstantInfo::Rec(_, _, _, _, _, _, _, _, r_uns, _, _) => {
          assert_eq!(r_uns, 0, "model advice: an unsafe container recursor");
          () } ,
      };
      KernelClaim::run_check(rc, x);
      ()
    }
⟧

  -- Every recursor among the outside references: its record (the family record, for a
  -- member of one) uses only its block's references, its block's members, members of
  -- the blocks those references project from, and witnessed outside references (the
  -- closure of the modeled block). So none depends on the modeled block.

def container_recs_refs := aiur_fn⟦
  fn container_recs_refs(rc: KernelRoles::RoleCtx, xs: Lists::List<Bytes::AddressRef>, wset: RBTreeMap::RBTreeMap<Field>) -> () {
      match (*(xs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(x, rest) => {
          let c0 = Ingress::load_verified_constant(x);
          match c0 {
            Ixon::Constant::Mk(info, _, _, _, _) => {
              match info {
                Ixon::ConstantInfo::Recr(_) => {  container_refs_check(rc, x, c0, wset) } ,
                Ixon::ConstantInfo::RPrj(_) => {
                  container_refs_check(rc, x, Ingress::load_verified_constant(projection_block(c0)), wset) } ,
                _ => {  () } ,
              } } ,
          };
          container_recs_refs(rc, rest, wset) } ,
      }
    }
⟧

def container_refs_check := aiur_fn⟦
  fn container_refs_check(rc: KernelRoles::RoleCtx, x: Bytes::AddressRef, c: Ixon::Constant, wset: RBTreeMap::RBTreeMap<Field>) -> () {
      let iblock = rec_family_block(x);
      let ib = Ingress::load_verified_constant(iblock);
      match c {
        Ixon::Constant::Mk(_, _, refs, _, _) => {
          match ib {
            Ixon::Constant::Mk(_, _, irefs, _, _) => {
              container_refs_ok(rc, refs, KernelClaim::const_idxs_of(c), 0, x, iblock, irefs,
                                KernelClaim::const_idxs_of(ib), wset);
              assert_inner_refs_safe(rc, refs, KernelClaim::const_idxs_of(c)) } ,
          } } ,
      }
    }
⟧

def container_refs_ok := aiur_fn⟦
  fn container_refs_ok(rc: KernelRoles::RoleCtx, refs: Lists::List<Bytes::AddressRef>, used: Lists::List<Field>, i: Field,
                       self: Bytes::AddressRef,
                       iblock: Bytes::AddressRef, irefs: Lists::List<Bytes::AddressRef>,
                       iused: Lists::List<Field>, wset: RBTreeMap::RBTreeMap<Field>) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          match KernelClaim::g_list_has(used, i) {
            1 => {
              assert_eq!(Bytes::address_eq(r, self), 0,
                "model advice: a container recursor references itself");
              let ok = match used_ref_has(irefs, iused, 0, r) {
                1 => {  1 } ,
                _ => {
                  match is_projection_of(r, iblock) {
                    1 => {  1 } ,
                    _ => {
                      match projection_of_ref_block(rc, r, irefs, iused) {
                        1 => {  1 } ,
                        _ => {
                          match KernelClaim::addr_set_member(r, wset) {
                            1 => {
                              let wc = Ingress::load_verified_constant(r);
                              match wc {
                                Ixon::Constant::Mk(winfo, _, _, _, _) => {
                                  match winfo {
                                    Ixon::ConstantInfo::Recr(_) => {  0 } ,
                                    Ixon::ConstantInfo::RPrj(_) => {  0 } ,
                                    _ => {  1 } ,
                                  } } ,
                              } } ,
                            _ => {  0 } ,
                          } } ,
                      } } ,
                  } } ,
              };
              assert_eq!(ok, 1, "model advice: a container recursor references outside its block");
              () } ,
            _ => {  () } ,
          };
          container_refs_ok(rc, rest, used, i + 1, self, iblock, irefs, iused, wset) } ,
      }
    }
⟧

  -- Is `r` a type or constructor of the block one of `irefs` projects from?

def projection_of_ref_block := aiur_fn⟦
  fn projection_of_ref_block(rc: KernelRoles::RoleCtx, r: Bytes::AddressRef, irefs: Lists::List<Bytes::AddressRef>,
                             iused: Lists::List<Field>) -> Field {
      let c = Ingress::load_verified_constant(r);
      match c {
        Ixon::Constant::Mk(info, _, _, _, _) => {
          match info {
            Ixon::ConstantInfo::IPrj(_) => {  Ingress::get_ci(r); ref_projects_from(rc, r, irefs, iused, 0, projection_block(c)) } ,
            Ixon::ConstantInfo::CPrj(_) => {  Ingress::get_ci(r); ref_projects_from(rc, r, irefs, iused, 0, projection_block(c)) } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def ref_projects_from := aiur_fn⟦
  fn ref_projects_from(rc: KernelRoles::RoleCtx, r: Bytes::AddressRef,
                       irefs: Lists::List<Bytes::AddressRef>, iused: Lists::List<Field>, i: Field,
                       block: Bytes::AddressRef) -> Field {
      match (*(irefs)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(q, rest) => {
          -- a hit through a covered used reference counts only for a covered `r`
          let hit = match KernelClaim::g_list_has(iused, i) {
            1 => {
              match is_projection_of(q, block) {
                1 => {  1 - addr_covered(rc, q) * (1 - addr_covered(rc, r)) } ,
                _ => {  0 } ,
              } } ,
            _ => {  0 } ,
          };
          match hit {
            1 => {  1 } ,
            _ => {  ref_projects_from(rc, r, rest, iused, i + 1, block) } ,
          } } ,
      }
    }
⟧

def is_projection_of := aiur_fn⟦
  fn is_projection_of(r: Bytes::AddressRef, block: Bytes::AddressRef) -> Field {
      let c = Ingress::load_verified_constant(r);
      match c {
        Ixon::Constant::Mk(info, _, _, _, _) => {
          match info {
            Ixon::ConstantInfo::IPrj(_) => {  Ingress::get_ci(r); Bytes::address_eq(projection_block(c), block) } ,
            Ixon::ConstantInfo::CPrj(_) => {  Ingress::get_ci(r); Bytes::address_eq(projection_block(c), block) } ,
            Ixon::ConstantInfo::RPrj(_) => {  Ingress::get_ci(r); Bytes::address_eq(projection_block(c), block) } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

  -- ## The advice records

def check_advice_records := aiur_fn⟦
  fn check_advice_records(rc: KernelRoles::RoleCtx, advice: Lists::List<Bytes::AddressRef>,
                          seen: RBTreeMap::RBTreeMap<Field>, wset: RBTreeMap::RBTreeMap<Field>)
        -> RBTreeMap::RBTreeMap<Field> {
      match (*(advice)) {
        Lists::Node::Nil => {  seen } ,
        Lists::Node::Cons(a, rest) => {
          assert_eq!(KernelClaim::addr_set_member(a, seen), 0,
            "model advice: duplicate advice record");
          assert_eq!(KernelClaim::addr_set_member(a, wset), 0,
            "model advice: an advice record is a witnessed reference");
          check_advice_record(rc, a, seen, wset);
          check_advice_records(rc, rest, RBTreeMap::rbtree_map_insert(a, 1, seen), wset) } ,
      }
    }
⟧

  -- One advice record, as an ordinary declaration of the kinds the modeller emits: a safe
  -- definition, a theorem, a native inductive block or its recursor, or a projection of
  -- an earlier advice block. Every reference it uses is earlier advice, a projection of an
  -- earlier advice block, or a witnessed outside reference.

def check_advice_record := aiur_fn⟦
  fn check_advice_record(rc: KernelRoles::RoleCtx, a: Bytes::AddressRef,
                         aset: RBTreeMap::RBTreeMap<Field>, wset: RBTreeMap::RBTreeMap<Field>) -> () {
      -- the advice record itself is reached through the payload, past every `walk_ctx`
      KernelRoles::assert_in_order(rc, a);
      let c = Ingress::load_verified_constant(a);
      match c {
        Ixon::Constant::Mk(info, _, refs, _, _) => {
          match info {
            Ixon::ConstantInfo::Defn(d) => {
              match d {
                Ixon::Definition::Mk(kind, safety, _, _, _, _) => {
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
              -- and it names a member of that block
              Ingress::get_ci(a);
              () } ,
            Ixon::ConstantInfo::CPrj(_) => {
              assert_eq!(KernelClaim::addr_set_member(projection_block(c), aset), 1,
                "model advice: a projection of a block that is not advice");
              Ingress::get_ci(a);
              () } ,
          };
          advice_refs_ok(refs, KernelClaim::const_idxs_of(c), 0, aset, wset);
          assert_inner_refs_safe(rc, refs, KernelClaim::const_idxs_of(c)) } ,
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

  -- The walk's contract on an inner record's references, which the three inner reference checks
  -- do not themselves assert: every used reference is allowed (no inert axiom) and, where not
  -- covered, its record and owner are safe (`assert_safe_used_refs`), and none names a block
  -- record (`assert_not_block_ref`). An honest inner record satisfies both.

def assert_used_not_block := aiur_fn⟦
  fn assert_used_not_block(refs: Lists::List<Bytes::AddressRef>, used: Lists::List<Field>, i: Field) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          match KernelClaim::g_list_has(used, i) {
            1 => {  KernelClaim::assert_not_block_ref(r) } ,
            _ => {  () } ,
          };
          assert_used_not_block(rest, used, i + 1) } ,
      }
    }
⟧

def assert_inner_refs_safe := aiur_fn⟦
  fn assert_inner_refs_safe(rc: KernelRoles::RoleCtx, refs: Lists::List<Bytes::AddressRef>,
                            used: Lists::List<Field>) -> () {
      KernelClaim::assert_safe_used_refs(rc, refs, used, 0, RBTreeMap::RBTreeMap::Nil);
      assert_used_not_block(refs, used, 0);
      assert_used_in_order(rc, refs, used, 0)
    }
⟧

  -- The walk's order assertion at every used reference of an inner record
  -- (`KernelRoles::assert_in_order`): no `walk_ctx` passes them.

def assert_used_in_order := aiur_fn⟦
  fn assert_used_in_order(rc: KernelRoles::RoleCtx, refs: Lists::List<Bytes::AddressRef>,
                          used: Lists::List<Field>, i: Field) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          match KernelClaim::g_list_has(used, i) {
            1 => {  KernelRoles::assert_in_order(rc, r) } ,
            _ => {  () } ,
          };
          assert_used_in_order(rc, rest, used, i + 1) } ,
      }
    }
⟧

  -- No address of the recursor family record is bound to a role: an honest table binds no role at
  -- a mutual or nested family's recursor (the condition the modeled type and constructor assert).

def assert_no_role := aiur_fn⟦
  fn assert_no_role(rc: KernelRoles::RoleCtx, xs: Lists::List<Bytes::AddressRef>) -> () {
      match (*(xs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(x, rest) => {
          assert_eq!(KernelRoles::role_index_of(rc, x), 0,
            "a modeled recursor is bound to a role");
          assert_no_role(rc, rest) } ,
      }
    }
⟧

  -- Covered: bound to a role whose record a validation walks (`role_admission_checks`). The
  -- top-level walk does not enter a covered record, so what lies past one is not top-walked: a
  -- witness reached past one must be covered itself.

def addr_covered := aiur_fn⟦
  fn addr_covered(rc: KernelRoles::RoleCtx, a: Bytes::AddressRef) -> Field {
      let r1 = KernelRoles::role_index_of(rc, a);
      match r1 {
        0 => {  0 } ,
        _ => {  KernelRoles::role_admission_checks(r1 - 1) } ,
      }
    }
⟧

def assert_covered_past := aiur_fn⟦
  fn assert_covered_past(rc: KernelRoles::RoleCtx, passed: Field, x: Bytes::AddressRef) -> () {
      match passed {
        0 => {  () } ,
        _ => {
          assert_eq!(addr_covered(rc, x), 1,
            "model advice: a witness past a role-bound record is not bound to a role");
          () } ,
      }
    }
⟧

def projection_of_advice := aiur_fn⟦
  fn projection_of_advice(r: Bytes::AddressRef, aset: RBTreeMap::RBTreeMap<Field>) -> Field {
      let c = Ingress::load_verified_constant(r);
      match c {
        Ixon::Constant::Mk(info, _, _, _, _) => {
          match info {
            Ixon::ConstantInfo::IPrj(_) => {  Ingress::get_ci(r); KernelClaim::addr_set_member(projection_block(c), aset) } ,
            Ixon::ConstantInfo::CPrj(_) => {  Ingress::get_ci(r); KernelClaim::addr_set_member(projection_block(c), aset) } ,
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
      -- No model advice under user axioms: the claim's axioms tree is empty, so every axiom
      -- this claim checks, the advice's and the block closure's, is standard or inert, and
      -- no accepted constant uses an inert one. The role binding binds Lean's compiler-trust
      -- axioms as inert roles, so a claim over Lean's `Init` lists no user axiom.
      match KernelRoles::role_ctx_axioms(rc) {
        RBTreeMap::RBTreeMap::Nil => {  () } ,
        RBTreeMap::RBTreeMap::Node(_, _, _, _, _) => {
          assert_eq!(0, 1, "model advice: a claim with user axioms");
          () } ,
      };
      let s0 = read_payload(block);
      let (rb, s1) = IxonDeserialize::get_address(s0);
      assert_eq!(Bytes::address_eq(rb, rec_block), 1,
        "model advice: the payload names another recursor family");
      -- the family record is reached through the payload too (its members are bound to no
      -- role: `assert_no_role` below)
      KernelRoles::assert_in_order(rc, rec_block);
      let (n_a, s2) = get_count(s1);
      let (advice, s3) = get_addrs(s2, n_a);
      let (n_w, s4) = get_count(s3);
      let (outside, s5) = check_witnesses(rc, block, s4, n_w);
      let wset = KernelClaim::addr_set_build(outside, RBTreeMap::RBTreeMap::Nil);
      container_recs_refs(rc, outside, wset);
      let aset = check_advice_records(rc, advice, RBTreeMap::RBTreeMap::Nil, wset);
      let bc = Ingress::load_verified_constant(block);
      match bc {
        Ixon::Constant::Mk(binfo, _, _, _, _) => {
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
              assert_no_role(rc, rec_addrs);
              assert_no_type_role(rc, type_addrs);
              let n_recs = Lists::length(rec_addrs);
              let (rec_models, s8) = get_addrs(s7, n_recs);
              let src = Lists::concat(type_addrs, Lists::concat(ctor_addrs, rec_addrs));
              let dst = Lists::concat(type_models, Lists::concat(ctor_models, rec_models));
              members_val(type_addrs, type_models, src, dst, aset, src);
              members_val(ctor_addrs, ctor_models, src, dst, aset,
                Lists::concat(ctor_addrs, rec_addrs));
              members_val(rec_addrs, rec_models, src, dst, aset, rec_addrs);
              -- the family-wide elimination level and the block's level count, from the
              -- block alone: its types share their level count and result universe, and
              -- a block of two or more types (mutual, or nested, which the kernel
              -- flattens) eliminates into every sort exactly when that universe is never
              -- `Prop` (Lean's `elim_only_at_universe_zero`)
              let (bnl, univ_offset) = block_elim(rc, type_addrs);
              -- the family's auxiliary members are the nested occurrences the block's
              -- constructors require, no more and no fewer
              let flat = KernelCheck::build_flat_block(rec_block, block, univ_offset);
              check_nested_aux(block, flat);
              -- no partial family record: empty (a declaration-only family) or one recursor per
              -- member of the flattened block, asserted before the per-recursor loop; under a
              -- group's validation (the binding stores what it checks) only a complete one
              let complete = Fields::is_zero(n_recs - Lists::length(flat));
              let empty_ok = Fields::is_zero(n_recs) * (1 - KernelRoles::rc_validates_group(rc));
              assert_eq!(complete + empty_ok - complete * empty_ok, 1,
                "modeled recursor family record is neither empty nor one recursor per member of the flattened block");
              -- the family record references only what the block's own walk checks:
              -- the block's used references, members of the blocks those project from,
              -- the block's members, and witnessed members of its closure
              family_refs_ok(rc, rec_block, block, wset);
              let s9 = check_recs(rc, type_addrs, rec_addrs, rec_models, src, dst, aset, s8,
                                  n_recs, 0, np, univ_offset, bnl, rec_addrs, 0);
              let s10 = check_projs(rc, block, members, 0, type_addrs, type_models, src, dst,
                                    aset, np, bnl, s9);
              let Lists::Node::Nil = (*(s10));
              () } ,
          } } ,
      }
    }
⟧

  -- The block's level count and its family-wide elimination offset. Every type
  -- has the first's level count and result universe (one `inductDecl` has one level
  -- list, and Lean's mutual types live in one universe); the offset is 1 exactly
  -- when that universe is never zero. A modeled block flattens to two or more types,
  -- where Lean's `elim_only_at_universe_zero` has no constructor case.

def block_elim := aiur_fn⟦
  fn block_elim(rc: KernelRoles::RoleCtx, type_addrs: Lists::List<Bytes::AddressRef>) -> (Field, Field) {
      let Lists::Node::Cons(t0, rest) = (*(type_addrs));
      match (*(Ingress::get_ci(t0))) {
        KernelTypes::KConstantInfo::Induct(nl, ty, np, ni, _, _, _, _) => {
          let lvl = KernelCheck::get_result_sort_level(rc, ty, np + ni, (&(Lists::Node::Nil)));
          peers_agree(rc, rest, nl, lvl);
          (nl, KernelLevels::level_is_not_zero(lvl)) } ,
      }
    }
⟧

def peers_agree := aiur_fn⟦
  fn peers_agree(rc: KernelRoles::RoleCtx, type_addrs: Lists::List<Bytes::AddressRef>,
                 nl0: Field, lvl0: KernelTypes::KLevel) -> () {
      match (*(type_addrs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(t, rest) => {
          match (*(Ingress::get_ci(t))) {
            KernelTypes::KConstantInfo::Induct(nl, ty, np, ni, _, _, _, _) => {
              assert_eq!(nl, nl0, "modeled block: types disagree on the universe-parameter count");
              let lvl = KernelCheck::get_result_sort_level(rc, ty, np + ni, (&(Lists::Node::Nil)));
              assert_eq!(KernelLevels::level_equal(lvl, lvl0), 1,
                "modeled block: types land in different universes");
              peers_agree(rc, rest, nl0, lvl0) } ,
          } } ,
      }
    }
⟧

  -- ## The family: its auxiliary members

  -- The auxiliary members a nested block's recursor family has, derived from the block's
  -- constructors as Lean's kernel derives them when it reduces a nested block to a mutual one
  -- (`elim_nested_inductive`): in a constructor's type after its parameters, an occurrence
  -- `I Ds is` of an inductive `I` outside the block whose parameters `Ds` mention a type of
  -- the block, read outermost first and not inside an occurrence, adds every type of `I`'s
  -- block at `Ds` and at the occurrence's levels; their constructors, at `Ds`, are read in
  -- turn. The family's auxiliary members (`flat`, read off the family record) must be these,
  -- as a set: no motive for an occurrence the constructors do not have, and none missing.
  -- An entry is `(type, is auxiliary, parameters, levels)`, at the recursor's levels.

def check_nested_aux := aiur_fn⟦
  fn check_nested_aux(block: Bytes::AddressRef,
                      flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>) -> () {
      let derived = nested_walk(block, flat_reals(flat), 0);
      assert_eq!(aux_count(derived), aux_count(flat),
        "modeled recursor family: its auxiliary members are not the constructors' nested occurrences");
      assert_eq!(aux_all_in(derived, flat), 1,
        "modeled recursor family: its auxiliary members are not the constructors' nested occurrences");
      ()
    }
⟧

  -- The block's own types among the entries, in order.

def flat_reals := aiur_fn⟦
  fn flat_reals(flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>)
        -> Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)> {
      match (*(flat)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (_, is_aux, _, _) => {
              match is_aux {
                0 => {  (&(Lists::Node::Cons(m, flat_reals(rest)))) } ,
                _ => {  flat_reals(rest) } ,
              } } ,
          } } ,
      }
    }
⟧

  -- The worklist: the constructors of entry `i` onwards, each new entry appended.

def nested_walk := aiur_fn⟦
  fn nested_walk(block: Bytes::AddressRef,
                 acc: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                 i: Field)
        -> Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)> {
      match Lists::length(acc) - i {
        0 => {  acc } ,
        _ => {
          let (addr, is_aux, sp, us) = Lists::lookup(acc, i);
          match (*(Ingress::get_ci(addr))) {
            KernelTypes::KConstantInfo::Induct(_, _, np, _, nctors, _, mblk, midx) => {
              nested_walk(block,
                ctors_scan(block, mblk, midx, nctors, 0, np, is_aux, sp, us, acc), i + 1) } ,
          } } ,
      }
    }
⟧

  -- The constructors `c..` of one entry: a type of the block at its own parameters, an
  -- auxiliary one at its parameters `sp`; both at the entry's levels `us`.

def ctors_scan := aiur_fn⟦
  fn ctors_scan(block: Bytes::AddressRef, mblk: Bytes::AddressRef, midx: Field, nctors: Field, c: Field,
                np: Field, is_aux: Field, sp: Lists::List<KernelTypes::KExpr>,
                us: Lists::List<KernelTypes::KLevel>,
                acc: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>)
        -> Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)> {
      match nctors - c {
        0 => {  acc } ,
        _ => {
          match (*(Ingress::get_ci_cprj(mblk, midx, c))) {
            KernelTypes::KConstantInfo::Ctor(_, cty, _, _, _, _, _, _) => {
              let t = KernelLevels::expr_inst_levels(cty, us);
              let body = match is_aux {
                0 => {  KernelCheck::peel_n_foralls_zeta(t, np) } ,
                _ => {  inst_ctor_params(t, sp) } ,
              };
              ctors_scan(block, mblk, midx, nctors, c + 1, np, is_aux, sp, us,
                         occ_scan(block, body, 0, acc)) } ,
          } } ,
      }
    }
⟧

  -- A constructor type's parameters, instantiated by `sp` (terms over the recursor's
  -- parameters), stepping through leading `let` bindings.

def inst_ctor_params := aiur_fn⟦
  fn inst_ctor_params(t: KernelTypes::KExpr, sp: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(sp)) {
        Lists::Node::Nil => {  t } ,
        Lists::Node::Cons(v, rest) => {
          match (*(t)) {
            KernelTypes::KExprNode::Forall(_, body, _) => {
              inst_ctor_params(KernelSubst::expr_inst1(body, v, 0), rest) } ,
            KernelTypes::KExprNode::Let(_, lv, lb) => {
              inst_ctor_params(KernelSubst::expr_inst1(lb, lv, 0), sp) } ,
          } } ,
      }
    }
⟧

  -- The nested occurrences in `e`, under `d` binders of the constructor's type. A subterm
  -- that does not mention the block has none.

def occ_scan := aiur_fn⟦
  fn occ_scan(block: Bytes::AddressRef, e: KernelTypes::KExpr, d: Field,
              acc: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>)
        -> Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)> {
      let blocks = (&(Lists::Node::Cons(block, (&(Lists::Node::Nil)))));
      match occ_mentions_block(e, blocks) {
        0 => {  acc } ,
        _ => {
          match (*(e)) {
            KernelTypes::KExprNode::App(_, _) => {
              let (head, args) = KernelCheck::collect_spine_zeta(e);
              match (*(head)) {
                KernelTypes::KExprNode::Const(c, us) => {
                  match (*(Ingress::get_ci(c))) {
                    KernelTypes::KConstantInfo::Induct(_, _, cnp, _, _, _, cblk, _) => {
                      let nested = match Bytes::address_eq(cblk, block) {
                        1 => {  0 } ,
                        _ => {
                          match UInt32::less_than_fields(Lists::length(args), cnp) {
                            1 => {  0 } ,
                            _ => {  occ_any_mentions_block(Lists::take(args, cnp), blocks) } ,
                          } } ,
                      };
                      match nested {
                        1 => {
                          add_block_members(KernelCheck::build_flat_originals(cblk, 0),
                            occ_params_lower(Lists::take(args, cnp), d), us, acc) } ,
                        _ => {  occ_scan_list(block, args, d, acc) } ,
                      } } ,
                    _ => {  occ_scan_list(block, args, d, acc) } ,
                  } } ,
                _ => {  occ_scan_list(block, args, d, occ_scan(block, head, d, acc)) } ,
              } } ,
            KernelTypes::KExprNode::Lam(t, b, _) => {
              occ_scan(block, b, d + 1, occ_scan(block, t, d, acc)) } ,
            KernelTypes::KExprNode::Forall(t, b, _) => {
              occ_scan(block, b, d + 1, occ_scan(block, t, d, acc)) } ,
            KernelTypes::KExprNode::Let(_, v, b) => {
              occ_scan(block, KernelSubst::expr_inst1(b, v, 0), d, acc) } ,
            KernelTypes::KExprNode::Proj(_, _, x) => {  occ_scan(block, x, d, acc) } ,
            _ => {  acc } ,
          } } ,
      }
    }
⟧

def occ_scan_list := aiur_fn⟦
  fn occ_scan_list(block: Bytes::AddressRef, es: Lists::List<KernelTypes::KExpr>, d: Field,
                   acc: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>)
        -> Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)> {
      match (*(es)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(x, rest) => {  occ_scan_list(block, rest, d, occ_scan(block, x, d, acc)) } ,
      }
    }
⟧

  -- An occurrence's parameters, from under `d` binders to the recursor's parameters: they
  -- mention no binder of the constructor's type (Lean's kernel refuses such a nested
  -- occurrence).

def occ_params_lower := aiur_fn⟦
  fn occ_params_lower(ds: Lists::List<KernelTypes::KExpr>, d: Field) -> Lists::List<KernelTypes::KExpr> {
      match (*(ds)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(x, rest) => {
          assert_eq!(KernelSubst::has_bvar_in_range(x, 0, d), 0,
            "nested occurrence: its parameters mention a local variable");
          (&(Lists::Node::Cons(KernelSubst::expr_lower(x, d, 0), occ_params_lower(rest, d)))) } ,
      }
    }
⟧

  -- Every type of an occurrence's block (`members`, as `build_flat_originals` lists them)
  -- at the occurrence's parameters and levels, unless already an entry.

def add_block_members := aiur_fn⟦
  fn add_block_members(members: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                       sp: Lists::List<KernelTypes::KExpr>, us: Lists::List<KernelTypes::KLevel>,
                       acc: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>)
        -> Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)> {
      match (*(members)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (maddr, _, _, _) => {
              let acc2 = match aux_entry_in(acc, maddr, sp, us) {
                1 => {  acc } ,
                _ => {  Lists::snoc(acc, (maddr, 1, sp, us)) } ,
              };
              add_block_members(rest, sp, us, acc2) } ,
          } } ,
      }
    }
⟧

  -- Whether `(addr, sp, us)` is an auxiliary entry: the same type, structurally the same
  -- parameters and levels.

def aux_entry_in := aiur_fn⟦
  fn aux_entry_in(flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                  addr: Bytes::AddressRef, sp: Lists::List<KernelTypes::KExpr>,
                  us: Lists::List<KernelTypes::KLevel>) -> Field {
      match (*(flat)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (a, is_aux, s, u) => {
              match is_aux * Bytes::address_eq(a, addr) {
                1 => {
                  match KernelCheck::spec_params_zeta_eq(s, sp) * KernelCheck::level_list_struct_eq(u, us) {
                    1 => {  1 } ,
                    _ => {  aux_entry_in(rest, addr, sp, us) } ,
                  } } ,
                _ => {  aux_entry_in(rest, addr, sp, us) } ,
              } } ,
          } } ,
      }
    }
⟧

def aux_count := aiur_fn⟦
  fn aux_count(flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>) -> Field {
      match (*(flat)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (_, is_aux, _, _) => {  aux_count(rest) + is_aux } ,
          } } ,
      }
    }
⟧

  -- `derived` and `flat` are the same entries in the same order: the family record's
  -- auxiliary members are the derived ones, in the derived order.

def aux_all_in := aiur_fn⟦
  fn aux_all_in(derived: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>) -> Field {
      match (*(derived)) {
        Lists::Node::Nil => {
          match (*(flat)) {
            Lists::Node::Nil => {  1 } ,
            _ => {  0 } ,
          } } ,
        Lists::Node::Cons(m, rest) => {
          match (*(flat)) {
            Lists::Node::Nil => {  0 } ,
            Lists::Node::Cons(m2, rest2) => {
              match m {
                (a, is_aux, s, u) => {
                  match m2 {
                    (a2, is_aux2, s2, u2) => {
                      let same_kind = match is_aux - is_aux2 {
                        0 => {  1 } ,
                        _ => {  0 } ,
                      };
                      let same = ((Bytes::address_eq(a, a2) * same_kind) *
                        KernelCheck::spec_params_zeta_eq(s, s2)) *
                        KernelCheck::level_list_struct_eq(u, u2);
                      match same {
                        1 => {  aux_all_in(rest, rest2) } ,
                        _ => {  0 } ,
                      } } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

  -- The family record's used references: each is a used reference of the block, a
  -- member of the block or of a block one of those projects from, or a witnessed
  -- member of the block's closure. The family adds no constant the claim's walk of
  -- the block does not check (a canonical family mentions only the block's types,
  -- constructors, parameter and index domains, and the containers it nests through).

def family_refs_ok := aiur_fn⟦
  fn family_refs_ok(rc: KernelRoles::RoleCtx, rec_block: Bytes::AddressRef, block: Bytes::AddressRef,
                    wset: RBTreeMap::RBTreeMap<Field>) -> () {
      let rcst = Ingress::load_verified_constant(rec_block);
      let bc = Ingress::load_verified_constant(block);
      match rcst {
        Ixon::Constant::Mk(_, _, refs, _, _) => {
          match bc {
            Ixon::Constant::Mk(_, _, irefs, _, _) => {
              family_refs_go(rc, refs, KernelClaim::const_idxs_of(rcst), 0, block, irefs,
                             KernelClaim::const_idxs_of(bc), wset);
              assert_inner_refs_safe(rc, refs, KernelClaim::const_idxs_of(rcst)) } ,
          } } ,
      }
    }
⟧

def family_refs_go := aiur_fn⟦
  fn family_refs_go(rc: KernelRoles::RoleCtx, refs: Lists::List<Bytes::AddressRef>, used: Lists::List<Field>, i: Field,
                    block: Bytes::AddressRef, irefs: Lists::List<Bytes::AddressRef>,
                    iused: Lists::List<Field>, wset: RBTreeMap::RBTreeMap<Field>) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          match KernelClaim::g_list_has(used, i) {
            1 => {
              let ok = match used_ref_has(irefs, iused, 0, r) {
                1 => {  1 } ,
                _ => {
                  let rc0 = Ingress::load_verified_constant(r);
                  let own = match rc0 {
                    Ixon::Constant::Mk(info, _, _, _, _) => {
                      match info {
                        Ixon::ConstantInfo::IPrj(_) => {  Ingress::get_ci(r); Bytes::address_eq(projection_block(rc0), block) } ,
                        Ixon::ConstantInfo::CPrj(_) => {  Ingress::get_ci(r); Bytes::address_eq(projection_block(rc0), block) } ,
                        _ => {  0 } ,
                      } } ,
                  };
                  match own {
                    1 => {  1 } ,
                    _ => {
                      match projection_of_ref_block(rc, r, irefs, iused) {
                        1 => {  1 } ,
                        _ => {  KernelClaim::addr_set_member(r, wset) } ,
                      } } ,
                  } } ,
              };
              assert_eq!(ok, 1, "modeled recursor family references outside its block's closure");
              () } ,
            _ => {  () } ,
          };
          family_refs_go(rc, rest, used, i + 1, block, irefs, iused, wset) } ,
      }
    }
⟧

  -- Is `r` one of the used references `irefs`?

def used_ref_has := aiur_fn⟦
  fn used_ref_has(irefs: Lists::List<Bytes::AddressRef>, iused: Lists::List<Field>, i: Field,
                  r: Bytes::AddressRef) -> Field {
      match (*(irefs)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(q, rest) => {
          let hit = match KernelClaim::g_list_has(iused, i) {
            1 => {  Bytes::address_eq(q, r) } ,
            _ => {  0 } ,
          };
          match hit {
            1 => {  1 } ,
            _ => {  used_ref_has(rest, iused, i + 1, r) } ,
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
        Ixon::Constant::Mk(info, _, _, _, _) => {
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
                 aset: RBTreeMap::RBTreeMap<Field>,
                 later: Lists::List<Bytes::AddressRef>) -> () {
      match (*(members)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(m, rest) => {
          let Lists::Node::Cons(md, mrest) = (*(models));
          member_val(m, md, src, dst, aset, later);
          members_val(rest, mrest, src, dst, aset, later) } ,
      }
    }
⟧

  -- `checkMemberVal`: the model is an advice definition at the member's level count,
  -- whose type is the member's under the block renaming, structurally.

def member_val := aiur_fn⟦
  fn member_val(member: Bytes::AddressRef, model: Bytes::AddressRef,
                src: Lists::List<Bytes::AddressRef>, dst: Lists::List<Bytes::AddressRef>,
                aset: RBTreeMap::RBTreeMap<Field>,
                later: Lists::List<Bytes::AddressRef>) -> () {
      assert_eq!(KernelClaim::addr_set_member(model, aset), 1, "model advice: a model that is not advice");
      let (nl, ty) = ci_lvls_type((*(Ingress::get_ci(member))));
      -- the member's type names no member stored after it: a type's names none, a
      -- constructor's no constructor and no recursor, a recursor's no recursor
      assert_eq!(expr_mentions_addrs(ty, later), 0,
        "modeled block: a member's type names a member that is not stored before it");
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
        KernelTypes::KExprNode::Lam(t, b, bl) => {
          (&(KernelTypes::KExprNode::Lam(rename(t, src, dst), rename(b, src, dst), bl))) } ,
        KernelTypes::KExprNode::Forall(t, b, bl) => {
          (&(KernelTypes::KExprNode::Forall(rename(t, src, dst), rename(b, src, dst), bl))) } ,
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

  -- Each member of the family record: safe, no K, the block's parameter count, one
  -- motive per member (a complete family), eliminating motive `k` at position `k`, its
  -- first motives' carriers the block's types in order; its type well-scoped and a
  -- type; the canonical recursor at the family-wide elimination offset (the level
  -- link, the type up to definitional equality and every rule syntactically the
  -- reconstruction's, from the block and the family record alone); then each rule's
  -- `iota_j` theorem, which shows the advice's model satisfies that canonical rule.
  -- The advice decides no reduction: a second payload for the block could only
  -- witness another model of the same canonical family.

def check_recs := aiur_fn⟦
  fn check_recs(rc: KernelRoles::RoleCtx, type_addrs: Lists::List<Bytes::AddressRef>,
                recs: Lists::List<Bytes::AddressRef>, models: Lists::List<Bytes::AddressRef>,
                src: Lists::List<Bytes::AddressRef>, dst: Lists::List<Bytes::AddressRef>,
                aset: RBTreeMap::RBTreeMap<Field>, s: Bytes::Stream,
                n_recs: Field, k: Field, np: Field, univ_offset: Field, bnl: Field,
                fam: Lists::List<Bytes::AddressRef>, form: Field) -> Bytes::Stream {
      match (*(recs)) {
        Lists::Node::Nil => {  s } ,
        Lists::Node::Cons(r, rest) => {
          let Lists::Node::Cons(rm, mrest) = (*(models));
          let rci = (*(Ingress::get_ci(r)));
          match rci {
            KernelTypes::KConstantInfo::Rec(nl, ty, rnp, ni, nmot, nmin, rules, kf, r_uns, _, _) => {
              assert_eq!(kf, 0, "modeled recursor declares K");
              -- the family's recursors are safe: the reader declines an unsafe one, so
              -- no model stores it
              assert_eq!(r_uns, 0, "modeled recursor family has an unsafe member");
              assert_eq!(rnp, np, "modeled recursor parameter count differs from its block's");
              assert_eq!(nmot, n_recs, "modeled recursor family record is not one complete family");
              assert_eq!(UInt32::less_than_fields(1, nmot), 1,
                "a modeled recursor family with one motive");
              assert_eq!(UInt32::less_than_fields(Lists::length(type_addrs), nmot + 1), 1,
                "modeled recursor has fewer motives than its block has types");
              check_rec_motive(ty, (((rnp + nmot) + nmin) + ni) + 1, rnp + k);
              check_carriers(ty, rnp, type_addrs);
              -- the raw type, as `check_const` checks a recursor reached directly
              KernelCheck::validate_expr_well_scoped(ty, 0, nl);
              -- and it names no member of its own family record, so that every constant it
              -- names is the block's or stored before the family. No stored record reaches
              -- this: `get_ci` above reads a recursor's type with no recursive reference in scope
              -- (a `Rec` node does not convert), and a `Ref` to a member of the same family
              -- record would name an address computed from the record itself. Kept as the
              -- condition the refinement states.
              assert_eq!(expr_mentions_addrs(ty, fam), 0,
                "a modeled recursor's type mentions its own family");
              -- the renaming to the model leaves its parameter domains as they are, and no
              -- parameter argument of its major premise mentions a motive or a minor premise:
              -- a rule's pins are over the parameters only
              let (_, pdoms) = peel_collect(ty, rnp, (&(Lists::Node::Nil)));
              let (_, pdoms_m) = peel_collect(rename(ty, src, dst), rnp, (&(Lists::Node::Nil)));
              assert_eq!(KernelCheck::spec_params_ptr_eq(pdoms, pdoms_m), 1,
                "a modeled recursor's parameter domain names a member of its family");
              let (_, _, pins) = rec_major_pins(ty, (rnp + nmot) + nmin, ni);
              let _pins_over_params = lower_pins(pins, nmot + nmin);
              KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
              KernelCheck::assert_safety(0, ty);
              KernelCheck::assert_safety_rules(0, rules);
              let parent = KernelCheck::rec_to_parent_addr(ty, rnp, nmot, nmin, ni);
              -- the family record takes one form for all its members (`form`, carried from the
              -- members before this one)
              let form2 = KernelCheck::check_recursor_canonical_at(rc, rci, r, (*(Ingress::get_ci(parent))),
                parent, univ_offset, bnl, form);
              -- the header as plain syntax, as a native recursor's
              KernelCheck::check_rec_header_lets(ty, rnp, nmot, nmin, ni);
              let s2 = check_rules(rc, rm, nl, ty, rnp + nmot + nmin, ni, rules, src, dst, aset, s);
              check_recs(rc, type_addrs, rest, mrest, src, dst, aset, s2, n_recs, k + 1, np,
                         univ_offset, bnl, fam, form2) } ,
          } } ,
      }
    }
⟧

  -- Whether `e` names one of `addrs`, as a constant or as a projection's structure.

def expr_mentions_addrs := aiur_fn⟦
  fn expr_mentions_addrs(e: KernelTypes::KExpr, addrs: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(e)) {
        KernelTypes::KExprNode::Const(c, _) => {  KernelCheck::addr_list_contains(addrs, c) } ,
        KernelTypes::KExprNode::App(f, x) => {
          match expr_mentions_addrs(f, addrs) {
            0 => {  expr_mentions_addrs(x, addrs) } ,
            _ => {  1 } ,
          } } ,
        KernelTypes::KExprNode::Lam(t, b, _) => {
          match expr_mentions_addrs(t, addrs) {
            0 => {  expr_mentions_addrs(b, addrs) } ,
            _ => {  1 } ,
          } } ,
        KernelTypes::KExprNode::Forall(t, b, _) => {
          match expr_mentions_addrs(t, addrs) {
            0 => {  expr_mentions_addrs(b, addrs) } ,
            _ => {  1 } ,
          } } ,
        KernelTypes::KExprNode::Let(t, v, b) => {
          match expr_mentions_addrs(t, addrs) {
            0 => {
              match expr_mentions_addrs(v, addrs) {
                0 => {  expr_mentions_addrs(b, addrs) } ,
                _ => {  1 } ,
              } } ,
            _ => {  1 } ,
          } } ,
        KernelTypes::KExprNode::Proj(s, _, x) => {
          match KernelCheck::addr_list_contains(addrs, s) {
            0 => {  expr_mentions_addrs(x, addrs) } ,
            _ => {  1 } ,
          } } ,
        _ => {  0 } ,
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
            KernelTypes::KExprNode::Forall(mdom, body, _) => {
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
      -- the stored rule: closed, a λ-telescope over the prefix and the fields, and typable
      -- once renamed to the model: no member of the block or of the family record is left
      -- in it, so no rule of the family being checked fires while it is typed
      KernelCheck::validate_expr_well_scoped(rhs, 0, nl);
      let (_, peeled, _) = KernelCheck::peel_n_lams_collect(rhs, d, 0, (&(Lists::Node::Nil)));
      assert_eq!(peeled, d, "rule shape mismatch");
      let rhs_m = rename(rhs, src, dst);
      KernelInfer::k_infer(rc, rhs_m, (&(Lists::Node::Nil)));
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
              -- the residual head before instantiation is a constant (the family former), as
              -- IxC tests it: a variable head could be captured by a pin instantiation
              let (chead0, _) = KernelTypes::collect_spine(KernelCheck::peel_n_foralls(cty_l, cnp + cnf));
              match (*(chead0)) {
                KernelTypes::KExprNode::Const(_, _) => {  () } ,
              };
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
              let ty_m = rename(ty_r, src, dst);
              defeq_tele(rc, tty, ty_m, rp, (&(Lists::Node::Nil)));
              defeq_tele(rc, KernelCheck::peel_n_foralls(tty, rp), crest, cnf, Lists::drop(ctx, cnf));
              -- the rule's side, renamed like the statement's: the comparands inhabit the
              -- constructor's parameter domains, and the rule's λ-domains are the recursor's
              -- prefix and the fields
              let (_, ctx_p) = peel_collect(ty_m, rp, (&(Lists::Node::Nil)));
              let crest_p = inst_params_typed(rc, rename(cty_l, src, dst), pins_ren, ctx_p);
              let (rhs_rp, lctx) = defeq_lam_tele(rc, rhs_m, ty_m, rp, (&(Lists::Node::Nil)));
              let (_, _) = defeq_lam_tele(rc, rhs_rp, crest_p, cnf, lctx);
              -- the right side: the rule applied to the opened variables
              let rhs_app = KernelWhnf::apply_spine(rhs_m, bvars_desc(d, d));
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
            KernelTypes::KExprNode::Forall(d, b, _) => {
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
            KernelTypes::KExprNode::Forall(_, b, _) => {
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
            KernelTypes::KExprNode::Forall(dom, b, _) => {
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
            KernelTypes::KExprNode::Forall(da, ba, _) => {
              match (*(b)) {
                KernelTypes::KExprNode::Forall(db, bb, _) => {
                  assert_eq!(KernelDefEq::k_is_def_eq(rc, da, db, ctx), 1, "iota statement domain mismatch");
                  defeq_tele(rc, ba, bb, n - 1, (&(Lists::Node::Cons(da, ctx)))) } ,
              } } ,
          } } ,
      }
    }
⟧

  -- A `λ`-telescope's first `n` domains against a `∀`-telescope's, each under the
  -- `∀`-telescope's earlier domains; returns the body and the context extended by them.

def defeq_lam_tele := aiur_fn⟦
  fn defeq_lam_tele(rc: KernelRoles::RoleCtx, l: KernelTypes::KExpr, p: KernelTypes::KExpr, n: Field,
                    ctx: Lists::List<KernelTypes::KExpr>) -> (KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>) {
      match n {
        0 => {  (l, ctx) } ,
        _ => {
          match (*(l)) {
            KernelTypes::KExprNode::Lam(dl, bl, _) => {
              match (*(p)) {
                KernelTypes::KExprNode::Forall(dp, bp, _) => {
                  assert_eq!(KernelDefEq::k_is_def_eq(rc, dl, dp, ctx), 1, "rule domain mismatch");
                  defeq_lam_tele(rc, bl, bp, n - 1, (&(Lists::Node::Cons(dp, ctx)))) } ,
              } } ,
          } } ,
      }
    }
⟧

  -- Whether `e` mentions a peer of `block_addrs` after ζ-expanding `let` bindings, used
  -- solely by `occ_scan` so dead `let` bindings do not introduce phantom nested occurrences.

def occ_mentions_block := aiur_fn⟦
  fn occ_mentions_block(e: KernelTypes::KExpr, block_addrs: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(e)) {
        KernelTypes::KExprNode::BVar(_) => {  0 } ,
        KernelTypes::KExprNode::Srt(_) => {  0 } ,
        KernelTypes::KExprNode::Const(caddr, _) => {  KernelCheck::caddr_is_peer(caddr, block_addrs) } ,
        KernelTypes::KExprNode::App(f, a) => {
          match occ_mentions_block(f, block_addrs) {
            1 => {  1 } ,
            _ => {  occ_mentions_block(a, block_addrs) } ,
          } } ,
        KernelTypes::KExprNode::Lam(t, b, _) => {
          match occ_mentions_block(t, block_addrs) {
            1 => {  1 } ,
            _ => {  occ_mentions_block(b, block_addrs) } ,
          } } ,
        KernelTypes::KExprNode::Forall(t, b, _) => {
          match occ_mentions_block(t, block_addrs) {
            1 => {  1 } ,
            _ => {  occ_mentions_block(b, block_addrs) } ,
          } } ,
        KernelTypes::KExprNode::Let(_, v, b) => {
          occ_mentions_block(KernelSubst::expr_inst1(b, v, 0), block_addrs) } ,
        KernelTypes::KExprNode::Lit(_) => {  0 } ,
        KernelTypes::KExprNode::Proj(_, _, e1) => {  occ_mentions_block(e1, block_addrs) } ,
      }
    }
⟧

def occ_any_mentions_block := aiur_fn⟦
  fn occ_any_mentions_block(es: Lists::List<KernelTypes::KExpr>,
                            block_addrs: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(es)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(e, rest) => {
          match occ_mentions_block(e, block_addrs) {
            1 => {  1 } ,
            _ => {  occ_any_mentions_block(rest, block_addrs) } ,
          } } ,
      }
    }
⟧

  -- No type address of the modeled block is bound to a role.

def assert_no_type_role := aiur_fn⟦
  fn assert_no_type_role(rc: KernelRoles::RoleCtx, xs: Lists::List<Bytes::AddressRef>) -> () {
      match (*(xs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(x, rest) => {
          assert_eq!(KernelRoles::role_index_of(rc, x), 0,
            "a modeled inductive is bound to a role");
          assert_no_type_role(rc, rest) } ,
      }
    }
⟧

  -- ## Modeled structure projections

  -- Pairwise structural equality of the first `n` domains of two `∀`-telescopes (ignoring
  -- the outer binders' `PropWhen` metadata), returning the first telescope's residual body.

def struct_eq_tele := aiur_fn⟦
  fn struct_eq_tele(a: KernelTypes::KExpr, b: KernelTypes::KExpr, n: Field) -> KernelTypes::KExpr {
      match n {
        0 => {  a } ,
        _ => {
          match (*(a)) {
            KernelTypes::KExprNode::Forall(da, ba, _) => {
              match (*(b)) {
                KernelTypes::KExprNode::Forall(db, bb, _) => {
                  assert_eq!(KernelCheck::kexpr_struct_eq(da, db), 1,
                    "modeled projection: telescope domain mismatch");
                  struct_eq_tele(ba, bb, n - 1) } ,
              } } ,
          } } ,
      }
    }
⟧

  -- Whether a type former's sort after `n` binders (stepping through `let`s), instantiated
  -- at `lvls`, is either never zero or always zero (so the set-model representation of its
  -- constructors is fixed across all level assignments).

def type_sort_fixed_zeta := aiur_fn⟦
  fn type_sort_fixed_zeta(ty: KernelTypes::KExpr, n: Field, lvls: Lists::List<KernelTypes::KLevel>) -> Field {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(_, body, _) => {
          match n {
            0 => {  0 } ,
            _ => {  type_sort_fixed_zeta(body, n - 1, lvls) } ,
          } } ,
        KernelTypes::KExprNode::Srt(l) => {
          match n {
            0 => {
              let li = KernelLevels::level_inst_params(l, lvls);
              match KernelLevels::level_is_not_zero(li) {
                1 => {  1 } ,
                _ => {  KernelLevels::level_equal(li, (&(KernelTypes::KLevelNode::Zero))) } ,
              } } ,
            _ => {  0 } ,
          } } ,
        KernelTypes::KExprNode::Let(_, v, b) => {
          type_sort_fixed_zeta(KernelSubst::expr_inst1(b, v, 0), n, lvls) } ,
        _ => {  0 } ,
      }
    }
⟧

  -- Check every projection-eligible member of the modeled block against its projection
  -- definitions and iota theorems in the payload stream.

def check_projs := aiur_fn⟦
  fn check_projs(rc: KernelRoles::RoleCtx, block: Bytes::AddressRef,
                 members: Lists::List<Ixon::MutConst>, pos: Field,
                 type_addrs: Lists::List<Bytes::AddressRef>,
                 type_models: Lists::List<Bytes::AddressRef>,
                 src: Lists::List<Bytes::AddressRef>, dst: Lists::List<Bytes::AddressRef>,
                 aset: RBTreeMap::RBTreeMap<Field>, np: Field, bnl: Field,
                 s: Bytes::Stream) -> Bytes::Stream {
      match (*(members)) {
        Lists::Node::Nil => {  s } ,
        Lists::Node::Cons(_, rest) => {
          let Lists::Node::Cons(t_addr, t_rest) = (*(type_addrs));
          let Lists::Node::Cons(t_model, tm_rest) = (*(type_models));
          let s2 = match modeled_proj_eligible(block, pos) {
            1 => {
              check_member_projs_start(rc, block, pos, t_addr, t_model, src, dst, aset, np, bnl, s) } ,
            _ => {  s } ,
          };
          check_projs(rc, block, rest, pos + 1, t_rest, tm_rest, src, dst, aset, np, bnl, s2) } ,
      }
    }
⟧

def check_member_projs_start := aiur_fn⟦
  fn check_member_projs_start(rc: KernelRoles::RoleCtx, block: Bytes::AddressRef, pos: Field,
                              t_addr: Bytes::AddressRef, t_model: Bytes::AddressRef,
                              src: Lists::List<Bytes::AddressRef>, dst: Lists::List<Bytes::AddressRef>,
                              aset: RBTreeMap::RBTreeMap<Field>, np: Field, bnl: Field,
                              s: Bytes::Stream) -> Bytes::Stream {
      let c_addr = KernelCheck::projection_addr_ctor(pos, 0, block);
      let c_model = rename_addr(c_addr, src, dst);
      match (*(Ingress::get_ci(t_addr))) {
        KernelTypes::KConstantInfo::Induct(tnl, tty, tnp, tni, tnc, _, _, _) => {
          assert_eq!(tnl, bnl, "modeled projection: type level count mismatch");
          assert_eq!(tnp, np, "modeled projection: type param count mismatch");
          assert_eq!(tni, 0, "modeled projection: indexed member");
          assert_eq!(tnc, 1, "modeled projection: multi-constructor member");
          match (*(Ingress::get_ci(c_addr))) {
            KernelTypes::KConstantInfo::Ctor(cnl, cty, _, _, _, cnp, cnf, _) => {
              assert_eq!(cnl, bnl, "modeled projection: ctor level count mismatch");
              assert_eq!(cnp, np, "modeled projection: ctor param count mismatch");
              assert_eq!(Fields::is_zero(cnf), 0, "modeled projection: zero fields");
              let (cbody, _) = peel_collect(cty, np + cnf, (&(Lists::Node::Nil)));
              let expected_ret = KernelWhnf::apply_spine(
                (&(KernelTypes::KExprNode::Const(t_addr, KernelCheck::build_param_lvls_range(0, bnl, 0)))),
                bvars_desc(np + cnf, np));
              assert_eq!(KernelCheck::kexpr_struct_eq(cbody, expected_ret), 1,
                "modeled projection: constructor return type mismatch");
              let cty_m = rename(cty, src, dst);
              let ftele = inst_params(cty_m, bvars_desc(np + 1, np));
              let ctele = KernelCheck::peel_n_foralls(cty_m, np);
              check_member_projs(rc, t_model, c_model, tty, cty_m, ftele, ctele, np, bnl, cnf, 0, aset, s) } ,
          } } ,
      }
    }
⟧

def check_member_projs := aiur_fn⟦
  fn check_member_projs(rc: KernelRoles::RoleCtx, t_model: Bytes::AddressRef, c_model: Bytes::AddressRef,
                        tty: KernelTypes::KExpr, cty_m: KernelTypes::KExpr,
                        ftele: KernelTypes::KExpr, ctele: KernelTypes::KExpr,
                        np: Field, bnl: Field, cnf: Field, fidx: Field,
                        aset: RBTreeMap::RBTreeMap<Field>, s: Bytes::Stream) -> Bytes::Stream {
      match cnf - fidx {
        0 => {  s } ,
        _ => {
          let (proj_i, s1) = IxonDeserialize::get_address(s);
          let (iota_i, s2) = IxonDeserialize::get_address(s1);
          assert_eq!(KernelClaim::addr_set_member(proj_i, aset), 1,
            "modeled projection: projection model is not advice");
          assert_eq!(KernelClaim::addr_set_member(iota_i, aset), 1,
            "modeled projection: iota theorem is not advice");
          match (*(ftele)) {
            KernelTypes::KExprNode::Forall(fdom, frest, _) => {
              match (*(ctele)) {
                KernelTypes::KExprNode::Forall(raw_dom, crest, _) => {
                  let param_lvls = KernelCheck::build_param_lvls_range(0, bnl, 0);
                  match (*(Ingress::get_ci(proj_i))) {
                    KernelTypes::KConstantInfo::Defn(pnl, pty, pval, _, _) => {
                      assert_eq!(pnl, bnl, "modeled projection: level count mismatch");
                      let pty_after_p = struct_eq_tele(pty, tty, np);
                      match (*(pty_after_p)) {
                        KernelTypes::KExprNode::Forall(sdom, rdom, _) => {
                          let expected_sdom = KernelWhnf::apply_spine(
                            (&(KernelTypes::KExprNode::Const(t_model, param_lvls))),
                            bvars_desc(np, np));
                          assert_eq!(KernelCheck::kexpr_struct_eq(sdom, expected_sdom), 1,
                            "modeled projection: subject domain mismatch");
                          assert_eq!(KernelCheck::kexpr_struct_eq(rdom, fdom), 1,
                            "modeled projection: codomain mismatch");
                          () } ,
                      };
                      check_proj_iota(rc, proj_i, iota_i, c_model, cty_m, raw_dom, np, bnl, cnf, fidx);
                      match Fields::is_zero(np) * Fields::is_zero(bnl) {
                        1 => {  () } ,
                        _ => {  check_proj_pure(rc, t_model, pval, np, bnl, cnf, fidx, aset) } ,
                      };
                      let proj_app = KernelWhnf::apply_spine(
                        (&(KernelTypes::KExprNode::Const(proj_i, param_lvls))),
                        Lists::snoc(bvars_desc(np + 1, np), (&(KernelTypes::KExprNode::BVar(0)))));
                      let ftele_next = KernelSubst::expr_inst1(frest, proj_app, 0);
                      check_member_projs(rc, t_model, c_model, tty, cty_m, ftele_next, crest,
                                         np, bnl, cnf, fidx + 1, aset, s2) } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def check_proj_iota := aiur_fn⟦
  fn check_proj_iota(rc: KernelRoles::RoleCtx, proj_i: Bytes::AddressRef, iota_i: Bytes::AddressRef,
                     c_model: Bytes::AddressRef, cty_m: KernelTypes::KExpr, raw_dom: KernelTypes::KExpr,
                     np: Field, bnl: Field, cnf: Field, fidx: Field) -> () {
      match (*(Ingress::get_ci(iota_i))) {
        KernelTypes::KConstantInfo::Thm(inl, ity, _) => {
          assert_eq!(inl, bnl, "modeled projection: iota level count mismatch");
          let ibody = struct_eq_tele(ity, cty_m, np + cnf);
          let (eqh, targs) = KernelTypes::collect_spine(ibody);
          match (*(eqh)) {
            KernelTypes::KExprNode::Const(eqa, eqls) => {
              assert_eq!(Bytes::address_eq(eqa, KernelRoles::role_addr(rc, KernelRoleSpec::role_eq())), 1,
                "modeled projection: iota statement is not an equation");
              let Lists::Node::Cons(_, eqrest) = (*(eqls));
              let Lists::Node::Nil = (*(eqrest));
              assert_eq!(Lists::length(targs), 3, "modeled projection: iota equation arity");
              let alpha = Lists::lookup(targs, 0);
              let lhs = Lists::lookup(targs, 1);
              let rhs = Lists::lookup(targs, 2);
              let expected_alpha = KernelSubst::expr_lift(raw_dom, cnf - fidx, 0);
              assert_eq!(KernelCheck::kexpr_struct_eq(alpha, expected_alpha), 1,
                "modeled projection: iota type slot mismatch");
              let param_lvls = KernelCheck::build_param_lvls_range(0, bnl, 0);
              let pvars = bvars_desc(np + cnf, np);
              let ctor_app = KernelWhnf::apply_spine(
                (&(KernelTypes::KExprNode::Const(c_model, param_lvls))),
                Lists::concat(pvars, bvars_desc(cnf, cnf)));
              let expected_lhs = KernelWhnf::apply_spine(
                (&(KernelTypes::KExprNode::Const(proj_i, param_lvls))),
                Lists::snoc(pvars, ctor_app));
              assert_eq!(KernelCheck::kexpr_struct_eq(lhs, expected_lhs), 1,
                "modeled projection: iota lhs mismatch");
              match (*(rhs)) {
                KernelTypes::KExprNode::BVar(rbv) => {
                  assert_eq!(rbv, (cnf - 1) - fidx, "modeled projection: iota rhs mismatch");
                  () } ,
              } } ,
          } } ,
      }
    }
⟧

  -- Coherence gate for parameterized or universe-polymorphic modeled projections: verifies
  -- that `t_model` unfolds to a native never-zero indexed auxiliary inductive `aux p⃗ (tag_c p⃗)`
  -- with unique constructor `aux.c_J` for `tag_c`, and that `pval` computes field `fidx` via
  -- `aux.rec` (either directly or through a mutual recursor model), returning either the raw
  -- field `f_{fidx}` or a level- and parameter-independent `unpack` tree walk over `aux`.

def find_aux_ctor_for_tag := aiur_fn⟦
  fn find_aux_ctor_for_tag(aux_blk: Bytes::AddressRef, anc: Field, k: Field,
                           np: Field, bnl: Field, aux_addr: Bytes::AddressRef,
                           tag_blk: Bytes::AddressRef, tag_cidx: Field, cnf: Field,
                           found_flag: Field, found_j: Field) -> Field {
      match anc - k {
        0 => {
          assert_eq!(found_flag, 1, "modeled projection: no aux constructor for tag");
          found_j } ,
        _ => {
          match (*(Ingress::get_ci_cprj(aux_blk, 0, k))) {
            KernelTypes::KConstantInfo::Ctor(knl, kty, _, _, _, knp, knf, _) => {
              assert_eq!(knl, bnl, "modeled projection: aux ctor level count");
              assert_eq!(knp, np, "modeled projection: aux ctor param count");
              let kres = KernelCheck::peel_n_foralls_zeta(kty, np + knf);
              let (kh, kargs) = KernelTypes::collect_spine(kres);
              match (*(kh)) {
                KernelTypes::KExprNode::Const(aux_addr2, _) => {
                  assert_eq!(Bytes::address_eq(aux_addr2, aux_addr), 1,
                    "modeled projection: aux ctor return head");
                  assert_eq!(Lists::length(kargs), np + 1,
                    "modeled projection: aux ctor return arity");
                  let kidx_arg = Lists::lookup(kargs, np);
                  let (kth, kt_args) = KernelTypes::collect_spine(kidx_arg);
                  match (*(kth)) {
                    KernelTypes::KExprNode::Const(ktc_addr, kt_lvls) => {
                      match (*(Ingress::get_ci(ktc_addr))) {
                        KernelTypes::KConstantInfo::Ctor(ktc_nl, _, ktc_blk, ktc_ind, ktc_cidx, ktc_np, ktc_cnf, _) => {
                          assert_eq!(Lists::length(kt_lvls), ktc_nl,
                            "modeled projection: aux ctor tag level arity");
                          assert_eq!(Lists::length(kt_args), ktc_np + ktc_cnf,
                            "modeled projection: aux ctor tag arity");
                          assert_eq!(Bytes::address_eq(ktc_blk, tag_blk), 1,
                            "modeled projection: aux ctor tag block mismatch");
                          assert_eq!(ktc_ind, 0, "modeled projection: aux ctor tag index mismatch");
                          match ktc_cidx - tag_cidx {
                            0 => {
                              assert_eq!(found_flag, 0,
                                "modeled projection: duplicate aux ctor for tag");
                              assert_eq!(knf, cnf,
                                "modeled projection: aux ctor field count mismatch");
                              find_aux_ctor_for_tag(aux_blk, anc, k + 1, np, bnl, aux_addr,
                                                    tag_blk, tag_cidx, cnf, 1, k) } ,
                            _ => {
                              find_aux_ctor_for_tag(aux_blk, anc, k + 1, np, bnl, aux_addr,
                                                    tag_blk, tag_cidx, cnf, found_flag, found_j) } ,
                          } } ,
                      } } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

  -- Extract `(rnf, ih_args)` from the `k`-th rule of `aux.rec`: checks that the rule peels
  -- `np + 1 + anc + rnf` lambdas to `BVar((rnf + anc - 1) - k)` applied to `rnf` field vars
  -- followed by `ih_args`.

def rec_rule_ih_args := aiur_fn⟦
  fn rec_rule_ih_args(rule: KernelTypes::KRecRule, np: Field, anc: Field, k: Field)
        -> (Field, Lists::List<KernelTypes::KExpr>) {
      match rule {
        KernelTypes::KRecRule::Mk(rcidx, rnf, rrhs) => {
          assert_eq!(rcidx, k, "modeled projection: aux rec rule ctor index");
          let total = ((np + 1) + anc) + rnf;
          let (rbody, rpeeled, _) = KernelCheck::peel_n_lams_collect(rrhs, total, 0, (&(Lists::Node::Nil)));
          assert_eq!(rpeeled, total, "modeled projection: aux rec rule lambda arity");
          let (rh, rargs) = KernelTypes::collect_spine(rbody);
          match (*(rh)) {
            KernelTypes::KExprNode::BVar(hbv) => {
              assert_eq!(hbv, ((rnf + anc) - 1) - k, "modeled projection: aux rec rule minor head");
              assert_eq!(UInt32::less_than_fields(rnf, Lists::length(rargs) + 1), 1,
                "modeled projection: aux rec rule arity");
              assert_eq!(KernelCheck::spec_params_ptr_eq(
                Lists::take(rargs, rnf), bvars_desc(rnf, rnf)), 1,
                "modeled projection: aux rec rule fields");
              (rnf, Lists::drop(rargs, rnf)) } ,
          } } ,
      }
    }
⟧

def check_unpack_rebuild_args := aiur_fn⟦
  fn check_unpack_rebuild_args(fargs: Lists::List<KernelTypes::KExpr>,
                               kftele: KernelTypes::KExpr, l: Field,
                               rnf: Field, n_ih: Field,
                               ih_args: Lists::List<KernelTypes::KExpr>,
                               aux_addr: Bytes::AddressRef,
                               aux_rec_addr: Bytes::AddressRef, np: Field, bnl: Field,
                               anc: Field) -> () {
      match (*(fargs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(arg, rest) => {
          match (*(kftele)) {
            KernelTypes::KExprNode::Forall(kfdom, kfrest, _) => {
              match (*(arg)) {
                KernelTypes::KExprNode::BVar(bv) => {
                  match bv - (((n_ih + rnf) - 1) - l) {
                    0 => {  () } ,
                    _ => {
                      assert_eq!(UInt32::less_than_fields(bv, n_ih), 1,
                        "modeled projection: unpack rebuild argument out of range");
                      let pos = (n_ih - 1) - bv;
                      let ih_expr = Lists::lookup(ih_args, pos);
                      let (ih_h, ih_sargs) = KernelTypes::collect_spine(ih_expr);
                      match (*(ih_h)) {
                        KernelTypes::KExprNode::Const(ih_rec, ih_lvls) => {
                          assert_eq!(Bytes::address_eq(ih_rec, aux_rec_addr), 1,
                            "modeled projection: unpack IH head is not aux.rec");
                          assert_eq!(KernelCheck::level_list_struct_eq(
                            ih_lvls, KernelCheck::build_param_lvls_range(0, bnl + 1, 0)), 1,
                            "modeled projection: unpack IH levels");
                          assert_eq!(Lists::length(ih_sargs), ((np + 1) + anc) + 2,
                            "modeled projection: unpack IH arity");
                          assert_eq!(KernelCheck::spec_params_ptr_eq(
                            Lists::take(ih_sargs, (np + 1) + anc),
                            bvars_desc(((np + 1) + anc) + rnf, (np + 1) + anc)), 1,
                            "modeled projection: unpack IH prefix args");
                          let ih_major = Lists::lookup(ih_sargs, ((np + 1) + anc) + 1);
                          match (*(ih_major)) {
                            KernelTypes::KExprNode::BVar(mbv) => {
                              assert_eq!(mbv, (rnf - 1) - l,
                                "modeled projection: unpack IH field mismatch");
                              () } ,
                          } } ,
                      };
                      let (kfh, _) = KernelTypes::collect_spine(kfdom);
                      match (*(kfh)) {
                        KernelTypes::KExprNode::Const(kfh_addr, _) => {
                          assert_eq!(Bytes::address_eq(kfh_addr, aux_addr), 1,
                            "modeled projection: unpack recursive field head mismatch");
                          () } ,
                      } } ,
                  };
                  check_unpack_rebuild_args(
                    rest, kfrest, l + 1, rnf, n_ih, ih_args, aux_addr, aux_rec_addr, np, bnl, anc) } ,
              } } ,
          } } ,
      }
    }
⟧

def check_unpack_minors := aiur_fn⟦
  fn check_unpack_minors(minors: Lists::List<KernelTypes::KExpr>,
                         arules: Lists::List<KernelTypes::KRecRule>,
                         aux_blk: Bytes::AddressRef, aux_addr: Bytes::AddressRef,
                         aux_rec_addr: Bytes::AddressRef,
                         np: Field, bnl: Field, anc: Field, k: Field) -> () {
      match (*(minors)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(arules));
          () } ,
        Lists::Node::Cons(minor_k, mrest) => {
          let Lists::Node::Cons(rule_k, rrest) = (*(arules));
          let (rnf_k, ih_args) = rec_rule_ih_args(rule_k, np, anc, k);
          let n_ih_k = Lists::length(ih_args);
          let (mbody_k, mpeeled_k, _) = KernelCheck::peel_n_lams_collect(
            minor_k, rnf_k + n_ih_k, 0, (&(Lists::Node::Nil)));
          assert_eq!(mpeeled_k, rnf_k + n_ih_k, "modeled projection: unpack minor lambda arity");
          let (mh_k, margs_k) = KernelTypes::collect_spine(mbody_k);
          let param_lvls = KernelCheck::build_param_lvls_range(0, bnl, 0);
          let aux_c_k = KernelCheck::projection_addr_ctor(0, k, aux_blk);
          match (*(mh_k)) {
            KernelTypes::KExprNode::Const(mc_addr, mc_lvls) => {
              match Bytes::address_eq(mc_addr, aux_c_k) {
                1 => {
                  assert_eq!(KernelCheck::level_list_struct_eq(mc_lvls, param_lvls), 1,
                    "modeled projection: unpack passthrough levels");
                  assert_eq!(Lists::length(margs_k), np + rnf_k,
                    "modeled projection: unpack passthrough arity");
                  assert_eq!(KernelCheck::spec_params_ptr_eq(
                    Lists::take(margs_k, np), bvars_desc((np + rnf_k) + n_ih_k, np)), 1,
                    "modeled projection: unpack passthrough params");
                  assert_eq!(KernelCheck::spec_params_ptr_eq(
                    Lists::drop(margs_k, np), bvars_desc(rnf_k + n_ih_k, rnf_k)), 1,
                    "modeled projection: unpack passthrough fields");
                  () } ,
                _ => {
                  match (*(Ingress::get_ci(mc_addr))) {
                    KernelTypes::KConstantInfo::Ctor(cnl_k, _, cblk_k, cind_k, _, cnp_k, cnf_k, _) => {
                      assert_eq!(cnf_k, rnf_k, "modeled projection: unpack rebuild field count");
                      assert_eq!(block_is_modeled(cblk_k), 0,
                        "modeled projection: unpack container is modeled");
                      assert_eq!(Fields::is_zero(cnp_k), 0,
                        "modeled projection: unpack container has zero params");
                      assert_eq!(Lists::length(mc_lvls), cnl_k,
                        "modeled projection: unpack container level arity");
                      assert_eq!(Lists::length(margs_k), cnp_k + cnf_k,
                        "modeled projection: unpack container arity");
                      match (*(Ingress::get_ci_iprj(cblk_k, cind_k))) {
                        KernelTypes::KConstantInfo::Induct(inl_k, ity_k, inp_k, ini_k, _, _, _, _) => {
                          assert_eq!(inl_k, cnl_k, "modeled projection: unpack container ind levels");
                          assert_eq!(inp_k, cnp_k, "modeled projection: unpack container ind params");
                          assert_eq!(type_sort_fixed_zeta(ity_k, inp_k + ini_k, mc_lvls), 1,
                            "modeled projection: unpack container sort is not fixed");
                          match (*(Ingress::get_ci_cprj(aux_blk, 0, k))) {
                            KernelTypes::KConstantInfo::Ctor(_, kty, _, _, _, _, _, _) => {
                              let kftele = KernelCheck::peel_n_foralls(kty, np);
                              check_unpack_rebuild_args(
                                Lists::drop(margs_k, cnp_k), kftele, 0, rnf_k, n_ih_k, ih_args,
                                aux_addr, aux_rec_addr, np, bnl, anc) } ,
                          } } ,
                      } } ,
                  } } ,
              } } ,
          };
          check_unpack_minors(mrest, rrest, aux_blk, aux_addr, aux_rec_addr, np, bnl, anc, k + 1) } ,
      }
    }
⟧

def check_proj_nested_minor := aiur_fn⟦
  fn check_proj_nested_minor(mbody: KernelTypes::KExpr, aux_blk: Bytes::AddressRef,
                             aux_addr: Bytes::AddressRef,
                             aux_rec_addr: Bytes::AddressRef,
                             arules: Lists::List<KernelTypes::KRecRule>,
                             np: Field, bnl: Field, anc: Field, cnf: Field, n_ih_j: Field,
                             fidx: Field, aset: RBTreeMap::RBTreeMap<Field>) -> () {
      let target_bv = ((n_ih_j + cnf) - 1) - fidx;
      match (*(mbody)) {
        KernelTypes::KExprNode::BVar(bv) => {
          assert_eq!(bv, target_bv, "modeled projection: minor field variable mismatch");
          () } ,
        _ => {
          let (uh, uargs) = KernelTypes::collect_spine(mbody);
          let param_lvls = KernelCheck::build_param_lvls_range(0, bnl, 0);
          match (*(uh)) {
            KernelTypes::KExprNode::Const(u_addr, u_lvls) => {
              assert_eq!(KernelClaim::addr_set_member(u_addr, aset), 1,
                "modeled projection: unpack helper is not advice");
              assert_eq!(KernelCheck::level_list_struct_eq(u_lvls, param_lvls), 1,
                "modeled projection: unpack helper levels");
              let ulen = Lists::length(uargs);
              assert_eq!(UInt32::less_than_fields(np, ulen), 1,
                "modeled projection: unpack helper arity");
              assert_eq!(KernelCheck::spec_params_ptr_eq(
                Lists::take(uargs, np), bvars_desc(((np + 1) + cnf) + n_ih_j, np)), 1,
                "modeled projection: unpack helper params");
              let ulast = Lists::lookup(uargs, ulen - 1);
              match (*(ulast)) {
                KernelTypes::KExprNode::BVar(ubv) => {
                  assert_eq!(ubv, target_bv, "modeled projection: unpack helper subject mismatch");
                  () } ,
              };
              match (*(Ingress::get_ci(u_addr))) {
                KernelTypes::KConstantInfo::Defn(unl, _, uval, _, _) => {
                  assert_eq!(unl, bnl, "modeled projection: unpack helper level count");
                  let (ubody, upeeled, _) = KernelCheck::peel_n_lams_collect(
                    uval, ulen, 0, (&(Lists::Node::Nil)));
                  assert_eq!(upeeled, ulen, "modeled projection: unpack helper lambda arity");
                  let (uah, ua_args) = KernelTypes::collect_spine(ubody);
                  match (*(uah)) {
                    KernelTypes::KExprNode::Const(ua_addr, ua_lvls) => {
                      assert_eq!(KernelClaim::addr_set_member(ua_addr, aset), 1,
                        "modeled projection: unpackAll is not advice");
                      assert_eq!(KernelCheck::level_list_struct_eq(ua_lvls, param_lvls), 1,
                        "modeled projection: unpackAll levels");
                      assert_eq!(Lists::length(ua_args), np + 2,
                        "modeled projection: unpackAll arity");
                      assert_eq!(KernelCheck::spec_params_ptr_eq(
                        Lists::take(ua_args, np), bvars_desc(ulen, np)), 1,
                        "modeled projection: unpackAll params");
                      match (*(Lists::lookup(ua_args, np + 1))) {
                        KernelTypes::KExprNode::BVar(abv) => {
                          assert_eq!(abv, 0, "modeled projection: unpackAll subject");
                          () } ,
                      };
                      match (*(Ingress::get_ci(ua_addr))) {
                        KernelTypes::KConstantInfo::Defn(uanl, _, uaval, _, _) => {
                          assert_eq!(uanl, bnl, "modeled projection: unpackAll level count");
                          let (uabody, uapeeled, _) = KernelCheck::peel_n_lams_collect(
                            uaval, np, 0, (&(Lists::Node::Nil)));
                          assert_eq!(uapeeled, np, "modeled projection: unpackAll lambda arity");
                          let (uarh, uar_args) = KernelTypes::collect_spine(uabody);
                          match (*(uarh)) {
                            KernelTypes::KExprNode::Const(uar_addr, uar_lvls) => {
                              assert_eq!(Bytes::address_eq(uar_addr, aux_rec_addr), 1,
                                "modeled projection: unpackAll recursor mismatch");
                              assert_eq!(Lists::length(uar_lvls), bnl + 1,
                                "modeled projection: unpackAll recursor level arity");
                              assert_eq!(KernelCheck::level_list_struct_eq(
                                Lists::drop(uar_lvls, 1), param_lvls), 1,
                                "modeled projection: unpackAll recursor levels");
                              assert_eq!(Lists::length(uar_args), (np + 1) + anc,
                                "modeled projection: unpackAll recursor arity");
                              assert_eq!(KernelCheck::spec_params_ptr_eq(
                                Lists::take(uar_args, np), bvars_desc(np, np)), 1,
                                "modeled projection: unpackAll recursor params");
                              check_unpack_minors(
                                Lists::drop(uar_args, np + 1), arules, aux_blk, aux_addr,
                                aux_rec_addr, np, bnl, anc, 0) } ,
                          } } ,
                      } } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def check_proj_pure := aiur_fn⟦
  fn check_proj_pure(rc: KernelRoles::RoleCtx, t_model: Bytes::AddressRef, pval: KernelTypes::KExpr,
                     np: Field, bnl: Field, cnf: Field, fidx: Field,
                     aset: RBTreeMap::RBTreeMap<Field>) -> () {
      let param_lvls = KernelCheck::build_param_lvls_range(0, bnl, 0);
      match (*(Ingress::get_ci(t_model))) {
        KernelTypes::KConstantInfo::Defn(tmnl, _, tmval, _, _) => {
          assert_eq!(tmnl, bnl, "modeled projection: type model level count");
          let (tm_body, tm_peeled, _) = KernelCheck::peel_n_lams_collect(
            tmval, np, 0, (&(Lists::Node::Nil)));
          assert_eq!(tm_peeled, np, "modeled projection: type model lambda arity");
          let (aux_h, aux_args) = KernelTypes::collect_spine(tm_body);
          match (*(aux_h)) {
            KernelTypes::KExprNode::Const(aux_addr, aux_lvls) => {
              assert_eq!(KernelCheck::level_list_struct_eq(aux_lvls, param_lvls), 1,
                "modeled projection: aux levels mismatch");
              assert_eq!(Lists::length(aux_args), np + 1, "modeled projection: aux arity");
              assert_eq!(KernelCheck::spec_params_ptr_eq(
                Lists::take(aux_args, np), bvars_desc(np, np)), 1,
                "modeled projection: aux params mismatch");
              let tag_app = Lists::lookup(aux_args, np);
              let (tc_h, tc_args) = KernelTypes::collect_spine(tag_app);
              match (*(tc_h)) {
                KernelTypes::KExprNode::Const(tag_c_addr, tc_lvls) => {
                  assert_eq!(KernelCheck::level_list_struct_eq(tc_lvls, param_lvls), 1,
                    "modeled projection: tag ctor levels mismatch");
                  assert_eq!(KernelCheck::spec_params_ptr_eq(tc_args, bvars_desc(np, np)), 1,
                    "modeled projection: tag ctor params mismatch");
                  match (*(Ingress::get_ci(tag_c_addr))) {
                    KernelTypes::KConstantInfo::Ctor(tcnl, _, tag_blk, tag_ind, tag_cidx, tcnp, tcnf, _) => {
                      assert_eq!(tcnl, bnl, "modeled projection: tag ctor level count");
                      assert_eq!(tag_ind, 0, "modeled projection: tag ind index");
                      assert_eq!(tcnp, np, "modeled projection: tag ctor param count");
                      assert_eq!(tcnf, 0, "modeled projection: tag ctor field count");
                      assert_eq!(block_is_modeled(tag_blk), 0, "modeled projection: tag is modeled");
                      let tag_addr = KernelDefEq::compute_iprj_addr(tag_blk, 0);
                      let tag_r1 = KernelRoles::role_index_of(rc, tag_addr);
                      assert_eq!(Fields::is_zero(tag_r1 - (KernelRoleSpec::role_nat() + 1)), 0,
                        "modeled projection: tag is Nat");
                      match (*(Ingress::get_ci_iprj(tag_blk, 0))) {
                        KernelTypes::KConstantInfo::Induct(tlnl, tlty, tlnp, tlni, tlnc, _, _, _) => {
                          assert_eq!(tlnl, bnl, "modeled projection: tag level count");
                          assert_eq!(tlnp, np, "modeled projection: tag param count");
                          assert_eq!(tlni, 0, "modeled projection: tag index count");
                          assert_eq!(UInt32::less_than_fields(1, tlnc), 1,
                            "modeled projection: tag ctor count");
                          assert_eq!(KernelWhnf::type_sort_never(tlty, tlnp, param_lvls), 1,
                            "modeled projection: tag sort may be zero");
                          () } ,
                      };
                      match (*(Ingress::get_ci(aux_addr))) {
                        KernelTypes::KConstantInfo::Induct(anl, aty, anp, ani, anc, _, aux_blk, aind) => {
                          assert_eq!(anl, bnl, "modeled projection: aux level count");
                          assert_eq!(anp, np, "modeled projection: aux param count");
                          assert_eq!(ani, 1, "modeled projection: aux index count");
                          assert_eq!(aind, 0, "modeled projection: aux member index");
                          assert_eq!(block_is_modeled(aux_blk), 0, "modeled projection: aux is modeled");
                          assert_eq!(KernelWhnf::type_sort_never(aty, anp + 1, param_lvls), 1,
                            "modeled projection: aux sort may be zero");
                          let j_idx = find_aux_ctor_for_tag(
                            aux_blk, anc, 0, np, bnl, aux_addr, tag_blk, tag_cidx, cnf, 0, 0);
                          check_proj_pure_body(
                            pval, aux_blk, aux_addr, anc, tag_c_addr, np, bnl, cnf, fidx, j_idx, aset) } ,
                      } } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def check_proj_pure_rec := aiur_fn⟦
  fn check_proj_pure_rec(phead_addr: Bytes::AddressRef, pargs: Lists::List<KernelTypes::KExpr>,
                         arnl: Field, arty: KernelTypes::KExpr, arnp: Field, arni: Field,
                         arnmot: Field, arnmin: Field,
                         arules: Lists::List<KernelTypes::KRecRule>,
                         aux_blk: Bytes::AddressRef, aux_addr: Bytes::AddressRef,
                         anc: Field, tag_c_addr: Bytes::AddressRef,
                         np: Field, bnl: Field, cnf: Field, fidx: Field, j_idx: Field,
                         aset: RBTreeMap::RBTreeMap<Field>) -> () {
      let param_lvls = KernelCheck::build_param_lvls_range(0, bnl, 0);
      assert_eq!(Bytes::address_eq(rec_family_block(phead_addr), aux_blk), 1,
        "modeled projection: recursor block mismatch");
      assert_eq!(arnl, bnl + 1, "modeled projection: aux rec level count");
      assert_eq!(arnp, np, "modeled projection: aux rec param count");
      assert_eq!(arni, 1, "modeled projection: aux rec index count");
      assert_eq!(arnmot, 1, "modeled projection: aux rec motive count");
      assert_eq!(arnmin, anc, "modeled projection: aux rec minor count");
      let maj_pi = KernelCheck::peel_n_foralls(arty, ((np + 1) + anc) + 1);
      match (*(maj_pi)) {
        KernelTypes::KExprNode::Forall(maj_dom, _, _) => {
          let (maj_h, maj_args) = KernelTypes::collect_spine(maj_dom);
          match (*(maj_h)) {
            KernelTypes::KExprNode::Const(maj_addr, maj_lvls) => {
              assert_eq!(Bytes::address_eq(maj_addr, aux_addr), 1,
                "modeled projection: aux rec major head mismatch");
              assert_eq!(KernelCheck::level_list_struct_eq(
                maj_lvls, KernelCheck::build_param_lvls_range(1, bnl, 0)), 1,
                "modeled projection: aux rec major levels");
              assert_eq!(Lists::length(maj_args), np + 1,
                "modeled projection: aux rec major arity");
              assert_eq!(KernelCheck::spec_params_ptr_eq(
                Lists::take(maj_args, np), bvars_desc(((np + 1) + anc) + 1, np)), 1,
                "modeled projection: aux rec major params");
              match (*(Lists::lookup(maj_args, np))) {
                KernelTypes::KExprNode::BVar(mbv) => {
                  assert_eq!(mbv, 0, "modeled projection: aux rec major index");
                  () } ,
              } } ,
          } } ,
      };
      assert_eq!(Lists::length(pargs), ((np + 1) + anc) + 2,
        "modeled projection: aux rec arity");
      assert_eq!(KernelCheck::spec_params_ptr_eq(
        Lists::take(pargs, np), bvars_desc(np + 1, np)), 1,
        "modeled projection: aux rec params");
      let expected_tag = KernelWhnf::apply_spine(
        (&(KernelTypes::KExprNode::Const(tag_c_addr, param_lvls))),
        bvars_desc(np + 1, np));
      assert_eq!(KernelCheck::kexpr_struct_eq(
        Lists::lookup(pargs, (np + 1) + anc), expected_tag), 1,
        "modeled projection: aux rec tag arg");
      match (*(Lists::lookup(pargs, ((np + 1) + anc) + 1))) {
        KernelTypes::KExprNode::BVar(sbv) => {
          assert_eq!(sbv, 0, "modeled projection: aux rec subject");
          () } ,
      };
      let (rnf_j, ih_args_j) = rec_rule_ih_args(Lists::lookup(arules, j_idx), np, anc, j_idx);
      assert_eq!(rnf_j, cnf, "modeled projection: aux rec rule field count");
      let n_ih_j = Lists::length(ih_args_j);
      let minor_j = Lists::lookup(pargs, (np + 1) + j_idx);
      let (mbody, mpeeled, _) = KernelCheck::peel_n_lams_collect(
        minor_j, cnf + n_ih_j, 0, (&(Lists::Node::Nil)));
      assert_eq!(mpeeled, cnf + n_ih_j, "modeled projection: minor lambda arity");
      check_proj_nested_minor(
        mbody, aux_blk, aux_addr, phead_addr, arules, np, bnl, anc, cnf, n_ih_j, fidx, aset)
    }
⟧

def check_proj_pure_defn := aiur_fn⟦
  fn check_proj_pure_defn(phead_addr: Bytes::AddressRef, pargs: Lists::List<KernelTypes::KExpr>,
                          rnl: Field, rval: KernelTypes::KExpr,
                          aux_blk: Bytes::AddressRef, aux_addr: Bytes::AddressRef,
                          anc: Field, tag_c_addr: Bytes::AddressRef,
                          np: Field, bnl: Field, cnf: Field, fidx: Field, j_idx: Field,
                          aset: RBTreeMap::RBTreeMap<Field>) -> () {
      assert_eq!(KernelClaim::addr_set_member(phead_addr, aset), 1,
        "modeled projection: recursor model is not advice");
      assert_eq!(rnl, bnl + 1, "modeled projection: recursor model level count");
      let plen = Lists::length(pargs);
      assert_eq!(UInt32::less_than_fields((np + anc) + 1, plen), 1,
        "modeled projection: recursor model arity");
      let n_mot = (plen - np) - (anc + 1);
      assert_eq!(KernelCheck::spec_params_ptr_eq(
        Lists::take(pargs, np), bvars_desc(np + 1, np)), 1,
        "modeled projection: recursor model params");
      match (*(Lists::lookup(pargs, plen - 1))) {
        KernelTypes::KExprNode::BVar(sbv) => {
          assert_eq!(sbv, 0, "modeled projection: recursor model subject");
          () } ,
      };
      let (rbody, rpeeled, _) = KernelCheck::peel_n_lams_collect(
        rval, plen, 0, (&(Lists::Node::Nil)));
      assert_eq!(rpeeled, plen, "modeled projection: recursor model lambda arity");
      let (rh, rargs) = KernelTypes::collect_spine(rbody);
      match (*(rh)) {
        KernelTypes::KExprNode::Const(aux_rec_addr, ar_lvls) => {
          assert_eq!(Bytes::address_eq(rec_family_block(aux_rec_addr), aux_blk), 1,
            "modeled projection: mutual aux rec block mismatch");
          assert_eq!(KernelCheck::level_list_struct_eq(
            ar_lvls, KernelCheck::build_param_lvls_range(0, bnl + 1, 0)), 1,
            "modeled projection: mutual aux rec levels");
          match (*(Ingress::get_ci(aux_rec_addr))) {
            KernelTypes::KConstantInfo::Rec(arnl, arty, arnp, arni, arnmot, arnmin, arules, _, _, _, _) => {
              assert_eq!(arnl, bnl + 1, "modeled projection: mutual aux rec level count");
              assert_eq!(arnp, np, "modeled projection: mutual aux rec param count");
              assert_eq!(arni, 1, "modeled projection: mutual aux rec index count");
              assert_eq!(arnmot, 1, "modeled projection: mutual aux rec motive count");
              assert_eq!(arnmin, anc, "modeled projection: mutual aux rec minor count");
              let maj_pi = KernelCheck::peel_n_foralls(arty, ((np + 1) + anc) + 1);
              match (*(maj_pi)) {
                KernelTypes::KExprNode::Forall(maj_dom, _, _) => {
                  let (maj_h, maj_args) = KernelTypes::collect_spine(maj_dom);
                  match (*(maj_h)) {
                    KernelTypes::KExprNode::Const(maj_addr, maj_lvls) => {
                      assert_eq!(Bytes::address_eq(maj_addr, aux_addr), 1,
                        "modeled projection: mutual aux rec major head mismatch");
                      assert_eq!(KernelCheck::level_list_struct_eq(
                        maj_lvls, KernelCheck::build_param_lvls_range(1, bnl, 0)), 1,
                        "modeled projection: mutual aux rec major levels");
                      assert_eq!(Lists::length(maj_args), np + 1,
                        "modeled projection: mutual aux rec major arity");
                      assert_eq!(KernelCheck::spec_params_ptr_eq(
                        Lists::take(maj_args, np), bvars_desc(((np + 1) + anc) + 1, np)), 1,
                        "modeled projection: mutual aux rec major params");
                      match (*(Lists::lookup(maj_args, np))) {
                        KernelTypes::KExprNode::BVar(mbv) => {
                          assert_eq!(mbv, 0, "modeled projection: mutual aux rec major index");
                          () } ,
                      } } ,
                  } } ,
              };
              assert_eq!(Lists::length(rargs), ((np + 1) + anc) + 2,
                "modeled projection: mutual aux rec arity");
              assert_eq!(KernelCheck::spec_params_ptr_eq(
                Lists::take(rargs, np), bvars_desc(plen, np)), 1,
                "modeled projection: mutual aux rec params");
              assert_eq!(KernelCheck::spec_params_ptr_eq(
                Lists::take(Lists::drop(rargs, np + 1), anc), bvars_desc(anc + 1, anc)), 1,
                "modeled projection: mutual aux rec minors");
              let expected_rtag = KernelWhnf::apply_spine(
                (&(KernelTypes::KExprNode::Const(tag_c_addr,
                    KernelCheck::build_param_lvls_range(1, bnl, 0)))),
                bvars_desc(plen, np));
              assert_eq!(KernelCheck::kexpr_struct_eq(
                Lists::lookup(rargs, (np + 1) + anc), expected_rtag), 1,
                "modeled projection: mutual aux rec tag arg");
              match (*(Lists::lookup(rargs, ((np + 1) + anc) + 1))) {
                KernelTypes::KExprNode::BVar(rbv) => {
                  assert_eq!(rbv, 0, "modeled projection: mutual aux rec subject");
                  () } ,
              };
              let (rnf_j, ih_args_j) = rec_rule_ih_args(Lists::lookup(arules, j_idx), np, anc, j_idx);
              assert_eq!(rnf_j, cnf, "modeled projection: mutual aux rec rule field count");
              let n_ih_j = Lists::length(ih_args_j);
              let minor_j = Lists::lookup(pargs, (np + n_mot) + j_idx);
              let (mbody, mpeeled, _) = KernelCheck::peel_n_lams_collect(
                minor_j, cnf + n_ih_j, 0, (&(Lists::Node::Nil)));
              assert_eq!(mpeeled, cnf + n_ih_j, "modeled projection: mutual minor lambda arity");
              check_proj_nested_minor(
                mbody, aux_blk, aux_addr, aux_rec_addr, arules, np, bnl, anc, cnf, n_ih_j, fidx, aset) } ,
          } } ,
      }
    }
⟧

def check_proj_pure_body := aiur_fn⟦
  fn check_proj_pure_body(pval: KernelTypes::KExpr, aux_blk: Bytes::AddressRef,
                          aux_addr: Bytes::AddressRef, anc: Field,
                          tag_c_addr: Bytes::AddressRef, np: Field, bnl: Field, cnf: Field,
                          fidx: Field, j_idx: Field, aset: RBTreeMap::RBTreeMap<Field>) -> () {
      let param_lvls = KernelCheck::build_param_lvls_range(0, bnl, 0);
      let (pbody, ppeeled, _) = KernelCheck::peel_n_lams_collect(pval, np + 1, 0, (&(Lists::Node::Nil)));
      assert_eq!(ppeeled, np + 1, "modeled projection: body lambda arity");
      let (ph, pargs) = KernelTypes::collect_spine(pbody);
      match (*(ph)) {
        KernelTypes::KExprNode::Const(phead_addr, phead_lvls) => {
          assert_eq!(Lists::length(phead_lvls), bnl + 1, "modeled projection: head level arity");
          assert_eq!(KernelCheck::level_list_struct_eq(Lists::drop(phead_lvls, 1), param_lvls), 1,
            "modeled projection: head levels mismatch");
          match (*(Ingress::get_ci(phead_addr))) {
            KernelTypes::KConstantInfo::Rec(arnl, arty, arnp, arni, arnmot, arnmin, arules, _, _, _, _) => {
              check_proj_pure_rec(phead_addr, pargs, arnl, arty, arnp, arni, arnmot, arnmin, arules,
                                  aux_blk, aux_addr, anc, tag_c_addr, np, bnl, cnf, fidx, j_idx, aset) } ,
            KernelTypes::KConstantInfo::Defn(rnl, _, rval, _, _) => {
              check_proj_pure_defn(phead_addr, pargs, rnl, rval,
                                   aux_blk, aux_addr, anc, tag_c_addr, np, bnl, cnf, fidx, j_idx, aset) } ,
          } } ,
      }
    }
⟧

  -- Negative-occurrence scan on a block's constructors, mirroring IxC's
  -- `BlockHasNegOcc` (`IxC/Kernel/Frontend/InModel/Check.lean`): a block with any
  -- member mentioned in a Pi domain of any constructor field has no in-process
  -- projection models, so `modeled_proj_eligible` rejects it.

def field_has_neg := aiur_fn⟦
  fn field_has_neg(e: KernelTypes::KExpr, mems: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(e)) {
        KernelTypes::KExprNode::Forall(dom, body, _) => {
          match KernelWhnf::se_mentions(dom, mems) {
            1 => {  1 } ,
            _ => {  field_has_neg(body, mems) } ,
          } } ,
        KernelTypes::KExprNode::Let(_, v, b) => {
          field_has_neg(KernelSubst::expr_inst1(b, v, 0), mems) } ,
        _ => {  0 } ,
      }
    }
⟧

def fields_have_neg := aiur_fn⟦
  fn fields_have_neg(ty: KernelTypes::KExpr, nf: Field, mems: Lists::List<Bytes::AddressRef>) -> Field {
      match nf {
        0 => {  0 } ,
        _ => {
          match (*(ty)) {
            KernelTypes::KExprNode::Forall(dom, body, _) => {
              match field_has_neg(dom, mems) {
                1 => {  1 } ,
                _ => {  fields_have_neg(body, nf - 1, mems) } ,
              } } ,
            KernelTypes::KExprNode::Let(_, v, b) => {
              fields_have_neg(KernelSubst::expr_inst1(b, v, 0), nf, mems) } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def ctors_have_neg := aiur_fn⟦
  fn ctors_have_neg(block: Bytes::AddressRef, pos: Field, n_ctors: Field,
                    mems: Lists::List<Bytes::AddressRef>, cidx: Field) -> Field {
      match n_ctors - cidx {
        0 => {  0 } ,
        _ => {
          match (*(Ingress::get_ci_cprj(block, pos, cidx))) {
            KernelTypes::KConstantInfo::Ctor(_, cty, _, _, _, np, nf, _) => {
              let body = KernelCheck::peel_n_foralls_zeta(cty, np);
              let found = match KernelWhnf::se_mentions(body, mems) {
                0 => {  0 } ,
                _ => {  fields_have_neg(body, nf, mems) } ,
              };
              match found {
                1 => {  1 } ,
                _ => {  ctors_have_neg(block, pos, n_ctors, mems, cidx + 1) } ,
              } } ,
          } } ,
      }
    }
⟧

def members_have_neg := aiur_fn⟦
  fn members_have_neg(block: Bytes::AddressRef, members: Lists::List<Ixon::MutConst>,
                      pos: Field, mems: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(members)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Indc(ind) => {
              match ind {
                Ixon::Inductive::Mk(_, _, _, _, _, ctors) => {
                  match ctors_have_neg(block, pos, Lists::length(ctors), mems, 0) {
                    1 => {  1 } ,
                    _ => {  members_have_neg(block, rest, pos + 1, mems) } ,
                  } } ,
              } } ,
            _ => {  members_have_neg(block, rest, pos + 1, mems) } ,
          } } ,
      }
    }
⟧

def block_has_neg_occ := aiur_fn⟦
  fn block_has_neg_occ(block: Bytes::AddressRef) -> Field {
      let c = Ingress::load_verified_constant(block);
      match c {
        Ixon::Constant::Mk(info, _, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              let mems = Ingress::build_recur_addrs(members, block);
              members_have_neg(block, members, 0, mems) } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

  -- Whether member `ind_idx` of a modeled block is eligible for `.proj`: one constructor,
  -- zero indices, never-zero declared sort, matching constructor parameter count and at
  -- least one field, and no syntactic negative occurrence in the block. Pure channel-2
  -- function of `(block, ind_idx)`.

def modeled_proj_eligible := aiur_fn⟦
  fn modeled_proj_eligible(block: Bytes::AddressRef, ind_idx: Field) -> Field {
      match (*(Ingress::get_ci_iprj(block, ind_idx))) {
        KernelTypes::KConstantInfo::Induct(nl, ty, np, ni, nctors, _, _, _) => {
          match Fields::is_zero(ni) * Fields::is_zero(nctors - 1) {
            1 => {
              match KernelWhnf::type_sort_never(ty, np, KernelCheck::build_param_lvls_range(0, nl, 0)) {
                1 => {
                  match (*(Ingress::get_ci_cprj(block, ind_idx, 0))) {
                    KernelTypes::KConstantInfo::Ctor(cnl, _, _, _, _, cnp, cnf, _) => {
                      let ok = (Fields::is_zero(cnl - nl) * Fields::is_zero(cnp - np))
                               * (1 - Fields::is_zero(cnf));
                      match ok {
                        1 => {  1 - block_has_neg_occ(block) } ,
                        _ => {  0 } ,
                      } } ,
                    _ => {  0 } ,
                  } } ,
                _ => {  0 } ,
              } } ,
            _ => {  0 } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

  -- Whether `.proj` is allowed at member `ind_idx` of `block`: always 1 on native blocks,
  -- and `modeled_proj_eligible` on modeled blocks.

def proj_allowed_at := aiur_fn⟦
  fn proj_allowed_at(block: Bytes::AddressRef, ind_idx: Field) -> Field {
      match block_is_modeled(block) {
        0 => {  1 } ,
        _ => {  modeled_proj_eligible(block, ind_idx) } ,
      }
    }
⟧

end

end IxVM
