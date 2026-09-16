use super::*;
use crate::{
  boolean::BooleanR1csPlan,
  ixby::paged_code::{BLOCKS, CONSTRUCTORS, FUNCTIONS},
};
fn extend(b: &Builder, x: &[usize], width: usize) -> Bits {
  let mut r = x.to_vec();
  r.resize(width, b.zero);
  r
}
fn function(b: &mut Builder, on: usize, x: &[usize]) {
  b.require_zero(on, &x[32..]);
  bound(b, on, &x[..8], 64);
  bound(b, on, &x[16..32], 256);
  let entry = extend(b, &x[8..16], 16);
  let good = lt(b, &entry, &x[16..32]);
  b.require(on, good);
}
fn header(b: &mut Builder, on: usize, x: &[usize]) {
  bound(b, on, &x[..8], 128);
  b.require_zero(on, &x[11..16]);
  b.require_zero(on, &x[19..24]);
  bound(b, on, &x[32..40], 65);
  bound(b, on, &x[40..48], 64);
  bound(b, on, &x[48..56], 128);
  b.require_zero(on, &x[56..64]);
  b.require_zero(on, &x[112..]);
}
fn fn_address(b: &Builder, f: &[usize]) -> Bits {
  let mut a = b.constant(128, FUNCTIONS);
  a[..16].copy_from_slice(f);
  a
}
fn block_address(b: &Builder, f: &[usize], block: &[usize]) -> Bits {
  let mut a = b.constant(128, BLOCKS);
  a[16..32].copy_from_slice(f);
  a[8..16].copy_from_slice(block);
  a
}
fn ctor_address(b: &mut Builder, index: &[usize]) -> Bits {
  let x = extend(b, index, 16);
  let twice = plus(b, b.one, &x, &x);
  let triple = plus(b, b.one, &x, &twice);
  let at = plus(b, b.one, &triple, &b.constant(16, 2));
  let mut a = b.constant(128, CONSTRUCTORS);
  a[..16].copy_from_slice(&at);
  a
}
fn control(
  b: &Builder,
  phase: u64,
  f: &[usize],
  block: &[usize],
  alt: &[usize],
) -> Bits {
  let mut c = b.constant(128, phase);
  c[8..24].copy_from_slice(f);
  c[24..32].copy_from_slice(block);
  c[32..40].copy_from_slice(alt);
  c
}
pub(super) fn plan() -> BooleanR1csPlan {
  let mut builder = Builder::new(INPUTS, OUTPUTS, 1 << 16);
  let b = &mut builder;
  bound(b, b.one, &word(0), 1024);
  let nonzero = b.any(&word(0));
  b.require(b.one, nonzero);
  bound(b, b.one, &word(1), 256);
  let entry = lt(b, &word(2), &word(0));
  b.require(b.one, entry);
  let e = word(6)[0];
  b.require_zero(b.one, &word(6)[1..]);
  let c = word(3);
  let cf = word(4);
  let ch = word(5);
  b.require_zero(b.one, &c[2..8]);
  b.require_zero(b.one, &c[40..]);
  let phase = [0, 1, 2, 3].map(|v| eqc(b, &c[..2], v));
  let on = phase.map(|p| b.b.and(e, p));
  let f = &c[8..24];
  let block = &c[24..32];
  let alt = &c[32..40];
  let live = b.not(phase[3]);
  let good = lt(b, f, &word(0)[..16]);
  b.require(live, good);
  same(b, phase[3], f, &word(0)[..16]);
  let empty = b.any(&[phase[0], phase[3]]);
  b.require_zero(empty, &c[24..40]);
  b.require_zero(empty, &cf);
  let body = b.any(&[phase[1], phase[2]]);
  function(b, body, &cf);
  let good = lt(b, &extend(b, block, 16), &cf[16..32]);
  b.require(body, good);
  let noalt = b.not(phase[2]);
  b.require_zero(noalt, alt);
  b.require_zero(noalt, &ch);
  header(b, phase[2], &ch);
  let case = eqc(b, &ch[8..16], 5);
  b.require(phase[2], case);
  let good = lt(b, alt, &ch[48..56]);
  b.require(phase[2], good);
  let r = [word(7), word(9), word(11), word(13)];
  function(b, on[0], &r[0]);
  header(b, on[1], &r[0]);
  b.require_zero(on[2], &r[0][16..]);
  let inst = std::array::from_fn::<_, 8, _>(|i| eqc(b, &r[0][8..16], i as u64));
  let op = std::array::from_fn::<_, 8, _>(|i| eqc(b, &r[0][16..24], i as u64));
  let letrow = b.b.and(on[1], inst[0]);
  let callop = b.any(&[op[4], op[5]]);
  let letforeign = b.b.and(letrow, callop);
  let tailforeign = b.b.and(on[1], inst[2]);
  let foreign = b.any(&[letforeign, tailforeign]);
  let closure = b.b.and(letrow, op[4]);
  let callop = b.b.and(letrow, op[5]);
  let call = b.any(&[callop, tailforeign]);
  let construct = b.b.and(letrow, op[2]);
  let selflet = b.b.and(letrow, op[6]);
  let selftail = b.b.and(on[1], inst[3]);
  let selfcall = b.any(&[selflet, selftail]);
  let branchlike = b.any(&[inst[6], inst[7]]);
  let branches = b.b.and(on[1], branchlike);
  let target0 = b.any(&[letrow, branches]);
  let casenat = b.b.and(on[1], inst[6]);
  function(b, foreign, &r[1]);
  let good = lt(b, &r[0][64..80], &word(0)[..16]);
  b.require(foreign, good);
  same(b, call, &r[0][40..48], &r[1][..8]);
  let good = lt(b, &r[0][40..48], &r[1][..8]);
  b.require(closure, good);
  same(b, selfcall, &r[0][40..48], &cf[..8]);
  let good = lt(b, &r[0][64..80], &word(1)[..16]);
  b.require(construct, good);
  same(b, construct, &extend(b, &r[0][40..48], 128), &r[1]);
  let ctorread = b.any(&[construct, on[2]]);
  bound(b, ctorread, &r[1], 64);
  let good = lt(b, &extend(b, &r[0][..8], 16), &word(1)[..16]);
  b.require(on[2], good);
  // Function entries and every static successor have the declared local frame.
  header(b, on[0], &r[1]);
  same(b, on[0], &r[1][..8], &r[0][..8]);
  let target2 = b.any(&[target0, on[2]]);
  header(b, target2, &r[2]);
  header(b, branches, &r[3]);
  let good = lt(b, &extend(b, &r[0][80..88], 16), &cf[16..32]);
  b.require(target0, good);
  let good = lt(b, &extend(b, &r[0][88..96], 16), &cf[16..32]);
  b.require(branches, good);
  let good = lt(b, &extend(b, &r[0][8..16], 16), &cf[16..32]);
  b.require(on[2], good);
  let current = extend(b, &r[0][..8], 9);
  let mut inc = b.constant(9, 0);
  inc[0] = letrow;
  let n0 = plus(b, target0, &current, &inc);
  same(b, target0, &n0, &extend(b, &r[2][..8], 9));
  inc[0] = casenat;
  let n1 = plus(b, branches, &current, &inc);
  same(b, branches, &n1, &extend(b, &r[3][..8], 9));
  let nalt = plus(b, on[2], &extend(b, &ch[..8], 9), &extend(b, &r[1][..8], 9));
  same(b, on[2], &nalt, &extend(b, &r[2][..8], 9));
  // Four fixed read ports; unused replies are canonical null reads.
  let mut alt_address = block_address(b, f, block);
  alt_address[7] = b.one;
  alt_address[..7].copy_from_slice(&alt[..7]);
  let ctor = ctor_address(b, &r[0][64..80]);
  let altctor = ctor_address(b, &r[0][..8]);
  let addresses = [
    vec![
      (on[0], fn_address(b, f)),
      (on[1], block_address(b, f, block)),
      (on[2], alt_address),
    ],
    vec![
      (on[0], block_address(b, f, &r[0][8..16])),
      (foreign, fn_address(b, &r[0][64..80])),
      (construct, ctor),
      (on[2], altctor),
    ],
    vec![
      (target0, block_address(b, f, &r[0][80..88])),
      (on[2], block_address(b, f, &r[0][8..16])),
    ],
    vec![(branches, block_address(b, f, &r[0][88..96]))],
  ];
  for (i, choices) in addresses.iter().enumerate() {
    let enabled = b.any(&choices.iter().map(|(e, _)| *e).collect::<Vec<_>>());
    let disabled = b.not(enabled);
    b.require_zero(disabled, &r[i]);
    b.require_zero(b.one, &word(8 + 2 * i));
    let address = select(b, choices, 128);
    b.write(INPUTS + 3 + 4 * i, &address);
    b.write(INPUTS + 4 + 4 * i, &[]);
    b.write(INPUTS + 5 + 4 * i, &r[i]);
    b.write(INPUTS + 6 + 4 * i, &word(8 + 2 * i));
  }
  // Every active row advances the fixed enumeration; disabled rows preserve it.
  let zero8 = b.constant(8, 0);
  let nextblock = plus(b, b.one, &extend(b, block, 16), &b.constant(16, 1));
  let moreblocks = lt(b, &nextblock, &cf[16..32]);
  let nextfn = plus(b, b.one, f, &b.constant(16, 1));
  let morefn = lt(b, &nextfn, &word(0)[..16]);
  let nextfnctrl = choose(
    b,
    morefn,
    &control(b, 0, &nextfn, &zero8, &zero8),
    &control(b, 3, &nextfn, &zero8, &zero8),
  );
  let advance = choose(
    b,
    moreblocks,
    &control(b, 1, f, &nextblock[..8], &zero8),
    &nextfnctrl,
  );
  let advance_cache = mask(b, moreblocks, &cf);
  let hasalts = b.any(&r[0][48..56]);
  let enter = b.b.and(inst[5], hasalts);
  let nextalt = plus(b, b.one, alt, &b.constant(8, 1));
  let morealts = lt(b, &nextalt, &ch[48..56]);
  let fromblock = choose(b, enter, &control(b, 2, f, block, &zero8), &advance);
  let fromalt =
    choose(b, morealts, &control(b, 2, f, block, &nextalt), &advance);
  let blockcache = choose(b, enter, &cf, &advance_cache);
  let altcache = choose(b, morealts, &cf, &advance_cache);
  let blockheader = mask(b, enter, &r[0]);
  let altheader = mask(b, morealts, &ch);
  let next = [
    select(
      b,
      &[
        (phase[0], control(b, 1, f, &zero8, &zero8)),
        (phase[1], fromblock),
        (phase[2], fromalt),
        (phase[3], c.clone()),
      ],
      128,
    ),
    select(
      b,
      &[(phase[0], r[0].clone()), (phase[1], blockcache), (phase[2], altcache)],
      128,
    ),
    select(b, &[(phase[1], blockheader), (phase[2], altheader)], 128),
  ];
  for (i, v) in next.iter().enumerate() {
    let v = choose(b, e, v, &word(3 + i));
    b.write(INPUTS + i, &v);
  }
  builder.finish(INPUTS + OUTPUTS - 1)
}
