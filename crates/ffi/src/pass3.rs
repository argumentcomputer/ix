//! Test-only FFI to the Rust Pass 3 core (`ix_compile::compile::pass3`),
//! which the compiler does not call yet: the images of a canonical block's
//! Lean recursors, for the `pass3-rust-parity` suite
//! (`Tests/Ix/Compile/Pass3RustParity.lean`) to compare with
//! `Ix.Compile.Image.imageOf` on the same input.

use ix_common::env::{ConstantInfo, Name};
use ix_compile::compile::pass3::build::image_of;
use ix_compile::compile::pass3::spec::{
  BlockCanon, ComponentCanon, image_spec_of_block,
};
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanCtor, LeanExcept, LeanOwned,
};
use rustc_hash::FxHashMap;

use crate::builder::LeanBuildCache;
use crate::lean::{LeanIxConstantInfo, LeanIxExpr, LeanIxName};

/// The canonical form of a block from its components' classes (each class
/// representative first). The image construction reads the classes only;
/// `members` lists them in class order and `nested` stays empty.
fn block_of(comps: &[Vec<Vec<Name>>]) -> BlockCanon {
  let components: Vec<ComponentCanon> = comps
    .iter()
    .map(|classes| ComponentCanon {
      members: classes.iter().flatten().cloned().collect(),
      classes: classes.clone(),
      nested: None,
    })
    .collect();
  let all = components.iter().flat_map(|c| c.members.clone()).collect();
  BlockCanon { all, components }
}

/// FFI: the Rust images of a block's Lean recursors.
///
/// Lean signature:
/// `@[extern "rs_pass3_images"]
///  opaque rsPass3Images : @& Array Ix.ConstantInfo →
///    @& Array (Array (Array Ix.Name)) → @& Array Ix.Name →
///    Except String (Array (Except String RsImage))`
///
/// `consts` is the generator's whole lookup (a name absent from it is absent
/// to `image_of`), the second argument the block's components as classes,
/// the third the Lean recursors. The outer error is `image_spec_of_block`'s;
/// each recursor's `image_of` error is its own entry.
/// `RsImage` is `{ levelParams : Array Ix.Name, type value : Ix.Expr,
/// arity : Nat }`.
#[unsafe(no_mangle)]
pub extern "C" fn rs_pass3_images(
  consts: LeanArray<LeanBorrowed<'_>>,
  comps: LeanArray<LeanBorrowed<'_>>,
  recs: LeanArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let mut env: FxHashMap<Name, ConstantInfo> = FxHashMap::default();
  for c in consts.iter() {
    let info = LeanIxConstantInfo(c).decode();
    env.insert(info.get_name().clone(), info);
  }
  let comps: Vec<Vec<Vec<Name>>> =
    comps.map(|c| c.as_array().map(|k| LeanIxName::decode_array(k.as_array())));
  let recs = LeanIxName::decode_array(recs);
  let const_of = |n: &Name| env.get(n).cloned();
  let spec = match image_spec_of_block(&const_of, &block_of(&comps)) {
    Ok(s) => s,
    Err(e) => return LeanExcept::error_string(&e),
  };
  let mut cache = LeanBuildCache::new();
  let out = LeanArray::alloc(recs.len());
  for (i, r) in recs.iter().enumerate() {
    let entry = match image_of(&const_of, &spec, r) {
      Ok(img) => {
        let ctor = LeanCtor::alloc(0, 4, 0);
        ctor.set(0, LeanIxName::build_array(&mut cache, &img.level_params));
        ctor.set(1, LeanIxExpr::build(&mut cache, &img.typ));
        ctor.set(2, LeanIxExpr::build(&mut cache, &img.value));
        ctor.set(3, LeanOwned::from_nat_u64(img.arity as u64));
        LeanExcept::ok(ctor)
      },
      Err(e) => LeanExcept::error_string(&e),
    };
    out.set(i, entry);
  }
  LeanExcept::ok(out)
}
