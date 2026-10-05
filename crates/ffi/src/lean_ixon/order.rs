//! Test-only oracle for the certified adapter's canonical block ordering.
//! Decode the original Ixon record, use native anonymous ingress and the
//! production kernel comparator/refinement, and return member indices. The
//! Lean implementation's projection keys and ordering are never inputs.

use crate::lean::{LeanIxAddress, LeanIxonConstant};
use ix_common::address::Address;
use ix_kernel::canonical_check::{
  sort_kconsts, validate_canonical_block_single_pass,
};
use ix_kernel::env::KEnv;
use ix_kernel::ingress::ingress_anon_block;
use ix_kernel::mode::Anon;
use ixon::constant::{
  Constant, ConstantInfo, ConstructorProj, DefinitionProj, InductiveProj,
  MutConst, RecursorProj, ctor_proj_address, defn_proj_address,
  indc_proj_address, recr_proj_address,
};
use ixon::env::Env;
use lean_ffi::object::{LeanArray, LeanBorrowed, LeanOwned, LeanString};

fn canonical_classes(
  owner: &Address,
  source: &Constant,
  env: &Env,
) -> Result<String, String> {
  let ConstantInfo::Muts(members) = &source.info else {
    return Err("expected a mutual block".to_owned());
  };
  env.store_const(owner.clone(), source.clone());
  for (index, member) in members.iter().enumerate() {
    let idx = u64::try_from(index).map_err(|e| e.to_string())?;
    let block = owner.clone();
    let (key, info) = match member {
      MutConst::Defn(_) => (
        defn_proj_address(idx, owner),
        ConstantInfo::DPrj(DefinitionProj { idx, block }),
      ),
      MutConst::Recr(_) => (
        recr_proj_address(idx, owner),
        ConstantInfo::RPrj(RecursorProj { idx, block }),
      ),
      MutConst::Indc(ind) => {
        for cidx in 0..ind.ctors.len() {
          let cidx = u64::try_from(cidx).map_err(|e| e.to_string())?;
          env.store_const(
            ctor_proj_address(idx, cidx, owner),
            Constant::new(ConstantInfo::CPrj(ConstructorProj {
              idx,
              cidx,
              block: owner.clone(),
            })),
          );
        }
        (
          indc_proj_address(idx, owner),
          ConstantInfo::IPrj(InductiveProj { idx, block }),
        )
      },
    };
    env.store_const(key, Constant::new(info));
  }
  let mut kernel = KEnv::<Anon>::new();
  let ids = ingress_anon_block(&mut kernel, env, source, owner)?;
  let pairs = ids
    .iter()
    .map(|id| {
      kernel
        .consts
        .get(id)
        .map(|value| (id.clone(), value))
        .ok_or_else(|| "native ingress omitted a block member".to_owned())
    })
    .collect::<Result<Vec<_>, _>>()?;
  let resolve = |id: &_| kernel.get(id);
  let classes = sort_kconsts::<Anon>(&pairs, &resolve)
    .map_err(|error| format!("{error:?}"))?;
  let encoded = classes
    .iter()
    .map(|class| {
      let indices = class
        .iter()
        .map(|(id, _)| {
          ids.iter().position(|original| original == id).unwrap().to_string()
        })
        .collect::<Vec<_>>()
        .join(",");
      format!("[{indices}]")
    })
    .collect::<Vec<_>>()
    .join(",");
  let accepted =
    validate_canonical_block_single_pass::<Anon>(owner, &pairs, &resolve)
      .is_ok();
  Ok(format!("{{\"classes\":[{encoded}],\"accepted\":{accepted}}}"))
}

#[unsafe(no_mangle)]
pub extern "C" fn rs_kernel_canonical_classes(
  owner: LeanIxAddress<LeanBorrowed<'_>>,
  source: LeanIxonConstant<LeanBorrowed<'_>>,
  blobs: LeanArray<LeanBorrowed<'_>>,
) -> LeanString<LeanOwned> {
  let env = Env::new();
  for (key, bytes) in blobs.map(|value| {
    let pair = value.as_ctor();
    let key =
      LeanIxAddress::from_borrowed(pair.get(0).as_byte_array()).decode();
    let bytes = pair.get(1).as_byte_array().as_bytes().to_vec();
    (key, bytes)
  }) {
    env.blobs.insert(key, bytes);
  }
  let result = canonical_classes(&owner.decode(), &source.decode(), &env)
    .unwrap_or_else(|error| format!("error:{error}"));
  LeanString::new(&result)
}
