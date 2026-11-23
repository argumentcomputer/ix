use super::*;
use crate::kzg::curve::{Bls12381, Bn254};
use ark_ec::VariableBaseMSM;

fn reference<C: KzgCurve>(
  owner: &Owner<C>,
  start: usize,
  values: &[C::Fr],
) -> G1ProjectiveOf<C> {
  G1ProjectiveOf::<C>::msm(&owner.srs.g1[start..start + values.len()], values)
    .unwrap()
}

fn check_cached_msm<C: KzgCurve>() {
  let count = 4099;
  let mut bases = Srs::<C>::unsafe_dev_setup(8192, b"cuda-cache-a");
  // MSM accepts arbitrary bases, including infinity and repeated points.
  bases.g1[0] = G1AffineOf::<C>::identity();
  bases.g1[1] = -bases.g1[2];
  bases.g1[3] = bases.g1[2];
  let first = Owner::new(Arc::new(bases));
  let second =
    Owner::new(Arc::new(Srs::<C>::unsafe_dev_setup(8192, b"cuda-cache-b")));
  let values: Vec<_> = (0..count).map(|i| C::Fr::from(i as u64)).collect();
  let scale = C::Fr::from(19u64);
  let inverse = scale.inverse().unwrap();
  let structured: Vec<_> =
    (0..count).map(|i| if i % 7 == 0 { C::FR_ZERO } else { inverse }).collect();
  let device = Devices::get::<C>().acquire_at(0);
  let handles = prepare::<C>(&device, &first, 0, count);
  for column in [&values, &structured, &vec![C::FR_ZERO; count]] {
    assert_eq!(
      invoke::<C>(
        &device,
        &handles,
        Scalars::Host(column),
        msm_normalization::<C>(column)
      ),
      reference(&first, 0, column)
    );
  }
  let hits = caches::<C>()[device.index].lock().unwrap().hits;
  let subset = prepare::<C>(&device, &first, 7, 33);
  assert_eq!(subset.point_offset, 7);
  assert_eq!(caches::<C>()[device.index].lock().unwrap().hits, hits + 1);
  assert_eq!(
    invoke::<C>(&device, &subset, Scalars::Host(&values[11..44]), None),
    reference(&first, 7, &values[11..44])
  );

  let mut pointer = std::ptr::null_mut();
  check(
    unsafe {
      C::ffi_polynomial_upload(
        device.id(),
        values.as_ptr().cast(),
        count,
        &mut pointer,
      )
    },
    "cache test scalar upload",
  );
  let polynomial = LeasedPolynomial::<C> {
    device: &device,
    context: pointer,
    _curve: PhantomData,
  };
  assert_eq!(unsafe { C::ffi_polynomial_destroy(-1, pointer) }, 1);
  let resident =
    Scalars::Resident { pointer: pointer as usize, offset: 11, count: 33 };
  assert_eq!(
    invoke::<C>(&device, &subset, resident, None),
    reference(&first, 7, &values[11..44])
  );
  assert_eq!(
    invoke::<C>(&device, &subset, resident, Some((scale, inverse))),
    reference(&first, 7, &values[11..44])
  );
  let mut output = [C::FqLimbs::default(); 3];
  let code = unsafe {
    C::ffi_srs_msm(
      device.id(),
      subset.workspace as *mut c_void,
      subset.points as *const c_void,
      count + 1,
      &mut output,
      values.as_ptr().cast(),
      std::ptr::null(),
      0,
      33,
      std::ptr::null(),
    )
  };
  assert_eq!(code, 1);
  assert_eq!(
    invoke::<C>(&device, &subset, resident, None),
    reference(&first, 7, &values[11..44])
  );
  drop(polynomial);

  let other = prepare::<C>(&device, &second, 7, 33);
  assert_eq!(other.point_offset, 0);
  assert_eq!(
    invoke::<C>(&device, &other, Scalars::Host(&values[11..44]), None),
    reference(&second, 7, &values[11..44])
  );
  let uploads = {
    let mut cache = caches::<C>()[device.index].lock().unwrap();
    let index =
      cache.entries.iter().position(|entry| entry.id == first.id).unwrap();
    cache.evict::<C>(&device, index);
    cache.uploads
  };
  let reloaded = prepare::<C>(&device, &first, 7, 33);
  assert_eq!(caches::<C>()[device.index].lock().unwrap().uploads, uploads + 1);
  assert_eq!(
    invoke::<C>(&device, &reloaded, Scalars::Host(&values[11..44]), None),
    reference(&first, 7, &values[11..44])
  );
  let second_id = second.id;
  drop(second);
  let mut cache = caches::<C>()[device.index].lock().unwrap();
  cache.purge::<C>(&device);
  assert!(cache.entries.iter().all(|entry| entry.id != second_id));
  drop(first);
  cache.purge::<C>(&device);
  cache.drop_workspace::<C>(&device);
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cached_msm_preserves_offsets_owners_and_resident_scalars() {
  check_cached_msm::<Bn254>();
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn bls12_381_cached_msm_preserves_offsets_owners_and_resident_scalars() {
  check_cached_msm::<Bls12381>();
}
