use super::*;
use ark_ec::VariableBaseMSM;

fn reference(owner: &Owner, start: usize, values: &[Fr]) -> G1Projective {
  G1Projective::msm(&owner.srs.g1[start..start + values.len()], values).unwrap()
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cached_msm_preserves_offsets_owners_and_resident_scalars() {
  let count = 4099;
  let mut bases = Srs::unsafe_dev_setup(8192, b"cuda-cache-a");
  // MSM accepts arbitrary bases, including infinity and repeated points.
  bases.g1[0] = G1Affine::identity();
  bases.g1[1] = -bases.g1[2];
  bases.g1[3] = bases.g1[2];
  let first = Owner::new(Arc::new(bases));
  let second =
    Owner::new(Arc::new(Srs::unsafe_dev_setup(8192, b"cuda-cache-b")));
  let values: Vec<_> = (0..count).map(|i| Fr::from(i as u64)).collect();
  let scale = Fr::from(19);
  let inverse = scale.inverse().unwrap();
  let structured: Vec<_> =
    (0..count).map(|i| if i % 7 == 0 { Fr::ZERO } else { inverse }).collect();
  let device = Devices::get().acquire_at(0);
  let handles = prepare(&device, &first, 0, count);
  for column in [&values, &structured, &vec![Fr::ZERO; count]] {
    assert_eq!(
      invoke(
        &device,
        &handles,
        Scalars::Host(column),
        msm_normalization(column)
      ),
      reference(&first, 0, column)
    );
  }
  let hits = caches()[device.index].lock().unwrap().hits;
  let subset = prepare(&device, &first, 7, 33);
  assert_eq!(subset.point_offset, 7);
  assert_eq!(caches()[device.index].lock().unwrap().hits, hits + 1);
  assert_eq!(
    invoke(&device, &subset, Scalars::Host(&values[11..44]), None),
    reference(&first, 7, &values[11..44])
  );

  let mut pointer = std::ptr::null_mut();
  check(
    unsafe {
      ix_kzg_polynomial_upload(
        device.id(),
        values.as_ptr().cast(),
        count,
        &mut pointer,
      )
    },
    "cache test scalar upload",
  );
  let polynomial = LeasedPolynomial { device: &device, context: pointer };
  assert_eq!(unsafe { ix_kzg_polynomial_destroy(-1, pointer) }, 1);
  let resident =
    Scalars::Resident { pointer: pointer as usize, offset: 11, count: 33 };
  assert_eq!(
    invoke(&device, &subset, resident, None),
    reference(&first, 7, &values[11..44])
  );
  assert_eq!(
    invoke(&device, &subset, resident, Some((scale, inverse))),
    reference(&first, 7, &values[11..44])
  );
  let mut output = [[0; FQ_LIMBS]; 3];
  let code = unsafe {
    ix_kzg_srs_msm(
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
    invoke(&device, &subset, resident, None),
    reference(&first, 7, &values[11..44])
  );
  drop(polynomial);

  let other = prepare(&device, &second, 7, 33);
  assert_eq!(other.point_offset, 0);
  assert_eq!(
    invoke(&device, &other, Scalars::Host(&values[11..44]), None),
    reference(&second, 7, &values[11..44])
  );
  let uploads = {
    let mut cache = caches()[device.index].lock().unwrap();
    let index =
      cache.entries.iter().position(|entry| entry.id == first.id).unwrap();
    cache.evict(&device, index);
    cache.uploads
  };
  let reloaded = prepare(&device, &first, 7, 33);
  assert_eq!(caches()[device.index].lock().unwrap().uploads, uploads + 1);
  assert_eq!(
    invoke(&device, &reloaded, Scalars::Host(&values[11..44]), None),
    reference(&first, 7, &values[11..44])
  );
  let second_id = second.id;
  drop(second);
  let mut cache = caches()[device.index].lock().unwrap();
  cache.purge(&device);
  assert!(cache.entries.iter().all(|entry| entry.id != second_id));
  drop(first);
  cache.purge(&device);
  cache.drop_workspace(&device);
}
