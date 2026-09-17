//! Named physical setups selected by the semantics-2 quota census.
//! These constants are verifier policy, never inferred from a proof or trace.
//! The complete 31-family order is `Chip::ALL`; measurements and workload
//! limits are recorded in docs/IxbyBatchTuning.md.
use super::{BatchClass, batch::BatchShape};

pub(super) fn shape(class: BatchClass) -> Option<BatchShape> {
  let (quotas, cells, parents, nu) = match class {
    BatchClass::Arithmetic768 => (
      [
        768, 1536, 683, 43, 43, 128, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
        6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
      ],
      512,
      1023,
      14,
    ),
    BatchClass::Arithmetic3072 => (
      [
        3072, 6144, 2731, 171, 171, 512, 24, 24, 24, 24, 24, 24, 24, 24, 24,
        24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
      ],
      1536,
      3071,
      16,
    ),
    BatchClass::Arithmetic4096 => (
      [
        4096, 8192, 3641, 228, 228, 683, 32, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
      ],
      2048,
      4095,
      16,
    ),
    BatchClass::Arrays768 => (
      [
        768, 1726, 6, 191, 191, 575, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
        6, 6, 6, 6, 383, 2686, 1151, 383, 6, 6, 6,
      ],
      2048,
      4095,
      15,
    ),
    BatchClass::Builders768 => (
      [
        768, 1152, 6, 129, 128, 384, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
        6, 6, 6, 6, 512, 6, 6, 512, 256, 640, 512,
      ],
      1024,
      2047,
      14,
    ),
    BatchClass::Mixed3072 => (
      [
        3072, 4486, 557, 941, 715, 2995, 267, 24, 24, 24, 529, 24, 490, 274,
        48, 24, 24, 24, 48, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
      ],
      1536,
      6143,
      16,
    ),
    BatchClass::Cslib2048 => (
      [
        2048, 3419, 619, 632, 539, 2268, 285, 16, 39, 154, 365, 39, 633, 357,
        73, 39, 16, 64, 73, 39, 64, 16, 16, 16, 248, 1360, 585, 248, 256, 768,
        768,
      ],
      1536,
      4095,
      16,
    ),
    _ => return None,
  };
  Some(BatchShape { quotas, cells, parents: Some(parents), nu })
}
