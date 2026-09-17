//! Named physical setups selected by the semantics-2 quota census.
//! These constants are verifier policy, never inferred from a proof or trace.
//! The original 31-family order is `Chip::ALL`; fused families are appended
//! in `Chip::FUSED` order. See docs/IxbyBatchTuning.md and docs/IxbyFusion.md.
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
    BatchClass::FusedCompact => {
      (BatchClass::SharedCompactLinked.quotas(), 24, 255, 11)
    },
    BatchClass::CslibFused => (
      [
        679, 905, 64, 10, 10, 400, 179, 10, 25, 97, 229, 25, 396, 224, 80, 40,
        10, 40, 80, 25, 40, 10, 10, 10, 155, 850, 366, 155, 160, 480, 480,
      ],
      1152,
      4095,
      15,
    ),
    _ => return None,
  };
  Some(BatchShape {
    quotas,
    fused: class.fused_quotas(),
    cells,
    parents: Some(parents),
    nu,
  })
}

/// Count-only starting point from five preselected full-run captures. The
/// production fused layout additionally avoids state/memory padding cliffs.
#[cfg(test)]
pub(super) fn fused_reference_shape() -> BatchShape {
  BatchShape {
    quotas: [
      1086, 1448, 67, 16, 16, 593, 285, 16, 39, 154, 365, 39, 633, 357, 73, 39,
      16, 64, 73, 39, 64, 16, 16, 16, 248, 1360, 585, 248, 256, 768, 768,
    ],
    fused: [632, 587, 230, 37, 39, 250, 180, 115],
    cells: 1536,
    parents: Some(4095),
    nu: 16,
  }
}
