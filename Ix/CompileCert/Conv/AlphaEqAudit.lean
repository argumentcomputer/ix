import Ix.CompileCert.Audit
import Ix.CompileCert.Conv.AlphaEq

/-! Explicit extra roots for the alpha-equality repair. The existing frozen
audit lists are unchanged. This module must be checked for the new source. -/

run_cmd (Ix.CompileCert.Audit.checkAuditRoots #[
  ``Ix.Compile.Image.RawExact.nameEq_eq_true,
  ``Ix.Compile.Image.RawExact.levelEq_eq_true,
  ``Ix.Compile.Image.RawExact.levelsEq_eq_true,
  ``Ix.CompileCert.Conv.alphaEq_er,
  ``Ix.CompileCert.Conv.alphaEq_name_collision_refused,
  ``Ix.CompileCert.Conv.alphaEq_level_collision_refused,
  ``Ix.CompileCert.Conv.alphaEq_fvar_neighbour,
  ``Ix.CompileCert.Conv.alphaEq_bvar_collision_refused,
  ``Ix.CompileCert.Conv.alphaEq_one_sided_mdata_refused,
  ``Ix.CompileCert.Img.fresh_injective,
  ``Ix.CompileCert.Img.fresh_eq_iff,
  ``Ix.CompileCert.Img.exactInjOn_shift
] Ix.CompileCert.Audit.allowedAxioms)
