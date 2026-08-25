//! `.ixc` catalog + anonymous merge FFI: thin JSON-carrying wrappers
//! over `ixon::catalog` for the `ix catalog` / `ix merge` CLI verbs.
//!
//! The JSON here is an FFI carrier between the Lean CLI and the Rust
//! core, not a user-facing artifact surface: argv parsing and
//! presentation live in Lean (`Ix/Cli/CatalogCmd.lean`), the artifact
//! algebra lives in `ixon::catalog`, and these functions just marshal.
//! No Lean frontend is involved anywhere behind these entry points.

use std::path::PathBuf;

use ixon::catalog::{self as cat, Catalog, CatalogStorage, MemberSpec};
use lean_ffi::object::{LeanBorrowed, LeanIOResult, LeanOwned, LeanString};

fn member_json(m: &ixon::catalog::CatalogMember) -> serde_json::Value {
  serde_json::json!({
    "envRoot": m.env_root.hex(),
    "constCount": m.const_count,
    "label": m.label,
    "toolchain": m.toolchain,
    "sourcePin": m.source_pin,
    "deps": m.deps,
    "preimage": m.preimage.as_ref().map(|a| a.hex()),
  })
}

fn catalog_json(c: &Catalog) -> serde_json::Value {
  let storage = match &c.storage {
    CatalogStorage::Fat(pieces) => serde_json::json!({
      "profile": "fat",
      "pieces": pieces.iter().map(|p| serde_json::json!({
        "fileHash": p.file_hash.hex(),
        "fileBytes": p.file_bytes,
      })).collect::<Vec<_>>(),
    }),
    CatalogStorage::Chunked(chunks) => serde_json::json!({
      "profile": "chunked",
      "chunks": chunks.iter().map(|ch| serde_json::json!({
        "chunkRoot": ch.chunk_root.hex(),
        "fileHash": ch.file_hash.hex(),
        "fileBytes": ch.file_bytes,
        "owner": ch.owner,
      })).collect::<Vec<_>>(),
    }),
  };
  serde_json::json!({
    "membersRoot": c.members_root.hex(),
    "contentRoot": c.content_root.hex(),
    "members": c.members.iter().map(member_json).collect::<Vec<_>>(),
    "storage": storage,
  })
}

/// Assemble a fat-profile `.ixc` DIRECTORY from piece files: pieces
/// are ingested (hard link or copy; already-inside paths untouched)
/// as `<label>.ixe` and the manifest is written at
/// `<out_dir>/manifest` (`.tmp` + atomic rename) — the result is one
/// self-contained tree.
///
/// `members_json`: `[{"path": …, "label": …, "toolchain": …,
/// "sourcePin": …, "deps": [u32…]}, …]`, topo order (deps first).
/// The JSON here (and in the return value) is an in-memory FFI
/// carrier between the Lean CLI and this core — never a disk
/// artifact.
///
/// Lean signature:
/// ```lean
/// @[extern "rs_catalog_assemble"]
/// opaque rsCatalogAssembleFFI : @& String → @& String → IO String
/// ```
#[unsafe(no_mangle)]
pub extern "C" fn rs_catalog_assemble(
  out_path: LeanString<LeanBorrowed<'_>>,
  members_json: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let out_path = out_path.as_str().to_string();
  let parsed: serde_json::Value =
    match serde_json::from_str(members_json.as_str()) {
      Ok(v) => v,
      Err(e) => {
        return LeanIOResult::error_string(&format!(
          "rs_catalog_assemble: bad members JSON: {e}"
        ));
      },
    };
  let Some(rows) = parsed.as_array() else {
    return LeanIOResult::error_string(
      "rs_catalog_assemble: members JSON is not an array",
    );
  };
  let mut specs = Vec::with_capacity(rows.len());
  for row in rows {
    let field =
      |k: &str| row.get(k).and_then(|v| v.as_str()).map(str::to_string);
    let Some(path) = field("path") else {
      return LeanIOResult::error_string(
        "rs_catalog_assemble: member row missing \"path\"",
      );
    };
    let Some(label) = field("label") else {
      return LeanIOResult::error_string(
        "rs_catalog_assemble: member row missing \"label\"",
      );
    };
    let deps: Vec<u32> = row
      .get("deps")
      .and_then(|v| v.as_array())
      .map(|xs| {
        xs.iter()
          .filter_map(|x| x.as_u64())
          .filter_map(|x| u32::try_from(x).ok())
          .collect()
      })
      .unwrap_or_default();
    specs.push(MemberSpec {
      path: PathBuf::from(path),
      label,
      toolchain: field("toolchain").unwrap_or_default(),
      source_pin: field("sourcePin").unwrap_or_default(),
      deps,
    });
  }
  let dir = PathBuf::from(&out_path);
  let catalog = match cat::assemble_into(&dir, &specs) {
    Ok(c) => c,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_catalog_assemble: {e}"));
    },
  };
  let manifest_bytes = std::fs::metadata(dir.join(cat::MANIFEST_FILE))
    .map(|m| m.len())
    .unwrap_or(0);
  let mut summary = catalog_json(&catalog);
  summary["bytes"] = serde_json::json!(manifest_bytes);
  summary["out"] = serde_json::json!(out_path);
  LeanIOResult::ok(LeanString::new(&summary.to_string()))
}

/// Verify a self-contained `.ixc` directory (see
/// `ixon::catalog::verify` — pieces resolve inside the directory).
/// Returns the verification summary JSON (in-memory FFI carrier);
/// any violated invariant is an `IO` error.
///
/// Lean signature:
/// ```lean
/// @[extern "rs_catalog_verify"]
/// opaque rsCatalogVerifyFFI : @& String → Bool → IO String
/// ```
#[unsafe(no_mangle)]
pub extern "C" fn rs_catalog_verify(
  ixc_dir: LeanString<LeanBorrowed<'_>>,
  deep: u8,
) -> LeanIOResult<LeanOwned> {
  let dir = PathBuf::from(ixc_dir.as_str());
  let catalog = match cat::load_dir(&dir) {
    Ok(c) => c,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_catalog_verify: {e}"));
    },
  };
  let outcome = match cat::verify(&catalog, &dir, deep != 0) {
    Ok(o) => o,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_catalog_verify: {e}"));
    },
  };
  let summary = serde_json::json!({
    "membersRoot": catalog.members_root.hex(),
    "contentRoot": catalog.content_root.hex(),
    "members": outcome.members,
    "unionConsts": outcome.union_consts,
    "deep": outcome.deep,
    "profile": if catalog.is_chunked() { "chunked" } else { "fat" },
  });
  LeanIOResult::ok(LeanString::new(&summary.to_string()))
}

/// Parse a `.ixc` directory's manifest and return the dump as JSON
/// (in-memory FFI carrier — presentation is the Lean CLI's job). No
/// piece files are touched (`members_root` is still recomputed on
/// load).
///
/// Lean signature:
/// ```lean
/// @[extern "rs_catalog_info"]
/// opaque rsCatalogInfoFFI : @& String → IO String
/// ```
#[unsafe(no_mangle)]
pub extern "C" fn rs_catalog_info(
  ixc_dir: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let dir = PathBuf::from(ixc_dir.as_str());
  let catalog = match cat::load_dir(&dir) {
    Ok(c) => c,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_catalog_info: {e}"));
    },
  };
  let manifest_bytes = std::fs::metadata(dir.join(cat::MANIFEST_FILE))
    .map(|m| m.len())
    .unwrap_or(0);
  let mut summary = catalog_json(&catalog);
  summary["bytes"] = serde_json::json!(manifest_bytes);
  LeanIOResult::ok(LeanString::new(&summary.to_string()))
}

/// Per-section entry counts of a `.ixe`, via the lazy index (bodies
/// never parsed): `{consts, named, names, blobs, hints, comms,
/// assumptions, main}` as JSON. Test/introspection surface — the
/// strict-anon gate pins §5 = 0 and §3 survival with it.
///
/// Lean signature:
/// ```lean
/// @[extern "rs_env_section_counts"]
/// opaque rsEnvSectionCountsFFI : @& String → IO String
/// ```
#[unsafe(no_mangle)]
pub extern "C" fn rs_env_section_counts(
  ixe_path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let path = ixe_path.as_str().to_string();
  let bytes = match std::fs::read(&path) {
    Ok(b) => b,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_env_section_counts: read {path}: {e}"
      ));
    },
  };
  let index = match ixon::env::Env::parse_lazy_index(&bytes) {
    Ok(i) => i,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_env_section_counts: {path}: {e}"
      ));
    },
  };
  let summary = serde_json::json!({
    "consts": index.consts.len(),
    "named": index.named.len(),
    "blobs": index.blobs.len(),
    "hints": index.hints.len(),
    "comms": index.comms.len(),
    "assumptions": index.assumptions.len(),
    "main": index.main.as_ref().map(|a| a.hex()),
  });
  LeanIOResult::ok(LeanString::new(&summary.to_string()))
}

/// Anonymous k-way merge of `.ixe` pieces into one ordinary v1 env
/// (see `ixon::catalog::merge_anon`). `pieces_json` is a JSON array of
/// file paths. Returns the merge stats JSON.
///
/// Lean signature:
/// ```lean
/// @[extern "rs_merge_anon"]
/// opaque rsMergeAnonFFI : @& String → @& String → IO String
/// ```
#[unsafe(no_mangle)]
pub extern "C" fn rs_merge_anon(
  out_path: LeanString<LeanBorrowed<'_>>,
  pieces_json: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let out_path = out_path.as_str().to_string();
  let parsed: serde_json::Value =
    match serde_json::from_str(pieces_json.as_str()) {
      Ok(v) => v,
      Err(e) => {
        return LeanIOResult::error_string(&format!(
          "rs_merge_anon: bad pieces JSON: {e}"
        ));
      },
    };
  let Some(rows) = parsed.as_array() else {
    return LeanIOResult::error_string(
      "rs_merge_anon: pieces JSON is not an array",
    );
  };
  let mut paths = Vec::with_capacity(rows.len());
  for row in rows {
    match row.as_str() {
      Some(p) => paths.push(PathBuf::from(p)),
      None => {
        return LeanIOResult::error_string(
          "rs_merge_anon: pieces JSON entries must be strings",
        );
      },
    }
  }
  let stats = match cat::merge_anon(&paths, &PathBuf::from(&out_path)) {
    Ok(s) => s,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_merge_anon: {e}"));
    },
  };
  let summary = serde_json::json!({
    "root": stats.root.hex(),
    "consts": stats.consts,
    "blobs": stats.blobs,
    "bytes": stats.bytes_written,
    "out": out_path,
  });
  LeanIOResult::ok(LeanString::new(&summary.to_string()))
}
