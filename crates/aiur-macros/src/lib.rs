//! Generated native executors for formal Aiur programs.
//!
//! `kernel!(pub Name, "path/to/artifact.json")` reads an execution package
//! (a bytecode `Program`, or an export with a `program` field) at compile time,
//! derives its normalized plan with `aiur`'s own checker, and expands to a
//! unit type `Name` implementing [`aiur::native::Kernel`]. The path is relative
//! to the invoking crate's manifest directory unless absolute; the form
//! `kernel!(pub Name, env = "VAR")` reads the path from an environment variable
//! at compile time. The expansion references the artifact with
//! `include_bytes!` and the variable with `env!`, so Cargo regenerates it when
//! either the file or the variable changes.
//!
//! Binding the kernel (`PreparedHints::bind_native`) checks its fingerprint,
//! so an expansion can only run the program it was generated from.
use proc_macro::{Delimiter, TokenStream, TokenTree};
use std::path::PathBuf;

mod emit;

#[proc_macro]
pub fn kernel(input: TokenStream) -> TokenStream {
  match expand(input) {
    Ok(code) => code.parse().unwrap_or_else(|e| {
      compile_error(&format!("aiur kernel expansion does not parse: {e}"))
    }),
    Err(message) => compile_error(&message),
  }
}

fn compile_error(message: &str) -> TokenStream {
  format!("::core::compile_error!({message:?});").parse().unwrap()
}

struct Input {
  public: bool,
  name: String,
  path: PathBuf,
  variable: Option<String>,
}

fn parse(input: TokenStream) -> Result<Input, String> {
  let usage = "expected `kernel!([pub] Name, \"artifact.json\")` or \
               `kernel!([pub] Name, env = \"VAR\")`";
  let tokens: Vec<TokenTree> = input
    .into_iter()
    .flat_map(|t| match t {
      // `$x` fragments from macro_rules arrive wrapped in invisible groups.
      TokenTree::Group(g) if g.delimiter() == Delimiter::None => {
        g.stream().into_iter().collect()
      },
      t => vec![t],
    })
    .collect();
  let mut i = 0;
  let public = matches!(tokens.first(), Some(TokenTree::Ident(id)) if id.to_string() == "pub");
  if public {
    i += 1;
  }
  let Some(TokenTree::Ident(name)) = tokens.get(i) else {
    return Err(usage.into());
  };
  let name = name.to_string();
  i += 1;
  if !matches!(tokens.get(i), Some(TokenTree::Punct(p)) if p.as_char() == ',') {
    return Err(usage.into());
  }
  i += 1;
  let literal = |t: Option<&TokenTree>| -> Result<String, String> {
    let Some(TokenTree::Literal(l)) = t else { return Err(usage.into()) };
    let text = l.to_string();
    let inner = text
      .strip_prefix('"')
      .and_then(|s| s.strip_suffix('"'))
      .ok_or_else(|| usage.to_string())?;
    if inner.contains('\\') {
      return Err("artifact paths may not contain escapes".into());
    }
    Ok(inner.to_owned())
  };
  let mut variable = None;
  let raw = match tokens.get(i) {
    Some(TokenTree::Ident(id)) if id.to_string() == "env" => {
      if !matches!(tokens.get(i + 1), Some(TokenTree::Punct(p)) if p.as_char() == '=')
      {
        return Err(usage.into());
      }
      let var = literal(tokens.get(i + 2))?;
      i += 3;
      let raw = std::env::var(&var).map_err(|e| {
        format!("environment variable {var} must name the artifact: {e}")
      })?;
      variable = Some(var);
      raw
    },
    t => {
      i += 1;
      literal(t)?
    },
  };
  if i != tokens.len()
    && !(i + 1 == tokens.len()
      && matches!(&tokens[i], TokenTree::Punct(p) if p.as_char() == ','))
  {
    return Err(usage.into());
  }
  let mut path = PathBuf::from(raw);
  if path.is_relative() {
    let root = std::env::var("CARGO_MANIFEST_DIR")
      .map_err(|e| format!("CARGO_MANIFEST_DIR: {e}"))?;
    path = PathBuf::from(root).join(path);
  }
  Ok(Input { public, name, path, variable })
}

#[derive(serde::Deserialize)]
struct Package {
  program: aiur::Program,
}

fn expand(input: TokenStream) -> Result<String, String> {
  let input = parse(input)?;
  let bytes = std::fs::read(&input.path)
    .map_err(|e| format!("cannot read {}: {e}", input.path.display()))?;
  let program = match aiur::decode_artifact::<Package>(&bytes) {
    Ok(package) => package.program,
    Err(_) => aiur::decode_artifact::<aiur::Program>(&bytes).map_err(|e| {
      format!("{}: not an execution package: {e}", input.path.display())
    })?,
  };
  let checked = program.check()?;
  let plan = checked.native_plan();
  let fingerprint = aiur::native::native_fingerprint(checked.program(), &plan);
  let path =
    input.path.to_str().ok_or("artifact path is not valid UTF-8")?.to_owned();
  Ok(emit::kernel(&emit::Kernel {
    program: checked.program(),
    public: input.public,
    name: &input.name,
    artifact: &path,
    variable: input.variable.as_deref(),
    fingerprint: &fingerprint,
    plan: &plan,
  }))
}
