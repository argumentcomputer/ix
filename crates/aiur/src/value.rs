//! Entry-only structured IO. No pointer or opaque-type variant is available.
use crate::field::FieldBackend;
use serde::{Deserialize, Serialize};
use serde_json::Value as Json;
use std::fmt;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum IoType {
  Field,
  Tuple { items: Vec<IoType> },
  Array { element: Box<IoType>, length: usize },
  Struct { name: String, fields: Vec<(String, IoType)> },
  Enum { name: String, constructors: Vec<(String, Vec<IoType>)> },
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Value {
  Field { value: u64 },
  Tuple { items: Vec<Value> },
  Array { items: Vec<Value> },
  Struct { name: String, fields: Vec<(String, Value)> },
  Enum { name: String, constructor: String, args: Vec<Value> },
}
impl From<u64> for Value {
  fn from(value: u64) -> Self {
    Self::Field { value }
  }
}
fn widths(items: &[IoType]) -> Result<usize, String> {
  items.iter().try_fold(0usize, |n, t| {
    n.checked_add(t.checked_width()?).ok_or("IO width overflow".into())
  })
}
impl IoType {
  pub fn checked_width(&self) -> Result<usize, String> {
    match self {
      Self::Field => Ok(1),
      Self::Tuple { items } => widths(items),
      Self::Array { element, length } => element
        .checked_width()?
        .checked_mul(*length)
        .ok_or("IO width overflow".into()),
      Self::Struct { fields, .. } => {
        fields.iter().try_fold(0usize, |n, (_, t)| {
          n.checked_add(t.checked_width()?).ok_or("IO width overflow".into())
        })
      },
      Self::Enum { constructors, .. } => {
        let payload = constructors
          .iter()
          .map(|(_, fields)| widths(fields))
          .collect::<Result<Vec<_>, _>>()?
          .into_iter()
          .max()
          .unwrap_or(0);
        payload
          .checked_add(usize::from(constructors.len() > 1))
          .ok_or("IO width overflow".into())
      },
    }
  }
  /// Type-directed JSON: numbers for fields, arrays for tuples/arrays, objects
  /// for structs, and {"Constructor": [arguments]} for enum values.
  pub fn read_json(&self, json: &Json) -> Result<Value, String> {
    match self {
      Self::Field => Ok(Value::from(
        json.as_u64().ok_or("expected a nonnegative field integer")?,
      )),
      Self::Tuple { items } => {
        Ok(Value::Tuple { items: read_list(items, json)? })
      },
      Self::Array { element, length } => {
        let values = json.as_array().ok_or("expected an array")?;
        if values.len() != *length {
          return Err("array length mismatch".into());
        }
        Ok(Value::Array {
          items: values
            .iter()
            .map(|v| element.read_json(v))
            .collect::<Result<_, _>>()?,
        })
      },
      Self::Struct { name, fields } => {
        let values = json.as_object().ok_or("expected a struct object")?;
        if values.len() != fields.len() {
          return Err("struct field count mismatch".into());
        }
        Ok(Value::Struct {
          name: name.clone(),
          fields: fields
            .iter()
            .map(|(n, t)| {
              Ok((
                n.clone(),
                t.read_json(
                  values
                    .get(n)
                    .ok_or_else(|| format!("missing struct field {n}"))?,
                )?,
              ))
            })
            .collect::<Result<_, String>>()?,
        })
      },
      Self::Enum { name, constructors } => {
        let object =
          json.as_object().ok_or("expected a single-constructor object")?;
        if object.len() != 1 {
          return Err("expected exactly one enum constructor".into());
        }
        let (ctor, args) = object.iter().next().unwrap();
        let (_, types) = constructors
          .iter()
          .find(|(n, _)| n == ctor)
          .ok_or_else(|| format!("unknown constructor {name}::{ctor}"))?;
        Ok(Value::Enum {
          name: name.clone(),
          constructor: ctor.clone(),
          args: read_list(types, args)?,
        })
      },
    }
  }
  pub fn flatten<B: FieldBackend>(
    &self,
    value: &Value,
    field: B,
  ) -> Result<Vec<B::Element>, String> {
    let mut output = vec![];
    match (self, value) {
      (Self::Field, Value::Field { value }) if field.contains(*value) => {
        output.push(field.from_u64(*value))
      },
      (Self::Tuple { items: types }, Value::Tuple { items }) => {
        output = flatten_list(types, items, field)?
      },
      (Self::Array { element, length }, Value::Array { items })
        if items.len() == *length =>
      {
        for value in items {
          output.extend(element.flatten(value, field)?);
        }
      },
      (
        Self::Struct { name, fields: types },
        Value::Struct { name: actual, fields },
      ) if name == actual && types.len() == fields.len() => {
        for (n, t) in types {
          if fields.iter().filter(|(k, _)| k == n).count() != 1 {
            return Err(format!("missing or duplicate field {n}"));
          }
          output.extend(
            t.flatten(&fields.iter().find(|(k, _)| k == n).unwrap().1, field)?,
          );
        }
      },
      (
        Self::Enum { name, constructors },
        Value::Enum { name: actual, constructor, args },
      ) if name == actual => {
        let (index, (_, types)) = constructors
          .iter()
          .enumerate()
          .find(|(_, (n, _))| n == constructor)
          .ok_or("unknown enum constructor")?;
        if constructors.len() as u128 > u128::from(field.modulus()) {
          return Err("enum tags do not fit in field".into());
        }
        if constructors.len() > 1 {
          output.push(field.from_u64(index as u64));
        }
        output.extend(flatten_list(types, args, field)?);
        output.resize(self.checked_width()?, field.zero());
      },
      _ => {
        return Err(
                    "value does not match entry IO type, or field element is noncanonical".into(),
                );
      },
    }
    Ok(output)
  }
  pub fn unflatten<B: FieldBackend>(
    &self,
    words: &[B::Element],
    field: B,
  ) -> Result<Value, String> {
    if words.len() != self.checked_width()?
      || words.iter().any(|w| !field.valid(*w))
    {
      return Err("invalid flat entry value".into());
    }
    match self {
      Self::Field => Ok(field.to_u64(words[0]).into()),
      Self::Tuple { items } => {
        Ok(Value::Tuple { items: unflatten_list(items, words, field)? })
      },
      Self::Array { element, length } => {
        let width = element.checked_width()?;
        let items = (0..*length)
          .map(|i| element.unflatten(&words[i * width..(i + 1) * width], field))
          .collect::<Result<_, _>>()?;
        Ok(Value::Array { items })
      },
      Self::Struct { name, fields } => {
        let mut offset = 0;
        let mut values = vec![];
        for (n, t) in fields {
          let width = t.checked_width()?;
          values.push((
            n.clone(),
            t.unflatten(&words[offset..offset + width], field)?,
          ));
          offset += width;
        }
        Ok(Value::Struct { name: name.clone(), fields: values })
      },
      Self::Enum { name, constructors } => {
        let tagged = constructors.len() > 1;
        if constructors.len() as u128 > u128::from(field.modulus()) {
          return Err("enum tags do not fit in field".into());
        }
        let tag = if tagged {
          usize::try_from(field.to_u64(words[0]))
            .map_err(|_| "invalid enum tag")?
        } else {
          0
        };
        let (constructor, types) =
          constructors.get(tag).ok_or("invalid enum tag")?;
        let payload = &words[usize::from(tagged)..];
        let width = widths(types)?;
        if payload[width..].iter().any(|w| *w != field.zero()) {
          return Err("nonzero enum padding".into());
        }
        let args = unflatten_list(types, &payload[..width], field)?;
        Ok(Value::Enum {
          name: name.clone(),
          constructor: constructor.clone(),
          args,
        })
      },
    }
  }
}
fn read_list(types: &[IoType], json: &Json) -> Result<Vec<Value>, String> {
  let values = json.as_array().ok_or("expected an array of values")?;
  if types.len() != values.len() {
    return Err("value arity mismatch".into());
  }
  types.iter().zip(values).map(|(t, v)| t.read_json(v)).collect()
}
fn flatten_list<B: FieldBackend>(
  types: &[IoType],
  values: &[Value],
  field: B,
) -> Result<Vec<B::Element>, String> {
  if types.len() != values.len() {
    return Err("value arity mismatch".into());
  }
  let mut result = vec![];
  for (t, v) in types.iter().zip(values) {
    result.extend(t.flatten(v, field)?);
  }
  Ok(result)
}
fn unflatten_list<B: FieldBackend>(
  types: &[IoType],
  words: &[B::Element],
  field: B,
) -> Result<Vec<Value>, String> {
  let mut offset = 0;
  let mut result = vec![];
  for ty in types {
    let width = ty.checked_width()?;
    result.push(ty.unflatten(&words[offset..offset + width], field)?);
    offset += width;
  }
  Ok(result)
}
impl fmt::Display for Value {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fn list(f: &mut fmt::Formatter<'_>, values: &[Value]) -> fmt::Result {
      for (i, value) in values.iter().enumerate() {
        if i != 0 {
          write!(f, ", ")?;
        }
        write!(f, "{value}")?;
      }
      Ok(())
    }
    match self {
      Self::Field { value } => write!(f, "{value}"),
      Self::Tuple { items } => {
        write!(f, "(")?;
        list(f, items)?;
        if items.len() == 1 {
          write!(f, ",")?;
        }
        write!(f, ")")
      },
      Self::Array { items } => {
        write!(f, "[")?;
        list(f, items)?;
        write!(f, "]")
      },
      Self::Struct { name, fields } => {
        write!(f, "{name} {{")?;
        for (i, (n, v)) in fields.iter().enumerate() {
          if i != 0 {
            write!(f, ",")?;
          }
          write!(f, " {n}: {v}")?;
        }
        write!(f, " }}")
      },
      Self::Enum { name, constructor, args } => {
        write!(f, "{name}::{constructor}")?;
        if !args.is_empty() {
          write!(f, "(")?;
          list(f, args)?;
          write!(f, ")")?;
        }
        Ok(())
      },
    }
  }
}
