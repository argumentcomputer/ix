package main

// Receiver multiplicities do not affect program values. If all requests are
// boolean and bounded below the field characteristic, lookup inclusion allows
// replacing their receiver weights by exact nonnegative occurrence counts.
// The validator establishes the isolation and homogeneity needed for that
// replacement; schemas outside this class retain explicit integer ranges.
type aiurCountKind uint8

const (
	aiurCountIndependent aiurCountKind = iota
	aiurCountZero
	aiurCountLinear
	aiurCountUnsafe
)

type aiurCountDependence struct {
	kind       aiurCountKind
	column     int
	references bool
}

func aiurCountExpression(node aiurNode, values []aiurCountDependence, columns map[int]bool) aiurCountDependence {
	independent := aiurCountDependence{kind: aiurCountIndependent}
	unsafe := aiurCountDependence{kind: aiurCountUnsafe, references: true}
	switch node.Op {
	case "constant":
		value, err := canonical(node.Value, scalarModulus())
		if err != nil {
			return unsafe
		}
		if value.Sign() == 0 {
			return aiurCountDependence{kind: aiurCountZero}
		}
		return independent
	case "main":
		if !columns[node.Column] {
			return independent
		}
		if node.Next {
			return unsafe
		}
		return aiurCountDependence{kind: aiurCountLinear, column: node.Column, references: true}
	case "fixed", "first", "last", "transition":
		return independent
	case "neg":
		return values[node.A]
	case "add", "sub", "mul":
		a, b := values[node.A], values[node.B]
		refs := a.references || b.references
		if a.kind == aiurCountUnsafe || b.kind == aiurCountUnsafe || (a.references && b.references && a.column != b.column) {
			return unsafe
		}
		result := func(kind aiurCountKind, column int) aiurCountDependence {
			if a.references {
				column = a.column
			} else if b.references {
				column = b.column
			}
			return aiurCountDependence{kind: kind, column: column, references: refs}
		}
		if node.Op == "mul" {
			if a.references && b.references {
				return unsafe
			}
			if a.kind == aiurCountZero || b.kind == aiurCountZero {
				return result(aiurCountZero, 0)
			}
			if a.kind == aiurCountLinear {
				return result(aiurCountLinear, a.column)
			}
			if b.kind == aiurCountLinear {
				return result(aiurCountLinear, b.column)
			}
			return result(aiurCountIndependent, 0)
		}
		if a.kind == aiurCountZero {
			return result(b.kind, b.column)
		}
		if b.kind == aiurCountZero {
			return result(a.kind, a.column)
		}
		if a.kind == aiurCountIndependent && b.kind == aiurCountIndependent {
			return result(aiurCountIndependent, 0)
		}
		if a.kind == aiurCountLinear && b.kind == aiurCountLinear && a.column == b.column {
			return result(aiurCountLinear, a.column)
		}
		return result(aiurCountUnsafe, 0)
	default:
		return unsafe
	}
}

// The caller validates indices and dimensions before this structural analysis.
func (s *aiurSchema) countElisionSafe() bool {
	if !s.BooleanRequests {
		return false
	}
	var requests uint64 = 1
	for _, chip := range s.Circuits {
		columns := make(map[int]bool)
		for _, lookup := range chip.Lookups {
			if !lookup.Negative {
				if ^uint64(0)-requests < uint64(chip.Rows) {
					return false
				}
				requests += uint64(chip.Rows)
				continue
			}
			node := chip.Nodes[lookup.Count]
			if node.Op != "main" || node.Next || columns[node.Column] {
				return false
			}
			columns[node.Column] = true
		}
		values := make([]aiurCountDependence, len(chip.Nodes))
		for i, node := range chip.Nodes {
			values[i] = aiurCountExpression(node, values, columns)
		}
		for _, id := range chip.Constraints {
			if values[id].kind == aiurCountUnsafe {
				return false
			}
		}
		for _, lookup := range chip.Lookups {
			if !lookup.Negative && values[lookup.Count].references {
				return false
			}
			for _, id := range lookup.Args {
				if values[id].references {
					return false
				}
			}
		}
	}
	// The concrete scalar field is BN254 Fr, so a u64 request budget is strict.
	return requests > 0
}
