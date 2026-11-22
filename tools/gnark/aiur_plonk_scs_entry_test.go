//go:build plonk || !groth16

package main

import (
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

// TestAiurScsEntryRoot runs the Lean exporter and checker on the
// testdata/aiur-entry terminal (plonk_entry_fixture): the exported entry
// EntryRoot::run asserts a == b and returns helper(a, b), and helper, which
// is not an entry, accepts any (a, b). The root table must call the schema's
// callable whatever the circuit order, so both orders give a system that
// accepts (1, 1) and rejects (1, 2). A callable that is not an exported
// entry, a missing callable and a wrong argument/output split are refused by
// both tools.
//
//	IX_PLONK_EXPORT: the plonk_export binary
//	IX_PLONK_CHECK_STAGE: the plonk_check_stage binary
func TestAiurScsEntryRoot(t *testing.T) {
	exporter := aiurScsEnv(t, "IX_PLONK_EXPORT")
	checker := aiurScsEnv(t, "IX_PLONK_CHECK_STAGE")
	dir := filepath.Join("testdata", "aiur-entry")
	ixa := filepath.Join(dir, "entry.ixa")
	data, err := os.ReadFile(filepath.Join(dir, "schema.json"))
	if err != nil {
		t.Fatal(err)
	}
	var base map[string]any
	if err := json.Unmarshal(data, &base); err != nil {
		t.Fatal(err)
	}
	circuits := base["circuits"].([]any)
	if len(circuits) != 2 || circuits[0].(map[string]any)["name"] != "EntryRoot::run" {
		t.Fatalf("unexpected fixture circuits %v", circuits)
	}
	variant := func(edit func(map[string]any)) string {
		s := map[string]any{}
		for k, v := range base {
			s[k] = v
		}
		edit(s)
		out, err := json.Marshal(s)
		if err != nil {
			t.Fatal(err)
		}
		f, err := os.CreateTemp(t.TempDir(), "schema-*.json")
		if err != nil {
			t.Fatal(err)
		}
		if _, err := f.Write(out); err != nil {
			t.Fatal(err)
		}
		f.Close()
		return f.Name()
	}
	helperFirst := func(s map[string]any) { s["circuits"] = []any{circuits[1], circuits[0]} }
	run := func(name string, args ...string) error {
		out, err := exec.Command(name, args...).CombinedOutput()
		t.Logf("%s %v:\n%s", filepath.Base(name), args[1:], out)
		return err
	}

	for _, order := range []struct {
		name string
		edit func(map[string]any)
	}{{"run-first", func(map[string]any) {}}, {"helper-first", helperFirst}} {
		schema := variant(order.edit)
		if err := run(checker, ixa, schema); err != nil {
			t.Fatalf("%s: plonk_check_stage rejects the schema: %v", order.name, err)
		}
		out := filepath.Join(t.TempDir(), "entry.ixscs")
		if err := run(exporter, ixa, schema, out); err != nil {
			t.Fatalf("%s: plonk_export fails: %v", order.name, err)
		}
		file, err := os.ReadFile(out)
		if err != nil {
			t.Fatal(err)
		}
		s, err := parseAiurScs(file)
		if err != nil {
			t.Fatal(err)
		}
		for _, runRow := range []bool{true, false} {
			if aiurScsEntrySolve(s, 1, 2, runRow) == nil {
				t.Fatalf("%s: statement (1, 2) solves (run row filled: %v)", order.name, runRow)
			}
		}
		if err := aiurScsEntrySolve(s, 1, 1, true); err != nil {
			t.Fatalf("%s: the execution of run(1, 1) does not solve: %v", order.name, err)
		}
	}

	for _, bad := range []struct {
		name string
		edit func(map[string]any)
	}{
		{"helper callable", func(s map[string]any) { s["callable"] = 1 }},
		{"helper callable, helper first", func(s map[string]any) { helperFirst(s); s["callable"] = 1 }},
		{"callable out of range", func(s map[string]any) { s["callable"] = 7 }},
		{"no callable", func(s map[string]any) { delete(s, "callable") }},
		{"argument/output split", func(s map[string]any) { s["public_inputs"], s["private_outputs"] = 3, 17 }},
	} {
		schema := variant(bad.edit)
		if run(checker, ixa, schema) == nil {
			t.Errorf("%s: plonk_check_stage accepts the schema", bad.name)
		}
		out := filepath.Join(t.TempDir(), "entry.ixscs")
		if run(exporter, ixa, schema, out) == nil {
			t.Errorf("%s: plonk_export accepts the schema", bad.name)
		}
		if _, err := os.Stat(out); err == nil {
			t.Errorf("%s: plonk_export wrote %s", bad.name, out)
		}
	}
}

// aiurScsEntrySolve solves s for the statement (a, b) with helper's row of
// helper(a, b) and, with runRow, run's row of run(a, b) (all zero
// otherwise): the 18 output words of both functions are 1 at positions 8 and
// 17, and the cells after a row's arguments and outputs are 1 on an active
// row.
func aiurScsEntrySolve(s *aiurScs, a, b int, runRow bool) error {
	vals := make([]frontend.Variable, s.Cells)
	for i := range vals {
		vals[i] = 0
	}
	vals[0], vals[1], vals[2+8], vals[2+17] = a, b, 1, 1
	for _, table := range s.Tables {
		base := int(table.CellBase)
		switch table.Name {
		case "EntryRoot::helper":
			vals[base], vals[base+1], vals[base+2], vals[base+3] = a, b, 1, 1
		case "EntryRoot::run":
			if !runRow {
				continue
			}
			vals[base], vals[base+1] = a, b
			vals[base+2+8], vals[base+2+17], vals[base+20], vals[base+21] = 1, 1, 1, 1
		}
	}
	pairing := aiurScsTestPairing()
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, newAiurScsCircuit(s, pairing))
	if err != nil {
		return err
	}
	c := newAiurScsCircuit(s, pairing)
	copy(c.Public, vals[:s.Publics])
	copy(c.Cells, vals[s.Publics:])
	w, err := frontend.NewWitness(c, ecc.BN254.ScalarField())
	if err != nil {
		return err
	}
	_, err = ccs.Solve(w)
	return err
}
