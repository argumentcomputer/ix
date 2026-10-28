package main

import (
	"crypto/rand"
	"fmt"
	"io"
	"math/big"
	"os"
	"path/filepath"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/plonk"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	fcs "github.com/consensys/gnark/frontend/cs"
	"github.com/consensys/gnark/frontend/cs/scs"
	"github.com/consensys/gnark/logger"
)

func compileProfile(path, dir string) error {
	p, err := loadVerifyingKey(path)
	if err != nil {
		return err
	}
	vkHash, err := fileHash(path)
	if err != nil {
		return err
	}
	if _, err := os.Stat(filepath.Join(dir, "manifest.json")); err == nil {
		m, err := loadManifest(dir)
		if err != nil {
			return err
		}
		if m.InnerVKSHA256 != vkHash.SHA256 {
			return fmt.Errorf("artifact directory belongs to a different verifying key")
		}
		if err := m.checkFile(dir, "circuit.bin"); err != nil {
			return err
		}
		fmt.Printf("reused_circuit=true constraints=%d domain=%d commitments=%d\n", m.Constraints, m.Domain, m.Commitments)
		return nil
	} else if !os.IsNotExist(err) {
		return err
	}
	start := time.Now()
	ccs, err := frontend.Compile(curveID.ScalarField(), scs.NewBuilder, newCircuit(p))
	if err != nil {
		return err
	}
	seconds := time.Since(start).Seconds()
	identity, err := os.Executable()
	if err != nil {
		return err
	}
	executable, err := fileHash(identity)
	if err != nil {
		return err
	}
	m := &manifest{
		Format: artifactFormat, ExecutableSHA256: executable.SHA256,
		InnerVKSHA256: vkHash.SHA256, Constraints: ccs.GetNbConstraints(),
		PublicInputs: ccs.GetNbPublicVariables(),
		Commitments:  len(ccs.GetCommitments().CommitmentIndexes()),
		Domain:       ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + ccs.GetNbPublicVariables())),
		Files:        make(map[string]artifact), Seconds: map[string]float64{"compile": seconds},
	}
	if m.PublicInputs != 2 {
		return fmt.Errorf("expected two public digest limbs")
	}
	if err := atomicFile(filepath.Join(dir, "vk.json"), func(w io.Writer) error {
		f, err := os.Open(path)
		if err != nil {
			return err
		}
		defer f.Close()
		_, err = io.Copy(w, f)
		return err
	}); err != nil {
		return err
	}
	m.Files["vk.json"] = vkHash
	if err := saveBinary(dir, "circuit.bin", ccs, m); err != nil {
		return err
	}
	if err := writeJSON(filepath.Join(dir, "manifest.json"), m); err != nil {
		return err
	}
	fmt.Printf("constraints=%d domain=%d public=%d commitments=%d compile_seconds=%.3f\n", m.Constraints, m.Domain, m.PublicInputs, m.Commitments, seconds)
	return nil
}

func loadCircuit(dir string) (*verifyingKey, constraint.ConstraintSystem, *manifest, error) {
	m, err := loadManifest(dir)
	if err != nil {
		return nil, nil, nil, err
	}
	if err := m.checkFile(dir, "circuit.bin"); err != nil {
		return nil, nil, nil, err
	}
	p, err := loadVerifyingKey(filepath.Join(dir, "vk.json"))
	if err != nil {
		return nil, nil, nil, err
	}
	ccs := plonk.NewCS(curveID)
	if err := readBinary(filepath.Join(dir, "circuit.bin"), ccs); err != nil {
		return nil, nil, nil, err
	}
	if ccs.GetNbPublicVariables() != 2 || ccs.GetNbConstraints() != m.Constraints || ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints()+2)) != m.Domain {
		return nil, nil, nil, fmt.Errorf("constraint metadata differs")
	}
	return p, ccs, m, nil
}

// diagnosticCommitment is only for checking assignments without a proving key.
// PLONK proving supplies its own KZG-bound commitment challenge.
func diagnosticCommitment(modulus *big.Int, _ []*big.Int, outputs []*big.Int) error {
	if len(outputs) != 1 {
		return fmt.Errorf("unexpected diagnostic commitment outputs")
	}
	for {
		value, err := rand.Int(rand.Reader, modulus)
		if err != nil {
			return err
		}
		if value.Sign() != 0 {
			outputs[0].Set(value)
			return nil
		}
	}
}

func checkWitness(dir, path string) error {
	p, ccs, _, err := loadCircuit(dir)
	if err != nil {
		return err
	}
	assignment, err := witnessAssignment(p, path)
	if err != nil {
		return err
	}
	w, err := frontend.NewWitness(assignment, curveID.ScalarField())
	if err != nil {
		return err
	}
	start := time.Now()
	option := solver.OverrideHint(solver.GetHintID(fcs.Bsb22CommitmentComputePlaceholder), diagnosticCommitment)
	if err := ccs.IsSolved(w, option); err != nil {
		return err
	}
	fmt.Printf("diagnostic_witness_check=passed proof_created=false witness_seconds=%.3f\n", time.Since(start).Seconds())
	return nil
}

func run(args []string) error {
	if len(args) == 5 && args[0] == "import-lagrange-sp1" {
		return importLagrangeSP1(args[1], args[2], args[3], args[4])
	}
	if len(args) == 3 && args[0] == "compile" {
		return compileProfile(args[1], args[2])
	}
	if len(args) == 3 && args[0] == "check-witness" {
		return checkWitness(args[1], args[2])
	}
	if len(args) == 4 && args[0] == "prepare" {
		return prepare(args[1], args[2], args[3])
	}
	if len(args) == 4 && args[0] == "prove" {
		return prove(args[1], args[2], args[3])
	}
	if len(args) == 5 && args[0] == "verify" {
		return verify(args[1], args[2], args[3], args[4])
	}
	if len(args) == 6 && args[0] == "verify" {
		return verify(args[1], args[2], args[3], args[4], args[5])
	}
	return fmt.Errorf("usage: PLONK helper compile <verifying key.json> <artifacts> | check-witness <artifacts> <witness.json> | import-lagrange-sp1 <artifacts> <ix-srs.bin> <trusted-srs-blake3> <plonk_pk.bin> | prepare <artifacts> <ix-srs.bin> <trusted-srs-blake3> | prove <artifacts> <witness.json> <out> | verify <key.bin> <trusted-key-sha256> <proof.bin> <expected-claim-digest>")
}

func main() {
	logger.SetOutput(os.Stderr)
	if err := run(os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
