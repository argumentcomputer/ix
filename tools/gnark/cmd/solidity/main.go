// Command solidity writes gnark's Solidity verifier for a serialized BN254
// PLONK or Groth16 verifying key, such as a bundled release key. The export
// options match the verifiers that key preparation writes beside each key, so
// both sources are byte-identical for the same key.
package main

import (
	"bytes"
	"crypto/sha256"
	"flag"
	"fmt"
	"io"
	"log"
	"os"
	"path/filepath"

	g16 "github.com/consensys/gnark/backend/groth16/bn254"
	plonkbn254 "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/backend/solidity"
)

func main() {
	system := flag.String("system", "plonk", "proof system of the key: plonk or groth16")
	key := flag.String("key", "", "serialized gnark verifying key")
	output := flag.String("out", "", "Solidity file to write")
	flag.Parse()
	if *key == "" || *output == "" {
		flag.Usage()
		os.Exit(2)
	}
	if err := run(*system, *key, *output); err != nil {
		log.Fatal(err)
	}
}

func run(system, keyPath, output string) error {
	data, err := os.ReadFile(keyPath)
	if err != nil {
		return err
	}
	var source bytes.Buffer
	switch system {
	case "plonk":
		vk := new(plonkbn254.VerifyingKey)
		if err := readExact(vk, data); err != nil {
			return err
		}
		if vk.NbPublicVariables != 2 {
			return fmt.Errorf("PLONK key has %d public inputs; Ix keys have two digest limbs", vk.NbPublicVariables)
		}
		err = vk.ExportSolidity(&source)
	case "groth16":
		vk := new(g16.VerifyingKey)
		if err := readExact(vk, data); err != nil {
			return err
		}
		if commitments := len(vk.PublicAndCommitmentCommitted); commitments > 1 || len(vk.G1.K) != 3+commitments {
			return fmt.Errorf("Groth16 key has an unsupported public-input or commitment schema")
		}
		// Ix proves Groth16 commitments with SHA-256 hash-to-field; the
		// exported verifier must hash them the same way.
		err = vk.ExportSolidity(&source, solidity.WithHashToFieldFunction(sha256.New()), solidity.WithPragmaVersion("^0.8.28"))
	default:
		return fmt.Errorf("unknown proof system %q", system)
	}
	if err != nil {
		return err
	}
	return writeAtomic(output, source.Bytes())
}

func readExact(key io.ReaderFrom, data []byte) error {
	n, err := key.ReadFrom(bytes.NewReader(data))
	if err != nil {
		return err
	}
	if n != int64(len(data)) {
		return fmt.Errorf("trailing verifying key data")
	}
	return nil
}

func writeAtomic(output string, data []byte) error {
	file, err := os.CreateTemp(filepath.Dir(output), ".solidity-*.sol")
	if err != nil {
		return err
	}
	defer os.Remove(file.Name())
	if err := file.Chmod(0o644); err != nil {
		file.Close()
		return err
	}
	if _, err := file.Write(data); err != nil {
		file.Close()
		return err
	}
	if err := file.Close(); err != nil {
		return err
	}
	return os.Rename(file.Name(), output)
}
