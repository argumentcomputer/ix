// Command ignition verifies the final two Aztec Ignition contributions and
// writes a gnark BN254 SRS for release preparation.
package main

import (
	"bufio"
	"flag"
	"fmt"
	"log"
	"os"
	"path/filepath"

	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
	"github.com/consensys/gnark-ignition-verifier/ignition"
)

// The Ix mirror of the MAIN IGNITION manifest and its final two
// contributions, byte-identical to Aztec's originals.
const (
	mirrorURL      = "https://argument-kzg-params-063002298335-us-east-1-an.s3.us-east-1.amazonaws.com/bn254/ignition/"
	mirrorCeremony = "main-197"
)

func main() {
	baseURL := flag.String("base-url", mirrorURL, "ceremony host; https://aztec-ignition.s3.amazonaws.com/ with -ceremony \"MAIN IGNITION\" reads Aztec's originals")
	ceremony := flag.String("ceremony", mirrorCeremony, "ceremony directory under the base URL")
	cache := flag.String("cache", "data", "directory for downloaded ceremony transcripts")
	output := flag.String("out", "srs.bin", "new gnark SRS file")
	powers := flag.Int("powers", 1<<26, "number of G1 powers to retain")
	flag.Parse()
	if err := run(*baseURL, *ceremony, *cache, *output, *powers); err != nil {
		log.Fatal(err)
	}
}

func run(baseURL, ceremony, cache, output string, powers int) error {
	if powers < 2 || powers > 1<<26 || powers&(powers-1) != 0 {
		return fmt.Errorf("powers must be a power of two in [2, 2^26]")
	}
	if _, err := os.Stat(output); err == nil {
		return fmt.Errorf("output already exists: %s", output)
	} else if !os.IsNotExist(err) {
		return err
	}
	config := ignition.Config{BaseURL: baseURL, Ceremony: ceremony, CacheDir: cache}
	if err := os.MkdirAll(cache, 0755); err != nil {
		return err
	}
	manifest, err := ignition.NewManifest(config)
	if err != nil {
		return err
	}
	// These are manifest indices; the corresponding ceremony positions are 196 and 197.
	if len(manifest.Participants) != 176 || manifest.Participants[174].Position != 196 || manifest.Participants[175].Position != 197 || powers > manifest.NumG1Points {
		return fmt.Errorf("unexpected MAIN IGNITION manifest")
	}
	previous := ignition.NewContribution(manifest.NumG1Points)
	final := ignition.NewContribution(manifest.NumG1Points)
	if err := previous.Get(manifest.Participants[174], config); err != nil {
		return err
	}
	if err := final.Get(manifest.Participants[175], config); err != nil {
		return err
	}
	if !final.Follows(&previous) {
		return fmt.Errorf("final contribution does not follow its predecessor")
	}
	_, _, _, g2 := bn254.Generators()
	srs := &kzg.SRS{Pk: kzg.ProvingKey{G1: final.G1[:powers]}, Vk: kzg.VerifyingKey{G1: final.G1[0], G2: [2]bn254.G2Affine{g2, final.G2[0]}}}
	return writeSRS(output, srs)
}

func writeSRS(output string, srs *kzg.SRS) error {
	for i := range srs.Vk.G2 {
		srs.Vk.Lines[i] = bn254.PrecomputeLines(srs.Vk.G2[i])
	}
	polynomial := []fr.Element{fr.NewElement(3), fr.NewElement(5)}
	commitment, err := kzg.Commit(polynomial, srs.Pk)
	if err != nil {
		return err
	}
	point := fr.NewElement(7)
	proof, err := kzg.Open(polynomial, point, srs.Pk)
	if err != nil {
		return err
	}
	if err := kzg.Verify(&commitment, &proof, point, srs.Vk); err != nil {
		return err
	}
	file, err := os.CreateTemp(filepath.Dir(output), ".ignition-*.bin")
	if err != nil {
		return err
	}
	defer os.Remove(file.Name())
	defer file.Close()
	writer := bufio.NewWriterSize(file, 1<<20)
	if _, err := srs.WriteRawTo(writer); err != nil {
		return err
	}
	if err := writer.Flush(); err != nil {
		return err
	}
	if err := file.Close(); err != nil {
		return err
	}
	return os.Link(file.Name(), output)
}
