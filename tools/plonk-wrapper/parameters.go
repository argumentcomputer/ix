package main

import (
	"bufio"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strconv"
)

type lagrangeManifest struct {
	Format, SetupID, MonomialBLAKE3 string
	Domain                          uint64
	Points                          artifact
}

func readAffinePoints(r io.Reader, count uint64) ([]nativeG1, error) {
	points := make([]nativeG1, count)
	for i := range points {
		var raw [2 * baseBytes]byte
		if _, err := io.ReadFull(r, raw[:]); err != nil {
			return nil, err
		}
		if err := points[i].X.SetBytesCanonical(raw[:baseBytes]); err != nil {
			return nil, err
		}
		if err := points[i].Y.SetBytesCanonical(raw[baseBytes:]); err != nil {
			return nil, err
		}
	}
	return points, nil
}

func writeAffinePoints(w io.Writer, points []nativeG1) error {
	b := bufio.NewWriterSize(w, 1<<20)
	for _, point := range points {
		x, y := point.X.Bytes(), point.Y.Bytes()
		if _, err := b.Write(x[:]); err != nil {
			return err
		}
		if _, err := b.Write(y[:]); err != nil {
			return err
		}
	}
	return b.Flush()
}

func lagrangeLocation(root string, domain uint64, setupID, receipt string) (lagrangeManifest, string, error) {
	want := lagrangeManifest{Format: lagrangeFormat, SetupID: setupID, MonomialBLAKE3: receipt, Domain: domain}
	identity, err := json.Marshal(want)
	if err != nil {
		return want, "", err
	}
	digest := sha256.Sum256(identity)
	dir := filepath.Join(root, strconv.FormatUint(domain, 10), hex.EncodeToString(digest[:]))
	return want, dir, nil
}

func publishLagrange(dir string, want lagrangeManifest, points []nativeG1) error {
	pointsPath, metadata := filepath.Join(dir, "points.bin"), filepath.Join(dir, "manifest.json")
	var err error
	if err := atomicFile(pointsPath, func(w io.Writer) error { return writeAffinePoints(w, points) }); err != nil {
		return err
	}
	want.Points, err = fileHash(pointsPath)
	if err != nil {
		return err
	}
	if err := writeJSON(metadata, want); err != nil {
		return err
	}
	return nil
}

func lagrangeParameters(root string, srs *nativeSRS, domain uint64, setupID, receipt string) (*nativeSRS, bool, error) {
	if domain < 2 || domain > 1<<26 || domain&(domain-1) != 0 || uint64(len(srs.Pk.G1)) < domain+3 {
		return nil, false, fmt.Errorf("invalid Lagrange domain or monomial prefix")
	}
	want, dir, err := lagrangeLocation(root, domain, setupID, receipt)
	if err != nil {
		return nil, false, err
	}
	metadata := filepath.Join(dir, "manifest.json")
	pointsPath := filepath.Join(dir, "points.bin")
	if _, err := os.Stat(metadata); err == nil {
		var stored lagrangeManifest
		if err := decodeJSON(metadata, &stored); err != nil {
			return nil, false, err
		}
		pointsInfo := stored.Points
		stored.Points = artifact{}
		if stored != want || pointsInfo.Bytes != int64(2*baseBytes*domain) {
			return nil, false, fmt.Errorf("Lagrange cache identity differs")
		}
		got, err := fileHash(pointsPath)
		if err != nil {
			return nil, false, err
		}
		if got != pointsInfo {
			return nil, false, fmt.Errorf("Lagrange cache checksum differs")
		}
		f, err := os.Open(pointsPath)
		if err != nil {
			return nil, false, err
		}
		defer f.Close()
		points, err := readAffinePoints(bufio.NewReaderSize(f, 1<<20), domain)
		if err != nil {
			return nil, false, err
		}
		return &nativeSRS{Pk: nativeKzgProvingKey{G1: points}, Vk: srs.Vk}, true, nil
	} else if !os.IsNotExist(err) {
		return nil, false, err
	}
	points, err := toLagrange(srs.Pk.G1[:domain])
	if err != nil {
		return nil, false, err
	}
	if err := publishLagrange(dir, want, points); err != nil {
		return nil, false, err
	}
	return &nativeSRS{Pk: nativeKzgProvingKey{G1: points}, Vk: srs.Vk}, false, nil
}
