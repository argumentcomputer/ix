//go:build plonk || !groth16

package main

import (
	"encoding/binary"
	"encoding/hex"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/zeebo/blake3"
)

func TestAiurIgnitionDomainBoundary(t *testing.T) {
	const ceremonyPowers = 100800000
	if aiurMaxDomain != 1<<26 || aiurMaxDomain+3 > ceremonyPowers || 2*aiurMaxDomain+3 <= ceremonyPowers {
		t.Fatal("Aiur domain is not the largest power of two served by Ignition")
	}
	info := circuitInfo{Domain: aiurMaxDomain, Constraints: aiurMaxDomain - 2, PublicInputs: 2, Commitments: 1}
	if err := validateAiurInfo(info); err != nil {
		t.Fatal(err)
	}
	info.Domain *= 2
	info.Constraints = int(info.Domain) - info.PublicInputs
	if err := validateAiurInfo(info); err == nil {
		t.Fatal("accepted the next domain beyond the ceremony")
	}
	schema := aiurSchema{Format: aiurPlonkFormat, Circuits: []aiurChip{{Rows: aiurMaxDomain, MainWidth: 1}}}
	if err := schema.validate(); err != nil {
		t.Fatal(err)
	}
	schema.Circuits[0].Rows *= 2
	if err := schema.validate(); err == nil {
		t.Fatal("accepted an oversized row capacity")
	}
}

func TestAiurLargeDomainRequiresThreeOpeningPowersBeforeAllocation(t *testing.T) {
	for _, count := range []uint64{aiurMaxDomain, aiurMaxDomain + 2, aiurMaxDomain + 3} {
		var header [88]byte
		copy(header[:8], srsMagic)
		binary.LittleEndian.PutUint64(header[40:48], 100800000-1)
		binary.LittleEndian.PutUint64(header[80:88], count)
		path := filepath.Join(t.TempDir(), "header.bin")
		if err := os.WriteFile(path, header[:], 0600); err != nil {
			t.Fatal(err)
		}
		digest := blake3.Sum256(header[:])
		_, err := readSRS(path, hex.EncodeToString(digest[:]), aiurMaxDomain)
		if err == nil {
			t.Fatal("accepted a header without powers")
		}
		if count < aiurMaxDomain+3 && !strings.Contains(err.Error(), "required power count") {
			t.Fatalf("short prefix reached point allocation: %v", err)
		}
		if count == aiurMaxDomain+3 && !strings.Contains(err.Error(), "invalid SRS export length") {
			t.Fatalf("complete power count did not reach framing validation: %v", err)
		}
	}
}
