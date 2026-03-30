package bigmod

import (
	"encoding/binary"
	"math/big"
	"math/rand"
	"os"
	"testing"
)

// benchLimbSizes are the limb sizes to benchmark (exponentially increasing).
var benchLimbSizes = []int{1, 2, 4, 8, 16, 32, 64, 128}

const benchPairsPerSize = 1000
const benchInputFile = "testdata/extgcd_bench_inputs.bin"

// TestGenerateBenchInputs generates deterministic (a, m) pairs for benchmarking
// extendedGCD and writes them to testdata/extgcd_bench_inputs.bin.
//
// File format (all little-endian length headers, big-endian number bytes):
//
//	uint32: number of limb configs
//	For each config:
//	  uint32: limb count
//	  uint32: number of pairs
//	  uint32: byte length per number (limb count * 8)
//	  For each pair:
//	    [byteLen]byte: a (big-endian, zero-padded to byteLen)
//	    [byteLen]byte: m (big-endian, zero-padded to byteLen)
//
// Inputs satisfy: m > a > 0, m odd (so not both even), m has exactly
// `limb_count` limbs (top limb nonzero).
func TestGenerateBenchInputs(t *testing.T) {
	if _, err := os.Stat(benchInputFile); err == nil {
		t.Skipf("%s already exists; delete it to regenerate", benchInputFile)
	}

	rng := rand.New(rand.NewSource(42))

	f, err := os.Create(benchInputFile)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()

	writeU32 := func(v uint32) {
		if err := binary.Write(f, binary.LittleEndian, v); err != nil {
			t.Fatal(err)
		}
	}

	writeU32(uint32(len(benchLimbSizes)))

	for _, limbs := range benchLimbSizes {
		byteLen := limbs * 8
		writeU32(uint32(limbs))
		writeU32(uint32(benchPairsPerSize))
		writeU32(uint32(byteLen))

		for i := 0; i < benchPairsPerSize; i++ {
			// Generate m as a random big.Int with exactly `limbs` 64-bit limbs,
			// top limb nonzero, m odd.
			mLimbs := make([]uint64, limbs)
			for j := range mLimbs {
				mLimbs[j] = rng.Uint64()
			}
			for mLimbs[limbs-1] == 0 {
				mLimbs[limbs-1] = rng.Uint64()
			}
			mLimbs[0] |= 1 // ensure odd

			mBig := limbsToBig(mLimbs)

			// Generate a < m, a > 0.
			var aBig *big.Int
			for {
				aLimbs := make([]uint64, limbs)
				for j := range aLimbs {
					aLimbs[j] = rng.Uint64()
				}
				aBig = limbsToBig(aLimbs)
				aBig.Mod(aBig, mBig)
				if aBig.Sign() > 0 {
					break
				}
			}

			// Write a and m as fixed-length big-endian byte slices.
			aBytes := zeroPadBigEndian(aBig, byteLen)
			mBytes := zeroPadBigEndian(mBig, byteLen)
			if _, err := f.Write(aBytes); err != nil {
				t.Fatal(err)
			}
			if _, err := f.Write(mBytes); err != nil {
				t.Fatal(err)
			}
		}
	}
}

// limbsToBig converts little-endian uint64 limbs to a *big.Int.
func limbsToBig(limbs []uint64) *big.Int {
	buf := make([]byte, len(limbs)*8)
	for i, l := range limbs {
		off := (len(limbs) - 1 - i) * 8
		binary.BigEndian.PutUint64(buf[off:], l)
	}
	return new(big.Int).SetBytes(buf)
}

// zeroPadBigEndian returns v as a big-endian byte slice zero-padded to length n.
func zeroPadBigEndian(v *big.Int, n int) []byte {
	b := v.Bytes()
	if len(b) >= n {
		return b[len(b)-n:]
	}
	buf := make([]byte, n)
	copy(buf[n-len(b):], b)
	return buf
}
