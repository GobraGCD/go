package bigmod

import (
	"encoding/binary"
	"fmt"
	"os"
	"testing"
)

// benchInput holds a pre-constructed (a, m) pair for benchmarking.
type benchInput struct {
	a, m *Nat
}

// loadBenchInputs reads the binary input file and returns pre-constructed
// Nat pairs grouped by limb count, using resetToBytes.
func loadBenchInputs(t testing.TB) map[int][]benchInput {
	f, err := os.Open(benchInputFile)
	if err != nil {
		t.Fatalf("open %s: %v (run TestGenerateBenchInputs first)", benchInputFile, err)
	}
	defer f.Close()

	var nConfigs uint32
	if err := binary.Read(f, binary.LittleEndian, &nConfigs); err != nil {
		t.Fatal(err)
	}

	inputs := make(map[int][]benchInput)
	for i := 0; i < int(nConfigs); i++ {
		var limbCount, nPairs, byteLen uint32
		binary.Read(f, binary.LittleEndian, &limbCount)
		binary.Read(f, binary.LittleEndian, &nPairs)
		binary.Read(f, binary.LittleEndian, &byteLen)

		pairs := make([]benchInput, nPairs)
		aBytes := make([]byte, byteLen)
		mBytes := make([]byte, byteLen)

		for j := 0; j < int(nPairs); j++ {
			if _, err := f.Read(aBytes); err != nil {
				t.Fatal(err)
			}
			if _, err := f.Read(mBytes); err != nil {
				t.Fatal(err)
			}

			pairs[j] = benchInput{
				a: NewNat().resetToBytes(aBytes),
				m: NewNat().resetToBytes(mBytes),
			}
		}
		inputs[int(limbCount)] = pairs
	}
	return inputs
}

func BenchmarkExtendedGCD_Limbs_1(b *testing.B)   { benchExtendedGCD(b, 1) }
func BenchmarkExtendedGCD_Limbs_2(b *testing.B)   { benchExtendedGCD(b, 2) }
func BenchmarkExtendedGCD_Limbs_4(b *testing.B)   { benchExtendedGCD(b, 4) }
func BenchmarkExtendedGCD_Limbs_8(b *testing.B)   { benchExtendedGCD(b, 8) }
func BenchmarkExtendedGCD_Limbs_16(b *testing.B)  { benchExtendedGCD(b, 16) }
func BenchmarkExtendedGCD_Limbs_32(b *testing.B)  { benchExtendedGCD(b, 32) }
func BenchmarkExtendedGCD_Limbs_64(b *testing.B)  { benchExtendedGCD(b, 64) }
func BenchmarkExtendedGCD_Limbs_128(b *testing.B) { benchExtendedGCD(b, 128) }

// benchExtendedGCD benchmarks extendedGCD for a given limb size.
// Each input pair runs as its own sub-benchmark so that b.Loop() measures
// a single pair repeatedly. Use -count=N with benchstat for statistics.
//
// Run with:
//
//	./run_with_local_toolchain.sh -tags=sync_legacy -bench=BenchmarkExtendedGCD -run=^$ -count=10 | tee legacy.txt
//	./run_with_local_toolchain.sh -tags=sync_fixed  -bench=BenchmarkExtendedGCD -run=^$ -count=10 | tee fixed.txt
//	benchstat legacy.txt fixed.txt
func benchExtendedGCD(b *testing.B, limbs int) {
	inputs := loadBenchInputs(b)
	pairs := inputs[limbs]
	if len(pairs) == 0 {
		b.Fatalf("no inputs for %d limbs", limbs)
	}

	for j := range pairs {
		p := &pairs[j]
		b.Run(fmt.Sprintf("pair_%d", j), func(b *testing.B) {
			for b.Loop() {
				extendedGCD(p.a, p.m)
			}
		})
	}
}
