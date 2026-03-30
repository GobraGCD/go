//go:build !sync_legacy && !sync_fixed

package bigmod

import (
	"fmt"
	stdbig "math/big"
	"math/bits"
	"testing"
)

// gcdVarTimeWithFlag calls GCDVarTime with the given flag setting,
// recovering from panics. Returns (gcd, panicMsg) where panicMsg is
// non-empty if the function panicked.
func gcdVarTimeWithFlag(a, b *Nat, fixed bool) (gcd *stdbig.Int, panicMsg string) {
	prev := UseSynchronizedWrappingInExtendedGCD
	UseSynchronizedWrappingInExtendedGCD = fixed
	defer func() {
		UseSynchronizedWrappingInExtendedGCD = prev
		if r := recover(); r != nil {
			panicMsg = fmt.Sprint(r)
		}
	}()

	x := NewNat()
	result, err := x.GCDVarTime(a, b)
	if err != nil {
		return nil, "error: " + err.Error()
	}
	return result.asBig(), ""
}

// natFromUint64Limbs creates a Nat with the given little-endian uint64 limbs.
// On 32-bit platforms the test is skipped.
func natFromUint64Limbs(t *testing.T, limbs []uint64) *Nat {
	t.Helper()
	if bits.UintSize != 64 {
		t.Skip("test requires 64-bit limbs")
	}
	x := NewNat()
	x.reset(len(limbs))
	for i, l := range limbs {
		x.limbs[i] = uint(l)
	}
	return x
}

// TestGCDVarTimeCornerCases tests GCDVarTime with
// UseSynchronizedWrappingInExtendedGCD=true for corner cases where the
// formal precondition a.Repr() < b.Repr() is violated.
// Each test compares against math/big.GCD as ground truth.
func TestGCDVarTimeCornerCases(t *testing.T) {
	if bits.UintSize != 64 {
		t.Skip("test cases assume 64-bit limbs")
	}

	tests := []struct {
		name   string
		aLimbs []uint64 // little-endian limbs for a
		bLimbs []uint64 // little-endian limbs for b
	}{
		// --- Group 1: a > b, same number of limbs (1 limb) ---
		{
			name:   "a>b_single_limb_both_odd",
			aLimbs: []uint64{15},
			bLimbs: []uint64{7}, // GCD(15,7)=1
		},
		{
			name:   "a>b_single_limb_a_even_b_odd",
			aLimbs: []uint64{14},
			bLimbs: []uint64{9}, // GCD(14,9)=1
		},
		{
			name:   "a>b_single_limb_a_odd_b_even",
			aLimbs: []uint64{15},
			bLimbs: []uint64{10}, // GCD(15,10)=5
		},
		{
			name:   "a>b_single_limb_gcd_gt_1",
			aLimbs: []uint64{21},
			bLimbs: []uint64{15}, // GCD(21,15)=3
		},

		// --- Group 2: a == b ---
		{
			name:   "a_eq_b_single_limb",
			aLimbs: []uint64{15},
			bLimbs: []uint64{15}, // GCD(15,15)=15
		},
		{
			name:   "a_eq_b_both_1",
			aLimbs: []uint64{1},
			bLimbs: []uint64{1}, // GCD(1,1)=1
		},

		// --- Group 3: different limb counts ---
		// a has more limbs (trailing zero limb), a.Repr() > b.Repr().
		{
			name:   "a_more_limbs_via_expand_a_gt_b",
			aLimbs: []uint64{7, 0},
			bLimbs: []uint64{5}, // GCD(7,5)=1, different AnnouncedLen
		},
		// a has more limbs but a.Repr() < b.Repr() — the numeric precondition
		// holds but the limb count mismatch could still cause issues.
		{
			name:   "a_more_limbs_via_expand_a_lt_b",
			aLimbs: []uint64{5, 0},
			bLimbs: []uint64{7}, // GCD(5,7)=1
		},
		// b has more limbs (trailing zero limb), a.Repr() > b.Repr().
		{
			name:   "b_more_limbs_via_expand_a_gt_b",
			aLimbs: []uint64{7},
			bLimbs: []uint64{5, 0}, // GCD(7,5)=1
		},

		// --- Group 4: values at the limb boundary (2^64) ---
		{
			name:   "a_max_single_limb_b_small",
			aLimbs: []uint64{0xFFFFFFFFFFFFFFFF},
			bLimbs: []uint64{3}, // GCD(2^64-1, 3)=3
		},
		{
			name:   "a_max_single_limb_b_large_odd",
			aLimbs: []uint64{0xFFFFFFFFFFFFFFFF},
			bLimbs: []uint64{0xFFFFFFFFFFFFFFFD}, // GCD(2^64-1, 2^64-3)
		},
		// a crosses limb boundary (2 limbs), b is max single limb.
		{
			name:   "a_crosses_limb_boundary_b_max_single",
			aLimbs: []uint64{1, 1},              // 2^64 + 1
			bLimbs: []uint64{0xFFFFFFFFFFFFFFFF}, // 2^64 - 1
		},

		// --- Group 5: multi-limb values, a > b ---
		{
			name:   "both_2_limbs_a_gt_b",
			aLimbs: []uint64{3, 5}, // 3 + 5*2^64
			bLimbs: []uint64{7, 3}, // 7 + 3*2^64
		},
		{
			name:   "a_2_limbs_b_1_limb_a_even",
			aLimbs: []uint64{0, 1}, // 2^64 (even)
			bLimbs: []uint64{3},    // GCD(2^64, 3)=1
		},

		// --- Group 6: a barely larger than b ---
		{
			name:   "a_eq_b_plus_1",
			aLimbs: []uint64{100},
			bLimbs: []uint64{99}, // GCD(100,99)=1
		},
		{
			name:   "a_eq_b_plus_3_shared_factor",
			aLimbs: []uint64{102},
			bLimbs: []uint64{99}, // GCD(102,99)=3
		},

		// --- Group 7: one input is 1 ---
		{
			name:   "a_large_b_is_1",
			aLimbs: []uint64{0xFFFFFFFFFFFFFFFF},
			bLimbs: []uint64{1}, // GCD(2^64-1, 1)=1, a>b
		},
		{
			name:   "a_is_1_b_large",
			aLimbs: []uint64{1},
			bLimbs: []uint64{0xFFFFFFFFFFFFFFFF}, // GCD(1, 2^64-1)=1, a<b OK
		},

		// --- Group 8: 2-limb symmetry (swap a and b) ---
		{
			name:   "a_pow2m1_b_pow2p1_2limbs_a_lt_b",
			aLimbs: []uint64{0xFFFFFFFFFFFFFFFF, 0}, // 2^64-1
			bLimbs: []uint64{1, 1},                   // 2^64+1, a<b OK
		},
		{
			name:   "a_pow2p1_b_pow2m1_2limbs_a_gt_b",
			aLimbs: []uint64{1, 1},                  // 2^64+1
			bLimbs: []uint64{0xFFFFFFFFFFFFFFFF, 0}, // 2^64-1, a>b violated
		},

		// --- Group 9: large values stressing syncAdd wrapping ---
		{
			name:   "large_coprimes_2_limbs",
			aLimbs: []uint64{0xFFFFFFFFFFFFFFFD, 0xFFFFFFFFFFFFFFFF}, // 2^128-3
			bLimbs: []uint64{0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFE}, // 2^128-2^64-1
		},
		{
			name:   "large_value_a_gt_b_3_limbs",
			aLimbs: []uint64{1, 0, 1}, // 2^128+1
			bLimbs: []uint64{3, 0, 0}, // 3 in 3 limbs
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			aBig := natFromUint64Limbs(t, tt.aLimbs).asBig()
			bBig := natFromUint64Limbs(t, tt.bLimbs).asBig()

			// Ground truth from math/big.
			wantGCD := new(stdbig.Int).GCD(nil, nil, aBig, bBig)

			// Test both modes. We rebuild the Nats each time because
			// GCDVarTime may mutate them internally.
			for _, mode := range []struct {
				name  string
				fixed bool
			}{
				{"legacy", false},
				{"fixed", true},
			} {
				t.Run(mode.name, func(t *testing.T) {
					a := natFromUint64Limbs(t, tt.aLimbs)
					b := natFromUint64Limbs(t, tt.bLimbs)

					gotGCD, panicMsg := gcdVarTimeWithFlag(a, b, mode.fixed)

					if panicMsg != "" {
						t.Errorf("GCDVarTime(a=%s, b=%s) panicked: %s; expected GCD=%s",
							aBig, bBig, panicMsg, wantGCD)
						return
					}

					if gotGCD == nil {
						t.Errorf("GCDVarTime(a=%s, b=%s) returned error; expected GCD=%s",
							aBig, bBig, wantGCD)
						return
					}

					if gotGCD.Cmp(wantGCD) != 0 {
						t.Errorf("GCDVarTime(a=%s, b=%s) = %s, want %s (math/big)",
							aBig, bBig, gotGCD, wantGCD)
					} else {
						t.Logf("GCDVarTime(a=%s, b=%s) = %s OK", aBig, bBig, gotGCD)
					}
				})
			}
		})
	}
}
