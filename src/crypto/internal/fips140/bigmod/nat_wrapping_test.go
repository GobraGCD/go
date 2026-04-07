//go:build !sync_legacy && !sync_fixed

package bigmod

// Tests extendedGCD by comparing its output (for different
// values of `UseSynchronizedWrappingInExtendedGCD`) to
// `math/big.GCD`.

import (
	stdbig "math/big"
	"testing"
)

func extendedGCDCongruence(a, m uint64, fixed bool) (gcd, congr *stdbig.Int, err error) {
	prev := UseSynchronizedWrappingInExtendedGCD
	UseSynchronizedWrappingInExtendedGCD = fixed
	defer func() { UseSynchronizedWrappingInExtendedGCD = prev }()

	u, A, err := extendedGCD(NewNat().SetUint(uint(a)), NewNat().SetUint(uint(m)))
	if err != nil {
		return nil, nil, err
	}
	aBig := new(stdbig.Int).SetUint64(a)
	mBig := new(stdbig.Int).SetUint64(m)
	gcd = u.asBig()
	congr = new(stdbig.Int).Mod(new(stdbig.Int).Mul(A.asBig(), aBig), mBig)
	return gcd, congr, nil
}

func TestExtendedGCDBehaviorMatrix(t *testing.T) {
	tests := []struct {
		name                    string
		a, m                    uint64
		expectLegacyEdgeFailure bool
	}{
		{name: "small_control", a: 21, m: 15, expectLegacyEdgeFailure: false},
		{name: "wrapping_edge_case", a: 65537, m: 65536, expectLegacyEdgeFailure: true},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			aBig := new(stdbig.Int).SetUint64(tt.a)
			mBig := new(stdbig.Int).SetUint64(tt.m)
			wantGCD := new(stdbig.Int)
			mathBigX := new(stdbig.Int)
			wantGCD.GCD(mathBigX, nil, aBig, mBig)
			mathBigCongr := new(stdbig.Int).Mod(new(stdbig.Int).Mul(mathBigX, aBig), mBig)

			legacyGCD, legacyCongr, err := extendedGCDCongruence(tt.a, tt.m, false)
			if err != nil {
				t.Fatalf("legacy extendedGCD(%d, %d): %v", tt.a, tt.m, err)
			}

			fixedGCD, fixedCongr, err := extendedGCDCongruence(tt.a, tt.m, true)
			if err != nil {
				t.Fatalf("fixed extendedGCD(%d, %d): %v", tt.a, tt.m, err)
			}

			t.Logf("math/big  : gcd=%s, coeff*a mod m=%s", wantGCD.String(), mathBigCongr.String())
			t.Logf("legacy    : gcd=%s, coeff*a mod m=%s", legacyGCD.String(), legacyCongr.String())
			t.Logf("fixed     : gcd=%s, coeff*a mod m=%s", fixedGCD.String(), fixedCongr.String())

			if legacyGCD.Cmp(wantGCD) != 0 || fixedGCD.Cmp(wantGCD) != 0 {
				t.Fatalf("gcd mismatch: want %s, legacy %s, fixed %s", wantGCD.String(), legacyGCD.String(), fixedGCD.String())
			}
			if fixedCongr.Cmp(mathBigCongr) != 0 {
				t.Fatalf("fixed mode mismatch: got %s want %s", fixedCongr.String(), mathBigCongr.String())
			}
			if tt.expectLegacyEdgeFailure {
				if legacyCongr.Cmp(mathBigCongr) == 0 {
					t.Fatalf("expected legacy mismatch on edge case, both were %s", legacyCongr.String())
				}
			} else {
				if legacyCongr.Cmp(mathBigCongr) != 0 {
					t.Fatalf("unexpected legacy mismatch on control case: legacy=%s math/big=%s", legacyCongr.String(), mathBigCongr.String())
				}
			}
		})
	}
}
