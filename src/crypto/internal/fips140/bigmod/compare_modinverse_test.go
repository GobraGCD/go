//go:build !sync_legacy && !sync_fixed

package bigmod

// Tests Nat.InverseVarTime by comparing its output (for different
// values of `UseSynchronizedWrappingInExtendedGCD`) to
// `math/big.ModInverse`.

import (
	stdbig "math/big"
	"testing"
)

func setExtendedGCDFixMode(t *testing.T, enabled bool) {
	prev := UseSynchronizedWrappingInExtendedGCD
	UseSynchronizedWrappingInExtendedGCD = enabled
	t.Cleanup(func() {
		UseSynchronizedWrappingInExtendedGCD = prev
	})
}

func inverseProduct(a, m uint64, fixed bool) (prod *stdbig.Int, ok bool, err error) {
	prev := UseSynchronizedWrappingInExtendedGCD
	UseSynchronizedWrappingInExtendedGCD = fixed
	defer func() { UseSynchronizedWrappingInExtendedGCD = prev }()

	modInt := new(stdbig.Int).SetUint64(m)
	aInt := new(stdbig.Int).SetUint64(a)
	mod, err := NewModulus(modInt.Bytes())
	if err != nil {
		return nil, false, err
	}
	inv, ok := NewNat().InverseVarTime(NewNat().SetUint(uint(a)), mod)
	if !ok {
		return nil, false, nil
	}
	invInt := new(stdbig.Int).SetBytes(inv.Bytes(mod))
	return new(stdbig.Int).Mod(new(stdbig.Int).Mul(aInt, invInt), modInt), true, nil
}

func TestModInverseBehaviorMatrix(t *testing.T) {
	tests := []struct {
		name                    string
		a, m                    uint64
		expectLegacyEdgeFailure bool
	}{
		{name: "small_control", a: 2, m: 5, expectLegacyEdgeFailure: false},
		{name: "wrapping_edge_case", a: 65537, m: 65536, expectLegacyEdgeFailure: true},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			modInt := new(stdbig.Int).SetUint64(tt.m)
			aInt := new(stdbig.Int).SetUint64(tt.a)
			mbInv := new(stdbig.Int).ModInverse(aInt, modInt)
			if mbInv == nil {
				t.Fatalf("math/big.ModInverse(%d, %d) returned nil", tt.a, tt.m)
			}
			mathBigProd := new(stdbig.Int).Mod(new(stdbig.Int).Mul(aInt, mbInv), modInt)
			if mathBigProd.Cmp(stdbig.NewInt(1)) != 0 {
				t.Fatalf("math/big produced invalid inverse: a*inv mod m = %s", mathBigProd.String())
			}

			legacyProd, ok, err := inverseProduct(tt.a, tt.m, false)
			if err != nil {
				t.Fatalf("legacy inverseProduct(%d, %d): %v", tt.a, tt.m, err)
			}
			if !ok {
				t.Fatalf("legacy InverseVarTime(%d, %d) returned ok=false", tt.a, tt.m)
			}

			fixedProd, ok, err := inverseProduct(tt.a, tt.m, true)
			if err != nil {
				t.Fatalf("fixed inverseProduct(%d, %d): %v", tt.a, tt.m, err)
			}
			if !ok {
				t.Fatalf("fixed InverseVarTime(%d, %d) returned ok=false", tt.a, tt.m)
			}

			t.Logf("math/big  : a*inv mod m = %s", mathBigProd.String())
			t.Logf("legacy    : a*inv mod m = %s", legacyProd.String())
			t.Logf("fixed     : a*inv mod m = %s", fixedProd.String())

			if fixedProd.Cmp(mathBigProd) != 0 {
				t.Fatalf("fixed mode mismatch: got %s want %s", fixedProd.String(), mathBigProd.String())
			}
			if tt.expectLegacyEdgeFailure {
				if legacyProd.Cmp(mathBigProd) == 0 {
					t.Fatalf("expected legacy mismatch on edge case, both were %s", legacyProd.String())
				}
			} else {
				if legacyProd.Cmp(mathBigProd) != 0 {
					t.Fatalf("unexpected legacy mismatch on control case: legacy=%s math/big=%s", legacyProd.String(), mathBigProd.String())
				}
			}
		})
	}
}
