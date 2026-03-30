//go:build !sync_legacy && !sync_fixed

package bigmod

import (
	"errors"
	"math/big"
	"testing"
)

func keygenLikeConsistencyWithFixedPrimes(pBytes, qBytes []byte, fixed bool) (passes bool, err error) {
	prev := UseSynchronizedWrappingInExtendedGCD
	UseSynchronizedWrappingInExtendedGCD = fixed
	defer func() { UseSynchronizedWrappingInExtendedGCD = prev }()

	p := new(big.Int).SetBytes(pBytes)
	q := new(big.Int).SetBytes(qBytes)
	one := big.NewInt(1)

	pm1 := new(big.Int).Sub(new(big.Int).Set(p), one)
	qm1 := new(big.Int).Sub(new(big.Int).Set(q), one)
	g := new(big.Int).GCD(nil, nil, pm1, qm1)
	lambda := new(big.Int).Div(new(big.Int).Mul(pm1, qm1), g)

	λ, err := NewModulus(lambda.Bytes())
	if err != nil {
		return false, err
	}

	e := NewNat().SetUint(65537)
	d, ok := NewNat().InverseVarTime(e, λ)
	if !ok {
		return false, errors.New("unexpected: e not invertible mod λ")
	}

	// Same consistency check keygen uses before accepting d.
	return e.ExpandFor(λ).Mul(d, λ).IsOne() == 1, nil
}

func mathBigKeygenConsistencyWithFixedPrimes(pBytes, qBytes []byte) (passes bool, err error) {
	p := new(big.Int).SetBytes(pBytes)
	q := new(big.Int).SetBytes(qBytes)
	one := big.NewInt(1)

	pm1 := new(big.Int).Sub(new(big.Int).Set(p), one)
	qm1 := new(big.Int).Sub(new(big.Int).Set(q), one)
	g := new(big.Int).GCD(nil, nil, pm1, qm1)
	lambda := new(big.Int).Div(new(big.Int).Mul(pm1, qm1), g)

	e := big.NewInt(65537)
	d := new(big.Int).ModInverse(e, lambda)
	if d == nil {
		return false, errors.New("math/big: e not invertible mod λ")
	}
	check := new(big.Int).Mod(new(big.Int).Mul(e, d), lambda)
	return check.Cmp(one) == 0, nil
}

func TestDeterministicKeygenPathBehaviorMatrix(t *testing.T) {
	tests := []struct {
		name string
		p, q []byte
	}{
		{name: "wrapping_edge_case", p: []byte{0x01, 0x00, 0x01}, q: []byte{0x01, 0x01}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			mathBigPasses, err := mathBigKeygenConsistencyWithFixedPrimes(tt.p, tt.q)
			if err != nil {
				t.Fatalf("mathBigKeygenConsistencyWithFixedPrimes: %v", err)
			}

			legacyPasses, err := keygenLikeConsistencyWithFixedPrimes(tt.p, tt.q, false)
			if err != nil {
				t.Fatalf("legacy keygenLikeConsistencyWithFixedPrimes: %v", err)
			}

			fixedPasses, err := keygenLikeConsistencyWithFixedPrimes(tt.p, tt.q, true)
			if err != nil {
				t.Fatalf("fixed keygenLikeConsistencyWithFixedPrimes: %v", err)
			}

			t.Logf("math/big  : keygen consistency check passed = %t", mathBigPasses)
			t.Logf("legacy    : keygen consistency check passed = %t", legacyPasses)
			t.Logf("fixed     : keygen consistency check passed = %t", fixedPasses)

			if !mathBigPasses {
				t.Fatal("math/big consistency check should pass")
			}
			if fixedPasses != mathBigPasses {
				t.Fatalf("fixed mode mismatch: got %t want %t", fixedPasses, mathBigPasses)
			}
			if legacyPasses == mathBigPasses {
				t.Fatalf("expected legacy mismatch on edge case, both were %t", legacyPasses)
			}
		})
	}
}
