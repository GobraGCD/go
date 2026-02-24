package bigmod

import "testing"

// TestExtendedGCDWrappingDivergence demonstrates that extendedGCD uses
// independent wrapping for coefficient updates, which differs from fiat-crypto's
// synchronized wrapping. With a=2, m=5, the relational invariant
// v = D*m - C*a breaks after the first v >= u subtraction.
func TestExtendedGCDWrappingDivergence(t *testing.T) {
	// --- Part 1: Call extendedGCD(2, 5) and verify the result ---
	//
	// extendedGCD computes gcd(a, m) and the Bézout coefficient A
	// such that A*a ≡ gcd (mod m).
	a := NewNat().SetUint(2)
	m := NewNat().SetUint(5)

	u, A, err := extendedGCD(a, m)
	if err != nil {
		t.Fatal(err)
	}

	uVal := u.IsOdd() // just to use u; we check limbs below
	_ = uVal
	t.Logf("extendedGCD(2, 5): u=%d, A=%d", u.limbs[0], A.limbs[0])

	if u.limbs[0] != 1 {
		t.Fatalf("gcd = %d, want 1", u.limbs[0])
	}
	if (A.limbs[0]*2)%5 != 1 {
		t.Fatalf("A*a mod m = %d, want 1", (A.limbs[0]*2)%5)
	}
	t.Logf("Correct: %d * 2 = %d ≡ 1 (mod 5)", A.limbs[0], A.limbs[0]*2)

	// --- Part 2: Reproduce the divergent coefficient update step ---
	//
	// Trace of extendedGCD(2, 5):
	//   Initial:  u=2, v=5, A=1, B=0, C=0, D=1
	//
	//   u is even → halve u:
	//     u=1, A=(1+5)/2=3, B=(0+2)/2=1
	//
	//   State:    u=1, v=5, A=3, B=1, C=0, D=1
	//     relU: 3*2 - 1*5 = 1 = u  ✓
	//     relV: 1*5 - 0*2 = 5 = v  ✓
	//
	//   Both odd, v ≥ u → subtract v -= u = 4, then:
	//     C.Add(A, mMod):  C = (0+3) mod 5 = 3   (3 < 5, no wrap)
	//     D.Add(B, aMod):  D = (1+1) mod 2 = 0   (2 ≥ 2, WRAPS!)
	//
	//   Fiat-crypto (synchronized wrapping):
	//     borrow = (C+A ≥ m) = (3 ≥ 5) = false
	//     C = 3 (same), D = 2 (NOT reduced, follows C's borrow)
	//     relV: 2*5 - 3*2 = 4 = v'  ✓
	//
	//   Go (independent wrapping):
	//     C = 3, D = 0 (independently reduced since D+B ≥ a)
	//     relV: 0*5 - 3*2 = -6 ≠ 4  ✗

	mMod, err := NewModulus([]byte{5})
	if err != nil {
		t.Fatal(err)
	}
	aMod, err := NewModulus([]byte{2})
	if err != nil {
		t.Fatal(err)
	}

	C := NewNat().SetUint(0)
	Ac := NewNat().SetUint(3)
	D := NewNat().SetUint(1)
	B := NewNat().SetUint(1)

	t.Logf("Before: C=%d, A=%d, D=%d, B=%d", C.limbs[0], Ac.limbs[0], D.limbs[0], B.limbs[0])
	t.Logf("C+A = %d (vs m=5), D+B = %d (vs a=2)",
		C.limbs[0]+Ac.limbs[0], D.limbs[0]+B.limbs[0])

	C.Add(Ac, mMod) // independent: wraps if C+A ≥ 5  → 3 < 5: no wrap  → C=3
	D.Add(B, aMod)   // independent: wraps if D+B ≥ 2  → 2 ≥ 2: WRAPS!  → D=0

	CVal := int(C.limbs[0])
	DVal := int(D.limbs[0])

	t.Logf("After: C=%d, D=%d", CVal, DVal)

	// Check relV: v' = D'*m - C'*a should equal v' = 4
	relV := DVal*5 - CVal*2
	t.Logf("relV = D*m - C*a = %d*5 - %d*2 = %d (want v'=4)", DVal, CVal, relV)

	if relV == 4 {
		t.Log("relV preserved — wrapping agreed by coincidence")
	} else {
		t.Logf("relV BROKEN: got %d, want 4", relV)
	}

	t.Log("")
	t.Log("Fiat-crypto (synchronized wrapping) would produce:")
	t.Log("  borrow = (C+A >= m) = (3 >= 5) = false")
	t.Log("  C = 3 (same), D = 2 (not reduced, follows C's borrow)")
	t.Logf("  relV = 2*5 - 3*2 = 4 = v'  (preserved)")

	// Assert the divergence
	if DVal == 0 {
		t.Log("CONFIRMED: D wrapped to 0 independently (D+B=2 >= a=2)")
		t.Log("Fiat-crypto would keep D=2 (synchronized with C's no-wrap)")
	}
	if relV != 4 {
		t.Errorf("relational invariant v = D*m - C*a broken: got %d, want 4", relV)
	}
}
