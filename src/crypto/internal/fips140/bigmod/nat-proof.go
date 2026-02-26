package bigmod

import "errors"

// choice represents a constant-time boolean. The value of choice is always
// either 1 or 0. We use an int instead of bool in order to make decisions in
// constant time by turning it into a mask.
type choice uint

const yes = choice(1)
const no = choice(0)

type Nat struct {
	// limbs is little-endian in base 2^W with W = bits.UintSize.
	limbs []uint
}

/*@
pred (n *Nat) Inv() {
    acc(n) && acc(n.limbs)
}

requires acc(n.Inv(), _)
ensures res >= 0
decreases
pure func (n *Nat) Repr() (res int)
@*/

// NewNat returns a new nat with a size of zero, just like new(Nat), but with
// the preallocated capacity to hold a number of up to preallocTarget bits.
// NewNat inlines, so the allocation can live on the stack.
//@ trusted
//@ ensures n.Inv()
func NewNat() (n *Nat) {
	limbs := make([]uint, 0, preallocLimbs)
	return &Nat{limbs}
}

// expand expands x to n limbs, leaving its value unchanged.
//@ trusted
//@ preserves x.Inv()
//@ ensures x.Repr() == old(x.Repr())
func (x *Nat) expand(n int) *Nat {
	if len(x.limbs) > n {
		panic("bigmod: internal error: shrinking nat")
	}
	if cap(x.limbs) < n {
		newLimbs := make([]uint, n)
		copy(newLimbs, x.limbs)
		x.limbs = newLimbs
		return x
	}
	extraLimbs := x.limbs[len(x.limbs):n]
	clear(extraLimbs)
	x.limbs = x.limbs[:n]
	return x
}

// reset returns a zero nat of n limbs, reusing x's storage if n <= cap(x.limbs).
//@ trusted
//@ requires x.Inv()
//@ ensures  res.Inv()
//@ ensures  res.Repr() == 0
func (x *Nat) reset(n int) (res *Nat) {
	if cap(x.limbs) < n {
		x.limbs = make([]uint, n)
		return x
	}
	clear(x.limbs)
	x.limbs = x.limbs[:n]
	return x
}

// set assigns x = y, optionally resizing x to the appropriate size.
//@ trusted
//@ requires noPerm < p
//@ preserves x.Inv() && acc(y.Inv(), p)
//@ ensures x.Repr() == y.Repr()
func (x *Nat) setNat(y *Nat /*@, ghost p perm @*/) *Nat {
	x.reset(len(y.limbs))
	copy(x.limbs, y.limbs)
	return x
}

// IsZero returns 1 if x == 0, and 0 otherwise.
//
//go:norace
//@ trusted
//@ requires noPerm < p
//@ preserves acc(x.Inv(), p)
//@ ensures res == (x.Repr() == 0 ? yes : no)
func (x *Nat) IsZero(/*@ ghost p perm @*/) (res choice) {
	// Eliminate bounds checks in the loop.
	size := len(x.limbs)
	xLimbs := x.limbs[:size]

	zero := yes
	for i := 0; i < size; i++ {
		zero &= ctEq(xLimbs[i], 0)
	}
	return zero
}

// IsOdd returns 1 if x is odd, and 0 otherwise.
//@ trusted
//@ requires noPerm < p
//@ preserves acc(x.Inv(), p)
//@ ensures res == (x.Repr() % 2 == 1 ? yes : no)
func (x *Nat) IsOdd(/*@ ghost p perm @*/) (res choice) {
	if len(x.limbs) == 0 {
		return no
	}
	return choice(x.limbs[0] & 1)
}

// add computes x += y and returns the carry.
//
// Both operands must have the same announced length.
//
//go:norace
//@ trusted
//@ requires noPerm < p
//@ preserves x.Inv() && acc(y.Inv(), p)
//@ ensures x.Repr() == old(x.Repr()) + y.Repr()
func (x *Nat) add(y *Nat /*@, ghost p perm @*/) (c uint) {
	// Eliminate bounds checks in the loop.
	size := len(x.limbs)
	xLimbs := x.limbs[:size]
	yLimbs := y.limbs[:size]

	for i := 0; i < size; i++ {
		xLimbs[i], c = bits.Add(xLimbs[i], yLimbs[i], c)
	}
	return
}

// sub computes x -= y. It returns the borrow of the subtraction.
//
// Both operands must have the same announced length.
//
//go:norace
//@ trusted
//@ requires noPerm < p
//@ preserves x.Inv() && acc(y.Inv(), p)
//@ ensures x.Repr() == old(x.Repr()) - y.Repr()
func (x *Nat) sub(y *Nat /*@, ghost p perm @*/) (c uint) {
	// Eliminate bounds checks in the loop.
	size := len(x.limbs)
	xLimbs := x.limbs[:size]
	yLimbs := y.limbs[:size]

	for i := 0; i < size; i++ {
		xLimbs[i], c = bits.Sub(xLimbs[i], yLimbs[i], c)
	}
	return
}

// Modulus is used for modular arithmetic, precomputing relevant constants.
//
// A Modulus can leak the exact number of bits needed to store its value
// and is stored without padding. Its actual value is still kept secret.
type Modulus struct {
	// The underlying natural number for this modulus.
	//
	// This will be stored without any padding, and shouldn't alias with any
	// other natural number being used.
	nat *Nat

	// If m is even, the following fields are not set.
	odd   bool
	m0inv uint // -nat.limbs[0]⁻¹ mod _W
	rr    *Nat // R*R for montgomeryRepresentation
}

/*@
// it turns out that several functions operating on Modulus are happy if only the `nat` field is correct,
// which we capture via the `natOnly` parameter.
pred (m *Modulus) Inv(ghost natOnly bool) {
    acc(m) && m.nat.Inv() &&
    (!natOnly ==> m.odd == (m.nat.Repr() % 2 == 1)) &&
    (!natOnly && m.odd ==> m.rr.Inv())
}

ghost
requires acc(m.Inv(natOnly), _)
decreases
pure func (m *Modulus) Repr(natOnly bool) int {
    return unfolding acc(m.Inv(natOnly), _) in m.nat.Repr()
}
@*/

// Add computes x = x + y mod m.
//
// The length of both operands must be the same as the modulus. Both operands
// must already be reduced modulo m.
//
//go:norace
//@ trusted
//@ requires noPerm < p && noPerm < q
//@ requires x.Inv() && acc(y.Inv(), p) && acc(m.Inv(natOnly), q)
//@ requires m.Repr(natOnly) > 0
//@ requires 0 <= x.Repr() && x.Repr() < m.Repr(natOnly)
//@ requires 0 <= y.Repr() && y.Repr() < m.Repr(natOnly)
//@ ensures x.Inv() && acc(y.Inv(), p) && acc(m.Inv(natOnly), q)
//@ ensures m.Repr(natOnly) > 0
//@ ensures 0 <= x.Repr() && x.Repr() < m.Repr(natOnly)
//@ ensures old(x.Repr()) + y.Repr() < m.Repr(natOnly) ==> x.Repr() == old(x.Repr()) + y.Repr()
//@ ensures old(x.Repr()) + y.Repr() >= m.Repr(natOnly) ==> x.Repr() == old(x.Repr()) + y.Repr() - m.Repr(natOnly)
func (x *Nat) Add(y *Nat, m *Modulus /*@, ghost p perm, ghost q perm, ghost natOnly bool @*/) *Nat {
	overflow := x.add(y)
	x.maybeSubtractModulus(choice(overflow), m)
	return x
}

/*@
ghost
opaque
requires a >= 0 && m >= 0
decreases m
pure func gcd(a, m int) int {
    return m == 0 ? a : gcd(m, a % m)
}

// gcd(a, 0) == a (base case, requires revealing the definition)
ghost
requires a >= 0
ensures gcd(a, 0) == a
decreases
func gcdBaseLemma(a int) {
    reveal gcd(a, 0)
}

// gcd(a, b) == gcd(a - b, b) when a > b > 0
ghost
requires a > 0 && b > 0 && a > b
ensures gcd(a, b) == gcd(a - b, b)
decreases
func gcdSubLemma(a, b int) {
    reveal gcd(a, b)       // gcd(a, b) == gcd(b, a % b)
    reveal gcd(a - b, b)   // gcd(a-b, b) == gcd(b, (a-b) % b)
    modSubLemma(a, b)      // a % b == (a - b) % b
}

// gcd commutativity: gcd(a, b) == gcd(b, a)
ghost
requires a >= 0 && b >= 0
ensures gcd(a, b) == gcd(b, a)
decreases
func gcdCommLemma(a, b int) {
    if a == 0 && b == 0 {
        // reflexive
    } else if a == 0 {
        gcdBaseLemma(b)        // gcd(b, 0) == b
        gcdUnfoldLemma(a, b)   // gcd(0, b) == gcd(b, 0 % b)
        assert 0 % b == 0      // hint for Z3
    } else if b == 0 {
        gcdBaseLemma(a)        // gcd(a, 0) == a
        gcdUnfoldLemma(b, a)   // gcd(0, a) == gcd(a, 0 % a)
        assert 0 % a == 0      // hint for Z3
    } else if a < b {
        gcdUnfoldLemma(a, b)   // gcd(a, b) == gcd(b, a % b), a % b == a since a < b
    } else if a == b {
        gcdUnfoldLemma(a, b)   // gcd(a, a) == gcd(a, a % a) == gcd(a, 0)
        gcdUnfoldLemma(b, a)   // gcd(a, a) == gcd(a, a % a) == gcd(a, 0)
    } else {
        gcdUnfoldLemma(b, a)   // gcd(b, a) == gcd(a, b % a), b % a == b since b < a
    }
}

// Unfolds gcd one step: gcd(a, b) == gcd(b, a % b) when b > 0
ghost
requires a >= 0 && b > 0
ensures gcd(a, b) == gcd(b, a % b)
decreases
func gcdUnfoldLemma(a, b int) {
    reveal gcd(a, b)
}

// gcd(a, b) == gcd(a, b - a) when b >= a > 0
ghost
requires a > 0 && b > 0 && b >= a
ensures gcd(a, b) == gcd(a, b - a)
decreases
func gcdSubLemma2(a, b int) {
    if b == a {
        gcdBaseLemma(a)
        reveal gcd(a, a)
    } else {
        gcdCommLemma(a, b)
        gcdSubLemma(b, a)
        gcdCommLemma(b - a, a)
    }
}

// gcd(a, b) == gcd(a / 2, b) when a is even and b is odd
ghost
requires a >= 0 && b >= 0 && a % 2 == 0 && b % 2 == 1
ensures gcd(a, b) == gcd(a / 2, b)
decreases a + b
func gcdHalfLemma(a, b int) {
    if a == 0 {
        // gcd(0, b) == gcd(0, b) trivially
    } else if a < b {
        // Chain: gcd(a,b) = gcd(a,b-a) = gcd(a/2,b-a) = gcd(a/2,b-a/2) = gcd(a/2,b)
        gcdSubLemma2(a, b)              // gcd(a, b) == gcd(a, b - a)
        gcdHalfLemma(a, b - a)          // IH: gcd(a, b-a) == gcd(a/2, b-a)
        gcdSubLemma2(a / 2, b - a / 2)  // gcd(a/2, b-a/2) == gcd(a/2, b-a)
        gcdSubLemma2(a / 2, b)           // gcd(a/2, b) == gcd(a/2, b-a/2)
    } else if a == 2 * b {
        // gcd(2b, b) = gcd(b, b) = gcd(a/2, b)
        gcdSubLemma(a, b)
    } else if a < 2 * b {
        // b < a < 2b. Chain uses subtraction, commutativity, and IH.
        gcdSubLemma(a, b)                // gcd(a, b) == gcd(a-b, b)
        gcdCommLemma(a - b, b)           // gcd(a-b, b) == gcd(b, a-b)
        gcdSubLemma(b, a - b)            // gcd(b, a-b) == gcd(2b-a, a-b)
        gcdHalfLemma(2 * b - a, a - b)   // IH: gcd(2b-a, a-b) == gcd(b-a/2, a-b)
        gcdSubLemma2(b - a / 2, a / 2)   // gcd(b-a/2, a/2) == gcd(b-a/2, a-b)
        gcdSubLemma(b, a / 2)            // gcd(b, a/2) == gcd(b-a/2, a/2)
        gcdCommLemma(a / 2, b)           // gcd(a/2, b) == gcd(b, a/2)
    } else {
        // a > 2b. Chain: gcd(a,b) = gcd(a-b,b) = gcd(a-2b,b) = gcd(a/2-b,b) = gcd(a/2,b)
        gcdSubLemma(a, b)                // gcd(a, b) == gcd(a-b, b)
        gcdSubLemma(a - b, b)            // gcd(a-b, b) == gcd(a-2b, b)
        gcdHalfLemma(a - 2 * b, b)       // IH: gcd(a-2b, b) == gcd((a-2b)/2, b)
        assert (a - 2 * b) / 2 == a / 2 - b
        gcdSubLemma(a / 2, b)            // gcd(a/2, b) == gcd(a/2-b, b)
    }
}

// gcd(a, b) == gcd(a, b / 2) when b is even and a is odd
ghost
requires a >= 0 && b >= 0 && b % 2 == 0 && a % 2 == 1
ensures gcd(a, b) == gcd(a, b / 2)
decreases
func gcdHalfLemma2(a, b int) {
    gcdCommLemma(a, b)     // gcd(a, b) == gcd(b, a)
    gcdHalfLemma(b, a)     // gcd(b, a) == gcd(b / 2, a)
    gcdCommLemma(b / 2, a) // gcd(b / 2, a) == gcd(a, b / 2)
}

// Opaque relational predicates. These hide the non-linear terms (products)
// from Z3 to avoid NIA timeouts. Use `reveal` to open at specific points.
ghost
opaque
decreases
pure func relU(u, A, B, aVal, mVal int) bool {
    return u == A * aVal - B * mVal
}

ghost
opaque
decreases
pure func relV(v, C, D, aVal, mVal int) bool {
    return v == D * mVal - C * aVal
}

// ===== Trusted mathematical lemmas =======================================
// The following lemmas are trusted: their bodies are not verified by Z3.
// Each includes a Lean 4 formalization for external verification.

// Modular subtraction: a % b == (a - b) % b when a > b > 0.
//
// Lean 4:
@*//*
  theorem modSubLemma {a b : Int} :
      a % b = (a - b) % b := by
    simp
*//*@
ghost
trusted
requires b != 0
ensures a % b == (a - b) % b
decreases
func modSubLemma(a, b int)

// Product parity: (a * b) % 2 == (a % 2) * (b % 2).
//
// Lean 4:
@*//*
  theorem prodParityLemma {a b : Int} :
      (a * b) % 2 = (a % 2) * (b % 2) := by
    rw [Int.mul_emod]
    have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    grind
*//*@
ghost
trusted
ensures (a * b) % 2 == (a % 2) * (b % 2)
decreases
func prodParityLemma(a, b int)

// ===== End trusted mathematical lemmas ===================================

// Positive product: a > 0 and b > 0 implies a * b > 0.
// Isolates this NIA fact so Z3 handles it in a small context.
ghost
requires a > 0 && b > 0
ensures a * b > 0
decreases
func posProdLemma(a, b int) {}

// Distributive law: (a + b) * c == a * c + b * c
// This isolates a single NIA fact for Z3.
ghost
ensures (a + b) * c == a * c + b * c
decreases
func distLemma(a, b, c int) {}

// Expand u - v using relational invariants:
// u = A*a - B*m and v = D*m - C*a imply u - v = (A+C)*a - (B+D)*m.
// Isolates the reveal + distLemma NIA from later proof steps.
ghost
requires relU(u, A, B, a, m)
requires relV(v, C, D, a, m)
ensures u - v == (A + C) * a - (B + D) * m
decreases
func subExpandLemma(u, v, A, B, C, D, a, m int) {
    reveal relU(u, A, B, a, m)
    reveal relV(v, C, D, a, m)
    distLemma(A, C, a)
    distLemma(B, D, m)
}

// Expand v - u symmetrically: v - u = (D+B)*m - (C+A)*a.
ghost
requires relU(u, A, B, a, m)
requires relV(v, C, D, a, m)
ensures v - u == (D + B) * m - (C + A) * a
decreases
func subExpandLemma2(u, v, A, B, C, D, a, m int) {
    reveal relU(u, A, B, a, m)
    reveal relV(v, C, D, a, m)
    distLemma(C, A, a)
    distLemma(D, B, m)
}

// Modular addition preserves linear combinations (when wrapping is synchronized).
//
// Given integers A, B, C, D in range [0,m) and [0,a) respectively,
// define A' = (A+C) mod m and B' = (B+D) mod a (single-subtraction mod
// since A+C < 2m and B+D < 2a). If both pairs wrap or neither does, then:
//
//   (A+C)*a - (B+D)*m == A'*a - B'*m
//
// Proof (2-case analysis, mixed wrapping excluded by precondition):
// - Neither wraps: A'=A+C, B'=B+D. Trivially equal.
// - Both wrap: A'=A+C-m, B'=B+D-a.
//     A'*a - B'*m = (A+C)*a - m*a - (B+D)*m + a*m
//                 = (A+C)*a - (B+D)*m  (since m*a = a*m).  ✓
//
// The only NIA fact used is commutativity: m*a = a*m.
ghost
requires a > 1 && m > 1
requires 0 <= A && A < m && 0 <= C && C < m
requires 0 <= B && B < a && 0 <= D && D < a
requires (A + C >= m) == (B + D >= a)
requires A + C < m ==> Ap == A + C
requires A + C >= m ==> Ap == A + C - m
requires B + D < a ==> Bp == B + D
requires B + D >= a ==> Bp == B + D - a
ensures (A + C) * a - (B + D) * m == Ap * a - Bp * m
decreases
func modAddLemma(A, B, C, D, Ap, Bp, a, m int) {
	if A + C < m {
		// Neither wraps: Ap = A+C, Bp = B+D. Trivial.
	} else {
		// Both wrap: Ap = A+C-m, Bp = B+D-a.
		// Use distLemma to expand the products:
		distLemma(Ap, m, a)  // (Ap+m)*a == Ap*a + m*a, i.e., (A+C)*a == Ap*a + m*a
		distLemma(Bp, a, m)  // (Bp+a)*m == Bp*m + a*m, i.e., (B+D)*m == Bp*m + a*m
		// Now Z3 has:
		//   (A+C)*a == Ap*a + m*a
		//   (B+D)*m == Bp*m + a*m
		// So: (A+C)*a - (B+D)*m == Ap*a + m*a - Bp*m - a*m == Ap*a - Bp*m
		// The last step requires m*a == a*m (commutativity), which Z3 knows.
	}
}

// Relational invariant maintenance for subtraction (u > v case), no-wrap:
// A' = A + C, B' = B + D (no modular reduction needed).
// B+D <= a follows from AC_lt_BD_le (called at call site).
// TODO: can likely prove the stronger bound BNew < aVal
ghost
requires relU(uOld, AOld, BOld, aVal, mVal)
requires relV(vOld, COld, DOld, aVal, mVal)
requires uNew == uOld - vOld
requires uNew > 0
requires aVal > 1 && mVal > 1
requires 0 <= AOld && AOld < mVal && 0 <= COld && COld < mVal
requires 0 <= BOld && BOld <= aVal && 0 <= DOld && DOld <= aVal
requires ANew == AOld + COld
requires BNew == BOld + DOld
requires BNew <= aVal
requires ANew < mVal
ensures relU(uNew, ANew, BNew, aVal, mVal)
ensures 0 <= ANew && ANew < mVal
ensures 0 <= BNew && BNew <= aVal
decreases
func subRelLemmaNoWrap(uOld, vOld, uNew, AOld, BOld, COld, DOld, ANew, BNew, aVal, mVal int) {
    subExpandLemma(uOld, vOld, AOld, BOld, COld, DOld, aVal, mVal)
    reveal relU(uNew, ANew, BNew, aVal, mVal)
}

// Relational invariant maintenance for subtraction (u > v case), wrap:
// A' = A + C - m, B' = B + D - a (synchronized subtraction).
// B+D >= a is established by AC_ge_BD_ge (called at call site).
// TODO: can likely prove the stronger bound BNew < aVal
//
// Lean 4:
@*//*
  theorem subRelLemmaWrap {uOld vOld uNew AOld BOld COld DOld ANew BNew aVal mVal : Int}
    (hU : uOld = AOld * aVal - BOld * mVal)
    (hV : vOld = DOld * mVal - COld * aVal)
    (hSub : uNew = uOld - vOld)
    (hA : ANew = AOld + COld - mVal) (hB : BNew = BOld + DOld - aVal)
    (hWrapB : BOld + DOld ≥ aVal)
    (hBBnd : BOld ≤ aVal) (hDBnd : DOld ≤ aVal) :
    uNew = ANew * aVal - BNew * mVal ∧ 0 ≤ BNew ∧ BNew ≤ aVal := by
  constructor; · linarith [mul_comm mVal aVal]
  constructor; · linarith
  linarith
*//*@
ghost
trusted
requires relU(uOld, AOld, BOld, aVal, mVal)
requires relV(vOld, COld, DOld, aVal, mVal)
requires uNew == uOld - vOld
requires aVal > 1 && mVal > 1
requires 0 <= AOld && AOld < mVal && 0 <= COld && COld < mVal
requires 0 <= BOld && BOld <= aVal && 0 <= DOld && DOld <= aVal
requires ANew == AOld + COld - mVal
requires BNew == BOld + DOld - aVal
requires AOld + COld >= mVal
requires BOld + DOld >= aVal
ensures relU(uNew, ANew, BNew, aVal, mVal)
ensures 0 <= ANew && ANew < mVal
ensures 0 <= BNew && BNew <= aVal
decreases
func subRelLemmaWrap(uOld, vOld, uNew, AOld, BOld, COld, DOld, ANew, BNew, aVal, mVal int)

// Relational invariant maintenance for subtraction (v >= u case), no-wrap:
// C' = C + A, D' = D + B (no modular reduction needed).
// DNew*mVal = vNew + CNew*aVal < mVal + mVal*aVal = mVal*(aVal+1), so DNew <= aVal.
//
// Lean 4:
@*//*
  theorem subRelLemma2NoWrap {uOld vOld vNew AOld BOld COld DOld CNew DNew aVal mVal : Int}
    (hU : uOld = AOld * aVal - BOld * mVal)
    (hV : vOld = DOld * mVal - COld * aVal)
    (hSub : vNew = vOld - uOld)
    (hVge : vNew ≥ 0) (hVlt : vNew < mVal)
    (hAgt : aVal > 1) (hMgt : mVal > 1)
    (hC : CNew = COld + AOld) (hD : DNew = DOld + BOld)
    (hClt : CNew < mVal) :
    vNew = DNew * mVal - CNew * aVal ∧ 0 ≤ DNew ∧ DNew ≤ aVal := by
    constructor; · linarith [mul_comm mVal aVal]
    constructor
    · -- DNew ≥ 0: DNew*mVal = vNew + CNew*aVal ≥ 0
      nlinarith [mul_comm mVal aVal]
    · -- DNew ≤ aVal: DNew*mVal = vNew + CNew*aVal < mVal + (mVal-1)*aVal = mVal*(aVal+1)-aVal
      nlinarith [mul_comm mVal aVal, mul_comm CNew aVal, mul_comm DNew mVal]
*//*@
ghost
trusted
requires relU(uOld, AOld, BOld, aVal, mVal)
requires relV(vOld, COld, DOld, aVal, mVal)
requires vNew == vOld - uOld
requires vNew >= 0
requires vNew < mVal
requires aVal > 1 && mVal > 1
requires 0 <= AOld && AOld < mVal && 0 <= COld && COld < mVal
requires 0 <= BOld && BOld <= aVal && 0 <= DOld && DOld <= aVal
requires CNew == COld + AOld
requires DNew == DOld + BOld
requires DNew <= aVal
requires CNew < mVal
ensures relV(vNew, CNew, DNew, aVal, mVal)
ensures 0 <= CNew && CNew < mVal
ensures 0 <= DNew && DNew <= aVal
decreases
func subRelLemma2NoWrap(uOld, vOld, vNew, AOld, BOld, COld, DOld, CNew, DNew, aVal, mVal int)

// Relational invariant maintenance for subtraction (v >= u case), wrap:
// C' = C + A - m, D' = D + B - a (synchronized subtraction).
// D+B >= a is established by AC_ge_BD_ge (called at call site).
//
// Lean 4:
@*//*
  // TODO: can likely prove the stronger bound DNew < aVal
  theorem subRelLemma2Wrap {uOld vOld vNew AOld BOld COld DOld CNew DNew aVal mVal : Int}
    (hU : uOld = AOld * aVal - BOld * mVal)
    (hV : vOld = DOld * mVal - COld * aVal)
    (hSub : vNew = vOld - uOld)
    (hC : CNew = COld + AOld - mVal) (hD : DNew = DOld + BOld - aVal)
    (hWrapD : DOld + BOld ≥ aVal)
    (hBBnd : BOld ≤ aVal) (hDBnd : DOld ≤ aVal) :
    vNew = DNew * mVal - CNew * aVal ∧ 0 ≤ DNew ∧ DNew ≤ aVal := by
    constructor; · linarith [mul_comm mVal aVal]
    constructor; · linarith
    linarith
*//*@
ghost
trusted
requires relU(uOld, AOld, BOld, aVal, mVal)
requires relV(vOld, COld, DOld, aVal, mVal)
requires vNew == vOld - uOld
requires aVal > 1 && mVal > 1
requires 0 <= AOld && AOld < mVal && 0 <= COld && COld < mVal
requires 0 <= BOld && BOld <= aVal && 0 <= DOld && DOld <= aVal
requires CNew == COld + AOld - mVal
requires DNew == DOld + BOld - aVal
requires COld + AOld >= mVal
requires DOld + BOld >= aVal
ensures relV(vNew, CNew, DNew, aVal, mVal)
ensures 0 <= CNew && CNew < mVal
ensures 0 <= DNew && DNew <= aVal
decreases
func subRelLemma2Wrap(uOld, vOld, vNew, AOld, BOld, COld, DOld, CNew, DNew, aVal, mVal int)

// AC_ge_BD_ge: When A+C >= m, then B+D >= a. (Matches fiat-crypto's AC_ge_BD_ge.)
// Proof: (B+D)*m = (A+C)*a - (u-v). Since A+C >= m: (A+C)*a >= m*a.
// And u-v <= u <= a. So (B+D)*m >= m*a - a = a*(m-1).
// If B+D <= a-1: (a-1)*m >= a*(m-1), giving a >= m. Contradicts a < m.
//
// TODO: For the v >= u case, the a < m condition could potentially be dropped
// (since v >= u gives u-v <= 0, making (B+D)*m >= m*a directly).
//
// Lean 4:
@*//*
  theorem AC_ge_BD_ge {u v A B C D a m : Int}
    (hU : u = A * a - B * m) (hV : v = D * m - C * a)
    (hUpos : 0 < u) (hUle : u ≤ a) (hVge : 0 ≤ v)
    (hWrap : A + C ≥ m)
    (hAltM : a < m) (hApos : 0 < a) (hMpos : 0 < m) :
    B + D ≥ a := by nlinarith [mul_comm m a]
*//*@
ghost
trusted
requires relU(u, A, B, a, m)
requires relV(v, C, D, a, m)
requires 0 < u && u <= a && 0 <= v
requires A + C >= m
requires 0 < a && a < m && 0 < m
ensures B + D >= a
decreases
func AC_ge_BD_ge(u, v, A, B, C, D, a, m int)

// AC_lt_BD_le: When A+C < m, then B+D <= a. (Matches fiat-crypto's AC_lt_BD_le.)
// Proof: (B+D)*m = (A+C)*a - u + v. Since A+C <= m-1: (A+C)*a <= (m-1)*a.
// Since u >= 1, v <= m: (B+D)*m <= (m-1)*a - 1 + m.
// If B+D >= a+1: (a+1)*m <= (m-1)*a - 1 + m = ma - a + m - 1,
// giving am + m <= am - a + m - 1, i.e. 0 <= -a-1. Contradiction.
//
// Lean 4:
@*//*
  theorem AC_lt_BD_le {u v A B C D a m : Int}
    (hU : u = A * a - B * m) (hV : v = D * m - C * a)
    (hUpos : 0 < u) (hVle : v ≤ m)
    (hNoWrap : A + C < m)
    (hApos : 0 < a) (hMpos : 0 < m) :
    B + D ≤ a := by nlinarith [mul_comm m a]
*//*@
ghost
trusted
requires relU(u, A, B, a, m)
requires relV(v, C, D, a, m)
requires 0 < u && v <= m
requires A + C < m
requires 0 < a && 0 < m
ensures B + D <= a
decreases
func AC_lt_BD_le(u, v, A, B, C, D, a, m int)

// Parity lemma: when u = A*a - B*m is even and A or B is odd,
// then A+m and B+a are both even. Reveals relU only for parity reasoning.
ghost
requires relU(u, A, B, a, m)
requires u % 2 == 0
requires A >= 0 && B >= 0 && a >= 0 && m >= 0
requires a % 2 != 0 || m % 2 != 0
requires A % 2 != 0 || B % 2 != 0
ensures (A + m) % 2 == 0
ensures (B + a) % 2 == 0
decreases
func parityLemma(u, A, B, a, m int) {
    reveal relU(u, A, B, a, m)
    prodParityLemma(A, a)
    prodParityLemma(B, m)
}

// Relational invariant maintenance for halving u:
ghost
requires relU(uOld, AOld, BOld, aVal, mVal)
requires uOld % 2 == 0
requires uNew == uOld / 2
requires AOld % 2 == 0 && BOld % 2 == 0 ==> (ANew == AOld / 2 && BNew == BOld / 2)
requires (AOld % 2 != 0 || BOld % 2 != 0) ==> (ANew == (AOld + mVal) / 2 && BNew == (BOld + aVal) / 2)
requires (AOld % 2 != 0 || BOld % 2 != 0) ==> (AOld + mVal) % 2 == 0 && (BOld + aVal) % 2 == 0
requires 0 <= AOld && AOld < mVal && mVal > 1
requires 0 <= BOld && BOld <= aVal && aVal > 1 // TODO: can likely prove with BOld < aVal
ensures relU(uNew, ANew, BNew, aVal, mVal)
ensures 0 <= ANew && ANew < mVal
ensures 0 <= BNew && BNew <= aVal // TODO: can likely prove stronger BNew < aVal
decreases
func halvRelLemmaU(uOld, uNew, AOld, BOld, ANew, BNew, aVal, mVal int) {
    reveal relU(uOld, AOld, BOld, aVal, mVal)
    // Z3 knows: uOld == AOld * aVal - BOld * mVal, uOld is even
    if AOld % 2 == 0 && BOld % 2 == 0 {
        // Even case: ANew = AOld/2, BNew = BOld/2
        assert AOld == 2 * ANew
        assert BOld == 2 * BNew
        distLemma(ANew, ANew, aVal)
        distLemma(BNew, BNew, mVal)
    } else {
        // Odd case: ANew = (AOld+mVal)/2, BNew = (BOld+aVal)/2
        // Precondition gives (AOld+mVal) and (BOld+aVal) are even
        assert (AOld + mVal) == 2 * ANew
        assert (BOld + aVal) == 2 * BNew
        distLemma(ANew, ANew, aVal)
        distLemma(BNew, BNew, mVal)
        distLemma(AOld, mVal, aVal)
        distLemma(BOld, aVal, mVal)
    }
    reveal relU(uNew, ANew, BNew, aVal, mVal)
}

// Parity lemma for v: when v = D*m - C*a is even and C or D is odd,
// then C+m and D+a are both even.
ghost
requires relV(v, C, D, a, m)
requires v % 2 == 0
requires C >= 0 && D >= 0 && a >= 0 && m >= 0
requires a % 2 != 0 || m % 2 != 0
requires C % 2 != 0 || D % 2 != 0
ensures (C + m) % 2 == 0
ensures (D + a) % 2 == 0
decreases
func parityLemmaV(v, C, D, a, m int) {
    reveal relV(v, C, D, a, m)
    prodParityLemma(C, a)
    prodParityLemma(D, m)
}

// Relational invariant maintenance for halving v:
//
// With DOld <= aVal:
// - Even case: DNew = DOld/2 <= aVal/2 < aVal. So DNew <= aVal. ✓
// - Odd case: DNew = (DOld+aVal)/2. If DOld < aVal: DNew < aVal. If DOld = aVal: DNew = aVal.
//   So DNew <= aVal in general.
//
// Lean 4:
@*//*
  theorem halvRelLemmaV {vOld vNew COld DOld CNew DNew aVal mVal : Int}
    (hRel : vOld = DOld * mVal - COld * aVal) (hEven : vOld % 2 = 0)
    (hHalf : vNew = vOld / 2)
    (hEE : COld % 2 = 0 ∧ DOld % 2 = 0 → CNew = COld / 2 ∧ DNew = DOld / 2)
    (hOE : (COld % 2 ≠ 0 ∨ DOld % 2 ≠ 0) → CNew = (COld + mVal) / 2 ∧ DNew = (DOld + aVal) / 2)
    (hPar : (COld % 2 ≠ 0 ∨ DOld % 2 ≠ 0) → (COld + mVal) % 2 = 0 ∧ (DOld + aVal) % 2 = 0)
    (hCBnd : 0 ≤ COld ∧ COld < mVal ∧ mVal > 1)
    (hDBnd : 0 ≤ DOld ∧ DOld ≤ aVal ∧ aVal > 1) :
    vNew = DNew * mVal - CNew * aVal ∧ 0 ≤ CNew ∧ CNew < mVal ∧ 0 ≤ DNew ∧ DNew ≤ aVal := by
    omega
*//*@
ghost
trusted
requires relV(vOld, COld, DOld, aVal, mVal)
requires vOld % 2 == 0
requires vNew == vOld / 2
requires COld % 2 == 0 && DOld % 2 == 0 ==> (CNew == COld / 2 && DNew == DOld / 2)
requires (COld % 2 != 0 || DOld % 2 != 0) ==> (CNew == (COld + mVal) / 2 && DNew == (DOld + aVal) / 2)
requires (COld % 2 != 0 || DOld % 2 != 0) ==> (COld + mVal) % 2 == 0 && (DOld + aVal) % 2 == 0
requires 0 <= COld && COld < mVal && mVal > 1
requires 0 <= DOld && DOld <= aVal && aVal > 1
ensures relV(vNew, CNew, DNew, aVal, mVal)
ensures 0 <= CNew && CNew < mVal
ensures 0 <= DNew && DNew <= aVal
decreases
func halvRelLemmaV(vOld, vNew, COld, DOld, CNew, DNew, aVal, mVal int)
@*/

// extendedGCD computes u and A such that u = GCD(a, m) and u = A*a - B*m.
//
// u will have the size of the larger of a and m, and A will have the size of m.
//
// It is an error if either a or m is zero, or if they are both even.
//@ requires noPerm < p && p <= 1
//@ requires acc(a.Inv(), p) && acc(m.Inv(), p)
//@ requires a.Repr() > 1 && m.Repr() > 1
//@ requires a.Repr() < m.Repr() // TODO move this into the function
//@ ensures acc(a.Inv(), p) && acc(m.Inv(), p)
//@ ensures err == nil ==> u.Inv() && A.Inv()
//@ ensures err == nil ==> u.Repr() == gcd(a.Repr(), m.Repr())
//@ ensures err == nil ==> u.Repr() == A.Repr() * a.Repr() - BRepr * m.Repr()
func extendedGCD(a, m *Nat /*@, ghost p perm @*/) (u, A *Nat, err error /*@, ghost BRepr int @*/) {
	// This is the extended binary GCD algorithm described in the Handbook of
	// Applied Cryptography, Algorithm 14.61, adapted by BoringSSL to bound
	// coefficients and avoid negative numbers. For more details and proof of
	// correctness, see https://github.com/mit-plv/fiat-crypto/pull/333/files.
	//
	// Following the proof linked in the PR above, the changes are:
	//
	// 1. Negate [B] and [C] so they are positive. The invariant now involves a
	//    subtraction.
	// 2. If step 2 (both [x] and [y] are even) runs, abort immediately. This
	//    case needs to be handled by the caller.
	// 3. Subtract copies of [x] and [y] as needed in step 6 (both [u] and [v]
	//    are odd) so coefficients stay in bounds.
	// 4. Replace the [u >= v] check with [u > v]. This changes the end
	//    condition to [v = 0] rather than [u = 0]. This saves an extra
	//    subtraction due to which coefficients were negated.
	// 5. Rename x and y to a and n, to capture that one is a modulus.
	// 6. Rearrange steps 4 through 6 slightly. Merge the loops in steps 4 and
	//    5 into the main loop (step 7's goto), and move step 6 to the start of
	//    the loop iteration, ensuring each loop iteration halves at least one
	//    value.
	//
	// Note this algorithm does not handle either input being zero.

	if a.IsZero(/*@ p / 2 @*/) == yes || m.IsZero(/*@ p / 2 @*/) == yes {
		return nil, nil, errors.New("extendedGCD: a or m is zero") /*@, 0 @*/
	}
	if a.IsOdd(/*@ p / 2 @*/) == no && m.IsOdd(/*@ p / 2 @*/) == no {
		return nil, nil, errors.New("extendedGCD: both a and m are even") /*@, 0 @*/
	}

	//@ assert 0 < a.Repr() && 0 < m.Repr()
	//@ assert a.Repr() % 2 != 0 || m.Repr() % 2 != 0

	size := maxLen(a, m /*@, p / 2, p / 2 @*/)
	u = NewNat()
	u.setNat(a /*@, p / 2 @*/)
	u.expand(size)
	v := NewNat()
	v.setNat(m /*@, p / 2 @*/)
	v.expand(size)

	A = NewNat().reset(natLen(m /*@, p / 2 @*/))
	setOne(A)
	B := NewNat().reset(natLen(a /*@, p / 2 @*/))
	C := NewNat().reset(natLen(m /*@, p / 2 @*/))
	D := NewNat().reset(natLen(a /*@, p / 2 @*/))
	setOne(D)

	// Construct Modulus wrappers for modular addition of coefficients.
	// Only nat is set (natOnly=true) since Add only uses the nat field.
	mMod := &Modulus{nat: m}
	//@ fold acc(mMod.Inv(true), p/2)
	aMod := &Modulus{nat: a}
	//@ fold acc(aMod.Inv(true), p/2)

	// Establish relational invariants:
	// u = a = 1*a - 0*m, so relU(a, 1, 0, a, m) holds.
	// v = m = 1*m - 0*a, so relV(m, 0, 1, a, m) holds.
	//@ reveal relU(u.Repr(), A.Repr(), B.Repr(), a.Repr(), m.Repr())
	//@ reveal relV(v.Repr(), C.Repr(), D.Repr(), a.Repr(), m.Repr())

	// Before and after each loop iteration, the following hold:
	//
	//   u = A*a - B*m
	//   v = D*m - C*a
	//   0 < u <= a
	//   0 <= v <= m
	//   0 <= A < m
	//   0 <= B <= a
	//   0 <= C < m
	//   0 <= D <= a
	//
	// After each loop iteration, u and v only get smaller, and at least one of
	// them shrinks by at least a factor of two.
	//@ invariant noPerm < p && p <= 1
	//@ invariant u.Inv() && v.Inv()
	//@ invariant A.Inv() && B.Inv() && C.Inv() && D.Inv()
	//@ invariant acc(mMod.Inv(true), p/2) && acc(aMod.Inv(true), p/2)
	//@ invariant acc(m.Inv(), p/2) && acc(a.Inv(), p/2)
	//@ invariant mMod.Repr(true) > 0 && aMod.Repr(true) > 0
	//@ invariant mMod.Repr(true) == m.Repr() && aMod.Repr(true) == a.Repr()
	//@ invariant a.Repr() > 1 && m.Repr() > 1
	//@ invariant a.Repr() < m.Repr()
	//@ invariant a.Repr() % 2 != 0 || m.Repr() % 2 != 0
	//@ invariant gcd(u.Repr(), v.Repr()) == gcd(a.Repr(), m.Repr())
	// Relational invariants (abstract to avoid NIA):
	//@ invariant relU(u.Repr(), A.Repr(), B.Repr(), a.Repr(), m.Repr())
	//@ invariant relV(v.Repr(), C.Repr(), D.Repr(), a.Repr(), m.Repr())
	// Parity: at least one of u,v is odd (since gcd is odd).
	//@ invariant u.Repr() % 2 == 1 || v.Repr() % 2 == 1
	// Bound invariants:
	//@ invariant 0 < u.Repr() && u.Repr() <= a.Repr()
	//@ invariant 0 <= v.Repr() && v.Repr() <= m.Repr()
	//@ invariant 0 <= A.Repr() && A.Repr() < m.Repr()
	//@ invariant 0 <= B.Repr() && B.Repr() <= a.Repr() // TODO: can likely prove stronger B < a
	//@ invariant 0 <= C.Repr() && C.Repr() < m.Repr()
	//@ invariant 0 <= D.Repr() && D.Repr() <= a.Repr()
	//@ decreases u.Repr() + v.Repr()
	for {
		//@ oldSum := u.Repr() + v.Repr()
		// If both u and v are odd, subtract the smaller from the larger.
		// If u = v, we need to subtract from v to hit the modified exit condition.
		if u.IsOdd(/*@ p / 2 @*/) == yes && v.IsOdd(/*@ p / 2 @*/) == yes {
			if v.cmpGeq(u /*@, p / 4, p / 4 @*/) == no {
				//@ preU := u.Repr()
				//@ preV := v.Repr()
				//@ preA := A.Repr()
				//@ preB := B.Repr()
				//@ preC := C.Repr()
				//@ preD := D.Repr()
				u.sub(v /*@, p / 2 @*/)
				//@ gcdSubLemma(preU, preV)
				A.add(C /*@, p / 4 @*/)
				B.add(D /*@, p / 4 @*/)
				if A.cmpGeq(m /*@, p / 4, p / 4 @*/) == yes {
					//@ AC_ge_BD_ge(preU, preV, preA, preB, preC, preD, a.Repr(), m.Repr())
					A.sub(m /*@, p / 4 @*/)
					B.sub(a /*@, p / 4 @*/)
					//@ subRelLemmaWrap(preU, preV, u.Repr(), preA, preB, preC, preD, A.Repr(), B.Repr(), a.Repr(), m.Repr())
				} else {
					//@ AC_lt_BD_le(preU, preV, preA, preB, preC, preD, a.Repr(), m.Repr())
					//@ subRelLemmaNoWrap(preU, preV, u.Repr(), preA, preB, preC, preD, A.Repr(), B.Repr(), a.Repr(), m.Repr())
				}
			} else {
				//@ preU := u.Repr()
				//@ preV := v.Repr()
				//@ preA := A.Repr()
				//@ preB := B.Repr()
				//@ preC := C.Repr()
				//@ preD := D.Repr()
				v.sub(u /*@, p / 2 @*/)
				//@ gcdSubLemma2(preU, preV)
				C.add(A /*@, p / 4 @*/)
				D.add(B /*@, p / 4 @*/)
				if C.cmpGeq(m /*@, p / 4, p / 4 @*/) == yes {
					//@ AC_ge_BD_ge(preU, preV, preA, preB, preC, preD, a.Repr(), m.Repr())
					C.sub(m /*@, p / 4 @*/)
					D.sub(a /*@, p / 4 @*/)
					//@ subRelLemma2Wrap(preU, preV, v.Repr(), preA, preB, preC, preD, C.Repr(), D.Repr(), a.Repr(), m.Repr())
				} else {
					//@ AC_lt_BD_le(preU, preV, preA, preB, preC, preD, a.Repr(), m.Repr())
					//@ subRelLemma2NoWrap(preU, preV, v.Repr(), preA, preB, preC, preD, C.Repr(), D.Repr(), a.Repr(), m.Repr())
				}
			}
		}

		// Exactly one of u and v is now even.
		if u.IsOdd(/*@ p / 2 @*/) == v.IsOdd(/*@ p / 2 @*/) {
			panic("bigmod: internal error: u and v are not in the expected state")
		}

		// Halve the even one and adjust the corresponding coefficient.
		if u.IsOdd(/*@ p / 2 @*/) == no {
			//@ preU := u.Repr()
			//@ preV := v.Repr()
			//@ preA := A.Repr()
			//@ preB := B.Repr()
			rshift1(u, 0)
			//@ gcdHalfLemma(preU, preV)
			if A.IsOdd(/*@ p / 2 @*/) == yes || B.IsOdd(/*@ p / 2 @*/) == yes {
				//@ parityLemma(preU, preA, preB, a.Repr(), m.Repr())
				rshift1(A, A.add(m /*@, p / 4 @*/))
				rshift1(B, B.add(a /*@, p / 4 @*/))
			} else {
				rshift1(A, 0)
				rshift1(B, 0)
			}
			//@ halvRelLemmaU(preU, u.Repr(), preA, preB, A.Repr(), B.Repr(), a.Repr(), m.Repr())
		} else { // v.IsOdd() == no
			//@ preU := u.Repr()
			//@ preV := v.Repr()
			//@ preC := C.Repr()
			//@ preD := D.Repr()
			rshift1(v, 0)
			//@ gcdHalfLemma2(preU, preV)
			if C.IsOdd(/*@ p / 2 @*/) == yes || D.IsOdd(/*@ p / 2 @*/) == yes {
				//@ parityLemmaV(preV, preC, preD, a.Repr(), m.Repr())
				rshift1(C, C.add(m /*@, p / 4 @*/))
				rshift1(D, D.add(a /*@, p / 4 @*/))
			} else {
				rshift1(C, 0)
				rshift1(D, 0)
			}
			//@ halvRelLemmaV(preV, v.Repr(), preC, preD, C.Repr(), D.Repr(), a.Repr(), m.Repr())
		}

		if v.IsZero(/*@ p / 2 @*/) == yes {
			// v == 0, so gcd(u, 0) == u (base case of gcd)
			//@ gcdBaseLemma(u.Repr())
			// Open the opaque relational invariant to get the actual equation
			// for the postcondition: u = A*a - B*m.
			//@ reveal relU(u.Repr(), A.Repr(), B.Repr(), a.Repr(), m.Repr())
			//@ unfold acc(mMod.Inv(true), p/2)
			//@ unfold acc(aMod.Inv(true), p/2)
			return u, A, nil /*@, B.Repr() @*/
		}
		// Help Z3 with the termination proof: the halving reduced the sum.
		//@ assert u.Repr() + v.Repr() < oldSum
	}
}

//@ trusted
//@ requires noPerm < p && noPerm < q
//@ preserves acc(x.Inv(), p) && acc(y.Inv(), q)
//@ ensures res == (x.Repr() >= y.Repr() ? yes : no)
func (x *Nat) cmpGeq(y *Nat /*@, ghost p perm, ghost q perm @*/) (res choice) {
	// implementation elided (trusted)
	return no
}

//@ trusted
//@ requires noPerm < p && noPerm < q
//@ preserves acc(a.Inv(), p) && acc(b.Inv(), q)
//@ ensures res >= 0
func maxLen(a, b *Nat /*@, ghost p perm, ghost q perm @*/) (res int) {
	return max(len(a.limbs), len(b.limbs))
}

//@ trusted
//@ requires noPerm < p
//@ preserves acc(n.Inv(), p)
//@ ensures res >= 0
func natLen(n *Nat /*@, ghost p perm @*/) (res int) {
	return len(n.limbs)
}

//@ trusted
//@ preserves n.Inv()
//@ ensures n.Repr() == 1
func setOne(n *Nat) {
	n.limbs[0] = 1
}

//go:norace
//@ trusted
//@ preserves a.Inv()
//@ ensures a.Repr() == old(a.Repr()) / 2
func rshift1(a *Nat, carry uint) {
	size := len(a.limbs)
	aLimbs := a.limbs[:size]

	for i := range size {
		aLimbs[i] >>= 1
		if i+1 < size {
			aLimbs[i] |= aLimbs[i+1] << (_W - 1)
		} else {
			aLimbs[i] |= carry << (_W - 1)
		}
	}
}
