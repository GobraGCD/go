package bigmod

import (
	"errors"
	"math/bits"
)

const (
	// _W is the size in bits of our limbs.
	_W = bits.UintSize
	// _S is the size in bytes of our limbs.
	_S = _W / 8
)

// choice represents a constant-time boolean. The value of choice is always
// either 1 or 0. We use an int instead of bool in order to make decisions in
// constant time by turning it into a mask.
type choice uint

//@ trusted
//@ requires c.isValid()
//@ ensures  r.isValid() && r.Repr() == !c.Repr()
//@ decreases
//@ pure
func not(c choice) (r choice) {
	return 1 ^ c
}

//@ trusted // trusted because Gobra does not yet reason about bitwise operations
//@ requires a.isValid() && b.isValid()
//@ ensures  r.isValid() && r.Repr() == (a.Repr() || b.Repr())
//@ decreases
//@ pure
func or(a, b choice) (r choice) {
	return a | b
}

const yes = choice(1)
const no = choice(0)

type Nat struct {
	// limbs is little-endian in base 2^W with W = bits.UintSize.
	limbs []uint
}


// preallocTarget is the size in bits of the numbers used to implement the most
// common and most performant RSA key size. It's also enough to cover some of
// the operations of key sizes up to 4096.
const preallocTarget = 2048
const preallocLimbs = (preallocTarget + _W - 1) / _W

// NewNat returns a new nat with a size of zero, just like new(Nat), but with
// the preallocated capacity to hold a number of up to preallocTarget bits.
// NewNat inlines, so the allocation can live on the stack.
//@ ensures n.Inv()
//@ ensures n.Repr() == 0 && n.AnnouncedLen() == 0
func NewNat() (n *Nat) {
	limbs := make([]uint, 0, preallocLimbs)
	n = &Nat{limbs}
	//@ fold n.Inv()
	//@ assert reveal n.AnnouncedLen() == 0
	//@ assert reveal exp(2, 0) == 1
	return n
}

// expand expands x to n limbs, leaving its value unchanged.
//@ trusted
//@ requires x.Inv() && x.AnnouncedLen() <= n
//@ ensures  x.Inv()
//@ ensures  x.AnnouncedLen() == n
//@ ensures  x.Repr() == old(x.Repr())
func (x *Nat) expand(n int) *Nat {
	//@ assert reveal x.AnnouncedLen() <= n
	//@ xRepr := x.Repr()
	//@ reveal x.Repr()
	//@ unfold x.Inv()
	if len(x.limbs) > n {
		panic("bigmod: internal error: shrinking nat")
	}
	if cap(x.limbs) < n {
		newLimbs := make([]uint, n)
		copy(newLimbs, x.limbs /*@, perm(1/2) @*/)
		//@ equalLimbsRepr(x.limbs, newLimbs, perm(1/2))
		x.limbs = newLimbs
		//@ fold x.Inv()
		//@ assert reveal x.AnnouncedLen() == n
		//@ assert reveal x.Repr() == xRepr
		return x
	}
	// Note: this branch does not verify yet
	extraLimbs := x.limbs[len(x.limbs):n]
	clear(extraLimbs)
	x.limbs = x.limbs[:n]
	//@ fold x.Inv()
	//@ assert reveal x.AnnouncedLen() == n
	//@ assert reveal x.Repr() == xRepr
	return x
}

// reset returns a zero nat of n limbs, reusing x's storage if n <= cap(x.limbs).
//@ trusted
//@ requires  0 <= n
//@ preserves x.Inv()
//@ ensures   x == res
//@ ensures   x.Repr() == 0
//@ ensures   x.AnnouncedLen() == n
func (x *Nat) reset(n int) (res *Nat) {
	//@ reveal x.Repr()
	//@ unfold x.Inv()
	if cap(x.limbs) < n {
		x.limbs = make([]uint, n)
		//@ equalLimbsRepr([]uint{}, x.limbs, perm(1/2))
		//@ fold x.Inv()
		//@ assert reveal x.AnnouncedLen() == n
		//@ assert reveal x.Repr() == 0
		return x
	}
	clear(x.limbs)
	//@ equalLimbsRepr([]uint{}, x.limbs, perm(1/2))
	// Note: this branch does not verify yet
	x.limbs = x.limbs[:n]
	//@ fold x.Inv()
	//@ assert reveal x.AnnouncedLen() == n
	//@ assert reveal x.Repr() == 0
	return x
}

// "set" is unfortunately a keyword in Gobra so we use "setNat" instead.
// set assigns x = y, optionally resizing x to the appropriate size.
//@ requires  noPerm < p
//@ preserves x.Inv() && acc(y.Inv(), p)
//@ ensures   r == x
//@ ensures   x.Repr() == y.Repr()
//@ ensures   x.AnnouncedLen() == y.AnnouncedLen()
func (x *Nat) setNat(y *Nat /*@, ghost p perm @*/) (r *Nat) {
	//@ reveal y.AnnouncedLen()
	//@ unfold acc(y.Inv(), p/2)
	x.reset(len(y.limbs))
	//@ reveal x.AnnouncedLen()
	//@ unfold x.Inv()
	copy(x.limbs, y.limbs /*@, p/4 @*/)
	//@ equalLimbsRepr(x.limbs, y.limbs, p/4)
	//@ fold x.Inv()
	//@ fold acc(y.Inv(), p/2)
	//@ assert reveal x.Repr() == reveal y.Repr()
	//@ assert reveal x.AnnouncedLen() == reveal y.AnnouncedLen()
	return x
}

// IsZero returns 1 if x == 0, and 0 otherwise.
//
//go:norace
//@ trusted
//@ requires  noPerm < p
//@ preserves acc(x.Inv(), p)
//@ ensures   res == (x.Repr() == 0 ? yes : no)
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

// IsOne returns 1 if x == 1, and 0 otherwise.
//
//go:norace
//@ trusted
//@ requires  noPerm < p
//@ preserves acc(x.Inv(), p)
//@ ensures   res == (x.Repr() == 1 ? yes : no)
func (x *Nat) IsOne(/*@ ghost p perm @*/) (res choice) {
	// Eliminate bounds checks in the loop.
	size := len(x.limbs)
	xLimbs := x.limbs[:size]

	if len(xLimbs) == 0 {
		return no
	}

	one := ctEq(xLimbs[0], 1)
	for i := 1; i < size; i++ {
		one &= ctEq(xLimbs[i], 0)
	}
	return one
}

// IsOdd returns 1 if x is odd, and 0 otherwise.
//@ trusted
//@ requires  noPerm < p
//@ preserves acc(x.Inv(), p)
//@ ensures   res == (x.Repr() % 2 == 1 ? yes : no)
func (x *Nat) IsOdd(/*@ ghost p perm @*/) (res choice) {
	if len(x.limbs) == 0 {
		return no
	}
	return choice(x.limbs[0] & 1)
}

// assign sets x <- y if on == 1, and does nothing otherwise.
//
// Both operands must have the same announced length.
//
//go:norace
//@ trusted
//@ requires noPerm < p
//@ requires x.Inv() && acc(y.Inv(), p)
//@ requires x.AnnouncedLen() == y.AnnouncedLen()
//@ requires on.isValid()
//@ ensures  r == x
//@ ensures  x.Inv() && acc(y.Inv(), p)
//@ ensures  x.Repr() == (on.Repr() ? y.Repr() : old(x.Repr()))
//@ ensures  x.AnnouncedLen() == old(x.AnnouncedLen())
func (x *Nat) assign(on choice, y *Nat /*@, ghost p perm @*/) (r *Nat) {
	// Eliminate bounds checks in the loop.
	size := len(x.limbs)
	xLimbs := x.limbs[:size]
	yLimbs := y.limbs[:size]

	mask := ctMask(on)
	for i := 0; i < size; i++ {
		xLimbs[i] ^= mask & (xLimbs[i] ^ yLimbs[i])
	}
	return x
}

// add computes x += y and returns the carry.
//
// Both operands must have the same announced length.
//
//go:norace
//@ trusted
//@ requires noPerm < p
//@ requires x.Inv() && acc(y.Inv(), p)
//@ requires x.AnnouncedLen() == y.AnnouncedLen()
//@ ensures  x.Inv() && acc(y.Inv(), p)
//@ ensures  x.AnnouncedLen() == old(x.AnnouncedLen())
//@ ensures  0 <= c && c <= 1
//@ ensures  c == 0 ==> x.Repr() == old(x.Repr()) + y.Repr()
//@ ensures  c == 1 ==> x.Repr() == old(x.Repr()) + y.Repr() - old(x.ValCount())
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
//@ requires x.Inv() && acc(y.Inv(), p)
//@ requires x.AnnouncedLen() == y.AnnouncedLen()
//@ ensures  x.Inv() && acc(y.Inv(), p)
//@ ensures  x.AnnouncedLen() == old(x.AnnouncedLen())
//@ ensures  0 <= c && c <= 1
//@ ensures  c == 0 ==> old(x.Repr()) >= y.Repr() && x.Repr() == old(x.Repr()) - y.Repr()
//@ ensures  c == 1 ==> old(x.Repr()) < y.Repr() && x.Repr() == old(x.Repr()) - y.Repr() + old(x.ValCount())
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

	//@ ghost natOnly bool
}

// maybeSubtractModulus computes x -= m if and only if x >= m or if "always" is yes.
//
// It can be used to reduce modulo m a value up to 2m - 1, which is a common
// range for results computed by higher level operations.
//
// always is usually a carry that indicates that the operation that produced x
// overflowed its size, meaning abstractly x > 2^_W*n > m even if x < m.
//
// x and m operands must have the same announced length.
//
//go:norace
//@ requires noPerm < p
//@ requires x.Inv() && acc(m.Inv(), p)
//@ requires x.Repr() < 2*m.Repr()
//@ requires x.AnnouncedLen() == m.AnnouncedLen()
//@ requires always.isValid()
//@ ensures  x.Inv() && acc(m.Inv(), p)
//@ ensures  0 < m.Repr() // this is a direct consequence of the precondition but required to make `_ % m.Repr()` well-defined
//@ ensures  always.Repr() ?
//@		x.Repr() == (old(x.Repr()) >= m.Repr() ? old(x.Repr()) - m.Repr() : old(x.Repr()) - m.Repr() + x.ValCount()) :
//@		x.Repr() == old(x.Repr()) % m.Repr()
//@ ensures  x.AnnouncedLen() == old(x.AnnouncedLen())
func (x *Nat) maybeSubtractModulus(always choice, m *Modulus /*@, ghost p perm @*/) {
	t := NewNat().setNat(x /*@, 1/2 @*/)
	assert t.Repr() == x.Repr() && t.AnnouncedLen() == x.AnnouncedLen()
	//@ unfold acc(m.Inv(), p)
	underflow := t.sub(m.nat /*@, p/2 @*/)
	//@ fold acc(m.Inv(), p)
	// We keep the result if x - m didn't underflow (meaning x >= m)
	// or if always was set.
	keep := or(not(choice(underflow)), choice(always))
	x.assign(keep, t /*@, 1/2 @*/)
}

// Add computes x = x + y mod m.
//
// The length of both operands must be the same as the modulus. Both operands
// must already be reduced modulo m.
//
//go:norace
//@ requires noPerm < p && noPerm < q
//@ requires x.Inv() && acc(y.Inv(), p) && acc(m.Inv(), q)
//@ requires x.AnnouncedLen() == m.AnnouncedLen() && y.AnnouncedLen() == m.AnnouncedLen()
//@ requires 0 <= x.Repr() && x.Repr() < m.Repr()
//@ requires 0 <= y.Repr() && y.Repr() < m.Repr()
//@ ensures  r == x
//@ ensures  x.Inv() && acc(y.Inv(), p) && acc(m.Inv(), q)
//@ ensures  0 <= x.Repr() && x.Repr() < m.Repr()
//@ ensures  x.Repr() == (old(x.Repr()) + y.Repr()) % m.Repr()
func (x *Nat) Add(y *Nat, m *Modulus /*@, ghost p, q perm @*/) (r *Nat) {
	overflow := x.add(y /*@, p/2 @*/)
	x.maybeSubtractModulus(choice(overflow), m /*@, q/2 @*/)
	return x
}

// InverseVarTime calculates x = a⁻¹ mod m and returns (x, true) if a is
// invertible. Otherwise, InverseVarTime returns (x, false) and x is not
// modified.
//
// a must be reduced modulo m, but doesn't need to have the same size. The
// output will be resized to the size of m and overwritten.
//
//go:norace
//@ requires noPerm < p && p <= writePerm
//@ requires x.Inv() && acc(a.Inv(), p) && acc(m.Inv(), p)
//@ requires a.Repr() < m.Repr() // a must be reduced modulo m
//@ ensures  x.Inv() && acc(a.Inv(), p) && acc(m.Inv(), p)
//@ ensures  r == x
//@ ensures  ok ==> gcd(a.Repr(), m.Repr()) == x.Repr() * a.Repr() - BRepr * m.Repr()
//@ ensures  ok ==> x.AnnouncedLen() == m.AnnouncedLen()
//@ ensures !ok ==> x.Repr() == old(x.Repr()) && x.AnnouncedLen() == old(x.AnnouncedLen()) // x is not modified on failure
func (x *Nat) InverseVarTime(a *Nat, m *Modulus /*@, ghost p perm @*/) (r *Nat, ok bool /*@, ghost BRepr uint @*/) {
	//@ unfold acc(m.Inv(), p/2)
	u, A, err /*@, BRepr @*/ := extendedGCD(a, m.nat /*@, p/4 @*/)
	//@ fold acc(m.Inv(), p/2)
	if err != nil {
		return x, false /*@, BRepr @*/
	}
	if u.IsOne(/*@ p/2 @*/) == no {
		return x, false /*@, BRepr @*/
	}
	return x.setNat(A /*@, 1/2 @*/), true /*@, BRepr @*/
}

// GCDVarTime calculates x = GCD(a, b) where at least one of a or b is odd, and
// both are non-zero. If GCDVarTime returns an error, x is not modified.
//
// The output will be resized to the size of the larger of a and b.
//@ requires noPerm < p && p <= writePerm
//@ requires x.Inv() && acc(a.Inv(), p) && acc(b.Inv(), p)
//@ requires a.Repr() % 2 == 1 || b.Repr() % 2 == 1 // at least one of a or b is odd
//@ requires a.Repr() != 0 && b.Repr() != 0 // both a and b are non-zero
//@ ensures  x.Inv() && acc(a.Inv(), p) && acc(b.Inv(), p)
//@ ensures  err == nil ==> r == x
//@ ensures  err == nil ==> x.Repr() == gcd(a.Repr(), b.Repr())
//@ ensures  err != nil ==> x.Repr() == old(x.Repr()) && x.AnnouncedLen() == old(x.AnnouncedLen()) // x is not modified on failure
func (x *Nat) GCDVarTime(a, b *Nat /*@, ghost p perm @*/) (r *Nat, err error) {
	// bug: we cannot simply invoke `extendedGCD` due to its
	// preconditions!
	// TODO: if a.Equal(b) == yes
	u, _, err /*@, BRepr @*/ := extendedGCD(a, b /*@, p @*/)
	if err != nil {
		return nil, err
	}
	return x.setNat(u /*@, 1/2 @*/), nil
}

// syncAdd adds Y to X and W to Z, then subtracts bound1 from X and bound2 from Z
// if the mathematical sum X+Y >= bound1. This is synchronized single-subtraction
// modular reduction: X = (X + Y) mod bound1, with Z tracking the same wrap/no-wrap.
//
// Internally, the add may overflow the limb representation (when X+Y >= 2^(_W*len)),
// but the subsequent conditional subtraction corrects for this. The carry from add
// is used to detect overflow: if carry == 1 || X >= bound1, we subtract.
// In the overflow+borrow case, ValCount cancels: X+Y-VC-bound1+VC = X+Y-bound1.
//
// The ghost parameters U, V, A, B, C, D represent the relational
// context from the extended GCD loop. syncAdd proves the synchronized
// wrap/no-wrap property internally via AC_ge_BD_ge / AC_lt_BD_le, and
// maintains nonLinearSub through the addition.
//
//go:norace
//@ requires noPerm < p && p <= writePerm
//@ requires X.Inv() && Z.Inv()
//@ requires acc(Y.Inv(), p) && acc(W.Inv(), p)
//@ requires acc(bound1.Inv(), p) && acc(bound2.Inv(), p)
//@ requires X.AnnouncedLen() == Y.AnnouncedLen() && X.AnnouncedLen() == bound1.AnnouncedLen()
//@ requires Z.AnnouncedLen() == W.AnnouncedLen() && Z.AnnouncedLen() == bound2.AnnouncedLen()
//@ requires X.Repr() < bound1.Repr() && Y.Repr() < bound1.Repr() // sum < 2*bound1
//@ requires Z.Repr() <= bound2.Repr() && W.Repr() <= bound2.Repr() // sum <= 2*bound2
// Ghost relational preconditions:
//@ requires A + C == X.Repr() + Y.Repr()
//@ requires B + D == Z.Repr() + W.Repr()
//@ requires nonLinearSub(U, A, B, bound2.Repr(), bound1.Repr())
//@ requires nonLinearSub(V, D, C, bound1.Repr(), bound2.Repr())
//@ requires 0 < U && U <= bound2.Repr()
//@ requires 0 <= V && V <= bound1.Repr()
//@ requires 0 < bound2.Repr() && bound2.Repr() < bound1.Repr()
//@ requires 0 <= A && A < bound1.Repr()
//@ requires 0 <= C && C < bound1.Repr()
//@ requires 0 <= B && B <= bound2.Repr()
//@ requires 0 <= D && D <= bound2.Repr()
//@ ensures  X.Inv() && Z.Inv()
//@ ensures  acc(Y.Inv(), p) && acc(W.Inv(), p)
//@ ensures  acc(bound1.Inv(), p) && acc(bound2.Inv(), p)
//@ ensures  X.AnnouncedLen() == old(X.AnnouncedLen())
//@ ensures  Z.AnnouncedLen() == old(Z.AnnouncedLen())
//@ ensures  old(X.Repr()) + Y.Repr() <  bound1.Repr() ==> X.Repr() == old(X.Repr()) + Y.Repr()
//@ ensures  old(X.Repr()) + Y.Repr() >= bound1.Repr() ==> X.Repr() == old(X.Repr()) + Y.Repr() - bound1.Repr()
//@ ensures  old(X.Repr()) + Y.Repr() <  bound1.Repr() ==> Z.Repr() == old(Z.Repr()) + W.Repr()
//@ ensures  old(X.Repr()) + Y.Repr() >= bound1.Repr() ==> Z.Repr() == old(Z.Repr()) + W.Repr() - bound2.Repr()
// Ghost relational postconditions:
//@ ensures  nonLinearSub(U - V, X.Repr(), Z.Repr(), bound2.Repr(), bound1.Repr())
//@ ensures  nonLinearSub(V - U, Z.Repr(), X.Repr(), bound1.Repr(), bound2.Repr())
// Sync facts (for range reasoning at call sites):
//@ ensures  old(X.Repr()) + Y.Repr() <  bound1.Repr() ==> old(Z.Repr()) + W.Repr() <= bound2.Repr()
//@ ensures  old(X.Repr()) + Y.Repr() >= bound1.Repr() ==> old(Z.Repr()) + W.Repr() >= bound2.Repr()
func syncAdd(X, Y, Z, W, bound1, bound2 *Nat /*@, ghost U, V, A, B, C, D uint, ghost p perm @*/) {
	// Establish sync preconditions from nonLinearSub via AC_ge_BD_ge / AC_lt_BD_le:
	/*@
	ghost if A + C >= bound1.Repr() {
		AC_ge_BD_ge(U, V, A, B, C, D, bound2.Repr(), bound1.Repr())
	} else {
		AC_lt_BD_le(U, V, A, B, C, D, bound2.Repr(), bound1.Repr())
	}
	@*/

	c := X.add(Y /*@, p / 2 @*/)
	Z.add(W /*@, p / 2 @*/)
	// After add: X.Repr() is either xOld+Y (c==0) or xOld+Y-VC (c==1).
	// Z.Repr() is either zOld+W (no overflow) or zOld+W-VC_Z (overflow).

	if choice(c) == yes || X.cmpGeq(bound1 /*@, p / 2 @*/) == yes {
		// We enter here when xOld + Y >= bound1.
		// Case c==1: add overflowed, so xOld+Y >= VC > bound1.
		// Case c==0, cmpGeq==yes: X.Repr() = xOld+Y >= bound1.
		//@ assert old(X.Repr()) + Y.Repr() >= bound1.Repr()
		// From sync property (proven by AC_ge_BD_ge above):
		//@ assert old(Z.Repr()) + W.Repr() >= bound2.Repr()

		X.sub(bound1 /*@, p / 2 @*/)
		Z.sub(bound2 /*@, p / 2 @*/)
		// For X: both sub-cases yield xOld + Y - bound1:
		//   c==0: X = xOld+Y - bound1 (no borrow, since xOld+Y >= bound1)
		//   c==1: X = (xOld+Y-VC) - bound1 + VC = xOld+Y-bound1 (borrow, VC cancels)
		// For Z: same double-wrap cancellation applies:
		//   Z.add didn't overflow: Z_after_add = zOld+W >= bound2, sub gives zOld+W-bound2.
		//   Z.add overflowed: Z_after_add = zOld+W-VC < bound2 (since zOld+W <= 2*bound2, VC > bound2),
		//     sub borrows: zOld+W-VC-bound2+VC = zOld+W-bound2.
	}

	// Prove nonLinearSub postconditions:
	// subExpandLemma: U - V = (A + C) * bound2 - (B + D) * bound1
	//@ subExpandLemma(U, V, A, B, C, D, bound2.Repr(), bound1.Repr())
	// In the wrap case, modAddLemma bridges:
	//   (A + C) * bound2 - (B + D) * bound1 = X.Repr() * bound2 - Z.Repr() * bound1
	// In the no-wrap case, X.Repr() = A + C and Z.Repr() = B + D, so the equation holds trivially.
	/*@
	ghost if old(X.Repr()) + Y.Repr() >= bound1.Repr() {
		modAddLemma(A, B, C, D, X.Repr(), Z.Repr(), bound2.Repr(), bound1.Repr())
	}
	@*/
	//@ assert reveal nonLinearSub(U - V, X.Repr(), Z.Repr(), bound2.Repr(), bound1.Repr())
	//@ assert reveal nonLinearSub(V - U, Z.Repr(), X.Repr(), bound1.Repr(), bound2.Repr())
}

// extendedGCD computes u and A such that u = GCD(a, m) and u = A*a - B*m.
//
// u will have the size of the larger of a and m, and A will have the size of m.
//
// It is an error if either a or m is zero, or if they are both even.
//@ requires noPerm < p && p <= writePerm
//@ requires acc(a.Inv(), p) && acc(m.Inv(), p)
//@ requires a.Repr() < m.Repr() // TODO move this into the function
//@ ensures  acc(a.Inv(), p) && acc(m.Inv(), p)
//@ ensures  err == nil ==> u.Inv() && A.Inv()
//@ ensures  err == nil ==> u.Repr() == gcd(a.Repr(), m.Repr())
//@ ensures  err == nil ==> u.Repr() == A.Repr() * a.Repr() - BRepr * m.Repr()
//@ ensures  err == nil ==> u.AnnouncedLen() == gmax(a.AnnouncedLen(), m.AnnouncedLen())
//@ ensures  err == nil ==> A.AnnouncedLen() == m.AnnouncedLen()
func extendedGCD(a, m *Nat /*@, ghost p perm @*/) (u, A *Nat, err error /*@, ghost BRepr uint @*/) {
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

	// TODO: we need a lemma that gives us the fact that !m.IsZero ==> m.AnnouncedLen() > 0
	assume m.AnnouncedLen() > 0
	assume a.AnnouncedLen() > 0
	//@ assert 0 < a.Repr() && 0 < m.Repr()
	//@ assert a.Repr() % 2 != 0 || m.Repr() % 2 != 0

	size := maxLen(a, m /*@, p / 2 @*/)
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
	mMod := &Modulus{nat: m}
	//@ mMod.natOnly = true
	//@ fold acc(mMod.Inv(), p/2)
	aMod := &Modulus{nat: a}
	//@ aMod.natOnly = true
	//@ fold acc(aMod.Inv(), p/2)

	// Establish relational invariants:
	// u = a = 1*a - 0*m, so nonLinearSub(a, 1, 0, a, m) holds.
	// v = m = 1*m - 0*a, so nonLinearSub(m, 1, 0, m, a) holds.
	//@ assert reveal nonLinearSub(u.Repr(), A.Repr(), B.Repr(), a.Repr(), m.Repr())
	//@ assert reveal nonLinearSub(v.Repr(), D.Repr(), C.Repr(), m.Repr(), a.Repr())

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
	// Permissions & sizes:
	//@ invariant acc(m.Inv(), p/2) && 0 < m.AnnouncedLen()
	//@ invariant acc(a.Inv(), p/2) && 0 < a.AnnouncedLen()
	//@ invariant size == gmax(a.AnnouncedLen(), m.AnnouncedLen())
	//@ invariant u.Inv() && u.AnnouncedLen() == size
	//@ invariant v.Inv() && v.AnnouncedLen() == size
	//@ invariant A.Inv() && A.AnnouncedLen() == m.AnnouncedLen()
	//@ invariant B.Inv() && B.AnnouncedLen() == a.AnnouncedLen()
	//@ invariant C.Inv() && C.AnnouncedLen() == m.AnnouncedLen()
	//@ invariant D.Inv() && D.AnnouncedLen() == a.AnnouncedLen()
	//@ invariant acc(mMod.Inv(), p/2) && mMod.IsNatOnly()
	//@ invariant acc(aMod.Inv(), p/2) && aMod.IsNatOnly()
	// Bounds:
	//@ invariant 0 < a.Repr() && 0 < m.Repr()
	//@ invariant mMod.Repr() == m.Repr() && aMod.Repr() == a.Repr()
	//@ invariant a.Repr() < m.Repr()
	//@ invariant 0 < u.Repr() && u.Repr() <= a.Repr() // range for u
	//@ invariant 0 <= v.Repr() && v.Repr() <= m.Repr() // range for v
	//@ invariant 0 <= A.Repr() && A.Repr() < m.Repr() // range for A
	//@ invariant 0 <= B.Repr() && B.Repr() < a.Repr() // range for B; stronger than fiat-crypto's B ≤ a
	//@ invariant 0 <= C.Repr() && C.Repr() < m.Repr() // range for C
	//@ invariant 0 <= D.Repr() && D.Repr() <= a.Repr() // range for D
	// Parity: at least one of a,m is odd:
	//@ invariant a.Repr() % 2 == 1 || m.Repr() % 2 == 1
	// Parity: at least one of u,v is odd (since gcd is odd).
	//@ invariant u.Repr() % 2 == 1 || v.Repr() % 2 == 1
	//@ invariant gcd(u.Repr(), v.Repr()) == gcd(a.Repr(), m.Repr())
	// Relational invariants (abstract to avoid NIA):
	//@ invariant nonLinearSub(u.Repr(), A.Repr(), B.Repr(), a.Repr(), m.Repr())
	//@ invariant nonLinearSub(v.Repr(), D.Repr(), C.Repr(), m.Repr(), a.Repr())
	//@ decreases u.Repr() + v.Repr()
	for {
		// If both u and v are odd, subtract the smaller from the larger.
		// If u = v, we need to subtract from v to hit the modified exit condition.
		if u.IsOdd(/*@ p / 2 @*/) == yes && v.IsOdd(/*@ p / 2 @*/) == yes {
			if v.cmpGeq(u /*@, p / 4 @*/) == no {
				//@ preU := u.Repr()
				u.sub(v /*@, p / 2 @*/)
				//@ gcdSubLemma(preU, v.Repr())
				syncAdd(A, C, B, D, m, a /*@, preU, v.Repr(), A.Repr(), B.Repr(), C.Repr(), D.Repr(), p / 4 @*/)
			} else {
				//@ preV := v.Repr()
				v.sub(u /*@, p / 2 @*/)
				//@ gcdSubLemma2(u.Repr(), preV)
				syncAdd(C, A, D, B, m, a /*@, u.Repr(), preV, A.Repr(), B.Repr(), C.Repr(), D.Repr(), p / 4 @*/)
			}
		}

		// Exactly one of u and v is now even.
		if u.IsOdd(/*@ p / 2 @*/) == v.IsOdd(/*@ p / 2 @*/) {
			// this branch is unreachable -- good!
			panic("bigmod: internal error: u and v are not in the expected state")
		}

		// Halve the even one and adjust the corresponding coefficient.
		if u.IsOdd(/*@ p / 2 @*/) == no {
			//@ preU := u.Repr()
			rshift1(u, 0)
			//@ gcdHalfLemma(preU, v.Repr())
			if A.IsOdd(/*@ p / 2 @*/) == yes || B.IsOdd(/*@ p / 2 @*/) == yes {
				//@ parityLemma(preU, A.Repr(), B.Repr(), a.Repr(), m.Repr())
				rshift1(A, A.add(m /*@, p / 4 @*/))
				rshift1(B, B.add(a /*@, p / 4 @*/))
				//@ halvRelLemmaU2(u.Repr(), A.Repr(), B.Repr(), a.Repr(), m.Repr())
			} else {
				rshift1(A, 0)
				rshift1(B, 0)
				//@ halvRelLemmaU1(u.Repr(), A.Repr(), B.Repr(), a.Repr(), m.Repr())
			}
		} else { // v.IsOdd() == no
			//@ preV := v.Repr()
			rshift1(v, 0)
			//@ gcdHalfLemma2(u.Repr(), preV)
			if C.IsOdd(/*@ p / 2 @*/) == yes || D.IsOdd(/*@ p / 2 @*/) == yes {
				//@ parityLemmaV(preV, C.Repr(), D.Repr(), a.Repr(), m.Repr())
				rshift1(C, C.add(m /*@, p / 4 @*/))
				rshift1(D, D.add(a /*@, p / 4 @*/))
				//@ halvRelLemmaV2(v.Repr(), C.Repr(), D.Repr(), a.Repr(), m.Repr())
			} else {
				rshift1(C, 0)
				rshift1(D, 0)
				//@ halvRelLemmaV1(v.Repr(), C.Repr(), D.Repr(), a.Repr(), m.Repr())
			}
		}

		if v.IsZero(/*@ p / 2 @*/) == yes {
			// v == 0, so gcd(u, 0) == u (base case of gcd)
			//@ gcdBaseLemma(u.Repr())
			// Open the opaque relational invariant to get the actual equation
			// for the postcondition: u = A*a - B*m.
			//@ assert reveal nonLinearSub(u.Repr(), A.Repr(), B.Repr(), a.Repr(), m.Repr())
			//@ unfold acc(mMod.Inv(), p/2)
			//@ unfold acc(aMod.Inv(), p/2)
			return u, A, nil /*@, B.Repr() @*/
		}
	}
}

// cmpGeq returns 1 if x >= y, and 0 otherwise.
//
// Both operands must have the same announced length.
//
//go:norace
//@ trusted
//@ requires noPerm < p
//@ requires acc(x.Inv(), p) && acc(y.Inv(), p)
//@ requires x.AnnouncedLen() == y.AnnouncedLen()
//@ ensures  acc(x.Inv(), p) && acc(y.Inv(), p)
//@ ensures  res == (x.Repr() >= y.Repr() ? yes : no)
func (x *Nat) cmpGeq(y *Nat /*@, ghost p perm @*/) (res choice) {
	// Eliminate bounds checks in the loop.
	size := len(x.limbs)
	xLimbs := x.limbs[:size]
	yLimbs := y.limbs[:size]

	var c uint
	for i := 0; i < size; i++ {
		_, c = bits.Sub(xLimbs[i], yLimbs[i], c)
	}
	// If there was a carry, then subtracting y underflowed, so
	// x is not greater than or equal to y.
	return not(choice(c))
}

//@ requires  noPerm < p
//@ preserves acc(a.Inv(), p) && acc(b.Inv(), p)
//@ ensures   res == gmax(a.AnnouncedLen(), b.AnnouncedLen())
func maxLen(a, b *Nat /*@, ghost p perm @*/) (res int) {
	//@ unfold acc(a.Inv(), p/2)
	//@ unfold acc(b.Inv(), p/2)
	res = max(len(a.limbs), len(b.limbs))
	//@ fold acc(b.Inv(), p/2)
	//@ fold acc(a.Inv(), p/2)
	//@ assert res == gmax(reveal a.AnnouncedLen(), reveal b.AnnouncedLen())
	return
}

//@ requires  noPerm < p
//@ preserves acc(n.Inv(), p)
//@ ensures   res == n.AnnouncedLen()
func natLen(n *Nat /*@, ghost p perm @*/) (res int) {
	//@ unfold acc(n.Inv(), p/2)
	res = len(n.limbs)
	//@ fold acc(n.Inv(), p/2)
	//@ assert res == reveal n.AnnouncedLen()
	return
}

//@ trusted // TODO: can we verify this?
//@ preserves n.Inv()
//@ ensures   n.Repr() == 1
//@ ensures   n.AnnouncedLen() == gmax(1, old(n.AnnouncedLen()))
func setOne(n *Nat) {
	n.reset(max(1, natLen(n /*@, 1/2 @*/)))
	//@ unfold n.Inv()
	n.limbs[0] = 1
	//@ fold n.Inv()
}

//go:norace
//@ trusted
//@ requires 0 <= carry && carry <= 1
//@ requires a.Inv()
//@ ensures  a.Inv()
//@ ensures  carry == 0 ==> a.Repr() == old(a.Repr()) / 2
//@ ensures  carry == 1 ==> a.Repr() == (old(a.Repr()) + old(a.ValCount())) / 2
//@ ensures  a.AnnouncedLen() == old(a.AnnouncedLen())
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
