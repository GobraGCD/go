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

/*@
ghost
decreases
pure func (c choice) isValid() bool {
	return c == yes || c == no
}

ghost
requires c.isValid()
decreases
pure func (c choice) Repr() bool {
	return c == yes
}
@*/

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

/*@
pred (n *Nat) Inv() {
    acc(n) &&
	(forall j int :: { &n.limbs[j] } 0 <= j && j < cap(n.limbs) ==> acc(&n.limbs[j]))
}

ghost
opaque
requires acc(n.Inv(), _)
ensures  0 <= res
decreases
pure func (n *Nat) AnnouncedLen() (res int) {
	return unfolding acc(n.Inv(), _) in len(n.limbs)
}

ghost
requires acc(n.Inv(), _)
decreases
// The number of values representable by n's limbs.
pure func (n *Nat) ValCount() (res uint) {
	return unfolding acc(n.Inv(), _) in exp(2, _W * n.AnnouncedLen())
}

ghost
opaque
requires acc(n.Inv(), _)
ensures  0 <= res && res < n.ValCount()
decreases
pure func (n *Nat) Repr() (res uint) {
	// TODO: is it a good idea to reveal within a pure function?
	return let _ := reveal n.AnnouncedLen() in
		unfolding acc(n.Inv(), _) in limbsRepr(n.limbs)
}

ghost
requires acc(limbs, _)
ensures  0 <= res && res < exp(2, _W * len(limbs))
decreases
pure func limbsRepr(limbs []uint) (res uint) {
	return limbsReprHelperLemma(limbs, 0)
}

ghost
ensures 0 <= i && i < exp(2, _W) && r == i
decreases
// we have to axiomatize the range of `uint` as this is currently not
// supported by Gobra
pure func uintRange(i uint) (r uint)

ghost
requires acc(limbs, _) && 0 <= idx && idx <= len(limbs)
decreases len(limbs) - idx
pure func limbsReprHelper(limbs []uint, idx int) (res uint) {
	return idx == len(limbs) ? 0 : uintRange(limbs[idx]) + exp(2, _W) * limbsReprHelper(limbs, idx + 1)
}

ghost
requires acc(limbs, _) && 0 <= idx && idx <= len(limbs)
ensures  res == limbsReprHelper(limbs, idx)
ensures  0 <= res && res < exp(2, _W * (len(limbs) - idx))
decreases len(limbs) - idx
pure func limbsReprHelperLemma(limbs []uint, idx int) (res uint) {
    return let res := limbsReprHelper(limbs, idx) in
        idx == len(limbs) ? res :
            // prove for else branch
            let prev_res := limbsReprHelperLemma(limbs, idx + 1) in
            let _ := mulLtLemma(prev_res, len(limbs) - idx) in
            res
}

ghost
decreases
requires 0 < diff
requires a <= exp(2, _W * (diff - 1)) - 1
ensures  exp(2, _W) * a <= exp(2, _W * diff) - exp(2, _W)
pure func mulLtLemma(a uint, diff int) bool {
    return let _ := mulIeqLemma(a, exp(2, _W * (diff - 1)) - 1, exp(2, _W)) in
    let _ := expLemma(2, _W, _W * (diff - 1)) in
    true
}

ghost
requires a <= b && 0 <= c
ensures  c * a <= c * b
decreases
pure func mulIeqLemma(a, b, c uint) bool {
    return true
}

ghost
requires noPerm < p
requires acc(limbs1, p) && acc(limbs2, p)
requires len(limbs1) <= len(limbs2)
requires forall j int :: { limbs1[j], limbs2[j] } 0 <= j && j < len(limbs1) ==> limbs1[j] == limbs2[j]
requires forall j int :: { limbs2[j] } len(limbs1) <= j && j < len(limbs2) ==> limbs2[j] == 0
ensures  acc(limbs1, p) && acc(limbs2, p)
ensures  limbsRepr(limbs1) == limbsRepr(limbs2)
decreases
func equalLimbsRepr(limbs1, limbs2 []uint, p perm) {
    equalLimbsReprHelper(limbs1, limbs2, 0, p)
}

ghost
requires noPerm < p
requires 0 <= idx && idx <= len(limbs2)
requires acc(limbs1, p) && acc(limbs2, p)
requires len(limbs1) <= len(limbs2)
requires forall j int :: { limbs1[j], limbs2[j] } idx <= j && j < len(limbs1) ==> limbs1[j] == limbs2[j]
requires forall j int :: { limbs2[j] } len(limbs1) <= j && j < len(limbs2) ==> limbs2[j] == 0
ensures  acc(limbs1, p) && acc(limbs2, p)
ensures  idx <= len(limbs1) ==> limbsReprHelper(limbs1, idx) == limbsReprHelper(limbs2, idx)
ensures  len(limbs1) <= idx ==> limbsReprHelper(limbs2, idx) == 0
decreases len(limbs2) - idx
func equalLimbsReprHelper(limbs1, limbs2 []uint, idx int, p perm) {
	if idx != len(limbs2) {
		equalLimbsReprHelper(limbs1, limbs2, idx + 1, p/2)
	}
}
@*/

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

/*@
// Gobra doesn't have `clear` yet
preserves limbs != nil ==> acc(limbs)
ensures   limbs != nil ==> forall j int :: { limbs[j] } 0 <= j && j < len(limbs) ==> limbs[j] == 0
decreases
func clear(limbs []uint) {
	if limbs == nil {
		return // clear is noop if limbs is nil
	}

	invariant 0 <= i && i <= len(limbs)
	invariant acc(limbs)
	invariant forall j int :: { limbs[j] } 0 <= j && j < i ==> limbs[j] == 0
	decreases len(limbs) - i
	for i := 0; i < len(limbs); i++ {
		limbs[i] = 0
	}
	return
}
@*/

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

/*@
ghost
opaque
requires 0 <= e
ensures  0 < b ==> 0 < r
decreases e
pure func exp(b, e int) (r uint) {
	return e == 0 ? 1 : uint(b) * exp(b, e - 1)
}

ghost
requires 0 < b
requires 0 <= e1 && 0 <= e2
ensures  exp(b, e1) * exp(b, e2) == exp(b, e1 + e2)
decreases e1 + e2
pure func expLemma(b, e1, e2 int) bool {
    return e1 == 0 ?
        reveal exp(b, e1) == 1 :
        // prove for else branch
        let _ := reveal exp(b, e1) * exp(b, e2) == uint(b) * exp(b, e1 - 1) * exp(b, e2) in
        let _ := reveal exp(b, e1 + e2) == uint(b) * exp(b, (e1 - 1) + e2) in
        expLemma(b, e1 - 1, e2)
}
@*/

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

/*@
// it turns out that several functions operating on Modulus are happy if only the `nat` field is correct,
// which we capture via the `natOnly` ghost field.
pred (m *Modulus) Inv() {
    acc(m) && m.nat.Inv() &&
    (!m.natOnly ==> m.odd == (m.nat.Repr() % 2 == 1)) &&
    (!m.natOnly && m.odd ==> m.rr.Inv())
}

ghost
requires acc(m.Inv(), _)
decreases
pure func (m *Modulus) IsNatOnly() bool {
	return unfolding acc(m.Inv(), _) in m.natOnly
}

ghost
requires acc(m.Inv(), _)
decreases
pure func (m *Modulus) AnnouncedLen() (res int) {
	return unfolding acc(m.Inv(), _) in m.nat.AnnouncedLen()
}

ghost
requires acc(m.Inv(), _)
decreases
pure func (m *Modulus) Repr() uint {
    return unfolding acc(m.Inv(), _) in m.nat.Repr()
}
@*/

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

/*@
ghost
opaque
requires  0 <= a && 0 <= m
decreases m
pure func gcd(a, m uint) uint {
    return m == 0 ? a : gcd(m, a % m)
}

// gcd(a, 0) == a (base case, requires revealing the definition)
ghost
requires 0 <= a
ensures  gcd(a, 0) == a
decreases
func gcdBaseLemma(a uint) {
    reveal gcd(a, 0)
}

// gcd(a, b) == gcd(a - b, b) when a > b > 0
ghost
requires 0 < b && b < a
ensures  gcd(a, b) == gcd(a - b, b)
decreases
func gcdSubLemma(a, b uint) {
    reveal gcd(a, b)       // gcd(a, b) == gcd(b, a % b)
    reveal gcd(a - b, b)   // gcd(a-b, b) == gcd(b, (a-b) % b)
    modSubLemma(a, b)      // a % b == (a - b) % b
}

// gcd commutativity: gcd(a, b) == gcd(b, a)
ghost
requires 0 <= a && 0 <= b
ensures gcd(a, b) == gcd(b, a)
decreases
func gcdCommLemma(a, b uint) {
    if a == b {
        // reflexive
    } else if a == 0 || a < b {
	 	reveal gcd(a, b)
    } else {
        reveal gcd(b, a)
    }
}

// gcd(a, b) == gcd(a, b - a) when b >= a > 0
ghost
requires 0 < a && a <= b
ensures gcd(a, b) == gcd(a, b - a)
decreases
func gcdSubLemma2(a, b uint) {
    if a == b {
        reveal gcd(a, a)
    } else {
        gcdCommLemma(a, b)
        gcdSubLemma(b, a)
        gcdCommLemma(b - a, a)
    }
}

// gcd(a, b) == gcd(a / 2, b) when a is even and b is odd
ghost
requires 0 <= a && 0 <= b && a % 2 == 0 && b % 2 == 1
ensures gcd(a, b) == gcd(a / 2, b)
decreases a + b
func gcdHalfLemma(a, b uint) {
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
        gcdSubLemma(a / 2, b)            // gcd(a/2, b) == gcd(a/2-b, b)
    }
}

// gcd(a, b) == gcd(a, b / 2) when b is even and a is odd
ghost
requires 0 <= a && 0 <= b && b % 2 == 0 && a % 2 == 1
ensures gcd(a, b) == gcd(a, b / 2)
decreases
func gcdHalfLemma2(a, b uint) {
    gcdCommLemma(a, b)     // gcd(a, b) == gcd(b, a)
    gcdHalfLemma(b, a)     // gcd(b, a) == gcd(b / 2, a)
    gcdCommLemma(b / 2, a) // gcd(b / 2, a) == gcd(a, b / 2)
}

// Opaque relational predicate. This hides the non-linear terms (products)
// from Z3 to avoid NIA timeouts. Use `reveal` to open at specific points.
ghost
opaque
decreases
pure func nonLinearSub(u, A, B, aVal, mVal uint) bool {
    return u == A * aVal - B * mVal
}

// ===== Trusted lemmas =====================================================
// The following lemmas are trusted: their bodies are not verified by Z3.
// Each includes a Lean 4 formalization for external verification.
//
// 1. modSubLemma     — modular subtraction identity
// 2. prodParityLemma — product parity identity
// 3. AC_ge_BD_ge     — synchronized wrapping (fiat-crypto)
// 4. AC_lt_BD_le     — synchronized no-wrap (fiat-crypto)

// Modular subtraction: a % b == (a - b) % b when a > b > 0.
//
// Lean 4:
@*//*
  // 20260226 LA: checked in Lean
  theorem modSubLemma {a b : Int} :
      a % b = (a - b) % b := by
    simp
*//*@
ghost
trusted
requires b != 0 // required for well-formedness
ensures a % b == (a - b) % b
decreases
func modSubLemma(a, b uint)

// Product parity: (a * b) % 2 == (a % 2) * (b % 2).
//
// Lean 4:
@*//*
  // 20260226 LA: checked in Lean
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
func prodParityLemma(a, b uint)

// Positive product: 0 < a and 0 < b implies 0 < a * b.
// Isolates this NIA fact so Z3 handles it in a small context.
ghost
requires 0 < a && 0 < b
ensures 0 < a * b
decreases
func posProdLemma(a, b int) {
	// no body needed
}

// Distributive law: (a + b) * c == a * c + b * c
// This isolates a single NIA fact for Z3.
ghost
ensures (a + b) * c == a * c + b * c
decreases
func distLemma(a, b, c uint) {
	// no body needed
}

// Expand u - v using relational invariants:
// u = A*a - B*m and v = D*m - C*a imply u - v = (A+C)*a - (B+D)*m.
// Isolates the reveal + distLemma NIA from later proof steps.
ghost
requires nonLinearSub(u, A, B, a, m)
requires nonLinearSub(v, D, C, m, a)
ensures u - v == (A + C) * a - (B + D) * m
decreases
func subExpandLemma(u, v, A, B, C, D, a, m uint) {
    reveal nonLinearSub(u, A, B, a, m)
    reveal nonLinearSub(v, D, C, m, a)
    distLemma(A, C, a)
    distLemma(B, D, m)
}

// Expand v - u symmetrically: v - u = (D+B)*m - (C+A)*a.
ghost
requires nonLinearSub(u, A, B, a, m)
requires nonLinearSub(v, D, C, m, a)
ensures v - u == (D + B) * m - (C + A) * a
decreases
func subExpandLemma2(u, v, A, B, C, D, a, m uint) {
    reveal nonLinearSub(u, A, B, a, m)
    reveal nonLinearSub(v, D, C, m, a)
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
requires a > 0 && m > 0
requires 0 <= A && A < m && 0 <= C && C < m
requires 0 <= B && B <= a && 0 <= D && D <= a
requires (A + C >= m) == (B + D >= a)
requires A + C < m ==> Ap == A + C
requires A + C >= m ==> Ap == A + C - m
requires B + D < a ==> Bp == B + D
requires B + D >= a ==> Bp == B + D - a
ensures (A + C) * a - (B + D) * m == Ap * a - Bp * m
decreases
func modAddLemma(A, B, C, D, Ap, Bp, a, m uint) {
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
ghost
requires nonLinearSub(u + v, A - C, B - D, a, m)
requires nonLinearSub(v, D, C, m, a)
requires 0 < u && 0 < v && v < m // range for u, v
requires 0 < a // range for a
requires C <= A && A < m // range for A
requires D <= B && B <= a + D // range for B
requires 0 <= C && C < m // range for C
requires 0 <= D && D <= a // range for D
ensures nonLinearSub(u, A, B, a, m)
ensures B <= a
decreases
func subRelLemmaNoWrap(u, v, A, B, C, D, a, m uint) {
	uOld := u + v
	AOld := A - C
	BOld := B - D
	AC_lt_BD_le(uOld, v, AOld, BOld, C, D, a, m)
	subExpandLemma(uOld, v, AOld, BOld, C, D, a, m)
	assert reveal nonLinearSub(u, A, B, a, m)
}

// Relational invariant maintenance for subtraction (u > v case), wrap:
// A' = A + C - m, B' = B + D - a (synchronized subtraction).
// B+D >= a is established by AC_ge_BD_ge (called at call site).
ghost
requires nonLinearSub(u + v, A - C + m, B - D + a, a, m)
requires nonLinearSub(v, D, C, m, a)
requires 0 < u && 0 <= v && u + v <= a // range for u, v
requires 0 < a && a < m // range for a
requires 0 <= A && A < C // range for A
requires B <= D // range for B
requires 0 <= C && C < m // range for C
requires 0 <= D && D <= a // range for D
ensures nonLinearSub(u, A, B, a, m)
decreases
func subRelLemmaWrap(u, v, A, B, C, D, a, m uint) {
	uOld := u + v
	AOld := A - C + m
	BOld := B - D + a
	AC_ge_BD_ge(uOld, v, AOld, BOld, C, D, a, m)
	subExpandLemma(uOld, v, AOld, BOld, C, D, a, m)
	// u == (AOld+C)*a - (BOld+D)*m
	modAddLemma(AOld, BOld, C, D, A, B, a, m)
	// (AOld+C)*a - (BOld+D)*m == A*a - B*m
	assert reveal nonLinearSub(u, A, B, a, m)
}

// Relational invariant maintenance for subtraction (v >= u case), no-wrap:
// C' = C + A, D' = D + B (no modular reduction needed).
// D+B <= a follows from AC_lt_BD_le (called at call site).
ghost
requires nonLinearSub(u, A, B, a, m)
requires nonLinearSub(v + u, D - B, C - A, m, a)
requires 0 < u && v + u <= m
requires 0 < a
requires 0 <= A && A < m // range of A
requires 0 <= B && B <= D // range of B
requires C < m // range of C
ensures nonLinearSub(v, D, C, m, a)
ensures D <= a
decreases
func subRelLemma2NoWrap(u, v, A, B, C, D, a, m uint) {
	vOld := v + u
	COld := C - A
	DOld := D - B
	AC_lt_BD_le(u, vOld, A, B, COld, DOld, a, m)
	subExpandLemma2(u, vOld, A, B, COld, DOld, a, m)
	assert reveal nonLinearSub(v, D, C, m, a)
}

// Relational invariant maintenance for subtraction (v >= u case), wrap:
// C' = C + A - m, D' = D + B - a (synchronized subtraction).
ghost
requires nonLinearSub(u, A, B, a, m)
requires nonLinearSub(v + u, D - B + a, C - A + m, m, a)
requires 0 < a && a < m // range of a
requires 0 <= v + u && u <= a
requires A < m // range of A
requires 0 <= C && C < A // range of C
requires 0 <= D && D <= B // range of D
requires 0 <= B && B <= a // range of B
ensures nonLinearSub(v, D, C, m, a)
decreases
func subRelLemma2Wrap(u, v, A, B, C, D, a, m uint) {
	vOld := v + u
	COld := C - A + m
	DOld := D - B + a
	AC_ge_BD_ge(u, vOld, A, B, COld, DOld, a, m)
	subExpandLemma2(u, vOld, A, B, COld, DOld, a, m)
	// v == (DOld+B)*m - (COld+A)*a
	// With D = DOld+B-a and C = COld+A-m:
	// (DOld+B)*m == (D+a)*m, (COld+A)*a == (C+m)*a
	distLemma(D, a, m)  // (D+a)*m == D*m + a*m
	distLemma(C, m, a)  // (C+m)*a == C*a + m*a
	// Z3: v == D*m + a*m - C*a - m*a == D*m - C*a
	assert reveal nonLinearSub(v, D, C, m, a)
}

// AC_ge_BD_ge: When A+C >= m, then B+D >= a. (Matches fiat-crypto's AC_ge_BD_ge.)
// Proof: (B+D)*m = (A+C)*a - (u-v). Since A+C >= m: (A+C)*a >= m*a.
// And u-v <= u <= a. So (B+D)*m >= m*a - a = a*(m-1).
// If B+D <= a-1: (a-1)*m >= a*(m-1), giving a >= m. Contradicts a < m.
//
// Note: For the v >= u case, the a < m condition is not needed
// (since v >= u gives (B+D)*m = (A+C)*a + (v-u) >= m*a directly).
// We keep the single lemma with a < m since it's an invariant anyway.
//
// Lean 4:
@*//*
  // 20260226 LA: checked in Lean (needs `import Mathlib.Tactic.ByContra`)
  theorem AC_ge_BD_ge {u v A B C D a m : Int}
    (hU : u = A * a - B * m) (hV : v = D * m - C * a)
    (hUle : u ≤ a) (hVge : 0 ≤ v)
    (hWrap : A + C ≥ m)
    (hApos : 0 < a) (hAltM : a < m) (hMpos : 0 < m) :
    B + D ≥ a := by
    -- From hU and hV: (B+D)*m = (A+C)*a - u + v
    -- Key NIA facts we establish manually:
    have hACa : (A + C) * a ≥ m * a := Int.mul_le_mul_of_nonneg_right hWrap (Int.le_of_lt hApos)
    have hma : m * a = a * m := Int.mul_comm m a
    -- By contradiction: assume B+D ≤ a-1
    by_contra h
    have hBD : B + D ≤ a - 1 := by omega
    have hBDm : (B + D) * m ≤ (a - 1) * m := Int.mul_le_mul_of_nonneg_right hBD (Int.le_of_lt hMpos)
    -- But (B+D)*m = (A+C)*a - u + v ≥ m*a - a + 0
    -- And (a-1)*m = a*m - m
    -- So a*m - m ≥ m*a - a, giving a ≥ m. Contradiction.
    grind
*//*@
ghost
trusted
requires nonLinearSub(u, A, B, a, m)
requires nonLinearSub(v, D, C, m, a)
requires u <= a && 0 <= v
requires A + C >= m
requires 0 < a && a < m && 0 < m
ensures  B + D >= a
decreases
func AC_ge_BD_ge(u, v, A, B, C, D, a, m uint)

// AC_lt_BD_le: When A+C < m, then B+D <= a. (Matches fiat-crypto's AC_lt_BD_le.)
// Proof: (B+D)*m = (A+C)*a - u + v. Since A+C <= m-1: (A+C)*a <= (m-1)*a.
// Since u >= 1, v <= m: (B+D)*m <= (m-1)*a - 1 + m.
// If B+D >= a+1: (a+1)*m <= (m-1)*a - 1 + m = ma - a + m - 1,
// giving am + m <= am - a + m - 1, i.e. 0 <= -a-1. Contradiction.
//
// Lean 4:
@*//*
  // 20260226 LA: checked in Lean (needs `import Mathlib.Tactic.ByContra`)
  theorem AC_lt_BD_le {u v A B C D a m : Int}
    (hU : u = A * a - B * m) (hV : v = D * m - C * a)
    (hUpos : 0 < u) (hVle : v ≤ m)
    (hNoWrap : A + C < m)
    (hApos : 0 < a) (hMpos : 0 < m) :
    B + D ≤ a := by
    -- From hU and hV: (B+D)*m = (A+C)*a - u + v
    -- Key NIA facts:
    have hAC : A + C ≤ m - 1 := by omega
    have hACa : (A + C) * a ≤ (m - 1) * a := Int.mul_le_mul_of_nonneg_right hAC (Int.le_of_lt hApos)
    have hma : m * a = a * m := Int.mul_comm m a
    -- By contradiction: assume B+D ≥ a+1
    by_contra h
    have hBD : B + D ≥ a + 1 := by omega
    have hBDm : (B + D) * m ≥ (a + 1) * m := Int.mul_le_mul_of_nonneg_right hBD (Int.le_of_lt hMpos)
    -- But (B+D)*m = (A+C)*a - u + v ≤ (m-1)*a - 1 + m
    -- And (a+1)*m = a*m + m
    -- So a*m + m ≤ (m-1)*a - 1 + m = a*m - a + m - 1
    -- Giving 0 ≤ -a - 1. Contradiction.
    grind
*//*@
ghost
trusted
requires nonLinearSub(u, A, B, a, m)
requires nonLinearSub(v, D, C, m, a)
requires 0 < u && v <= m
requires A + C < m
requires 0 < a && 0 < m
ensures  B + D <= a
decreases
func AC_lt_BD_le(u, v, A, B, C, D, a, m uint)

// Parity lemma: when u = A*a - B*m is even and A or B is odd,
// then A+m and B+a are both even. Reveals nonLinearSub only for parity reasoning.
ghost
requires nonLinearSub(u, A, B, a, m)
requires u % 2 == 0
requires A >= 0 && B >= 0 && a >= 0 && m >= 0
requires a % 2 != 0 || m % 2 != 0
requires A % 2 != 0 || B % 2 != 0
ensures (A + m) % 2 == 0
ensures (B + a) % 2 == 0
decreases
func parityLemma(u, A, B, a, m uint) {
    reveal nonLinearSub(u, A, B, a, m)
    prodParityLemma(A, a)
    prodParityLemma(B, m)
}

// Relational invariant maintenance for halving u:
ghost
requires nonLinearSub(u * 2, A * 2, B * 2, a, m)
requires 0 < u
requires 0 <= A && A * 2 < m // range for A
requires 0 <= B && B * 2 <= a // range for B
ensures nonLinearSub(u, A, B, a, m)
decreases
func halvRelLemmaU1(u, A, B, a, m uint) {
	uOld := u * 2
	AOld := A * 2
	BOld := B * 2
	assert reveal nonLinearSub(uOld, AOld, BOld, a, m)
	distLemma(A, A, a)
	distLemma(B, B, m)
	assert reveal nonLinearSub(u, A, B, a, m)
}

ghost
requires nonLinearSub(u * 2, A * 2 - m, B * 2 - a, a, m)
requires 0 < u
requires 0 < m && A < m && m <= A * 2 // range for m
requires 0 < a && B <= a && a <= B * 2 // range for a
ensures nonLinearSub(u, A, B, a, m)
ensures 0 <= A
ensures 0 <= B && B < a
decreases
func halvRelLemmaU2(u, A, B, a, m uint) {
	uOld := u * 2
	AOld := A * 2 - m
	BOld := B * 2 - a
	assert reveal nonLinearSub(uOld, AOld, BOld, a, m)
	distLemma(A, A, a)
	distLemma(B, B, m)
	distLemma(AOld, m, a)
	distLemma(BOld, a, m)
	assert reveal nonLinearSub(u, A, B, a, m)
}

// Parity lemma for v: when v = D*m - C*a is even and C or D is odd,
// then C+m and D+a are both even.
ghost
requires nonLinearSub(v, D, C, m, a)
requires v % 2 == 0
requires C >= 0 && D >= 0 && a >= 0 && m >= 0
requires a % 2 != 0 || m % 2 != 0
requires C % 2 != 0 || D % 2 != 0
ensures (C + m) % 2 == 0
ensures (D + a) % 2 == 0
decreases
func parityLemmaV(v, C, D, a, m uint) {
    reveal nonLinearSub(v, D, C, m, a)
    prodParityLemma(C, a)
    prodParityLemma(D, m)
}

// Relational invariant maintenance for halving v (mirrors halvRelLemmaU):
ghost
requires nonLinearSub(v * 2, D * 2, C * 2, m, a)
requires 0 < a
requires 0 <= C && C * 2 < m // range for C
requires 0 <= D && D * 2 <= a // range for D
ensures nonLinearSub(v, D, C, m, a)
decreases
func halvRelLemmaV1(v, C, D, a, m uint) {
	vOld := v * 2
	COld := C * 2
	DOld := D * 2
	assert reveal nonLinearSub(vOld, DOld, COld, m, a)
	assert COld == 2 * C
	assert DOld == 2 * D
	distLemma(C, C, a)
	distLemma(D, D, m)
	assert reveal nonLinearSub(v, D, C, m, a)
}

ghost
requires nonLinearSub(v * 2, D * 2 - a, C * 2 - m, m, a)
requires 0 < m
requires C < m && m <= C * 2 // range for m
requires 0 < a && D <= a && a <= D * 2 // range for a
ensures nonLinearSub(v, D, C, m, a)
ensures 0 <= C
ensures 0 <= D
decreases
func halvRelLemmaV2(v, C, D, a, m uint) {
	vOld := v * 2
	COld := C * 2 - m
	DOld := D * 2 - a
	assert reveal nonLinearSub(vOld, DOld, COld, m, a)
	distLemma(C, C, a)
	distLemma(D, D, m)
	distLemma(COld, m, a)
	distLemma(DOld, a, m)
	assert reveal nonLinearSub(v, D, C, m, a)
}
@*/

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

// since Go has a built-in max function, we wrap it in
// spec comments such that only Gobra but not the Go compiler
// picks it up:
/*@
ghost
decreases
pure func gmax(a, b int) int {
	return a >= b ? a : b
}

ensures r == gmax(a, b)
decreases
func max(a, b int) (r int) {
	if a >= b {
		return a
	}
	return b
}
@*/

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
