// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build sync_legacy

package bigmod

// UseSynchronizedWrappingInExtendedGCD is compiled as a constant so the
// compiler can eliminate the dead branch in extendedGCD.
// Rebuild with -tags=sync_fixed for the synchronized-wrapping path.
const UseSynchronizedWrappingInExtendedGCD = false
