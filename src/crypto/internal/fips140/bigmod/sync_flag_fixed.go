// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build sync_fixed

package bigmod

// UseSynchronizedWrappingInExtendedGCD is compiled as a constant so the
// compiler can eliminate the dead branch in extendedGCD.
// Rebuild with -tags=sync_legacy for the legacy path.
const UseSynchronizedWrappingInExtendedGCD = true
