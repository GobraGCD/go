// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build !sync_legacy && !sync_fixed

package bigmod

// UseSynchronizedWrappingInExtendedGCD switches coefficient updates in
// extendedGCD between the legacy modular-add path and the synchronized-wrap
// path.
//
// false: legacy behavior (buggy in some edge cases)
// true: synchronized wrapping fix
//
// This is a var so that tests can toggle it at runtime to compare both modes.
// Build with -tags=sync_legacy or -tags=sync_fixed to get a const (enabling
// dead-code elimination by the compiler).
var UseSynchronizedWrappingInExtendedGCD bool
