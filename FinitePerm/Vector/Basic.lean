/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

@[expose] public section

namespace Vector

@[simp, grind =]
theorem swap_same {xs : Vector α n} {i : Nat} {hi} : xs.swap i i hi hi = xs := by grind
