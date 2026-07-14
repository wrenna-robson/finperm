/--
A `FinPerm n` is a permutation on `n` elements represented by two vectors, which we can
think of as an array of values and a corresponding array of indexes which are inverse to
one another. (One can flip the interpretation of indexes and values, and this is essentially
the inversion operation.)
It is designed to be a more performant version of `Equiv.Perm`.
-/
structure FinPerm (n : Nat) where
  /--
  Gives the `FinPerm` as an vector of size `n`.
  -/
  protected toVector : Vector Nat n
  /--
  Gives the inverse of the `FinPerm` as a vector of size `n`.
  -/
  protected invVector : Vector Nat n
  getElem_invVector_getElem_toVector :
      ∀ i, (hi : i < n) → ∃ (hi' : toVector[i] < n), invVector[toVector[i]] = i := by decide
