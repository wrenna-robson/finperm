/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
public import FinitePerm.Congr

public section

/-!
# Notation and `Repr` instances for `PermVector` and `FinitePerm`

This file provides:

* `#pv[i₀, i₁, ..., iₙ₋₁]`, notation for the `PermVector n` sending each `k < n` to `iₖ`.
* `fp[i₀, i₁, ..., iₙ₋₁]`, notation for the `FinitePerm` obtained from that `PermVector` by
  trimming trailing fixed points.
* `Repr` instances for `PermVector` and `FinitePerm` which display values using this notation,
  so that e.g. `#eval fp[0, 2, 1, 3] * fp[1, 0]` prints as a `fp[...]` literal.
-/

/-- `#pv[i₀, i₁, ..., iₙ₋₁]` is the `PermVector n` sending each `k < n` to `iₖ`. -/
syntax (name := permVectorLit) "#pv[" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(#pv[ $elems,* ]) => `(Vector.Nodup.toPermVector #v[$elems,*])

/-- `fp[i₀, i₁, ..., iₙ₋₁]` is the `FinitePerm` sending each `k < n` to `iₖ` (and every other
value to itself), obtained by trimming trailing fixed points from the corresponding
`PermVector n`. -/
syntax (name := finitePermLit) "fp[" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(fp[ $elems,* ]) => `(PermVector.toFinitePerm #pv[$elems,*])

@[app_unexpander Vector.Nodup.toPermVector]
meta def unexpandNodupToPermVector : Lean.PrettyPrinter.Unexpander
  | `($_ #v[$elems,*] $_ $_) => `(#pv[$elems,*])
  | _ => throw ()

@[app_unexpander PermVector.toFinitePerm]
meta def unexpandToFinitePerm : Lean.PrettyPrinter.Unexpander
  | `($_ #pv[$elems,*]) => `(fp[$elems,*])
  | _ => throw ()

instance : Repr (PermVector n) where
  reprPrec a _ :=
    Std.Format.bracket "#pv[" (Std.Format.joinSep (a.toVector.toList.map repr) ("," ++ Std.Format.line)) "]"

instance : Repr FinitePerm where
  reprPrec a _ :=
    Std.Format.bracket "fp[" (Std.Format.joinSep (a.toPermOf.toVector.toList.map repr) ("," ++ Std.Format.line)) "]"
