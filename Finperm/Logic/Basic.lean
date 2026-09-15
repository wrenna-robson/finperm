/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

@[expose] public section

@[simp, grind =]
theorem getElem_dite {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (a : P → coll) (b : ¬ P → coll)
    {k : idx} {hk : valid (if h : P then a h else b h) k} :
    (if h : P then a h else b h)[k] =
    if h : P then (a h)[k]'(by grind) else (b h)[k]'(by grind) := by grind

@[simp, grind =]
theorem getElem_ite {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (a b : coll)
    {k : idx} {hk : valid (if P then a else b) k} :
    (if P then a else b)[k] =
    if h : P then a[k]'(by grind) else b[k]'(by grind) := getElem_dite _ _ _

@[simp, grind =]
theorem dite_getElem {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (i : P → idx) (j : ¬ P → idx)
    {v : coll} {hk : valid v (if h : P then i h else j h)} :
    v[if h : P then i h else j h] =
    if h : P then v[i h]'(by grind) else v[j h]'(by grind) := by grind

@[simp, grind =]
theorem ite_getElem {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (i j : idx)
    {v : coll} {hk : valid v (if P then i else j)} :
    v[if P then i else j] =
    if h : P then v[i]'(by grind) else v[j]'(by grind) := dite_getElem _ _ _

@[simp] theorem forall_true_left (p : True → Prop) : (∀ (h : True), p h) ↔ p True.intro :=
    ⟨fun h => h _, fun h _ => h⟩
