/-
Minimal standalone example demonstrating grind E-matching limitation.

Only requires Mathlib. Demonstrates that grind cannot automatically apply
function extensionality (marked @[grind _=_]) when proving membership properties.
A direct characterization lemma with @[grind =] is needed as a workaround.

This mirrors the pattern from LTS.setImageMultistep_foldl_setImage and
LTS.mem_foldl_setImage, but with minimal types (just Nat and List Nat).
-/

import Mathlib

-- Inductive definition of reaching a result via list folding
inductive Reaches : Nat → List Nat → Nat → Prop where
  | nil : Reaches n [] n
  | cons : Reaches (n + x) xs r → Reaches n (x :: xs) r

-- Inductive version: set of all reachable results
def reachSet (n : Nat) (xs : List Nat) : Set Nat :=
  {r | Reaches n xs r}

-- Foldl version: singleton set containing the foldl result
def foldlSet (n : Nat) (xs : List Nat) : Set Nat :=
  {List.foldl (· + ·) n xs}

-- Function extensionality: the two definitions are equal
-- Marked @[grind _=_] (low priority for E-matching)
@[grind _=_]
theorem reachSet_eq_foldlSet :
    reachSet = foldlSet := by
  ext n xs r
  simp only [reachSet, foldlSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons _ ih => exact ih
  · intro h
    subst h
    induction xs generalizing n with
    | nil => exact Reaches.nil
    | cons x xs ih =>
      simp only [List.foldl_cons]
      exact Reaches.cons (ih (n + x))

-- BEFORE: Without helper lemma, manual rewrite needed
-- (grind cannot apply reachSet_eq_foldlSet automatically)
theorem example_before (n : Nat) (xs : List Nat) (r : Nat) :
    r ∈ foldlSet n xs ↔ Reaches n xs r := by
  rw [← reachSet_eq_foldlSet]
  simp [reachSet]

-- WORKAROUND: Direct characterization with @[grind =]
@[grind =]
theorem mem_foldlSet (n : Nat) (xs : List Nat) (r : Nat) :
    r ∈ foldlSet n xs ↔ Reaches n xs r := by
  rw [← reachSet_eq_foldlSet]
  simp [reachSet]

-- AFTER: With helper lemma, grind works automatically
theorem example_after (n : Nat) (xs : List Nat) (r : Nat) :
    r ∈ foldlSet n xs ↔ Reaches n xs r := by
  grind
