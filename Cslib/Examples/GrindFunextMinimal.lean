/-
Copyright (c) 2025 Jesse Hathaway. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Hathaway
-/

import Cslib.Init

/-!
# Minimal Example: Grind E-matching Limitation with Function Extensionality

This file demonstrates a limitation in Lean's `grind` tactic where it cannot automatically
apply function extensionality under congruence during E-matching.

## The Pattern

This minimal example mirrors the pattern from PR #154 where adding `LTS.mem_foldl_setImage`
with `@[grind =]` enabled grind to automatically complete a proof.

## The Problem

When two functions are proven equal via function extensionality (marked `@[grind _=_]`),
grind cannot automatically apply this equality when proving membership properties.

## The Workaround

Adding a direct characterization lemma with `@[grind =]` provides a concrete pattern
that grind's E-matching can reliably match.

## References

- Original PR: https://github.com/leanprover/cslib/pull/154
-/

namespace Cslib

-- Simple state type
structure SimpleState where
  value : Nat

-- Simple accumulator function (analogous to LTS.setImage)
def accumulate (S : Set SimpleState) (n : Nat) : Set SimpleState :=
  S ∪ {⟨n⟩}

-- Inductive multi-step version (analogous to LTS.MTr)
inductive MultiStep : Set SimpleState → List Nat → SimpleState → Prop where
  | base {S : Set SimpleState} {s : SimpleState} :
      s ∈ S → MultiStep S [] s
  | step {S : Set SimpleState} {n : Nat} {ns : List Nat} {s : SimpleState} :
      MultiStep (accumulate S n) ns s → MultiStep S (n :: ns) s

-- Foldl-based version (analogous to using List.foldl lts.setImage)
def foldlAccumulate (S : Set SimpleState) (ns : List Nat) : Set SimpleState :=
  List.foldl accumulate S ns

-- Helper to characterize membership in the inductive version
def multiStepSet (S : Set SimpleState) (ns : List Nat) : Set SimpleState :=
  {s | MultiStep S ns s}

-- The equivalence via function extensionality
-- This is marked @[grind _=_] which is lower priority
@[grind _=_]
theorem multiStepSet_eq_foldl :
    multiStepSet = foldlAccumulate := by
  ext S ns s
  simp only [multiStepSet, Set.mem_setOf_eq, foldlAccumulate]
  constructor
  · intro h
    induction h with
    | base hs => exact hs
    | step _ ih => exact ih
  · intro h
    induction ns generalizing S with
    | nil => exact MultiStep.base h
    | cons n ns ih =>
      simp only [List.foldl_cons] at h
      exact MultiStep.step (ih (accumulate S n) h)

-- BEFORE: Without the helper lemma, this theorem needs manual rewrite
-- grind cannot automatically apply multiStepSet_eq_foldl
theorem example_before (S : Set SimpleState) (ns : List Nat) (s : SimpleState) :
    s ∈ foldlAccumulate S ns ↔ MultiStep S ns s := by
  -- Manual rewrite needed
  rw [← multiStepSet_eq_foldl]
  simp [multiStepSet]

-- WORKAROUND: Helper lemma with @[grind =] for direct E-matching
@[grind =]
theorem mem_foldl_accumulate (S : Set SimpleState) (ns : List Nat) (s : SimpleState) :
    s ∈ foldlAccumulate S ns ↔ MultiStep S ns s := by
  rw [← multiStepSet_eq_foldl]
  simp [multiStepSet]

-- AFTER: With the helper lemma, grind works automatically
theorem example_after (S : Set SimpleState) (ns : List Nat) (s : SimpleState) :
    s ∈ foldlAccumulate S ns ↔ MultiStep S ns s := by
  grind

end Cslib
