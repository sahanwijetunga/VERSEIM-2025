 --------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- it is probably useful to read the section in [math-in-lean] on
-- induction proofs in §5 and §6

-- also useful -- and maybe a little more lucid on this sort of topic
-- [Theorem proving in Lean] esp. §7 though you'll want to read parts
-- of §2 §3 first.  **link** is here:
 
-- https://lean-lang.org/theorem_proving_in_lean4/


--inductive data types have constructors, e.g. like the Option type

inductive MyOption (α:Type) where
  | some : α → MyOption α
  | none : MyOption α

-- or natural numbers

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

-- e.g. Lean already has a Nat type -- also attached to the symbol ℕ
-- -- which is like that just introduced. We can see that:

open Nat in
example : 3 = succ ( succ (succ zero)) := rfl



