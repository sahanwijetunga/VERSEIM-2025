 --------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- I had a thought yesterday evening that it is perhaps easier to
-- start with symmetric bilinear forms, despite their eventual greater
-- comlpexity.

-- e.g. you probably saw what is known as "Gram-Schmidt" in your
-- linear algebra class. So let's implement that!

-- so *for the time being* we are going to take k = ℝ

-- We need some notions about bilinear forms.

def BilinearMap (k V : Type) [AddCommGroup V] [Field k] [Module k V]: Type := 
  V →ₗ[k] V →ₗ[k] k 

#check β x

def BilSymmetric {k V : Type} [AddCommGroup V] [Field k] [Module k V] (β:BilinearMap k V) : Prop := 
  ∀ (x y : V), x = y
