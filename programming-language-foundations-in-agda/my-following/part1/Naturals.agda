module part1.Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ
{-# BUILTIN NATURAL ℕ  #-}

-- Exercise 1: Seven in longhand
seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 3 + 4 ≡ 7
_ =
 begin
   3 + 4
 ≡⟨⟩
   (suc 2) + 4
 ≡⟨⟩
   suc (2 + 4)
 ≡⟨⟩
   suc ((suc 1) + 4)
 ≡⟨⟩
   suc (suc (1 + 4))
 ≡⟨⟩
   suc (suc ((suc 0) + 4))
 ≡⟨⟩
   suc (suc (suc (0 + 4)))
 ≡⟨⟩
   suc (suc (suc 4))
 ≡⟨⟩
   7
 ∎

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

{-
_ : 3 * 4 ≡ 12
_ =
 begin
   3 * 4
 ≡⟨⟩
   (suc 2) * 4
 ≡⟨⟩
   4 + (2 * 4)
 ≡⟨⟩
   4 + ((suc 1) * 4)
 ≡⟨⟩
   4 + (4 + (1 * 4))
 ≡⟨⟩
   4 + (4 + ((suc 0) * 4))
 ≡⟨⟩
   4 + (4 + (4 + (0 * 4)))
 ≡⟨⟩
   4 + 4 + 4
 ≡⟨⟩
   12
 ∎
-}

_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎
