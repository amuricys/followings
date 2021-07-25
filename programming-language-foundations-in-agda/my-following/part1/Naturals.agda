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

_ : 3 * 4 ≡ 12
_ =
 begin
   3 * 4
 ≡⟨⟩
   4 + (2 * 4)
 ≡⟨⟩
   4 + (4 + (1 * 4))
 ≡⟨⟩
   4 + (4 + (4 + (0 * 4)))
 ≡⟨⟩
   12
 ∎

_^_ : ℕ → ℕ → ℕ
n       ^ zero    = 1
n       ^ (suc m) =  n * (n ^ m)

_ : 9 ^ 3 ≡ 729 
_ =
 begin
   9 ^ 3
 ≡⟨⟩
   9 * (9 ^ 2)
 ≡⟨⟩
   9 * (9 * (9 ^ 1))
 ≡⟨⟩
   729
 ∎

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎


_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

-- Turd: So what we're doing is *just pattern matching*, right?
-- When we define an equation/operator, we're saying "here are the
-- patterns you can match on, and what equates to what. And those equalities
-- will fall on steps of a theorem proving operation/reasoning chain.