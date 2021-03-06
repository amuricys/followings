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

infixl 6  _+_  _∸_
infixl 7  _*_

-- Turd: What is the difference between the types 3 ∸ 5 ≡ 0 and 0?
-- I don't know, but it seems there's no difference between 3 ∸ 5 ≡ 0 and 3 ∸ 4 ≡ 0.
-- The same "expression" (the proof/content of the chain of reasoning) typechecks for both
-- type signatures. Perhaps types are the same if they correspond to the same proofs?
_ : 3 ∸ 4 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

-- Turd: I don't understand what kind of additional insight this part of the chapter is
-- supposed to be adding. It seems completely trivial and void of content:
-- On the fourth day, we know about addition of 0, 1, 2, and 3.
-- 0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
-- 1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
-- 2 + 0 = 2     2 + 1 = 3     2 + 2 = 4     2 + 3 = 5     ...
-- 3 + 0 = 3     3 + 1 = 4     3 + 2 = 5     3 + 3 = 6     ...

-- Turd: Que desgraça! Eu não consigo fazer essa porra com o modo interativo. C-c C-, não funciona de jeito nium
-- _#-_ : ℕ → ℕ → ℕ
-- zero #- n = n
-- suc zero #- zero = {!!}

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- First stretch: Bin inc
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (p I) =  (inc p) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ =
  begin
    inc (⟨⟩ I O I I)
  ≡⟨⟩
    (inc (⟨⟩ I O I ) O)
  ≡⟨⟩
    ( inc (⟨⟩ I O) O O )
  ≡⟨⟩
    ⟨⟩ I I O O
  ∎

to : ℕ → Bin
to zero    = ⟨⟩ O
to (suc n) = inc (to n)

_ : to 4 ≡ ⟨⟩ I O O
_ =
  begin
    to (suc 3)
  ≡⟨⟩
    inc (to (suc 2))
  ≡⟨⟩
    (inc (inc (to (suc 1))))
  ≡⟨⟩
    (inc (inc (inc (to (suc 0)))))
  ≡⟨⟩
    (inc (inc (inc (inc (to 0)))))
  ≡⟨⟩
    (inc (inc (inc (inc (⟨⟩ O)))))
  ≡⟨⟩
    (inc (inc (inc (⟨⟩ I))))
  ≡⟨⟩
    (inc (inc (⟨⟩ I O)))
  ≡⟨⟩
    (inc (⟨⟩ I I))
  ≡⟨⟩
    ⟨⟩ I O O
  ∎


-- Turd: Era pra usar `inc` de alguma forma aqui?? Não consigo ver como :( 
from : Bin → ℕ
from ⟨⟩     = zero 
from (p I)  = suc (2 * (from p))
from (p O)  = 2 * (from p)

_ : from (⟨⟩ I O O)  ≡  4  
_ =
  begin
    from (⟨⟩ I O O)
   ≡⟨⟩
    4
  ∎
