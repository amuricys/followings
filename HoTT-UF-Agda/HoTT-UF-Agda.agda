{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

-- https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#hlevel

module HoTT-UF-Agda where

-- 12/03/2024
open import Universes public

variable
 𝓤 𝓥 𝓦 𝓣 : Universe

data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇ ) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : (B : 𝓤 ̇ ) → B → (𝟙 → B)
𝟙-recursion B b = 𝟙-induction (λ _ → B) b

!𝟙' : (X : 𝓤 ̇ ) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇ } → X → 𝟙
!𝟙 x = ⋆

data 𝟘 : 𝓤₀ ̇  where

𝟘-induction : (A : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → A x
𝟘-induction a ()

𝟘-recursion : (A : 𝓤 ̇ ) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

data ℕ : 𝓤₀ ̇  where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (A : ℕ → 𝓤 ̇ ) -- I have a property on the natural numbers
            → A 0           -- and a proof that the property holds for 0
            → ((n : ℕ) → A n → A (succ n)) -- and a proof that, given a natural number and the fact that the property holds for it, then it holds for its successor
            → (n : ℕ) → A n -- then if you give me a natural number, I can give you a proof that the property holds for it
ℕ-induction A a₀ f = h
 where
  h : (n : ℕ) → A n
  h zero = a₀ 
  h (succ x) = f x (h x)

ℕ-recursion : (X : 𝓤 ̇ ) -- I have a type
            → X         -- And an element of that type
            → (ℕ → X → X) -- and a way to generate this type from a natural number and an element of that type
            → ℕ → X     -- then give me a natural number and i can give you a value of this type
ℕ-recursion X = ℕ-induction (λ _ → X)

ℕ-iteration : (X : 𝓤 ̇ )
            → X
            → (X → X)
            → ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

module Arithmetic where
  _+_  _×_ : ℕ → ℕ → ℕ
  x + 0      = x
  x + succ y = succ (x + y)
  x × 0      = 0
  x × succ y = x + x × y
  infixl 20 _+_
  infixl 21 _×_

module Arithmetic' where
  _+_  _×_ : ℕ → ℕ → ℕ
  x + y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ x succ
  x × y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ 0 (x +_)
  infixl 20 _+_
  infixl 21 _×_

data _+_ {𝓤 𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 inl : X → X + Y
 inr : Y → X + Y

+-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇ ) -- to prove a property on X + Y
            → ((x : X) → A (inl x)) -- I need to prove it for inl x for all x : X
            → ((y : Y) → A (inr y)) -- and for inr y for all y : Y
            → (z : X + Y) → A z  -- then I can prove it for all z : X + Y
+-induction A f g (inl x) = f x 
+-induction A f g (inr x) = g x

+-recursion : {X : 𝓤 ̇} 
            → {Y : 𝓥 ̇} 
            → {A : 𝓦 ̇} 
            → (X → A)
            → (Y → A)
            → X + Y → A
+-recursion {A = A} = +-induction (λ _ → A)

𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

pattern a ∅ = inl a

𝟚-induction : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ n = +-induction A (λ {⋆ → a₀})
                                      (λ {⋆ → a₁}) 
                                      n

record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
  constructor
   _,_
  field
   x : X
   y : Y x

pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ x ꞉ X , y

Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } 
              {A : Σ Y → 𝓦 ̇ } -- Given a property of a type family Y
            → ((x : X) (y : Y x) → A (x , y)) -- and a proof that the property holds ∀ x : X and y : Y x
            → (y : Σ Y) → A y  -- Give me any y : Σ Y and I will give you a proof that the property holds for it
Σ-induction f (x , y) = f x y

-- The inverse
curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } 
        {A : Σ Y → 𝓦 ̇ } -- Given a property of a type family Y
      → ((y : Σ Y) → A y) -- And a proof that it holds for y : Σ Y
      → ((x : X) (y : Y x) → A (x , y)) -- Then give me any x : X and y : Y x and I will give you a proof that the property holds for (x , y)
curry f x y = f (x , y)

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {X = X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y

syntax -Π A (λ x → b) = Π x ꞉ A , b

id : {X : 𝓤 ̇ } → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇ ) → X → X
𝑖𝑑 X = id

_∘_ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : ∀ {x : X} → Y x → 𝓦 ̇ }
    → (∀ {x : X} → (y : Y x) → Z y)
    → (f : (x : X) → Y x)
    → (x : X) → Z (f x)
f ∘ g = λ x → f (g x)

domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X

data Id {𝓤} (X : 𝓤 ̇ ) : X → X → 𝓤 ̇  where
 refl : (x : X) → Id X x x

{- 
Intuitively, the above definition would say that the only element of the type 
Id X x x is something called refl x (for reflexivity). But, as we shall see 
in a moment, this intuition turns out to be incorrect.

Notice a crucial difference with the previous definitions using data or induction: 
In the previous cases, we defined types, namely 𝟘, 𝟙, ℕ, or a type depending on 
type parameters, namely _+_, with 𝓤 and 𝓥 fixed,

_+_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇

But here we are defining a type family indexed by the elements of a given type,
rather than a new type from old types. ***Given a type X in a universe 𝓤***, we define
a function

Id X : X → X → 𝓤

by some mysterious sort of induction. 
-}

_＝_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ＝ y = Id _ x y

{-
Whereas we can make the intuition that x ＝ x has precisely one element good
by postulating a certain K axiom due to Thomas Streicher, which comes with 
Agda by default but we have disabled above, we cannot prove that refl x is the
only element of x ＝ x for an arbitrary type X. This non-provability result
was established by Hofmann and Streicher, by giving a model of type theory
in which types are interpreted as 1-groupoids. This is in spirit similar 
to the non-provability of the parallel postulate in Euclidean geometry, which 
also considers models, which in turn are interesting in their own right.

However, for the elements of some types, such as the type ℕ of natural numbers, 
it is possible to prove that any identity type x ＝ y has at most one element. 
Such types are called sets in univalent mathematics.

If instead of the axiom K we adopt Voevodsky’s univalence axiom, we get specific 
examples of objects x and y such that the type x ＝ y has multiple elements, 
within the type theory. It follows that the identity type x ＝ y is fairly 
under-specified in general, in that we can’t prove or disprove that it has at 
most one element.

There are two opposing ways to resolve the ambiguity or under-specification of 
the identity types: (1) We can consider the K axiom, which postulates that all 
types are sets, or (2) we can consider the univalence axiom, arriving at 
univalent mathematics, which gives rise to types that are more general than sets, 
the n-groupoids and ∞-groupoids. In fact, the univalence axiom will say, in 
particular, that for some types X and elements x y : X, the identity type x ＝ y 
does have more than one element.

A possible way to understand the element refl x of the type x ＝ x is as 
the “generic identification” between the point x and itself, but which is by 
no means necessarily the only identitification in univalent foundations. It is 
generic in the sense that to explain what happens with all identifications 
p : x ＝ y between any two points x and y of a type X, it suffices to explain 
what happens with the identification refl x : x ＝ x for all points x : X. This 
is what the induction principle for identity given by Martin-Löf says, which 
he called J (we could have called it ＝-induction, but we prefer to honour MLTT 
tradition):
-}

-- 13/03/2024
𝕁 : (X : 𝓤 ̇ )                       -- given a type X
    (A : (x y : X) → x ＝ y → 𝓥 ̇ )  -- and a property of any equality x =ₓ y 
  → (f : (x : X) → A x x (refl x))  -- And a proof that the property holds for refl x for all x : X
  → (x y : X) (p : x ＝ y) → A x y p -- Then I can prove the property for any x y : X and p : x ＝ y
𝕁 X A f x .x (refl .x) = f x -- How, dude. its so magic

{-
This is related to the Yoneda Lemma in category theory, for readers familiar with the subject, 
which says that certain natural transformations are uniquely determined by their 
action on the identity arrows, even if they are defined for all arrows. Similarly 
here, 𝕁 is uniquely determined by its action on reflexive identifications, but is 
defined for all identifications between any two points, not just reflexivities.
-}


ℍ : {X : 𝓤 ̇ } -- Alternate J. Given a type
    (x : X)   -- An element x of that type 
    (B : (y : X) → x ＝ y → 𝓥 ̇ ) -- A property on equalities between x and all other elements of X
  → B x (refl x) -- A proof that the property holds for refl x
  → (y : X) (p : x ＝ y) → B y p -- Then I can prove the property for any y : X and p : x ＝ y
ℍ x B b x (refl x) = b


𝕁' : (X : 𝓤 ̇ )                    -- given a type X
     (A : (x y : X) → x ＝ y → 𝓥 ̇ ) -- and a property on equalities between x and any other y : X
   → (f : (x : X) → A x x (refl x)) -- and a proof that the property holds for refl x for all x : X
   → (x y : X) (p : x ＝ y) → A x y p -- Then I can prove the property for any x y : X and p : x ＝ y
𝕁' X A f x y p = ℍ {X = X} x (A x) (f x) y p

𝕁s-agreement : (X : 𝓤 ̇ ) (A : (x y : X) → x ＝ y → 𝓥 ̇ )
               (f : (x : X) → A x x (refl x)) (x y : X) (p : x ＝ y)
             → 𝕁 X A f x y p ＝ 𝕁' X A f x y p

𝕁s-agreement X A f x x (refl x) = refl (f x)

transport : {X : 𝓤 ̇ }     -- Given a type X
            (A : X → 𝓥 ̇ ) -- A property on elements of X
            {x y : X}     -- And two elements x and y of X
          → x ＝ y →      -- And a proof that x = y
          A x → A y       -- Then if A holds for x, it holds for y
transport {𝓥  = 𝓥 } {X = X} A {x} {y} p = 
    𝕁 X 
      property-of-equality 
      proof-that-property-of-equality-holds-for-refl 
      x 
      y 
      p
  where 
    property-of-equality : (x y : X) → (p : x ＝ y) → 𝓥 ̇
    -- What is this property? Well given two elements and their
    -- equality, whatever it is, what we ultimately want is that A x 
    -- *implies* A y. The J rule gives us "A x y p", which we are free
    -- to choose as A x → A y. See the bottom line of the transport type
    -- signature!

    -- Yes this is not really a property "on the equality" in the sense
    -- that the equality is ignored; but it doesn't matter: we want this property
    -- to hold for all x y GIVEN a proof p that x = y. 
    property-of-equality = (λ x y _p  → A x → A y)

    proof-that-property-of-equality-holds-for-refl : (x₁ : X) → property-of-equality x₁ x₁ (refl x₁)
    -- Well what is `property-of-equality x₁ x₁ (refl x₁)`? It is `A x₁ → A x₁`!
    -- Just substitute its arguments: x becomes x₁, y becomes x₁ , _p becomes refl x₁, and it's done.
    -- It returns a type with all that substiuted: A x₁ → A x₁, and this type is exactly
    -- in the type signature of this function.
    proof-that-property-of-equality-holds-for-refl x₁ = id

{-
In the same way ℕ-recursion can be seen as the non-dependent special case of ℕ-induction,
the following transport function can be seen as the non-dependent special case of the 
＝-induction principle ℍ with some of the arguments permuted and made implicit:
-}
nondep-ℍ : {X : 𝓤 ̇ }              -- given a type
           (x : X)                -- an element x of that type
           (A : X → 𝓥 ̇ )          -- A property on all elements of that type
           → A x                  -- A proof that the property holds for x
           → (y : X)              -- Another element y of the same type
           → x ＝ y → A y         -- Then given a proof that x = y, I can prove A holds for y
nondep-ℍ x A = ℍ x (λ y _ → A y)

-- Aren't the arguments just in a different order?
transportℍ : {X : 𝓤 ̇ } 
             (A : X → 𝓥 ̇ ) 
             {x y : X}
           → x ＝ y
           → A x → A y
transportℍ A {x} {y} p a = nondep-ℍ x A a y p

-- I'm omitting the pattern matching-based transport
transports-agreement : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ＝ y)
                     → (transportℍ A p ＝ transport A p)
transports-agreement A (refl x) = refl (transport A (refl x))

{- 
The following is for use when we want to recover implicit arguments without mentioning them.
-}

lhs : {X : 𝓤 ̇ } {x y : X} → x ＝ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ＝ y → X
rhs {𝓤} {X} {x} {y} p = y


-- Transport is "non-dependent induction". I still don't see how. My version, needs awkward sym:
_∙'_ : {X : 𝓤 ̇ } 
      {x y z : X} 
      → x ＝ y
      → y ＝ z → x ＝ z
_∙'_ {X = X} {x = x} {y = y} {z = z} p q = transportℍ (λ (x : X) → x ＝ z) {x = y} {y = x} (sym p) q
  where sym : ∀ {x y} → x ＝ y → y ＝ x
        sym (refl x) = refl x

-- The book's version:
_∙_ : {X : 𝓤 ̇ } {x y z : X} → x ＝ y → y ＝ z → x ＝ z
p ∙ q = transport (lhs p ＝_) q p

_＝⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ＝ y → y ＝ z → x ＝ z
x ＝⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ＝ x
x ∎ = refl x

{-
Inversion of identifications. Given an identification, we get an 
identification in the opposite direction:
-}

_⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ＝ y → y ＝ x
p ⁻¹ = transport (_＝ lhs p) p (refl (lhs p))

{-
We can define an alternative of identification composition with this:
 HAHA! I already did it
-}

_∙''_ : {X : 𝓤 ̇ } {x y z : X} → x ＝ y → y ＝ z → x ＝ z
p ∙'' q = transport (_＝ rhs q) (p ⁻¹) q

∙agreement : {X : 𝓤 ̇ } {x y z : X} (p : x ＝ y) (q : y ＝ z)
           → (p ∙' q) ＝ (p ∙ q)
∙agreement (refl x) (refl x) = refl (refl x)

{- 
But refl y is a ***definitional*** neutral element for one of them on the 
right and for the other one on the left,

p ∙ refl y = p,
refl y ∙' q = q,
-}

rdnel : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y)
      → (p ∙ refl y) ＝ p
rdnel p = refl p

rdner : {X : 𝓤 ̇ } {y z : X} (q : y ＝ z)
      → (refl y  ∙' q) ＝ q
rdner q = refl q

-- Finally: AP!
ap : {X : 𝓤 ̇ }  {Y : 𝓥 ̇ } -- given two types
     (f : X → Y)           -- and a function between them
     {x x' : X}            -- and two elements of X
     → x ＝ x'             -- then give me a proof that they are equal
     → f x ＝ f x'         -- and i'll give you a proof that their images are equal
ap f {x = x} p = transport (λ x₁ → f x ＝ f x₁) p (refl (f x))
-- it's the same as cong?

_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
--  look at how fucked up this is. `domain` doesn't work well at all with dependent stuff
-- _∼_ {X = X} {A = A} f g = (x : domain {Y = (x : X) → A x} λ x → f) → f x ＝ g x
f ∼ g = ∀ x → f x ＝ g x

¬¬ ¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬  A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)

dni : (A : 𝓤 ̇ ) → A → ¬¬ A
dni = λ A x x₁ → x₁ x

{- 
Mathematically, this (above) says that if we have a point of A (we say that A is pointed)
then A is nonempty. There is no general procedure to implement the converse, that is,
from a function (A → 𝟘) → 𝟘 to get a point of A.
-}


-- It makes sense doesnt it: I have a function from a to b, but I have that b is
-- nonsense (empty). Therefore a must be empty also (in fact this function must be the identity).
contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ¬ B → ¬ A
contrapositive a→b ¬b = (¬b ∘ a→b)

tno : (A : 𝓤 ̇ ) → ¬¬¬ A → ¬ A
tno A = contrapositive (dni A)

-- Logical equivalence
_⇔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ⇔ Y = (X → Y) × (Y → X)

lr-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⇔ Y) → (X → Y)
lr-implication = pr₁

rl-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⇔ Y) → (Y → X)
rl-implication = pr₂

absurdity³-is-absurdity : {A : 𝓤 ̇ } → ¬¬¬ A ⇔ ¬ A
absurdity³-is-absurdity {𝓤} {A} = tno A , dni (¬ A)

_≠_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≠ y = ¬(x ＝ y)

_ : 3 ≠ 4 -- hehe
_ = λ {()} 

≠-sym : {X : 𝓤 ̇ } {x y : X} → x ≠ y → y ≠ x
≠-sym {x = x} {y = y} = λ (x₁ : x ≠ y) (x₂ : (y ＝ x)) → x₁ (x₂ ⁻¹)

-- Makes sense right? If two types are equal, there's obviously a way to give
-- a function from one to the other starting from an equality.
-- The other way to look at this is as just transport: given an equality between
-- two types, a property that applies to the first type (the identity) applies to
-- the second one. That's why id is passed here
Id→Fun : {X Y : 𝓤 ̇ } → X ＝ Y → X → Y
Id→Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇ ))

-- Why is this different? Well when you pattern match on the equality,
-- the compiler learns something: it learns that X and Y are the same type.
-- Therefore given an element of X (which is the same as an element of Y),
-- return an element of Y. Well it's the thing you were given!!!
Id→Fun' : {X Y : 𝓤 ̇ } → X ＝ Y → X → Y
Id→Fun' (refl X) = 𝑖𝑑 X

Id→Funs-agree : {X Y : 𝓤 ̇ } (p : X ＝ Y)
              → Id→Fun p ＝ Id→Fun' p
Id→Funs-agree (refl X) = refl (𝑖𝑑 X)

{-
So if we have a hypothetical identification p : 𝟙 ＝ 𝟘, then we get a function 𝟙 → 𝟘.
We apply this function to ⋆ : 𝟙 to conclude the proof.
-}
𝟙-is-not-𝟘 : 𝟙 ≠ 𝟘
𝟙-is-not-𝟘 p = Id→Fun p ⋆

-- THIS IS SO INSANE DUDE.
-- The values ₁ and ₀ are of a totally different type, has nothing whatsoever
-- to do with 𝟙 and 𝟘, except that they're members of the sum 𝟙 + 𝟙. What is the type of
-- 𝟙-is-not-𝟘 really? It's `Id Set 𝟙 𝟘 → 𝟘`. So it always takes a proof that 𝟙 ＝ 𝟘, ok.
-- And then what is the type of ₁ ≠ ₀? Well it's `Id (𝟙 + 𝟙) ₁ ₀ → 𝟘` So they have the
-- same target, 𝟘. So I can use 𝟙-is-not-𝟘 to produce the value of the output of ₁-is-not-₀
-- (a value of 𝟘). It's just that I need an argument of type `Id Set 𝟙 𝟘` then, and I have a
-- hypothetical argument that ₁ ＝ ₀. So I can just transform either side of this hypothetical
-- "equality" to the type Set, by using `ap`.
₁-is-not-₀ : ₁ ≠ ₀
₁-is-not-₀ p = 𝟙-is-not-𝟘 hypothetical-1=0
  where
    f : 𝟙 + 𝟙 → Set
    f ₀ = 𝟘
    f ₁ = 𝟙
    hypothetical-1=0 : 𝟙 ＝ 𝟘
    hypothetical-1=0 = ap f p

-- The empty pattern really does feel like cheating :sob:  
₁-is-not-₀[not-an-MLTT-proof] : ¬(₁ ＝ ₀)
₁-is-not-₀[not-an-MLTT-proof] ()

-- WHAT??????
-- WHY is this not annoying me due to incmplete patterns and shit????? f is not
-- even a total function!! If I make it a total function I get this warning:
-- warning: -W[no]CoverageNoExactSplit
-- Exact splitting is enabled, but the following clause could not be
-- preserved as definitional equalities in the translation to a case
-- tree:
--   f x = 𝟘
-- when checking the definition of f
-- WHAT IS HAPPENING!!
two-is-not-four : 4 ≠ 2
two-is-not-four  p = 𝟙-is-not-𝟘 hypothetical-1=0
  where
    f : ℕ → Set
    f (succ (succ zero)) = 𝟘
    f (succ (succ (succ (succ zero)))) = 𝟙
    hypothetical-1=0 : 𝟙 ＝ 𝟘
    hypothetical-1=0 = ap f  p

-- 14/03/2024
decidable : 𝓤 ̇ → 𝓤 ̇
decidable A = A + ¬ A

has-decidable-equality : 𝓤 ̇ → 𝓤 ̇
has-decidable-equality X = (x y : X) → decidable (x ＝ y)

-- Give me two values of 1 + 1 and I'll give you either a proof of their equality or of their inequality
𝟚-has-decidable-equality : has-decidable-equality 𝟚 -- (x y : 𝟙 + 𝟙) →  x ＝ y + ¬ (x ＝ y)
𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-equality ₀ ₁ = inr (≠-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)

-- Given n and a proof that it's not 0, i'll give you a proof it's 1.
-- What are the cases? Either the value is 0 and the proof is nonsense, or the value is 1.
-- If the proof is nonsense, it means it can generate a value of 0. And a value of 0
-- can be fed to !𝟘 to generate a value of any type. Since in the first pattern we need to
-- prove that n (taking the value of ₀) is ₁, we can just say that the type we want the value
-- of is 0 = 1. Then we use not0 to generate a value of 0 from a value of ₀ = ₀ and feed that
-- to !0. In the second pattern, we just return refl ₁, definitional. 
not-zero-is-one : (n : 𝟚) → n ≠ ₀ → n ＝ ₁
not-zero-is-one ₀ not0 = !𝟘 (₀ ＝ ₁) (not0 (refl ₀)) 
not-zero-is-one ₁ not0 = refl ₁

-- Generalization
inl-inr-disjoint-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → inl x ≠ inr y
inl-inr-disjoint-images p = 𝟙-is-not-𝟘 one-is-zero
  where
    -- Maybe this is why the version on natural numbers above works. The natural numbers
    -- can of course be seen as a sum of sets, but how did the compiler know that it was
    -- not necessary to check all constructors for it? It just seems like it was *too smart*
    f : ∀ {X Y} → X + Y → 𝓤₀ ̇
    f (inl x) = 𝟙
    f (inr x) = 𝟘
    one-is-zero : 𝟙 ＝ 𝟘
    one-is-zero = ap f p

right-fails-gives-left-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → P + Q → ¬ Q → P
right-fails-gives-left-holds (inl p) notq = p
right-fails-gives-left-holds {P = P} (inr q) notq = !𝟘 P (notq q)

module ℕ-order where
  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  0      ≤ y      = 𝟙
  succ x ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x

  infix 10 _≤_
  infix 10 _≥_


module twin-primes where

 open Arithmetic renaming (_×_ to _*_ ; _+_ to _∔_)
 open ℕ-order

 is-prime : ℕ → 𝓤₀ ̇
 is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ＝ n → (x ＝ 1) + (x ＝ n))

 twin-prime-conjecture : 𝓤₀ ̇
 twin-prime-conjecture = (n : ℕ) → Σ p ꞉ ℕ ,  ((p ≥ n) × (is-prime p) × (is-prime (p ∔ 2)))

{-
Thus, not only can we write down definitions, constructions, theorems and proofs, but also conjectures.
They are just definitions of types. Likewise, the univalence axiom, to be formulated in due course, is a type.

-- of course right? they're mathematical statements/propositions. Whether they're inhabited
-- or not determines whether they're true or false.
-}

-- Peano axioms
positive-not-zero : (x : ℕ) → succ x ≠ 0
positive-not-zero x p = 𝟙-is-not-𝟘 (g p)
 where
  -- Here we are again...................
  f : ℕ → 𝓤₀ ̇
  f 0        = 𝟘
  f (succ x) = 𝟙

  g : succ x ＝ 0 → 𝟙 ＝ 𝟘
  g = ap f

pred : ℕ → ℕ
pred 0        = 0
pred (succ n) = n

succ-left-cancellable : {x y : ℕ} → succ x ＝ succ y → x ＝ y
succ-left-cancellable p = ap pred p

-- Without assuming excluded middle!
ℕ-has-decidable-equality : has-decidable-equality ℕ -- (x y : ℕ) → decidable (x ＝ y) => (x ＝ y) + ¬ (x ＝ y)
ℕ-has-decidable-equality zero zero = inl (refl zero)
ℕ-has-decidable-equality zero (succ y) = inr (≠-sym ( positive-not-zero y )) 
ℕ-has-decidable-equality (succ x) zero = inr (positive-not-zero x)
ℕ-has-decidable-equality (succ x) (succ y) = t (ℕ-has-decidable-equality x y)
  where 
    t : decidable (x ＝ y) → decidable (succ x ＝ succ y)
    t (inl p) = inl (ap succ p)
    t (inr ¬p) = inr λ (psucc : succ x ＝ succ y) → ¬p (ap pred psucc)


{-
Exercise. Students should do this kind of thing at least once in their academic life:
rewrite the above proof of the decidability of equality of ℕ to use the ℕ-induction 
principle instead of pattern matching and recursion, to understand by themselves 
that this can be done.
-}


-- Fuckin hell. Alright I don't see how to avoid pattern matching D:

-- succ-is-not : (x : ℕ) → succ x ≠ x
-- succ-is-not x = ℕ-induction (λ x₁ → succ x₁ ≠ x₁) 
--                             (positive-not-zero zero) 
--                             (λ n ¬succ succsucc → ¬succ (ap pred succsucc)) 
--                             x

-- 0-is-dec : (y : ℕ) → decidable (0 ＝ y)
-- 0-is-dec x = ℕ-induction (λ x₁ → decidable (0 ＝ x₁))   -- A property on the natural numbers
--                          (inl (refl 0))                 -- A proof that the property holds for 0
--                          (λ n x₁ → inr λ (x₂ : 0 ＝ succ n) → positive-not-zero n (x₂ ⁻¹)) -- A way to prove that if the property holds for n, it holds for succ n
--                          x

-- bimap-sum : {X Y Z W : 𝓤 ̇ } → (X → Y) → (Z → W) → (X + Z) → (Y + W)
-- bimap-sum f g (inl x) = inl (f x)
-- bimap-sum f g (inr z) = inr (g z)


-- 1-is-dec : (y : ℕ) → decidable (y ＝ 1)
-- 1-is-dec y = ℕ-induction (λ x → decidable (x ＝ 1)) 
--                          (inr (≠-sym (positive-not-zero zero)))
--                          {!   !}
--                          {!   !}

-- succ-is-dec : {n : ℕ} → (y : ℕ) → decidable (n ＝ y) → decidable (n ＝ succ y)
-- succ-is-dec {n} y p = +-induction (λ (x : decidable (n ＝ y)) → {!   !}) 
--                                   {!   !} {!   !} {!   !}

-- if-dec-n-then-dec-succn : {n : ℕ} → ((y : ℕ) → decidable (n ＝ y)) → (y : ℕ) → decidable (succ n ＝ y)
-- if-dec-n-then-dec-succn {n} decn y = ℕ-induction (λ x → decidable (succ n ＝ x)) 
--                                                  (bimap-sum (λ x → x ⁻¹) ≠-sym (0-is-dec (succ n))) 
--                                                  succ-is-dec 
--                                                  y
-- ℕ-has-decidable-equality-ind : has-decidable-equality ℕ
-- ℕ-has-decidable-equality-ind = 
--         induction-principle-reminder (λ x → (y : ℕ) → decidable (x ＝ y)) -- The property ON THE NATURALS - i.e. FORALL naturals, not for the set as a "point"
--                                      0-is-dec  -- It holds for 0
--                                      λ n → if-dec-n-then-dec-succn {n}   -- If it holds for n, it holds for succ n
--   where induction-principle-reminder : {𝓤 : Universe} 
--                    (A : ℕ → 𝓤 ̇) -- Given a property on the natural numbers
--                    → A 0        -- A proof that the property holds for 0
--                    → ((n : ℕ) → A n → A (succ n)) -- A way to prove that if the property holds for n, it holds for succ n
--                    → (n : ℕ) → A n  -- Then give me a natural number and I'll give you a proof that the property holds for it
--         induction-principle-reminder = ℕ-induction


module basic-arithmetic-and-order where

  open ℕ-order public
  open Arithmetic renaming (_+_ to _∔_) hiding (_×_)
  +-assoc : (x y z : ℕ) → (x ∔ y) ∔ z ＝ x ∔ (y ∔ z)
  +-assoc x y 0        = refl _

  -- this REALLY needs =⟨_⟩ to be infixr lol
  +-assoc x y (succ z) = (x ∔ y) ∔ succ z   ＝⟨ refl _     ⟩
                         succ ((x ∔ y) ∔ z) ＝⟨ ap succ IH ⟩
                         succ (x ∔ (y ∔ z)) ＝⟨ refl _     ⟩
                         x ∔ (y ∔ succ z)   ∎
   where
    IH : (x ∔ y) ∔ z ＝ x ∔ (y ∔ z)
    IH = +-assoc x y z

{-
Notice that the proofs refl _ should be read as “by definition” or “by construction”.
They are not necessary, because Agda knows the definitions and silently expands
them when necessary, but we are writing them here for the sake of clarity. Here is
the version with the silent expansion of definitions, for the sake of illustration
(the author of these notes can write, but not read it the absence of the above verbose version):
-}
  +-assoc' : (x y z : ℕ) → (x ∔ y) ∔ z ＝ x ∔ (y ∔ z)
  +-assoc' x y zero     = refl _
  +-assoc' x y (succ z) = ap succ (+-assoc' x y z)


-- There's a bunch more stuff in the tutorial for the arithmetic and order,
-- but now I want to move on to univalence finally.

{- Univalent Mathematics in Agda

Our univalent type theory
* A spartan MLTT as above.
* Univalence axiom as below.
* Subsingleton (or truth-value or propositional) truncations as below.
But, as discussed above, rather than postulating univalence and truncation,
we will use them as explicit assumptions each time they are needed.
-}

-- or contractible
is-singleton : 𝓤 ̇ → 𝓤 ̇
is-singleton X = Σ c ꞉ X , ((x : X) → c ＝ x)

-- Already a question: if a type is contractible, isn't every inhabitant 
-- a center of contraction, due to transitivity of equality?
is-center : (X : 𝓤 ̇ ) → X → 𝓤 ̇
is-center X c = (x : X) → c ＝ x

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , 𝟙-induction (λ x → ⋆ ＝ x) (refl ⋆)

center : (X : 𝓤 ̇ ) → is-singleton X → X
center X (c , φ) = c

centrality : (X : 𝓤 ̇ ) (i : is-singleton X) (x : X) → center X i ＝ x
centrality X (c , φ) = φ

{-
A type is a subsingleton (or proposition) if it has at most one element, 
that is, any two of its elements are equal, or identified.
-}
is-subsingleton : 𝓤 ̇ → 𝓤 ̇
is-subsingleton X = (x y : X) → x ＝ y
-- compare with     Σ c ꞉ X , ((x : X) → c ＝ x)
-- the difference between these two is that is-subsingleton gives the possibility
-- of "vacuous population": if X has no inhabitants, then it is true vacuously that
-- forall x y : X , x = y. But is-singleton starts with THERE EXISTS (encoded in a Sigma)

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = !𝟘 (x ＝ y) x

singletons-are-subsingletons : (X : 𝓤 ̇ ) → is-singleton X → is-subsingleton X
singletons-are-subsingletons X (c , φ) x y = x ＝⟨ (φ x)⁻¹ ⟩
                                             c ＝⟨ φ y     ⟩
                                             y ∎

𝟙-is-subsingleton : is-subsingleton 𝟙
𝟙-is-subsingleton = singletons-are-subsingletons 𝟙 𝟙-is-singleton

pointed-subsingletons-are-singletons : (X : 𝓤 ̇ ) → X → is-subsingleton X → is-singleton X
pointed-subsingletons-are-singletons X x s = (x , s x)


singleton-iff-pointed-and-subsingleton : {X : 𝓤 ̇ } → is-singleton X ⇔ (X × is-subsingleton X)
singleton-iff-pointed-and-subsingleton {𝓤} {X} = (a , b)
 where
  a : is-singleton X → X × is-subsingleton X
  a s = center X s , singletons-are-subsingletons X s

  b : X × is-subsingleton X → is-singleton X
  b (x , t) = pointed-subsingletons-are-singletons X x t

{-
The terminology stands for subtype of a singleton and is justified
by the fact that a type X is a subsingleton according to the above
definition if and only if the map X → 𝟙 is an embedding, if and only
if X is embedded into a singleton.
-}

is-prop is-truth-value : 𝓤 ̇ → 𝓤 ̇
is-prop        = is-subsingleton
is-truth-value = is-subsingleton

{- 
In univalent mathematics, however, propositions are mathematical, 
rather than meta-mathematical, objects, and the fact that a type 
turns out to be a proposition requires mathematical proof. Moreover, 
such a proof may be subtle and not immediate and require significant 
preparation. An example is the proof that the univalence axiom is a proposition (!!!!!!!!!!),
which relies on the fact that univalence implies function extensionality, 
which in turn implies that the statement that a map is an equivalence is a 
proposition. Another non-trivial example, which again relies on univalence 
or at least function extensionality, is the proof that the statement that a
type X is a proposition is itself a proposition, which can be written as is-prop (is-prop X) (!!!!!!).

Singletons and subsingletons are also called -2-groupoids and -1-groupoids respectively.
-- just Totally Insane.
-}

{- A type is defined to be a set if there is at most one way
for any two of its elements to be equal: -}
-- Justifies "equality is data". An equality can absolutely be the same
-- or different from another equality, but not for ELEMENTS of a set: given
-- data MySet : Set where a b c : MySet, a is either equal to some x : MySet or it
-- isn't; true/false. however, for elements of Set i.e. the type of sets, there
-- are many different equalities. MySet is equal to Fin 3 under several different isos.
is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ＝ y)

-- Here's excluded middle: we're not PROVING it, we're just STATING it, i.e.
-- representing it as a type. What EM says is: "Given a type, if it is a subsingleton
-- i.e. a proposition that can be true or false, then either it is true or it is false".
EM EM' : ∀ 𝓤 → 𝓤 ⁺ ̇
EM  𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → X + ¬ X
EM' 𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → is-singleton X + is-empty X

EM-gives-EM' : EM 𝓤 → EM' 𝓤
EM-gives-EM' em X s = γ (em X s)
 where
  γ : X + ¬ X → is-singleton X + is-empty X
  γ (inl x) = inl (pointed-subsingletons-are-singletons X x s)
  γ (inr ν) = inr ν

EM'-gives-EM : EM' 𝓤 → EM 𝓤
EM'-gives-EM em' X s = γ (em' X s)
 where
  γ : is-singleton X + is-empty X → X + ¬ X
  γ (inl i) = inl (center X i)
  γ (inr e) = inr e

{-
We will not assume or deny excluded middle, which is an independent statement in our spartan
univalent type theory - it can’t be proved or disproved, just as the parallel postulate in
Euclidean geometry can’t be proved or disproved. We will deliberately keep it undecided, adopting
a neutral approach to the constructive vs. non-constructive dichotomy. We will however prove
a couple of consequences of excluded middle in discussions of foundational issues such as size
and existence of subsingleton truncations. We will also prove that excluded middle is a consequence
of the axiom of choice.
-}

{-
It should be emphasized that the potential failure of excluded middle doesn’t say that
there may be mysterious subsingletons that fail to be singletons and also fail to be empty.
No such things occur in mathematical nature:
-}
-- So it's not like there is a type that IS a subsingleton but is NOT a singleton AND is NOT empty.
-- If you are a subsingleton and not a singleton, you must be empty.
no-unicorns : ¬(Σ X ꞉ 𝓤 ̇ , is-subsingleton X × ¬(is-singleton X) × ¬(is-empty X))
no-unicorns (X , i , f , g) = c
 where
  e : is-empty X
  e x = f (pointed-subsingletons-are-singletons X x i)

  c : 𝟘
  c = g e



subsing-is-either-sing-or-empty : {X : 𝓤 ̇} → is-subsingleton X → ¬¬(is-singleton X + is-empty X)
subsing-is-either-sing-or-empty {X = X} s x = 
    x -- The sigma inside inl is a is-singleton proof, so wont work: (inl ({! {- Needs an x - cannot get from anywhere -}  !} , {!   !}))
      (inr λ x₁ → -- But here, we are giving a is-empty proof (x → 𝟘). Therefore it *introduces* an x
        -- We still need to produce a 𝟘. Well x is what does it, but now we have an X in scope:
        x (inl (x₁ , (s x₁))))

cps-thing : {X : 𝓤 ̇} → {R : 𝓤 ̇} → ((X + (X → R)) → R) → R
cps-thing x = x (inr (λ x₁ → x (inl x₁)))


module magmas where

 Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
 Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , is-set X × (X → X → X)
 ⟨_⟩ : Magma 𝓤 → 𝓤 ̇
 ⟨ X , i , _·_ ⟩ = X

 magma-is-set : (M : Magma 𝓤) → is-set ⟨ M ⟩
 magma-is-set (X , i , _·_) = i

 magma-operation : (M : Magma 𝓤) → ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
 magma-operation (X , i , _·_) = _·_

 syntax magma-operation M x y = x ·⟨ M ⟩ y

 is-magma-hom : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
 is-magma-hom M N f = (x y : ⟨ M ⟩) → f (x ·⟨ M ⟩ y) ＝ f x ·⟨ N ⟩ f y

 id-is-magma-hom : (M : Magma 𝓤) → is-magma-hom M M (𝑖𝑑 ⟨ M ⟩)
 id-is-magma-hom M x y = refl (id (x ·⟨ M ⟩  y))

 is-magma-iso : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
 is-magma-iso M N f = is-magma-hom M N f
                    × (Σ g ꞉ (⟨ N ⟩ → ⟨ M ⟩), is-magma-hom N M g
                                            × (g ∘ f ∼ 𝑖𝑑 ⟨ M ⟩)
                                            × (f ∘ g ∼ 𝑖𝑑 ⟨ N ⟩))

 id-is-magma-iso : (M : Magma 𝓤) → is-magma-iso M M (𝑖𝑑 ⟨ M ⟩)
 id-is-magma-iso M = id-is-magma-hom M ,
                     𝑖𝑑 ⟨ M ⟩ ,
                     id-is-magma-hom M ,
                     refl ,
                     refl

 Id→iso : {M N : Magma 𝓤} → M ＝ N → ⟨ M ⟩ → ⟨ N ⟩
 Id→iso p = transport ⟨_⟩ p

 Id→iso-is-iso : {M N : Magma 𝓤} (p : M ＝ N) → is-magma-iso M N (Id→iso p)
 Id→iso-is-iso (refl M) = id-is-magma-iso M

 _≅ₘ_ : Magma 𝓤 → Magma 𝓤 → 𝓤 ̇
 M ≅ₘ N = Σ f ꞉ (⟨ M ⟩ → ⟨ N ⟩), is-magma-iso M N f

-- 15/03/2024
 







infix   0 _∼_
infixr 50 _,_
infixr 30 _×_
infixr 20 _+_
infixl 70 _∘_
infix   0 Id
infix   0 _＝_
infix  10 _⇔_
infixl 30 _∙_
infixr  0 _＝⟨_⟩_
infix   1 _∎
infix  40 _⁻¹
--infix  10 _◁_
--infixr  0 _◁⟨_⟩_
--infix   1 _◀
--infix  10 _≃_
--infixl 30 _●_
--infixr  0 _≃⟨_⟩_
--infix   1 _■
--infix  40 _∈_
--infix  30 _[_,_]
infixr -1 -Σ
infixr -1 -Π
--infixr -1 -∃!