
/-
We will see below that the arguments of the constructors can include objects
of type Foo, subject to a certain "positivity" constraint, which guarantees
that elements of Foo are built from the bottom up. Roughly speaking, each ...
can be any arrow type constructed from Foo and previously defined types, in
which Foo appears, if at all, only as the "target" of the dependent arrow type.
-/
-- Where have I seen this before? Somewhere in Haskell. Like GADTs have constructors
-- that consume them.

inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  deriving Repr

open Weekday -- the fuck. This really necessary huh

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

-- OMG YOU CAN PRINT FUNCTION DEFINITIONS!!
set_option pp.all true
#print numberOfDay
-- ... numberOfDay.match_1
-- WTF this is broken by deriving Repr: #print numberOfDay.match_1
-- ... Weekday.casesOn ...
#print Weekday.casesOn
-- ... Weekday.rec ...
#check @Weekday.rec
/-
@Weekday.rec.{u}
 : {motive : Weekday → Sort u} →
    motive Weekday.sunday →
    motive Weekday.monday →
    motive Weekday.tuesday →
    motive Weekday.wednesday →
    motive Weekday.thursday →
    motive Weekday.friday →
    motive Weekday.saturday →
    (t : Weekday) → motive t
-/

namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl

end Weekday

def next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl -- good lord this tactics business is just crazy. just what are they?

-- wtf is this
def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)

/-
The argument motive is used to specify the type of the object you want
to construct, and it is a function because it may depend on the pair.
-/
-- "object you want to construct." Construct out of what?


def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)


/-
There are rules that govern what the eliminator of an inductive type
can eliminate to, that is, what kinds of types can be the target of a
recursor. Roughly speaking, what characterizes inductive types in Prop
is that one can only eliminate to other types in Prop. This is
consistent with the understanding that if p : Prop, an element hp : p
carries no data.
-/


#check @Nat.rec
/-
   {motive : Nat → Sort u}
  → motive Nat.zero
  → ((n : Nat) → motive n → motive (Nat.succ n))
  → (t : Nat) → motive t
The implicit argument, motive, is the codomain of the function being
defined. In type theory it is common to say motive is the motive for
the elimination/recursion, since it describes the kind of object we
wish to construct. The next two arguments specify how to compute the
zero and successor cases, as described above. They are also known as
the minor premises. Finally, the t : Nat, is the input to the function.
It is also known as the major premise.
-/
-- heh. see Intro to HoTT

/-
As another example, let us prove the associativity of addition, ∀ m n k,
m + n + k = m + (n + k). The hardest part is figuring out which variable to
do the induction on. Since addition is defined by recursion on the second
argument, k is a good guess, and once we make that choice the proof almost
writes itself:
-/
-- Induction on k huh?
open Nat
example (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + succ k = m + (n + succ k) from
      calc m + n + succ k
        _ = succ (m + n + k)   := rfl
        _ = succ (m + (n + k)) := by rw [ih]
        _ = m + succ (n + k)   := rfl
        _ = m + (n + succ k)   := rfl)

namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl

-- Exercise: prove the following lemmas about append
theorem append_nil (as : List α) : append as nil = as :=
  List.recOn (motive := λ as ↦ append as nil = as) as
    (show append nil nil = nil from rfl)
    (λ h t ih => show append (cons h t) nil = cons h t from
      calc append (cons h t) nil
           _ = cons h (append t nil) := rfl
           _ = cons h t           := by rw [ih])

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  List.recOn (motive := λ cs ↦ append (append as bs) cs = append as (append bs cs))
    cs
    (show append (append as bs) nil = append as (append bs nil) from
      calc append (append as bs) nil
           _ = append as bs := by rw [append_nil]
           _ = append as (append bs nil) := by rw [append_nil])
    (λ h t ih => show append (append as bs) (cons h t) = append as (append bs (cons h t)) from
      -- GODDAMN this syntax is horrible. doing things with recOn is so cursed
      -- the induction principle in general (for any type) is just so hard to have land
      -- on me brain comfortably. especially when the types here look like
      -- α: Type u_1
      -- asbscs: Hidden.List.{u_1} α
      -- h: α
      -- t: Hidden.List.{u_1} α
      -- ih: (fun (cs : Hidden.List.{u_1} α) =>
      --     @Eq.{u_1 + 1} (Hidden.List.{u_1} α) (@Hidden.List.append.{u_1} α (@Hidden.List.append.{u_1} α as bs) cs)
      --       (@Hidden.List.append.{u_1} α as (@Hidden.List.append.{u_1} α bs cs)))
      --   t
      -- ⊢ (fun (cs : Hidden.List.{u_1} α) =>
      --     @Eq.{u_1 + 1} (Hidden.List.{u_1} α) (@Hidden.List.append.{u_1} α (@Hidden.List.append.{u_1} α as bs) cs)
      --       (@Hidden.List.append.{u_1} α as (@Hidden.List.append.{u_1} α bs cs)))
      --   (@Hidden.List.cons.{u_1} α h t)
      _
      )
end List
end Hidden


example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz  -- goal is p 0
  . apply hs  -- goal is a : Nat ⊢ p (succ a)

/-
There are extra bells and whistles. For one thing, cases allows you to
choose the names for each alternative using a with clause. In the next
example, for example, we choose the name m for the argument to succ, so
that the second case refers to succ m. More importantly, the cases tactic
will detect any items in the local context that depend on the target
variable. It reverts these elements, does the split, and reintroduces
them. In the example below, notice that the hypothesis h : n ≠ 0 becomes
h : 0 ≠ 0 in the first branch, and h : succ m ≠ 0 in the second.
-/

open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
    -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    apply absurd rfl h
  | succ m =>
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    rfl

inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo
def silly (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b

/-
If the expression you case on does not appear in the goal, the cases
tactic uses have to put the type of the expression into the context.
Here is an example:
-/
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge



-- Tf is this. Some kind of infinite tree
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree
namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree


end CBTree

/-
Just as the cases tactic can be used to carry out proof by cases, the
induction tactic can be used to carry out proofs by induction. The syntax
is similar to that of cases, except that the argument can only be a term
in the local context. Here is an example:
-/
namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
end Hidden

/-
We close this section with one last tactic that is designed to facilitate
working with inductive types, namely, the injection tactic. By design,
the elements of an inductive type are freely generated, which is to say,
the constructors are **injective** and have disjoint ranges. The injection
tactic is designed to make use of this fact:
-/
open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h' -- h' : succ m = succ n
  injection h' with h'' -- h'' : m = n
  rw [h''] -- this is REALLY NICE



----- INDUCTIVE FAMILIES

/-
An inductive family is an indexed family of types defined
by a simultaneous induction of the following form: -- simultaneous??

inductive foo : ... → Sort u where
  | constructor₁ : ... → foo ...
  | constructor₂ : ... → foo ...
  ...
  | constructorₙ : ... → foo ...
-/

-- So yes ok, the thing to the right of the colon is the index
-- for each element in the index, you get one concrete different
-- type, fine. fine fine fine fine fine

-- so what do the constructors create here?
inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0     -- The single element of all types Vector α 0.
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1) -- from an element of Vector α n and an α, you get an element of ANOTHER type

/-
Notice that the cons constructor takes an element of Vector α n and
returns an element of Vector α (n+1), thereby using an element of one
member of the family to build an element of another.
-/


/-
A more exotic example is given by the definition of the equality type in Lean:
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
For each fixed α : Sort u and a : α, this definition constructs a family of types
Eq a x, indexed by x : α. Notably, however, there is only one constructor, refl,
which is an element of Eq a a. Intuitively, the only way to construct a proof of
Eq a x is to use reflexivity, in the case where x is a. Note that Eq a a is the
only inhabited type in the family of types Eq a x. The elimination principle
generated by Lean is as follows:
-/
universe u v
#check (@Eq.rec : {α : Sort u} → {a : α} → {motive : (x : α) → a = x → Sort v}
                  → motive a rfl → {b : α} → (h : a = b) → motive b h)

-- So basically what happens is: By defining the family, you define a bunch of types
-- One can think of a family as a giant hashmap where the keys are types and the
-- values are functions from two inhabitants of that type to a Prop. The prop is true
-- (inhabited) if the two inhabitants are equal and false otherwise; but the thing is
-- the TYPE 1 = 2 still exists and is represented by the family; it's just not inhabited.
-- But it is just as "real" and valid as a type as Empty.

/-
The recursor Eq.rec is also used to define substitution:
-/
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : a = b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁



/-
You can also define subst using match.
-/


theorem subst2 {α : Type u} {a b : α} {p : α → Prop} (h₁ : a = b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂


/-
Actually, Lean compiles the match expressions using a definition based on Eq.rec.
-/
namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

set_option pp.all true
#print subst
  -- ... subst.match_1 ...
#print subst2.match_1
  -- ... Eq.casesOn ...
#print Eq.casesOn
  -- ... Eq.rec ...
end Hidden

-- Interesting internal details of Lean. It makes sense that match gets compiled down
-- to the induction principle, it actually explains "cognitively" why depedently typed
-- programming is soooo intuitive with pattern matching but so hard when explicitly invoking
-- the induction principle.

/-
We have seen that the constructor to an inductive type takes parameters --- intuitively,
the arguments that remain fixed throughout the inductive construction --- and indices,
the arguments parameterizing the family of types that is simultaneously under construction.
-/

-- Is this what is meant by "fix one of the endpoints" of an equality? I think I finally understand
-- the difference between a parameter and and index then.

-- For instance, the below can never work:
-- inductive Vector2 (α : Type u) (n : Nat) : Type u where
--   | nil  : Vector2 α 0
--   | cons : α → Vector2 α n → Vector2 α (n+1)
-- Because here, n is a parameter and not an index, so the constructors are getting to decide
-- what the type is. It just doesn't work. The constructors of this type are straight up "overriding"
-- the caller's choice of n. I think it belongs to the realm of "not even wrong". Like imagine the following:

-- inductive EitherInt (α β : Type u) : Type u where
--   | leftInt : Int → EitherInt Int β
--   | left : α → EitherInt α β
--   | right : β → EitherInt α β

-- It's just babble. What this is trying to represent somehow is a type that either
-- contains an integer, or a left α or a right β. But the correct version would be
-- to include leftInt in the type Either α β, which is the parametrized type we're defining.
-- Two things that "work" are these:

inductive Vector3 (α : Type u) (n : Nat) : Type u where
  | nil  : Vector3 α n
  | cons : α → Vector3 α n → Vector3 α n

inductive Vector4 (α : Type u) : (n : Nat) → Type u where
  | nil  : Vector4 α 0
  | cons : α → Vector4 α 0 → Vector4 α 1
  | cons2 : α → Vector4 α 1 → Vector4 α 2

-- But the first one is just a list with a phantom type parameter n! The second
-- one is indexed by all natural numbers, but what it says is basically it only covers
-- a part of its indexing. You're basically defining a whole family of types, one for each natural
-- number, but only 3 of them are inhabited - namely Vector4 α 0, Vector4 α 1 and Vector4 α 2.

-- If I was better at Lean i'd be able to do an empty pattern match on this to prove that:
example (p : n > 3) (a : Vector4 α n) : Empty := sorry


-- The restriction in the book makes total sense:

/-
Each constructor should have a type, where the argument types are built up from previously defined types,
the parameter and index types, and the inductive family currently being defined. The requirement is that
if the latter is present at all, it occurs only **strictly positively**.

This means simply that any argument to the constructor in which it occurs is a dependent arrow type
in which the inductive type under definition occurs only as the resulting type, where the indices
are given in terms of constants and previous arguments.
-/

-- At some point I had the intuition that "indexes are outputs from the constructors", and that
-- parameters are inputs to the type somehow. I think this is a formal articulation of that intuition.

-- Mutually inductive types:

mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end

-- Finite trees with nodes labeled by elements of α:
mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end

/-
This definition is inconvenient to work with, however. It would be much nicer if the list
of subtrees were given by the type List (Tree α), especially since Lean's library contains
a number of functions and theorems for working with lists. One can show that the type
TreeList α is isomorphic to List (Tree α), but translating results back and forth along
this isomorphism is tedious.

In fact, Lean allows us to define the inductive type we really want:
-/
inductive TreeWeWant (α : Type u) where
  | mk : α → List (TreeWeWant α) → TreeWeWant α
