
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
