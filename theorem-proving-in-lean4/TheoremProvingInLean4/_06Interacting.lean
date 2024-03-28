section
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end


-- Namespaces - protected keyword forces stuff to be namespaced
protected def Foo.bar : Nat := 1

open Foo

-- #check bar -- error
#check Foo.bar

-- Arguments to opening namespaces
open Nat (succ zero gcd)
#check zero     -- Nat
#eval gcd 15 6  -- 3

open Nat hiding succ gcd
#check zero     -- Nat
-- #eval gcd 15 6  -- error
#eval Nat.gcd 15 6  -- 3

-- they really are kind of like Agda's modules

open Nat renaming mul → times, add → plus
#eval plus (times 2 2) 3  -- 7


def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

-- Tagging explicitly with the attribute is necessary if
-- we want it to be local to this file
attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

example (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [simp] List.isPrefix_self


instance : LE (List α) where
  le := isPrefix -- IT ACTUALLY DOES TYPE CHECK

-- very very good
example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩


---- Implicit argments being fed eagerly (?)
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} => -- nicee
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} => -- nice
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
 th2 (th1 reflr @euclr) @euclr
 /- the @ operator makes all of the arguments to a theorem or definition explicit-/

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- r ?m1 ?m2 → r ?m1 ?m3 → r ?m2 ?m3
#check @euclr


-- Notation
-- huh. Adding a namespace or section or even local here
-- do not stop the notation from being defined globally
--local
  -- infixl:65   " + " => HAdd.hAdd  -- left-associative
  -- infix:50    " = " => Eq         -- non-associative
  -- infixr:80   " ^ " => HPow.hPow  -- right-associative
  -- prefix:100  "-"   => Neg.neg
  -- set_option quotPrecheck false
  -- postfix:max "⁻¹"  => Inv.inv

  -- -- WOOW clever. left-associative just means "right hand
  -- -- side has higher precedence".
  -- notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
  -- notation:50 lhs:50 " = " rhs:50 => Eq lhs rhs
  -- notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
  -- notation:100 "-" arg:100 => Neg.neg arg
  -- set_option quotPrecheck false
  -- notation:1024 arg:1024 "⁻¹" => Inv.inv arg  -- `max` is a shorthand for precedence 1024

/-
where the precedences do not sufficiently determine associativity,
Lean's parser will default to right associativity. More precisely,
Lean's parser follows a local longest parse rule in the presence of
ambiguous grammars: when parsing the right-hand side of a ~ in
a ~ b ~ c, it will continue parsing as long as possible (as the
current precedence allows), not stopping after b but parsing ~ c
as well. Thus the term is equivalent to a ~ (b ~ c).
-/


set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4
#reduce (fun x => x + 2) = (fun x => x + 3) --difference btwn reduce and eval?
#check (fun x => x + 1) 1


-- they really do be relyin on convention
/-
Lean's library developers follow general naming guidelines to make
it easier to guess the name of a theorem you need, or to find it
using tab completion in editors with a Lean mode that supports this,
which is discussed in the next section. Identifiers are generally
camelCase, and types are CamelCase. For theorem names, we rely on
descriptive names where the different components are separated by _s.
-/


def compose.{u, v, w}
            {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

/-
Lean 4 supports a new feature called auto bound implicit arguments.
It makes functions such as compose much more convenient to write. When Lean
processes the header of a declaration, any unbound identifier is
automatically added as an implicit argument **if** it is a single lower case or
greek letter. With this feature we can write compose as
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
-/
-- HAHA this is great actually. i wonder if it's auto-scoped?
def hmm (f : α → β) (g : β → γ) (l : List α) : List γ :=
  List.map mine l
  where mine : α → γ := g ∘ f -- yeah it is

-- Implicit lambdas, wat? I guess I need to use the language more t
-- appreciate this?
/-
namespace ex2
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because
-- we use `@` before `fun`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- In this example, implicit lambda introduction has been disabled
-- because we used the binder annotation `{...}`
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
end ex2
-/



-- Section function application sugar
namespace ex3
#check (· + 1)
-- fun a => a + 1
#check (2 - ·)
-- fun a => 2 - a
#eval [1, 2, 3, 4, 5].foldl (·*·) 1
-- 120

def f (x y z : Nat) :=
  x + y + z

#check (f · 1 ·)
-- fun a b => f a 1 b

#eval [(1, 2), (3, 4), (5, 6)].map (·.1)
-- [1, 3, 5]
end ex3



-- NAMED ARGUMENTS YES!!

def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
    : p a a b :=
  -- Is this the same as what match was doing?? Does "match" as
  -- a langauge construct have a "motive" argument that is
  Eq.subst (motive := fun x => p a x b) h₂ h₁


def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl
example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl
example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl
example : f = (fun x z => x + 1 + 2 - z) := rfl
example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl
example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]
example : g = fun (a c : α) => a + c := rfl
example (x : α) : g (c := x) = fun (a : α) => a + x := rfl
example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl
example (x : α) : g x = fun (c : α) => x + c := rfl
example (x y : α) : g x y = fun (c : α) => x + y + c := rfl


inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | app    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none
