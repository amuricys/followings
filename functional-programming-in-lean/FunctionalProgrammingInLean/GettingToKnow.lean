-- Chapter 1
def hello : String := "world"
#eval String.append "hello " (if true then "hmm" else "world")
#eval String.startsWith "hello world" hello
#eval (-2 )
#eval (1 - 2 : Int)
def incCurried : Nat → Nat := λ x => x + 1
def incCurriedFun : Nat → Nat := fun x => x + 1
def incUncurriedIdk (x : Nat) (y : Nat) : Nat := x + y + 1
#check (incUncurriedIdk)
/- What's wrong with this?? "unreachable code reached". Something with List.foldl
def joinStringsWith (xₛ : List String) (btwn : String) : if List.length xₛ < 2 then Bool else String
  := match xₛ with
     | ([] : List String) => true
     | [x] => false
     -- Interestingly, this pattern match needs to be
     -- exhaustive, even though if the others two didn't match,
     -- the list would have to have at least 2 elements.
     | x :: x' :: xs =>  List.foldl String.append "" (List.intersperse btwn xs)
-/

structure Point2D where
  x : Float
  y : Float
deriving Repr

def point_x0y2 : Point2D := { x := 0.0, y := 2.0 }

instance point2dAdd : HAdd Point2D Point2D Point2D where
  hAdd p₁ p₂ := { x := p₁.x + p₂.x, y := p₁.y + p₂.y }
instance point2dAddFloat : HAdd Point2D Float Point2D where
  hAdd p f := { x := p.x + f, y := p.y + f }
/- Interesting. I love that add is parametrized, but although
   building these two instances works, the second one can't be used:
#eval point_x0y2 + 0.4
-/
#eval point_x0y2 + point_x0y2

def distance (p₁ p₂ : Point2D) : Float :=
  Float.sqrt ((p₁.x - p₂.x)^2 + (p₁.y - p₂.y)^2)

structure Point3D (a : Type) where
  x : a
  y : Float
  z : Float
deriving Repr

-- Interesting; type is necessary for a structure literal. makes sense.
def origin3D : Point3D Point2D := { x := {x := 0.0, y := 0.0}, y := 0.0, z := 0.0 }

-- Nesting examples
def zeroX (p : Point3D (Point3D Point2D)) : Point3D (Point3D Point2D) :=
  { p with x.x.y := 0 }
def zeroX' (p : Point3D (Point3D Point2D)) : Point3D Float :=
  { p with x := 0 }

structure RectangularPrism where
  rectprism ::
  width : Float
  height : Float
  depth : Float
deriving Repr

def volume (m : RectangularPrism) := m.width * m.height * m.depth

inductive ℕ : Type
  | zero : ℕ
  | succ : ℕ → ℕ
  deriving Repr

def toNat (m : ℕ) : Nat := match m with
  | ℕ.zero => 0
  | ℕ.succ n => Nat.succ (toNat n)

def fromNat (m : Nat) : ℕ := match m with
  | 0 => ℕ.zero
  | Nat.succ n => ℕ.succ (fromNat n)

-- This is very interesting! What's this instance doing?
instance (n : Nat) : OfNat ℕ n where
  ofNat := fromNat n

def add (m n : ℕ) : ℕ := match m with
  | ℕ.zero => n
  | (ℕ.succ m) => ℕ.succ (add m n)

#eval add 5 1

-- This syntax is so terse i love it :drool:
def sub : ℕ → ℕ → ℕ
  | n, ℕ.zero => n
  | ℕ.zero, _ => ℕ.zero
  | ℕ.succ n, ℕ.succ m => sub n m

/- Needs the LT instance; stay tuned
instance : LT ℕ where
  lt n m := ???
def div (n : ℕ) (k : ℕ) : ℕ :=
  if n < k then
    0
  else ℕ.succ (div (sub n k) k)
-/

-- STAY TUNED!
-- structure Poly where
--   pos : Type
--   dir : pos → Type

-- structure Lens (p₁ p₂ : Poly) where
--   mapPosition : p₁.pos → p₂.pos
--   mapDirection : (fromPos : p₁.pos) → p₂.dir (mapPosition fromPos) → p₁.dir fromPos

-- def lensCompose {p₁ p₂ p₃ : Poly} (l₁ : Lens p₁ p₂) (l₂ : Lens p₂ p₃) : Lens p₁ p₃ :=
--   { mapPosition := l₂.mapPosition ∘ l₁.mapPosition,
--     mapDirection := λ fromPos dir => l₁.mapDirection fromPos (l₂.mapDirection (l₁.mapPosition fromPos) dir) }

-- infixr:90 " ∘ₐc "  => lensCompose

inductive Sign where
  | pos
  | neg

-- Interesting syntax for matching at type level. wonder if my dumbass if stmt
-- on the above is why it breaks
def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => 3
  | Sign.neg => -3

inductive L (a : Type) where
  | nil : L a
  | cons : a → L a → L a

def length {a : Type} (l : L a) : Nat := match l with
  | L.nil => 0
  | L.cons _ l => Nat.succ (length l)

-- wait WHY does this work? Because it is defined in the list namespace and therefore
-- any value of the type of the namespace is allowed to use dot notation with this value? lol
#eval [1,2,3,4].length


-- ann for annotations? hmm
inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

-- Universe levels can be given as arguments
inductive MyType : Type 1 where
  | ctor : (α : Type) → α → MyType

-- This one can't be fixed: a type's constructor can't consume its argument (?)
-- inductive MyType2 : Type where
--   | ctor : (MyType2 → Int) → MyType2

def __ : 1 = 1 :=
  Eq.refl 1

#check fun {α : Type} (x : α) => x
#check fun
  | 0 => none
  | n + 1 => some n

-- Section syntax. so close to clojure's #(%1 %2) syntax
-- where we can name arguments.
def f (x : Nat) : Nat := ((· + 2) ∘ (· + 1)) x

namespace NewNamespace
  namespace NestedNamespace
    def g (x : Nat) : Nat := x + 1
  end NestedNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace

open NewNamespace
#eval open NestedNamespace in g (triple 3)
#eval s!"three fives is {NewNamespace.triple 5}"

