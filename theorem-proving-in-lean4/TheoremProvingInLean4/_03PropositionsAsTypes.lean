def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop

variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  let hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

open Classical

-- theorem dne {p : Prop} (h : ¬¬p) : p :=
--   Or.elim (em p)
--     (λ hp : p ↦ hp)
--     (λ hnp : ¬p ↦ absurd hnp h)


-- exercises from PLFA lol: show EM from DNE
axiom dne {p : Prop} (h : ¬¬p) : p

/-
postulate
  dne : ∀ {p : Type lzero} → ¬ (¬ p) → p

lem : ∀ {p : Type lzero} → (p ⊎ ¬ p)
lem {p} = dne k
  where k : ¬ ¬ (p ⊎ ¬ p)
        k x = x (inr (λ x₁ → x (inl x₁)))

peirce : ∀ {p q : Type lzero} → ((p → q) → p) → p
peirce {p} {q} = dne k
  where k : ¬ ¬ (((p → q) → p) → p)
        k w = w -- w here is assuming that peirce WASN'T true.
              λ ⦅p→q⦆→p → -- So it takes a function whose assumption is that peirce IS true
              ⦅p→q⦆→p -- this function takes an implication p → q
              λ (p1 : p) → -- So that's this lambda. the argument is of type p
              -- and now we need to give a q, which we need from the ether.
              -- Needing things from the ether is usually call for `absurd`.

              absurd {A = q {- we need a q -} }

                -- absurd needs a ⊥. The only thing that generates it is w
                -- recall that w is: "what if peirce wasn't true". So it takes
                -- "peirce is true" as an argument. We will construct that.
                (w
                  -- a value of "peirce is true" is a function that takes p→q→p
                  -- and returns p.
                  λ (x : (p → q) → p) →
                  -- But wait, we assumed p forever ago. So we can just return that.
                  p1
                  )

imp-as-disj : ∀ {p q : Type lzero} → (p → q) → ¬ p ⊎ q
imp-as-disj {p} {q} = dne k
   where
       k : ¬ ¬ ((p → q) → ¬ (p ⊎ q))
       k x = {!   !}
-/
#check 1

