example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro -- 2 goals
  exact hp        -- closes one of them
  apply And.intro -- opens 2 more goals
  exact hq        -- closes one of them
  exact hp        -- closes the other

/-
Tactics that may produce multiple subgoals often tag them.
For example, the tactic apply And.intro tagged the first subgoal
as left, and the second as right. In the case of the apply
tactic, the tags are inferred from the parameters' names used
in the And.intro declaration. You can structure your tactics
using the notation case <tag> => <tactics>. The following is
a structured version of our first tactic proof in this chapter.
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

-- ? stupid syntax
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

-- Wait it's not so stupid. the goals aligned with the dots
-- are the subgoals that satisfy the tactic.
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr
