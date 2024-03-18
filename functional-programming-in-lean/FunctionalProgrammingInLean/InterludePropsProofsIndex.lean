def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]
-- def oops := woodlandCritters[3]

-- Hmm so Props have different kinds from Types...
def OnePlusOneIsTwo : Prop := 1 + 1 = 2
theorem onePlusOneIsTwo : 1 + 1 = 2 := by
  simp

-- Hmm, simp doesn't find this
theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" :=
  And.intro onePlusOneIsTwo rfl

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

def third (xs : List α) (ok : GT.gt xs.length 2) : α := xs[2]

-- I really REALLY wish we could get away with not passing simps at all
#eval third [1, 2, 3, 4] (by simp)

-- the ? is very nice
def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlandCritters

-- HMm, how do I construct it manually? I guess I'll go to Theorem proving in Lean
theorem fiveLessThanEight : LT.lt 5 8 := by simp
