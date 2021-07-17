module Average 
export
-- Turd 0: I tried adding a "predicate" to str here saying its length should be three. So code that calls
-- this with string types that dont have a predicate attached to them proving the string has length
-- 3 should simply not compile. But it didn't like this; is this a pocket of computational irreducibility?
-- Must you simply _run_ the _compiled_ program in order to figure out the length of a string? I suspect not.
-- I just think Idris has heavier weight syntax for this than I originally thought.
average : (str : String) -> Double
average str = let numWords = wordCount str
                  totalLength = sum (allLengths (words str)) in
                  cast totalLength / cast numWords
  where
    wordCount : String -> Nat
    wordCount str = length (words str)
    allLengths : List String -> List Nat
    allLengths strs = map length strs
export
showAverage : String -> String
showAverage str = "The average word length is: " ++
                   show (average str) ++ "\n"

-- Turdly: 
-- So, in the example double (double 15),
 
-- First, the inner double 15 is rewritten as 15 + 15.
-- 15 + 15 is rewritten as 30.
-- double 30 is rewritten as 30 + 30.
-- 30 + 30 is rewritten as 60.
double : (Num a) => a -> a
double a = a + a
-- Does this mean every piece of code is essentially a "macro"? Code gets REWRITTEN as
-- it gets compiled? I guess that makes sense if you want to just be able to run programs on
-- your types, but it seems like compilation will pretty much always take an eternity. 

-- Idris> :t the Int
-- the Int : Int -> Int

-- Idris> :t the Bool
-- the Bool : Bool -> Bool

-- `the` is essentially Type Application in Haskell then
    
    
-- Let is only for values and where only for functions? No way
myLet : Double -> String
myLet x = let
    dub = x * x
    res = pal dub
    in
        res
      where 
          pal : (Show a) => a -> String 
          pal = show

-- Yep, this works. So just a convention
myWrongLet : Double -> String
myWrongLet x = let
    dub = x * x
    res = pal
    res2 = res (dub + res3)
    in
        res2
      where 
          pal : (Show a) => a -> String 
          pal = show
          res3 = 3 + 3

-- Exercises
palindrome1 : String -> Bool
palindrome1 x = x == reverse x
palindrome2 : String -> Bool
palindrome2 x = let x' = toUpper x in x' == reverse x'
palindrome3 : String -> Bool
palindrome3 x = palindrome1 x && length x >= 10 
palindrome4 : Nat -> String -> Bool
palindrome4 n x = palindrome1 x && length x >= n
counts : String -> (Nat, Nat)
counts s = (length s, length . words $ s) 