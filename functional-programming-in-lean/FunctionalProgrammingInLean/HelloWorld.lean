import Http

def intro : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

-- #eval intro

def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions

-- #eval runActions (countdown 3)

------ Feline example
def bufsize : USize := 20 * 1024

-- Hmm, partial seems to play exactly the same role as
-- {-# TERMINATING #-}. It asserts that the function terminates
-- even though the termination checker can't verify it. i guess
-- partial functions are the same as non-terminating functions in some deep way
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf -- this is *almost* the same as >>=
    -- Using >>= would look like this. It's weird because write is a *field* of IO.FS.Stream
    -- IO.getStdout >>= flip IO.FS.Stream.write buf
    dump stream

-- very imperative style, the book uses
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))


-- "Just as with if, each branch of a match that is used as a statement in a
-- do is implicitly provided with its own do." damn idk if i like this
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨filename⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args

def main (args : List String) : IO UInt32 := do
  let conn ← Connection.create "www.google.com" "80"
  -- omg we can omit `some` when creating an Option literal. Due to Coe!
  let req : Uri := { Uri.empty with path := "https://www.google.com" }
  Connection.get conn req >>= λ m => match m with
    | Except.ok resp => do
       IO.println "Yooo good stuff"
       IO.println resp
    | Except.error e => do
       IO.println "NAHH"
       IO.println e
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args
