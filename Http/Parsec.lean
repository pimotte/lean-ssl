import Lean.Data.Parsec

open Lean Lean.Parsec ParseResult

namespace Http.Parsec

@[inline]
def digitNat : Parsec Nat := do
  let c ← satisfy (fun c => '0' ≤ c ∧ c ≤ '9')
  return c.val.toNat - '0'.val.toNat

@[inline]
def rest : Parsec String := fun it =>
  success it it.remainingToString

@[inline]
def oneOf (cs : List Char) : Lean.Parsec Char := do
  let c ← anyChar
  if cs.contains c then
    pure c
  else
    fail s!"expected one of: {cs}"

@[inline]
def andAppend {α : Type} [Append α] (f : Parsec α) (g : Parsec α) : Parsec α := do 
  let a ← f
  let b ← g
  return a ++ b

@[inline]
def andHAppend {A B C : Type} [HAppend A B C] (f : Parsec A) (g : Parsec B) : Parsec C := do 
  let a ← f
  let b ← g
  return a ++ b

instance {α : Type} [Append α] : Append $ Parsec α := ⟨andAppend⟩
instance {A B C : Type} [HAppend A B C] : HAppend (Parsec A) (Parsec B) (Parsec C) := ⟨andHAppend⟩



/-
Convert errors to none
-/
def option (p : Parsec α) : Parsec $ Option α := fun pos =>
  match p pos with
  | success rem a => success rem (some a)
  | error rem err => success pos (none)

@[inline]
partial def manyStringsCore (p : Parsec String) (acc : String) : Parsec String := do
  if let some res ← option p then
    manyStringsCore p (acc.append $ res)
  else
    pure acc

/-
One or more matching chars
-/
@[inline]
def many1Strings (p : Parsec String) : Parsec String := do
  manyStringsCore p (←p)


@[inline]
partial def manyCharsCore (p : Parsec Char) (acc : String) : Parsec String := do
  if let some res ← option p then
    manyCharsCore p (acc.push $ res)
  else
    pure acc

/-
Zero or more matching chars
-/
@[inline]
def manyChars (p : Parsec Char) : Parsec String := manyCharsCore p ""

/-
One or more matching chars
-/
@[inline]
def many1Chars (p : Parsec Char) : Parsec String := do manyCharsCore p (←p).toString



def parseDigit! (c : Char) : Nat :=
  match c with
  | '0' => 0
  | '1' => 1
  | '2' => 2
  | '3' => 3
  | '4' => 4
  | '5' => 5
  | '6' => 6
  | '7' => 7
  | '8' => 8
  | '9' => 9
  | _ => panic! "Not a digit"

def parseUInt16 : Parsec UInt16 := do
  let as ← many1 digit
  let mut n := 0
  for (i, c) in as.toList.reverse.enum do
    let d := parseDigit! c
    n := n + d * 10 ^ i
  return n.toUInt16

/-
Try to match but rewind iterator if failure and return success bool
-/
def test (p : Parsec α) : Parsec Bool := fun pos =>
  match p pos with
  | success rem a => success rem true
  | error rem err => success pos false



def parse {A: Type} (p: Parsec A) (s : String) : Except String A :=
  match p s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it err  => Except.error s!"offset {repr it.i.byteIdx}: {err}"