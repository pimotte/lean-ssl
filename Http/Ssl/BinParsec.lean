namespace BinParsec

structure BinIterator where
  source : Array UInt8
  idx : Nat
deriving BEq

def BinIterator.hasNext (bit : BinIterator) : Bool := bit.idx < bit.source.size

inductive ParseResult (α : Type) where
  | success (pos : BinIterator) (res : α)
  | error (pos : BinIterator) (err : String)

def BinParsec (α : Type) : Type := BinIterator → ParseResult α


open ParseResult

instance (α : Type) : Inhabited (BinParsec α) :=
  ⟨λ it => error it ""⟩

@[inline]
protected def pure (a : α) : BinParsec α := λ it =>
 success it a

@[inline]
def bind {α β : Type} (f : BinParsec α) (g : α → BinParsec β) : BinParsec β := λ it =>
  match f it with
  | success rem a => g a rem
  | error pos msg => error pos msg

instance : Monad BinParsec :=
  { pure := BinParsec.pure, bind }

@[inline]
def fail (msg : String) : BinParsec α := fun it =>
  error it msg

@[inline]
def orElse (p : BinParsec α) (q : Unit → BinParsec α) : BinParsec α := fun it =>
  match p it with
  | success rem a => success rem a
  | error rem err =>
    if it == rem then q () it else error rem err

@[inline]
def attempt (p : BinParsec α) : BinParsec α := λ it =>
  match p it with
  | success rem res => success rem res
  | error _ err => error it err

instance : Alternative BinParsec :=
{ failure := fail "", orElse }

protected def run (p : BinParsec α) (arr : Array UInt8) : Except String α :=
  match p (.mk arr 0) with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error it err  => Except.error s!"offset {repr it.idx}: {err}"

def expectedEndOfInput := "expected end of input"

@[inline]
def eof : BinParsec Unit := fun it =>
  if it.hasNext then
    error it expectedEndOfInput
  else
    success it ()
