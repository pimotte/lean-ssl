import Http.Types
import Http.Headers
import Http.Parsec
import Lean.Data.Parsec

namespace Http.Response

namespace Parser
open Lean Http.Headers Lean.Parsec Http.Parsec

def protocol : Parsec Protocol := do
  let name ← Http.Parsec.many1Chars asciiLetter
  skipChar '/'
  let version ← Http.Parsec.many1Chars (digit <|> pchar '.')
  match name with
  | "HTTP" => return Protocol.http version
  | "HTTPS" => return Protocol.https version
  | s => return Protocol.other s version

def digitsToNat (ds : Array Nat) : Nat :=
  ds.toList.enum.foldl (λ acc (d, i) => acc + d * 10 ^ i) 0

def response : Parsec Response := do
  let protocol ← protocol
  ws
  let statusCode ← digitsToNat <$> many1 digitNat
  ws
  let message ← Http.Parsec.manyChars <| satisfy (λ c => c != '\n')
  ws
  let headers ← Parser.headers
  let body ← rest
  return {
    protocol,
    headers,
    message,
    body := some body,
    statusCode,
  : Response }

end Parser

def parse (s : String) : Except String Response := Http.Parsec.parse Http.Response.Parser.response s

end Http.Response
