import Lean
import Http.Parsec
import Http.Types
import Socket

open Std Lean.Parsec Socket Http.Parsec Lean

namespace Http

namespace URI

private def toString (uri : URI) : String :=
  s!"{uri.scheme}://"
  ++ if let some user := uri.userInfo then s!"{user}@"
  else ""
  ++ s!"{uri.host}"
  ++ if let some port := uri.port then s!":{port}"
  else ""
  ++ s!"{uri.path}"
  ++ if let some query := uri.query then s!"?{query}"
  else ""
  ++ if let some fragment := uri.fragment then s!"#{fragment}"
  else ""

instance : ToString URI := ⟨toString⟩

namespace Parser

def schemeParser : Parsec Scheme :=
  Scheme.mk <$> Http.Parsec.manyChars (asciiLetter <|> oneOf ['+', '-', '.'])

def hostName : Parsec Hostname := do
  let name := Http.Parsec.many1Chars (asciiLetter <|> digit <|> pchar '-')
  let start := name ++ pstring "."
  many1Strings start ++ name

def maybePort : Parsec (Option UInt16) := do
  option $ parseUInt16

def psegment : Lean.Parsec String :=
  Http.Parsec.many1Chars <| oneOf ['-', '%', '_', '+', '$', '.', ':', '*', '@' ] <|> asciiLetter <|> digit

partial def pathParser : Lean.Parsec Path := do
  let rec comp : Parsec Path := do
    if ← test <| pstring "/" then
      let part ← psegment
      let rest ← comp
      pure <| part :: rest
    else
      pure []
  comp

def userInfoParser : Lean.Parsec UserInfo := do
  let username ← Http.Parsec.many1Chars <| asciiLetter <|> digit
  let password ← option do skipChar ':'; Http.Parsec.many1Chars <| asciiLetter <|> digit
  skipChar '@'
  return { username, password : UserInfo }

partial def queryParser : Lean.Parsec Query := do
  skipChar '?'
  let rec entries := do
    let k ← psegment
    skipChar '='
    let v ← psegment
    if ← test $ skipChar '&' then
      pure <| (k, v) :: (← entries)
    else
      pure [(k, v)]
  entries

partial def fragmentParser : Lean.Parsec Fragment := do
  skipChar '#'
  let rec entries := do
    let k ← psegment
    skipChar '='
    let v ← psegment
    if ← test $ skipChar '&' then
      pure <| (k, v) :: (← entries)
    else
      pure [(k, v)]
  entries

def url : Parsec URI := do  
  let scheme ← schemeParser
  skipString "://"
  let userInfo ← option userInfoParser
  let host ← hostName
  let optPort ← maybePort
  let path ← pathParser
  let query ← option queryParser
  let fragment ← option fragmentParser
  return { scheme, host, port := optPort, path, query, fragment, userInfo : URI }

end Parser

def parse (s : String) : Except String URI := Http.Parsec.parse Http.URI.Parser.url s

end URI
end Http
