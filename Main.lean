import Http
import Http.Ssl.Handshake
import Http.Ssl.Test
-- import OpenSSL

-- open OpenSSL
open Http

open Ssl

def main (args : List String) : IO UInt32 := do
  let bytes ← Ssl.sendtest
  dbg_trace bytes
  pure 0

-- def main (args : List String) : IO UInt32 := do
--   try
--     -- let ssl ← sslClientInit
    
--     match args with
--     | [ "--get", surl ] => do
--       let url ← IO.ofExcept <| URI.parse surl
--       let response ← Client.get url
--       println! "headers : {response.headers}"
--       println! "body: {response.body}"
--     | [ "--post", surl, body ] => do
--       let url ← IO.ofExcept <| URI.parse surl
--       let response ← Client.post url body
--       println! "headers : {response.headers}"
--       println! "body: {response.body}"
--     | unknown => println! "Invalid arguments {unknown}"
--     pure 0
--   catch e =>
--     IO.eprintln <| "error: " ++ toString e
--     pure 1
