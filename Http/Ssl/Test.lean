import Socket
import Http.Ssl.Handshake
import Http.Ssl.ToBytes
import Mathlib.Control.Random

open Socket

namespace Ssl

def randVector (n : Nat) : IO (List UInt8) :=
  match n with
  | .zero => pure []
  | .succ n => do
    let head : Fin 256 ← IO.runRand (Random.randFin)
    let tail ← randVector n
    pure (.mk head :: tail)


def sendtest : IO ByteArray := do
  let remoteAddr ← SockAddr.mk
    (host := "catfact.ninja")
    (port := 443 |> ToString.toString)
    (family := .inet)
    (type := .stream)
  let socket ← Socket.mk .inet .stream
  socket.connect remoteAddr

  let rand ← randVector 32
  dbg_trace s!"Randvectorlength {rand.length}"

  let clientHello : ClientHello := {
    random := rand
    cipherSuites := [[0x13,0x02], [0x13, 0x01]]
    extensions := ([⟨ .supportedVersions , [0x0304]⟩] : VariableVector (Extension .clientHello) 2)
  }

  let handshake : Handshake .clientHello := {
    length := ⟨clientHello.toBytes.size.mod (2^24), Nat.mod_lt _ (by simp_arith) ⟩
    body := clientHello
  }

  let plaintext : TLSPlaintext := {
    type := .handshake
    length := handshake.toBytes.size.toUInt16
    fragment := handshake.toBytes
  }

  dbg_trace plaintext.toBytes

  discard $ socket.send (.mk plaintext.toBytes)
  let bytesRecv ← socket.recv 8000
  dbg_trace String.fromUTF8Unchecked bytesRecv
  let tlsPlaintextB := BinParsec.run (BinParsec.tLSPlaintext) bytesRecv.data 

  match tlsPlaintextB with
  | .error e =>
    dbg_trace s!"Error plaintext {e}"
    return bytesRecv
  | .ok tlsPlaintext =>
    let serverHello := BinParsec.run (BinParsec.serverHello) tlsPlaintext.fragment
    match serverHello with
    | .ok val =>
      dbg_trace s!"Success !"
      return bytesRecv
    | .error e =>
      dbg_trace s!"Error {e}"
      return bytesRecv