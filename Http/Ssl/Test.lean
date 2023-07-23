import Socket
import Http.Ssl.Handshake
import Mathlib.Control.Random

open Socket

open Ssl

def randVector (n : Nat) : IO (Vector UInt8 n) :=
  match n with
  | .zero => pure ⟨[], by simp⟩
  | .succ n => do
    let head : Fin 256 ← IO.runRand (Random.randFin)
    let ⟨ tail, htail⟩ ← randVector n
    pure ⟨⟨ head ⟩ :: tail, by simp [htail]⟩

def send (request : Request) : IO ByteArray := do
  let remoteAddr ← SockAddr.mk
    (host := "catfact.ninja")
    (port := 443 |> ToString.toString)
    (family := .inet)
    (type := .stream)
  let socket ← Socket.mk .inet .stream
  socket.connect remoteAddr

  let rand ← randVector 28

  let clientHello : ClientHello := {
    random := rand
    cipherSuites := ⟨#[ ⟨[0x13,0x02], by simp⟩, ⟨[0x13, 0x01], by simp⟩], by simp ⟩
    extensions := ⟨#[ ]
  }

  discard $ socket.send strSend.toUTF8
  let bytesRecv ← socket.recv 5000
  return bytesRecv