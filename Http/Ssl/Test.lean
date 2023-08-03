import Socket
import Http.Ssl.Handshake
import Http.Ssl.ToBytes
import Mathlib.Control.Random
import Http.Ssl.Bytesize

open Socket

namespace Ssl

def randVector (n : Nat) : IO (List UInt8) :=
  match n with
  | .zero => pure []
  | .succ n => do
    let head : Fin 256 ← IO.runRand (Random.randFin)
    let tail ← randVector n
    pure (.mk head :: tail)


def Char.toUInt8 : Char → UInt8 := fun c =>
  c.toNat.toUInt8

def String.toBytes : List Char → List UInt8 := fun cs =>
  match cs with 
  | [] => []
  | c :: cs => Char.toUInt8 c :: String.toBytes cs

  

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
    cipherSuites := ⟨[CipherSuite.TLS_AES_128_GCM_SHA256], by simp⟩
    extensions := ⟨[⟨ .supportedVersions , ⟨[SupportedVersions.tls1_3], by simp⟩⟩,
                    ⟨ .serverName , ⟨[⟨ String.toBytes "catfact.ninja".data , by simp⟩]  , by {
                      simp [List.map, ServerName.bytesize_eq _, VariableVector.bytesize_eq _]
                    }⟩⟩], by {
                      rw [List.map, Extension.bytesize_eq _]
                      dsimp [VariableVector.bytesize_eq _]
                      -- simp [List.map, ServerName.bytesize_eq _, VariableVector.bytesize_eq _]
      -- rw [List.map, bytesize, ToBytes.toBytes]
      -- unfold instToBytesExtension
      -- rw [Extension.bytesize_eq _]
      -- simp
    }⟩
  }

  let handshake : Handshake := {
    hType := .clientHello
    length := ⟨clientHello.toBytes.length.mod (2^24), Nat.mod_lt _ (by simp_arith) ⟩
    body := clientHello
  }

  let plaintext : TLSPlaintext := {
    type := .handshake
    length := handshake.toBytes.length.toUInt16
    fragment := handshake.toBytes
  }

  dbg_trace plaintext.toBytes

  discard $ socket.send (.mk plaintext.toBytes.toArray)
  let bytesRecv ← socket.recv 8000
  dbg_trace String.fromUTF8Unchecked bytesRecv
  let tlsPlaintextB := BinParsec.run (BinParsec.tLSPlaintext) bytesRecv.data 

  match tlsPlaintextB with
  | .error e =>
    dbg_trace s!"Error plaintext {e}"
    return bytesRecv
  | .ok tlsPlaintext =>
    match tlsPlaintext.type with
    | .handshake =>
      let serverHello := BinParsec.run (BinParsec.handshake) tlsPlaintext.fragment.toArray
      match serverHello with
      | .ok val =>
        dbg_trace s!"Success ServHello !"
        return bytesRecv
      | .error e =>
        dbg_trace s!"Error {e}"
        return bytesRecv
    | .alert => 
      -- TODO correct
      let alert := BinParsec.run (BinParsec.alert) tlsPlaintext.fragment.toArray
      match alert with
      | .ok val =>
        dbg_trace s!"Alert: {repr val}"
        return bytesRecv
      | .error e =>
        dbg_trace s!"Error {e}"
        return bytesRecv
    | _ => 
        dbg_trace s!"Unimplemented contenType"
        return bytesRecv