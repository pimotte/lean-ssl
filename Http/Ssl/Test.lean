import Socket
import Http.Ssl.Handshake

open Socket

open Ssl

def send (request : Request) : IO ByteArray := do
  let remoteAddr ← SockAddr.mk
    (host := "catfact.ninja")
    (port := 443 |> ToString.toString)
    (family := .inet)
    (type := .stream)
  let socket ← Socket.mk .inet .stream
  socket.connect remoteAddr

  let clientHello : ClientHello := {
    protocolVersion := {
      major := 3
      minor := 0
    },
    random := {
      gmxUnixTime := 
    }
  }

  discard $ socket.send strSend.toUTF8
  let bytesRecv ← socket.recv 5000
  return bytesRecv