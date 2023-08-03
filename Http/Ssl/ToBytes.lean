import Http.Ssl.Types

namespace Ssl



def ClientHello.toBytes : ClientHello → List UInt8 := fun ch =>
  -- v1.2 hardcoded
  [0x03, 0x03] 
    ++ List.toBytes ch.random 
    -- Legacy session id
    ++ [0] 
    ++ ch.cipherSuites.toBytes 
    -- Legacy Compression methods
    ++ [1, 0]
    ++ ch.extensions.toBytes

instance : ToBytes ClientHello where
  toBytes := ClientHello.toBytes

def ServerHello.toBytes : ServerHello → List UInt8 := fun ch =>
  -- v1.2 hardcoded
  [0x03, 0x03] 
    ++ List.toBytes ch.random 
    -- Legacy session id
    ++ [0] 
    ++ List.toBytes ch.cipherSuite
    -- Legacy Compression methods
    ++ [1, 0]
    ++ ch.extensions.toBytes

instance : ToBytes ServerHello where
  toBytes := ServerHello.toBytes

def HandshakeType.toBytes : HandshakeType → List UInt8
  | .clientHello => [1]
  | .serverHello => [2]
  | _ => [0]

instance : ToBytes HandshakeType where
  toBytes := HandshakeType.toBytes

def Handshake.toBytes : Handshake → List UInt8 := fun msg =>
  let hType := msg.hType
  let bodyFunction : hType.asType → List UInt8 := match hType with
  | .clientHello => ClientHello.toBytes
  | .serverHello => ServerHello.toBytes
  | _ => fun _ => [1, 3, 3, 7]
  hType.toBytes ++ msg.length.toBytes ++ (bodyFunction msg.body)

instance : ToBytes Handshake where
  toBytes := Handshake.toBytes

def ContentType.toBytes : ContentType → List UInt8
  | .invalid => [0]
  | .changeCipherSpec => [20]
  | .alert => [21]
  | .handshake => [22]
  | .applicationData => [23]

instance : ToBytes ContentType where
  toBytes := ContentType.toBytes

def TLSPlaintext.toBytes (plain : TLSPlaintext) : List UInt8 :=
  plain.type.toBytes 
  -- legacy record version
  ++ [3, 3] ++ 
  UInt16.toBytes plain.length
  ++ plain.fragment

instance : ToBytes (TLSPlaintext) where
  toBytes := TLSPlaintext.toBytes