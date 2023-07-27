namespace Ssl

class ToBytes (α : Type) where
  toBytes : α → Array UInt8

inductive HandshakeType where 
  | clientHello | serverHello
  | newSessionTicket | endOfEarlyData
  | encryptedExtensions | certificate
  | certificateRequest | certificateVerify
  | finished | keyUpdate
  | messageHash
deriving BEq



def UInt24.size := 2^24

abbrev UInt24 := Fin UInt24.size


abbrev  VariableVector (α : Type) (lengthByteSize : Nat) := List α

-- def VariableVector.maxByteSize (v : VariableVector α maxByteSize) : UInt64 v.maxByteSize


abbrev Random := List UInt8 
deriving instance ToString for Random

abbrev SessionId := VariableVector UInt8 1


abbrev CipherSuite := List UInt8 
deriving instance ToString for CipherSuite

abbrev ProtocolVersion := UInt16

inductive ExtensionType where
  | serverName | maxFragmentLength | statusRequest | supportedGroups | signatureAlgorithms | useSrtp
  | heartbeat | applicationLayerProtocolNegotiation | signedCertificateTimestamp
  | clientCertificateType | serverCertificateType | padding | preSharedKey
  | earlyData | supportedVersions | cookie | pskKeyExchangeModes | certificateAuthorities
  | oidFilters | postHandshakeAuth | signatureAlgorithmsCert | keyShare
deriving Repr

abbrev SupportedVersions := VariableVector ProtocolVersion 1

abbrev Hostname := VariableVector UInt8 2

structure ServerName where
  -- NameType can only be host name
  name : Hostname

abbrev ServerNameList := VariableVector ServerName

def ExtensionData : ExtensionType → HandshakeType → Type
  | .supportedVersions , .clientHello => SupportedVersions
  | .supportedVersions , .serverHello => ProtocolVersion
  | _, _  => VariableVector UInt8 1

structure Extension (hType : HandshakeType) where
  extensionType : ExtensionType
  extensionData : ExtensionData extensionType hType 

structure ClientHello where
  random : Random
  cipherSuites : VariableVector CipherSuite 2
  extensions : VariableVector (Extension .clientHello) 2

structure ServerHello where
  -- protocolVersion : static #[3, 3]
  random : Random
  -- legacySessionIdEcho : SessionId (not relevant, since we don't send sessionIds)
  cipherSuite : CipherSuite
  -- compressionMethod : CompressionMethod
  extensions : VariableVector (Extension .serverHello) 2

def HandshakeType.asType : HandshakeType → Type
  | .clientHello => ClientHello
  | .serverHello => ServerHello
  | _ => String

structure Handshake (hType : HandshakeType) where
  length : UInt24
  body : hType.asType

inductive ContentType where
  | invalid | changeCipherSpec | alert
  | handshake | applicationData

structure TLSPlaintext where
  type : ContentType
  length : UInt16
  fragment : Array UInt8