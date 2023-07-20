import Std.Data.List.Lemmas
import Std.Data.Nat.Lemmas
import Http.Ssl.BinParsec

namespace Ssl

open BinParsec
-- Use RFC 8446 as base

class ToBytes (α : Type) where
  toBytes : α → Array UInt8

abbrev Vector (α : Type) (n : Nat) := Subtype (fun arr : List α => arr.length = n)

inductive HandshakeType where 
  | clientHello | serverHello
  | certificate | serverKeyExchange
  | certificateRequest | serverHelloDone
  | certificateVerify | clientKeyExchange
  | finished 

def concatMap (f : α → Array β) (as : List α) : Array β :=
  as.foldl (init := .empty) fun bs a => bs ++ f a


def Vector.toBytes [ToBytes α] : Vector α n → Array UInt8
  | ⟨ as , _ ⟩ => (concatMap (fun a : α => (@ToBytes.toBytes α) a) as)

def vector (length : Nat) (elem : BinParsec α) : BinParsec (Vector α length) := do
  match length with
  | .zero => pure ⟨[] , by simp ⟩
  | .succ len => 
    let first ← elem
    let ⟨ tail , htail ⟩ ← vector len elem

    pure ⟨first :: tail, by simp [htail]⟩

instance [ToBytes α] : ToBytes (Vector α n) where
  toBytes := fun v => Vector.toBytes v

abbrev VariableVector (α : Type) (lower : Nat) (upper : Nat) := 
  Subtype (fun arr : Array α => lower <= arr.size ∧ arr.size <= upper)

def VariableVector.toBytes [ToBytes α] : VariableVector α l u → Array UInt8
  | ⟨ arr , _ ⟩ => 
  arr.concatMap (fun a : α => (@ToBytes.toBytes α) a)


abbrev Random := Vector UInt8 28

def UInt8.toBytes : UInt8 → Array UInt8 := fun i => #[i]

instance : ToBytes UInt8 where
  toBytes := UInt8.toBytes

def UInt32.toBytes : UInt32 → Array UInt8 :=
  fun i => #[(i.shiftRight (8*3)).toUInt8, (i.shiftRight (8*2)).toUInt8, 
            (i.shiftRight (8*1)).toUInt8, (i.shiftRight (8*0)).toUInt8]

-- #eval UInt32.toBytes 5000 -- #[0, 0, 19, 136]

instance : ToBytes UInt32 where
  toBytes := UInt32.toBytes


abbrev SessionId := VariableVector UInt8 0 32

abbrev CipherSuite := Vector UInt8 2

inductive ExtensionType where
  | serverName | maxFragmentLength | statusRequest | supportedGroups | signatureAlgoritms | useSrtp
  | heartbeat | applicationLayerProtocolNegotiation | signedCertificateTimestamp
  | clientCertificateType | serverCertificateType | padding | preSharedKey
  | earlyData | supportedVersions | cookie | pskKeyExchangeModes | certificateAuthorities
  | oidFilters | postHandshakeAuth | signatureAlgorithmsCert | keyShare

structure Extension where
  extensionType : ExtensionType
  extensionData : VariableVector UInt8 0 (2^16-1)
 

structure ClientHello where
  protocolVersion : ProtocolVersion
  random : Random
  cipherSuites : VariableVector CipherSuite 2 (2^16-1)
  extensions : VariableVector Extension 8 (2^16-1)


def ClientHello.toBytes : ClientHello → Array UInt8 := fun ch =>
  -- v1.2 hardcoded
  #[0x03, 0x03] 
    ++ ch.random.toBytes 
    -- Legacy session id
    ++ #[0] 
    ++ ch.cipherSuites.toBytes 
    -- Legacy Compression methods
    ++ #[0]
    -- Empty extensions
    ++ #[0 , 0]

structure ServerHello where
  serverVersion : ProtocolVersion
  random : Random
  -- legacySessionIdEcho : SessionId (not relevant, since we don't send sessionIds)
  cipherSuite : CipherSuite
  -- compressionMethod : CompressionMethod
  extensions : VariableVector Extension 6 (2^16-1)

def HandshakeType.asType : HandshakeType → Type
  | .clientHello => ClientHello
  | _ => String

abbrev UInt24 := Subtype (fun n : UInt32 => n <= 167777215)

structure Handshake (hType : HandshakeType) where
  length : UInt24
  body : hType.asType
