import Std.Data.List.Lemmas
import Std.Data.Nat.Lemmas
import Http.Ssl.BinParsec
import Mathlib.Tactic.Linarith

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

def UInt8.toBytes : UInt8 → Array UInt8 := fun i => #[i]

instance : ToBytes UInt8 where
  toBytes := UInt8.toBytes

def BinParsec.uInt8 : BinParsec UInt8 := fun bit => 
  if bit.hasNext then
    let val := bit.source.get! bit.idx
    .success {
      source := bit.source
      idx := bit.idx + 1
    } val
  else
    .error bit "Expected UInt8 instead of end of array"

def UInt16.toBytes : UInt16 → Array UInt8 := fun i => 
  #[(i.shiftRight (8*1)).toUInt8, (i.shiftRight (8*0)).toUInt8]

-- #eval UInt16.toBytes 5000 -- #[19, 136]

def BinParsec.uInt16 : BinParsec UInt16 := do
  let b1 ← BinParsec.uInt8
  let b2 ← BinParsec.uInt8
  pure (b1.toUInt16.shiftLeft 8 + b2.toUInt16)

#eval BinParsec.run BinParsec.uInt16 #[19, 136] -- 5000

instance : ToBytes UInt16 where
  toBytes := UInt16.toBytes

abbrev UInt24 := Fin (2^24)

def UInt24.toBytes : UInt24 → Array UInt8 := fun i =>
  #[(i.shiftRight (⟨8 , by simp ⟩*⟨ 2 , by simp ⟩)).val.toUInt8, 
    (i.shiftRight (⟨8 , by simp ⟩*⟨ 1 , by simp ⟩)).val.toUInt8, 
    (i.shiftRight (⟨8 , by simp ⟩*⟨ 0 , by simp ⟩)).val.toUInt8]

instance : ToBytes UInt24 where
  toBytes := UInt24.toBytes

def lemma_uint8 (b : UInt8) : b.toNat < 2^8 := by {
  simp
  exact b.val.isLt
}

def le_sub_one_of_lt (h : n < m) : n ≤ m - 1 := by
  induction h with
  | refl => simp_arith
  | step h ih => {
    simp_arith
    exact Nat.le_trans ih (by simp_arith)
  }

def BinParsec.uInt24 : BinParsec UInt24 := do
  let b1 ← BinParsec.uInt8
  let b2 ← BinParsec.uInt8
  let b3 ← BinParsec.uInt8
  pure ⟨(b1.toNat * 2^16  + b2.toNat * 2^8 + b3.toNat), 
    by {

      simp_arith [UInt8.toNat]
      have h1 : b2.toNat * 2^8 ≤ (2^8-1)*2^8 := 
        Nat.mul_le_mul_of_nonneg_right (le_sub_one_of_lt b2.val.isLt)
      
      have h2 : b1.toNat * 2^16 ≤ (2^8-1)*2^16 := 
        Nat.mul_le_mul_of_nonneg_right (le_sub_one_of_lt b1.val.isLt)
      
      linarith [h1, h2, b3.val.isLt]
    }⟩

-- #eval BinParsec.run BinParsec.uInt24 #[0, 19, 136] -- 5000
#eval UInt24.toBytes ⟨5000, by simp⟩ -- #[0, 19, 136]

def UInt32.toBytes : UInt32 → Array UInt8 :=
  fun i => #[(i.shiftRight (8*3)).toUInt8, (i.shiftRight (8*2)).toUInt8, 
            (i.shiftRight (8*1)).toUInt8, (i.shiftRight (8*0)).toUInt8]

-- #eval UInt32.toBytes ⟨5000, by simp⟩ -- #[0, 0, 19, 136]
-- #eval UInt32.toBytes 16909060 -- #[1, 2, 3, 4]

instance : ToBytes UInt32 where
  toBytes := UInt32.toBytes

def UInt64.toBytes : UInt64 → Array UInt8 :=
  fun i => #[(i.shiftRight (8*7)).toUInt8, (i.shiftRight (8*6)).toUInt8, 
            (i.shiftRight (8*5)).toUInt8, (i.shiftRight (8*4)).toUInt8,
            (i.shiftRight (8*3)).toUInt8, (i.shiftRight (8*2)).toUInt8, 
            (i.shiftRight (8*1)).toUInt8, (i.shiftRight (8*0)).toUInt8]

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
