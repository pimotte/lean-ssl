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

def BinParsec.byte (b : UInt8) : BinParsec UInt8 := fun bit =>
  if bit.hasNext then
    let val := bit.source.get! bit.idx
    if val = b then
      .success {
        source := bit.source
        idx := bit.idx + 1
      } val
    else
      .error bit s!"Expected {b} instead of {val}"
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

def UInt24.size := 2^24

abbrev UInt24 := Fin UInt24.size

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
  
def ineq_uint24 (a b c : Fin 256) : a.val * 2^16 + b.val * 2^8 + c.val < 2^24 := by 
  linarith [a.isLt, b.isLt, c.isLt]

def BinParsec.uInt24 : BinParsec UInt24 := do
  let b1 ← BinParsec.uInt8
  let b2 ← BinParsec.uInt8
  let b3 ← BinParsec.uInt8
  pure ⟨(b1.toNat * 2^16  + b2.toNat * 2^8 + b3.toNat), ineq_uint24 b1.val b2.val b3.val⟩

-- #eval BinParsec.run BinParsec.uInt24 #[0, 19, 136] -- 5000
-- #eval UInt24.toBytes ⟨5000, by simp⟩ -- #[0, 19, 136]

def UInt32.toBytes : UInt32 → Array UInt8 :=
  fun i => #[(i.shiftRight (8*3)).toUInt8, (i.shiftRight (8*2)).toUInt8, 
            (i.shiftRight (8*1)).toUInt8, (i.shiftRight (8*0)).toUInt8]

-- #eval UInt32.toBytes ⟨5000, by simp⟩ -- #[0, 0, 19, 136]
-- #eval UInt32.toBytes 16909060 -- #[1, 2, 3, 4]

instance : ToBytes UInt32 where
  toBytes := UInt32.toBytes

def BinParsec.uInt32 : BinParsec UInt32 := do
  let b1 ← BinParsec.uInt8
  let b2 ← BinParsec.uInt8
  let b3 ← BinParsec.uInt8
  let b4 ← BinParsec.uInt8
  pure (b1.toUInt32.shiftLeft (8*3) + b2.toUInt32.shiftLeft (8*2) 
      + b3.toUInt32.shiftLeft (8*1) + b4.toUInt32)

-- #eval BinParsec.run BinParsec.uInt32 #[1, 2, 3, 4] -- 16909060

def UInt64.toBytes : UInt64 → Array UInt8 :=
  fun i => #[(i.shiftRight (8*7)).toUInt8, (i.shiftRight (8*6)).toUInt8, 
            (i.shiftRight (8*5)).toUInt8, (i.shiftRight (8*4)).toUInt8,
            (i.shiftRight (8*3)).toUInt8, (i.shiftRight (8*2)).toUInt8, 
            (i.shiftRight (8*1)).toUInt8, (i.shiftRight (8*0)).toUInt8]

instance : ToBytes UInt64 where
  toBytes := UInt64.toBytes

def BinParsec.uInt64 : BinParsec UInt64 := do
  let b1 ← BinParsec.uInt8
  let b2 ← BinParsec.uInt8
  let b3 ← BinParsec.uInt8
  let b4 ← BinParsec.uInt8
  let b5 ← BinParsec.uInt8
  let b6 ← BinParsec.uInt8
  let b7 ← BinParsec.uInt8
  let b8 ← BinParsec.uInt8
  pure (b1.toUInt64.shiftLeft (8*7) + b2.toUInt64.shiftLeft (8*6) 
      + b3.toUInt64.shiftLeft (8*5) + b4.toUInt64.shiftLeft (8*4)
      + b5.toUInt64.shiftLeft (8*3) + b6.toUInt64.shiftLeft (8*2) 
      + b7.toUInt64.shiftLeft (8*1) + b8.toUInt64)

def concatMap (f : α → Array β) (as : List α) : Array β :=
  as.foldl (init := .empty) fun bs a => bs ++ f a


def Vector.toBytes [ToBytes α] : Vector α n → Array UInt8
  | ⟨ as , _ ⟩ => (concatMap (fun a : α => (@ToBytes.toBytes α) a) as)

def BinParsec.vector (length : Nat) (elem : BinParsec α) : BinParsec (Vector α length) := do
  match length with
  | .zero => pure ⟨[] , by simp ⟩
  | .succ len => 
    let first ← elem
    
    let ⟨ tail , htail ⟩ ← vector len elem
    pure ⟨first :: tail, by simp [htail]⟩

instance [ToBytes α] : ToBytes (Vector α n) where
  toBytes := fun v => Vector.toBytes v

-- #eval BinParsec.run (BinParsec.vector 3 BinParsec.uInt64) (Vector.toBytes (⟨[16909061, 16909060, 16909062], (by simp) ⟩ : Vector UInt64 3)) -- 16909060


abbrev VariableVector (α : Type) (lower : Nat) (upper : UInt64) := 
  Subtype (fun arr : Array α => lower <= arr.size ∧ arr.size <= upper.val)

def UInt64.toVariableBytes (n : UInt64) (u : UInt64) : Array UInt8 :=
  let raw := (UInt64.toBytes n).toList
  if u.toNat < UInt8.size then
    (raw.drop 7).toArray
  else
    if u.toNat < UInt16.size then
      (raw.drop 6).toArray
    else
      if u.toNat < UInt24.size then
        (raw.drop 5).toArray
      else
        if u.toNat < UInt32.size then
          (raw.drop 4).toArray
        else
          raw.toArray

def BinParsec.variableNumber (u : UInt64) : BinParsec Nat := 
  if u.toNat < UInt8.size then
    BinParsec.uInt8 >>= (fun i it => .success it i.toNat)
  else
    if u.toNat < UInt16.size then
      BinParsec.uInt16 >>= (fun i it => .success it i.toNat)
    else
      if u.toNat < UInt24.size then
        BinParsec.uInt24 >>= (fun i it => .success it i.val)
      else
        if u.toNat < UInt32.size then
          BinParsec.uInt32 >>= (fun i it => .success it i.toNat)
        else
          BinParsec.uInt64 >>= (fun i it => .success it i.toNat)

def VariableVector.toBytes [ToBytes α] : VariableVector α l u → Array UInt8
  | ⟨ arr , ⟨ _ , hu ⟩ ⟩ =>
    let size : Array UInt8 := UInt64.toVariableBytes ⟨ arr.size , (by linarith [u.val.isLt]) ⟩ u
    size ++ arr.concatMap (fun a : α => (@ToBytes.toBytes α) a)

def BinParsec.variableVector (l : Nat) (u : UInt64) (elem : BinParsec α) : BinParsec (VariableVector α l u) := do
  let length ← BinParsec.variableNumber u
  if h1 : l ≤ length  then
    if h2 : length ≤ u.toNat then
      let content ← BinParsec.vector length elem
    
      pure ⟨ content.val.toArray , 
        ⟨ by simp [h1, content.property]
        , by {
          rw [UInt64.toNat] at h2
          simp [h2, content.property]
        }⟩ ⟩ 
    else
      fail "Parsed length of variable vector too long"
  else
    fail "Parsed length of variable vector too short"

-- #eval BinParsec.run (BinParsec.variableVector 2 10 BinParsec.uInt64) (VariableVector.toBytes (⟨#[16909061, 16909060, 16909062], ⟨by simp, by simp ⟩ ⟩ : VariableVector UInt64 2 10)) -- 16909060

abbrev Random := Vector UInt8 28

abbrev SessionId := VariableVector UInt8 0 32

abbrev CipherSuite := Vector UInt8 2

inductive ExtensionType where
  | serverName | maxFragmentLength | statusRequest | supportedGroups | signatureAlgorithms | useSrtp
  | heartbeat | applicationLayerProtocolNegotiation | signedCertificateTimestamp
  | clientCertificateType | serverCertificateType | padding | preSharedKey
  | earlyData | supportedVersions | cookie | pskKeyExchangeModes | certificateAuthorities
  | oidFilters | postHandshakeAuth | signatureAlgorithmsCert | keyShare

def ExtensionType.toBytes : ExtensionType → Array UInt8
  | .serverName => #[0, 0]
  | .maxFragmentLength => #[0, 1]
  | .statusRequest => #[0, 5]
  | .supportedGroups => #[0, 10]
  | .signatureAlgorithms => #[0, 13]
  | .useSrtp => #[0, 14]
  | .heartbeat => #[0, 15]
  | .applicationLayerProtocolNegotiation => #[0, 16]
  | .signedCertificateTimestamp => #[0, 18]
  | .clientCertificateType => #[0, 19]
  | .serverCertificateType => #[0, 20]
  | .padding => #[0, 21]
  | .preSharedKey => #[0, 41]
  | .earlyData => #[0, 42]
  | .supportedVersions => #[0, 43]
  | .cookie => #[0, 44]
  | .pskKeyExchangeModes => #[0, 45]
  | .certificateAuthorities => #[0, 47]
  | .oidFilters => #[0, 48]
  | .postHandshakeAuth => #[0, 49]
  | .signatureAlgorithmsCert => #[0, 50]
  | .keyShare => #[0, 51]

instance : ToBytes ExtensionType where
  toBytes := ExtensionType.toBytes

def BinParsec.extensionType : BinParsec ExtensionType := do
  let _ ← BinParsec.byte 0
  let b ← BinParsec.uInt8
  match b with
  | 0 => pure .serverName
  | 1 => pure .maxFragmentLength
  | 5 => pure .statusRequest
  | 10 => pure .supportedGroups
  | 13 => pure .signatureAlgorithms
  | 14 => pure .useSrtp
  | 15 => pure .heartbeat
  | 16 => pure .applicationLayerProtocolNegotiation
  | 18 => pure .signedCertificateTimestamp
  | 19 => pure .clientCertificateType
  | 20 => pure .serverCertificateType
  | 21 => pure .padding
  | 41 => pure .preSharedKey
  | 42 => pure .earlyData
  | 43 => pure .supportedVersions
  | 44 => pure .cookie
  | 45 => pure .pskKeyExchangeModes
  | 47 => pure .certificateAuthorities
  | 48 => pure .oidFilters
  | 49 => pure .postHandshakeAuth
  | 50 => pure .signatureAlgorithmsCert
  | 51 => pure .keyShare
  | otr => fail s!"Unexpected byte {otr} when parsing ExtensionType"

structure Extension where
  extensionType : ExtensionType
  extensionData : VariableVector UInt8 0 (2^16-1).toUInt64

def Extension.toBytes (ext : Extension) : Array UInt8 :=
  ext.extensionType.toBytes ++ ext.extensionData.toBytes

instance : ToBytes Extension where
  toBytes := Extension.toBytes

def BinParsec.extension : BinParsec Extension := do
  let type ← BinParsec.extensionType
  let data ← BinParsec.variableVector 0 (2^16-1).toUInt64 BinParsec.uInt8
  pure (.mk type data)
 

structure ClientHello where
  random : Random
  cipherSuites : VariableVector CipherSuite 2 (2^16-1).toUInt64
  extensions : VariableVector Extension 8 (2^16-1).toUInt64


def ClientHello.toBytes : ClientHello → Array UInt8 := fun ch =>
  -- v1.2 hardcoded
  #[0x03, 0x03] 
    ++ ch.random.toBytes 
    -- Legacy session id
    ++ #[0] 
    ++ ch.cipherSuites.toBytes 
    -- Legacy Compression methods
    ++ #[0]
    ++ ch.extensions.toBytes

instance : ToBytes ClientHello where
  toBytes := ClientHello.toBytes

def BinParsec.clientHello : BinParsec ClientHello := do
  let _ ← BinParsec.byte 3
  let _ ← BinParsec.byte 3
  let random ← BinParsec.vector 28 BinParsec.uInt8
  let _ ← BinParsec.byte 0
  let suites ← BinParsec.variableVector 2 (2^16-1).toUInt64 (BinParsec.vector 2 BinParsec.uInt8)
  let _ ← BinParsec.byte 0
  let extensions ← BinParsec.variableVector 8 (2^16-1).toUInt64 BinParsec.extension
  pure {
    random := random
    cipherSuites := suites
    extensions := extensions
  }

structure ServerHello where
  -- protocolVersion : static #[3, 3]
  random : Random
  -- legacySessionIdEcho : SessionId (not relevant, since we don't send sessionIds)
  cipherSuite : CipherSuite
  -- compressionMethod : CompressionMethod
  extensions : VariableVector Extension 6 (2^16-1).toUInt64

def BinParsec.serverHello : BinParsec ServerHello := do
  let _ ← BinParsec.byte 3
  let _ ← BinParsec.byte 3
  let random ← BinParsec.vector 28 BinParsec.uInt8
  let _ ← BinParsec.byte 0
  let suite ← BinParsec.vector 2 BinParsec.uInt8
  let _ ← BinParsec.byte 0
  let extensions ← BinParsec.variableVector 6 (2^16-1).toUInt64 BinParsec.extension
  pure {
    random := random
    cipherSuite := suite
    extensions := extensions
  }
def HandshakeType.asType : HandshakeType → Type
  | .clientHello => ClientHello
  | _ => String


structure Handshake (hType : HandshakeType) where
  length : UInt24
  body : hType.asType
