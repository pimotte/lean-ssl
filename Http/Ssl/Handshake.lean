import Std.Data.List.Lemmas
import Std.Data.Nat.Lemmas
import Http.Ssl.BinParsec
import Http.Ssl.ToBytes
import Mathlib.Tactic.Linarith

namespace Ssl

open BinParsec
-- Use RFC 8446 as base

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


-- #eval UInt16.toBytes 5000 -- #[19, 136]

def BinParsec.uInt16 : BinParsec UInt16 := do
  let b1 ← BinParsec.uInt8
  let b2 ← BinParsec.uInt8
  pure (b1.toUInt16.shiftLeft 8 + b2.toUInt16)

#eval BinParsec.run BinParsec.uInt16 #[19, 136] -- 5000

instance : ToBytes UInt16 where
  toBytes := UInt16.toBytes

  
def ineq_uint24 (a b c : Fin 256) : a.val * 2^16 + b.val * 2^8 + c.val < 2^24 := by 
  linarith [a.isLt, b.isLt, c.isLt]

def BinParsec.uInt24 : BinParsec UInt24 := do
  let b1 ← BinParsec.uInt8
  let b2 ← BinParsec.uInt8
  let b3 ← BinParsec.uInt8
  pure ⟨(b1.toNat * 2^16  + b2.toNat * 2^8 + b3.toNat), ineq_uint24 b1.val b2.val b3.val⟩

-- #eval BinParsec.run BinParsec.uInt24 #[0, 19, 136] -- 5000
-- #eval UInt24.toBytes ⟨5000, by simp⟩ -- #[0, 19, 136]

-- #eval UInt32.toBytes ⟨5000, by simp⟩ -- #[0, 0, 19, 136]
-- #eval UInt32.toBytes 16909060 -- #[1, 2, 3, 4]

def BinParsec.uInt32 : BinParsec UInt32 := do
  let b1 ← BinParsec.uInt8
  let b2 ← BinParsec.uInt8
  let b3 ← BinParsec.uInt8
  let b4 ← BinParsec.uInt8
  pure (b1.toUInt32.shiftLeft (8*3) + b2.toUInt32.shiftLeft (8*2) 
      + b3.toUInt32.shiftLeft (8*1) + b4.toUInt32)

-- #eval BinParsec.run BinParsec.uInt32 #[1, 2, 3, 4] -- 16909060


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

def BinParsec.list (numBytes : Nat) (elem : BinParsec α) : BinParsec (List α) := do
  if 0 < numBytes then
    let ⟨first, bytesConsumed ⟩ ← BinParsec.counting elem
    if 0 < bytesConsumed  then
      let tail  ← list (numBytes - bytesConsumed) elem
      pure (first :: tail)
    else
      fail "Infinite loop, elem does not consume bytes when parsing list"
  else
    pure []
  decreasing_by apply Nat.sub_lt <;> assumption

instance [ToBytes α] : ToBytes (List α) where
  toBytes := List.toBytes

-- #eval BinParsec.run (BinParsec.vector 3 BinParsec.uInt64) (Vector.toBytes (⟨[16909061, 16909060, 16909062], (by simp) ⟩ : Vector UInt64 3)) -- 16909060



def BinParsec.variableNumber (width : Nat) : BinParsec Nat := 
  if width = 1 then
    BinParsec.uInt8 >>= (fun i it => .success it i.toNat)
  else
    if width = 2 then
      BinParsec.uInt16 >>= (fun i it => .success it i.toNat)
    else
      if width = 3 then
        BinParsec.uInt24 >>= (fun i it => .success it i.val)
      else
        if width = 4 then
          BinParsec.uInt32 >>= (fun i it => .success it i.toNat)
        else 
          if width <= 8 then
            BinParsec.uInt64 >>= (fun i it => .success it i.toNat)
          else
            fail "Variable number with size more than 8 bytes unsupported"


def BinParsec.variableVector [ToBytes α] (lengthByteSize : Nat) (elem : BinParsec α) : BinParsec (VariableVector α n) := do
    let byteSize ← BinParsec.variableNumber lengthByteSize

    let content ← BinParsec.list byteSize elem

    if h : (content.map bytesize).sum < 2 ^ (8 * n) then
       pure ⟨ content , h ⟩
    else 
      fail "Bytesize to large in parsing vector"


-- #eval BinParsec.run (BinParsec.variableVector 2 10 BinParsec.uInt64) (VariableVector.toBytes (⟨#[16909061, 16909060, 16909062], ⟨by simp, by simp ⟩ ⟩ : VariableVector UInt64 2 10)) -- 16909060
deriving instance ToString for SessionId




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



def BinParsec.extensionData : BinParsec (ExtensionData eType hType) :=
  match eType, hType with
  | .supportedVersions , .clientHello => BinParsec.variableVector 1 BinParsec.uInt16
  | .supportedVersions , .serverHello => BinParsec.uInt16
  | _ , _ => do fail "Unimplemented"


def BinParsec.extension : BinParsec (Extension hType) := do
  let type ← BinParsec.extensionType
  let data ← BinParsec.extensionData
  pure (.mk type data)
 





def BinParsec.clientHello : BinParsec ClientHello := do
  let _ ← BinParsec.byte 3
  let _ ← BinParsec.byte 3
  let random ← BinParsec.list 32 BinParsec.uInt8
  let _ ← BinParsec.byte 0
  let suites ← BinParsec.variableVector 2 (BinParsec.list 2 BinParsec.uInt8)
  let _ ← BinParsec.byte 0
  let extensions ← BinParsec.variableVector 2 BinParsec.extension
  pure {
    random := random
    cipherSuites := suites
    extensions := extensions
  }


-- def ServerHello.toString : ServerHello → String := fun m =>
--   s!"random: {m.random}, cipherSuite : {m.cipherSuite}, extensions: {m.extensions}"

-- instance : ToString ServerHello where
--   toString := ServerHello.toString



def BinParsec.serverHello : BinParsec ServerHello := do
  let _ ← BinParsec.byte 3
  let _ ← BinParsec.byte 3
  let random ← BinParsec.list 32 BinParsec.uInt8
  let _ ← BinParsec.byte 0
  let suite ← BinParsec.list 2 BinParsec.uInt8
  let _ ← BinParsec.byte 0
  let extensions ← BinParsec.variableVector 2 BinParsec.extension
  pure {
    random := random
    cipherSuite := suite
    extensions := extensions
  }

  


def BinParsec.handshakeType : BinParsec HandshakeType := do
  let b ← BinParsec.uInt8
  match b with
  | 0 => pure .clientHello
  | 1 => pure .serverHello
  | _ => fail "Unimplemented handshake type"






def BinParsec.handshake : BinParsec (Handshake hType) := do
  let t ← BinParsec.handshakeType
  if t == hType then
    let l ← BinParsec.uInt24
    match hType with
    | .clientHello => 
      let body ← BinParsec.clientHello
      pure {
        length := l
        body := body
      }
    | .serverHello => 
      let body ← BinParsec.serverHello
      pure {
        length := l
        body := body
      }
    | _ => fail "Unimplemented handshake type"
  else
    fail "Unexpected type"

def BinParsec.contentType : BinParsec ContentType := do
  let b ← BinParsec.uInt8
  match b with
  | 20 => pure .changeCipherSpec
  | 21 => pure .alert
  | 22 => pure .handshake
  | 23 => pure .applicationData
  | _ => pure .invalid
  
def BinParsec.tLSPlaintext : BinParsec TLSPlaintext := do
  let t ← BinParsec.contentType
  let _ ← BinParsec.byte 3
  let _ ← BinParsec.byte 3
  let l ← BinParsec.uInt16
  let fragment ← BinParsec.list l.toNat BinParsec.uInt8
  pure {
    type := t
    length := l
    fragment := fragment.toArray
  }