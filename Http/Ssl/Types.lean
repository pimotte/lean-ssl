import Mathlib.Data.List.BigOperators.Basic

namespace Ssl

class ToBytes (α : Type) where
  toBytes : α → List UInt8
  
  
def bytesize [ToBytes α] : α → Nat := fun a => (ToBytes.toBytes a).length

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


abbrev VariableVector (α : Type) [ToBytes α] (lengthByteSize : Nat) := {as : List α // (as.map bytesize).sum < 2^(8 *lengthByteSize) }


def List.toBytes [ToBytes α] : List α → List UInt8
  := List.foldl (init := []) fun bs a => bs ++ ToBytes.toBytes a 

instance [ToBytes α] : ToBytes (List α) where
  toBytes := List.toBytes

@[simp]
def Nat.toVariableBytes (n : Nat) (numBytes : Nat) : List UInt8 :=
  match numBytes with
  | .zero => []
  | .succ b => (n.toUInt64.shiftRight (8 * b).toUInt64).toUInt8 :: Nat.toVariableBytes n b
-- #eval Nat.toVariableBytes 5 3

def VariableVector.toBytes [ToBytes α] : VariableVector α n → List UInt8
  | as =>   
    let contents :=  as.val.foldl (init := []) fun bs a => bs ++ (@ToBytes.toBytes α) a
    let size := (Nat.toVariableBytes contents.length n)
    size ++ contents

instance [ToBytes α] : ToBytes (VariableVector α n) where
  toBytes := VariableVector.toBytes


abbrev Random := List UInt8 
deriving instance ToString for Random

def UInt8.toBytes : UInt8 → List UInt8 := fun i => [i]

instance : ToBytes UInt8 where
  toBytes := UInt8.toBytes

def UInt16.toBytes : UInt16 → List UInt8 := fun i => 
  [(i.shiftRight (8*1)).toUInt8, (i.shiftRight (8*0)).toUInt8]

instance : ToBytes UInt16 where
  toBytes := UInt16.toBytes

def UInt24.toBytes : UInt24 → List UInt8 := fun i =>
  [(i.shiftRight (⟨8 , by simp ⟩*⟨ 2 , by simp ⟩)).val.toUInt8, 
    (i.shiftRight (⟨8 , by simp ⟩*⟨ 1 , by simp ⟩)).val.toUInt8, 
    (i.shiftRight (⟨8 , by simp ⟩*⟨ 0 , by simp ⟩)).val.toUInt8]

instance : ToBytes UInt24 where
  toBytes := UInt24.toBytes

def UInt32.toBytes : UInt32 → List UInt8 :=
  fun i => [(i.shiftRight (8*3)).toUInt8, (i.shiftRight (8*2)).toUInt8, 
            (i.shiftRight (8*1)).toUInt8, (i.shiftRight (8*0)).toUInt8]

-- #eval UInt32.toBytes ⟨5000, by simp⟩ -- #[0, 0, 19, 136]
-- #eval UInt32.toBytes 16909060 -- #[1, 2, 3, 4]

instance : ToBytes UInt32 where
  toBytes := UInt32.toBytes

def UInt64.toBytes : UInt64 → List UInt8 :=
  fun i => [(i.shiftRight (8*7)).toUInt8, (i.shiftRight (8*6)).toUInt8, 
            (i.shiftRight (8*5)).toUInt8, (i.shiftRight (8*4)).toUInt8,
            (i.shiftRight (8*3)).toUInt8, (i.shiftRight (8*2)).toUInt8, 
            (i.shiftRight (8*1)).toUInt8, (i.shiftRight (8*0)).toUInt8]

instance : ToBytes UInt64 where
  toBytes := UInt64.toBytes

abbrev SessionId := VariableVector UInt8 1


abbrev CipherSuite := List UInt8 

def CipherSuite.TLS_AES_128_GCM_SHA256 : CipherSuite := [0x13,0x02]


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

def SupportedVersions.tls1_3 : ProtocolVersion := 0x0304

abbrev Hostname := VariableVector UInt8 2




def ExtensionType.toBytes : ExtensionType → List UInt8
  | .serverName => [0, 0]
  | .maxFragmentLength => [0, 1]
  | .statusRequest => [0, 5]
  | .supportedGroups => [0, 10]
  | .signatureAlgorithms => [0, 13]
  | .useSrtp => [0, 14]
  | .heartbeat => [0, 15]
  | .applicationLayerProtocolNegotiation => [0, 16]
  | .signedCertificateTimestamp => [0, 18]
  | .clientCertificateType => [0, 19]
  | .serverCertificateType => [0, 20]
  | .padding => [0, 21]
  | .preSharedKey => [0, 41]
  | .earlyData => [0, 42]
  | .supportedVersions => [0, 43]
  | .cookie => [0, 44]
  | .pskKeyExchangeModes => [0, 45]
  | .certificateAuthorities => [0, 47]
  | .oidFilters => [0, 48]
  | .postHandshakeAuth => [0, 49]
  | .signatureAlgorithmsCert => [0, 50]
  | .keyShare => [0, 51]

instance : ToBytes ExtensionType where
  toBytes := ExtensionType.toBytes

structure ServerName where
  -- NameType can only be host name
  name : Hostname

def ServerName.toBytes : ServerName → List UInt8 := fun sn => [0] ++ sn.name.toBytes

instance : ToBytes ServerName where
  toBytes := ServerName.toBytes

abbrev ServerNameList := VariableVector ServerName 2

def ExtensionData : ExtensionType → HandshakeType → Type
  | .supportedVersions , .clientHello => SupportedVersions
  | .supportedVersions , .serverHello => ProtocolVersion
  | .serverName , _ => ServerNameList
  | _, _  => VariableVector UInt8 1

structure Extension (hType : HandshakeType) where
  extensionType : ExtensionType
  extensionData : ExtensionData extensionType hType 

def ExtensionData.toBytes (eData : ExtensionData eType hType) : List UInt8 := 
  let rawBytes := match eType, hType with
  | .supportedVersions , .clientHello => VariableVector.toBytes eData
  | .supportedVersions , .serverHello => UInt16.toBytes eData
  | .serverName , _ => VariableVector.toBytes eData
  | _ , _ => [1]
  let size := (Nat.toVariableBytes rawBytes.length 2)
  size ++ rawBytes

instance : ToBytes (ExtensionData eType hType) where
  toBytes := ExtensionData.toBytes

def Extension.toBytes (ext : Extension hType) : List UInt8 :=
  ext.extensionType.toBytes ++ ext.extensionData.toBytes

instance : ToBytes (Extension hType) where
  toBytes := Extension.toBytes






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

structure Handshake where
  hType : HandshakeType
  length : UInt24
  body : hType.asType

inductive AlertLevel
  | warning | fatal
deriving Repr

def AlertLevel.toBytes : AlertLevel → List UInt8
  | .warning => [1]
  | .fatal => [2]

instance : ToBytes AlertLevel where
  toBytes := AlertLevel.toBytes

inductive AlertDescription
  | closeNotify | unexpectedMessage | badRecordMac | recordOverflow
  | handshakeFailure | badCertificate | unsupportedCertificate | certificateRevoked
  | certificateExpired | certificateUnknown | illegalParameter | unknownCa
  | accessDenied | decodeError | decryptError | protocolVersion | insufficientSecurity
  | internalError | inappropriateFallback | userCanceled | missingExtension
  | unsupportedExtension | unrecognizedName | badCertificateResponseStatus
  | unknownPskIdentity | certificateRequired | noApplicationProtocol
deriving Repr

def AlertDescription.toBytes : AlertDescription → List UInt8
  | .closeNotify => [0]
  | .unexpectedMessage => [10]
  | .badRecordMac => [20]
  | .recordOverflow => [22]
  | .handshakeFailure => [40]
  | .badCertificate => [42]
  | .unsupportedCertificate => [43]
  | .certificateRevoked => [44]
  | .certificateExpired => [45]
  | .certificateUnknown => [46]
  | .illegalParameter => [47]
  | .unknownCa => [48]
  | .accessDenied => [49]
  | .decodeError => [50]
  | .decryptError => [51]
  | .protocolVersion => [70]
  | .insufficientSecurity => [71]
  | .internalError => [80]
  | .inappropriateFallback => [86]
  | .userCanceled => [90]
  | .missingExtension => [109]
  | .unsupportedExtension => [110]
  | .unrecognizedName => [112]
  | .badCertificateResponseStatus => [113]
  | .unknownPskIdentity => [115]
  | .certificateRequired => [116]
  | .noApplicationProtocol => [120]

instance : ToBytes AlertDescription where
  toBytes := AlertDescription.toBytes

structure Alert where
  level : AlertLevel
  description : AlertDescription
deriving Repr

def Alert.toBytes : Alert → List UInt8 := fun al =>
  (level al).toBytes ++ (description al).toBytes

inductive ContentType where
  | invalid | changeCipherSpec | alert
  | handshake | applicationData

structure TLSPlaintext where
  type : ContentType
  length : UInt16
  fragment : List UInt8