import Http.Ssl.Types

def UInt8.toBytes : UInt8 → Array UInt8 := fun i => #[i]

namespace Ssl

instance : ToBytes UInt8 where
  toBytes := UInt8.toBytes

def UInt16.toBytes : UInt16 → Array UInt8 := fun i => 
  #[(i.shiftRight (8*1)).toUInt8, (i.shiftRight (8*0)).toUInt8]

instance : ToBytes UInt16 where
  toBytes := UInt16.toBytes

def UInt24.toBytes : UInt24 → Array UInt8 := fun i =>
  #[(i.shiftRight (⟨8 , by simp ⟩*⟨ 2 , by simp ⟩)).val.toUInt8, 
    (i.shiftRight (⟨8 , by simp ⟩*⟨ 1 , by simp ⟩)).val.toUInt8, 
    (i.shiftRight (⟨8 , by simp ⟩*⟨ 0 , by simp ⟩)).val.toUInt8]

instance : ToBytes UInt24 where
  toBytes := UInt24.toBytes

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

instance : ToBytes UInt64 where
  toBytes := UInt64.toBytes

-- TODO fold into function
def concatMap (f : α → Array β) (as : List α) : Array β :=
  as.foldl (init := .empty) fun bs a => bs ++ f a


def List.toBytes [ToBytes α] : List α → Array UInt8
  := concatMap (fun a : α => (@ToBytes.toBytes α) a)

instance [ToBytes α] : ToBytes (List α) where
  toBytes := List.toBytes

def Nat.toVariableBytes (n : Nat) (numBytes : Nat) : List UInt8 :=
  match numBytes with
  | .zero => []
  | .succ b => (n.toUInt64.shiftRight (8 * b).toUInt64).toUInt8 :: Nat.toVariableBytes n b
#eval Nat.toVariableBytes 5 3

def VariableVector.toBytes [ToBytes α] : VariableVector α n → Array UInt8
  | as =>   
    let contents :=  as.foldl (init := .empty) fun bs a => bs ++ (@ToBytes.toBytes α) a
    let size : Array UInt8 := (Nat.toVariableBytes contents.size n).toArray
    size ++ contents

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

def ExtensionData.toBytes (eData : ExtensionData eType hType) : Array UInt8 := 
  let payloadFun : ExtensionData eType hType → Array UInt8  := match eType, hType with
  | .supportedVersions , .clientHello => @VariableVector.toBytes _ 1 _
  | .supportedVersions , .serverHello => UInt16.toBytes
  | _ , _ => fun _ => #[1]
  @VariableVector.toBytes _ 2 _ (payloadFun eData).toList

instance : ToBytes (ExtensionData eType hType) where
  toBytes := ExtensionData.toBytes

def Extension.toBytes (ext : Extension hType) : Array UInt8 :=
  ext.extensionType.toBytes ++ ext.extensionData.toBytes

instance : ToBytes (Extension hType) where
  toBytes := Extension.toBytes


def ClientHello.toBytes : ClientHello → Array UInt8 := fun ch =>
  -- v1.2 hardcoded
  #[0x03, 0x03] 
    ++ List.toBytes ch.random 
    -- Legacy session id
    ++ #[0] 
    ++ ch.cipherSuites.toBytes 
    -- Legacy Compression methods
    ++ #[1, 0]
    ++ ch.extensions.toBytes

instance : ToBytes ClientHello where
  toBytes := ClientHello.toBytes

def ServerHello.toBytes : ServerHello → Array UInt8 := fun ch =>
  -- v1.2 hardcoded
  #[0x03, 0x03] 
    ++ List.toBytes ch.random 
    -- Legacy session id
    ++ #[0] 
    ++ List.toBytes ch.cipherSuite
    -- Legacy Compression methods
    ++ #[1, 0]
    ++ ch.extensions.toBytes

instance : ToBytes ServerHello where
  toBytes := ServerHello.toBytes

def HandshakeType.toBytes : HandshakeType → Array UInt8
  | .clientHello => #[1]
  | .serverHello => #[2]
  | _ => #[0]

instance : ToBytes HandshakeType where
  toBytes := HandshakeType.toBytes

def Handshake.toBytes : Handshake hType → Array UInt8 := fun msg =>
  let bodyFunction : hType.asType → Array UInt8 := match hType with
  | .clientHello => ClientHello.toBytes
  | .serverHello => ServerHello.toBytes
  | _ => fun _ => #[1, 3, 3, 7]
  hType.toBytes ++ msg.length.toBytes ++ (bodyFunction msg.body)

instance : ToBytes (Handshake hType) where
  toBytes := Handshake.toBytes

def ContentType.toBytes : ContentType → Array UInt8
  | .invalid => #[0]
  | .changeCipherSpec => #[20]
  | .alert => #[21]
  | .handshake => #[22]
  | .applicationData => #[23]

instance : ToBytes ContentType where
  toBytes := ContentType.toBytes

def TLSPlaintext.toBytes (plain : TLSPlaintext) : Array UInt8 :=
  plain.type.toBytes 
  -- legacy record version
  ++ #[3, 1] ++ 
  UInt16.toBytes plain.length
  ++ plain.fragment

instance : ToBytes (TLSPlaintext) where
  toBytes := TLSPlaintext.toBytes