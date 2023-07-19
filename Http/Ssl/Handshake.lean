namespace Ssl

-- Use RFC 8446 as base

class ToBytes (α : Type) where
  toBytes : α → Array UInt8

abbrev Vector (α : Type) (n : Nat) := Subtype (fun arr : List α => arr.length = n)

class FromBytes (α : Type) (n : Nat) where
  fromBytes : Vector UInt8 n → Except String α

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

-- def Vector.fromBytes [FromBytes α p] : Vector UInt8 (m * p) → Except String (Vector α m) := fun arr =>
--   match m with
--   | .zero => .ok ⟨ [], _ ⟩
--   | (.succ m) =>
--     match (FromBytes.fromBytes ⟨ ⟩).toArray, by {
--       simp
      
--     }⟩ : Except String α) with
--     | .ok a => _
--     | .error s => .error s

instance [ToBytes α] : ToBytes (Vector α n) where
  toBytes := fun v => Vector.toBytes v

abbrev VariableVector (α : Type) (lower : Nat) (upper : Nat) := 
  Subtype (fun arr : Array α => lower <= arr.size ∧ arr.size <= upper)

def VariableVector.toBytes [ToBytes α] : VariableVector α l u → Array UInt8
  | ⟨ arr , _ ⟩ => 
  arr.concatMap (fun a : α => (@ToBytes.toBytes α) a)

structure Random where
  gmxUnixTime : UInt32
  randomBytes : Vector UInt8 28

def UInt8.toBytes : UInt8 → Array UInt8 := fun i => #[i]

instance : ToBytes UInt8 where
  toBytes := UInt8.toBytes

def UInt32.toBytes : UInt32 → Array UInt8 :=
  fun i => #[(i.shiftRight (8*3)).toUInt8, (i.shiftRight (8*2)).toUInt8, 
            (i.shiftRight (8*1)).toUInt8, (i.shiftRight (8*0)).toUInt8]

-- #eval UInt32.toBytes 5000 -- #[0, 0, 19, 136]

instance : ToBytes UInt32 where
  toBytes := UInt32.toBytes

def Random.toBytes : Random → Array UInt8 :=
  fun r => ToBytes.toBytes (gmxUnixTime r) ++ (randomBytes r).val


abbrev SessionId := VariableVector UInt8 0 32

abbrev CipherSuite := Vector UInt8 2
 

structure ClientHello where
  protocolVersion : ProtocolVersion
  random : Random
  cipherSuites : VariableVector CipherSuite 2 (2^16-1)
  -- extensions : to be implemented

-- v1.2 hardcoded
def ClientHello.toBytes : ClientHello → Array UInt8 := fun ch =>
  #[0x03, 0x03] ++ ch.random.toBytes ++ #[0] ++ ch.cipherSuites.toBytes ++ #[0]
   -- Empty extensions
   ++ #[0 , 0]

structure ServerHello where
  serverVersion : ProtocolVersion
  random : Random
  sessionId : SessionId
  cipherSuite : CipherSuite
  compressionMethod : CompressionMethod

def HandshakeType.asType : HandshakeType → Type
  | .clientHello => ClientHello
  | _ => String

abbrev UInt24 := Subtype (fun n : UInt32 => n <= 167777215)

structure Handshake (hType : HandshakeType) where
  length : UInt24
  body : hType.asType
