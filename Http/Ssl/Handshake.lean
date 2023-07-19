import Std.Data.List.Lemmas
import Std.Data.Nat.Lemmas

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

def ineq_lemma (n p : Nat) : p ≤ (.succ n) * p := by
  induction p with
  | zero => simp
  | succ p' ihp => {
    rw [Nat.mul_succ, ← Nat.add_one]
    exact Nat.add_le_add ihp (Nat.pos_of_ne_zero (by simp))
  }

def nat_lemma : Nat.succ m * p - p = m * p := by 
  induction p with
  | zero => simp
  | succ p' ihp => {
    rw [Nat.mul_succ, Nat.succ_mul, Nat.mul_succ, ← ihp]
    
  }


def Vector.take (h : n ≤ m) (as : Vector α m) : Vector α n :=
  let ⟨ asl , aslh ⟩ := as
  let taken := asl.take n
  ⟨ taken , List.length_take_of_le (aslh ▸ h)⟩

theorem length_drop_of_le (h : n ≤ List.length l) : List.length (.drop n l) = List.length l - n := by simp

def Vector.drop (h : n ≤ m) (as : Vector α m) : Vector α (m - n) :=
  let ⟨ asl , aslh ⟩ := as
  let taken := asl.drop n
  ⟨ taken , aslh ▸ length_drop_of_le (aslh ▸ h)⟩

def Vector.fromBytes [FromBytes α p] : Vector UInt8 (m * p) → Except String (Vector α m) := fun as =>
  match m with
  | .zero => .ok ⟨ [], (by simp) ⟩
  | (.succ m) => 
    match ((FromBytes.fromBytes (Vector.take (ineq_lemma _ _) as)) : Except String α) with
    | .ok a => 
      match Vector.fromBytes (Vector.drop (ineq_lemma _ _) as) with
      | .ok ⟨ as , ash ⟩ => Except.ok (⟨a :: as, ash ▸ List.length_cons a as⟩ )
      | .error e => Except.error e
    | .error e => Except.error e
  
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
