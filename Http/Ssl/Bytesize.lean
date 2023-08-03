import Http.Ssl.ToBytes

namespace Ssl

def UInt8.bytesize_eq (i : UInt8) : bytesize i = 1 := by simp [bytesize, List.length]

def Extension.bytesize_eq (extension : Extension hType) : bytesize extension = 2 + bytesize extension.extensionData := by
  unfold bytesize
  rw [ToBytes.toBytes]
  unfold instToBytesExtension
  simp
  rw [Extension.toBytes, List.length_append]
  congr
  induction extension.extensionType <;> simp

def Nat.bytesize_eq (n : Nat) (numBytes : Nat): (Nat.toVariableBytes n numBytes).length = numBytes := by
  induction numBytes with
  | zero => simp
  | succ nb ih => simp [ih]

def List.bytesize_cons [ToBytes α] (a : α) (as : List α) : bytesize (a :: as) = bytesize a + bytesize as := by
  rw [bytesize, ToBytes.toBytes]
  unfold instToBytesList
  simp
  rw [toBytes]
  unfold List.foldr
  rw [List.length_append]
  rw [bytesize, bytesize, add_comm]
  congr
  
def List.bytesize_eq [ToBytes α] (as : List α) : bytesize as = (as.map bytesize).sum := by
  induction as with
  | nil => simp [bytesize, List.length]
  | cons a as ih => {
    rw [List.map_cons, List.sum_cons]
    rw [List.bytesize_cons _ _]
    congr
  }

def VariableVector.bytesize_eq [ToBytes α] (vec : VariableVector α n) : bytesize vec = n + (vec.val.map bytesize).sum := by
  rw [bytesize, ToBytes.toBytes]
  unfold instToBytesVariableVector
  simp [toBytes]
  rw [Nat.bytesize_eq]
  congr
  rw [← List.bytesize_eq]
  unfold bytesize ToBytes.toBytes instToBytesList
  simp [List.toBytes]
  congr

def ServerName.bytesize_eq (servName : ServerName) : bytesize servName = 1 + bytesize servName.name := by
  rw [bytesize, ToBytes.toBytes]
  unfold instToBytesServerName
  simp [ServerName.toBytes]
  rw [bytesize, ToBytes.toBytes]
  unfold instToBytesVariableVector
  simp_arith

def ExtensionData.bytesize_supportedversions_client_eq 
  (eData : ExtensionData .supportedVersions .clientHello) : bytesize eData = 1 + (eData.val.map bytesize).sum := by
    rw [bytesize, ToBytes.toBytes]
    unfold instToBytesExtensionData
    simp [ExtensionData.toBytes]
    simp_arith
    rw [add_comm]
    rw [← VariableVector.bytesize_eq]
    rw [VariableVector.bytesize_eq _]

  