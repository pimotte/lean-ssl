import Http.Ssl.ToBytes

namespace Ssl

def Extension.bytesize_eq (extension : Extension hType) : extension.toBytes.length = 2 + extension.extensionData.toBytes.length := by
  simp [Extension.toBytes, Array.size]
  induction extension.extensionType <;> simp

def Nat.bytesize_eq (n : Nat) (numBytes : Nat): (Nat.toVariableBytes n numBytes).length = numBytes := by
  induction numBytes with
  | zero => simp
  | succ nb ih => simp [ih]

def VariableVector.bytesize_eq [ToBytes α] (vec : VariableVector α n) : bytesize vec = n + (vec.val.map bytesize).sum := by
  rw [bytesize, ToBytes.toBytes,]
  unfold instToBytesVariableVector
  simp [toBytes]
 sorry
 -- dsimp [bytesize, ToBytes.toBytes, toBytes]