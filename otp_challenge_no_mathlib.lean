/- (Bitvectors are fixed-width sequences of binary digits. A bitvector can be understood from two perspectives: 
as a sequence of bits, or as a number encoded by a sequence of bits. When a bitvector represents a number, 
it can do so as either a signed or an unsigned number. Signed numbers are represented in two's complement form.)
-the lean language reference-


in this challenge you have a secret key ```k``` and want to send a message ```m``` (a string of bits/bitvector). 
you send the ciphertext c = k ^^^ m (k XOR m). the receiver reverses the ciphertext by k ^^^ c.
-/

def enc {n : Nat} (k m : BitVec n) : BitVec n := k ^^^ m
def dec {n : Nat} (k c : BitVec n) : BitVec n := k^^^ c

theorem xor_cancel {n : Nat} (a b : BitVec n) : a ^^^ b ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem otp_correct2 {n : Nat} (k m : BitVec n) : dec k (enc k m) = m := by
  unfold dec
  unfold enc
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]


theorem otp_reused_key2 {n : Nat} (k m_1 m_2 : BitVec n) :
    enc k m_1 ^^^ enc k m_2 = m_1 ^^^ m_2 := by
  unfold enc
  rw [BitVec.xor_assoc, ← BitVec.xor_assoc m_1 k m_2, BitVec.xor_comm m_1 k,
    BitVec.xor_assoc k m_1 m_2, ← BitVec.xor_assoc k k, BitVec.xor_self,
    BitVec.zero_xor]


theorem otp_perfect_secrecy3 {n : Nat} (m c : BitVec n) : 
  ∃ k, enc k m = c ∧ ∀ k', enc k' m = c → k' = k := by
  refine ⟨c ^^^ m, (?_), (?_)⟩
  · unfold enc
    exact xor_cancel c m
    
  · intro k hk
    unfold enc at hk
    rw [← hk]
    exact (xor_cancel k m).symm
