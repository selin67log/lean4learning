import Mathlib

def enc {n : ℕ} (k m : BitVec n) : BitVec n := k ^^^ m
def dec {n : ℕ} (k c : BitVec n) : BitVec n := k^^^ c

theorem otp_correct {n : ℕ} (k m : BitVec n) : dec k (enc k m) = m := by
  simp [dec, enc]

theorem otp_reused_key {n : ℕ} (k m_1 m_2 : BitVec n) :
    enc k m_1 ^^^ enc k m_2 = m_1 ^^^ m_2 := by
  unfold enc
  rw [BitVec.xor_assoc, ← BitVec.xor_assoc m_1 k m_2, BitVec.xor_comm m_1 k,
    BitVec.xor_assoc k m_1 m_2, ← BitVec.xor_assoc k k, BitVec.xor_self,
    BitVec.zero_xor]


theorem otp_perfect_secrecy {n : ℕ} (m_1 m_2 c : BitVec n) :
  (Finset.univ.filter (λ k => enc k m_1 = c)).card =
  (Finset.univ.filter (λ k => enc k m_2 = c)).card := by
  apply Finset.card_nbij' (fun k => k ^^^ m_1 ^^^ m_2) (fun k => k ^^^ m_2 ^^^ m_1)
  · intro k hk
    have h : enc k m_1 = c := (Finset.mem_filter.mp hk).2
    unfold enc at h
    unfold enc
    rw [← h]
    simp
  · intro k hk
    have h : enc k m_2 = c := (Finset.mem_filter.mp hk).2
    unfold enc at h 
    unfold enc 
    rw [← h]
    simp
  · intro k
    simp
  · intro k
    simp
