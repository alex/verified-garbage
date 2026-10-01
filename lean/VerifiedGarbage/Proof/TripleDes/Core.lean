import VerifiedGarbage.Proof.TripleDes.Permutation

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

theorem ip_bounds : ∀ k < 64, 1 ≤ ip.getD k 1 ∧ ip.getD k 1 ≤ 64 := by decide
theorem fp_bounds : ∀ k < 64, 1 ≤ fp.getD k 1 ∧ fp.getD k 1 ≤ 64 := by decide

theorem ip_fp_positions : ∀ j < 64,
    64 - fp.getD (64 - 1 - (64 - ip.getD (64 - 1 - j) 1)) 1 = j := by decide

theorem fp_ip_positions : ∀ j < 64,
    64 - ip.getD (64 - 1 - (64 - fp.getD (64 - 1 - j) 1)) 1 = j := by decide

theorem ip_fp (x : BitVec 64) : permute ip (permute fp x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj' : 64 - 1 - j < 64 := by omega
  obtain ⟨lo, hi⟩ := ip_bounds _ hj'
  have hk : 64 - ip.getD (64 - 1 - j) 1 < 64 := by omega
  rw [permute_bit ip _ (by decide) j hj,
    permute_bit fp _ (by decide) _ hk, ip_fp_positions j hj]

theorem fp_ip (x : BitVec 64) : permute fp (permute ip x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj' : 64 - 1 - j < 64 := by omega
  obtain ⟨lo, hi⟩ := fp_bounds _ hj'
  have hk : 64 - fp.getD (64 - 1 - j) 1 < 64 := by omega
  rw [permute_bit fp _ (by decide) j hj,
    permute_bit ip _ (by decide) _ hk, fp_ip_positions j hj]

def feistelStep (k : BitVec 48) (state : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 :=
  (state.2, state.1 ^^^ roundFunction state.2 k)

/-- DES between IP and FP, including its final half swap. -/
def desCore (keys : DesSchedule) (direction : Direction) (input : BitVec 64) : BitVec 64 :=
  let (l, r) := (List.range 16).foldl (fun state j =>
    feistelStep (keys.getD (if direction = .encrypt then j else 15 - j) 0) state)
      ((input >>> 32).setWidth 32, input.setWidth 32)
  r ++ l

theorem des_eq_core (keys : DesSchedule) (direction : Direction) (input : BitVec 64) :
    des keys direction input = permute fp (desCore keys direction (permute ip input)) := rfl

theorem encryptBlock_eq_cores (k : Schedule) (b : Block) :
    encryptBlock k b = encodeBlock (permute fp
      (desCore (componentSchedule k 2) .encrypt
        (desCore (componentSchedule k 1) .decrypt
          (desCore (componentSchedule k 0) .encrypt (permute ip (decodeBlock b)))))) := by
  unfold encryptBlock
  rw [des_eq_core, des_eq_core, des_eq_core, ip_fp, ip_fp]

theorem decryptBlock_eq_cores (k : Schedule) (b : Block) :
    decryptBlock k b = encodeBlock (permute fp
      (desCore (componentSchedule k 0) .decrypt
        (desCore (componentSchedule k 1) .encrypt
          (desCore (componentSchedule k 2) .decrypt (permute ip (decodeBlock b)))))) := by
  unfold decryptBlock
  rw [des_eq_core, des_eq_core, des_eq_core, ip_fp, ip_fp]

def roundKey (keys : DesSchedule) (direction : Direction) (j : Nat) : BitVec 48 :=
  keys.getD (if direction = .encrypt then j else 15 - j) 0

def roundPrefix (keys : DesSchedule) (direction : Direction) (n : Nat)
    (v : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 :=
  (List.range n).foldl (fun state j => feistelStep (roundKey keys direction j) state) v

theorem roundPrefix_zero (keys : DesSchedule) (direction : Direction)
    (v : BitVec 32 × BitVec 32) : roundPrefix keys direction 0 v = v := rfl

theorem roundPrefix_succ (keys : DesSchedule) (direction : Direction) (n : Nat)
    (v : BitVec 32 × BitVec 32) :
    roundPrefix keys direction (n + 1) v =
      feistelStep (roundKey keys direction n) (roundPrefix keys direction n v) := by
  unfold roundPrefix
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

theorem desCore_roundPrefix (keys : DesSchedule) (direction : Direction)
    (v : BitVec 64) :
    desCore keys direction v =
      let halves := roundPrefix keys direction 16 ((v >>> 32).setWidth 32, v.setWidth 32)
      halves.2 ++ halves.1 := rfl

end VG.Proof.TripleDes
