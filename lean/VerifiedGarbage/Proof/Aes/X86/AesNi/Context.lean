import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
import VerifiedGarbage.Proof.Aes.X86.Ctr32CT

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk scrP schR ctrR datR scrR argR)
open VG.Spec.Gcm (Block blockAt aesWith)

section
variable (s₀ : State)
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem ((schP s₀).setWidth 64) (16 * (nRounds s₀ + 1))
abbrev cb : Block := blockAt s₀.mem ((ctrP s₀).setWidth 64)
abbrev ciph : Block → Block := aesWith (nRounds s₀) (sch s₀)
abbrev bAddr (k : Nat) : Addr := (datP s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)
abbrev blk (k : Nat) : Block := blockAt s₀.mem (bAddr s₀ k)
abbrev pfx : BitVec 96 := (s₀.mem.readW ((ctrP s₀).setWidth 64) 128).extractLsb' 0 96
end

namespace CPre
variable {s₀ : State} (hp : CPre s₀)
include hp

omit hp in
theorem key_contains {j : Nat} (hj : j ≤ 14) :
    (schR s₀).Contains ((schP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j)) 16 :=
  Offset.contains_base _ (by omega) (by omega)

theorem block_contains {k : Nat} (hk : k < nBlk s₀) :
    (datR s₀).Contains (bAddr s₀ k) 16 :=
  Offset.contains_base _ (by omega) (by have h := hp.fD; omega)

theorem block_out {k : Nat} (hk : k < nBlk s₀) : InRegions s₀.wr (bAddr s₀ k) 16 :=
  ⟨datR s₀, by simp [hp.wr], block_contains hp hk⟩

/-- Data and scratch writes preserve every byte of the schedule. -/
theorem sch_frame {m : Mem} (hf : Frame [datR s₀, scrR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m ((schP s₀).setWidth 64) (16 * (nRounds s₀ + 1)) = sch s₀ := by
  have hn : 16 * (nRounds s₀ + 1) ≤ 240 := by
    rcases hp.rounds with h | h | h <;> omega
  simp only [sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨(schP s₀).setWidth 64, 16 * (nRounds s₀ + 1)⟩) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dSD.sub_left (Region.sub_prefix hn)
    · exact hp.dSB.sub_left (Region.sub_prefix hn)) (by change 16 * (nRounds s₀ + 1) ≤ 2 ^ 64; omega) hi

/-- The readable round keys and their standard byte representation. -/
theorem keys {s : State} (hptr : s.gpr .eax = schP s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [datR s₀, scrR s₀] s₀.mem s.mem) :
    Keys (nRounds s₀) (sch s₀) s := by
  have hnr : nRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have he : ∀ j ≤ nRounds s₀, s.ea (Impl.Aes.X86.AesNi.at_ .eax (16 * j)) =
      (schP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j) := by
    intro j hj
    rw [ea_mk]
    simp only [Impl.Aes.X86.AesNi.at_]
    rw [hptr]
    exact addr_eq (by have h := hp.fS; omega)
  refine ⟨hnr, fun j hj => ?_, fun j hj => ?_⟩
  · rw [he j hj, hrd, hwr]
    refine ⟨schR s₀, ?_, key_contains (Nat.le_trans hj hnr)⟩
    simp only [hp.rd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or]
  · rw [he j hj, ← sch_frame hp hf]
    have h := byte_roundKey s.mem ((schP s₀).setWidth 64)
      (L := 16 * (nRounds s₀ + 1)) (j := j) (by omega)
    rw [ofInt_natCast] at h
    exact h

end CPre
end VG.Proof.Aes.X86.AesNi
