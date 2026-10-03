import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Pre

/-! # Restricting ECB permissions to a consecutive subrange -/

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86
open VG.Proof.Rc2.X86 (addr32 addr_add)

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n) (hm : 1 ≤ m)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .ebx = s.gpr .ebx)
    (buf : s'.gpr .ebp = s.gpr .ebp)
    (sp : s'.gpr .esp = s.gpr .esp)
    (ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * i)) : StepPre s' m := by
  have fit : (s.gpr .esi).toNat + 8 * i < 2 ^ 32 := by omega_using [hp.dataFit, bound, hm]
  have ptrAddr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * i) := by
    rw [ptr, addr_add fit]
  have sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptrAddr]
    exact Offset.sub_base _ (by omega)
  constructor
  · have hc : Covers [keyR s', dataR s' m, bufR s'] [keyR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [dataR s' m, bufR s'] [dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub
  · rw [key]; exact hp.keyFit
  · rw [ptr]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [fit] : 8 * i < 2 ^ 32), Nat.mod_eq_of_lt fit]
    omega_using [hp.dataFit, bound]
  · rw [buf]; exact hp.bufFit
  · rw [sp]; exact hp.stackLo
  · simpa only [keyR, key, sp] using hp.stackKey
  · rw [sp]; exact hp.stackData.sub_right sub
  · simpa only [bufR, buf, sp] using hp.stackBuf

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn (by decide) rfl rfl rfl rfl rfl (by simp)

end VG.Proof.TripleDes.X86.Ecb
