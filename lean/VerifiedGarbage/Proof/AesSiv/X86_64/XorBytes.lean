import VerifiedGarbage.Proof.AesSiv.X86_64.Env
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy

/-!
# AES-SIV on x86-64: XORing a keystream block into the data (`xorBytes`)

`xorBytes` XORs the first `n` bytes (1 to 16) of the keystream block at
`K` into the data at `Q`, a byte at a time, changing only `rax`, `rdx`,
`r10` and the flags: the data then holds `Q[..n] ⊕ K[..n]` (`xorBytes_wp`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Proof.CmacAes.X86_64 (succ_ofNat bytesAt_succ)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)

theorem byte_xor (a b : Byte) : ((a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 : Byte) = a ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

theorem xorStep_ok (s : State) {Q K : Addr} {j n : Nat} (h13 : s.gpr .r13 = Q)
    (hk : s.gpr .r15 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (ksOff : Int) = K + BitVec.ofNat 64 j)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (hrcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 j) 1) (rk : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 j) 1)
    (wq : InRegions s.wr (Q + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax dataByte, .movzx8 .rdx ksByte, .alu .xor .rax (.reg .rdx),
        .store8 dataByte .rax, .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)] s = some s' ∧
      s'.mem = s.mem.writeW (Q + BitVec.ofNat 64 j)
        ((s.mem (Q + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j) : Byte)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 1 ∧
      s'.zf = some (BitVec.ofNat 64 j + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r13 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = Q + BitVec.ofNat 64 j := by
    rw [h13, h10, BitVec.mul_one]; simp
  refine ⟨_, by
    simp (config := {decide := true}) only [dataByte, ksByte, imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
      ite_false, ea, hk, rq, rk, wq]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, byte_xor]
  · simp [gpr_setReg, h10]
  · simp [h10, hrcx]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
  all_goals rfl

/-- What `xorBytes` leaves. -/
structure Xored (s : State) (Q : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem Q xs
  other : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem xorBytes_wp (s : State) {Q K W : Addr} {n : Nat} (hn : 0 < n) (hn16 : n ≤ 16) (h13 : s.gpr .r13 = Q)
    (h15 : s.gpr .r15 = W) (hK : W + BitVec.ofNat 64 ksOff = K) (hrcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1)
    (hrk : ∀ i < n, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (Q + BitVec.ofNat 64 i) 1)
    (hdis : (⟨Q, n⟩ : Region).Disjoint ⟨K, n⟩) (hwq : Q.toNat + n ≤ 2 ^ 64) :
    WP isa xorBytes s
      (Xored s Q (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q n) (Spec.Aes.bytesAt s.mem K n))) := by
  obtain ⟨s₁, run₁, r10₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (.imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .r10 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r h; simp [gpr_setReg, h]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .r10 = BitVec.ofNat 64 j ∧
      t.mem = writeBytes s.mem Q (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q j) (Spec.Aes.bytesAt s.mem K j)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn, r10₁, by rw [m₁]; simp [Spec.Aes.bytesAt, Spec.Cmac.xor, writeBytes_nil],
      fun r _ _ h₃ => g₁ r h₃, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, r10, mem, g, rd, wr⟩
  have hk : t.gpr .r15 + t.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (ksOff : Int) = K + BitVec.ofNat 64 j := by
    rw [g _ (by decide) (by decide) (by decide), h15, r10, BitVec.mul_one, ← hK]
    simp only [BitVec.ofInt_natCast]
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j), ← BitVec.add_assoc]
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := xorStep_ok t (Q := Q) (K := K) (j := j) (n := n)
    (by rw [g _ (by decide) (by decide) (by decide), h13]) hk r10
    (by rw [g _ (by decide) (by decide) (by decide), hrcx])
    (by rw [rd, wr]; exact hr j hj) (by rw [rd, wr]; exact hrk j hj) (by rw [wr]; exact hw j hj)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q j) (Spec.Aes.bytesAt s.mem K j)).length = j := by
    simp [Proof.Cmac.length_xor, Spec.Aes.bytesAt]
  have fr : Frame [⟨Q, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [hlen]; exact Region.contains_self _ _)
  have hq : t.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat Q (show j < 2 ^ 64 by omega)] at hcon; omega
  have hkk : t.mem (K + BitVec.ofNat 64 j) = s.mem (K + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdis _ (Region.sub_prefix (by omega) _ hcon) (Offset.contains_base K (by omega) (by omega))
  have hmem : t'.mem = writeBytes s.mem Q
      (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q (j + 1)) (Spec.Aes.bytesAt s.mem K (j + 1))) := by
    rw [mem', hq, hkk, mem, bytesAt_succ, bytesAt_succ, Proof.Cmac.xor_append (by simp [Spec.Aes.bytesAt]),
      show Spec.Cmac.xor [s.mem (Q + BitVec.ofNat 64 j)] [s.mem (K + BitVec.ofNat 64 j)] =
        [s.mem (Q + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j)] from rfl,
      writeBytes_snoc _ _ _ _ (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (j + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  by_cases he : j + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (j + 1), by omega, j + 1, rfl, by omega, by rw [r10', succ_ofNat], hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesSiv.X86_64
