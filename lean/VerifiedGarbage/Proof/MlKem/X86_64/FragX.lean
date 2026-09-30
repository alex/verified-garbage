import VerifiedGarbage.Impl.MlKem.X86_64.Expanded
import VerifiedGarbage.Proof.MlKem.X86_64.FragS

/-!
# ML-KEM-768 on x86-64: copies 16 bytes at a time

Untrusted: everything here is checked by Lean. What `copy16` does
(`copy16_ok`), and in a layout (`copy16_okL`), with the checks of a copy of
`16 n` bytes (`copyChk`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.Sha3 (bytesAt)

/-- A byte after a 16-byte store of a 16-byte load. -/
theorem writeW_readW128 (m m' : Mem) (d a x : Addr) :
    (m.writeW d (m'.readW a 128)) x =
      if (x - d).toNat < 16 then m' (a + BitVec.ofNat 64 (x - d).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, Nat.reduceDiv, Nat.reduceMul]
  split
  · rename_i h
    rw [← Mem.extractLsb'_read m' a (n := 16) h]
    rfl
  · rfl

theorem copy16Body_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16)
    (h1 : InRegions s.wr (s.gpr .rdi) 16) :
    WP isa (.block [.movdquLoad .xmm0 (at_ .rsi 0), .movdquStore (at_ .rdi 0) .xmm0, .alu .add .rdi (.imm 16),
      .alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem.readW (s.gpr .rsi) 128) ∧ s'.gpr .rdi = s.gpr .rdi + 16 ∧
        s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h0, h1, State.load128, State.store128, RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm,
    RegUpd.wr_setXmm, RegUpd.zf_setXmm, RegUpd.xmm_setReg, RegUpd.xmm_setFlags,
    RegUpd.xmm_setXmm_self]

theorem copy16_ok (dst src : Ptr) (n : Nat) (hn0 : 0 < n) (hn : 16 * n < 2 ^ 31) (hd : dst.2 < 2 ^ 31)
    (hs : src.2 < 2 ^ 31) (hsr : src.1 ≠ .rdi) (s : State)
    (hrd : InRegions (s.rd ++ s.wr) (pa s src) (16 * n)) (hwr : InRegions s.wr (pa s dst) (16 * n))
    (hdj : Region.Disjoint ⟨pa s src, 16 * n⟩ ⟨pa s dst, 16 * n⟩) :
    WP isa (copy16 dst src n) s fun s' =>
      bytesAt s'.mem (pa s dst) (16 * n) = bytesAt s.mem (pa s src) (16 * n) ∧
        Frame [⟨pa s dst, 16 * n⟩] s.mem s'.mem ∧ Keep [.rax, .rcx, .rsi, .rdi] s s' := by
  unfold copy16 lea
  refine WP.seq (WP.mono (WP.keep [.rdi, .rsi, .rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rdi = pa s dst ∧
      s'.gpr .rsi = pa s src ∧ s'.gpr .rcx = BitVec.ofNat 64 n)
    (by xrun [sx_ofNat hd, sx_ofNat hs, hsr, List.cons_append, List.nil_append, sw_ofNat (show n < 2 ^ 32 by omega)])
    (by rfl)) fun s1 ⟨⟨hm1, hdi1, hsi1, hcx1⟩, k1⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .rcx) (N := n) (by omega) hn0 (fun k s' =>
      s'.gpr .rdi = pa s dst + BitVec.ofNat 64 (16 * k) ∧ s'.gpr .rsi = pa s src + BitVec.ofNat 64 (16 * k) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨pa s dst, 16 * n⟩] s.mem s'.mem ∧
      (∀ j < 16 * k, s'.mem (pa s dst + BitVec.ofNat 64 j) = s.mem (pa s src + BitVec.ofNat 64 j)) ∧
      Keep [.rax, .rcx, .rsi, .rdi] s s')
    (fun k hk s' ⟨hdi, hsi, hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [hdi1]; simp, by rw [hsi1]; simp, k1.2.1, k1.2.2, by rw [hm1]; exact Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), k1.mono (by decide)⟩ hcx1)
    fun s' ⟨_, _, _, _, hf, hc, kk⟩ => ⟨?_, hf, kk⟩
  · have hr16 : InRegions (s'.rd ++ s'.wr) (s'.gpr .rsi) 16 := by
      rw [hrd', hwr', hsi]; exact inRegions_sub hrd (by omega) (by omega)
    have hw16 : InRegions s'.wr (s'.gpr .rdi) 16 := by
      rw [hwr', hdi]; exact inRegions_sub hwr (by omega) (by omega)
    refine WP.mono (copy16Body_ok s' hr16 hw16) fun s'' ⟨⟨hm, hdi', hsi', hcx, hz⟩, k'⟩ =>
      ⟨⟨by rw [hdi', hdi, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, off_add, Nat.mul_succ],
        by rw [hsi', hsi, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, off_add, Nat.mul_succ],
        k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_, (kk.trans k').mono (by decide)⟩, hcx, hz⟩
    · rw [hm, hdi]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [hm, hdi, hsi, writeW_readW128]
      by_cases e : 16 * k ≤ j
      · rw [ifp ((Offset.lt_iff _ _ (by omega)).mpr (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)),
          Offset.sub_toNat _ e (by omega), off_add, Nat.add_sub_cancel' e]
        exact hf.bytes (R := ⟨pa s src, 16 * n⟩) (by simpa using hdj) (show 16 * n ≤ 2 ^ 64 by omega)
          (show j < 16 * n by omega)
      · rw [ifn (fun h => e (by
          have := ((Offset.lt_iff _ _ (by omega)).mp h).1
          rwa [Mem.sub_ofNat_toNat _ (by omega)] at this)), hc j (by omega)]
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (List.mem_range.mp hi)

section
variable {rbs wbs : List (Reg × Nat)}

theorem copy16_okL {s : State} (L : Lay rbs wbs s) {dst src : Ptr} {n : Nat} (hsr : src.1 ≠ .rdi)
    (hc : copyChk (rbs ++ wbs) wbs dst src (16 * n) = true) :
    WP isa (copy16 dst src n) s fun s' => PPost s s' [(dst, 16 * n)] ∧
      bytesAt s'.mem (pa s dst) (16 * n) = bytesAt s.mem (pa s src) (16 * n) := by
  simp only [copyChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hod, hid⟩, hwd⟩, hos, his⟩, hs⟩, hn0⟩, hn⟩ := hc
  have hrd : InRegions (s.rd ++ s.wr) (pa s src) (16 * n) :=
    L.cR his _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have hwr : InRegions s.wr (pa s dst) (16 * n) := L.cW hwd _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  exact WP.mono (copy16_ok dst src n (by omega) hn hod hos hsr s hrd hwr (L.disj hs))
    fun s' ⟨hb, hf, k⟩ => ⟨post_of_keep k (by decide) hf, hb⟩

end

end VG.Proof.MlKem.X86_64
