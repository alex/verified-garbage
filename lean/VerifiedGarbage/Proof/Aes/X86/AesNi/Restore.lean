import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (CPre ctrP datP nBlk scrP ctrR datR scrR retR)
open VG.Impl.Aes.X86.AesNi (at_)

/-- Restoring the saved GPRs does not write memory; only the final numeric
counter word is written, in big-endian byte order. -/
theorem restoreCore_ok {s₀ s : State} (hp : CPre s₀) (saved : Saved s₀ s.mem)
    (edx : s.gpr .edx = ctrP s₀) (ebp : s.gpr .ebp = scrP s₀)
    (esp : s.gpr .esp = s₀.gpr .esp) (_rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    WP isa (.block Impl.Aes.X86.AesNi.restore) s fun s' =>
      s'.mem = s.mem.writeW (addr (ctrP s₀) 12) (bswap (s.gpr .ebx)) ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  have hc : InRegions s.wr (addr (ctrP s₀) 12) 4 := by
    refine ⟨ctrR s₀, ?_, ctr_contains hp (by decide)⟩
    simp only [wr, hp.wr, List.mem_cons, true_or]
  rw [show Impl.Aes.X86.AesNi.restore = .mov .eax (.reg .ebx) :: .bswap .eax :: .store (at_ .edx 12) .eax ::
    (Spill.restoreCode .ebp ([(.ebx, 0), (.esi, 4), (.edi, 8)] ++ [(.ebp, 12)]) ++ []) from rfl]
  refine Wp.wp_mov fun s₁ u₁ => Wp.wp_bswap fun s₂ u₂ => ?_
  refine Wp.wp_stm (by rw [u₂.other _ (by decide), u₁.other _ (by decide), edx])
    (by rw [u₂.wr, u₁.wr]; exact hc) fun s₃ u₃ => ?_
  have hm : s₃.mem = s.mem.writeW (addr (ctrP s₀) 12) (bswap (s.gpr .ebx)) := by
    rw [u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem]
  have e : s₃.gpr .ebp = scrP s₀ := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), ebp]
  have sv : Saved s₀ s₃.mem := by
    rw [hm]
    exact saved.of_readW fun p h => Mem.readW_writeW_sep (hp.dCB.symm.sep
      (scratch_contains hp (by have := savedRegs_bound p h; omega)) (ctr_contains hp (by decide))) (by decide)
  refine Spill.restoreBase_ok _ (by decide) (fun p h => by
      have := savedRegs_bound p (by revert p h; decide)
      rw [e, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
      exact inRegions_wr (by rw [wr]; exact scratch_in hp (by omega)))
    (by rw [e]; exact sv.sub (by decide)) fun s' r' => WP.block_nil ⟨by rw [r'.mem, hm],
        r'.abi (by decide) (by decide) (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), esp])⟩

/-- The complete restore preserves the encrypted data and the return slot,
and advances only the low 32 counter bits. -/
theorem restore_ok {s₀ s : State} (hp : CPre s₀) (i : Nat)
    (saved : Saved s₀ s.mem) (edx : s.gpr .edx = ctrP s₀) (ebp : s.gpr .ebp = scrP s₀)
    (esp : s.gpr .esp = s₀.gpr .esp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr)
    (frame : Frame [datR s₀, scrR s₀] s₀.mem s.mem)
    (low : s.gpr .ebx = (Spec.Gcm.blockAt s₀.mem ((ctrP s₀).setWidth 64)).extractLsb' 0 32 +
      BitVec.ofNat 32 i) :
    WP isa (.block Impl.Aes.X86.AesNi.restore) s fun s' =>
      abiPreserved s₀ s' ∧
      Spec.Gcm.blockAt s'.mem ((ctrP s₀).setWidth 64) =
        Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.blockAt s₀.mem ((ctrP s₀).setWidth 64)) ∧
      Spec.Gcm.blocksAt s'.mem ((datP s₀).setWidth 64) (nBlk s₀) =
        Spec.Gcm.blocksAt s.mem ((datP s₀).setWidth 64) (nBlk s₀) ∧
      Frame [ctrR s₀, datR s₀, scrR s₀] s₀.mem s'.mem ∧
      Frame [ctrR s₀] s.mem s'.mem := by
  refine WP.mono (restoreCore_ok hp saved edx ebp esp rd wr) fun s' ⟨mem, regs⟩ => ?_
  have f : Frame [ctrR s₀, datR s₀, scrR s₀] s₀.mem s'.mem := by
    rw [mem]
    exact (frame.mono (fun r hr => List.mem_cons_of_mem _ hr)).writeW
      List.mem_cons_self _ (ctr_contains hp (by decide))
  have fstore : Frame [ctrR s₀] s.mem s'.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ctr_contains hp (by decide))
  refine ⟨⟨regs, ?_⟩, ?_, ?_, f, fstore⟩
  · exact f.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.rC
      · exact hp.rD
      · exact hp.rB) (by decide)
  · apply VG.Proof.Aes.X86.ctr_after hp.fC (N := BitVec.ofNat 32 i) rfl
    · intro k hk
      rw [mem]
      change (s.mem.write (addr (ctrP s₀) 12) 4 (bswap (s.gpr .ebx))) (addr (ctrP s₀) k) = _
      rw [Mem.write_apply]
      · rw [addr_eq (by have hc := hp.fC; omega)]
        exact frame.bytes (R := ctrR s₀) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hp.dCD
          · exact hp.dCB) (by change 16 ≤ 2 ^ 64; decide) (by change k < 16; omega)
      · rw [addr_eq (by have hc := hp.fC; omega), addr_eq (by have hc := hp.fC; omega)]
        exact (Offset.sep_base ((ctrP s₀).setWidth 64) (n := 12) (e := 12) (k := 4)
          (by decide) (by decide)) _ (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hk)
    · rw [mem, Mem.readW_writeW_self32, low, ← VG.Proof.Aes.X86.icb_lo _ hp.fC]
  · unfold Spec.Gcm.blocksAt
    refine List.map_congr_left fun j hj => Proof.Gcm.blockAt_congr fun k hk => ?_
    have bound := List.mem_range.mp hj
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact fstore.bytes (R := datR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r; exact hp.dCD.symm) (by change 16 * nBlk s₀ ≤ 2 ^ 64; have hf := hp.fD; omega)
      (by change 16 * j + k < 16 * nBlk s₀; omega)

end VG.Proof.Aes.X86.AesNi
