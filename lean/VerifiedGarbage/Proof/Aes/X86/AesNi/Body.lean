import VerifiedGarbage.Proof.Aes.X86.AesNi.Invariant

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk scrP datR scrR argR)
open VG.Impl.Aes.X86.AesNi (at_ argOp ctrLoad aes xorData regs6)
open VG.Spec.Gcm (blockAt inc32)
open VG.Proof.Gcm.X86 (revMask)

/-- Public shape facts for the bulk and tail, evaluated once. -/
theorem regs_shape (rs : List XReg) (h : rs = regs6 ∨ rs = [.xmm0]) :
    rs.Nodup ∧ .xmm6 ∉ rs ∧ .xmm7 ∉ rs ∧ 0 < rs.length := by
  rcases h with rfl | rfl <;> decide

theorem Saved.of_data_frame {s₀ : State} (hp : CPre s₀) {m m' : Mem}
    (hs : Saved s₀ m) (hf : Frame [datR s₀] m m') : Saved s₀ m' :=
  hs.of_frame hf (fun p h => scratch_contains hp (by have := savedRegs_bound p h; omega))
    (by simp only [List.mem_singleton, forall_eq]; exact hp.dDB.symm)

structure Ready (s₀ s : State) (c : Nat) (rs : List XReg) (s' : State) : Prop where
  ks : ∀ k (h : k < rs.length), XBinOp.eval .pshufb (s'.xmm rs[k]) revMask =
    ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀))
  ebx : s'.gpr .ebx = s.gpr .ebx + BitVec.ofNat 32 rs.length
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem encrypt_ok {s₀ : State} (hp : CPre s₀) (rs : List XReg)
    (hrs : rs = regs6 ∨ rs = [.xmm0]) {c : Nat} (_hc : c + rs.length ≤ nBlk s₀)
    {s : State} (hI : Inv s₀ c c s) :
    WP isa (.seq (.block (ctrLoad rs)) (aes rs)) s (Ready s₀ s c rs) := by

  obtain ⟨hnd, h6, h7, hlen⟩ := regs_shape rs hrs
  have hw := hp.fD
  have ep : s.ea (at_ .ebp 16) = addr (scrP s₀) 16 := by
    rw [ea_mk]; simp only [at_, hI.ebp]
  have ea : s.ea (argOp 0) = argAddr s₀ 0 := by
    simp only [State.ea, argOp, at_, argAddr, hI.esp]
  have ha : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 := by
    rw [ea, hI.rd, hI.wr]
    exact ⟨argR s₀, by simp [hp.rd], arg_contains hp (by decide)⟩
  have harg : s.mem.readW (s.ea (argOp 0)) 32 = schP s₀ := by
    rw [ea]
    exact hI.frame.readW (arg_contains hp (by decide)) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.aD
      · exact hp.aB) (by decide)
  have hpfx : InRegions (s.rd ++ s.wr) (s.ea (at_ .ebp 16)) 16 := by
    rw [ep, hI.rd, hI.wr]
    exact inRegions_wr (scratch_in hp (by decide))
  refine WP.seq (WP.mono (ctrLoad_ok rs s hnd h7 hpfx ha)
    fun s₁ ⟨e₁, c₁, a₁, f₁⟩ => ?_)
  have ek : ∀ k (h : k < rs.length), st (s₁.xmm rs[k]) =
      VG.Proof.Aes.ctrState (cb s₀) (c + k) := by
    intro k hk
    rw [e₁ k hk, hI.ebx, ep, hI.scratchPrefix, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact counterLane_state _ _ _ (fun k hk => memory_prefix _ _ hk)
  have hK : Keys (nRounds s₀) (sch s₀) s₁ := CPre.keys hp (by rw [a₁, harg])
    (f₁.rd.trans hI.rd) (f₁.wr.trans hI.wr) (by rw [f₁.mem]; exact hI.frame)
  have ecx₁ : s₁.gpr .ecx = BitVec.ofNat 32 (nRounds s₀) := by
    rw [f₁.gpr .ecx (by decide) (by decide), hI.ecx]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (aes_ok rs hnd h6 hp.rounds s₁ hK ecx₁)
    fun s₂ ⟨e₂, f₂⟩ => ?_
  have ks : ∀ k (h : k < rs.length), XBinOp.eval .pshufb (s₂.xmm rs[k]) revMask =
      ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀)) := by
    intro k hk
    exact (aesWith_eq _ _ _ _ (by
      rw [e₂ _ (List.getElem_mem hk), ek k hk, ctrState_rev])).symm
  exact ⟨ks, by rw [f₂.gpr, c₁],
    fun r h1 h2 => by rw [f₂.gpr, f₁.gpr r h1 h2],
    f₂.mem.trans f₁.mem, f₂.rd.trans f₁.rd, f₂.wr.trans f₁.wr⟩

/-- Any supported lane group produces the next keystream blocks and XORs
exactly those blocks into data; a public register-update tail follows. -/
theorem blocks_ok {s₀ : State} (hp : CPre s₀) (rs : List XReg)
    (hrs : rs = regs6 ∨ rs = [.xmm0]) (tail : List Instr) {Q : State → Prop}
    {c : Nat} (hc : c + rs.length ≤ nBlk s₀) {s : State} (hI : Inv s₀ c c s)
    (hQ : ∀ s', Inv s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ctrLoad rs)) (.seq (aes rs) (.block (xorData rs 0 ++ tail)))) s Q := by
  obtain ⟨hnd, _, h7, hlen⟩ := regs_shape rs hrs
  have hw := hp.fD
  refine WP.seq (WP.mono (WP.seq_iff.mp (encrypt_ok hp rs hrs hc hI)) fun s₁ h => ?_)
  refine WP.seq (WP.mono h fun s₂ hR => ?_)
  have esi₂ : s₂.gpr .esi = datP s₀ + BitVec.ofNat 32 (16 * c) := by
    rw [hR.gpr .esi (by decide) (by decide), hI.esi]
  have esiNat : (s₂.gpr .esi).toNat = (datP s₀).toNat + 16 * c := by
    rw [esi₂, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have esiWide : (s₂.gpr .esi).setWidth 64 = bAddr s₀ c := by
    rw [esi₂]
    change addr (datP s₀) (16 * c) = _
    rw [addr_eq (by omega)]
  have addr' : ∀ k, (s₂.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * (0 + k)) =
      bAddr s₀ (c + k) := by
    intro k
    rw [esiWide, bAddr, bAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega]
  rw [WP.block_append_iff]
  refine WP.mono (xorData_ok rs 0 s₂ hnd h7 (fun k hk => by
    rw [addr' k, hR.wr, hI.wr]
    exact CPre.block_out hp (by omega)) (by rw [esiNat]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := hR.mem
  rw [hm₂] at b₃ fr₃
  rw [esiWide, Nat.mul_zero, BitVec.add_zero] at fr₃
  simp only [addr'] at b₃
  have frData : Frame [datR s₀] s.mem s₃.mem := fr₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨datR s₀, List.mem_singleton_self _, run_in hc⟩
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rd₃.trans (hR.rd.trans hI.rd),
    wr₃.trans (hR.wr.trans hI.wr), ?_,
    Saved.of_data_frame hp hI.saved frData, ?_, ?_⟩
  · rw [g₃, hR.ebx, hI.ebx, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [g₃, hR.gpr .esp (by decide) (by decide), hI.esp]
  · rw [g₃, hR.gpr .ecx (by decide) (by decide), hI.ecx]
  · rw [g₃, hR.gpr .edx (by decide) (by decide), hI.edx]
  · rw [g₃, hR.gpr .ebp (by decide) (by decide), hI.ebp]
  · rw [g₃, esi₂]
  · rw [g₃, hR.gpr .edi (by decide) (by decide), hI.edi]
  · exact hI.frame.trans (frData.mono fun r hr =>
      List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)))
  · rw [frData.readW (scratch_contains hp (by decide)) (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact hp.dDB.symm) (by decide), hI.scratchPrefix]
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + rs.length) →
        blockAt s₃.mem (bAddr s₀ k) = blockAt s.mem (bAddr s₀ k) := fun hn =>
      blockAt_frame fr₃ fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        exact run_sep hp hk hc hn
    by_cases hlo : k < c
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, show k < c + rs.length by omega, ite_true]
    · by_cases hhi : k < c + rs.length
      · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega⟩
        have hj : j < rs.length := by omega
        rw [b₃ j hj, hI.blocks _ hk, hR.ks j hj]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [out (by omega), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

end VG.Proof.Aes.X86.AesNi
