import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Finalize

/-!
# TDEA-CMAC on x86-64: `vg_cmac_triple_des_finalize` is correct

After the branch on the length, `rax` holds `Mₙ` (`BPost`); the function XORs
in the chaining value `C`, encrypts it and stores `CIPH_K(C ⊕ Mₙ)` as the
state, the MAC (`macFull_split8`).
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes VG.Proof.Cmac

/-- What the first block leaves. -/
structure P1 (s₀ : State) (W St P S : Addr) (s : State) : Prop where
  r15 : s.gpr .r15 = S
  r14 : s.gpr .r14 = W
  rbp : s.gpr .rbp = St
  rdi : s.gpr .rdi = W
  rdx : s.gpr .rdx = P
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  mem : s.mem = savedMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {s₀ : State} {W St P S : Addr} {L : Nat} (hp : FPre s₀ W St P S L)
include hp

theorem FPre.save_frame : ∀ r ∈ [(⟨S + BitVec.ofNat 64 48, 48⟩ : Region)], (⟨P, L⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact hp.last_scr.sub_right (FPre.scrD (by decide))

theorem FPre.keyD {d n : Nat} (h : d + n ≤ 400) {r : Region} (hr : Region.Sub r ⟨S, 640⟩) :
    (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r :=
  (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right hr

theorem full_wp (hL : L = 8) {s : State} (h : P1 s₀ W St P S s) :
    WP isa (.block full) s (BPost s₀ W St P S L) := by
  subst hL
  have kw := hp.key_wrap
  obtain ⟨s', run, ax, g, m, rd, wr⟩ := xor1_ok s .rdx .rdi 0 384 (P := P) (Q := W + BitVec.ofNat 64 384)
    (by rw [h.rdx]; simp) (by rw [h.rdi]) (by decide)
    (by rw [h.rd, h.wr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [h.rd, h.wr]; exact hp.inKey (d := 384) (n := 8) (by decide))
  refine WP.of_runBlock ⟨s', run, by rw [g _ (by decide), h.r14], by rw [g _ (by decide), h.r15],
    by rw [g _ (by decide), h.rbp], by rw [g _ (by decide), h.rsp], by rw [rd, h.rd], by rw [wr, h.wr],
    by rw [m, h.mem]; exact Frame.refl _ _, ?_⟩
  have fs := savedMem_frame s₀ S
  rw [ax, h.mem, le8_xor, le8_readW, le8_readW,
    bytesAt_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.last_scr.sub_right (FPre.scrD (by decide))) (by decide),
    bytesAt_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.keyD (d := 384) (n := 8) (by decide) (FPre.scrD (by decide))) (by decide)]
  simp only [mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
  exact xor_comm _ _

open VG.WriteBytes in
theorem partial_wp (hL : L < 8) {s : State} (h : P1 s₀ W St P S s) :
    WP isa partialBlock s (BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have hcx : s.gpr .rcx = BitVec.ofNat 64 L := by
    rw [h.rcx, ← hp.rcx]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 96 = C := ⟨_, rfl⟩
  have hc : s.gpr .r15 + BitVec.ofNat 64 96 = C := by rw [h.r15, hC]
  have dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 8⟩ := by rw [← hC]; exact hp.last_scr.sub_right (FPre.scrD (by decide))
  have sl : slot12 S = ⟨C, 8⟩ := by rw [← hC]
  -- Zero the slot.
  obtain ⟨s₁, run₁, zf₁, mem₁, g₁, rd₁, wr₁⟩ := zero_ok s hc hcx (by omega)
    (by rw [h.wr, ← hC]; exact hp.inScr (d := 96) (n := 8) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  let m₁ := (savedMem s₀ S).writeW C (BitVec.setWidth 64 (0 : BitVec 32))
  have zf : s₁.mem = m₁ := by rw [mem₁, h.mem]
  have fz : Frame [⟨C, 8⟩] (savedMem s₀ S) m₁ :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have lastS : Spec.Aes.bytesAt (savedMem s₀ S) P L = Spec.Aes.bytesAt s₀.mem P L :=
    bytesAt_frame (savedMem_frame s₀ S) (hp.save_frame) (by omega)
  have lastZ : Spec.Aes.bytesAt m₁ P L = Spec.Aes.bytesAt s₀.mem P L := by
    rw [bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega),
      lastS]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.mem = writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s₂.gpr r = s.gpr r) ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by show s₁.zf = _; rw [zf₁]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [Spec.Aes.bytesAt, writeBytes_nil], fun r h₁ _ => g₁ r h₁,
        by rw [rd₁, h.rd], by rw [wr₁, h.wr]⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_ok s₁ (by omega) hL (by rw [g₁ _ (by decide), h.rdx])
        (by rw [g₁ _ (by decide)]; exact hc) (by rw [g₁ _ (by decide)]; exact hcx)
        (fun i hi => by rw [rd₁, wr₁, h.rd, h.wr]; exact hp.inLast (d := i) (n := 1) (by omega))
        (fun i hi => by
          rw [wr₁, h.wr, ← hC, Offset.add_add]; exact hp.inScr (d := 96 + i) (n := 1) (by omega)) dPC) ?_
      rintro s₂ ⟨m₂, g₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], fun r h₁ h₂ => by rw [g₂ r h₁ h₂, g₁ r h₁], by rw [rd₂, rd₁, h.rd],
        by rw [wr₂, wr₁, h.wr]⟩
  · obtain ⟨m₂, g₂, rd₂, wr₂⟩ := h₂
    have r15₂ : s₂.gpr .r15 = S := by rw [g₂ _ (by decide) (by decide), h.r15]
    have rcx₂ : s₂.gpr .rcx = BitVec.ofNat 64 L := by rw [g₂ _ (by decide) (by decide), hcx]
    have rdi₂ : s₂.gpr .rdi = W := by rw [g₂ _ (by decide) (by decide), h.rdi]
    obtain ⟨s₃, run₃, m₃, ax₃, g₃, rd₃, wr₃⟩ := pad_ok s₂ (C := C) (K := W + BitVec.ofNat 64 392) (L := L)
      (by rw [r15₂, rcx₂, BitVec.mul_one, show BitVec.ofInt 64 96 = BitVec.ofNat 64 96 from rfl, ← hC,
        BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 L), ← BitVec.add_assoc])
      (by rw [r15₂, hC]) (by rw [rdi₂])
      (by rw [wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 96 + L) (n := 1) (by omega))
      (by rw [rd₂, wr₂, ← hC]; exact wr_in (hp.inScr (d := 96) (n := 8) (by decide)))
      (by rw [rd₂, wr₂]; exact hp.inKey (d := 392) (n := 8) (by decide))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have gg (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .r10) : s₃.gpr r = s.gpr r := by rw [g₃ r h₁, g₂ r h₁ h₂]
    have hlen : (Spec.Aes.bytesAt s₀.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have fB : Frame [⟨C, 8⟩] m₁ (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 8) (by omega) (by decide))
    have fW : Frame [⟨C, 8⟩] (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L)) s₃.mem := by
      rw [m₃, m₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    have f₃ : Frame [⟨C, 8⟩] (savedMem s₀ S) s₃.mem := (fz.trans fB).trans fW
    have kD : (⟨W + BitVec.ofNat 64 392, 8⟩ : Region).Disjoint ⟨C, 8⟩ := by
      rw [← hC]; exact hp.keyD (by decide) (FPre.scrD (by decide))
    have k2 : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 392) 8 =
        Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 392) 8 := by
      rw [bytesAt_frame f₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kD) (by decide),
        bytesAt_frame (savedMem_frame s₀ S) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.keyD (d := 392) (n := 8) (by decide) (FPre.scrD (by decide))) (by decide)]
    have pad : Spec.Aes.bytesAt s₃.mem C 8 =
        Spec.Aes.bytesAt s₀.mem P L ++ [0x80] ++ Spec.Cmac.zeros (8 - L - 1) := by
      have hz : Spec.Aes.bytesAt m₁ C 8 = Spec.Cmac.zeros 8 := by
        rw [← le8_readW, Mem.readW_writeW_self64]; decide
      have := padded_bytes8 m₁ C (Spec.Aes.bytesAt s₀.mem P L) (by rw [hlen]; exact hL) hz
      rw [hlen] at this
      rw [m₃, m₂]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide), h.r14], by rw [gg _ (by decide) (by decide), h.r15],
      by rw [gg _ (by decide) (by decide), h.rbp], by rw [gg _ (by decide) (by decide), h.rsp],
      by rw [rd₃, rd₂], by rw [wr₃, wr₂], by rw [sl]; exact f₃, ?_⟩
    rw [ax₃, ← m₃, le8_xor, le8_readW, le8_readW, pad, k2]
    simp only [mn, Spec.Cmac.lastBlock, hlen, show L ≠ 8 by omega, ite_false]
    exact xor_comm _ _

end

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L : Nat} (hp : FPre s₀ W St P S L) :
    WP isa finPre s₀ (BPost s₀ W St P S L) := by
  have hcx : s₀.gpr .rcx = BitVec.ofNat 64 L := by rw [← hp.rcx]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨s₁, run₁, r15₁, r14₁, rbp₁, g₁, zf₁, m₁, rd₁, wr₁⟩ :=
    pre1_ok s₀ (fun d _ h => by rw [hp.r8]; exact hp.inScr (by omega)) hcx hp.len
  have h1 : P1 s₀ W St P S s₁ := ⟨by rw [r15₁, hp.r8], by rw [r14₁, hp.rdi], by rw [rbp₁, hp.rsi],
    by rw [g₁ _ (by decide), hp.rdi], by rw [g₁ _ (by decide), hp.rdx], g₁ _ (by decide),
    g₁ _ (by decide), by rw [m₁, hp.r8], rd₁, wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases hL : L = 8
  · exact WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [hL]) (fun _ => full_wp hp hL h1) (fun h => by cases h)
  · exact WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega) h1)

theorem xorSt_ok (s : State) {St : Addr} (hb : s.gpr .rbp = St) (r : InRegions (s.rd ++ s.wr) St 8) :
    ∃ s', runBlock isa [.alu .xor .rax (.mem (at_ .rbp 0)), .bswap .rax] s = some s' ∧
      s'.gpr .rax = byteRev64 (s.gpr .rax ^^^ s.mem.readW St 64) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.load64, State.ea, offset_nat, Option.bind_some, hb, BitVec.add_zero, r,
      ite_true]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, bswap64_eq]
  · simp [gpr_setReg, hr]

theorem storeSt_ok (s : State) {St : Addr} (hb : s.gpr .rbp = St) (w : InRegions s.wr St 8) :
    ∃ s', runBlock isa [.bswap .rax, .store (at_ .rbp 0) .rax] s = some s' ∧
      s'.mem = s.mem.writeW St (byteRev64 (s.gpr .rax)) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      State.store64, State.ea, offset_nat, gpr_setReg, rd_setReg, wr_setReg, ite_true, ite_false, hb,
      BitVec.add_zero, w]
    rfl, ?_⟩
  refine ⟨by simp [mem_setReg, bswap64_eq], fun r hr => ?_, rfl, rfl⟩
  simp [gpr_setReg, hr]

theorem finalize_wp {s₀ : State} (h0 : finalizeX86_64.pre s₀) :
    WP isa finalize s₀ fun s' => gprPreserved s₀ s' ∧ finalizeX86_64.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .rdi = W at hp
  generalize hSt : s₀.gpr .rsi = St at hp
  generalize hP : s₀.gpr .rdx = P at hp
  generalize hS : s₀.gpr .r8 = S at hp
  generalize hL : (s₀.gpr .rcx).toNat = L at hp
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have tw := hp.st_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  have rdwr₁ : s₁.rd ++ s₁.wr = [⟨W, 400⟩, ⟨P, L⟩, ⟨St, 8⟩, ⟨S, 640⟩] := by rw [h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₂, run₂, ax₂, g₂, m₂, rd₂, wr₂⟩ := xorSt_ok s₁ h₁.rbp
    (by rw [rdwr₁]; exact in_rw (r := ⟨St, 8⟩) (by simp) (Region.contains_self _ _))
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have bp : BlockPre s₂ :=
    { sched := ⟨⟨W, 400⟩, by rw [rd₂, h₁.rd, hp.rd]; simp, by rw [g₂ _ (by decide), h₁.r14],
        by show 384 ≤ 400; decide, by show 400 < 2 ^ 64; decide⟩
      scr := ⟨⟨S, 640⟩, by rw [wr₂, h₁.wr, hp.wr]; simp, by rw [g₂ _ (by decide), h₁.r15],
        by show 48 ≤ 640; decide, by show 640 < 2 ^ 64; decide⟩
      disj := by
        rw [g₂ _ (by decide), g₂ _ (by decide), h₁.r14, h₁.r15]
        exact (hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right
          (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₃ ⟨same₃, r14₃, ax₃⟩ => ?_)
  rw [WP.block_append_iff]
  have rbp₃ : s₃.gpr .rbp = St := by rw [same₃.rbp, g₂ _ (by decide), h₁.rbp]
  have r15₃ : s₃.gpr .r15 = S := by rw [same₃.r15, g₂ _ (by decide), h₁.r15]
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ := storeSt_ok s₃ rbp₃
    (by rw [same₃.wr, wr₂, h₁.wr, hp.wr]; exact in_rw (r := ⟨St, 8⟩) (by simp) (Region.contains_self _ _))
  have rdwr₄ : s₄.rd ++ s₄.wr = [⟨W, 400⟩, ⟨P, L⟩, ⟨St, 8⟩, ⟨S, 640⟩] := by
    rw [rd₄, wr₄, same₃.rd, same₃.wr, rd₂, wr₂, rdwr₁]
  obtain ⟨s₅, run₅, b, c, d, e, f, g, rsp₅, m₅⟩ := restore_ok s₄ (by rw [g₄ _ (by decide), r15₃]) fun d _ h₂' => by
    rw [rdwr₄]; exact in_rw (r := ⟨S, 640⟩) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩
  -- Memory.
  have xR₂ : xR s₂ = ⟨S, 48⟩ := by rw [xR, g₂ _ (by decide), h₁.r15]
  have f₃ : Frame [⟨S, 48⟩] s₁.mem s₃.mem := by rw [← m₂, ← xR₂]; exact same₃.frame
  have f₄ : Frame [⟨St, 8⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fAll : Frame [slot12 S, ⟨S, 48⟩, ⟨St, 8⟩] (savedMem s₀ S) s₅.mem := by
    rw [m₅]
    exact ((h₁.frame.mono fun r hr => by simp at hr; simp [hr]).trans (f₃.mono fun r hr => by
      simp at hr; simp [hr])).trans (f₄.mono fun r hr => by simp at hr; simp [hr])
  have big : Frame [⟨S, 640⟩, ⟨St, 8⟩] s₀.mem s₅.mem :=
    ((savedMem_frame s₀ S).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨S, 640⟩, by simp, FPre.scrD (by decide)⟩).trans (fAll.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨S, 640⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨S, 640⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨St, 8⟩, by simp, fun _ h => h⟩)
  have hm : ∀ d, 48 ≤ d → d + 8 ≤ 96 →
      s₄.mem.readW (S + BitVec.ofNat 64 d) 64 = (savedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
    intro d h₁' h₂'
    rw [← m₅]
    refine fAll.readW (r := ⟨S + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (d := d) (e := 96) (by omega) (by omega) (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact (hp.st_scr.sub_right (FPre.scrD (by omega))).symm
  refine ⟨⟨restored (S := S) hm ⟨b, c, d, e, f, g⟩ (by rw [rsp₅, g₄ _ (by decide), same₃.rsp,
    g₂ _ (by decide), h₁.rsp]), ?_⟩, ?_⟩
  · refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_scr
    · exact hp.ret_st
  · intro hk msg hml hne hst
    rw [hW, hSt, hP, hL] at *
    have keyD (r : Region) (hr : Region.Sub r ⟨S, 640⟩) : (⟨W, 384⟩ : Region).Disjoint r :=
      (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right hr
    have f₁ : Frame [⟨S + BitVec.ofNat 64 48, 48⟩, slot12 S] s₀.mem s₁.mem :=
      ((savedMem_frame s₀ S).mono fun r hr => by simp at hr; simp [hr]).trans
        (h₁.frame.mono fun r hr => by simp at hr; simp [hr])
    have hS' : sch s₂ = Spec.TripleDes.scheduleAt s₀.mem W := by
      rw [sch, g₂ _ (by decide), h₁.r14, m₂]
      exact scheduleAt_frame f₁ fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact keyD _ (FPre.scrD (by decide))
        · exact keyD _ (FPre.scrD (by decide))
    have hst₁ : le8 (s₁.mem.readW St 64) = Spec.Aes.bytesAt s₀.mem St 8 := by
      rw [le8_readW]
      exact bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_scr.sub_right (FPre.scrD (by decide))
        · exact hp.st_scr.sub_right (FPre.scrD (by decide))) (by decide)
    have hks := subkeys_tdes (Spec.TripleDes.scheduleAt s₀.mem W)
    have hk' : Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 384) 8 ++
        Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 392) 8 =
        (Spec.Cmac.subkeys (ciphAt s₀.mem W) 8).1 ++ (Spec.Cmac.subkeys (ciphAt s₀.mem W) 8).2 := by
      rw [show W + BitVec.ofNat 64 392 = W + BitVec.ofNat 64 384 + BitVec.ofNat 64 8 from
        (Offset.add_add W 384 8).symm, ← bytesAt_split]; exact hk
    obtain ⟨k1, k2⟩ := List.append_inj hk' (by rw [Proof.Cmac.bytesAt_length, ciphAt, hks, length_le8])
    show Spec.Aes.bytesAt s₅.mem St 8 = _
    rw [m₅, m₄, ← le8_readW, Mem.readW_writeW_self64, ax₃, ax₂, hS', ← tdesWith_le8, le8_xor, h₁.blk, hst₁,
      macFull_split8 _ hml (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), ← hst, ← k1, ← k2, xor_comm]

end VG.Proof.CmacTripleDes.X86_64
