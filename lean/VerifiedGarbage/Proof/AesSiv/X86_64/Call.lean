import VerifiedGarbage.Proof.AesSiv.X86_64.Contract
import VerifiedGarbage.Proof.AesSiv.X86_64.Bits
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified

/-!
# AES-SIV on x86-64: calling `vg_cmac_aes_finalize` with any subkeys

`vg_cmac_aes_finalize`'s contract gives the CMAC of the message only when the
subkeys in its `key` are those of the key schedule's cipher. Its code needs
no such thing: it computes `CIPH_K(C ⊕ Mₙ)` from whatever subkeys `key`
holds, for the chaining value `C` at `state` and the last block `Mₙ` of
§6.2 step 4 (`finalize_raw_wp`). AES-SIV's contracts compute with the
subkeys its key context holds (`Spec.Siv.ctxMac`), so its calls use this
(`finr_call`), with `WP.call` from this correctness of the same code.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (FPre finPre_wp ctr_call bytesAt_frame finalizeX86_64 finalize_mx mn)
open VG.Proof.CmacAes.Stream.X86_64 (FArgs finalize_nosp finalize_depth callEntry_bytes toNat_ofNat)

/-- What `vg_cmac_aes_finalize`'s code computes, from any subkeys. -/
def finalizeRawX86_64 : Contract isa where
  pre := finalizeX86_64.pre
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
      Spec.Cmac.aesWith (s.gpr .rsi).toNat (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1)))
        (Spec.Cmac.xor (mn s.mem (s.gpr .rdi) (s.gpr .rcx) (s.gpr .r8).toNat)
          (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16))
  pub := finalizeX86_64.pub

theorem finalize_raw_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeX86_64.pre s₀) :
    WP isa (Impl.CmacAes.X86_64.finalize v.callee) s₀
      fun s' => gprPreserved s₀ s' ∧ finalizeRawX86_64.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .rdi = W at hp
  generalize hSt : s₀.gpr .rdx = St at hp
  generalize hP : s₀.gpr .rcx = P at hp
  generalize s₀.gpr .r9 = S at hp
  generalize hL : (s₀.gpr .r8).toNat = L at hp
  generalize hR' : (s₀.gpr .rsi).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (ctr_call v h₁.pre) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  have big : Frame [⟨St, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 8] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨S, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨below (s₀.gpr .rsp) 8, by simp, by rw [rsp₁]; exact fun _ h => h⟩
  have sch : Spec.Aes.bytesAt s₁.mem W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) :=
    bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))) (by omega)
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show Spec.Aes.bytesAt s₂.mem (s₀.gpr .rdx) 16 = _
    rw [hW, hSt, hP, hL, hR', h₂.out, sch, h₁.blk]

theorem finalize_raw_correct (v : Ctr32Impl) (s : State) (hs : finalizeRawX86_64.pre s) :
    ∃ t s', Exec isa (Impl.CmacAes.X86_64.finalize v.callee) s t s' ∧ abiPreserved s s' ∧
      finalizeRawX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finalize_raw_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (finalize_mx v) he hg, hp⟩

/-- What a call of `vg_cmac_aes_finalize` leaves, from any subkeys. -/
structure FRPost (s : State) (K St P S : Addr) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem St 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
      (Spec.Cmac.xor (mn s.mem K P L) (Spec.Aes.bytesAt s.mem St 16))

theorem finr_call (v : Ctr32Impl) (nm : String) {s : State} {K St P S : Addr} {L R : Nat}
    (h : FArgs s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.finalize v.callee)) s (FRPost s K St P S L R) := by
  have hR := VG.Proof.CmacAes.X86_64.toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := finalizeRawX86_64) (finalize_raw_correct v) (finalize_nosp v)
    (by rw [finalize_depth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [finalize_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [finalizeRawX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hL] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have eK : Spec.Aes.bytesAt s.callEntry.mem K (16 * (R + 1)) = Spec.Aes.bytesAt s.mem K (16 * (R + 1)) :=
    callEntry_bytes s (h.stkK.sub_right (Region.sub_prefix (by omega))) (by omega)
  have eK1 : Spec.Aes.bytesAt s.callEntry.mem (K + BitVec.ofNat 64 240) 16 =
      Spec.Aes.bytesAt s.mem (K + BitVec.ofNat 64 240) 16 :=
    callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 240) (n := 16) (by decide))) (by decide)
  have eK2 : Spec.Aes.bytesAt s.callEntry.mem (K + BitVec.ofNat 64 256) 16 =
      Spec.Aes.bytesAt s.mem (K + BitVec.ofNat 64 256) 16 :=
    callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 256) (n := 16) (by decide))) (by decide)
  have eSt := callEntry_bytes s h.stkSt (by decide)
  have eP := callEntry_bytes s h.stkP (by have := h.len; omega)
  simp only [mn, eK, eK1, eK2, eSt, eP] at hpost
  rw [← hm₂]
  exact hpost

end VG.Proof.AesSiv.X86_64
