import VerifiedGarbage.Proof.Hmac.X86.Finalize
import VerifiedGarbage.Proof.Sha256.X86.Stream.FinalizeVariant
import VerifiedGarbage.Impl.Hmac.Sha256.X86

/-! The efficient SHA-256 HMAC finalizer, proved for any compressor. -/
namespace VG.Proof.Hmac.Sha256.X86.Finalize
open VG VG.X86 VG.Impl.Hmac.X86
open VG.Impl.Sha256.X86 (at_)
open VG.Impl.Sha256.X86.Stream (compressAt restore saved)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_append repr_congr compressList_append
  hash_one lenBytes rest)
open VG.Proof.Hmac.X86
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Spec.Sha256 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes Repr)
open VG.Proof.Sha256 (countX86)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open VG.Proof.Hmac (countFinalizeX86)

open VG.Proof.Hmac.X86.Finalize
variable {name : String} {code : Prog isa}
  (hv : Verified X86.target code Proof.Sha256.compressX86)
  (hnosp : NoSp code) (hstack : stackUse code = 0)

theorem finalizeHash_eq : Impl.Hmac.Sha256.X86.finalizeHash name code = .seq (.block (([.mov .eax (.mem (at_ .esp 20))] : List Instr) ++
      VG.Impl.Sha256.X86.Stream.save .eax ++
      ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp 128) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp 132) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp 136) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63),
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx 32) .cl, .alu .add .edi (.imm 1),
       .mov .esi (.imm 0), .alu .cmp .edi (.imm 57)] : List Instr)))
    (.seq (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))
      (.loop (VG.Impl.MdStream.X86.finalizeBody VG.Impl.Sha256.X86.Stream.params name code) .e)) := rfl

include hv hnosp hstack

theorem hash_ok {s : State} (hp : SPre s) : WP isa (Impl.Hmac.Sha256.X86.finalizeHash name code) s (SDone s) := by
  rw [finalizeHash_eq, ← VG.Proof.Sha256.X86.Stream.Finalize.seq_assoc]
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86.Stream.Finalize.prologue_ok hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.loop (M := isa) (fun i s' => ∃ n, VG.Proof.Sha256.X86.Stream.Finalize.LInv s i n s') ?_ k s₁ ⟨_, hL⟩
  rintro i s' ⟨n, hL⟩
  refine WP.mono (VG.Proof.Sha256.X86.Stream.Finalize.body_of hv hnosp hstack hp hL) fun s'' h => ?_
  rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
  · exact .inl ⟨he, hD⟩
  · exact .inr ⟨he, 0, by omega_nat, 0, hL'⟩

theorem comp_of {s₀ s : State} (hp : Pre s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .esp = esp₀ s₀) (hebx : s.gpr .ebx = inn s₀) (hebp : s.gpr .ebp = scr s₀)
    (heax : s.gpr .eax = inn s₀ + 32) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨inA s₀, 32⟩, ⟨scA s₀, 112⟩, stkR s₀] s.mem s'.mem →
      stateAt s'.mem (inA s₀) =
        compress (stateAt s.mem (inA s₀)) (blockAt s.mem (inA s₀ + BitVec.ofNat 64 32)) → Q s') :
    WP isa (Impl.MdStream.X86.compressAt name code .ebx .ebp) s Q := by
  have fi := hp.in_fit
  have fs := hp.scr_fit
  have fsp := hp.sp_fit
  have hb := blk_eq hp
  have s32 : Region.Sub ⟨inA s₀, 32⟩ (inR s₀) := Region.sub_prefix (by omega_nat)
  have s112 : Region.Sub ⟨scA s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega_nat)
  have b64 : Region.Sub ⟨(inn s₀ + 32).setWidth 64, 64⟩ (inR s₀) := by rw [hb]; exact sub_offset (by omega_nat) (by omega_nat)
  refine compressAt_of hv hnosp hstack (st := inn s₀) (scr := scr s₀) (blk := inn s₀ + 32) (E := esp₀ s₀)
    (by decide) (by decide) (by decide) (by decide) hsp hebx hebp heax hp.sp_lo
    (by omega_nat) (by rw [show (inn s₀ + 32).toNat = (inn s₀).toNat + 32 by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega_nat)]; omega_nat) (by omega_nat)
    ((hp.in_scr.sub_left s32).sub_right s112) ?_ ((hp.in_scr.sub_left b64).sub_right s112)
    (hp.stk_in.sub_right s32) (hp.stk_scr.sub_right s112) (hp.stk_in.sub_right b64) ?_ ?_ ?_
  · rw [hb]
    intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    have := sep_off (inA s₀) (d := 32) (e := 0) (n := 64) (k := 32) (by omega_nat) (by omega_nat) (by omega_nat) a
      (by omega_nat) (by simp at h₂ ⊢; omega_nat)
    exact this
  · apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨inR s₀, by simp [hrd, hwr, hp.wr], 32, hb, by simp⟩
  · apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨inR s₀, by simp [hwr, hp.wr], 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp [hwr, hp.wr], 0, by simp, by simp⟩
  · intro s' h₁ h₂ h₃ h₄ h₇
    rw [hb] at h₇
    exact hQ s' h₁ h₂ h₃ h₄ h₇

/-! ## Writing the MAC -/

variable (hfSp : NoSp (Impl.Hmac.Sha256.X86.finalizeHash name code))
  (hfStack : stackUse (Impl.Hmac.Sha256.X86.finalizeHash name code) = 20)
include hfSp hfStack

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa (Impl.Hmac.Sha256.X86.finalize name code) s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Hmac.finalizeSha256X86.post s₀ s' := by
  have fi := hp.in_fit
  have fs := hp.scr_fit
  have fsp := hp.sp_fit
  unfold Impl.Hmac.Sha256.X86.finalize
  refine WP.seq (WP.mono (pro_ok hp) fun s₁ h₁ => ?_)
  have sp₁ : s₁.gpr .esp = esp₀ s₀ := h₁.gpr _ (by decide) (by decide)
  have s160 : Region.Sub ⟨scA s₀, 160⟩ (scR s₀) := Region.sub_prefix (by omega_nat)
  have a20 : Region.Sub ⟨addr (esp₀ s₀) 4, 20⟩ (argR s₀) := Region.sub_prefix (by omega_nat)
  have finSub : ∀ r ∈ finW s₀ ++ [stkR s₀], ∃ r' ∈ allR s₀, Region.Sub r r' := by
    intro r hr
    simp only [finW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, fun _ h => h⟩
    · exact ⟨outR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, s160⟩
    · exact ⟨argR s₀, by simp, a20⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  refine WP.seq (WP.narrowSp (hash_ok hv hnosp hstack (narrow_pre hp h₁)) ?_ ?_ hfSp
    (by rw [hfStack, sp₁]; exact hp.sp_lo) fun sD rdD wrD frD hD => ?_)
  · rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.nil_append, finW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨argR s₀, by simp, 0, by simp, by simp⟩
  · rw [h₁.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [finW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨argR s₀, by simp, 0, by simp, by simp⟩
  rw [hfStack, sp₁] at frD
  obtain ⟨hC, hHash⟩ := hD
  have e3 : VG.Proof.Sha256.X86.Stream.Finalize.out (narrow s₀ s₁) = out s₀ := narrow_arg hp h₁ (by omega_nat)
  have e4 : VG.Proof.Sha256.X86.Stream.Finalize.scr (narrow s₀ s₁) = scr s₀ := narrow_arg hp h₁ (by omega_nat)
  have outpD : sD.mem.readW (addr (scr s₀) 136) 32 = out s₀ := by
    have := hC.outp; rw [e4, e3] at this; exact this
  have savedD : ∀ p ∈ saved, sD.mem.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1 := by
    intro p hp'
    have := hC.saved p hp'
    rw [e4] at this
    refine this.trans ?_
    show s₁.gpr p.1 = s₀.gpr p.1
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> exact h₁.gpr _ (by decide) (by decide)
  have ebxD : sD.gpr .ebx = inn s₀ := hC.ebx.trans (narrow_arg hp h₁ (i := 0) (by omega_nat))
  have ebpD : sD.gpr .ebp = scr s₀ := hC.ebp.trans (narrow_arg hp h₁ (i := 4) (by omega_nat))
  have spD : sD.gpr .esp = esp₀ s₀ := hC.esp.trans sp₁
  have rdD' : sD.rd = s₀.rd := rdD.trans h₁.rd
  have wrD' : sD.wr = s₀.wr := wrD.trans h₁.wr
  -- `scratch[176..180)`, where `outer` is, lies outside what `finalizeHash` writes.
  have w176 : ∀ r ∈ finW s₀ ++ [stkR s₀], Region.Disjoint ⟨addr (scr s₀) 176, 4⟩ r := by
    have hs : Region.Sub ⟨addr (scr s₀) 176, 4⟩ (scR s₀) := hp.scr_sub (by omega_nat)
    intro r hr
    simp only [finW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.in_scr.symm.sub_left hs)
    · exact (hp.out_scr.symm.sub_left hs)
    · rw [addr_eq (by omega_nat)]; exact Offset.disjoint_base _ (by omega_nat) (by omega_nat)
    · exact (hp.a_scr.symm.sub_left hs).sub_right a20
    · exact hp.stk_scr.symm.sub_left hs
  have ouD : sD.mem.readW (addr (scr s₀) 176) 32 = ou s₀ := by
    rw [frD.readW (Region.contains_self _ _) w176 (by decide), h₁.mem, proMem_176 hp]
  refine WP.seq (WP.mono (mid_ok hp ⟨rdD', wrD', ebxD, ebpD, spD, ouD⟩) fun s₃ h₃ => ?_)
  have sp₃ : s₃.gpr .esp = esp₀ s₀ := by rw [h₃.gpr _ (by decide) (by decide) (by decide), spD]
  refine WP.seq (comp_of hv hnosp hstack hp h₃.rd h₃.wr sp₃ (by rw [h₃.gpr _ (by decide) (by decide) (by decide), ebxD])
    (by rw [h₃.gpr _ (by decide) (by decide) (by decide), ebpD]) h₃.eax fun s₄ rd₄ wr₄ cs₄ fr₄ st₄ => ?_)
  -- Words of the scratch space that neither the middle block nor the compression writes.
  have keep : ∀ d, 112 ≤ d → d + 4 ≤ 160 →
      s₄.mem.readW (addr (scr s₀) d) 32 = sD.mem.readW (addr (scr s₀) d) 32 := by
    intro d h₁ h₂
    have hs : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := hp.scr_sub (by omega_nat)
    rw [fr₄.readW (Region.contains_self _ _) ?_ (by decide), h₃.mem,
      (midMem_frame sD.mem).readW (Region.contains_self _ _) ?_ (by decide)]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.in_scr.symm.sub_left hs
      · exact hp.a_scr.symm.sub_left hs
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.in_scr.symm.sub_left hs).sub_right (Region.sub_prefix (by omega_nat))
      · rw [addr_eq (by omega_nat)]; exact Offset.disjoint_base _ (by omega_nat) (by omega_nat)
      · exact hp.stk_scr.symm.sub_left hs
  have csD : ∀ r ∈ calleeSaved, s₄.gpr r = sD.gpr r := fun r hr => by
    rw [cs₄ r hr, h₃.gpr r ?_ ?_ ?_] <;>
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  refine WP.mono (out_ok hp (rd₄.trans h₃.rd) (wr₄.trans h₃.wr) (by rw [csD _ (by decide), ebxD])
    (by rw [csD _ (by decide), ebpD]) (by rw [csD _ (by decide), spD])
    (by rw [keep 136 (by omega_nat) (by omega_nat)]; exact outpD)
    fun p hp' => ?_) fun s' ⟨rd', wr', cs', m'⟩ => ?_
  · have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> simp
    rw [keep p.2 hd.1 (by omega_nat)]
    exact savedD p hp'
  -- Everything written is within our regions.
  have f1 : Frame (allR s₀) s₀.mem s₁.mem := by rw [h₁.mem]; exact (proMem_frame hp).mono (by simp)
  have f2 : Frame (allR s₀) s₁.mem sD.mem := frD.sub finSub
  have f3 : Frame (allR s₀) sD.mem s₃.mem := by rw [h₃.mem]; exact (midMem_frame sD.mem).mono (by simp)
  have f4 : Frame (allR s₀) s₃.mem s₄.mem := by
    refine fr₄.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, Region.sub_prefix (by omega_nat)⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_nat)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  have f5 : Frame (allR s₀) s₄.mem s'.mem := by
    rw [m']
    refine (writeBytes_frame (R := outR s₀) _ _ _ ?_).mono (by simp)
    rw [beWords_length]; exact contains_offset (by omega_nat) (by omega_nat)
  have F : Frame (allR s₀) s₀.mem s'.mem := f1.trans (f2.trans (f3.trans (f4.trans f5)))
  refine ⟨⟨cs', F.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)⟩, ?_⟩
  · intro r hr
    simp only [allR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [hp.ret_in, hp.ret_out, hp.ret_scr, ret_a hp, ret_stk hp]
  intro k0 text hk hin hcnt hout
  -- The inner digest.
  have e0 : VG.Proof.Sha256.X86.Stream.Finalize.st (narrow s₀ s₁) = inn s₀ := narrow_arg hp h₁ (by omega_nat)
  have oD : ∀ r ∈ allR s₀, (ouR s₀).Disjoint r := by
    intro r hr
    simp only [allR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [hp.o_in, hp.o_out, hp.o_scr, hp.o_a, hp.stk_ou.symm]
  have hR₀ : VG.Proof.Sha256.X86.Stream.Finalize.R₀ (narrow s₀ s₁) (xorPad k0 ipad ++ text) := by
    refine ⟨?_, ?_⟩
    · show Repr s₁.mem ((VG.Proof.Sha256.X86.Stream.Finalize.st (narrow s₀ s₁)).setWidth 64) _
      rw [e0]
      refine repr_congr (fun i hi => ?_) hin
      rw [h₁.mem]
      refine frame_bytes (proMem_frame hp) (R := inR s₀) (fun r hr => ?_) (by simp) hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.in_scr, hp.a_in.symm]
    · show countX86 (narrow s₀ s₁) = _
      simp only [countX86]
      rw [narrow_arg hp h₁ (i := 2) (by omega_nat), narrow_arg hp h₁ (i := 1) (by omega_nat)]
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.length_append, xorPad_length, hk]
      exact hcnt
  have hdig : Spec.Sha256.hash (xorPad k0 ipad ++ text) = beWords sD.mem (inn s₀) 0 8 := by
    have e0A : VG.Proof.Sha256.X86.Stream.Finalize.stA (narrow s₀ s₁) = inA s₀ := by
      show (VG.Proof.Sha256.X86.Stream.Finalize.st (narrow s₀ s₁)).setWidth 64 = _
      rw [e0]
    rw [hHash _ hR₀, beWords_stateAt _ (by omega_nat), e0A, State.withRegions_mem]
  -- The outer hash value.
  have hou : stateAt s₃.mem (inA s₀) = Spec.Sha256.compressList Spec.Sha256.H0 (xorPad k0 opad) 1 := by
    rw [h₃.mem, midMem_state,
      VG.Proof.Sha256.Stream.stateAt_congr (mem := s₀.mem) fun i hi =>
        frame_bytes (f1.trans f2) (R := ouR s₀) oD (by simp) (by simp; omega_nat),
      hout.1, xorPad_length, hk]
  -- The block after it.
  have hblk : blockAt s₃.mem (inA s₀ + BitVec.ofNat 64 32) =
      parseBlock fun t => (beWords sD.mem (inn s₀) 0 8 ++ padBytes).getD t 0 := by
    have hb := midMem_block (s₀ := s₀) sD.mem
    rw [← h₃.mem] at hb
    exact VG.Proof.Sha256.Stream.parseBlock_congr fun k hk => bytesAt_getD hb (by omega_nat)
  -- The MAC.
  have hmac : bytesAt s'.mem (outA s₀) 32 = beWords s₄.mem (inn s₀) 0 8 := by
    rw [m', show outA s₀ + BitVec.ofNat 64 0 = outA s₀ by simp]
    have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s₄.mem (outA s₀)
      (beWords s₄.mem (inn s₀) 0 8) (by rw [beWords_length]; omega_nat)
    rw [beWords_length] at this
    simpa only [Nat.reduceMul] using this
  show bytesAt s'.mem (outA s₀) 32 = _
  rw [hmac, beWords_stateAt _ (by omega_nat), st₄, hou, hblk]
  simp only [hmacBlockKey, sha256]
  rw [hdig, outer_hash hk (beWords_length _ _ _ _)]


local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Hmac.finalizeSha256X86, Proof.Hmac.countFinalizeX86,
    VG.Proof.Hmac.X86.Finalize.finalizeWide, VG.Proof.Hmac.X86.Finalize.narrowWr, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem, VG.X86.State.withRegions_rd,
    VG.X86.State.withRegions_wr] $(loc)?)

theorem verified
    (hct : ConstantTime isa Proof.Hmac.finalizeSha256X86.pre Proof.Hmac.finalizeSha256X86.pub
      (Impl.Hmac.Sha256.X86.finalize name code)) :
    Verified X86.target (Impl.Hmac.Sha256.X86.finalize name code) (Spec.Hmac.finalizeSha256OutContract X86.abi 20) :=
  have hsat := finalizeWide_implies.sat_left
  (Verified.widen (Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, h⟩ := correct hv hnosp hstack hfSp hfStack (pre_of hs)
      exact ⟨t, s', he, h⟩) hct
    (.refl (hsat.elim fun s hs => ⟨_, finalizeWide_pre s hs⟩)))
    narrowWr finalizeWide_pre
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl)
        (.cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl) .nil))))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies finalizeWide_implies

end VG.Proof.Hmac.Sha256.X86.Finalize
