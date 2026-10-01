import VerifiedGarbage.Proof.Hmac.X86.Init
import VerifiedGarbage.Proof.Sha256.X86.Stream.CompressAt
import VerifiedGarbage.Impl.Hmac.Sha256.X86

/-! The efficient SHA-256 HMAC initializer, proved for any compressor. -/
namespace VG.Proof.Hmac.Sha256.X86.Init
open VG VG.X86 VG.Impl.Hmac.X86
open VG.Impl.Sha256.X86 (at_)
open VG.Impl.Sha256.X86.Stream (compressAt save restore saved)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_append repr_congr)
open VG.Proof.Hmac.X86
open VG.Proof.Hmac.Common (bytesAt_length writeState stateAt_writeState)
open VG.Spec.Sha256 (HashValue stateAt blockAt compress bytesAt Repr H0)
open VG.Spec.Hmac (xorPad ipad opad blockKey sha256)

open VG.Proof.Hmac.X86.Init
variable {name : String} {code : Prog isa}
  (hv : Verified X86.target code Proof.Sha256.compressX86)
  (hnosp : NoSp code) (hstack : stackUse code = 0)
include hv hnosp hstack

theorem compBuf_of {s₀ s : State} (hp : Pre s₀) {b : Reg} {x : BitVec 32} (hx : x = inn s₀ ∨ x = ou s₀)
    (hb : b = .ebx ∨ b = .esi) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hbx : s.gpr b = x)
    (hebp : s.gpr .ebp = scr s₀) (hsp : s.gpr .esp = esp₀ s₀) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s₀.rd → s'.wr = s₀.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨x.setWidth 64, 32⟩, ⟨scA s₀, 112⟩, stkR s₀] s.mem s'.mem →
      stateAt s'.mem (x.setWidth 64) =
        compress (stateAt s.mem (x.setWidth 64)) (blockAt s.mem (x.setWidth 64 + 32)) → Q s') :
    WP isa (Impl.Hmac.Sha256.X86.compressBuf name code b) s Q := by
  have fs := hp.scr_fit
  have fsp := hp.sp_fit
  obtain ⟨fx, dS, dK, hm⟩ : x.toNat + 96 ≤ 2 ^ 32 ∧ Region.Disjoint ⟨x.setWidth 64, 96⟩ (scR s₀) ∧
      (stkR s₀).Disjoint ⟨x.setWidth 64, 96⟩ ∧ (⟨x.setWidth 64, 96⟩ : Region) ∈ s₀.wr := by
    rcases hx with rfl | rfl
    · exact ⟨hp.in_fit, hp.i_s, hp.stk_i, by simp [hp.wr]⟩
    · exact ⟨hp.ou_fit, hp.o_s, hp.stk_o, by simp [hp.wr]⟩
  have hb' : b ≠ .eax := by rcases hb with rfl | rfl <;> decide
  unfold Impl.Hmac.Sha256.X86.compressBuf
  refine WP.seq (wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => WP.block_nil ?_)
  have g₄ : ∀ r, r ≠ .eax → s₄.gpr r = s.gpr r := fun r h => by rw [u₄.other r h, u₃.other r h]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem]
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, hrd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, hwr]
  have eax₄ : s₄.gpr .eax = x + 32 := by rw [u₄.gpr, u₃.gpr, hbx]
  have hbA : (x + 32).setWidth 64 = x.setWidth 64 + 32 := addr_eq (x := x) (k := 32) (by omega_nat)
  have s32 : Region.Sub ⟨x.setWidth 64, 32⟩ ⟨x.setWidth 64, 96⟩ := sub32 _
  have s112 : Region.Sub ⟨scA s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega_nat)
  have b64 : Region.Sub ⟨(x + 32).setWidth 64, 64⟩ ⟨x.setWidth 64, 96⟩ := by
    rw [hbA]; exact sub_offset (off := 32) (by omega_nat) (by omega_nat)
  refine compressAt_of hv hnosp hstack (st := x) (scr := scr s₀) (blk := x + 32) (E := esp₀ s₀)
    (by rcases hb with rfl | rfl <;> decide) (by decide) (by rcases hb with rfl | rfl <;> decide) (by decide)
    (by rw [g₄ _ (by decide), hsp]) (by rw [g₄ _ hb', hbx]) (by rw [g₄ _ (by decide), hebp]) eax₄ hp.sp_lo
    (by omega_nat) (by rw [show (x + 32).toNat = x.toNat + 32 by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega_nat)]; omega_nat) (by omega_nat)
    ((dS.sub_left s32).sub_right s112) ?_ ((dS.sub_left b64).sub_right s112)
    (dK.sub_right s32) (hp.stk_s.sub_right s112) (dK.sub_right b64) ?_ ?_ ?_
  · rw [hbA]; exact Offset.disjoint_base _ (d := 32) (by omega_nat) (by omega_nat)
  · rw [rd₄, wr₄]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, List.mem_append_right _ hm, 32, hbA, by simp⟩
  · rw [wr₄]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hm, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp [hp.wr], 0, by simp, by simp⟩
  · intro s' h₁ h₂ h₃ h₅ h₇
    rw [m₄] at h₅ h₇
    refine hQ s' (h₁.trans rd₄) (h₂.trans wr₄) (fun r hr => by
      rw [h₃ r hr, g₄ r (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]) h₅ ?_
    rw [h₇, hbA]

/-! ## Epilogue -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa (Impl.Hmac.Sha256.X86.init name code) s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Hmac.initSha256X86.post s₀ s' := by
  have hkl := hp.kl_le
  have fi := hp.in_fit
  have fo := hp.ou_fit
  have fs := hp.scr_fit
  unfold Impl.Hmac.Sha256.X86.init
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  -- The key.
  refine WP.seq (WP.mono (Q := Buf s₀ (kl s₀)) ?_ fun s₂ h₂ => ?_)
  · refine WP.ite (decide (kl s₀ = 0)) (by simp [eval, z₁]) (fun hb => WP.block_nil ?_)
      (fun hb => key_loop_ok hp h₁ ?_)
    · rw [of_decide_eq_true hb]; exact h₁.toBuf
    · have := of_decide_eq_false hb; omega_nat
  -- The padding.
  refine WP.seq (wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_movi fun s₅ u₅ =>
    wp_cmp fun s₆ f₆ _ z₆ => WP.block_nil ?_)
  have k₆ : ∀ r, r ≠ .eax → r ≠ .ecx → s₆.gpr r = s₂.gpr r := fun r h h' => by
    rw [f₆.gpr, u₅.other r h', u₄.other r h, u₃.other r h]
  have eax₆ : s₆.gpr .eax = inn s₀ + 96 := by
    rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, h₂.ebx]
  have hP : Pad s₀ (kl s₀) s₆ :=
    ⟨⟨h₂.j_le, by rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, h₂.rd], by rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr],
      by rw [k₆ _ (by decide) (by decide), h₂.ebx], by rw [k₆ _ (by decide) (by decide), h₂.esi],
      by rw [k₆ _ (by decide) (by decide), h₂.ebp], by rw [k₆ _ (by decide) (by decide), h₂.esp],
      by rw [k₆ _ (by decide) (by decide), h₂.edx], by rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact h₂.mem⟩,
      eax₆, by rw [f₆.gpr, u₅.gpr]⟩
  have hz : s₆.zf = some (decide (kl s₀ = 64)) := by
    rw [z₆, ← f₆.gpr, k₆ _ (by decide) (by decide), h₂.edx, eax₆, cmp_end _ hkl]
  refine WP.seq (WP.mono (Q := Buf s₀ 64) ?_ fun s₇ h₇ => ?_)
  · refine WP.ite (decide (kl s₀ = 64)) (by simp [eval, hz]) (fun hb => WP.block_nil ?_)
      (fun hb => pad_loop_ok hp hP ?_)
    · rw [← of_decide_eq_true hb]; exact hP.toBuf
    · have := of_decide_eq_false hb; omega_nat
  -- The outer buffer.
  have hbufI : bytesAt s₇.mem (inA s₀ + 32) 64 = xorPad (K0 s₀) ipad := by
    rw [h₇.mem.buf, List.take_of_length_le (by rw [K0_length s₀ hp])]; rfl
  refine WP.seq ?_
  rw [← List.append_nil ((List.range 16).flatMap opadWord)]
  refine xorWords_ok 16 [] s₇ _ h₇.ebx h₇.esi (by omega_nat) (by omega_nat)
    (fun k hk => ⟨inR s₀, by simp [h₇.rd, h₇.wr, hp.wr], hp.in_in (by omega_nat) (by omega_nat)⟩)
    (fun k hk => ⟨ouR s₀, by simp [h₇.wr, hp.wr], hp.ou_in (by omega_nat) (by omega_nat)⟩)
    (hp.i_o.sep (contains_offset (by omega_nat) (by omega_nat)) (contains_offset (by omega_nat) (by omega_nat)))
    fun s₈ g₈ rd₈ wr₈ m₈ => WP.block_nil ?_
  set ob := (bytesAt s₇.mem (inA s₀ + BitVec.ofNat 64 32) (4 * 16)).map (· ^^^ (0x6a : Byte)) with hob
  have hobl : ob.length = 64 := by simp [ob, bytesAt_length]
  have hob' : ob = xorPad (K0 s₀) opad := by
    rw [hob, show 4 * 16 = 64 from rfl, show inA s₀ + BitVec.ofNat 64 32 = inA s₀ + 32 from rfl, hbufI,
      xorPad_6a]
  let bO : Region := ⟨ouA s₀ + BitVec.ofNat 64 32, 64⟩
  have sO : Region.Sub bO (ouR s₀) := sub_offset (by omega_nat) (by omega_nat)
  have F₈ : Frame [bO] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_frame _ _ _ (by rw [hobl]; exact Region.contains_self _ _)
  have bOd : ∀ R : Region, R.Disjoint (ouR s₀) → ∀ r ∈ [bO], R.Disjoint r := fun R h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right sO
  have stI₈ : stateAt s₈.mem (inA s₀) = H0 := by
    rw [← h₇.mem.stI]
    exact Proof.Sha256.Stream.stateAt_congr fun i hi =>
      frame_bytes F₈ (R := ⟨inA s₀, 32⟩) (bOd _ (hp.i_o.sub_left (sub32 _))) (by simp) hi
  have bI₈ : bytesAt s₈.mem (inA s₀ + 32) 64 = xorPad (K0 s₀) ipad := by
    rw [← hbufI]
    exact Proof.Sha256.Stream.bytesAt_congr fun i hi =>
      frame_bytes F₈ (R := ⟨inA s₀ + 32, 64⟩)
        (bOd _ (hp.i_o.sub_left (sub_offset (off := 32) (by omega_nat) (by omega_nat)))) (by simp) hi
  have stO₈ : stateAt s₈.mem (ouA s₀) = H0 := by
    rw [← h₇.mem.stO]
    refine Proof.Sha256.Stream.stateAt_congr fun i hi => frame_bytes F₈ (R := ⟨ouA s₀, 32⟩) ?_ (by simp) hi
    simp only [List.mem_singleton]; rintro r rfl
    exact Offset.base_disjoint _ (e := 32) (by omega_nat) (by have := hp.ou_fit; omega_nat)
  have bO₈ : bytesAt s₈.mem (ouA s₀ + 32) 64 = xorPad (K0 s₀) opad := by
    rw [m₈, ← hob']
    have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s₇.mem (ouA s₀ + BitVec.ofNat 64 32) ob (by omega_nat)
    rw [hobl] at this
    exact this
  have sv₈ : Saved s₀ s₈.mem := saved_frame h₇.mem.saved F₈ fun d h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact save_disj hp (hp.o_s.sub_left sO) d h₁ h₂
  have f₈ : Frame [inR s₀, ouR s₀, scR s₀] s₀.mem s₈.mem :=
    h₇.mem.frame.trans (F₈.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ouR s₀, by simp, sO⟩)
  -- The inner block.
  refine WP.seq (compBuf_of hv hnosp hstack hp (x := inn s₀) (.inl rfl) (b := .ebx) (.inl rfl) (by rw [rd₈, h₇.rd])
    (by rw [wr₈, h₇.wr]) (by rw [g₈ _ (by decide), h₇.ebx]) (by rw [g₈ _ (by decide), h₇.ebp])
    (by rw [g₈ _ (by decide), h₇.esp]) fun s₉ rd₉ wr₉ cs₉ fr₉ st₉ => ?_)
  have hI₉ : Repr s₉.mem (inA s₀) (xorPad (K0 s₀) ipad) :=
    VG.Proof.Hmac.Common.repr_block stI₈ bI₈ (by simp [xorPad, K0_length s₀ hp]) st₉
  have dO : ∀ r ∈ [(⟨inA s₀, 32⟩ : Region), ⟨scA s₀, 112⟩, stkR s₀], Region.Disjoint (ouR s₀) r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o.symm.sub_right (sub32 _)
    · exact hp.o_s.sub_right (Region.sub_prefix (by omega_nat))
    · exact hp.stk_o.symm
  have stO₉ : stateAt s₉.mem (ouA s₀) = H0 := by
    rw [← stO₈]
    exact Proof.Sha256.Stream.stateAt_congr fun i hi =>
      frame_bytes fr₉ (R := ⟨ouA s₀, 32⟩) (fun r hr => (dO r hr).sub_left (sub32 _)) (by simp) hi
  have bO₉ : bytesAt s₉.mem (ouA s₀ + 32) 64 = xorPad (K0 s₀) opad := by
    rw [← bO₈]
    exact Proof.Sha256.Stream.bytesAt_congr fun i hi =>
      frame_bytes fr₉ (R := ⟨ouA s₀ + 32, 64⟩)
        (fun r hr => (dO r hr).sub_left (sub_offset (off := 32) (by omega_nat) (by omega_nat))) (by simp) hi
  have sv₉ : Saved s₀ s₉.mem := saved_frame sv₈ fr₉ fun d h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact save_disj hp (hp.i_s.sub_left (sub32 _)) d h₁ h₂
    · exact save_disj112 hp d h₁ h₂
    · exact save_disj hp hp.stk_s d h₁ h₂
  have f₉ : Frame (allR s₀) s₀.mem s₉.mem := (f₈.mono (by simp)).trans (fr₉.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, sub32 _⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_nat)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have cs₉' : ∀ r ∈ calleeSaved, s₉.gpr r = s₇.gpr r := fun r hr => by
    rw [cs₉ r hr, g₈ r (callee_ne_eax hr)]
  -- The outer block.
  refine WP.seq (compBuf_of hv hnosp hstack hp (x := ou s₀) (.inr rfl) (b := .esi) (.inr rfl) rd₉ wr₉
    (by rw [cs₉' _ (by decide), h₇.esi]) (by rw [cs₉' _ (by decide), h₇.ebp])
    (by rw [cs₉' _ (by decide), h₇.esp]) fun s₁₀ rd₁₀ wr₁₀ cs₁₀ fr₁₀ st₁₀ => ?_)
  have hO : Repr s₁₀.mem (ouA s₀) (xorPad (K0 s₀) opad) :=
    VG.Proof.Hmac.Common.repr_block stO₉ bO₉ (by simp [xorPad, K0_length s₀ hp]) st₁₀
  have hI : Repr s₁₀.mem (inA s₀) (xorPad (K0 s₀) ipad) := by
    refine repr_congr (fun i hi => frame_bytes fr₁₀ (R := inR s₀) ?_ (by simp) hi) hI₉
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o.sub_right (sub32 _)
    · exact hp.i_s.sub_right (Region.sub_prefix (by omega_nat))
    · exact hp.stk_i.symm
  have sv₁₀ : Saved s₀ s₁₀.mem := saved_frame sv₉ fr₁₀ fun d h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact save_disj hp (hp.o_s.sub_left (sub32 _)) d h₁ h₂
    · exact save_disj112 hp d h₁ h₂
    · exact save_disj hp hp.stk_s d h₁ h₂
  have f₁₀ : Frame (allR s₀) s₀.mem s₁₀.mem := f₉.trans (fr₁₀.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ouR s₀, by simp, sub32 _⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_nat)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have cs₁₀' : ∀ r ∈ calleeSaved, s₁₀.gpr r = s₇.gpr r := fun r hr => by rw [cs₁₀ r hr, cs₉' r hr]
  -- Epilogue.
  refine WP.mono (epilogue_ok hp rd₁₀ wr₁₀ (by rw [cs₁₀' _ (by decide), h₇.ebp])
    (by rw [cs₁₀' _ (by decide), h₇.esp]) sv₁₀) fun s' ⟨m', cs'⟩ => ⟨⟨cs', ?_⟩, ?_⟩
  · rw [m']
    refine f₁₀.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [allR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [hp.ret_i, hp.ret_o, hp.ret_s, ret_a hp, ret_stk hp]
  · show Repr s'.mem (inA s₀) (xorPad (blockKey sha256 (bytesAt s₀.mem (kA s₀) (kl s₀))) ipad) ∧
      Repr s'.mem (ouA s₀) (xorPad (blockKey sha256 (bytesAt s₀.mem (kA s₀) (kl s₀))) opad)
    rw [blockKey_eq hp, m']
    exact ⟨hI, hO⟩

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Hmac.initSha256X86, VG.Proof.Hmac.X86.Init.initWide, VG.Proof.Hmac.X86.Init.narrowWr, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem, VG.X86.State.withRegions_rd,
    VG.X86.State.withRegions_wr] $(loc)?)

theorem verified
    (hct : ConstantTime isa Proof.Hmac.initSha256X86.pre Proof.Hmac.initSha256X86.pub
      (Impl.Hmac.Sha256.X86.init name code)) :
    Verified X86.target (Impl.Hmac.Sha256.X86.init name code) (Spec.Hmac.initSha256Contract X86.abi 20) :=
  have hsat := initWide_implies.sat_left
  (Verified.widen (Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, h⟩ := correct hv hnosp hstack (pre_of hs)
      exact ⟨t, s', he, h⟩) hct
    (.refl (hsat.elim fun s hs => ⟨_, initWide_pre s hs⟩)))
    narrowWr initWide_pre
    (fun _ h => by
      obtain ⟨_, _, h₃, _⟩ := h
      rw [h₃]
      exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl)
        (.cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl) .nil))))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies initWide_implies

end VG.Proof.Hmac.Sha256.X86.Init
