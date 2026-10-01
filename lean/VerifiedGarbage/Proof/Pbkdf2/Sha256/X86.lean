import VerifiedGarbage.Proof.Pbkdf2.X86.Iterate
import VerifiedGarbage.Proof.Sha256.X86.Stream.CompressAt
import VerifiedGarbage.Impl.Pbkdf2.Sha256.X86

/-! PBKDF2-SHA-256's direct-compression loop, proved once for any backend. -/
namespace VG.Proof.Pbkdf2.Sha256.X86
open VG VG.X86
open VG.Proof.Pbkdf2.X86
open VG.Proof.Sha256.X86.Stream
open VG.Impl.Pbkdf2.X86 (digest)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt blockAt_eq xorBytes_length digest_self add_ofNat contains_base)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Hmac.Common (bytesAt_writeBytes_self bytesAt_writeBytes_sep bytesAt_length)
open VG.Spec.Sha256 (stateAt compress blockAt bytesAt)
variable {name : String} {code : Prog isa}
  (hv : Verified X86.target code Proof.Sha256.compressX86)
  (hnosp : NoSp code) (hstack : stackUse code = 0)
include hv hnosp hstack

theorem cmp_of {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s)
    (hax : s.gpr .eax = scr s₀ + BitVec.ofNat 32 192) {Q : State → Prop}
    (k : ∀ s', Keep s₀ s s' →
      stateAt s'.mem (tA s₀) = compress (stateAt s.mem (tA s₀)) (blockAt s.mem (blkA s₀)) → Q s') :
    WP isa (Impl.MdStream.X86.compressAt name code .ebx .ebp) s Q := by
  have := hp.scr_fit; have := hp.t_fit
  have ea : (scr s₀ + BitVec.ofNat 32 192).setWidth 64 = blkA s₀ := addr_off (len := 256) hp.scr_fit (by omega)
  have et : (scr s₀ + BitVec.ofNat 32 192).toNat = (scr s₀).toNat + 192 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsc : scR s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  have htr : tR s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  have b64 : Region.Sub ⟨(scr s₀ + BitVec.ofNat 32 192).setWidth 64, 64⟩ (sR s₀ 192 64) := by
    rw [ea]; exact fun _ h => h
  refine compressAt_of hv hnosp hstack (st := tP s₀) (scr := scr s₀) (blk := scr s₀ + BitVec.ofNat 32 192) (E := esp₀ s₀)
    (by decide) (by decide) (by decide) (by decide) h.esp h.ebx h.ebp hax hp.sp_lo (by omega)
    (by rw [et]; omega) (by omega) (hp.t_s.sub_right (cmp_sub s₀))
    ((hp.t_s.sub_right (scr_sub s₀ (o := 192) (n := 64) (by omega))).symm.sub_left b64)
    ((scr_disj0 s₀ (a := 192) (m := 64) (by omega) (by omega)).sub_left b64)
    hp.stk_t (hp.stk_s.sub_right (cmp_sub s₀)) (hp.stk_s.sub_right fun a ha => scr_sub s₀ (o := 192) (n := 64) (by omega) a (b64 a ha)) ?_ ?_
    fun s' hrd hwr hcs hf hst => k s' ⟨hrd, hwr, fun r hr => hcs r (by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved]), hf⟩ (by rw [hst, ea])
  · rw [ea]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨scR s₀, List.mem_append_right _ hsc, 192, rfl, by simp⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨tR s₀, htr, 0, by simp, by simp⟩
    · exact ⟨scR s₀, hsc, 0, by simp, by simp⟩

theorem body_ok {s₀ : State} (hp : Pre s₀) {r : Nat} {s : State} (h : Inv s₀ (r + 1) s) :
    WP isa (Impl.Pbkdf2.Sha256.X86.body name code) s fun s' => VG.X86.eval .ne s' = some (r != 0) ∧ Inv s₀ r s' := by
  have := hp.scr_fit
  unfold Impl.Pbkdf2.Sha256.X86.body
  have hU : ∀ {m : Mem}, Frame [tR s₀, cmpR s₀, stkR s₀] s.mem m →
      bytesAt m (blkA s₀) 32 = bytesAt s.mem (blkA s₀) 32 :=
    fun hf => frame_bytesAt hf (blk_disj hp) (by omega)
  have hpad : ∀ {m : Mem}, Frame (bodyR s₀) s.mem m → bytesAt m (blkA s₀ + 32) 32 = pad96 := by
    intro m hf
    rw [show blkA s₀ + 32 = scA s₀ + BitVec.ofNat 64 224 by
      change scA s₀ + 192 + 32 = scA s₀ + BitVec.ofNat 64 224
      rw [BitVec.add_assoc]; rfl, ← h.pad]
    exact frame_bytesAt hf (body_disj hp (o := 224) (n := 32) (.inr (Nat.le_refl _)) (by omega)) (by omega)
  -- The inner hash.
  refine WP.seq ?_
  refine load_ok hp h.toRegs (o := 0) (by omega) fun s₁ k₁ e₁ => ?_
  refine atBlock_ok (rest := []) (h.toRegs.keep k₁) fun s₂ k₂ m₂ x₂ => WP.block_nil ?_
  have h₂ := (h.toRegs.keep k₁).keep k₂
  refine WP.seq (cmp_of hv hnosp hstack hp h₂ x₂ fun s₃ k₃ e₃ => ?_)
  rw [m₂, e₁, blockAt_eq (hpad (frame_body k₁.frame (by simp))), hU k₁.frame] at e₃
  -- The outer hash.
  have h₃ := h₂.keep k₃
  refine WP.seq ?_
  refine digest_ok hp h₃ fun s₄ h₄ g₄ f₄ m₄ => ?_
  refine load_ok hp h₄ (o := 96) (by omega) fun s₅ k₅ e₅ => ?_
  refine atBlock_ok (rest := []) (h₄.keep k₅) fun s₆ k₆ m₆ x₆ => WP.block_nil ?_
  have h₆ := (h₄.keep k₅).keep k₆
  have f₃₄ : Frame (bodyR s₀) s.mem s₄.mem :=
    (frame_body ((k₁.trans k₂).trans k₃).frame (by simp)).trans (frame_body f₄ (by simp))
  refine WP.seq (cmp_of hv hnosp hstack hp h₆ x₆ fun s₇ k₇ e₇ => ?_)
  have hX : bytesAt s₅.mem (blkA s₀) 32 = Pbkdf2.digest (stateAt s₃.mem (tA s₀)) := by
    rw [frame_bytesAt (p := blkA s₀) (n := 32) k₅.frame (blk_disj hp) (by omega), m₄, digest_self]
  rw [m₆, e₅, blockAt_eq (hpad (f₃₄.trans (frame_body k₅.frame (by simp)))), hX, e₃] at e₇
  -- The digest, `T ← T ⊕ U` and the count.
  have h₇ := h₆.keep k₇
  refine digest_ok hp h₇ fun s₈ h₈ g₈ f₈ m₈ => ?_
  refine xor_ok (p := scr s₀) (by omega) 8 (Nat.le_refl _) _ s₈ _ h₈.ebp
    (fun j hj => InRegions.right (by rw [add_ofNat]; exact in_scr hp h₈.wr (a := 192 + 4 * j) (n := 4) (by omega)))
    (fun j hj => by rw [add_ofNat]; exact in_scr hp h₈.wr (a := 160 + 4 * j) (n := 4) (by omega))
    fun s₉ g₉ rd₉ wr₉ m₉ => ?_
  rw [show 4 * 8 = 32 from rfl] at m₉
  have f₉ : Frame [sR s₀ 160 32] s₈.mem s₉.mem := by
    rw [m₉]
    exact writeBytes_frame _ _ _ (contains_base (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]))
  have h₉ := h₈.write (fun r hr => g₉ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd₉ wr₉ (R := scR s₀) (by simp)
    (f₉.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)
  refine wp_subi fun s₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  have h₁₀ := h₉.write (fun r hr => u₁₀.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) u₁₀.rd u₁₀.wr (R := tR s₀) (by simp)
    (by rw [u₁₀.mem]; exact Frame.refl _ _)
  have xedi : s₉.gpr .edi = BitVec.ofNat 32 (r + 1) := by
    rw [g₉ _ (by decide), g₈ _ (by decide), k₇.gpr _ (by simp [kept]), k₆.gpr _ (by simp [kept]),
      k₅.gpr _ (by simp [kept]), g₄ _ (by decide), k₃.gpr _ (by simp [kept]), k₂.gpr _ (by simp [kept]),
      k₁.gpr _ (by simp [kept]), h.edi]
  have hlt : r + 1 < 2 ^ 32 := by have := h.le; have := (arg s₀ 2).isLt; simp only [nn] at *; omega
  have e₁₀ : s₉.gpr .edi - 1 = BitVec.ofNat 32 r := by
    rw [xedi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.add_sub_cancel]
  have fb : Frame (bodyR s₀) s.mem s₁₀.mem := by
    rw [u₁₀.mem]
    exact f₃₄.trans (frame_body ((k₅.trans k₆).trans k₇).frame (by simp)) |>.trans (frame_body f₈ (by simp))
      |>.trans (frame_body f₉ (by simp))
  have f₈' : Frame [tR s₀, cmpR s₀, stkR s₀, sR s₀ 192 32] s.mem s₈.mem :=
    (((k₁.trans k₂).trans k₃).frame.mono (by simp)) |>.trans (f₄.mono (by simp))
      |>.trans ((((k₅.trans k₆).trans k₇).frame).mono (by simp)) |>.trans (f₈.mono (by simp))
  have hT : bytesAt s₈.mem (TA s₀) 32 = bytesAt s.mem (TA s₀) 32 :=
    frame_bytesAt f₈' (T_disj hp) (by omega)
  have hU₈ : bytesAt s₈.mem (blkA s₀) 32 = stepM s₀ (bytesAt s.mem (blkA s₀) 32) := by
    rw [m₈, digest_self, e₇]; rfl
  have hsep : Mem.Sep (blkA s₀) 32 (TA s₀)
      (Spec.Pbkdf2.xorBytes (bytesAt s₈.mem (TA s₀) 32) (bytesAt s₈.mem (blkA s₀) 32)).length := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    exact Region.Disjoint.sep (scr_disj s₀ (a := 192) (m := 32) (b := 160) (n := 32) (by omega) (by omega)
      (by omega)) (contains_base (Nat.le_refl _)) (contains_base (Nat.le_refl _))
  have hU₁₀ : bytesAt s₁₀.mem (blkA s₀) 32 = stepM s₀ (bytesAt s.mem (blkA s₀) 32) := by
    rw [u₁₀.mem, m₉, bytesAt_writeBytes_sep _ _ hsep (by omega), hU₈]
  have hT₁₀ : bytesAt s₁₀.mem (TA s₀) 32 =
      Spec.Pbkdf2.xorBytes (bytesAt s.mem (TA s₀) 32) (stepM s₀ (bytesAt s.mem (blkA s₀) 32)) := by
    have := bytesAt_writeBytes_self s₈.mem (TA s₀)
      (Spec.Pbkdf2.xorBytes (bytesAt s₈.mem (TA s₀) 32) (bytesAt s₈.mem (blkA s₀) 32))
      (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length] at this
    rw [u₁₀.mem, m₉, this, hT, hU₈]
  have hle : r ≤ nn s₀ := by have := h.le; omega
  refine ⟨?_, { h₁₀ with edi := ?_, saved := h.saved.frame hp fb, pad := ?_, le := hle, val := ?_ }⟩
  · rw [eval_ne, z₁₀, e₁₀, ofNat_beq_zero (by omega)]
    cases r <;> rfl
  · rw [u₁₀.gpr, e₁₀]
  · rw [← h.pad]
    exact frame_bytesAt fb (body_disj hp (o := 224) (n := 32) (.inr (Nat.le_refl _)) (by omega)) (by omega)
  · rw [h.val, hU₁₀, hT₁₀]; rfl

theorem loop_ok {s₀ : State} (hp : Pre s₀) {n : Nat} {s : State} (h : Inv s₀ n s)
    (hz : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) (.loop (Impl.Pbkdf2.Sha256.X86.body name code) .ne)) s (Inv s₀ 0) := by
  refine WP.ite (decide (n = 0)) (by show s.zf = _; rw [hz]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => Inv s₀ (m + 1) s) (fun m s hs => WP.mono (body_ok hv hnosp hstack hp hs) fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

/-- Prologue and epilogue are unchanged; the loop calls this compressor. -/
theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa (Impl.Pbkdf2.Sha256.X86.iterate name code) s₀ (Post s₀) := by
  unfold Impl.Pbkdf2.Sha256.X86.iterate
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  exact WP.seq (WP.mono (loop_ok hv hnosp hstack hp h₁ z₁) fun s₂ h₂ => epilogue_ok hp h₂)

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Pbkdf2.iterateSha256X86, VG.Proof.Pbkdf2.X86.iterateWide,
    VG.Proof.Pbkdf2.X86.narrowRd, VG.Proof.Pbkdf2.X86.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem verified
    (hct : ConstantTime isa Proof.Pbkdf2.iterateSha256X86.pre
      Proof.Pbkdf2.iterateSha256X86.pub (Impl.Pbkdf2.Sha256.X86.iterate name code)) :
    Verified X86.target (Impl.Pbkdf2.Sha256.X86.iterate name code) (Spec.Pbkdf2.iterateSha256Contract X86.abi 20) :=
  have hsat := iterateWide_implies.sat_left
  (Verified.narrowTo (Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, h⟩ := correct hv hnosp hstack (pre_of hs)
      exact ⟨t, s', he, h⟩) hct (.refl ⟨sat, sat_pre⟩))
    narrowRd narrowWr iterateWide_pre
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
          0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies iterateWide_implies

end VG.Proof.Pbkdf2.Sha256.X86
