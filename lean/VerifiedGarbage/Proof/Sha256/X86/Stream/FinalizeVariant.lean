import VerifiedGarbage.Proof.Sha256.X86.Stream.Finalize
import VerifiedGarbage.Proof.Sha256.X86.Stream.CompressAt

/-! SHA-256's padding loop, independent of compression backend. -/
namespace VG.Proof.Sha256.X86.Stream.Finalize
open VG VG.X86
open VG.Proof.Sha256.X86.Stream
open VG.Proof.Sha256.Stream
open VG.Spec.Sha256 (stateAt blockAt compress bytesAt HashValue wordBytes parseBlock)
variable {name : String} {code : Prog isa}
  (hv : Verified X86.target code Proof.Sha256.compressX86)
  (hnosp : NoSp code) (hstack : stackUse code = 0)
include hv hnosp hstack

theorem compress_buf_of {s₀ : State} (hp : Pre s₀) {s : State} (hC : Common s₀ s)
    (heax : s.gpr .eax = st s₀ + BitVec.ofNat 32 32) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      stateAt s'.mem (stA s₀) = compress (stateAt s.mem (stA s₀)) (blockAt s.mem (stA s₀ + 32)) → Q s') :
    WP isa (Impl.MdStream.X86.compressAt name code .ebx .ebp) s Q := by
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hsp := hp.sp_fit
  have e32 : Region.Sub ⟨stA s₀, 32⟩ (stR s₀) := Region.sub_prefix (by omega)
  have e112 : Region.Sub ⟨scA s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hb : (st s₀ + BitVec.ofNat 32 32).setWidth 64 = stA s₀ + BitVec.ofNat 64 32 := addr_eq (by omega)
  have eb : Region.Sub ⟨(st s₀ + BitVec.ofNat 32 32).setWidth 64, 64⟩ (stR s₀) := by
    rw [hb]; exact sub_offset (by omega) (by omega)
  refine compressAt_of hv hnosp hstack (st := st s₀) (scr := scr s₀) (blk := st s₀ + BitVec.ofNat 32 32) (E := esp₀ s₀)
    (by decide) (by decide) (by decide) (by decide) hC.esp hC.ebx hC.ebp heax hp.sp_lo (by omega)
    (by rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (by omega)
    ((hp.st_scr.sub_left e32).sub_right e112) ?_ ((hp.st_scr.sub_left eb).sub_right e112)
    (hp.stk_st.sub_right e32) (hp.stk_scr.sub_right e112) (hp.stk_st.sub_right eb) ?_ ?_ ?_
  · rw [hb]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨stR s₀, by simp, 32, hb, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · intro s' hrd hwr hcs hf hstate
    have cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := hcs
    have word : ∀ d, 112 ≤ d → d + 4 ≤ 160 →
        s'.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
      intro d h₁ h₂
      refine hf.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.st_scr.symm.sub_left (hp.scr_sub h₂)).sub_right e32
      · rw [addr_eq (by omega)]; exact Offset.disjoint_base _ (by omega) (by omega)
      · exact hp.stk_scr.symm.sub_left (hp.scr_sub h₂)
    refine hQ s' ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.ebx,
      by rw [cs _ (by decide)]; exact hC.ebp, by rw [cs _ (by decide)]; exact hC.esp,
      hC.frame.trans (hf.sub ?_), fun p hp' => ?_, by rw [word 128 (by omega) (by omega)]; exact hC.lo,
      by rw [word 132 (by omega) (by omega)]; exact hC.hi, by rw [word 136 (by omega) (by omega)]; exact hC.outp⟩
      hcs (by rw [hstate, show (st s₀ + BitVec.ofNat 32 32).setWidth 64 = stA s₀ + 32 from hb])
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, e32⟩
      · exact ⟨scR s₀, by simp, e112⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
        simp only [VG.Impl.Sha256.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl | rfl <;> simp
      rw [word p.2 hd.1 (by omega)]
      exact hC.saved p hp'

theorem body_of {s₀ : State} (hp : Pre s₀) {k n : Nat} {s : State} (h : LInv s₀ k n s) :
    WP isa (Impl.MdStream.X86.finalizeBody Impl.Sha256.X86.Stream.params name code) s (Step s₀ k) := by
  have hk := h.k_le; have hn := h.n_le; have hst := hp.st_fit
  have hC := h.toCommon
  unfold Impl.MdStream.X86.finalizeBody
  change WP isa _ _ _
  -- `eax := 64` or `56`: the end of the zeros.
  refine WP.seq (wp_movi fun s₁ u₁ => wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
  have hz₂ : s₂.zf = some (decide (k = 0)) := by
    rw [z₂, u₁.other _ (by decide), h.esi, BitVec.and_self, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .eax = BitVec.ofNat 32 (56 + 8 * k) ∧
      (∀ r, r ≠ .eax → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr) ?_
    fun s₃ ⟨heax₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show s₂.zf = _; rw [hz₂]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine wp_movi fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr]; rfl, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [u₃.other r hr, f₂.gpr, u₁.other r hr]
      · rw [u₃.mem, f₂.mem, u₁.mem]
      · rw [u₃.rd, f₂.rd, u₁.rd]
      · rw [u₃.wr, f₂.wr, u₁.wr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [f₂.gpr, u₁.gpr, show k = 1 by omega]; rfl, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [f₂.gpr, u₁.other r hr]
      · rw [f₂.mem, u₁.mem]
      · rw [f₂.rd, u₁.rd]
      · rw [f₂.wr, u₁.wr]
  -- `ecx := 0; eax -= edi`: zero the rest of the buffer, up to `lim`.
  have hC₃ : Common s₀ s₃ := hC.of_gpr (fun r hr => g₃ r (regs3 hr).1) m₃ rd₃ wr₃
  refine WP.seq (wp_movi fun s₄ u₄ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have hC₄ : Common s₀ s₄ := hC₃.of_gpr (fun r hr => u₄.other r (regs3 hr).2.1) u₄.mem u₄.rd u₄.wr
  have hecx₄ : s₄.gpr .ecx = 0 := u₄.gpr
  have hedi₄ : s₄.gpr .edi = BitVec.ofNat 32 n := by rw [u₄.other _ (by decide), g₃ _ (by decide), h.edi]
  have heax₅ : s₅.gpr .eax = BitVec.ofNat 32 (56 + 8 * k - n) := by
    rw [u₅.gpr, u₄.other _ (by decide), heax₃, hedi₄, sub_ofNat (a := 56 + 8 * k) (b := n) (by omega)]
  have hZ : Zero s₀ s₄ n (56 + 8 * k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => u₅.other r ?_, u₅.rd, u₅.wr,
      by rw [u₅.other _ (by decide), hedi₄, Nat.add_zero], by rw [heax₅, Nat.sub_zero],
      by rw [u₅.mem, List.replicate_zero, writeBytes_nil]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have hz₅ : s₅.zf = some (decide (56 + 8 * k - n = 0)) := by
    rw [z₅, ← u₅.gpr, heax₅, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (zero_ok hp hC₄ hecx₄ (by omega) hn hZ hz₅) fun s₆ hZ₆ => ?_)
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃]
  have hf₆ : Frame [stR s₀] s₄.mem s₆.mem := by
    rw [hZ₆.mem]; exact buf_frame _ (by simp only [List.length_replicate]; omega)
  obtain ⟨hfr₆, hsv₆, hlo₆, hhi₆, hout₆⟩ := hC₄.frame_keep hp (hf₆.mono (by simp))
  have hC₆ : Common s₀ s₆ := ⟨hZ₆.rd.trans hC₄.rd, hZ₆.wr.trans hC₄.wr, by rw [hZ₆.keep _ (by simp), hC₄.ebx],
    by rw [hZ₆.keep _ (by simp), hC₄.ebp], by rw [hZ₆.keep _ (by simp), hC₄.esp], hfr₆, hsv₆, hlo₆, hhi₆, hout₆⟩
  have hst₆ : stateAt s₆.mem (stA s₀) = stateAt s.mem (stA s₀) := by
    rw [hZ₆.mem, hm₄]
    apply stateAt_congr
    intro i hi
    rw [st_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (stA s₀ + 32) (56 + 8 * k) =
      bytesAt s.mem (stA s₀ + 32) n ++ List.replicate (56 + 8 * k - n) 0 := by
    rw [hZ₆.mem, hm₄, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have hesi₆ : s₆.gpr .esi = BitVec.ofNat 32 k := by
    rw [hZ₆.keep _ (by simp), u₄.other _ (by decide), g₃ _ (by decide), h.esi]
  -- In the last block, the length.
  refine WP.seq (wp_test fun s₇ f₇ z₇ => WP.block_nil ?_)
  have hC₇ : Common s₀ s₇ := hC₆.of_gpr (fun r _ => by rw [f₇.gpr]) f₇.mem f₇.rd f₇.wr
  have hz₇ : s₇.zf = some (decide (k = 0)) := by
    rw [z₇, hesi₆, BitVec.and_self, ofNat_beq_zero (by omega)]
  have hesi₇ : s₇.gpr .esi = BitVec.ofNat 32 k := by rw [f₇.gpr, hesi₆]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common s₀ s₈ ∧ s₈.gpr .esi = BitVec.ofNat 32 k ∧
      stateAt s₈.mem (stA s₀) = stateAt s.mem (stA s₀) ∧
      ∀ m, R₀ s₀ m → bytesAt s₈.mem (stA s₀ + 32) 64 = bytesAt s.mem (stA s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)) ?_
    fun s₈ ⟨hC₈, hesi₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show s₇.zf = _; rw [hz₇]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine WP.mono (len_ok hp hC₇) fun s₈ ⟨g₈, rd₈, wr₈, m₈⟩ => ?_
      have hfL : Frame [stR s₀] s₇.mem s₈.mem := by
        rw [m₈]; exact buf_frame _ (by simp [lenL, wordBytes])
      obtain ⟨hfr, hsv, hlo, hhi, hout⟩ := hC₇.frame_keep hp (hfL.mono (by simp))
      refine ⟨⟨rd₈.trans hC₇.rd, wr₈.trans hC₇.wr, by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.ebx],
        by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.ebp],
        by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.esp], hfr, hsv, hlo, hhi, hout⟩,
        by rw [g₈ _ (by decide) (by decide) (by decide), hesi₇], ?_, fun m hm => ?_⟩
      · rw [m₈, ← hst₆, ← f₇.mem]
        apply stateAt_congr
        intro i hi
        rw [st_add]
        exact writeBytes_before _ _ _ (by omega) (by simp [lenL, wordBytes])
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        have e := bytesAt_writeBytes s₇.mem (stA s₀ + 32) 56 (lenL s₀) (by simp [lenL, wordBytes])
        simp only [lenL, List.length_append, show ∀ w, (wordBytes w).length = 4 from fun _ => rfl] at e
        rw [m₈, e, f₇.mem, hby₆, ← lenBytes_halves _ _ m hm.2]
        simp [List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₇, hesi₇, by rw [f₇.mem, hst₆], fun m _ => ?_⟩
      rw [f₇.mem, hby₆]; simp
  -- Compress the block.
  refine WP.seq (WP.mono (args_ok hC₈) fun s₉ ⟨hC₉, g₉, heax₉, hf₉⟩ => ?_)
  refine WP.seq (compress_buf_of hv hnosp hstack hp hC₉ heax₉ fun s₁₀ hC₁₀ cs₁₀ hst₁₀ => ?_)
  have hesi₁₀ : s₁₀.gpr .esi = BitVec.ofNat 32 k := by
    rw [cs₁₀ _ (by decide), g₉ _ (by decide), hesi₈]
  have hbyte : ∀ i, i < 96 → s₉.mem (stA s₀ + BitVec.ofNat 64 i) = s₈.mem (stA s₀ + BitVec.ofNat 64 i) :=
    fun i hi => frame_bytes hf₉ (R := stR s₀) (by simpa using hp.a_st.symm) (by simp) hi
  have hblk : ∀ m, R₀ s₀ m → blockAt s₉.mem (stA s₀ + 32) = parseBlock fun t =>
      (bytesAt s.mem (stA s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)).getD t 0 := by
    intro m hm
    apply parseBlock_congr
    intro t ht
    rw [show stA s₀ + 32 + BitVec.ofNat 64 t = stA s₀ + BitVec.ofNat 64 (32 + t) by
      simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl, hbyte _ (by omega),
      ← show stA s₀ + 32 + BitVec.ofNat 64 t = stA s₀ + BitVec.ofNat 64 (32 + t) by
      simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl]
    exact bytesAt_getD (hby₈ m hm) ht
  have hst₉ : stateAt s₉.mem (stA s₀) = stateAt s₈.mem (stA s₀) :=
    stateAt_congr fun i hi => hbyte i (by omega)
  -- Next block, if any.
  refine wp_movi fun s₁₁ u₁₁ => wp_subi fun s₁₂ u₁₂ z₁₂ => WP.block_nil ?_
  have hC₁₂ : Common s₀ s₁₂ := hC₁₀.of_gpr (fun r hr => by
      rw [u₁₂.other r (regs3 hr).2.2.2.2, u₁₁.other r (regs3 hr).2.2.2.1]) (by rw [u₁₂.mem, u₁₁.mem])
    (by rw [u₁₂.rd, u₁₁.rd]) (by rw [u₁₂.wr, u₁₁.wr])
  have hz : s₁₂.zf = some (decide (k = 1)) := by
    rw [z₁₂, u₁₁.other _ (by decide), hesi₁₀, lit32 1, sub_beq (a := k) (b := 1) (by omega) (by omega)]
  have hst : ∀ m, R₀ s₀ m → stateAt s₁₂.mem (stA s₀) = compress (stateAt s.mem (stA s₀)) (parseBlock fun t =>
      (bytesAt s.mem (stA s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)).getD t 0) := by
    intro m hm
    rw [u₁₂.mem, u₁₁.mem, hst₁₀, hst₉, hst₈, hblk m hm]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by show s₁₂.zf = _; rw [hz]; rfl, rfl, ⟨hC₁₂, by omega, by omega, ?_, ?_, fun m hm => ?_⟩⟩
    · rw [u₁₂.other _ (by decide), u₁₁.gpr]; rfl
    · rw [u₁₂.gpr, u₁₁.other _ (by decide), hesi₁₀]; rfl
    · rw [h.hash m hm]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst m hm]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by show s₁₂.zf = _; rw [hz]; rfl, hC₁₂, fun m hm => ?_⟩
    rw [h.hash m hm, hst m hm]
    simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]


end VG.Proof.Sha256.X86.Stream.Finalize
