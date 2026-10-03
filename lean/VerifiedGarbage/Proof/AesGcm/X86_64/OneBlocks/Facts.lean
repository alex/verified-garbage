import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Ok

/-!
# AES-GCM on x86-64: after `oneBlocks`

Untrusted: everything here is checked by Lean. What `seal` and `open` know
after `oneBlocks` (`ob_facts`): the whole blocks of the data in counter mode,
the counter after them, the accumulator over them, and everything else kept.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32 ghashFrom ghash blocks inc32 zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What `seal` and `open` write after their entry, with `oneBlocks`. -/
abbrev oneFrameB (W D SP : Addr) (n : Nat) : List Region :=
  [⟨W, 128⟩, ⟨W + BitVec.ofNat 64 192, 32⟩, ⟨W + BitVec.ofNat 64 240, 2320⟩, ⟨D, n⟩, below SP 24]

theorem oneFrame_B {W D SP : Addr} {n k : Nat} (hk : k ≤ n) {m m' : Mem}
    (h : Frame (oneFrame W (D + BitVec.ofNat 64 k) SP (n - k)) m m') : Frame (oneFrameB W D SP n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 192, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩

theorem obFrame_B {W D SP : Addr} {n : Nat} {m m' : Mem}
    (h : Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame W SP D (n / 16)) m m') : Frame (oneFrameB W D SP n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 192, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W, 128⟩, by simp, by rw [add_ofNat_assoc]; exact Offset.sub_base W (by decide)⟩
    · exact ⟨⟨W, 128⟩, by simp, by rw [add_ofNat_assoc]; exact Offset.sub_base W (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, fun _ h => h⟩

theorem oneB_trans {W D SP : Addr} {n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Frame (oneFrameB W D SP n) m₁ m₂)
    (h₂ : Frame (oneFrameB W D SP n) m₂ m₃) : Frame (oneFrameB W D SP n) m₁ m₃ := h₁.trans h₂

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The kept values are outside `oneFrameB`. -/
theorem kept_oneFrameB {D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) (h : (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240)) :
    ∀ r ∈ oneFrameB W D SP n, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := 8) (d := 0) (k := 128) (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (by omega) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (hD.sub_right (Lay.wSub (by omega))).symm
  · exact (t_w.sub_right (Lay.wSub (by omega))).symm

theorem saved_oneFrameB {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) : ∀ r ∈ oneFrameB W D SP n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 48) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.wSub (by decide))).symm
  · exact (t_w.sub_right (Lay.wSub (by decide))).symm

/-- The key context is outside `oneFrameB`. -/
theorem ctx_oneFrameB {D : Addr} {n : Nat} (hC : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩)
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) : ∀ r ∈ oneFrameB W D SP n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.cw'.sub_right (by simpa using Offset.sub_base W (d := 0) (n := 128) (k := 2560) (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact hC
  · exact t_c.symm

/-- The parts of the state `seal` and `open` keep through `oneBlocks`. -/
theorem st_obFrame {D : Addr} {n d k : Nat} (h : (d + k ≤ 16) ∨ (32 ≤ d ∧ d + k ≤ 48) ∨ (64 ≤ d ∧ d + k ≤ 80))
    (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame W SP D (n / 16)),
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [add_ofNat_assoc]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (by omega) (by omega) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (by omega) (by omega) (by decide)
  · exact ((hD.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by omega))).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (t_w.sub_right (Lay.wSub (by omega))).symm

/-- What `seal` and `open` know after `oneBlocks`, from what it did to the
whole blocks (`ho`, `hc`) and the accumulator (`hy`, over `Z`). -/
theorem ob_facts {R : Nat} {D : Addr} {n : Nat} {s s₃ : State} (h : ObPre Ctx W SP R D n s)
    (P : ObPost Ctx W SP D n s s₃) {H icb : Block} {x Z : List Byte}
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hcb : blockAt s.mem (cbA W) = icb)
    (habs : Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x) (hx : x.length % 16 = 0)
    (ho : blocksAt s₃.mem D (n / 16) = ctr32 (ciphOf s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem D (n / 16)))
    (hc : blockAt s₃.mem (cbA W) = Nat.repeat inc32 (n / 16) (blockAt s.mem (cbA W)))
    (hZ : Z.length % 16 = 0) (hy : blockAt s₃.mem (yA W) = ghashFrom H (blockAt s.mem (yA W)) (blocks Z)) :
    Frame (oneFrameB W D SP n) s.mem s₃.mem ∧ RoundsAt s₃.mem W R ∧
    blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H ∧ ciphOf s₃.mem Ctx R = ciphOf s.mem Ctx R ∧
    blockAt s₃.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) ∧
    bytesAt s₃.mem D (16 * (n / 16)) = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D (16 * (n / 16))) ∧
    Ctr s₃.mem (cbA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64) (ciphOf s₃.mem Ctx R) icb (16 * (n / 16)) ∧
    Absorbed s₃.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (x ++ Z) ∧
    bytesAt s₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
  have fr := P.frame
  have hD := h.data.ok.w
  have hR := h.rounds.2
  have hlt := h.data.ok.lt
  have fB := obFrame_B fr
  have dC := ctx_oneFrameB L h.data.ctx h.t_c
  have hc₃ : ciphOf s₃.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame fB dC hR
  have cw := Proof.Gcm.ctr_whole (ks := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64) (icb := icb) (n := 0)
    ⟨hcb, fun h => absurd rfl h⟩ rfl ho hc
  rw [Nat.zero_add, ← hc₃] at cw
  refine ⟨fB, rounds_frame fB (kept_oneFrameB L hD h.t_w (.inl ⟨by decide, by decide⟩)) h.rounds,
    by rw [blockAt_frame fB (fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))), hH], hc₃,
    by simpa using blockAt_frame fr (st_obFrame L (d := 0) (k := 16) (.inl (by decide)) hD h.t_w),
    by rw [cw.1, hc₃], cw.2, Proof.Gcm.absorb_whole habs hx hZ (by rw [hy]), bytesAt_frame fr (fun r hr => ?_) (by omega)⟩
  have hs : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨D, n⟩ := Offset.sub_base D (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · rw [add_ofNat_assoc]; exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · rw [add_ofNat_assoc]; exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · simpa using Offset.disjoint D (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (e := 0) (k := n / 16 * 16)
      (.inr (by omega)) (by omega) (by omega)
  · exact (hD.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (h.t_d.sub_right hs).symm

end

end VG.Proof.AesGcm.X86_64
