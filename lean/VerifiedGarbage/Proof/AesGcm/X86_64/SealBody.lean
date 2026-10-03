import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts

/-!
# AES-GCM on x86-64: the body of `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. After `J₀` and the additional
data: the whole blocks encrypted and absorbed (`oneBlocks`), the rest
encrypted (`oneCrypt`), and the tag of the ciphertext (`oneTag 0`):
`sealBody_ok`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32 ghashFrom ghash blocks inc32 zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The first 48 bytes of the state are outside `crypt`'s frame. -/
theorem st_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataOk (W + BitVec.ofNat 64 16) W SP s D n) {d k : Nat}
    (hk : d + k ≤ 48) : ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W SP D n,
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.st.sub_right (Lay.stSub (by omega))).symm
  · exact L.st_st (.inl (by omega)) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega)).symm

omit L in
/-- A prefix of the data is outside `crypt`'s frame over the rest. -/
theorem pre_crFrame {s : State} {D : Addr} {n k : Nat} (hd : DataOk (W + BitVec.ofNat 64 16) W SP s D n)
    (hk : k ≤ n) : ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W SP (D + BitVec.ofNat 64 k) (n - k),
      (⟨D, k⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨D, k⟩ ⟨D, n⟩ := Region.sub_prefix hk
  have hlt := hd.lt
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using Offset.disjoint D (d := 0) (n := k) (e := k) (k := n - k) (.inl (by omega)) (by omega) (by omega)
  · exact (hd.st.sub_left hs).sub_right (Lay.stSub (by decide))
  · exact (hd.w.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hd.stk.sub_right hs).symm

end

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The body of `seal`: the data encrypted from `icb`, and its tag. -/
theorem sealBody_ok {R : Nat} {D : Addr} {n al : Nat} {H icb : Block} {a : List Byte} {s : State}
    (h : ObPre Ctx W SP R D n s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hcb : blockAt s.mem (cbA W) = icb) (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (habs : Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length))) :
    WP isa (.seq (.seq (oneBlocks v.callees.enc) (oneCrypt v.callees)) (oneTag v.callees 0)) s fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (oneFrameB W D SP n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al n)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16))) := by
  have hD := h.data.ok.w
  have hlt := h.data.ok.lt
  have hR := h.rounds.2
  have hxa : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine WP.seq (WP.seq (WP.mono (oneBlocksE_ok L v h) fun s₃ ⟨P, o₁, o₂, o₃⟩ => ?_))
  obtain ⟨f₃, hR₃, hH₃, hc₃, hJ₃, hw₃, ct₃, ab₃, ht₃⟩ := ob_facts L h P hH hcb habs hxa o₁ o₂
    (Z := bytesAt s₃.mem D (16 * (n / 16))) (by rw [length_bytesAt]; omega)
    (by rw [o₃, show (Ctx + 240 : Addr) = Ctx + BitVec.ofNat 64 240 from rfl, hH, Proof.Gcm.blocksAt_eq])
  have hP : 16 * (n / 16) % 16 = 0 := by omega
  have hdw : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₃ (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    (h.data.of_eq P.rd P.wr).drop (by omega)
  have hlen₃ : s₃.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16)) := by
    rw [P.len]; congr 1; omega
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [f₃.readW (r := ⟨W + BitVec.ofNat 64 184, 8⟩) (Region.contains_self _ _)
      (kept_oneFrameB L hD h.t_w (.inl ⟨by decide, by decide⟩)) (by decide), hal]
  refine WP.mono (oneCrypt_ok v L (icb := icb) hP P.env hR₃ P.dat hlen₃ hdw) fun s₄ ⟨co, rd₄, wr₄⟩ => ?_
  have out₄ := co.out ct₃
  have g₄ := crFrame_one co.frame
  have hDW' := hdw.ok.w
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => g₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW' hd)
      (by decide)
  have hH₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame co.frame (fun r hr => (ctx_crFrame L hdw r hr).sub_left (Lay.ctxSub (by decide))), hH₃]
  have abs₄ : Absorbed s₄.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16))) := by
    have hl := Nat.mod_lt (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16))).length
      (show 16 > 0 by decide)
    exact ab₃.congr (blockAt_frame co.frame (st_crFrame L hdw.ok (d := 16) (k := 16) (by decide)))
      (bytesAt_frame co.frame (st_crFrame L hdw.ok (d := 32) (by omega)) (by omega))
  have hX : (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16))).length % 16 = 0 := by
    rw [List.length_append, length_bytesAt]; omega
  refine WP.mono (oneTag_ok v L (o := 0) (al := al) (.inl rfl) hX co.env hH₄ co.rounds
    (by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact P.dat)
    (by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact hlen₃)
    (by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact P.tlen) hlt
    (by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact hal₃) (hdw.ok.of_eq rd₄ wr₄) hDW' hdw.ctx)
    fun s₅ ⟨he₅, f₅, rd₅, wr₅, _, _, hq⟩ => ?_
  have T := hq abs₄
  have split : ∀ m : Mem, bytesAt m D n =
      bytesAt m D (16 * (n / 16)) ++ bytesAt m (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    fun m => by rw [← bytesAt_add, Nat.add_sub_cancel' (by omega)]
  have dDw : ∀ r ∈ (⟨W + BitVec.ofNat 64 0, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact h.data.ok.stk.symm
  have hd₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n := bytesAt_frame f₅ dDw (by omega)
  have hp₄ : bytesAt s₄.mem D (16 * (n / 16)) = bytesAt s₃.mem D (16 * (n / 16)) :=
    bytesAt_frame co.frame (pre_crFrame (h.data.ok.of_eq P.rd P.wr) (by omega)) (by omega)
  have hc₄ : ciphOf s₄.mem Ctx R = ciphOf s.mem Ctx R := by rw [ciph_frame co.frame (ctx_crFrame L hdw) hR, hc₃]
  have hJ₄ : blockAt s₄.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) := by
    rw [← hJ₃]; simpa using blockAt_frame co.frame (st_crFrame L hdw.ok (d := 0) (k := 16) (by decide))
  have hC : bytesAt s₅.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) := by
    rw [hd₅, split, split s.mem, hp₄, out₄, hw₃, hc₃, ht₃, Proof.Gcm.xorKs_append, length_bytesAt, Nat.zero_add]
  have eX : a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16)) ++
      bytesAt s₄.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      a ++ zeros (padLen a.length) ++ bytesAt s₅.mem D n := by
    rw [hd₅, split, hp₄, List.append_assoc]
  rw [eX, padded_eq, hc₄, hJ₄, show W + BitVec.ofNat 64 0 = W from BitVec.add_zero W] at T
  exact ⟨he₅, rd₅.trans (rd₄.trans P.rd), wr₅.trans (wr₄.trans P.wr),
    oneB_trans f₃ (oneB_trans (oneFrame_B (by omega) g₄)
      (oneFrame_B (k := 16 * (n / 16)) (by omega) (wFrame_one (o := 0) (.inl rfl) f₅))), hC, T⟩

end

end VG.Proof.AesGcm.X86_64
