import VerifiedGarbage.Proof.AesGcm.Arm.Absorb
import VerifiedGarbage.Proof.AesGcm.Arm.Words

/-!
# AES-GCM on ARMv7: padding the buffer (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. `flush yo` pads the `r6`
buffered bytes with zeros in `T` and absorbs them (`flush_ok`); `lens yo`
stores the lengths block of `r5:r4` and `r7:r6` bytes in `T` and absorbs it
(`lens_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghash blocks zeros padLen)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

/-- The regions `flush` and `lens` write. -/
abbrev tFrame (st w sp : BitVec 32) (yo : Nat) : List Region :=
  [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]

theorem gh_tFrame {st w sp : BitVec 32} {yo : Nat} {m m' : Mem}
    (h : Frame [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp] m m') :
    Frame (tFrame st w sp yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

theorem store4_zero_bytes (m : Mem) (p : Addr) : bytesAt (store4 m p 0 0 0 0) p 16 = zeros 16 := by
  rw [Cmac.bytesAt_store4, Cmac.le4_zero]; rfl

/-- The four words at `p`, as the code stores them at `b + o`, `b + o + 4`, … -/
theorem store4_eq (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ : BitVec 32) :
    store4 m p w₀ w₁ w₂ w₃ = (((m.writeW p w₀).writeW (p + BitVec.ofNat 64 4) w₁).writeW (p + BitVec.ofNat 64 8)
      w₂).writeW (p + BitVec.ofNat 64 12) w₃ := rfl

/-- Before `flush yo` (or `lens yo`): GHASH has absorbed `x`. -/
structure FlIn (c st w sp k7 k8 : BitVec 32) (H : Block) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H

/-- After `flush yo`: GHASH has absorbed `x`, from `m₀`. -/
structure FlOut (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x
  frame : Frame (tFrame st w sp yo) m₀ s.mem

/-- After the copy of the buffered bytes to `T`, padded with zeros. -/
structure FlMid (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (o : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  hT : bytesAt s.mem (State.addr w + BitVec.ofNat 64 96) 16 =
    bytesAt m₀ (State.addr st + BitVec.ofNat 64 32) o ++ zeros (16 - o)
  hY : blockAt s.mem (State.addr st + BitVec.ofNat 64 yo) = blockAt m₀ (State.addr st + BitVec.ofNat 64 yo)
  frame : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem ctx_tFrame : ∀ r ∈ tFrame st w sp yo, (⟨State.addr c + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

/-- The `o` buffered bytes copied to `T`, padded with zeros. -/
theorem flushCopy_ok {H : Block} {o : Nat} {s : State} (h : FlIn c st w sp k7 k8 H s)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 o) (ho : o < 16) (h0 : o ≠ 0) :
    WP isa (.seq (.block flushPre) copyLoop) s (FlMid c st w sp k7 k8 yo H o s.mem) := by
  have he := h.env
  have h10 := he.r10; have h11 := he.r11
  have w₀ := he.perm.wW (show 96 + 4 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 100 + 4 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 104 + 4 ≤ 2560 by decide)
  have w₃ := he.perm.wW (show 108 + 4 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hm₂, h1, h2, h3, hg₂, hk₂⟩ : ∃ s₂, runBlock isa flushPre s = some s₂ ∧
      s₂.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 96) 0 0 0 0 ∧
      s₂.gpr .r1 = st + BitVec.ofNat 32 32 ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 96 ∧
      s₂.gpr .r3 = BitVec.ofNat 32 o ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.sp = s.sp := by
    refine ⟨_, by simp only [flushPre]; arun [h10, h11, L.wA, L.stA, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, store4_eq, add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h10]
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, h6]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have eS := L.stA (d := 32) (by decide)
  have eT := L.wA (d := 96) (by decide)
  have lp : LoopPre s₂ (st + BitVec.ofNat 32 32) (w + BitVec.ofNat 32 96) o := by
    refine ⟨h1, h2, h3, by omega, by omega, by rw [L.stN (by decide)]; have := L.sw; omega,
      by rw [L.wN (by decide)]; have := L.ww; omega, ?_, ?_, ?_⟩
    · rw [hk₂.1, hk₂.2.1, eS]; exact covers_left (he.perm.stC (by omega))
    · rw [hk₂.2.1, eT]; exact he.perm.wC (by omega)
    · rw [eS, eT]; exact L.st_w (by omega) (.inr ⟨by decide, by omega⟩)
  refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [eS, eT] at hm₃
  -- The memory so far.
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hB₂ : bytesAt s₂.mem (State.addr st + BitVec.ofNat 64 32) o = bytesAt s.mem (State.addr st + BitVec.ofNat 64 32) o :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩))
      (by omega)
  have hlen := length_bytesAt s₂.mem (State.addr st + BitVec.ofNat 64 32) o
  have fc : Frame [⟨State.addr w + BitVec.ofNat 64 96, o⟩] s₂.mem s₃.mem := by
    rw [hm₃]; exact writeBytes_frame' _ hlen
  have f₃ : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] s.mem s₃.mem :=
    fz.trans (fc.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hg₂ _ (by decide) (by decide) (by decide) (by decide)])
      (lo.sp.trans hk₂.2.2) (lo.rd.trans hk₂.1) (lo.wr.trans hk₂.2.1), ?_, ?_, ?_, f₃⟩
  · rw [blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), h.hH]
  · rw [hm₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by decide), hlen, hB₂]
    congr 1
    have := store4_zero_bytes s.mem (State.addr w + BitVec.ofNat 64 96)
    rw [← hm₂, show (16 : Nat) = o + (16 - o) by omega, bytesAt_add] at this
    have e := congrArg (List.drop o) this
    rw [List.drop_left' (length_bytesAt _ _ _)] at e
    rw [e, show o + (16 - o) = 16 by omega, Spec.Gcm.zeros, List.drop_replicate]
    rfl
  · exact blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)

/-- The padded buffer absorbed. -/
theorem flushGh_ok {H : Block} {x : List Byte} {m₀ : Mem} {s : State}
    (h : FlMid c st w sp k7 k8 yo H (x.length % 16) m₀ s) (h0 : x.length % 16 ≠ 0) :
    WP isa (ghash1 yo .r11 tO) s (FlOut c st w sp k7 k8 yo H x (x ++ zeros (padLen x.length)) m₀) := by
  have he := h.env
  have eT := L.wA (d := 96) (by decide)
  refine WP.mono (ghash1_ok L hyo he .r11 96 (.inr rfl) (by decide) (P := w + BitVec.ofNat 32 96)
    (by rw [he.r11]) (by rw [L.wN (by decide)]; have := L.ww; omega) ?_ ?_ ?_ ?_) fun s₄ g => ?_
  · rw [eT]; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · rw [eT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [eT]; exact L.stk_w (by decide)
  · rw [eT]; exact covers_left (he.perm.wC (by decide))
  refine ⟨g.env he, ?_, ?_, ?_⟩
  · rw [blockAt_frame g.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.ctx_st (by decide) (by omega)
      · exact L.ctx_w (by decide) (by decide)
      · exact (L.stk_ctx (by decide)).symm), h.hH]
  · intro ha
    refine Proof.Gcm.absorb_pad ha h0 (B := bytesAt s.mem (State.addr w + BitVec.ofNat 64 96) 16) h.hT ?_
    rw [g.out, h.hY, h.hH, eT]; rfl
  · refine (h.frame.sub fun r hr => ?_).trans (gh_tFrame g.frame)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-- `flush yo`. -/
theorem flush_ok {H : Block} {x : List Byte} {s : State} (h : FlIn c st w sp k7 k8 H s)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 (x.length % 16)) :
    WP isa (flush yo) s (FlOut c st w sp k7 k8 yo H x (x ++ zeros (padLen x.length)) s.mem) := by
  have he := h.env
  have hlt := Nat.mod_lt x.length (show 16 > 0 by decide)
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r6 h6 (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁
  refine WP.ite (decide (x.length % 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : x.length % 16 = 0 := by simpa using ht
    rw [Proof.Gcm.padLen_of_mod h0]
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact h.hH, fun ha => by rw [hm₁]; simpa [zeros] using ha,
      by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : x.length % 16 ≠ 0 := by simpa using hf
    rw [← hm₁]
    refine WP.seq (WP.mono (flushCopy_ok L hyo (o := x.length % 16) ⟨he₁, by rw [hm₁]; exact h.hH⟩
      (by rw [hg₁]; exact h6) hlt h0) fun s₃ hm => flushGh_ok L hyo hm h0)

end

/-- `[8 (hi:lo)]₆₄` into `W + o`, as two byte-reversed words. -/
theorem be64Store_ok {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {s : State} (he : Env c st w sp k7 k8 s)
    (lo hi : Reg) (hlo : lo ≠ .r0) (o : Nat) (ho : o + 8 ≤ 2560) :
    ∃ s', runBlock isa (be64Store lo hi o) s = some s' ∧
      s'.mem = (s.mem.writeW (State.addr w + BitVec.ofNat 64 o) (byteRev32 ((s.gpr hi <<< 3) ||| (s.gpr lo >>> 29)))).writeW
        (State.addr w + BitVec.ofNat 64 o + BitVec.ofNat 64 4) (byteRev32 (s.gpr lo <<< 3)) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have w₀ := he.perm.wW (show o + 4 ≤ 2560 by omega)
  have w₁ := he.perm.wW (show o + 4 + 4 ≤ 2560 by omega)
  have e₁ := L.wA (d := o) (by omega)
  have e₂ := L.wA (d := o + 4) (by omega)
  have o₁ : o < 4096 := by omega
  have o₂ : o + 4 < 4096 := by omega
  refine ⟨_, by simp only [be64Store]; arun [h11, e₁, e₂, w₀, w₁, hlo, o₁, o₂], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, hlo, add_ofNat_assoc, rev_eq]
  · intro r a; simp [gpr_setReg, a]
  all_goals rfl

/-- `[8 (r5:r4)]₆₄ ‖ [8 (r7:r6)]₆₄`, the lengths block, stored in `T`. -/
theorem lensStore_ok {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {s : State} (he : Env c st w sp k7 k8 s) :
    WP isa (.block (be64Store .r4 .r5 tO ++ be64Store .r6 .r7 (tO + 8))) s fun s' =>
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 96)
        (byteRev32 ((s.gpr .r5 <<< 3) ||| (s.gpr .r4 >>> 29))) (byteRev32 (s.gpr .r4 <<< 3))
        (byteRev32 ((s.gpr .r7 <<< 3) ||| (s.gpr .r6 >>> 29))) (byteRev32 (s.gpr .r6 <<< 3)) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, run₁, hm₁, hg₁, hrd₁, hwr₁, hsp₁⟩ := be64Store_ok L he .r4 .r5 (by decide) tO (by decide)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hsp₁ hrd₁ hwr₁
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂, hsp₂⟩ := be64Store_ok L he₁ .r6 .r7 (by decide) (tO + 8)
    (by decide)
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  refine ⟨?_, fun r hr => by rw [hg₂ r hr, hg₁ r hr], hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁⟩
  rw [hm₂, hm₁, hg₁ .r6 (by decide), hg₁ .r7 (by decide)]
  simp only [store4_eq, tO, add_ofNat_assoc]

theorem lensBlock_eq (a₀ a₁ c₀ c₁ : BitVec 32) :
    le4 (byteRev32 ((a₁ <<< 3) ||| (a₀ >>> 29))) ++ le4 (byteRev32 (a₀ <<< 3)) ++
        le4 (byteRev32 ((c₁ <<< 3) ||| (c₀ >>> 29))) ++ le4 (byteRev32 (c₀ <<< 3)) =
      lensBlock (a₁ ++ a₀).toNat (c₁ ++ c₀).toNat := by
  rw [Cmac.le4_rev4, toBytes_append4, shl3_words, shl3_words, shl3_toNat, shl3_toNat, Proof.Gcm.be64_mod,
    Proof.Gcm.be64_mod]
  rfl

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- The lengths block of `r5:r4` and `r7:r6` bytes, absorbed. -/
theorem lens_ok {H : Block} {s : State} (he : Env c st w sp k7 k8 s)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H) :
    WP isa (lens yo) s fun s' => Env c st w sp k7 k8 s' ∧
      blockAt s'.mem (State.addr c + BitVec.ofNat 64 240) = H ∧
      blockAt s'.mem (State.addr st + BitVec.ofNat 64 yo) = ghashFrom H (blockAt s.mem (State.addr st + BitVec.ofNat 64 yo))
        [Spec.Gcm.ofBytes (lensBlock (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat)] ∧
      Frame (tFrame st w sp yo) s.mem s'.mem := by
  refine WP.seq (WP.mono (lensStore_ok L he) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂, hsp₂⟩ => ?_)
  have he₂ : Env c st w sp k7 k8 s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hsp₂ hrd₂ hwr₂
  have fT : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hT : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 96) 16 =
      lensBlock (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat := by
    rw [hm₂, Cmac.bytesAt_store4, lensBlock_eq]
  have hY₂ : blockAt s₂.mem (State.addr st + BitVec.ofNat 64 yo) = blockAt s.mem (State.addr st + BitVec.ofNat 64 yo) :=
    blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  have hH₂ : blockAt s₂.mem (State.addr c + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), hH]
  have eT := L.wA (d := 96) (by decide)
  refine WP.mono (ghash1_ok L hyo he₂ .r11 96 (.inr rfl) (by decide) (P := w + BitVec.ofNat 32 96)
    (by rw [he₂.r11]) (by rw [L.wN (by decide)]; have := L.ww; omega) ?_ ?_ ?_ ?_) fun s₃ g => ?_
  · rw [eT]; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · rw [eT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [eT]; exact L.stk_w (by decide)
  · rw [eT]; exact covers_left (he₂.perm.wC (by decide))
  refine ⟨g.env he₂, ?_, ?_, ?_⟩
  · rw [blockAt_frame g.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.ctx_st (by decide) (by omega)
      · exact L.ctx_w (by decide) (by decide)
      · exact (L.stk_ctx (by decide)).symm), hH₂]
  · have hb : blockAt s₂.mem (State.addr w + BitVec.ofNat 64 96) =
        Spec.Gcm.ofBytes (lensBlock (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat) := by
      rw [blockAt, hT]
    rw [g.out, hY₂, hH₂, eT, hb]
  · refine (fT.sub fun r hr => ?_).trans (gh_tFrame g.frame)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

end

end VG.Proof.AesGcm.Arm
