import VerifiedGarbage.Proof.AesGcm.AArch64.Fn

/-!
# AES-GCM on AArch64: the additional data padded before the first text

Untrusted: everything here is checked by Lean. `fo` leaves the number of
buffered bytes of additional data in `x25` if this is the first text (and
there is text), and 0 otherwise (`fo_ok`); `flush` then pads and absorbs
them, or changes nothing GHASH has absorbed (`flushStep_ok`): GHASH has then
absorbed `xf a c n`, which the text continues (`ghashInput_xf`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- What GHASH has absorbed before `n` more bytes of text: the additional data
padded if this is the first text. -/
def xf (a c : List Byte) (n : Nat) : List Byte :=
  if n ≠ 0 ∧ c = [] then a ++ zeros (padLen a.length) else ghashInput a c

theorem xf_len {a c : List Byte} {n : Nat} (hn : n ≠ 0) : (xf a c n).length % 16 = c.length % 16 := by
  unfold xf
  by_cases hc : c = []
  · subst hc
    simp only [ne_eq, hn, not_false_eq_true, true_and, ↓reduceIte, List.length_append, Proof.Gcm.length_zeros,
      List.length_nil]
    exact Proof.Gcm.length_pad_mod _
  · simp only [hc, and_false, ↓reduceIte, Proof.Gcm.ghashInput_of_ne hc, List.length_append,
      Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega

theorem ghashInput_xf (a c e : List Byte) : ghashInput a (c ++ e) = xf a c e.length ++ e := by
  by_cases he : e = []
  · subst he; simp [xf]
  · have hl : e.length ≠ 0 := fun h => he (List.eq_nil_of_length_eq_zero h)
    rw [Proof.Gcm.ghashInput_append _ _ _ he, xf]
    by_cases hc : c = [] <;> simp [hc, hl]

/-- `fo`: the bytes to pad, if this is the first text. -/
theorem fo_ok {s : State} {q n P : Nat} (h25 : s.gpr .x25 = BitVec.ofNat 64 q)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 n) (h27 : s.gpr .x27 = BitVec.ofNat 64 P) (hn : n < 2 ^ 64)
    (hP : P < 2 ^ 64) :
    WP isa fo s fun s' => s'.gpr .x25 = BitVec.ofNat 64 (if n ≠ 0 ∧ P = 0 then q else 0) ∧ Regs [.x25] s s' := by
  refine WP.ite (decide (n = 0)) (eval_zero h26 hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'; exact ⟨by simp [gpr_write, h0], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.ite (decide (P = 0)) (eval_zero h27 hP) (fun ht' => ?_) (fun hf' => ?_)
    · have h1 : P = 0 := by simpa using ht'
      exact WP.block_nil ⟨by simp [h25, h0, h1], Regs.refl _ _⟩
    · have h1 : P ≠ 0 := by simpa using hf'
      exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
        subst hs'; exact ⟨by simp [gpr_write, h1], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `flush` after `fo`: GHASH has absorbed `xf a c n`, where it had absorbed
`ghashInput a c`. -/
theorem flushStep_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {s : State} {a c : List Byte} {n : Nat}
    (he : Env Ctx St W SP s) (hk : Kept k s)
    (h25 : s.gpr .x25 = BitVec.ofNat 64 (if n ≠ 0 ∧ c.length = 0 then a.length % 16 else 0))
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (flush v.callees 16) s fun s' => Env Ctx St W SP s' ∧ Kept k s' ∧
      blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = H ∧ Frame (tFrame St W 16) s.mem s'.mem ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (xf a c n)) := by
  by_cases hf : n ≠ 0 ∧ c.length = 0
  · have hc : c = [] := List.eq_nil_of_length_eq_zero hf.2
    subst hc
    rw [ite_eq_left hf] at h25
    refine WP.mono (flush_ok L (.inr rfl) v (x := a) he hk h25 rfl hH) fun s' ⟨ho, hH', habs⟩ =>
      ⟨ho.env, ho.kept, hH', ho.frame, fun ha => ?_⟩
    rw [xf, ite_eq_left ⟨hf.1, rfl⟩]
    exact habs ha
  · rw [ite_eq_right hf] at h25
    refine WP.mono (flush0_ok L v (.inr rfl) he hk h25) fun s' ho =>
      ⟨ho.env, ho.kept, by rw [blockAt_frame ho.frame (ctx_tFrame L (.inr rfl)), hH], ho.frame, fun ha => ?_⟩
    have hx : xf a c n = ghashInput a c := by
      rw [xf, ite_eq_right]; intro h; exact hf ⟨h.1, by rw [h.2]; rfl⟩
    rw [hx]
    refine ha.congr ho.out ?_
    refine bytesAt_frame ho.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hl : (ghashInput a c).length % 16 < 16 := Nat.mod_lt _ (by decide)
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (.inr (by omega)) (by have := L.sw; omega) (by have := L.sw; omega)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)

end

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.Gcm (Absorbed Ctr)

/-- GHASH's accumulator and buffer stay as they are, outside a frame. -/
theorem Absorbed.frame {m m' : Mem} {St : Addr} {H : Block} {x : List Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r)
    (ha : Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H x) :
    Absorbed m' (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H x := by
  have hl : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
  exact ha.congr (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by omega)))
    (bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by omega))

/-- The counter block and the keystream block stay as they are, outside a frame. -/
theorem Ctr.frame {m m' : Mem} {St : Addr} {ciph : Block → Block} {icb : Block} {n : Nat} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r)
    (hc : Ctr m (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) ciph icb n) :
    Ctr m' (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) ciph icb n :=
  hc.congr (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by omega)))
    (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega)))

/-- `J₀` stays where it is, outside a frame. -/
theorem j0_frame {m m' : Mem} {St : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨St, 16⟩ : Region).Disjoint r) : blockAt m' St = blockAt m St :=
  blockAt_frame hf hd

section
variable {Ctx St W : Addr} (L : Lay Ctx St W)
include L

/-- Parts of the state apart from a part of `W`. -/
theorem st_wpart {d k e j : Nat} (hd : d + k ≤ 80) (he : 96 ≤ e ∧ e + j ≤ 2560) :
    (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
  L.st_w hd (.inr he)

theorem st_st' {d k e j : Nat} (h : d + k ≤ e ∨ e + j ≤ d) (hd : d + k ≤ 80) (he : e + j ≤ 80) :
    (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 e, j⟩ :=
  L.st_st h hd he

theorem st0_disj {e j : Nat} (h : 16 ≤ e) (he : e + j ≤ 80) :
    (⟨St, 16⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 e, j⟩ := by
  simpa using L.st_st (a := 0) (n := 16) (d := e) (k := j) (.inl h) (by decide) he

theorem st0_w {e j : Nat} (he : 96 ≤ e ∧ e + j ≤ 2560) :
    (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ := by
  simpa using L.st_w (a := 0) (n := 16) (d := e) (k := j) (by decide) (.inr he)

theorem st0_saved : (⟨St, 16⟩ : Region).Disjoint (savedR W) := st0_w L ⟨by decide, by decide⟩

end

end VG.Proof.AesGcm.AArch64
