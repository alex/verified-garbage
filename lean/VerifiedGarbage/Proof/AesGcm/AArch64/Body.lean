import VerifiedGarbage.Proof.AesGcm.AArch64.Text
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-!
# AES-GCM on AArch64: the bodies of `encrypt` and `decrypt`

Untrusted: everything here is checked by Lean. With the additional data `a`
and the ciphertext `c` so far, of `P` bytes, and `n` bytes at `D`: the
additional data padded if this is the first text (`fo`, `flush`), then the
data encrypted and the ciphertext absorbed (`encBody_ok`), or the data
absorbed and decrypted (`decBody_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- Code never changes the permissions or the stack pointer. -/
theorem WP.with_rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', e, q⟩ := h; exact ⟨t, s', e, q, (Exec.rdwr e).1, (Exec.rdwr e).2.1⟩

theorem WP.seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨t, s', e, q⟩ := h
  cases e with
  | seq e₁ e₂ => cases e₁ with
    | seq ea eb => exact ⟨_, _, .seq ea (.seq eb e₂), q⟩

/-- The regions the bodies write. -/
abbrev bodyFrame (St W D : Addr) (n : Nat) : List Region :=
  tFrame St W 16 ++ crFrame St W D n ++ absFrame St W 16

/-- Before a body. -/
structure BodyIn (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R n P : Nat) (D : Addr) (a c : List Byte)
    (H : Block) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x25 : s.gpr .x25 = BitVec.ofNat 64 (a.length % 16)
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = BitVec.ofNat 64 P
  x28 : s.gpr .x28 = D
  hc : c.length = P
  hP : P < 2 ^ 64
  data : DataW Ctx St W s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- What a body leaves, from `m₀`, where `e` is the data absorbed and `out`
what it leaves at `D`. -/
structure BodyOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R n P : Nat) (D : Addr) (a c : List Byte)
    (H : Block) (icb : Block) (e out : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  frame : Frame (bodyFrame St W D n) m₀ s.mem
  post : Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
    Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a (c ++ e)) ∧
      Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P + n) ∧
      bytesAt s.mem D n = out

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

theorem ctx_tFrame' : ∀ r ∈ tFrame St W 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))

theorem ctx_absFrame' : ∀ r ∈ absFrame St W 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))

theorem acc_tFrame_free : ∀ r ∈ tFrame St W 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact st_st' L (.inr (by decide)) (by decide) (by decide)
  · exact st_wpart L (by decide) ⟨by decide, by decide⟩
  · exact st_wpart L (by decide) ⟨by decide, by decide⟩

theorem ctr_absFrame : ∀ r ∈ absFrame St W 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact st_st' L (.inr (by decide)) (by decide) (by decide)
  · exact st_st' L (.inr (by decide)) (by decide) (by decide)
  · exact st_wpart L (by decide) ⟨by decide, by decide⟩

theorem acc_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W s D n) :
    ∀ r ∈ crFrame St W D n, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.st.sub_right (Lay.stSub (by decide))).symm
  · exact st_st' L (.inl (by decide)) (by decide) (by decide)
  · exact st_wpart L (by decide) ⟨by decide, by decide⟩

omit L in
theorem data_tFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W s D n) :
    ∀ r ∈ tFrame St W 16, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.ok.st.sub_right (Lay.stSub (by decide))
  · exact hd.ok.w.sub_right (Lay.wSub (by decide))
  · exact hd.ok.w.sub_right (Lay.wSub (by decide))

theorem hH_tFrame {m m' : Mem} (hf : Frame (tFrame St W 16) m m') :
    blockAt m' (Ctx + BitVec.ofNat 64 240) = blockAt m (Ctx + BitVec.ofNat 64 240) :=
  blockAt_frame hf fun r hr => (ctx_tFrame' L r hr).sub_left (Lay.ctxSub (by decide))

theorem hH_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W s D n) {m m' : Mem}
    (hf : Frame (crFrame St W D n) m m') :
    blockAt m' (Ctx + BitVec.ofNat 64 240) = blockAt m (Ctx + BitVec.ofNat 64 240) :=
  blockAt_frame hf fun r hr => (ctx_crFrame L hd r hr).sub_left (Lay.ctxSub (by decide))

/-- The additional data padded if this is the first text: `fo` and `flush`. -/
theorem pad_ok (v : GcmImpl) {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : BodyIn Ctx St W SP k R n P D a c H s) :
    WP isa (.seq fo (flush v.callees 16)) s fun s' => Env Ctx St W SP s' ∧ Kept k s' ∧
      blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = H ∧ Frame (tFrame St W 16) s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (xf a c n)) := by
  have hn := h.data.ok.lt
  refine WP.seq (WP.mono (fo_ok h.x25 h.x26 h.x27 hn h.hP) fun s₁ ⟨x25₁, r₁⟩ => ?_)
  have he₁ := h.env.of_regs r₁
  have h25 : s₁.gpr .x25 = BitVec.ofNat 64 (if n ≠ 0 ∧ c.length = 0 then a.length % 16 else 0) := by
    rw [x25₁, h.hc]
  refine WP.mono (WP.with_rdwr (flushStep_ok L v he₁ (h.kept.of_others r₁.others) h25
    (by rw [r₁.mem]; exact h.hH))) fun s₂ ⟨⟨he₂, hk₂, hH₂, f₂, abs₂⟩, rd₂, wr₂⟩ =>
    ⟨he₂, hk₂, hH₂, by rw [← r₁.mem]; exact f₂, by rw [rd₂, r₁.rd], by rw [wr₂, r₁.wr],
      fun ha => abs₂ (by rw [r₁.mem]; exact ha)⟩

omit L in
/-- `textArgs`: the offset into the text, and the text as the piece. -/
theorem textArgs_ok {k : Reg → BitVec 64} {n P : Nat} {D : Addr} {s : State} (hk : Kept k s)
    (k26 : k .x26 = BitVec.ofNat 64 n) (k27 : k .x27 = BitVec.ofNat 64 P) (k28 : k .x28 = D) (hP : P < 2 ^ 64) :
    WP isa (.block textArgs) s fun s' => s'.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧ s'.gpr .x23 = D ∧
      s'.gpr .x24 = BitVec.ofNat 64 n ∧ Regs [.x9, .x25, .x23, .x24] s s' := by
  have h26 := (hk .x26 (by decide)).trans k26
  have h27 := (hk .x27 (by decide)).trans k27
  have h28 := (hk .x28 (by decide)).trans k28
  refine WP.run ⟨_, by simp only [textArgs]; arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, by simp [gpr_write, h28], by simp [gpr_write, h26], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h27, BitVec.setWidth_eq]
  rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15,
    toNat_ofNat_of_lt hP]

omit L in
/-- `mov x23, x28; mov x24, x26`. -/
theorem textPiece_ok {k : Reg → BitVec 64} {n : Nat} {D : Addr} {s : State} (hk : Kept k s)
    (k26 : k .x26 = BitVec.ofNat 64 n) (k28 : k .x28 = D) :
    WP isa (.block [mov .x23 .x28, mov .x24 .x26]) s fun s' => s'.gpr .x23 = D ∧
      s'.gpr .x24 = BitVec.ofNat 64 n ∧ Regs [.x23, .x24] s s' := by
  have h26 := (hk .x26 (by decide)).trans k26
  have h28 := (hk .x28 (by decide)).trans k28
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  exact ⟨by simp [gpr_write, h28], by simp [gpr_write, h26], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩

omit L in
theorem mem_bt {St W D : Addr} {n : Nat} {r : Region} (h : r ∈ tFrame St W 16) : r ∈ bodyFrame St W D n :=
  List.mem_append_left _ (List.mem_append_left _ h)

omit L in
theorem mem_bc {St W D : Addr} {n : Nat} {r : Region} (h : r ∈ crFrame St W D n) : r ∈ bodyFrame St W D n :=
  List.mem_append_left _ (List.mem_append_right _ h)

omit L in
theorem mem_ba {St W D : Addr} {n : Nat} {r : Region} (h : r ∈ absFrame St W 16) : r ∈ bodyFrame St W D n :=
  List.mem_append_right _ h

/-- `encBody`: the data encrypted, and the ciphertext absorbed. -/
theorem encBody_ok (v : GcmImpl) {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : BodyIn Ctx St W SP k R n P D a c H s) (icb : Block) :
    WP isa (encBody v.callees) s (BodyOut Ctx St W SP k R n P D a c H icb
      (xorKs (ciphOf s.mem Ctx R) icb P (bytesAt s.mem D n))
      (xorKs (ciphOf s.mem Ctx R) icb P (bytesAt s.mem D n)) s.mem) := by
  have k22 : k .x22 = BitVec.ofNat 64 R := (h.kept .x22 (by decide)).symm.trans h.x22
  have k26 : k .x26 = BitVec.ofNat 64 n := (h.kept .x26 (by decide)).symm.trans h.x26
  have k27 : k .x27 = BitVec.ofNat 64 P := (h.kept .x27 (by decide)).symm.trans h.x27
  have k28 : k .x28 = D := (h.kept .x28 (by decide)).symm.trans h.x28
  have hlt := h.data.ok.lt
  refine WP.seq_assoc (WP.seq (WP.mono (pad_ok L v h) fun s₂ ⟨he₂, hk₂, hH₂, f₂, rd₂, wr₂, abs₂⟩ => ?_))
  refine WP.seq (WP.mono (textArgs_ok hk₂ k26 k27 k28 h.hP) fun s₃ ⟨x25₃, x23₃, x24₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have hd₃ : DataW Ctx St W s₃ D n := h.data.of_eq (by rw [r₃.rd, rd₂]) (by rw [r₃.wr, wr₂])
  have hCr : CrIn Ctx St W SP k R P D n s₃ :=
    ⟨he₃, hk₃, (hk₃ .x22 (by decide)).trans k22, h.rounds, x23₃, x24₃, x25₃, hd₃⟩
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L v (icb := icb) hCr)) fun s₄ ⟨h₄, rd₄, wr₄⟩ => ?_)
  refine WP.seq (WP.mono (textPiece_ok h₄.kept k26 k28) fun s₅ ⟨x23₅, x24₅, r₅⟩ => ?_)
  have he₅ := h₄.env.of_regs r₅
  have hk₅ := h₄.kept.of_others r₅.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have hc₃ : ciphOf s₃.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [m₃]; exact ciph_frame f₂ (ctx_tFrame' L) h.rounds
  have hD₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [m₃]; exact bytesAt_frame f₂ (data_tFrame h.data) (by omega)
  have F₅ : Frame (bodyFrame St W D n) s.mem s₅.mem := by
    rw [r₅.mem]
    exact (f₂.sub fun r hr => ⟨r, mem_bt hr, fun _ h => h⟩).trans
      (by rw [← m₃]; exact h₄.frame.sub fun r hr => ⟨r, mem_bc hr, fun _ h => h⟩)
  have hC₃ : ∀ hctr : Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx R) icb P,
      Ctr s₃.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₃.mem Ctx R) icb P := fun hctr => by
    rw [hc₃, m₃]; exact Ctr.frame f₂ (acc_tFrame_free L) hctr
  have hA₅ : ∀ ha : Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c),
      Absorbed s₅.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (xf a c n) := fun ha => by
    rw [r₅.mem]; exact Absorbed.frame h₄.frame (acc_crFrame L hd₃) (by rw [m₃]; exact abs₂ ha)
  have hO₅ : ∀ hctr : Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx R) icb P,
      bytesAt s₅.mem D n = xorKs (ciphOf s.mem Ctx R) icb P (bytesAt s.mem D n) := fun hctr => by
    rw [r₅.mem, h₄.out (hC₃ hctr), hc₃, hD₃]
  have hK₅ : ∀ hctr : Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx R) icb P,
      Ctr s₅.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx R) icb (P + n) :=
    fun hctr => by rw [r₅.mem, ← hc₃]; exact h₄.ctr (hC₃ hctr)
  have hlen : (xorKs (ciphOf s.mem Ctx R) icb P (bytesAt s.mem D n)).length = n := by
    rw [Proof.Gcm.length_xorKs, length_bytesAt]
  refine WP.ite (decide (n = 0)) (eval_zero ((hk₅ .x26 (by decide)).trans k26) hlt) (fun ht => ?_) (fun hf => ?_)
  · have hn0 : n = 0 := by simpa using ht
    refine WP.block_nil ⟨he₅, hk₅, F₅, fun ha hctr => ⟨?_, hK₅ hctr, hO₅ hctr⟩⟩
    rw [ghashInput_xf, hlen, hn0, show bytesAt s.mem D 0 = [] from rfl, Proof.Gcm.xorKs_nil, List.append_nil]
    have := hA₅ ha
    rw [hn0] at this
    exact this
  · have hn0 : n ≠ 0 := by simpa using hf
    have hA : AbsIn Ctx St W SP k H (xf a c n) D n (P % 16) s₅ :=
      ⟨he₅, hk₅, x23₅, x24₅, by rw [r₅.others _ (by decide), h₄.x25], by rw [xf_len hn0, h.hc],
        h.data.ok.of_eq (by rw [r₅.rd, rd₄, r₃.rd, rd₂]) (by rw [r₅.wr, wr₄, r₃.wr, wr₂]),
        by rw [r₅.mem, hH_crFrame L hd₃ h₄.frame, m₃, hH₂]⟩
    refine WP.mono (absorb_ok L (.inr rfl) v hA) fun s₆ h₆ => ⟨h₆.env, h₆.kept,
      F₅.trans (h₆.frame.sub fun r hr => ⟨r, mem_ba hr, fun _ h => h⟩), fun ha hctr => ⟨?_, ?_, ?_⟩⟩
    · rw [ghashInput_xf, hlen, ← hO₅ hctr]; exact h₆.abs (hA₅ ha)
    · exact Ctr.frame h₆.frame (ctr_absFrame L) (hK₅ hctr)
    · rw [bytesAt_frame h₆.frame (data_absFrame (.inr rfl) hA.data) (by omega), hO₅ hctr]

/-- `decBody`: the data absorbed, and decrypted. -/
theorem decBody_ok (v : GcmImpl) {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : BodyIn Ctx St W SP k R n P D a c H s) (icb : Block) :
    WP isa (decBody v.callees) s (BodyOut Ctx St W SP k R n P D a c H icb (bytesAt s.mem D n)
      (xorKs (ciphOf s.mem Ctx R) icb P (bytesAt s.mem D n)) s.mem) := by
  have k22 : k .x22 = BitVec.ofNat 64 R := (h.kept .x22 (by decide)).symm.trans h.x22
  have k26 : k .x26 = BitVec.ofNat 64 n := (h.kept .x26 (by decide)).symm.trans h.x26
  have k27 : k .x27 = BitVec.ofNat 64 P := (h.kept .x27 (by decide)).symm.trans h.x27
  have k28 : k .x28 = D := (h.kept .x28 (by decide)).symm.trans h.x28
  have hlt := h.data.ok.lt
  refine WP.seq (WP.seq_assoc (WP.seq (WP.mono (pad_ok L v h) fun s₂ ⟨he₂, hk₂, hH₂, f₂, rd₂, wr₂, abs₂⟩ => ?_)))
  refine WP.seq (WP.mono (textArgs_ok hk₂ k26 k27 k28 h.hP) fun s₃ ⟨x25₃, x23₃, x24₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have hD₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [m₃]; exact bytesAt_frame f₂ (data_tFrame h.data) (by omega)
  have hd₃ : DataW Ctx St W s₃ D n := h.data.of_eq (by rw [r₃.rd, rd₂]) (by rw [r₃.wr, wr₂])
  -- After the text is absorbed.
  have mid : WP isa (textAbs v.callees) s₃ fun s₄ => Env Ctx St W SP s₄ ∧ Kept k s₄ ∧
      s₄.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧ Frame (tFrame St W 16 ++ absFrame St W 16) s.mem s₄.mem ∧
      s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s₄.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c ++ bytesAt s.mem D n))) := by
    have F₃ : Frame (tFrame St W 16 ++ absFrame St W 16) s.mem s₃.mem := by
      rw [m₃]; exact f₂.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    refine WP.ite (decide (n = 0)) (eval_zero ((hk₃ .x26 (by decide)).trans k26) hlt) (fun ht => ?_) (fun hf => ?_)
    · have hn0 : n = 0 := by simpa using ht
      refine WP.block_nil ⟨he₃, hk₃, x25₃, F₃, by rw [r₃.rd, rd₂], by rw [r₃.wr, wr₂], fun ha => ?_⟩
      rw [ghashInput_xf, length_bytesAt, hn0, show bytesAt s.mem D 0 = [] from rfl, List.append_nil, m₃]
      have := abs₂ ha
      rw [hn0] at this
      exact this
    · have hn0 : n ≠ 0 := by simpa using hf
      have hA : AbsIn Ctx St W SP k H (xf a c n) D n (P % 16) s₃ :=
        ⟨he₃, hk₃, x23₃, x24₃, x25₃, by rw [xf_len hn0, h.hc], hd₃.ok, by rw [m₃, hH₂]⟩
      refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) v hA)) fun s₄ ⟨h₄, rd₄, wr₄⟩ =>
        ⟨h₄.env, h₄.kept, h₄.x25,
          F₃.trans (h₄.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩),
          by rw [rd₄, r₃.rd, rd₂], by rw [wr₄, r₃.wr, wr₂], fun ha => ?_⟩
      rw [ghashInput_xf, length_bytesAt, ← hD₃]
      exact h₄.abs (by rw [m₃]; exact abs₂ ha)
  refine WP.mono mid fun s₄ ⟨he₄, hk₄, x25₄, F₄, rd₄, wr₄, abs₄⟩ => ?_
  refine WP.seq (WP.mono (textPiece_ok hk₄ k26 k28) fun s₅ ⟨x23₅, x24₅, r₅⟩ => ?_)
  have he₅ := he₄.of_regs r₅
  have hk₅ := hk₄.of_others r₅.others
  have hd₅ : DataW Ctx St W s₅ D n := h.data.of_eq (by rw [r₅.rd, rd₄]) (by rw [r₅.wr, wr₄])
  have hCr : CrIn Ctx St W SP k R P D n s₅ :=
    ⟨he₅, hk₅, (hk₅ .x22 (by decide)).trans k22, h.rounds, x23₅, x24₅,
      by rw [r₅.others _ (by decide), x25₄], hd₅⟩
  have ctxF : ∀ r ∈ tFrame St W 16 ++ absFrame St W 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ctx_tFrame' L r hr
    · exact ctx_absFrame' L r hr
  have hc₅ : ciphOf s₅.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [r₅.mem]; exact ciph_frame F₄ ctxF h.rounds
  have hD₅ : bytesAt s₅.mem D n = bytesAt s.mem D n := by
    rw [r₅.mem]
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega)
    rcases List.mem_append.mp hr with hr | hr
    · exact data_tFrame h.data r hr
    · exact data_absFrame (.inr rfl) h.data.ok r hr
  refine WP.mono (crypt_ok L v (icb := icb) hCr) fun s₆ h₆ => ⟨h₆.env, h₆.kept, ?_, fun ha hctr => ⟨?_, ?_, ?_⟩⟩
  · rw [r₅.mem] at h₆
    exact (F₄.sub fun r hr => ⟨r, by
      rcases List.mem_append.mp hr with hr | hr
      · exact mem_bt hr
      · exact mem_ba hr, fun _ h => h⟩).trans (h₆.frame.sub fun r hr => ⟨r, mem_bc hr, fun _ h => h⟩)
  · rw [r₅.mem] at h₆
    exact Absorbed.frame h₆.frame (acc_crFrame L hd₅) (abs₄ ha)
  · have hC : Ctr s₅.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₅.mem Ctx R) icb P := by
      rw [hc₅, r₅.mem]
      refine Ctr.frame F₄ (fun r hr => ?_) hctr
      rcases List.mem_append.mp hr with hr | hr
      · exact acc_tFrame_free L r hr
      · exact ctr_absFrame L r hr
    have := h₆.ctr hC
    rw [hc₅] at this
    exact this
  · have hC : Ctr s₅.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₅.mem Ctx R) icb P := by
      rw [hc₅, r₅.mem]
      refine Ctr.frame F₄ (fun r hr => ?_) hctr
      rcases List.mem_append.mp hr with hr | hr
      · exact acc_tFrame_free L r hr
      · exact ctr_absFrame L r hr
    rw [h₆.out hC, hc₅, hD₅]

end

end VG.Proof.AesGcm.AArch64
