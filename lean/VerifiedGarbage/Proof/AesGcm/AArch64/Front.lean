import VerifiedGarbage.Proof.AesGcm.AArch64.OneEntry

/-!
# AES-GCM on AArch64: `J₀` and the additional data of `seal` and `open`

Untrusted: everything here is checked by Lean. After the entry, `j0` starts
the state at `W + 16` for the nonce, `oneAad` absorbs the additional data and
`encPrep` sets up the text's arguments from the slots the entry wrote
(`front_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt inc32)
open VG.Proof.Gcm (Absorbed)

/-- The regions `j0` and `oneAad` write. -/
abbrev frontFrame (St W : Addr) : List Region := j0Frame St W ++ absFrame St W 16

/-- The slots stay where they are, outside a frame apart from them. -/
theorem slot_kept {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {W : Addr}
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r) {d : Nat} (h₁ : 216 ≤ d)
    (h₂ : d + 8 ≤ 256) : m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub _ h₁ (by omega))) (by decide)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

theorem slots_j0Frame : ∀ r ∈ j0Frame St W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (d := 216) (k := 40) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem slots_absFrame : ∀ r ∈ absFrame St W 16, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem slots_frontFrame : ∀ r ∈ frontFrame St W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact slots_j0Frame L r hr
  · exact slots_absFrame L r hr

theorem saved_frontFrame : ∀ r ∈ frontFrame St W, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact saved_j0Frame L r hr
  · exact saved_absFrame L (.inr rfl) r hr

/-- After `encPrep`, from `s₀`. -/
structure Front (Ctx St W SP : Addr) (H : Block) (iv a : List Byte) (D : Addr) (n : Nat) (s₀ : State)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  x22 : s.gpr .x22 = s₀.gpr .x22
  x25 : s.gpr .x25 = BitVec.ofNat 64 (a.length % 16)
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = 0
  x28 : s.gpr .x28 = D
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  abs : Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H a
  frame : Frame (frontFrame St W) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `j0`, `oneAad` and `encPrep`. -/
theorem front_ok (v : GcmImpl) {s₀ : State} {k : Reg → BitVec 64} {H : Block} {Np A D : Addr} {nl al n : Nat}
    (he : Env Ctx St W SP s₀) (hk : Kept k s₀) (h23 : s₀.gpr .x23 = Np) (h24 : s₀.gpr .x24 = BitVec.ofNat 64 nl)
    (h26 : s₀.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s₀.gpr .x27 = 0)
    (hnon : DataOk St W s₀ Np nl) (haad : DataOk St W s₀ A al)
    (hH : blockAt s₀.mem (Ctx + BitVec.ofNat 64 240) = H)
    (sA : s₀.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s₀.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s₀.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s₀.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    {rest : Prog isa} {Q : State → Prop}
    (hr : ∀ s', Front Ctx St W SP H (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) D n s₀ s' → WP isa rest s' Q) :
    WP isa (.seq (j0 v.callees) (.seq (oneAad v.callees) (.seq (.block encPrep) rest))) s₀ Q := by
  have hlt := haad.lt
  refine WP.seq (WP.mono (WP.with_rdwr (j0_ok L v ⟨he, hk, h23, h24, h26, h27, hnon, hH⟩))
    fun s₁ ⟨h₁, rd₁, wr₁⟩ => ?_)
  have r₁ (d : Nat) (h : d + 8 ≤ 2560) := h₁.env.perm.wR h
  obtain ⟨s₂, run₂, x23₂, x24₂, x25₂, r₂⟩ : ∃ s₂, runBlock isa [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO,
      imm .x25 0] s₁ = some s₂ ∧ s₂.gpr .x23 = A ∧ s₂.gpr .x24 = BitVec.ofNat 64 al ∧
      s₂.gpr .x25 = BitVec.ofNat 64 0 ∧ Regs [.x23, .x24, .x25] s₁ s₂ := by
    have e₁ := slot_kept h₁.frame (slots_j0Frame L) (d := 216) (by decide) (by decide)
    have e₂ := slot_kept h₁.frame (slots_j0Frame L) (d := 224) (by decide) (by decide)
    rw [sA] at e₁
    rw [sL] at e₂
    have q₁ := r₁ 216 (by decide)
    have q₂ := r₁ 224 (by decide)
    refine ⟨_, by arun [h₁.env.x19, q₁, q₂], ?_⟩
    refine ⟨?_, ?_, by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← e₁]; rfl
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← e₂]; rfl
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩))
  have he₂ := h₁.env.of_regs r₂
  have hk₂ := h₁.kept.of_others r₂.others
  have hd₂ : DataOk St W s₂ A al := haad.of_eq (by rw [r₂.rd, rd₁]) (by rw [r₂.wr, wr₁])
  have hIn : AbsIn Ctx St W SP k H [] A al 0 s₂ :=
    ⟨he₂, hk₂, x23₂, x24₂, x25₂, rfl, hd₂, by rw [r₂.mem]; exact h₁.hH⟩
  refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) v hIn)) fun s₃ ⟨h₃, rd₃, wr₃⟩ => ?_
  have f₃ : Frame (frontFrame St W) s₀.mem s₃.mem :=
    (h₁.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (by rw [← r₂.mem]; exact h₃.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  have q (d : Nat) (h : d + 8 ≤ 2560) := h₃.env.perm.wR h
  obtain ⟨s₄, run₄, x25₄, x26₄, x27₄, x28₄, r₄⟩ : ∃ s₄, runBlock isa encPrep s₃ = some s₄ ∧
      s₄.gpr .x25 = BitVec.ofNat 64 (al % 16) ∧ s₄.gpr .x26 = BitVec.ofNat 64 n ∧ s₄.gpr .x27 = 0 ∧
      s₄.gpr .x28 = D ∧ Regs [.x9, .x10, .x25, .x26, .x27, .x28] s₃ s₄ := by
    have e₂ := slot_kept f₃ (slots_frontFrame L) (d := 224) (by decide) (by decide)
    have e₃ := slot_kept f₃ (slots_frontFrame L) (d := 232) (by decide) (by decide)
    have e₄ := slot_kept f₃ (slots_frontFrame L) (d := 240) (by decide) (by decide)
    rw [sL] at e₂
    rw [sD] at e₃
    rw [sN] at e₄
    have q₂ := q 224 (by decide)
    have q₃ := q 232 (by decide)
    have q₄ := q 240 (by decide)
    refine ⟨_, by simp only [encPrep]; arun [h₃.env.x19, q₂, q₃, q₄], ?_⟩
    refine ⟨?_, ?_, by simp [gpr_write], ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      rw [show s₃.mem.read (W + 224#64) 8 = s₃.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, e₂,
        show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hlt]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      rw [show s₃.mem.read (W + 240#64) 8 = s₃.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, e₄]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      rw [show s₃.mem.read (W + 232#64) 8 = s₃.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, e₃]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, hr s₄ ⟨h₃.env.of_regs r₄, ?_, ?_, x26₄, x27₄, x28₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩)
  · rw [r₄.others _ (by decide), h₃.kept .x22 (by decide), ← hk .x22 (by decide)]
  · rw [x25₄, length_bytesAt]
  · rw [r₄.mem, blockAt_frame h₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st0_disj L (by decide) (by decide)
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩), r₂.mem, h₁.j0]
  · rw [r₄.mem, blockAt_frame h₃.frame (ctx_absFrame L (.inr rfl)), r₂.mem, h₁.hH]
  · rw [r₄.mem, blockAt_frame h₃.frame (fun r hr => (ctr_absFrame L r hr).sub_left
      (Region.sub_prefix (by decide))), r₂.mem, h₁.cb]
  · rw [r₄.mem]
    have := h₃.abs (Proof.Gcm.absorbed_nil H (by rw [r₂.mem]; exact h₁.y))
    rw [List.nil_append, r₂.mem, bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact haad.st
      · exact haad.w.sub_right (Lay.wSub (by decide))
      · exact haad.w.sub_right (Lay.wSub (by decide))) (by omega)] at this
    exact this
  · rw [r₄.mem]; exact f₃
  · rw [r₄.rd, rd₃, r₂.rd, rd₁]
  · rw [r₄.wr, wr₃, r₂.wr, wr₁]

end

end VG.Proof.AesGcm.AArch64
