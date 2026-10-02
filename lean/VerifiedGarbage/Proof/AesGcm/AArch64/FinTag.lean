import VerifiedGarbage.Proof.AesGcm.AArch64.Body

/-!
# AES-GCM on AArch64: the tag of a whole message (`finBody`)

Untrusted: everything here is checked by Lean. `finBody o` pads and absorbs
the buffered bytes (of the text, or of the additional data if there is no
text), and writes `GHASH(…, lengths) ⊕ CIPH_K(J₀)` to `W + o`: the tag of the
message (`finBody_ok`, `Proof.Gcm.fullTag_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput zeros padLen ofBytes toBytes)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem lensBlock_mod_left (a c : Nat) : lensBlock (a % 2 ^ 64) c = lensBlock a c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (a % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * a)]
  congr 2; omega

/-- The buffered bytes: of the additional data if there is no text. -/
theorem ghashInput_mod {a c : List Byte} : (ghashInput a c).length % 16 =
    if c.length = 0 then a.length % 16 else c.length % 16 := by
  by_cases hc : c = []
  · subst hc; rfl
  · have hl : c.length ≠ 0 := fun h => hc (List.eq_nil_of_length_eq_zero h)
    rw [Proof.Gcm.ghashInput_of_ne hc, ite_eq_right hl]
    simp only [List.length_append, Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega

/-- The regions `finBody o` writes. -/
abbrev finFrame (St W : Addr) (o : Nat) : List Region := tFrame St W 16 ++ tagFrame St W o

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

omit L in
/-- The offset of the buffered bytes. -/
theorem finOff_ok {s : State} {A P : Nat} (h26 : s.gpr .x26 = BitVec.ofNat 64 A)
    (h27 : s.gpr .x27 = BitVec.ofNat 64 P) (hA : A < 2 ^ 64) (hP : P < 2 ^ 64) :
    WP isa (.ite (.zero .x .x27) (.block [imm .x9 15, .logic .and .x .x25 .x26 .x9])
      (.block [imm .x9 15, .logic .and .x .x25 .x27 .x9])) s fun s' =>
      s'.gpr .x25 = BitVec.ofNat 64 (if P = 0 then A % 16 else P % 16) ∧ Regs [.x9, .x25] s s' := by
  refine WP.ite (decide (P = 0)) (eval_zero h27 hP) (fun ht => ?_) (fun hf => ?_)
  · have h0 : P = 0 := by simpa using ht
    refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h26, BitVec.setWidth_eq, h0]
    rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hA]
  · have h0 : P ≠ 0 := by simpa using hf
    refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h27, BitVec.setWidth_eq, h0]
    rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hP]

/-- `finBody o`: the tag of the message `a`, `c` into `W + o`. -/
theorem finBody_ok (v : GcmImpl) {o : Nat} (ho : o = 0 ∨ o = 112) {k : Reg → BitVec 64} {R : Nat}
    {a c : List Byte} {H : Block} {s : State} (he : Env Ctx St W SP s) (hk : Kept k s)
    (h22 : s.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 a.length) (h27 : s.gpr .x27 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (finBody v.callees o) s fun s' => Env Ctx St W SP s' ∧ Kept k s' ∧
      Frame (finFrame St W o) s.mem s'.mem ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        bytesAt s'.mem (W + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom H (ghash H (blocks (padded a c))) [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem Ctx R (blockAt s.mem St))) := by
  have hA : a.length % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have h26' : s.gpr .x26 = BitVec.ofNat 64 (a.length % 2 ^ 64) := by rw [h26]; apply BitVec.eq_of_toNat_eq; simp
  refine WP.seq (WP.mono (finOff_ok h26' h27 hA hc) fun s₁ ⟨x25₁, r₁⟩ => ?_)
  have he₁ := he.of_regs r₁
  have hk₁ := hk.of_others r₁.others
  have h25 : s₁.gpr .x25 = BitVec.ofNat 64 ((ghashInput a c).length % 16) := by
    rw [x25₁, ghashInput_mod]
    by_cases h0 : c.length = 0
    · rw [ite_eq_left h0, ite_eq_left h0, Nat.mod_mod_of_dvd _ (by decide)]
    · rw [ite_eq_right h0, ite_eq_right h0]
  refine WP.seq (WP.mono (flush_ok L (.inr rfl) v (H := H) (x := ghashInput a c) he₁ hk₁ h25 rfl
    (by rw [r₁.mem]; exact hH)) fun s₂ ⟨h₂, hH₂, abs₂⟩ => ?_)
  have h22₂ : s₂.gpr .x22 = BitVec.ofNat 64 R := by
    rw [h₂.kept .x22 (by decide), ← hk .x22 (by decide), h22]
  refine WP.mono (tag_ok L v ho h₂.env h₂.kept h22₂ hR h₂.x25) fun s₃ h₃ => ⟨h₃.env, h₃.kept, ?_, fun ha => ?_⟩
  · rw [← r₁.mem]
    exact (h₂.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (h₃.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  · have f₂ := h₂.frame
    rw [r₁.mem] at f₂ abs₂
    have hacc := Proof.Gcm.Absorbed.whole_eq (abs₂ ha) (Proof.Gcm.length_padded a c)
    rw [h₃.out, hH₂, hacc]
    have h26₂ : (s₂.gpr .x26).toNat = a.length % 2 ^ 64 := by
      rw [h₂.kept .x26 (by decide), ← hk .x26 (by decide), h26', toNat_ofNat_of_lt hA]
    have h27₂ : (s₂.gpr .x27).toNat = c.length := by
      rw [h₂.kept .x27 (by decide), ← hk .x27 (by decide), h27, toNat_ofNat_of_lt hc]
    rw [h26₂, h27₂, lensBlock_mod_left, ciph_frame f₂ (ctx_tFrame' L) hR,
      blockAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact st0_disj L (by decide) (by decide)
        · exact st0_w L ⟨by decide, by decide⟩
        · exact st0_w L ⟨by decide, by decide⟩)]
    rfl

theorem saved_finFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ finFrame St W o, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact saved_tFrame L (.inr rfl) r hr
  · exact saved_tagFrame L ho r hr


end

end VG.Proof.AesGcm.AArch64
