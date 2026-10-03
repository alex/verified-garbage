import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `open`

The chunks decrypt the data's whole chunks and absorb them as they were;
the rest is absorbed, then decrypted by `vg_chacha20_xor`.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

/-- The data after the chunks is as it was. -/
theorem rest_orig {s₀ s u : State} {key msg : List Byte} {T : Nat}
    (hc : Crypted false s₀ s key msg T u) :
    bytesAt u.mem (dp s₀ + BitVec.ofNat 64 (pre false T)) (L s₀ - pre false T) =
      bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (pre false T)) (L s₀ - pre false T) := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  have e : dp s₀ + BitVec.ofNat 64 (pre false T) + BitVec.ofNat 64 i =
      dp s₀ + BitVec.ofNat 64 (512 * T + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
  have hle := hc.le
  have hi' : i < L s₀ - 512 * T := hi
  rw [e, hc.data _ (by omega), ite_eq_right (by omega)]

theorem openStitched_correct (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre s₀) :
    WP isa (openStitched v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ openAArch64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x4).isLt)
  unfold openStitched cryptRest
  refine WP.seq (WP.mono (WP.preservedV (prologue_ok hp)) fun s₁ ⟨h₁, v₁⟩ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x2).isLt)
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcA hp) h₁.inv.x21 h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  have i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  have R₃ := Repr.frame k₃.frame (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  refine WP.seq ((cryptStitched_ok false hp i₃ st₃ R₃).mono fun s₄ ⟨T, hc⟩ => ?_)
  have hle := hc.le
  have hpre : pre false T = 512 * T := rfl
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
    (srcAt hp (p := pre false T) (by omega)) hc.inv.x21 hc.inv.rd hc.inv.wr hc.x22 hc.x23))
    fun s₅ ⟨⟨k₅, r₅⟩, v₅⟩ => ?_)
  have i₅ := mac_inv0 hc.inv k₅
  have hd₅ : ∀ r ∈ macR s₀, (dR s₀).Disjoint r := by
    intro r hr; simp only [macR, List.mem_singleton] at hr; subst hr
    exact hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))
  refine WP.seq (WP.seq ((restArgs_ok i₅.x21).mono fun w ⟨⟨a0, a1, a2, a3, kw⟩, vw⟩ => ?_))
  have mw := kw.mem_eq
  refine (rest_call v hp (s := s₃) hle a0
    (by rw [a1, k₅.cs _ (pres .x22) (pres30 .x22), hc.x22, hpre])
    (by rw [a2, k₅.cs _ (pres .x23) (pres30 .x23), hc.x23, hpre]) a3 (by rw [kw.wr, i₅.wr])
    (by rw [mw, stateAt_frame k₅.frame (by rdisj_all), hc.cnt])
    (fun k hk => by rw [mw, data_frame k₅.frame hd₅ hk, hc.data k hk])).mono
    fun s₆ ⟨v₆, k₆, _, pt₆⟩ => ?_
  rw [D₃] at pt₆
  have k₅₆ : Kept [sub s₀ 64 384, dR s₀] s₅ s₆ :=
    (kw.sub fun _ hr => absurd hr List.not_mem_nil).trans k₆
  have i₆ : Inv0 s₀ s₆ := i₅.step k₅₆ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok0 hp i₆)) fun s₇ ⟨⟨i₇, k₇, r₇⟩, v₇⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (finalizeTo_ok0 hp i₇ (out := 640) (.inr ⟨by omega, by omega⟩)))
    fun s₈ ⟨⟨k₈, tag₈⟩, v₈⟩ => ?_)
  have x21₈ : s₈.gpr .x21 = cx s₀ := by rw [k₈.cs _ (pres .x21) (pres30 .x21), i₇.x21]
  refine WP.block_append (WP.mono (WP.preservedV (compare_ok hp x21₈ (by rw [k₈.rd, i₇.rd])
    (by rw [k₈.wr, i₇.wr]))) fun s₉ ⟨⟨rax₉, g₉, sp₉, m₉, rd₉, wr₉⟩, v₉⟩ => ?_)
  refine WP.mono (WP.preservedV (restore_ok hp (by rw [g₉ _ (pres .x21), x21₈])
    (by rw [m₉]; exact i₇.saved.frame k₈.frame (by rdisj_all))
    (by rw [rd₉, k₈.rd, i₇.rd]) (by rw [wr₉, k₈.wr, i₇.wr]))) fun s₁₀ ⟨⟨⟨rs₁₀, g₁₀, m₁₀⟩, sp₁₀⟩, v₁₀⟩ => ?_
  -- The tag computed, and the one received.
  have R₄ := hc.mac
  simp only [Bool.false_eq_true, ↓reduceIte] at R₄
  have R₅ := r₅ _ _ R₄
  rw [rest_orig hc, List.append_assoc, split_pad (pre_mod false T) (by omega), D₃] at R₅
  have T₈ := tag₈ _ _ (r₇ _ _ (Repr.frame k₅₆.frame (by rdisj_all) R₅))
  have L₆ : bytesAt s₆.mem (off (cx s₀) 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₅₆.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₅.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame hc.frame (by rdisj_all) (by lit_omega), len₃]
  have T0₈ : bytesAt s₈.mem (off (cx s₀) 48) 16 = T0 s₀ := by
    rw [bytesAt_frame k₈.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame i₇.frame (by rdisj_all) (by lit_omega), ← off48]
  have P₁₀ : bytesAt s₁₀.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₁₀, m₉, bytesAt_frame k₈.frame (by rdisj_all) hL', bytesAt_frame k₇.frame (by rdisj_all) hL',
      pt₆]
  rw [L₆, hA] at T₈
  have hg := abi_of0 i₇ (fun r hr h30 => by rw [g₉ r hr, k₈.cs r hr h30]) rs₁₀
    (fun r hr => by rw [g₁₀ r hr]) (by rw [sp₁₀, sp₉, k₈.sp])
  refine ⟨⟨hg.1, hg.2, fun r hr => ?_⟩, ?_⟩
  · exact (v₁₀ r hr).trans ((v₉ r hr).trans ((v₈ r hr).trans ((v₇ r hr).trans
      ((v₆ r hr).trans ((vw r hr).trans ((v₅ r hr).trans ((hc.vec r hr).trans
      ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr))))))))))
  · have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₈.mem (off (cx s₀) 640) 16 := by
      rw [T₈]
      simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
    rw [openAArch64, Contract.post_mk]
    dsimp only
    rw [g₁₀ .x0 (by decide), rax₉]
    split
    next pt hpt =>
      obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
      exact ⟨ite_eq_left (hm.symm.trans (hmac.trans T0₈.symm)), P₁₀⟩
    next hn => exact ite_eq_right fun he => decrypt_eq_none hn ((hm.trans he).trans T0₈)

end VG.Proof.ChaCha20Poly1305.AArch64
