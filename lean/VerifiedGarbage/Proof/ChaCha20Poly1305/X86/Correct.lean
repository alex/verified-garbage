import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Stages

/-!
# ChaCha20-Poly1305 on x86 (32-bit): correctness

Untrusted: everything here is checked by Lean. `seal` and `open`, from their
parts.
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

/-- That two of the regions the parts use are disjoint: parts of the context
at different offsets, the stack below the return address, the data, the
additional data and the return address. (Matching only reducibly, so that a
lemma that does not apply fails fast.) -/
macro "rdisj" : tactic => `(tactic| first
  | with_reducible exact sub_disj _ (by omega) (by omega) (by omega)
  | with_reducible exact (APre.stk_sub ‹APre _› (by omega)).symm
  | with_reducible exact APre.stk_sub ‹APre _› (by omega)
  | with_reducible exact APre.d_sub ‹APre _› (by omega)
  | with_reducible exact (APre.d_sub ‹APre _› (by omega)).symm
  | with_reducible exact (‹APre _›).stk_d.symm
  | with_reducible exact APre.a_sub ‹APre _› (by omega)
  | with_reducible exact (‹APre _›).stk_a.symm
  | with_reducible exact (‹APre _›).a_d
  | with_reducible exact APre.ret_sub ‹APre _› (by omega)
  | with_reducible exact (‹APre _›).ret_d
  | with_reducible exact APre.ret_stk ‹APre _›)

/-- A region is disjoint from each of a list of regions. -/
macro "rdisj_all" : tactic => `(tactic| (
  simp only [macR, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals rdisj))

theorem srcA {s₀ : State} (hp : APre s₀) : Src s₀ (arg s₀ 1) (arg s₀ 2).toNat :=
  ⟨hp.fit_a, hp.c_a, hp.stk_a, by simp [hp.rd]⟩

theorem srcD {s₀ : State} (hp : APre s₀) : Src s₀ (arg s₀ 3) (arg s₀ 4).toNat :=
  ⟨hp.fit_d, hp.c_d, hp.stk_d, by simp [hp.wr]⟩

theorem ctx48 (s₀ : State) : cx s₀ + 48 = cx s₀ + BitVec.ofNat 64 48 := rfl

theorem hAL (s₀ : State) : AL s₀ < 2 ^ 64 := by have := (ALN s₀).isLt; simp only [AL]; omega
theorem hL (s₀ : State) : L s₀ ≤ 2 ^ 64 := by have := (LN s₀).isLt; simp only [L]; omega

/-- The return address is unchanged. -/
theorem ret_kept {s₀ : State} (hp : APre s₀) {m₆ m' : Mem} (hi : Frame [workR s₀, dR s₀, stkR s₀] s₀.mem m₆)
    {out : Nat} (ho : OutOk out) (hf : Frame [sub s₀ 448 128, sub s₀ out 16, stkR s₀] m₆ m') :
    m'.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 := by
  unfold OutOk at ho
  have c : (retR s₀).Contains ((E s₀).setWidth 64) (32 / 8) := Region.contains_self _ _
  rw [hf.readW c (by rdisj_all) (by omega), hi.readW c (by rdisj_all) (by omega)]

theorem seal_eq : «seal» =
    .seq prologue (.seq (macPad (4 + 4 * 1) (8 + 4 * 1)) (.seq (.block lengths) (.seq crypt
    (.seq (macPad (4 + 4 * 3) (8 + 4 * 3)) (.seq (absorbOne 656) (.seq (finalizeTo 48) (.block restore))))))) := rfl

theorem seal_correct {s₀ : State} (hp : APre s₀) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealX86.post s₀ s' := by
  have hL' := hL s₀
  rw [seal_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ := bytesAt_frame h₁.fine (by rdisj_all) (hAL s₀).le
  refine WP.seq (WP.mono (macPad_ok hp (i := 1) (by omega) (srcA hp) h₁.inv) fun s₂ ⟨i₂, f₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (lengths_ok hp i₂) fun s₃ ⟨i₃, f₃, len₃⟩ => ?_)
  have st₃ : stateAt s₃.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₃ (by rdisj_all),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₂ (by rdisj_all), h₁.st]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₃ (by rdisj_all) hL', bytesAt_frame f₂ (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (crypt_ok hp i₃) fun s₄ ⟨i₄, f₄, ct₄⟩ => ?_)
  have C₄ := ct₄ st₃
  rw [D₃] at C₄
  refine WP.seq (WP.mono (macPad_ok hp (i := 3) (by omega) (srcD hp) i₄) fun s₅ ⟨i₅, f₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (absorbOne_ok hp i₅ (k := 656) (.inr ⟨by omega, by omega⟩))
    fun s₆ ⟨i₆, f₆, r₆⟩ => ?_)
  refine WP.seq (WP.mono (finalizeTo_ok hp i₆ (out := 48) (.inl rfl)) fun s₇ ⟨h₇, f₇, tag₇⟩ => ?_)
  refine WP.mono (restore_ok hp h₇) fun s₈ ⟨cs₈, _, m₈⟩ => ?_
  have R₄ := Repr.frame f₄ (by rdisj_all) (Repr.frame f₃ (by rdisj_all) (r₂ (otk s₀) [] h₁.poly))
  have T₇ := tag₇ _ _ (r₆ _ _ (r₅ _ _ R₄))
  have L₅ : bytesAt s₅.mem (cx s₀ + BitVec.ofNat 64 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame f₅ (by rdisj_all) (by omega), bytesAt_frame f₄ (by rdisj_all) (by omega), len₃]
  have C₈ : bytesAt s₈.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₈, bytesAt_frame f₇ (by rdisj_all) hL', bytesAt_frame f₆ (by rdisj_all) hL',
      bytesAt_frame f₅ (by rdisj_all) hL', C₄]
  refine ⟨⟨cs₈, by rw [m₈]; exact ret_kept hp i₆.frame (.inl rfl) f₇⟩, ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₈.mem (dp s₀) (L s₀), bytesAt s₈.mem (cx s₀ + 48) 16)
  rw [C₈, ctx48, m₈, T₇, L₅, C₄, hA]
  simp only [Spec.ChaCha20Poly1305.encrypt, macData, List.nil_append,
    List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]

theorem open_eq : «open» =
    .seq prologue (.seq (macPad (4 + 4 * 1) (8 + 4 * 1)) (.seq (macPad (4 + 4 * 3) (8 + 4 * 3))
    (.seq (.block lengths) (.seq (absorbOne 656) (.seq crypt (.seq (finalizeTo 640)
      (.block (Impl.ChaCha20Poly1305.X86.compare ++ restore)))))))) := rfl

theorem open_correct {s₀ : State} (hp : APre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openX86.post s₀ s' := by
  have hL' := hL s₀
  rw [open_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ := bytesAt_frame h₁.fine (by rdisj_all) (hAL s₀).le
  refine WP.seq (WP.mono (macPad_ok hp (i := 1) (by omega) (srcA hp) h₁.inv) fun s₂ ⟨i₂, f₂, r₂⟩ => ?_)
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₂ (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (macPad_ok hp (i := 3) (by omega) (srcD hp) i₂) fun s₃ ⟨i₃, f₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (lengths_ok hp i₃) fun s₄ ⟨i₄, f₄, len₄⟩ => ?_)
  refine WP.seq (WP.mono (absorbOne_ok hp i₄ (k := 656) (.inr ⟨by omega, by omega⟩))
    fun s₅ ⟨i₅, f₅, r₅⟩ => ?_)
  have st₅ : stateAt s₅.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₅ (by rdisj_all),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₄ (by rdisj_all),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₃ (by rdisj_all),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₂ (by rdisj_all), h₁.st]
  refine WP.seq (WP.mono (crypt_ok hp i₅) fun s₆ ⟨i₆, f₆, pt₆⟩ => ?_)
  refine WP.seq (WP.mono (finalizeTo_ok hp i₆ (out := 640) (.inr rfl)) fun s₇ ⟨h₇, f₇, tag₇⟩ => ?_)
  refine WP.block_append (WP.mono (compare_ok hp h₇) fun s₈ ⟨rax₈, g₈, m₈, rd₈, wr₈⟩ => ?_)
  have h₈ : Fin s₀ s₈ := ⟨⟨by rw [g₈ _ (by decide) (by decide), h₇.at_.esp], by rw [rd₈, h₇.at_.rd],
    by rw [wr₈, h₇.at_.wr]⟩, by rw [g₈ _ (by decide) (by decide), h₇.edi], by rw [m₈]; exact h₇.saved⟩
  refine WP.mono (restore_ok hp h₈) fun s₉ ⟨cs₉, rax₉, m₉⟩ => ?_
  -- The tag computed, and the one received.
  have R₃ := r₃ _ _ (r₂ (otk s₀) [] h₁.poly)
  have T₇ := tag₇ _ _ (Repr.frame f₆ (by rdisj_all) (r₅ _ _ (Repr.frame f₄ (by rdisj_all) R₃)))
  have T0₇ : bytesAt s₇.mem (cx s₀ + BitVec.ofNat 64 48) 16 = T0 s₀ := by
    rw [bytesAt_frame f₇ (by rdisj_all) (by omega), bytesAt_frame i₆.frame (by rdisj_all) (by omega), ← ctx48]
  have P₉ : bytesAt s₉.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₉, m₈, bytesAt_frame f₇ (by rdisj_all) hL', pt₆ st₅, bytesAt_frame f₅ (by rdisj_all) hL',
      bytesAt_frame f₄ (by rdisj_all) hL', bytesAt_frame f₃ (by rdisj_all) hL', D₂]
  rw [len₄, D₂, hA] at T₇
  refine ⟨⟨cs₉, by rw [m₉, m₈]; exact ret_kept hp i₆.frame (.inr rfl) f₇⟩, ?_⟩
  have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₇.mem (cx s₀ + BitVec.ofNat 64 640) 16 := by
    rw [T₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  show match Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
    | some pt => s₉.gpr .eax = 1 ∧ bytesAt s₉.mem (dp s₀) (L s₀) = pt
    | none => s₉.gpr .eax = 0
  rw [rax₉, rax₈, ← T0₇]
  unfold Spec.ChaCha20Poly1305.decrypt
  by_cases he : bytesAt s₇.mem (cx s₀ + BitVec.ofNat 64 640) 16 = bytesAt s₇.mem (cx s₀ + BitVec.ofNat 64 48) 16
  · rw [ite_eq_left he, show mac (polyKeyGen (K s₀) (N s₀)) (macData (A s₀) (D s₀)) =
      bytesAt s₇.mem (cx s₀ + BitVec.ofNat 64 48) 16 by rw [← he]; exact hm, ite_eq_left rfl]
    exact ⟨rfl, P₉⟩
  · rw [ite_eq_right he, ite_eq_right (by rw [show polyKeyGen (K s₀) (N s₀) = otk s₀ from rfl, hm]; exact he)]

end VG.Proof.ChaCha20Poly1305.X86
