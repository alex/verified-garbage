import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stages

/-!
# ChaCha20-Poly1305 on x86-64: correctness

Untrusted: everything here is checked by Lean. `seal` and `open`, from their
parts.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem APre.stk_d' {s₀ : State} (hp : APre s₀) : (stkR s₀).Disjoint (dR s₀) := hp.stk_d
theorem APre.stk_a' {s₀ : State} (hp : APre s₀) : (stkR s₀).Disjoint (aR s₀) := hp.stk_a

/-- That two of the regions the parts use are disjoint: parts of the context
at different offsets, the stack below the return address, and the data.
(Matching only reducibly, so that a lemma that does not apply fails fast.) -/
macro "rdisj" : tactic => `(tactic| first
  | with_reducible exact sub_disj _ (by omega) (by omega) (by omega)
  | with_reducible exact (APre.stk_sub ‹APre _› (by omega)).symm
  | with_reducible exact APre.stk_sub ‹APre _› (by omega)
  | with_reducible exact (‹APre _›).c_d.sub_left (sub_ctx _ (by omega))
  | with_reducible exact (‹APre _›).c_d.symm.sub_right (sub_ctx _ (by omega))
  | with_reducible exact (APre.stk_d' ‹APre _›).symm
  | with_reducible exact (‹APre _›).c_a.symm.sub_right (sub_ctx _ (by omega))
  | with_reducible exact (APre.stk_a' ‹APre _›).symm
  | with_reducible exact (‹APre _›).a_d
  | with_reducible exact (‹APre _›).ret_c.sub_right (sub_ctx _ (by omega))
  | with_reducible exact (‹APre _›).ret_d
  | with_reducible exact ret_stk _)

/-- A region is disjoint from each of a list of regions. -/
macro "rdisj_all" : tactic => `(tactic| (
  simp only [macR, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals rdisj))

theorem hRDX (s₀ : State) : s₀.gpr .rdx = BitVec.ofNat 64 (AL s₀) := by simp [AL]

theorem srcA {s₀ : State} (hp : APre s₀) : Src s₀ (ad s₀) (AL s₀) :=
  ⟨(s₀.gpr .rdx).isLt, hp.wrap_a, hp.c_a, hp.stk_a, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.rd], hc⟩⟩

theorem srcD {s₀ : State} (hp : APre s₀) : Src s₀ (dp s₀) (L s₀) :=
  ⟨(s₀.gpr .r8).isLt, hp.wrap_d, hp.c_d, hp.stk_d, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.wr], hc⟩⟩

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

theorem off48 (s₀ : State) : cx s₀ + 48 = off (cx s₀) 48 := by rw [off_eq]; rfl

/-- The return address is unchanged. -/
theorem ret_kept {s₀ : State} (hp : APre s₀) {m₆ m' : Mem} (hi : Frame [workR s₀, dR s₀, stkR s₀] s₀.mem m₆)
    {out : Nat} (ho : out + 16 ≤ 1024) (hf : Frame [sub s₀ 448 128, sub s₀ out 16, stkR s₀] m₆ m') :
    m'.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 := by
  have c : (retR s₀).Contains (s₀.gpr .rsp) (64 / 8) := Region.contains_self _ _
  rw [hf.readW c (by rdisj_all) (by omega), hi.readW c (by rdisj_all) (by omega)]

theorem seal_correct {s₀ : State} (hp : APre s₀) :
    WP isa «seal» s₀ fun s' => gprPreserved s₀ s' ∧ sealX86_64.post s₀ s' := by
  have hL' := (s₀.gpr .r8).isLt.le
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.fine (by rdisj_all) (s₀.gpr .rdx).isLt.le
  refine WP.seq (WP.mono (macPad_ok hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]), h₁.rbp]))
    fun s₃ ⟨i₃, _, f₃, len₃⟩ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₃ (by rdisj_all), stateAt_frame f₂ (by rdisj_all), h₁.st]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₃ (by rdisj_all) hL', bytesAt_frame f₂ (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (crypt_ok hp i₃ st₃) fun s₄ ⟨i₄, _, f₄, ct₄⟩ => ?_)
  rw [D₃] at ct₄
  refine WP.seq (WP.mono (macPad_ok hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₄.r15
    i₄.rsp i₄.rd i₄.wr i₄.r14 (by rw [i₄.r13]; exact hL s₀))
    fun s₅ ⟨cs₅, rd₅, wr₅, f₅, r₅⟩ => ?_)
  have i₅ := mac_inv hp i₄ cs₅ rd₅ wr₅ f₅
  refine WP.seq (WP.mono (absorbLengths_ok hp i₅) fun s₆ ⟨i₆, _, f₆, r₆⟩ => ?_)
  refine WP.seq (WP.mono (finalizeTo_ok hp i₆ (out := 48) (.inl (by omega)))
    fun s₇ ⟨cs₇, rd₇, wr₇, rdi₇, _, f₇, tag₇⟩ => ?_)
  refine WP.mono (restore_ok hp rdi₇ (i₆.saved.frame f₇ (by rdisj_all))
    (by rw [cs₇ _ (by simp [calleeSaved]), i₆.r12]) (by rw [cs₇ _ calleeSaved_rsp, i₆.rsp])
    (by rw [rd₇, i₆.rd]) (by rw [wr₇, i₆.wr])) fun s₈ ⟨cs₈, _, m₈⟩ => ?_
  have R₄ := Repr.frame f₄ (by rdisj_all) (Repr.frame f₃ (by rdisj_all) (r₂ (otk s₀) [] h₁.poly))
  have T₇ := tag₇ _ _ (r₆ _ _ (r₅ _ _ R₄))
  have L₅ : bytesAt s₅.mem (off (cx s₀) 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame f₅ (by rdisj_all) (by omega), bytesAt_frame f₄ (by rdisj_all) (by omega), len₃]
  have C₈ : bytesAt s₈.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₈, bytesAt_frame f₇ (by rdisj_all) hL', bytesAt_frame f₆ (by rdisj_all) hL',
      bytesAt_frame f₅ (by rdisj_all) hL', ct₄]
  have C₄ : bytesAt s₄.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := ct₄
  refine ⟨⟨cs₈, by rw [m₈]; exact ret_kept hp i₆.frame (by omega) f₇⟩, ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₈.mem (dp s₀) (L s₀), bytesAt s₈.mem (cx s₀ + 48) 16)
  rw [C₈, off48, m₈, T₇, L₅, C₄, hA]
  simp only [Spec.ChaCha20Poly1305.encrypt, macData, List.nil_append,
    List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]

theorem open_eq : «open» =
    .seq prologue (.seq (macPad .rbx .rbp) (.seq (macPad .r14 .r13) (.seq (.block lengths)
    (.seq absorbLengths (.seq crypt (.seq (finalizeTo 640) (.block (compare ++ restore)))))))) := rfl

theorem open_correct {s₀ : State} (hp : APre s₀) :
    WP isa «open» s₀ fun s' => gprPreserved s₀ s' ∧ openX86_64.post s₀ s' := by
  have hL' := (s₀.gpr .r8).isLt.le
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.fine (by rdisj_all) (s₀.gpr .rdx).isLt.le
  refine WP.seq (WP.mono (macPad_ok hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₂ (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (macPad_ok hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₂.r15
    i₂.rsp i₂.rd i₂.wr i₂.r14 (by rw [i₂.r13]; exact hL s₀))
    fun s₃ ⟨cs₃, rd₃, wr₃, f₃, r₃⟩ => ?_)
  have i₃ := mac_inv hp i₂ cs₃ rd₃ wr₃ f₃
  refine WP.seq (WP.mono (lengths_ok hp i₃ (by rw [cs₃ _ (by simp [calleeSaved]),
    cs₂ _ (by simp [calleeSaved]), h₁.rbp])) fun s₄ ⟨i₄, _, f₄, len₄⟩ => ?_)
  refine WP.seq (WP.mono (absorbLengths_ok hp i₄) fun s₅ ⟨i₅, _, f₅, r₅⟩ => ?_)
  have st₅ : stateAt s₅.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₅ (by rdisj_all), stateAt_frame f₄ (by rdisj_all), stateAt_frame f₃ (by rdisj_all),
      stateAt_frame f₂ (by rdisj_all), h₁.st]
  refine WP.seq (WP.mono (crypt_ok hp i₅ st₅) fun s₆ ⟨i₆, _, f₆, pt₆⟩ => ?_)
  refine WP.seq (WP.mono (finalizeTo_ok hp i₆ (out := 640) (.inr ⟨by omega, by omega⟩))
    fun s₇ ⟨cs₇, rd₇, wr₇, rdi₇, rcx₇, f₇, tag₇⟩ => ?_)
  refine WP.block_append (WP.mono (compare_ok hp rcx₇ rdi₇ (by rw [rd₇, i₆.rd]) (by rw [wr₇, i₆.wr]))
    fun s₈ ⟨rax₈, g₈, m₈, rd₈, wr₈⟩ => ?_)
  have g₈' : ∀ r ∈ calleeSaved, s₈.gpr r = s₇.gpr r := fun r hr =>
    g₈ r (calleeSaved_ne hr).1 (calleeSaved_ne hr).2.2.1
  refine WP.mono (restore_ok hp (by rw [g₈ _ (by decide) (by decide), rdi₇])
    (by rw [m₈]; exact i₆.saved.frame f₇ (by rdisj_all))
    (by rw [g₈' _ (by simp [calleeSaved]), cs₇ _ (by simp [calleeSaved]), i₆.r12])
    (by rw [g₈' _ calleeSaved_rsp, cs₇ _ calleeSaved_rsp, i₆.rsp])
    (by rw [rd₈, rd₇, i₆.rd]) (by rw [wr₈, wr₇, i₆.wr])) fun s₉ ⟨cs₉, rax₉, m₉⟩ => ?_
  -- The tag computed, and the one received.
  have R₃ := r₃ _ _ (r₂ (otk s₀) [] h₁.poly)
  have T₇ := tag₇ _ _ (Repr.frame f₆ (by rdisj_all) (r₅ _ _ (Repr.frame f₄ (by rdisj_all) R₃)))
  have L₄ : bytesAt s₄.mem (off (cx s₀) 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := len₄
  have T0₇ : bytesAt s₇.mem (off (cx s₀) 48) 16 = T0 s₀ := by
    rw [bytesAt_frame f₇ (by rdisj_all) (by omega), bytesAt_frame i₆.frame (by rdisj_all) (by omega), ← off48]
  have P₉ : bytesAt s₉.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₉, m₈, bytesAt_frame f₇ (by rdisj_all) hL', pt₆, bytesAt_frame f₅ (by rdisj_all) hL',
      bytesAt_frame f₄ (by rdisj_all) hL', bytesAt_frame f₃ (by rdisj_all) hL', D₂]
  rw [L₄, D₂, hA] at T₇
  refine ⟨⟨cs₉, by rw [m₉, m₈]; exact ret_kept hp i₆.frame (by omega) f₇⟩, ?_⟩
  have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₇.mem (off (cx s₀) 640) 16 := by
    rw [T₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  show match Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
    | some pt => (s₉.gpr .rax).setWidth 32 = 1 ∧ bytesAt s₉.mem (dp s₀) (L s₀) = pt
    | none => (s₉.gpr .rax).setWidth 32 = 0
  rw [rax₉, rax₈, ← T0₇]
  unfold Spec.ChaCha20Poly1305.decrypt
  by_cases he : bytesAt s₇.mem (off (cx s₀) 640) 16 = bytesAt s₇.mem (off (cx s₀) 48) 16
  · rw [ite_eq_left he, show mac (polyKeyGen (K s₀) (N s₀)) (macData (A s₀) (D s₀)) =
      bytesAt s₇.mem (off (cx s₀) 48) 16 by rw [← he]; exact hm, ite_eq_left rfl]
    exact ⟨rfl, P₉⟩
  · rw [ite_eq_right he, ite_eq_right (by rw [show polyKeyGen (K s₀) (N s₀) = otk s₀ from rfl, hm]; exact he)]

end VG.Proof.ChaCha20Poly1305.X86_64
