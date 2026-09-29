import VerifiedGarbage.Proof.MlKem.X86.SampleSetup

/-!
# ML-KEM on x86 (32-bit): the Keccak calls of `vg_mlkem_sample_ntt`

Untrusted: everything here is checked by Lean. From the all-zero state
(`Z`), absorbing the seed (`absorb_call`), padding for SHAKE128
(`pad_call`) and squeezing 840 bytes into `scratch` (`squeeze_call`) leaves
the first 840 bytes of the XOF output of the seed there (`Out`). Each call's
arguments are set by a block (`absArgs_piece`, `padArgs_piece`,
`sqArgs_piece`) from `esi = scratch` and the seed pointer on the stack.
-/

namespace VG.Proof.MlKem.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt Repr squeezeFrom shakeSuffix)

/-! ## Absorbing the seed -/

theorem absArgs_piece : Piece Pre Pub Z (fun s₀ s => Z s₀ s ∧ AbsArgs s (SS s₀) (dP s₀) (WW s₀) 168 0 34)
    (.block smpAbsorbArgs) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have a₀ := h.argEa (i := 0)
    have i₀ := h.argIn hp (i := 0) (by omega)
    have v₀ := h.argw hp (i := 0) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at a₀
    apply WP.of_runBlock
    simp (config := {decide := true}) only [smpAbsorbArgs, smpSt, smpWk, at_, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a₀, i₀, v₀, ite_true, ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, by simp [h.esi]⟩, h.st⟩,
      ⟨by simp [h.esi], rfl, rfl, rfl, rfl, by simp [h.esi]⟩⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.E1]

/-- `Ctx`, with the seed absorbed. -/
structure A1 (s₀ s : State) : Prop extends Ctx s₀ s where
  st : Repr s.mem ((SS s₀).setWidth 64) 168 (Bs s₀)

theorem absorb_call : Piece Pre Pub (fun s₀ s => Z s₀ s ∧ AbsArgs s (SS s₀) (dP s₀) (WW s₀) 168 0 34) A1
    (callWith rs6 "vg_keccak_absorb" Impl.Sha3.X86.Stream.absorb) := by
  refine absorb_piece E1 SS dP WW 168 0 34 rate168 (by decide) (by decide) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, by rw [SS, SS, hq.2.2.2.2], hq.2.2.1, by rw [WW, WW, hq.2.2.2.2]⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr post => ?_)
  · have hk := hp.kbufs
    have hs := hp.s_fit
    refine ⟨h.esp, ha, hk, hp.d_fit, ?_, ?_, (hp.stk_d.sub_left hp.c_sub), ?_, hp.within_s h.wr (by omega) (by omega),
      hp.within_s h.wr (by omega) (by omega)⟩
    · rw [hp.reg_s (by omega)]; exact hp.d_s.sub_right (hp.sub_s (by omega))
    · rw [hp.reg_s (by omega)]; exact hp.d_s.sub_right (hp.sub_s (by omega))
    · refine ⟨dR s₀, ?_, 0, (BitVec.add_zero _).symm, Nat.le_refl _⟩
      rw [h.rd, h.wr, pushed_rd, hp.rd]; simp
  · refine ⟨h.toCtx.call e₁ e₂ e₃ fr (calls_sub3 hp), ?_⟩
    have := post [] (repr_nil h.st) (by simp)
    rwa [List.nil_append, h.seed hp] at this

/-! ## Padding -/

theorem padArgs_piece : Piece Pre Pub A1 (fun s₀ s => A1 s₀ s ∧ PadArgs s (SS s₀) (WW s₀) 168 34 0x1f)
    (.block smpPadArgs) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [smpPadArgs, smpSt, smpWk, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, by simp [h.esi]⟩, h.st⟩,
    ⟨by simp [h.esi], rfl, rfl, rfl, by simp [h.esi]⟩⟩

/-- `Ctx`, with the seed absorbed and padded for SHAKE128. -/
structure A2 (s₀ s : State) : Prop extends Ctx s₀ s where
  st : stateAt s.mem ((SS s₀).setWidth 64) = padded 168 shakeSuffix (Bs s₀)

theorem pad_call : Piece Pre Pub (fun s₀ s => A1 s₀ s ∧ PadArgs s (SS s₀) (WW s₀) 168 34 0x1f) A2
    (callWith rs5 "vg_keccak_pad" Impl.Sha3.X86.Stream.pad) := by
  refine pad_piece E1 SS WW 168 34 0x1f rate168 (by decide) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, by rw [SS, SS, hq.2.2.2.2], by rw [WW, WW, hq.2.2.2.2]⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr post => ?_)
  · exact ⟨h.esp, ha, hp.kbufs, hp.within_s h.wr (by omega) (by omega), hp.within_s h.wr (by omega) (by omega)⟩
  · refine ⟨h.toCtx.call e₁ e₂ e₃ fr (calls_sub3 hp), ?_⟩
    have := post (Bs s₀) h.st (by rw [bytesAt_length])
    rwa [show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32] at this

/-! ## Squeezing -/

theorem sqArgs_piece : Piece Pre Pub A2 (fun s₀ s => A2 s₀ s ∧ AbsArgs s (SS s₀) (sP s₀) (WW s₀) 168 0 840)
    (.block smpSqueezeArgs) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [smpSqueezeArgs, smpSt, smpWk, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, by simp [h.esi]⟩, h.st⟩,
    ⟨by simp [h.esi], rfl, rfl, by simp [h.esi], rfl, by simp [h.esi]⟩⟩

/-- `Ctx`, with the first 840 bytes of the XOF output of the seed at `scratch`. -/
structure Out (s₀ s : State) : Prop extends Ctx s₀ s where
  out : ∀ p < 840, s.mem (sA s₀ + BitVec.ofNat 64 p) = xofByte (Bs s₀) p

theorem squeeze_call : Piece Pre Pub (fun s₀ s => A2 s₀ s ∧ AbsArgs s (SS s₀) (sP s₀) (WW s₀) 168 0 840) Out
    (callWith rs6 "vg_keccak_squeeze" Impl.Sha3.X86.Stream.squeeze) := by
  refine squeeze_piece E1 SS sP WW 168 0 840 rate168 (by decide) (by decide) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, by rw [SS, SS, hq.2.2.2.2], hq.2.2.2.2, by rw [WW, WW, hq.2.2.2.2]⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr r₁ _ => ?_)
  · have hs := hp.s_fit
    refine ⟨h.esp, ha, hp.kbufs, by omega, ?_, ?_, ?_, hp.within_s h.wr (by omega) (by omega),
      hp.within_s0 h.wr (by omega), hp.within_s h.wr (by omega) (by omega)⟩
    · rw [hp.reg_s (by omega), Pre.reg_s0]
      exact disj_at (len := 2048) (by omega) (by omega) hs (by omega)
    · rw [hp.reg_s (by omega), Pre.reg_s0]
      exact disj_at (len := 2048) (by omega) (by omega) hs (by omega)
    · rw [Pre.reg_s0]
      exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))
  · refine ⟨h.toCtx.call e₁ e₂ e₃ fr (calls_sub hp), fun p hp' => ?_⟩
    rw [h.st] at r₁
    have e := bytesAt_getD s'.mem (sA s₀) (len := 840) hp'
    rw [r₁, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [VG.Proof.Sha3.length_squeezeFrom (by decide) (by decide)]; exact hp'),
      Option.getD_some, xof_squeezeFrom_getElem _ hp', Nat.zero_add] at e
    exact e.symm

end VG.Proof.MlKem.X86.Sample
