import VerifiedGarbage.Proof.Pbkdf2.AArch64.Derive.Loop

/-!
# PBKDF2-HMAC-SHA-256 on AArch64: correctness

Untrusted: everything here is checked by Lean. The prologue, the key and the
salt, the registers of the loop, the loop, and the epilogue, put together,
inside the frame that saves `x30` (`WP.frameReg`).
-/

namespace VG.Proof.Pbkdf2.AArch64Derive

open VG VG.AArch64 VG.Impl.Pbkdf2.AArch64
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey sha256)
open VG.Proof.Sha256.AArch64.Stream (wp_ldr eval_zero ofNat_beq_zero)
open VG.AArch64.RegBlock (upd wp_run')

/-- Before the loop over the blocks. -/
structure Setup (s₀ s : State) : Prop where
  base : Base s₀ s
  x21 : s.gpr .x21 = s₀.gpr .x6
  core : 0 < ol s₀ → Core s₀ 0 s

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem setup_ok {s : State} (h : KS4 s₀ s) : WP isa (.block loopSetup) s (Setup s₀) := by
  obtain ⟨⟨k, hK⟩, hS⟩ := h
  have hpos := hp.pos
  refine wp_run' rfl fun s' hg hm rd wr sp => ?_
  have base : Base s₀ s' := k.base.regs rd wr sp (by rw [hg]; simp [upd]) (by rw [hg]; simp [upd])
    (by rw [hg]; simp [upd]) hm
  have x21 : s'.gpr .x21 = s₀.gpr .x6 := by rw [hg]; simp [upd, k.base.x25]
  refine ⟨base, x21, fun hol => ⟨⟨base, ?_, ?_, ?_, ?_, ?_⟩, hm ▸ hK, hm ▸ hS, by omega, ?_⟩⟩
  · rw [hg]; simp [upd]
  · rw [x21]; simp
  · rw [hg]; simp only [upd, reduceCtorEq, ite_true, ite_false]
    rw [k.base.x26]
    apply BitVec.eq_of_toNat_eq
    have := ((s₀.gpr .x4).setWidth 32).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, cc] at hpos this ⊢
    omega
  · rw [hg]; simp only [upd, reduceCtorEq, ite_true, ite_false, k.x23]
    apply BitVec.eq_of_toNat_eq
    have := (s₀.gpr .x3).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, sl]
    omega
  · rw [hg]; simp [upd, k.x24]
  · rw [hm]; rfl

theorem blocks_ok {s : State} (h : Setup s₀ s) :
    WP isa (.ite (.zero .x .x21) (.block []) (.loop block (.nonzero .x .x21))) s (Done s₀) := by
  have e : (s.gpr .x21 == 0) = decide (ol s₀ = 0) := by
    rw [h.x21, ← ofNat_beq_zero (ol_lt s₀)]; simp [ol]
  refine WP.ite (decide (ol s₀ = 0)) ((eval_zero s .x21).trans (by rw [e])) (fun hb => WP.block_nil ⟨h.base, ?_⟩)
    (fun hb => ?_)
  · have hol : ol s₀ = 0 := by simpa using hb
    rw [hol, List.take_zero]; rfl
  · exact loop_ok hp (h.core (by simp at hb; omega))

/-- The end: our caller's registers restored. -/
theorem epilogue_ok {s : State} (h : Done s₀ s) :
    WP isa (.block dEpilogue) s fun s' => (∀ p ∈ dSaved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.mem = s.mem ∧
      s'.sp = s.sp := by
  obtain ⟨b, -⟩ := h
  have sv := b.saved
  have io : ∀ {t : State}, t.wr = s₀.wr → ∀ d : Nat, d + 8 ≤ 2048 →
      InRegions (t.rd ++ t.wr) (sc s₀ + BitVec.ofNat 64 d) 8 := fun hw _ h => hp.in_sc' hw h
  simp only [dEpilogue, dSaved, List.map_cons, List.map_nil]
  refine wp_ldr (a := sc s₀ + BitVec.ofNat 64 432) (by decide) (by rw [b.x19]) (io b.wr _ (by omega))
    fun s₁ u₁ => ?_
  refine wp_ldr (a := sc s₀ + BitVec.ofNat 64 440) (by decide) (by rw [u₁.other _ (by decide), b.x19])
    (io (u₁.wr.trans b.wr) _ (by omega)) fun s₂ u₂ => ?_
  refine wp_ldr (a := sc s₀ + BitVec.ofNat 64 448) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), b.x19])
    (io (u₂.wr.trans (u₁.wr.trans b.wr)) _ (by omega)) fun s₃ u₃ => ?_
  refine wp_ldr (a := sc s₀ + BitVec.ofNat 64 456) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), b.x19])
    (io (u₃.wr.trans (u₂.wr.trans (u₁.wr.trans b.wr))) _ (by omega)) fun s₄ u₄ => ?_
  refine wp_ldr (a := sc s₀ + BitVec.ofNat 64 464) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      b.x19])
    (io (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans (u₁.wr.trans b.wr)))) _ (by omega)) fun s₅ u₅ => ?_
  refine wp_ldr (a := sc s₀ + BitVec.ofNat 64 472) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), b.x19])
    (io (u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans (u₁.wr.trans b.wr))))) _ (by omega))
    fun s₆ u₆ => ?_
  refine wp_ldr (a := sc s₀ + BitVec.ofNat 64 480) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), b.x19])
    (io (u₆.wr.trans (u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans (u₁.wr.trans b.wr)))))) _ (by omega))
    fun s₇ u₇ => ?_
  refine wp_ldr (a := sc s₀ + BitVec.ofNat 64 424) (by decide)
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), b.x19])
    (io (u₇.wr.trans (u₆.wr.trans (u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans
      (u₁.wr.trans b.wr))))))) _ (by omega))
    fun s₈ u₈ => WP.block_nil ⟨?_, by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
      by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩
  have m₁ : s₁.mem = s.mem := u₁.mem
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, m₂]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃]
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, m₄]
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, m₅]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, m₆]
  intro p hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    exact sv (.x20, 432) (by decide)
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, m₁]
    exact sv (.x21, 440) (by decide)
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, m₂]
    exact sv (.x22, 448) (by decide)
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, m₃]
    exact sv (.x23, 456) (by decide)
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, m₄]
    exact sv (.x24, 464) (by decide)
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, m₅]
    exact sv (.x25, 472) (by decide)
  · rw [u₈.other _ (by decide), u₇.gpr, m₆]
    exact sv (.x26, 480) (by decide)
  · rw [u₈.gpr, m₇]
    exact sv (.x19, 424) (by decide)

theorem epi_post {s : State} (h : Done s₀ s) {s' : State} (hm : s'.mem = s.mem) :
    Proof.Pbkdf2.pbkdf2Sha256AArch64.post s₀ s' := by
  show Spec.Pbkdf2.pbkdf2HmacSha256 (P s₀) (S s₀) (cc s₀) (ol s₀) = some (bytesAt s'.mem (op s₀) (ol s₀))
  unfold Spec.Pbkdf2.pbkdf2HmacSha256 Spec.Pbkdf2.pbkdf2
  split
  · rename_i hc; have := hp.len; omega
  · rw [hm, h.2, show ol s₀ + 32 - 1 = ol s₀ + 31 by omega]
    rfl

omit hp in
/-- `x27`–`x29` are written by no instruction, ours or our callees'. -/
theorem untouched_ok : ∀ r ∈ [Reg.x27, .x28, .x29], ∀ i ∈ instrs deriveMain, dstOf i ≠ some r := by
  have h : (instrs deriveMain).all (fun i => [Reg.x27, .x28, .x29].all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp h i hi
  simp only [List.all_eq_true, bne_iff_ne, ne_eq] at this
  exact this r hr

/-- `derive` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain :
    WP isa deriveMain (ini s₀) fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      Proof.Pbkdf2.pbkdf2Sha256AArch64.post s₀ s' := by
  refine WP.mono (Proof.Sha256.AArch64.Stream.WP.gprs (rs := [.x27, .x28, .x29])
    (Q := fun s' => (∀ p ∈ dSaved, s'.gpr p.1 = s₀.gpr p.1) ∧ Proof.Pbkdf2.pbkdf2Sha256AArch64.post s₀ s')
    ?_ untouched_ok) fun s' ⟨⟨hk, hpost⟩, hu⟩ =>
    ⟨fun r hr h30 => ?_, hpost⟩
  · unfold deriveMain
    exact WP.seq (WP.mono (prologue_ok hp) fun _ h1 => WP.seq (WP.mono (key_ok hp h1) fun _ h2 =>
      WP.seq (WP.mono (keySalt_ok hp h2) fun _ h3 => WP.seq (WP.mono (setup_ok hp h3) fun _ h4 =>
        WP.seq (WP.mono (blocks_ok hp h4) fun _ h5 =>
          WP.mono (epilogue_ok hp h5) fun _ h6 => ⟨h6.1, epi_post hp h5 h6.2.1⟩)))))
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hk (.x19, 424) (by decide)
    · exact hk (.x20, 432) (by decide)
    · exact hk (.x21, 440) (by decide)
    · exact hk (.x22, 448) (by decide)
    · exact hk (.x23, 456) (by decide)
    · exact hk (.x24, 464) (by decide)
    · exact hk (.x25, 472) (by decide)
    · exact hk (.x26, 480) (by decide)
    · exact hu .x27 (by decide)
    · exact hu .x28 (by decide)
    · exact hu .x29 (by decide)
    · exact absurd rfl h30

theorem correct :
    WP isa derive s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Pbkdf2.pbkdf2Sha256AArch64.post s₀ s' := by
  refine WP.frameReg (by have := hp.sp48; omega) (fun R hR => ?_)
    (WP.mono (correctMain hp) fun s' ⟨hk, hpost⟩ => ⟨⟨fun r hr => ?_, rfl⟩, hpost⟩)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hp.stk_o'.sub_left (fr_sub _)
    · exact hp.stk_s'.sub_left (fr_sub _)
  · by_cases h30 : r = .x30
    · subst h30; simp [State.write]
    · simp only [State.write, h30, ite_false]
      exact hk r hr h30

end

end VG.Proof.Pbkdf2.AArch64Derive
