import VerifiedGarbage.Proof.Pbkdf2.X86_64.Derive.Loop

/-!
# PBKDF2-HMAC-SHA-256 on x86-64: correctness

Untrusted: everything here is checked by Lean. The key and the salt, the
registers of the loop, the loop, and the epilogue, put together.
-/

namespace VG.Proof.Pbkdf2.X86_64.Derive

open VG VG.X86_64 VG.Impl.Pbkdf2.X86_64
open VG.Impl.Sha256.X86_64 (at_)
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey sha256)
open VG.Proof.Sha256.X86_64 (ea_at ofInt_natCast)
open VG.Proof.Sha256.X86_64.Stream (wp_movm wp_mov32m wp_addi wp_subi wp_test ofNat_beq_zero)
open VG.X86_64.RegBlock (upd wp_run)
open VG.Impl.Sha256.X86_64.Stream (Callee)

/-- Before the loop over the blocks. -/
structure Setup (s₀ s : State) : Prop where
  base : Base s₀ s
  zf : s.zf = some (decide (ol s₀ = 0))
  core : 0 < ol s₀ → Core s₀ 0 s

section
variable {s₀ : State} (hp : Pre s₀) {f : Callee} (hv : Vf f)
include hp

include hv in
theorem keySalt_ok (sfx : String) {s : State} (h : AtK s₀ s) : WP isa (keySalt f sfx) s (KS4 s₀) :=
  WP.seq (WP.mono (ks1_ok h) fun _ h1 => WP.seq (WP.mono (ks2_ok hp hv h1) fun _ h2 =>
    WP.seq (WP.mono (ks3_ok hp h2) fun _ h3 => ks4_ok hp hv h3)))

theorem setup_ok {s : State} (h : KS4 s₀ s) : WP isa (.block loopSetup) s (Setup s₀) := by
  obtain ⟨⟨k, hK⟩, hS⟩ := h
  have := ol_lt s₀
  have hpos := hp.pos
  simp only [loopSetup]
  refine wp_addi fun s₁ u₁ => ?_
  refine wp_mov32m (a := sc s₀ + BitVec.ofNat 64 472) (ea_sc (by rw [u₁.other _ (by decide), k.base.rbx]) _)
    (hp.in_sc' (u₁.wr.trans k.base.wr) (by omega)) fun s₂ u₂ => ?_
  refine wp_subi fun s₃ u₃ _ => ?_
  refine wp_run (is := [.mov32 .r12 (.imm 1)]) rfl fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  have rsp₄ : s₄.gpr .rsp = s₀.gpr .rsp := by
    rw [g₄]; simp only [upd, reduceCtorEq, ite_false]
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), k.base.rsp]
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, u₃.rd, u₂.rd, u₁.rd, k.base.rd]
  have mm₄ : s₄.mem = s.mem := by rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  refine wp_movm (a := stackArgAddr s₀ 0) (by rw [ea_at, ofInt_natCast, rsp₄]; rfl)
    ⟨argR s₀, by rw [rd₄', hp.rd]; simp, by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩ fun s₅ u₅ => ?_
  refine wp_test fun s₆ g₆ m₆ rd₆ wr₆ z₆ => WP.block_nil ?_
  have e : ∀ r, r ≠ .r15 → r ≠ .r14 → r ≠ .r12 → r ≠ .r13 → s₆.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₆, u₅.other r h4, g₄]; simp only [upd, h3, ite_false]
    rw [u₃.other r h2, u₂.other r h2, u₁.other r h1]
  have r13 : s₆.gpr .r13 = stackArg s₀ 0 := by rw [g₆, u₅.gpr, mm₄, k.base.arg_eq hp]
  have base : Base s₀ s₆ := k.base.regs (by rw [rd₆, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd])
    (by rw [wr₆, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr]) (e _ (by decide) (by decide) (by decide) (by decide))
    (e _ (by decide) (by decide) (by decide) (by decide)) (by rw [m₆, u₅.mem, mm₄])
  have hm : s₆.mem = s.mem := by rw [m₆, u₅.mem, mm₄]
  refine ⟨base, ?_, fun hol => ⟨⟨base, ?_, ?_, ?_, ?_, ?_⟩, hm ▸ hK, hm ▸ hS, by omega, rfl⟩⟩
  · rw [z₆, u₅.gpr, mm₄, k.base.arg_eq hp, BitVec.and_self]
    refine congrArg some ?_
    by_cases hx : stackArg s₀ 0 = 0
    · have : ol s₀ = 0 := by show (stackArg s₀ 0).toNat = 0; rw [hx]; rfl
      simp [hx, this]
    · have : ol s₀ ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq h)
      simp only [this, decide_false]
      exact beq_false_of_ne hx
  · rw [g₆, u₅.other _ (by decide), g₄]; simp [upd]
  · rw [r13, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [g₆, u₅.other _ (by decide), g₄]; simp only [upd, reduceCtorEq, ite_false]
    rw [u₃.gpr, u₂.gpr, u₁.mem, k.base.saved.2]
    have : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide
    rw [this]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, cc] at hpos ⊢
    have := ((s₀.gpr .r8).setWidth 32).isLt
    simp only [BitVec.toNat_setWidth] at this
    omega
  · rw [g₆, u₅.other _ (by decide), g₄]; simp only [upd, reduceCtorEq, ite_false]
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, k.r15]
    apply BitVec.eq_of_toNat_eq
    have : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 := by decide
    rw [this]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, sl]
    omega
  · rw [e _ (by decide) (by decide) (by decide) (by decide), k.rbp, Nat.mul_zero]; simp

include hv in
theorem blocks_ok (sfx : String) {s : State} (h : Setup s₀ s) :
    WP isa (.ite .e (.block []) (.loop (block f sfx) .ne)) s (Done s₀) := by
  refine WP.ite (decide (ol s₀ = 0)) h.zf (fun hb => WP.block_nil ⟨h.base, ?_⟩) (fun hb => ?_)
  · have hol : ol s₀ = 0 := by simpa using hb
    rw [hol, List.take_zero]; rfl
  · exact loop_ok hp hv sfx (h.core (by simp at hb; omega))

/-- The end: our caller's registers restored. -/
theorem epilogue_ok {s : State} (h : Done s₀ s) :
    WP isa (.block dEpilogue) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  obtain ⟨b, -⟩ := h
  have sv := b.saved.1
  have io : ∀ {t : State}, t.wr = s₀.wr → ∀ d : Nat, d + 8 ≤ 2048 →
      InRegions (t.rd ++ t.wr) (sc s₀ + BitVec.ofNat 64 d) 8 := fun hw _ h => hp.in_sc' hw h
  simp only [dEpilogue, dSaved, List.map_cons, List.map_nil]
  refine wp_movm (ea_sc b.rbx 432) (io b.wr _ (by omega)) fun s₁ u₁ => ?_
  refine wp_movm (ea_sc (by rw [u₁.other _ (by decide), b.rbx]) 440)
    (io (u₁.wr.trans b.wr) _ (by omega)) fun s₂ u₂ => ?_
  refine wp_movm (ea_sc (by rw [u₂.other _ (by decide), u₁.other _ (by decide), b.rbx]) 448)
    (io (u₂.wr.trans (u₁.wr.trans b.wr)) _ (by omega)) fun s₃ u₃ => ?_
  refine wp_movm (ea_sc (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), b.rbx]) 456)
    (io (u₃.wr.trans (u₂.wr.trans (u₁.wr.trans b.wr))) _ (by omega)) fun s₄ u₄ => ?_
  refine wp_movm (ea_sc (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), b.rbx]) 464)
    (io (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans (u₁.wr.trans b.wr)))) _ (by omega)) fun s₅ u₅ => ?_
  refine wp_movm (ea_sc (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), b.rbx]) 424)
    (io (u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans (u₁.wr.trans b.wr))))) _ (by omega))
    fun s₆ u₆ => WP.block_nil ⟨?_, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · rw [u₆.gpr, m₅]; exact sv (.rbx, 424) (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]; exact sv (.rbp, 432) (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), b.rsp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.mem]; exact sv (.r12, 440) (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
    exact sv (.r13, 448) (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
    exact sv (.r14, 456) (by decide)
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact sv (.r15, 464) (by decide)

theorem epi_post {s : State} (h : Done s₀ s) {s' : State}
    (h' : (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem) :
    gprPreserved s₀ s' ∧ Proof.Pbkdf2.pbkdf2Sha256X86_64.post s₀ s' := by
  refine ⟨⟨h'.1, by rw [h'.2]; exact h.1.ret_eq hp⟩, ?_⟩
  show Spec.Pbkdf2.pbkdf2HmacSha256 (P s₀) (S s₀) (cc s₀) (ol s₀) = some (bytesAt s'.mem (op s₀) (ol s₀))
  unfold Spec.Pbkdf2.pbkdf2HmacSha256 Spec.Pbkdf2.pbkdf2
  split
  · rename_i hc; have := hp.len; omega
  · rw [h'.2, h.2, show ol s₀ + 32 - 1 = ol s₀ + 31 by omega]
    rfl

include hv in
theorem correct (sfx : String) :
    WP isa (derive f sfx) s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Pbkdf2.pbkdf2Sha256X86_64.post s₀ s' :=
  WP.seq (WP.mono (prologue_ok hp) fun _ h1 => WP.seq (WP.mono (key_ok hp hv sfx h1) fun _ h2 =>
    WP.seq (WP.mono (keySalt_ok hp hv sfx h2) fun _ h3 => WP.seq (WP.mono (setup_ok hp h3) fun _ h4 =>
      WP.seq (WP.mono (blocks_ok hp hv sfx h4) fun _ h5 =>
        WP.mono (epilogue_ok hp h5) fun _ h6 => epi_post hp h5 h6)))))

end

end VG.Proof.Pbkdf2.X86_64.Derive
