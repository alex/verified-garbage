import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base

/-!
# Ed25519 public-key derivation on x86-64: correctness

The frame's body leaves the public key in `out` (`body_ok`), and the whole
function, for any implementation `v` of the SHA-512 compression function,
meets `pkLocal` and the ABI (`publicKey_ok`).
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem zero_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkZero) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem := by
  apply WP.of_runBlock
  simp only [pkZero, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), rfl⟩

theorem wipe_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkWipe) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem := by
  rw [pkWipe, WP.block_append_iff]
  refine WP.mono (zero_ok hc) fun u ⟨hu, hm⟩ => ?_
  exact WP.mono (stores_ok hu) fun u' ⟨hu', hf, _⟩ => ⟨hu', hm ▸ hf⟩

/-- `SHA-512(seed)` at `scratch + 1568`. -/
theorem hash_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (pkHash v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1568) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) :=
  WP.seq (WP.mono (init_step hL hc) fun _ ⟨hc₁, hr₁⟩ =>
    WP.seq (WP.mono (upd_step v hL hc₁ hr₁) fun _ ⟨hc₂, hr₂⟩ => fin_step v hL hc₂ hr₂))

/-- The public key of the seed in `out`. -/
theorem body_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (pkBody fld fs v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem L.out 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine WP.seq (WP.mono (hash_ok v hL hc) fun t₁ ⟨hc₁, hh₁⟩ => ?_)
  refine WP.seq (WP.mono (baseArgs_ok hc₁) fun t₂ ⟨hc₂, hm₂, ha₂⟩ => ?_)
  refine WP.seq (WP.mono (prune_ok hc₂ ha₂ (hm₂ ▸ hh₁)) fun t₃ ⟨hc₃, _, ha₃, hs⟩ => ?_)
  refine WP.seq (WP.mono (base_ok hL hc₃ ha₃ hs) fun t₃ ⟨hc₃, ho₃⟩ => ?_)
  refine WP.mono (wipe_ok hc₃) fun t₄ ⟨hc₄, hf₄⟩ => ⟨hc₄, ?_⟩
  rw [Spec.Ed25519.publicKey, Spec.Ed25519.expandSecret, ← ho₃]
  simp only [Spec.Ed25519.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact Frame.bytes (R := L.OUT) hf₄ (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hL.stk_OUT (d := 16) (n := 32) (by omega)).symm) (by show (32 : Nat) ≤ 2 ^ 64; decide)
    (List.mem_range.mp hi)

theorem pop_rsp (B : Addr) : B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (8 * 7) = B + BitVec.ofNat 64 72 := by
  rw [add_add]

/-- `vg_ed25519_public_key` meets `pkLocal` and the ABI. -/
theorem publicKey_ok (v : Compress) {s : State} (h : pkLocal.pre s) :
    WP isa (publicKey fld fs v.callee v.suffix) s fun s' => abiPreserved s s' ∧ pkLocal.post s s' := by
  have hL := lay_ok h
  have hc := push_ctx h
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide) (by show 8 * 7 ≤ _; have := h.1; omega)
    (WP.mono (body_ok v hL hc) fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 7 from rfl, pop_rsp, lay_ret]
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega) (by omega)
  · show Spec.Ed25519.bytesAt (popped .rax pushRs.length u).mem (lay s).out 32 = _
    rw [popped_mem, ho]
    rfl

end VG.Proof.Ed25519.X86_64.PublicKey
