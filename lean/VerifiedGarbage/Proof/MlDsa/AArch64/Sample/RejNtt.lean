import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_ntt_poly`

Untrusted: everything here is checked by Lean. Correctness: the function
runs in pieces, the prologue (`J0`), the sponge, whose output is
`G(ρ, 1008)` (`J6`), `a` set to zeros, the loop, which stores the
coefficients `rnFold` samples from it (`RejNttLoop.lean`), and the end,
which returns whether there are 256 of them. The postcondition of the
contract follows from the prefix lemmas (`rejNTT_some`, `rejNTT_none`).

Constant time up to the seed, relating two runs piece by piece (`Rel.lean`):
the prologue, the sponge, the zeros and the end by the taint analysis, from
registers that correctness makes equal in both runs; the loop by `memTaint`,
since both runs have the same output (a function of the seed, which the
contract lets the function leak) and zeros in `a`, and the loop touches
nothing else.
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep only_write wp_nil wp_subImm wp_lsr ptr_add toNat_lsr toNat_sub_n agree_of)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G PolyIs coeffAt)
open VG.Spec.Sha3 (bytesAt shakeSuffix)

/-- `vg_mldsa_rej_ntt_poly(seed = x0, a = x1, scratch = x2) -> w0`, with 16
bytes of stack below `sp`: the contract the proof is written against. -/
def rnK : Contract isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 34⟩
    let a : Region := ⟨s.gpr .x1, 1024⟩
    let scratch : Region := ⟨s.gpr .x2, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [seed] ∧ s.wr = [a, scratch] ∧ seed.Disjoint a ∧ seed.Disjoint scratch ∧
    a.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint a ∧
    stack.Disjoint scratch
  post s s' :=
    (s'.gpr .x0).setWidth 32 =
        (if (rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256 then 1 else 0) ∧
      ((rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256 →
        PolyIs s'.mem (s.gpr .x1) (toPoly (rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008))))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp ∧ bytesAt s₁.mem (s₁.gpr .x0) 34 = bytesAt s₂.mem (s₂.gpr .x0) 34

namespace RejNtt

/-- The call. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .x0, 34, σ.gpr .x2, σ.gpr .x1, 0⟩

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := G ((spOf σ).msg σ) 1008

theorem X_length (σ : State) : (X σ).length = 1008 := G_length _ _

theorem spOk {σ : State} (hp : rnK.pre σ) : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2, by show (34 : Nat) < 2 ^ 64; decide⟩

theorem pro_ok {σ : State} (hp : rnK.pre σ) :
    WP isa (.block (pro .x2 .x1 (.movz .x .x27 0 0) (.movz .x .x4 34 0))) σ (J0 (spOf σ) σ) :=
  Sample.pro_ok (spOk hp) rfl rfl (by decide) rfl
    (fun s _ => ⟨_, rfl, only_write _ _ _ _, by rfl⟩)
    (fun s _ => ⟨_, rfl, only_write _ _ _ _, by rfl⟩)

/-- After the sponge, and `a` set to zeros. -/
structure Z (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 1008 = X σ
  zero : ∀ i < 256, coeffAt s.mem (σ.gpr .x1) i = 0

theorem zero_ok {σ s : State} (hp : rnK.pre σ) (h : J6 168 1008 (spOf σ) σ s) :
    WP isa zeroPoly s (Z σ) :=
  WP.mono (zeroPoly_ok (fun i hi => inA (spOk hp) h.env.wr hi) h.env.x26) fun u ⟨k, z, f⟩ =>
    ⟨h.env.keepA (spOk hp) k f, by
      rw [MlKem.bytesAt_frame f (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (a_scr' (spOk hp) (by omega)).symm) (by omega), h.out,
        (G_eq _ _).symm], z⟩

theorem lpre {σ s : State} (hp : rnK.pre σ) (h : Z σ s) :
    RejNtt.LPre (X σ) ((spOf σ).at' 840) (σ.gpr .x1) s :=
  ⟨fun p hp' => by rw [← h.out, MlKem.bytesAt_getD _ _ hp'],
    fun p hp' => by rw [at_add]; exact inScrRd (spOk hp) h.env.rd h.env.wr (by omega),
    fun i hi => inA (spOk hp) h.env.wr hi, (a_scr' (spOk hp) (by omega)).symm,
    by rw [h.env.x25], h.env.x26⟩

/-- After the loop. -/
structure LP (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  x4 : (s.gpr .x4).toNat = 256 - (rnFold [] (X σ)).length
  st : Stored s.mem (σ.gpr .x1) (rnFold [] (X σ))

theorem loopP_ok {σ s : State} (hp : rnK.pre σ) (h : Z σ s) : WP isa rnLoop s (LP σ) :=
  WP.mono (RejNtt.loop_ok (X_length σ) (lpre hp h)) fun u hu => by
    have x4 := hu.x4
    have st := hu.st
    rw [RejNtt.Lt_336 (X_length σ)] at x4 st
    exact ⟨h.env.keepA (spOk hp) hu.keep hu.frame, x4, st⟩

/-- The end: the postcondition, and the calling convention. -/
theorem end_ok {σ s : State} (hp : rnK.pre σ) (h : LP σ s) :
    WP isa (.block (retZ ++ epi)) s fun s' => abiPreserved σ s' ∧ rnK.post σ s' := by
  rw [retZ, List.cons_append, List.cons_append, List.nil_append]
  refine wp_subImm (by decide) fun s₁ h₁ e₁ => wp_lsr (by decide) fun s₂ h₂ e₂ => ?_
  have hl := rnFold_length_le (a := ([] : List Zq)) (by simp) (X σ)
  have v0 : (s₂.gpr .x0).toNat = if (rnFold [] (X σ)).length = 256 then 1 else 0 := by
    have one : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [e₂, toNat_lsr, e₁, BitVec.toNat_sub, h.x4, one]
    simp only [VG.Spec.MlDsa.n, Nat.reducePow] at hl ⊢
    split <;> omega
  have e1 := (h.env.keep (h₁.keep.trans h₂.keep) (by rw [h₂.mem, h₁.mem]))
  refine WP.mono (epi_ok (spOk hp) e1) fun s' ⟨abi, m, k⟩ => ⟨abi, ?_, fun hf => ?_⟩
  · rw [k.get .x0]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, v0]
    split <;> rfl
  · rw [m, h₂.mem, h₁.mem]
    exact stored_polyIs h.st hf

theorem correct (σ : State) (hp : rnK.pre σ) :
    ∃ t s', Exec isa rejNTT σ t s' ∧ abiPreserved σ s' ∧ rnK.post σ s' :=
  WP.seq (WP.mono (pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok (spOk hp) (rate := 168) (outlen := 1008) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (zero_ok hp h2) fun _ h3 =>
        WP.seq (WP.mono (loopP_ok hp h3) fun _ h4 => end_ok hp h4))))

end RejNtt

end VG.Proof.MlDsa.AArch64.Sample
