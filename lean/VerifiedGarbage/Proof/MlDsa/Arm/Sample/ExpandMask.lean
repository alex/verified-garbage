import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.ExpandMask
import VerifiedGarbage.Proof.Framework.Arm.Inline

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_expand_mask_poly`

Untrusted: everything here is checked by Lean. The function runs in pieces:
the prologue (`J0`), the sponge, whose output is `H(ρ′, 640)` (`J6`), the
branch on `γ₁`, and the loop of `vg_mldsa_bit_unpack` for
`c = 1 + bitlen (γ₁ - 1)` on the first `32c` bytes of output
(`Pack.unpackLoop_buFin_ok`, run from the state permitted only those bytes
and `a`, and widened to the function's permissions by `Exec.widen`), which
are `H(ρ′, 32c)` (`H_take`). It is constant time: the taint analysis proves
each piece but the sponge, whose proof is `sponge_ct`, from the pointers
and `γ₁`.
-/

namespace VG.Proof.MlDsa.Arm.Sample.ExpandMask

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.Arm.Pack (unpackLoop buFin)
open VG.Spec.MlDsa (Zq q H PolyIs toRq bitUnpack bitlen)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `seed = r0`, `gamma1 = r1`, `a = r2`,
`scratch = r3`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r0, 66, σ.gpr .r3, σ.gpr .r2, σ.gpr .r1⟩

/-- `γ₁`. -/
abbrev gam (σ : State) : Nat := (σ.gpr .r1).toNat

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) 66

/-- What the proofs need of the entry state. -/
structure Pre (σ : State) : Prop where
  ok : SpOk (spOf σ) σ
  g : gam σ = 2 ^ 17 ∨ gam σ = 2 ^ 19

/-- What the function writes. -/
abbrev Out (σ : State) : Spec.MlDsa.Poly :=
  toRq (bitUnpack (H (B σ) (32 * (1 + bitlen (gam σ - 1)))) (gam σ - 1) (gam σ))

/-- After the loop. -/
structure EDone (σ : State) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : PolyIs s.mem (spOf σ).A (Out σ)

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- The loop of `BitUnpack` for `(B, d, c, nb)`, from the output of the
sponge. -/
theorem loop_ok {Bv d c nb : Nat} (hs : Pack.Shape d c nb) (hB : encodable (BitVec.ofNat 32 Bv) = true)
    (hB19 : Bv ≤ 2 ^ 19) (hd : bitlen (Bv - 1 + Bv) = d) (h32 : 32 * d ≤ 640) {s : State}
    (h : J6 136 640 (spOf σ) σ s) :
    WP isa (.seq (.block [.dp .add .r0 .r6 (.imm 840), .mov .r1 (.reg .r5)]) (unpackLoop (buFin Bv) d c nb)) s
      fun s' => Env (spOf σ) σ s' ∧ PolyIs s'.mem (spOf σ).A (toRq (bitUnpack (H (B σ) (32 * d)) (Bv - 1) Bv)) := by
  have fs := hp.fscr
  refine WP.seq (WP.mono (Q := fun s1 : State => s1.gpr .r0 = s.gpr .r6 + BitVec.ofNat 32 840 ∧ s1.gpr .r1 = s.gpr .r5 ∧
      s1.gpr .r5 = s.gpr .r5 ∧ s1.gpr .r6 = s.gpr .r6 ∧ s1.mem = s.mem ∧ s1.rd = s.rd ∧ s1.wr = s.wr ∧
      s1.sp = s.sp) (by run_block [and_self, and_true, true_and]; rfl) fun s1 ⟨g0, g1, g5, g6, m, rd, wr, sp⟩ => ?_)
  have e1 := h.env.same m g5 g6 rd wr sp
  have a0 : State.addr (s1.gpr .r0) = (spOf σ).at' 840 := by rw [g0, h.env.r6]; exact at_eq hp (by omega)
  have a1 : State.addr (s1.gpr .r1) = (spOf σ).A := by rw [g1, h.env.r5]
  let src : Region := ⟨State.addr (s1.gpr .r0), 32 * d⟩
  let t := s1.withRegions [src] [polyR (State.addr (s1.gpr .r1))]
  have hsep : src.Disjoint (polyR (State.addr (s1.gpr .r1))) := by
    show Region.Disjoint ⟨State.addr (s1.gpr .r0), 32 * d⟩ (polyR (State.addr (s1.gpr .r1)))
    rw [a0, a1]; exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 32 * d) (by omega))).symm
  have fit0 : (s1.gpr .r0).toNat + 32 * d ≤ 2 ^ 32 := by
    rw [g0, h.env.r6, BitVec.toNat_add, toNat_ofNat32 (by omega)]; omega
  have fit1 : (s1.gpr .r1).toNat + 1024 ≤ 2 ^ 32 := by rw [g1, h.env.r5]; exact hp.fa
  obtain ⟨tr, t', he, hpoly, hf, hk⟩ := Pack.unpackLoop_buFin_ok (s := t) (a := Bv - 1) hs hB hB19 hd
    (List.mem_append_left _ (List.mem_singleton_self _)) (List.mem_singleton_self _) hsep fit0 fit1
  have hc : Covers (t.rd ++ t.wr) (s1.rd ++ s1.wr) := by
    refine Covers.of_sub fun r hr => ?_
    simp only [t, State.withRegions_rd, State.withRegions_wr, List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨(spOf σ).scrR, List.mem_append_right _ (by rw [e1.wr, hp.wr]; simp), 840, a0, by show 840 + 32 * d ≤ 2048; omega⟩
    · exact ⟨(spOf σ).aR, List.mem_append_right _ (by rw [e1.wr, hp.wr]; simp), 0,
        by rw [a1]; exact (add_ofNat_zero _).symm, by simp⟩
  have hw : Covers t.wr s1.wr := by
    intro x k ⟨r, hr, hcr⟩
    simp only [t, State.withRegions_wr, List.mem_singleton] at hr
    subst hr
    rw [a1] at hcr
    exact ⟨(spOf σ).aR, by rw [e1.wr, hp.wr]; simp, hcr⟩
  have he' := Exec.widen he hc hw
  simp only [t, State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨tr, _, he', ?_, ?_⟩
  · have hf' : Frame [(spOf σ).aR] s1.mem t'.mem := by
      have := hf
      simp only [t, State.withRegions_gpr, State.withRegions_mem] at this
      rw [a1] at this; exact this
    exact e1.step hp hf' (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
      (hk.gpr (by decide)) (hk.gpr (by decide)) rfl rfl (hk.2.2.2)
  · show PolyIs t'.mem _ _
    rw [← a1]
    have eb : bytesAt t.mem (State.addr (t.gpr .r0)) (32 * d) = H (B σ) (32 * d) := by
      show bytesAt s1.mem (State.addr (s1.gpr .r0)) (32 * d) = _
      rw [a0, m, ← MlKem.bytesAt_take _ _ (show 32 * d ≤ 640 by omega), h.out, ← H_eq, H_take _ (by omega)]
    rw [eb] at hpoly
    exact hpoly

/-- The branch on `γ₁` and the loop. -/
theorem tail_ok (hg : gam σ = 2 ^ 17 ∨ gam σ = 2 ^ 19) {s : State} (h : J6 136 640 (spOf σ) σ s) :
    WP isa (.seq (.block [.cmp .r7 (.imm 0x20000)]) (.ite .eq (emLoop 18) (emLoop 20))) s (EDone σ) := by
  refine WP.seq (WP.mono (Q := fun s1 : State => s1.z = decide (gam σ = 2 ^ 17) ∧ s1.gpr = s.gpr ∧ s1.mem = s.mem ∧
      s1.rd = s.rd ∧ s1.wr = s.wr ∧ s1.sp = s.sp) ?_ fun s1 ⟨z1, g, m, rd, wr, sp⟩ => ?_)
  · have e : (s.gpr .r7 - 0x20000 == 0) = decide (gam σ = 2 ^ 17) := by
      rw [h.r7]
      show (σ.gpr .r1 - BitVec.ofNat 32 131072 == 0) = _
      rw [cmp_z _ 131072 (by decide)]
    run_block [e, and_self, and_true, true_and]
  have h1 : J6 136 640 (spOf σ) σ s1 :=
    ⟨h.env.same m (by rw [g]) (by rw [g]) rd wr sp, by rw [g]; exact h.r7, by rw [m]; exact h.out⟩
  refine WP.ite s1.z rfl (fun e => ?_) (fun e => ?_)
  · have hγ : gam σ = 2 ^ 17 := by rw [z1] at e; simpa using e
    refine WP.mono (loop_ok hp (Bv := 131072) (c := 4) (nb := 9) (by constructor <;> decide) (by decide) (by decide)
      (by decide) (by decide) h1) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [Out, hγ]; exact hpo
  · have hγ : gam σ = 2 ^ 19 := by rw [z1] at e; simp at e; omega
    refine WP.mono (loop_ok hp (Bv := 524288) (c := 2) (nb := 5) (by constructor <;> decide) (by decide) (by decide)
      (by decide) (by decide) h1) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [Out, hγ]; exact hpo

end

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct {σ : State} (hp : Pre σ) : WP isa Impl.MlDsa.Arm.Sample.expandMask σ fun s' =>
    PolyIs s'.mem (State.addr (σ.gpr .r2)) (Out σ) ∧ abiPreserved σ s' :=
  WP.seq (WP.mono (pro_rb hp.ok rfl rfl rfl rfl rfl) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok hp.ok (rate := 136) (outlen := 640) (by decide) (by decide) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (tail_ok hp.ok hp.g h2) fun _ h3 =>
        WP.mono (epi_ok' hp.ok h3.env) fun _ ⟨hm, ha⟩ => ⟨by rw [hm]; exact h3.out, ha⟩)))

/-! ## Constant time -/

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : Pre σ₁
  p₂ : Pre σ₂
  sp : σ₁.sp = σ₂.sp
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3

theorem all_ct {σ₁ σ₂ : State} (two : Two σ₁ σ₂) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.Arm.Sample.expandMask fun _ _ => True := by
  have hP : spOf σ₁ = spOf σ₂ := by simp only [spOf, two.r0, two.r1, two.r2, two.r3]
  have ok₂ : SpOk (spOf σ₁) σ₂ := hP ▸ two.p₂.ok
  refine RelCT.seq (R := fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₁) σ₂ b) (relW (taintRel [.r0, .r1, .r2, .r3]
      (fun a b h r hr => by
        rw [h.1, h.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [two.r0, two.r1, two.r2, two.r3]) (by taint_decide))
    fun a b h => ⟨by rw [h.1]; exact pro_rb two.p₁.ok rfl rfl rfl rfl rfl,
      by rw [h.2]; exact pro_rb ok₂ two.r0.symm two.r1.symm two.r2.symm two.r3.symm rfl⟩) ?_
  refine RelCT.seq (R := fun a b => J6 136 640 (spOf σ₁) σ₁ a ∧ J6 136 640 (spOf σ₂) σ₂ b)
    ((sponge_ct two.p₁.ok ok₂ two.sp (rate := 136) (outlen := 640) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide)).mono (fun _ _ h => h)
      fun a b h => ⟨h.1, hP ▸ h.2⟩) ?_
  refine RelCT.seq (R := fun a b => EDone σ₁ a ∧ EDone σ₂ b) (relW (taintRel [.r5, .r6, .r7]
      (fun a b h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.env.r5, h.2.env.r5, hP]
        · rw [h.1.env.r6, h.2.env.r6, hP]
        · rw [h.1.r7, h.2.r7, hP]) (by taint_decide))
    fun a b h => ⟨tail_ok two.p₁.ok two.p₁.g h.1, tail_ok two.p₂.ok two.p₂.g h.2⟩) ?_
  exact taintRel [.r6] (fun a b h r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6, hP]) (by taint_decide)

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlDsa.expandMaskContract Arm.abi 8).pre s) : Pre s := by
  sig_pre [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, b1, b2, b3, f1, f2, f3, hg⟩ := h
  exact ⟨⟨by rw [hrd]; exact List.mem_singleton_self _, hwr, d1, d2, d3, b1, b2, b3, f1, by show (66 : Nat) < 2 ^ 32; decide, f2, f3, h8⟩, hg⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x20000 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.Arm.Sample.ExpandMask

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open ExpandMask

theorem expandMask_verified :
    Verified Arm.target Impl.MlDsa.Arm.Sample.expandMask (Spec.MlDsa.expandMaskContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpoly, hpres⟩ := correct (pre_of hs)
    refine ⟨t, s', he, hpres, ?_⟩
    sig_post [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact hpoly
  · sig_pub [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, h0, h1, h2, h3⟩ := hpub
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlDsa.Arm.Sample
