import VerifiedGarbage.Proof.MlKem.AArch64.SampleSqueeze
import VerifiedGarbage.Proof.MlKem.AArch64.MemTaint

/-!
# ML-KEM on AArch64: `vg_mlkem_sample_ntt`

`sampleFull`, from any state satisfying the precondition, is `phaseA_ok` (the
SHAKE128 output, `a` zero) followed by `loop_ok` (`full_ok`). `sampleFast` is
the same with 504 bytes and 168 iterations (`fast_ok`); if they leave 256
coefficients, they are `SampleNTT`'s (`sampleNTT_of_full`), and otherwise
`sampleFull` runs from the original arguments, which `sampleRetry` restores
(`retry_ok`).

Constant time up to the seed, relating two runs (`RelCT`) from states that
agree on the pointers and on the seed: up to each loop, the taint analysis
(through the Keccak calls); then, by correctness, both runs have the same
SHAKE128 output (a function of the seed) in `scratch` and zeros in `a`, so
the loop, which touches nothing else, runs with permissions on only memory
both runs agree on (`RelCT.narrow`), where `memTaint` proves it leaks the
same (its branches depend on the output). By correctness again, both runs
of `sampleFast` leave the same number of coefficients, on which the retry
branches, and the retry is `sampleFull` from states that satisfy its
contract (`full_ct`).
-/

namespace VG.Proof.MlKem.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem phaseA_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : Pre s₀) :
    WP isa (sampleSqueezeWith v.callee) s₀ fun u => LPre 280 (Bs s₀) (So s₀ 0) (aP s₀) u ∧ Fin s₀ u :=
  WP.seq (WP.mono (prologue_ok hp) fun _ h => calls_ok v hp h (by decide) (by decide) fun _ m b =>
    rest_ok hp m b)

theorem pres_loop : ∀ r ∈ preserved, r ∉ (Reg.x0 :: lRegs) := by decide

/-- What the code guarantees: `sampleStrong`'s postcondition, and the ABI. -/
def Post (s₀ s' : State) : Prop :=
  abiPreserved s₀ s' ∧ Reduced s'.mem (aP s₀) ∧
    ((s'.gpr .x0 = 1 ∧ sampleNTT 280 (Bs s₀) = some (polyAt s'.mem (aP s₀))) ∨
      (s'.gpr .x0 = 0 ∧ sampleNTT 280 (Bs s₀) = none))

theorem full_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : Pre s₀) : WP isa (sampleFullWith v.callee) s₀ (Post s₀) := by
  refine WP.seq (WP.mono ((phaseA_ok v) hp) fun u ⟨hl, hf⟩ => WP.mono (loop_ok hl) fun s' ⟨k, _, res⟩ => ?_)
  refine ⟨⟨fun r hr => ?_, ?_, fun r hr => (k.vcs r hr).trans (hf.vcs r hr)⟩, res.1, ?_⟩
  · rw [k.gpr r (pres_loop r hr), hf.cs r hr]
  · rw [k.sp, hf.sp]
  rcases res.2 with ⟨h0, hpoly, hs⟩ | ⟨h0, hn⟩
  · exact .inl ⟨h0, by rw [hpoly.2]; exact hs⟩
  · exact .inr ⟨h0, hn⟩

/-! ## `sampleFast` -/

theorem fastA_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : Pre s₀) :
    WP isa ((sampleSqueezeNWith v.callee) 504 (sampleRegs 168)) s₀ fun u =>
      LPre 168 (Bs s₀) (So s₀ 0) (aP s₀) u ∧ MidA s₀ u :=
  WP.seq (WP.mono (prologue_ok hp) fun _ h => calls_ok v hp h (by decide) (by decide) fun _ m b =>
    WP.seq (restN_ok hp (by decide) (by decide) (by decide) m b))

/-- What `sampleFast` leaves: our caller's registers still saved, and the
coefficients of 168 iterations in `a`. -/
structure FastPost (s₀ u : State) : Prop where
  mid : MidA s₀ u
  len : (LA (Bs s₀) 168).length ≤ 256
  x4 : (u.gpr .x4).toNat = 256 - (LA (Bs s₀) 168).length
  coeffs : Coeffs u.mem (aP s₀) (LA (Bs s₀) 168)

theorem fastLoop_ok {s₀ : State} (hp : Pre s₀) {u : State} (hl : LPre 168 (Bs s₀) (So s₀ 0) (aP s₀) u)
    (hm : MidA s₀ u) : WP isa (.loop sampleBody (.nonzero .x .x5)) u (FastPost s₀) :=
  WP.mono (iters_ok (by decide) hl) fun _ hv =>
    ⟨MidA.keep hp hm hv.keep hv.acc.frame, hv.acc.len, hv.acc.x4, hv.acc.coeffs⟩

theorem fast_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : Pre s₀) : WP isa (sampleFastWith v.callee) s₀ (FastPost s₀) :=
  WP.seq (WP.mono ((fastA_ok v) hp) fun _ ⟨hl, hm⟩ => fastLoop_ok hp hl hm)

/-- 256 coefficients after 168 iterations: 1, and `SampleNTT`. -/
theorem done_ok {s₀ : State} (hp : Pre s₀) {u : State} (h : FastPost s₀ u)
    (hz : (u.gpr .x4).toNat = 0) : WP isa (.block sampleDone) u (Post s₀) := by
  have hf : (LA (Bs s₀) 168).length = 256 := by have := h.x4; have := h.len; omega
  refine wp_movz fun u₁ h₁ e₁ => ?_
  have m₁ : MidA s₀ u₁ := MidA.keep hp h.mid h₁.keep (by rw [h₁.mem]; exact Frame.refl _ _)
  refine WP.mono (restore_ok hp m₁ (P := fun v => v.gpr .x0 = 1 ∧ v.mem = u.mem)
    fun v hk hm => ⟨by rw [hk.get .x0, e₁]; rfl, by rw [hm, h₁.mem]⟩) fun s' ⟨⟨h0, hm⟩, hfin⟩ => ?_
  have hc := h.coeffs.full hf
  rw [hf] at hc
  refine ⟨⟨hfin.cs, hfin.sp, hfin.vcs⟩, ?_, .inl ⟨h0, ?_⟩⟩
  · rw [hm]; exact reduced_of_coeffs (L := LA (Bs s₀) 168) (by rw [hf]; exact hc)
  · rw [sampleNTT_of_full (by decide : 168 ≤ 280) hf]
    refine congrArg some ?_
    exact ((CoeffsUpTo.polyIs (by rw [hm]; exact hc) fun i hi => cv_toPoly hi).2).symm

/-- The original arguments, restored for `sampleFull`. -/
structure RetryPost (s₀ v : State) : Prop where
  rd : v.rd = s₀.rd
  wr : v.wr = s₀.wr
  sp : v.sp = s₀.sp
  x0 : v.gpr .x0 = sdP s₀
  x1 : v.gpr .x1 = aP s₀
  x2 : v.gpr .x2 = scP s₀
  cs : ∀ r ∈ preserved, v.gpr r = s₀.gpr r
  seed : bytesAt v.mem (sdP s₀) 34 = Bs s₀
  vcs : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

theorem retryBlock_ok {s₀ : State} (hp : Pre s₀) {u : State} (h : FastPost s₀ u) :
    WP isa (.block sampleRetry) u (RetryPost s₀) := by
  rw [sampleRetry, WP.block_append_iff]
  refine wp_mov fun u₁ h₁ e₁ => wp_mov fun u₂ h₂ e₂ => wp_mov fun u₃ h₃ e₃ => wp_nil ?_
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : MidA s₀ u₃ := MidA.keep hp h.mid k₃ (by rw [h₃.mem, h₂.mem, h₁.mem]; exact Frame.refl _ _)
  refine WP.mono (restore_ok hp m₃ (P := fun v => v.gpr .x0 = sdP s₀ ∧ v.gpr .x1 = aP s₀ ∧
    v.gpr .x2 = scP s₀ ∧ v.mem = u₃.mem) fun v hk hm => ⟨?_, ?_, ?_, hm⟩)
    fun v ⟨⟨e0, e1, e2, hm⟩, hfin⟩ => ⟨hfin.rd, hfin.wr, hfin.sp, e0, e1, e2, hfin.cs, by rw [hm]; exact m₃.seed, hfin.vcs⟩
  · rw [hk.get .x0, h₃.get .x0, h₂.get .x0, e₁, h.mid.x24]
  · rw [hk.get .x1, h₃.get .x1, e₂, h₁.get .x25, h.mid.x25]
  · rw [hk.get .x2, e₃, h₂.get .x26, h₁.get .x26, h.mid.x26]

theorem RetryPost.pre {s₀ v : State} (hp : Pre s₀) (h : RetryPost s₀ v) : sampleAArch64.pre v := by
  simp only [sampleAArch64, h.x0, h.x1, h.x2, h.rd, h.wr, h.sp]
  exact ⟨hp.rd, hp.wr, hp.d_sa, hp.d_ss, hp.d_as, hp.sp16, hp.k_s, hp.k_a, hp.k_c⟩

/-- Fewer: the original arguments back, and `sampleFull` from them. -/
theorem retry_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : Pre s₀) {u : State} (h : FastPost s₀ u) :
    WP isa (.seq (.block sampleRetry) (sampleFullWith v.callee)) u (Post s₀) := by
  refine WP.seq (WP.mono (retryBlock_ok hp h) fun u₁ hv => ?_)
  refine WP.mono ((full_ok v) (pre_of (hv.pre hp))) fun s' ⟨⟨cs, sp, vcs⟩, red, res⟩ => ?_
  have hB : Bs u₁ = Bs s₀ := by simp only [Bs, sdP, hv.x0]; exact hv.seed
  refine ⟨⟨fun r hr => by rw [cs r hr, hv.cs r hr], by rw [sp, hv.sp], fun r hr => (vcs r hr).trans (hv.vcs r hr)⟩, ?_, ?_⟩
  · simpa only [aP, hv.x1] using red
  · simpa only [aP, hv.x1, hB] using res

theorem strong_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : Pre s₀) : WP isa (sampleNTTWith v.callee) s₀ (Post s₀) := by
  refine WP.seq (WP.mono ((fast_ok v) hp) fun u h => ?_)
  refine WP.ite (u.gpr .x4 == 0) (eval_zero _ _) (fun hz => ?_) (fun _ => (retry_ok v) hp h)
  rw [eq_zero_iff, decide_eq_true_eq] at hz
  exact done_ok hp h hz

theorem correct (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : Pre s₀) :
    WP isa (sampleNTTWith v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ sampleAArch64.post s₀ s' := by
  refine WP.mono ((strong_ok v) hp) fun s' ⟨abi, red, res⟩ => ⟨abi, ?_⟩
  rcases res with ⟨h0, hs⟩ | ⟨h0, hn⟩
  · have r1 : (s'.gpr .x0).setWidth 32 = 1 := by rw [h0]; rfl
    exact ⟨fun _ => red, outcome_of_min (.inl ⟨r1, hs⟩)⟩
  · have r0 : (s'.gpr .x0).setWidth 32 = 0 := by rw [h0]; rfl
    refine ⟨fun h => ?_, outcome_of_min (.inr ⟨r0, hn⟩)⟩
    rw [r0] at h; cases h

/-! ## Constant time -/

/-- The bytes of a polynomial of zeros are zero. -/
theorem byte_zero {m : Mem} {p : Addr} (h : ∀ i < 256, coeffAt m p i = 0) {y : Addr}
    (hy : (polyRegion p).Contains y 1) : m y = 0 := by
  simp only [Region.Contains] at hy
  have e : y = coeffAddr p ((y - p).toNat / 4) + BitVec.ofNat 64 ((y - p).toNat % 4) := by
    rw [coeffAddr, ptr_add, show 4 * ((y - p).toNat / 4) + (y - p).toNat % 4 = (y - p).toNat by omega]
    bv_omega
  rw [e, Mem.readW_byte m _ (by omega), ← coeffAt_eq, h _ (by omega)]
  ext i hi
  simp

/-- A byte of a region, at its offset. -/
theorem at_off {b y : Addr} {len : Nat} (hy : (⟨b, len⟩ : Region).Contains y 1) :
    ∃ p < len, y = b + BitVec.ofNat 64 p := by
  simp only [Region.Contains] at hy
  exact ⟨(y - b).toNat, by omega, by bv_omega⟩

/-- The loop's regions. -/
abbrev lrd (N : Nat) (bP : Addr) : List Region := [⟨bP, 3 * N⟩]
abbrev lwr (aP : Addr) : List Region := [polyRegion aP]

theorem LPre.narrow {N : Nat} {B : List Byte} {bP aP : Addr} {s : State} (h : LPre N B bP aP s) :
    LPre N B bP aP (s.withRegions (lrd N bP) (lwr aP)) :=
  ⟨h.buf, fun p hp => in_rd (in_regions (List.mem_singleton_self _)
      (contains_off (by omega) (by have := h.bound; omega))),
    fun i hi => in_regions (List.mem_singleton_self _) (coeff_contains _ (show i < n from hi)),
    h.disj, h.zero, h.x2, h.x3, h.x4, h.x5, h.x9, h.x10, h.bound⟩

/-- Two runs of the loop from the same output and zeros agree on what
`memTaint` tracks. -/
theorem iters_agree {N : Nat} {B : List Byte} {bP aP : Addr} {u₁ u₂ : State}
    (h₁ : LPre N B bP aP u₁) (h₂ : LPre N B bP aP u₂) (hsp : u₁.sp = u₂.sp) :
    memTaint.Agree (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10]) (u₁.withRegions (lrd N bP) (lwr aP))
      (u₂.withRegions (lrd N bP) (lwr aP)) := by
  have n4 : ∀ {a b : BitVec 64} {k : Nat}, a.toNat = k → b.toNat = k → a = b :=
    fun ha hb => BitVec.eq_of_toNat_eq (ha.trans hb.symm)
  refine ⟨agree_of (by simp only [State.withRegions_sp]; exact hsp) fun r hr => ?_, rfl, rfl,
    fun y hy => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [State.withRegions_gpr]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.x2, h₂.x2]
    · rw [h₁.x3, h₂.x3]
    · exact n4 h₁.x4 h₂.x4
    · exact n4 h₁.x5 h₂.x5
    · exact n4 h₁.x9 h₂.x9
    · exact n4 h₁.x10 h₂.x10
  · simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem] at hy ⊢
    obtain ⟨R, hR, hc⟩ := hy
    rcases mem2 hR with rfl | rfl
    · obtain ⟨p, hp, rfl⟩ := at_off hc
      rw [h₁.buf p hp, h₂.buf p hp]
    · rw [byte_zero h₁.zero hc, byte_zero h₂.zero hc]

/-- The loop's regions are the parts of `scratch` and `a` it uses. -/
theorem covers_loop {σ u : State} (hp : Pre σ) {N : Nat} (hN : N ≤ 280) (hrd : u.rd = σ.rd)
    (hwr : u.wr = σ.wr) :
    Covers (lrd N (So σ 0) ++ lwr (aP σ)) (u.rd ++ u.wr) ∧ Covers (lwr (aP σ)) u.wr := by
  rw [hrd, hwr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · rcases mem2 hr with rfl | rfl
    · exact ⟨scR σ, by simp, 0, rfl, by show 0 + 3 * N ≤ 2048; omega⟩
    · exact ⟨aR σ, by simp, 0, (ptr_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨aR σ, by simp, 0, (ptr_zero _).symm, Nat.le_of_ble_eq_true rfl⟩

/-- The loop of `SampleNTT`, in two runs from the same output and zeros. -/
theorem loop_ct {N : Nat} {B : List Byte} {bP aP : Addr} {c : Prog isa} {P : State → State → Prop}
    (hl : ∀ s₁ s₂, P s₁ s₂ → LPre N B bP aP s₁ ∧ LPre N B bP aP s₂ ∧ s₁.sp = s₂.sp)
    (hc : ∀ s₁ s₂, P s₁ s₂ → (Covers (lrd N bP ++ lwr aP) (s₁.rd ++ s₁.wr) ∧ Covers (lwr aP) s₁.wr) ∧
      (Covers (lrd N bP ++ lwr aP) (s₂.rd ++ s₂.wr) ∧ Covers (lwr aP) s₂.wr))
    (hx : ∀ {u}, LPre N B bP aP u → ∃ t u', Exec isa c u t u')
    (ht : ∃ hint : Taint.Hint memTaint.T,
      (memTaint.check (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10]) c hint).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  obtain ⟨_, ht⟩ := ht
  refine RelCT.narrow (lrd N bP) (lwr aP) hc (fun s₁ s₂ h => ?_)
    (RelCT.taint (A := memTaint) (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10])
      (fun _ _ h => ?_) ht)
  · obtain ⟨l₁, l₂, -⟩ := hl s₁ s₂ h
    exact ⟨hx l₁.narrow, hx l₂.narrow⟩
  · obtain ⟨s₁, s₂, hP, rfl, rfl⟩ := h
    obtain ⟨l₁, l₂, hsp⟩ := hl s₁ s₂ hP
    exact iters_agree l₁ l₂ hsp

theorem loop_taint : ∃ hint : Taint.Hint memTaint.T,
    (memTaint.check (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10]) sampleLoop hint).isSome = true :=
  ⟨_, by taint_decide⟩

theorem iters_taint : ∃ hint : Taint.Hint memTaint.T,
    (memTaint.check (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10]) (.loop sampleBody (.nonzero .x .x5))
      hint).isSome = true :=
  ⟨_, by taint_decide⟩

/-- What each run of `sampleFull` knows after the Keccak calls. -/
abbrev FA (σ u : State) : Prop := LPre 280 (Bs σ) (So σ 0) (aP σ) u ∧ Fin σ u

theorem full_ct (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa sampleAArch64.pre sampleAArch64.pub (sampleFullWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.sampleFullTaint
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    ((VectorTaint.relCT (Taint.ofRegs [.x0, .x1, .x2])
      (fun _ _ h => agree_of h.2.2.2.2.2.1 (by
        obtain ⟨-, -, e0, e1, e2, -, -⟩ := h
        simp [e0, e1, e2])) hhint).wpDep (F := FA)
      fun s₁ s₂ h => ⟨(phaseA_ok v) (pre_of h.1), (phaseA_ok v) (pre_of h.2.1)⟩) ?_)
  refine RelCT.mono (RelCT.exists_ (P := fun (x : Addr × Addr × List Byte) s₁ s₂ =>
      ∃ σ₁ σ₂, (sampleAArch64.pre σ₁ ∧ sampleAArch64.pre σ₂ ∧ sampleAArch64.pub σ₁ σ₂) ∧ FA σ₁ s₁ ∧
        FA σ₂ s₂ ∧ So σ₁ 0 = x.1 ∧ aP σ₁ = x.2.1 ∧ Bs σ₁ = x.2.2)
    fun x => loop_ct (N := 280) (B := x.2.2) (bP := x.1) (aP := x.2.1) (fun s₁ s₂ h => ?_)
      (fun s₁ s₂ h => ?_) (fun hl => by obtain ⟨t, u, e, -⟩ := loop_ok hl; exact ⟨t, u, e⟩) loop_taint)
    (fun s₁ s₂ h => ?_) fun _ _ h => h
  · obtain ⟨σ₁, σ₂, ⟨-, -, -, e1, e2, esp, eB⟩, ⟨l₁, f₁⟩, ⟨l₂, f₂⟩, x1, x2, x3⟩ := h
    rw [← x1, ← x2, ← x3]
    rw [show So σ₂ 0 = So σ₁ 0 by rw [So, So, scP, scP, e2], show aP σ₂ = aP σ₁ from e1.symm,
      show Bs σ₂ = Bs σ₁ from (map_toNat_inj eB).symm] at l₂
    exact ⟨l₁, l₂, by rw [f₁.sp, f₂.sp, esp]⟩
  · obtain ⟨σ₁, σ₂, ⟨p₁, p₂, -, e1, e2, -, -⟩, ⟨-, f₁⟩, ⟨-, f₂⟩, x1, x2, -⟩ := h
    rw [← x1, ← x2]
    have c₂ := covers_loop (pre_of p₂) (N := 280) (by decide) f₂.rd f₂.wr
    rw [show So σ₂ 0 = So σ₁ 0 by rw [So, So, scP, scP, e2], show aP σ₂ = aP σ₁ from e1.symm] at c₂
    exact ⟨covers_loop (pre_of p₁) (by decide) f₁.rd f₁.wr, c₂⟩
  · obtain ⟨-, σ₁, σ₂, hP, f₁, f₂⟩ := h
    exact ⟨(So σ₁ 0, aP σ₁, Bs σ₁), σ₁, σ₂, hP, f₁, f₂, rfl, rfl, rfl⟩

/-- Constant time from any two states related by `P`, proved for each pair. -/
theorem RelCT.pointwise {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa (fun a b => a = s₁ ∧ b = s₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ _ _ _ _ hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

theorem ct (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa sampleAArch64.pre sampleAArch64.pub (sampleNTTWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.sampleFastTaint
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.pointwise fun σ₁ σ₂ hσ => ?_)
  obtain ⟨p₁, p₂, e0, e1, e2, esp, eB⟩ := hσ
  have hB : Bs σ₂ = Bs σ₁ := (map_toNat_inj eB).symm
  have q₁ := pre_of p₁
  have q₂ := pre_of p₂
  have eS : So σ₂ 0 = So σ₁ 0 := by rw [So, So, scP, scP, e2]
  have eA : aP σ₂ = aP σ₁ := e1.symm
  have e26 : scP σ₂ = scP σ₁ := e2.symm
  -- the output of `(sampleFastWith v.callee)`, and its loop
  refine RelCT.seq (RelCT.seq (R := fun a b => (LPre 168 (Bs σ₁) (So σ₁ 0) (aP σ₁) a ∧ MidA σ₁ a) ∧
      (LPre 168 (Bs σ₂) (So σ₂ 0) (aP σ₂) b ∧ MidA σ₂ b))
    (RelCT.mono ((VectorTaint.relCT (P := fun a b => a = σ₁ ∧ b = σ₂) (Taint.ofRegs [.x0, .x1, .x2])
      (fun a b h => by
        obtain ⟨rfl, rfl⟩ := h
        exact agree_of esp (by simp [e0, e1, e2])) hhint).wp
      (F₁ := fun a => LPre 168 (Bs σ₁) (So σ₁ 0) (aP σ₁) a ∧ MidA σ₁ a)
      (F₂ := fun b => LPre 168 (Bs σ₂) (So σ₂ 0) (aP σ₂) b ∧ MidA σ₂ b)
      fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨(fastA_ok v) q₁, (fastA_ok v) q₂⟩)
      (fun _ _ h => h) fun _ _ h => h.2)
    (RelCT.mono ((loop_ct (N := 168) (B := Bs σ₁) (bP := So σ₁ 0) (aP := aP σ₁) (fun a b h => ?_)
      (fun a b h => ?_) (fun hl => by obtain ⟨t, u, e, -⟩ := iters_ok (by decide) hl; exact ⟨t, u, e⟩)
      iters_taint).wp (F₁ := FastPost σ₁) (F₂ := FastPost σ₂)
      fun a b h => ⟨fastLoop_ok q₁ h.1.1 h.1.2, fastLoop_ok q₂ h.2.1 h.2.2⟩)
      (fun _ _ h => h) fun _ _ h => h.2)) ?_
  · obtain ⟨⟨l₁, m₁⟩, ⟨l₂, m₂⟩⟩ := h
    rw [hB, eS, eA] at l₂
    exact ⟨l₁, l₂, by rw [m₁.sp, m₂.sp, esp]⟩
  · obtain ⟨⟨-, m₁⟩, ⟨-, m₂⟩⟩ := h
    have c₂ := covers_loop q₂ (N := 168) (by decide) m₂.rd m₂.wr
    rw [eS, eA] at c₂
    exact ⟨covers_loop q₁ (by decide) m₁.rd m₁.wr, c₂⟩
  -- whether it is done
  refine RelCT.ite (fun a b h => ?_) (RelCT.mono (RelCT.taint (A := taint) (Taint.ofRegs [.x26])
      (fun a b h => agree_of (by rw [h.1.1.mid.sp, h.1.2.mid.sp, esp])
        (by simp [h.1.1.mid.x26, h.1.2.mid.x26, e26])) (by taint_decide)) (fun _ _ h => h) fun _ _ h => h)
    (RelCT.seq (RelCT.mono ((RelCT.taint (A := taint) (Taint.ofRegs [.x26])
      (fun a b h => agree_of (by rw [h.1.1.mid.sp, h.1.2.mid.sp, esp])
        (by simp [h.1.1.mid.x26, h.1.2.mid.x26, e26])) (by taint_decide)).wp
      (F₁ := RetryPost σ₁) (F₂ := RetryPost σ₂)
      fun a b h => ⟨retryBlock_ok q₁ h.1.1, retryBlock_ok q₂ h.1.2⟩) (fun _ _ h => h)
      fun _ _ h => h.2) ?_)
  · obtain ⟨h₁, h₂⟩ := h
    rw [eval_zero, eval_zero]
    have v : a.gpr .x4 = b.gpr .x4 := BitVec.eq_of_toNat_eq (by rw [h₁.x4, h₂.x4, hB])
    rw [v]
  · -- `(sampleFullWith v.callee)`, from states that satisfy its contract
    refine fun a b t₁ t₂ a' b' h e₁ e₂ => ⟨(full_ct v) a b t₁ t₂ a' b' (h.1.pre q₁) (h.2.pre q₂) ?_ e₁ e₂, trivial⟩
    obtain ⟨h₁, h₂⟩ := h
    refine ⟨by rw [h₁.x0, h₂.x0, sdP, sdP, e0], by rw [h₁.x1, h₂.x1, eA], by rw [h₁.x2, h₂.x2, e26],
      by rw [h₁.sp, h₂.sp, esp], ?_⟩
    rw [h₁.x0, h₂.x0, h₁.seed, h₂.seed, hB]

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem sample_correctWith (v : Proof.Sha3.AArch64.Permutation) (s : State) (hs : sampleAArch64.pre s) :
    ∃ t s', Exec isa (sampleNTTWith v.callee) s t s' ∧ abiPreserved s s' ∧ sampleAArch64.post s s' :=
  (correct v) (pre_of hs)

/-- What callers use: `a` is always reduced, and the return value is
determined by the seed (`SampleNTT` with 280 iterations). -/
def sampleStrong : Contract isa :=
  { sampleAArch64 with
    post := fun s s' => Reduced s'.mem (s.gpr .x1) ∧
      ((s'.gpr .x0 = 1 ∧ sampleNTT 280 (bytesAt s.mem (s.gpr .x0) 34) = some (polyAt s'.mem (s.gpr .x1))) ∨
        (s'.gpr .x0 = 0 ∧ sampleNTT 280 (bytesAt s.mem (s.gpr .x0) 34) = none)) }

theorem sample_strongWith (v : Proof.Sha3.AArch64.Permutation) (s : State) (hs : sampleStrong.pre s) :
    ∃ t s', Exec isa (sampleNTTWith v.callee) s t s' ∧ abiPreserved s s' ∧ sampleStrong.post s s' :=
  WP.mono ((strong_ok v) (pre_of hs)) fun _ h => h

theorem ct_strongWith (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa sampleStrong.pre sampleStrong.pub (sampleNTTWith v.callee) := (ct v)

theorem sample_verifiedWith (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target (sampleNTTWith v.callee) (Spec.MlKem.sampleNTTContract AArch64.abi 16) :=
  Verified.of_correct (sample_correctWith v) (ct v) (by
    mlkem_implies [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, sampleAArch64,
      AArch64.abi, AArch64.argRegs] [sat] using sat)

theorem sample_correct (s : State) (hs : sampleAArch64.pre s) :
    ∃ t s', Exec isa sampleNTT s t s' ∧ abiPreserved s s' ∧ sampleAArch64.post s s' :=
  sample_correctWith .scalar s hs

theorem sample_strong (s : State) (hs : sampleStrong.pre s) :
    ∃ t s', Exec isa sampleNTT s t s' ∧ abiPreserved s s' ∧ sampleStrong.post s s' :=
  sample_strongWith .scalar s hs

theorem ct_strong : ConstantTime isa sampleStrong.pre sampleStrong.pub sampleNTT :=
  ct_strongWith .scalar

theorem sample_verified :
    Verified AArch64.target sampleNTT (Spec.MlKem.sampleNTTContract AArch64.abi 16) :=
  sample_verifiedWith .scalar

end VG.Proof.MlKem.AArch64.Sample
