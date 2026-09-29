import VerifiedGarbage.Proof.MlKem.AArch64.SampleSqueeze
import VerifiedGarbage.Proof.MlKem.AArch64.MemTaint

/-!
# ML-KEM on AArch64: `vg_mlkem_sample_ntt`

Untrusted: everything here is checked by Lean. Correctness is `phaseA_ok`
(the SHAKE128 output, `a` zero) followed by `loop_ok`, and `outcome_of_min`.

Constant time up to the seed, relating two runs (`RelCT`) from states that
agree on the pointers and on the seed: up to the loop, the taint analysis
(through the Keccak calls); then, by correctness, both runs have the same
SHAKE128 output (a function of the seed) in `scratch[0, 840)` and zeros in
`a`, so the loop, which touches nothing else, runs with permissions on only
memory both runs agree on (`RelCT.narrow`), where `memTaint` proves it
leaks the same (its branches depend on the output).
-/

namespace VG.Proof.MlKem.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem phaseA_ok {s₀ : State} (hp : Pre s₀) :
    WP isa sampleSqueeze s₀ fun u => LPre (Bs s₀) (So s₀ 0) (aP s₀) u ∧ Fin s₀ u :=
  WP.seq (WP.mono (prologue_ok hp) fun _ h => calls_ok hp h fun _ m b => rest_ok hp m b)

theorem pres_loop : ∀ r ∈ preserved, r ∉ (Reg.x0 :: lRegs) := by decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa sampleNTT s₀ fun s' => abiPreserved s₀ s' ∧ sampleAArch64.post s₀ s' := by
  refine WP.seq (WP.mono (phaseA_ok hp) fun u ⟨hl, hf⟩ => WP.mono (loop_ok hl) fun s' ⟨k, _, res⟩ => ?_)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [k.gpr r (pres_loop r hr), hf.cs r hr]
  · rw [k.sp, hf.sp]
  rcases res with ⟨h0, hpoly, hs⟩ | ⟨h0, hn⟩
  · have r1 : (s'.gpr .x0).setWidth 32 = 1 := by rw [h0]; rfl
    refine ⟨fun _ => hpoly.1, outcome_of_min (.inl ⟨r1, ?_⟩)⟩
    show sampleNTT 280 (Bs s₀) = some (polyAt s'.mem (aP s₀))
    rw [hpoly.2]; exact hs
  · have r0 : (s'.gpr .x0).setWidth 32 = 0 := by rw [h0]; rfl
    refine ⟨fun h => ?_, outcome_of_min (.inr ⟨r0, ?_⟩)⟩
    · rw [r0] at h; cases h
    · show sampleNTT 280 (Bs s₀) = none
      exact hn

/-! ## Constant time -/

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

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
abbrev lrd (bP : Addr) : List Region := [⟨bP, 840⟩]
abbrev lwr (aP : Addr) : List Region := [polyRegion aP]

theorem LPre.narrow {B : List Byte} {bP aP : Addr} {s : State} (h : LPre B bP aP s) :
    LPre B bP aP (s.withRegions (lrd bP) (lwr aP)) :=
  ⟨h.buf, fun p hp => in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide))),
    fun i hi => in_regions (List.mem_singleton_self _) (coeff_contains _ (show i < n from hi)),
    h.disj, h.zero, h.x2, h.x3, h.x4, h.x5, h.x9, h.x10⟩

/-- What each run knows after the Keccak calls. -/
abbrev FA (σ u : State) : Prop := LPre (Bs σ) (So σ 0) (aP σ) u ∧ Fin σ u

/-- Two runs, from initial states `σ₁` and `σ₂` with the pointers `x`. -/
def Rel (x : Addr × Addr) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, (sampleAArch64.pre σ₁ ∧ sampleAArch64.pre σ₂ ∧ sampleAArch64.pub σ₁ σ₂) ∧ FA σ₁ s₁ ∧
    FA σ₂ s₂ ∧ So σ₁ 0 = x.1 ∧ aP σ₁ = x.2

theorem covers_loop {σ u : State} (hp : Pre σ) (hf : Fin σ u) :
    Covers (lrd (So σ 0) ++ lwr (aP σ)) (u.rd ++ u.wr) ∧ Covers (lwr (aP σ)) u.wr := by
  rw [hf.rd, hf.wr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · rcases mem2 hr with rfl | rfl
    · exact ⟨scR σ, by simp, 0, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨aR σ, by simp, 0, (ptr_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨aR σ, by simp, 0, (ptr_zero _).symm, Nat.le_of_ble_eq_true rfl⟩

theorem loop_agree {x : Addr × Addr} {u₁ u₂ : State}
    (h : ∃ s₁ s₂, Rel x s₁ s₂ ∧ u₁ = s₁.withRegions (lrd x.1) (lwr x.2) ∧
      u₂ = s₂.withRegions (lrd x.1) (lwr x.2)) :
    memTaint.Agree (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10]) u₁ u₂ := by
  obtain ⟨s₁, s₂, ⟨σ₁, σ₂, ⟨-, -, -, e1, e2, esp, eB⟩, ⟨l₁, f₁⟩, ⟨l₂, f₂⟩, hx1, hx2⟩, rfl, rfl⟩ := h
  rw [← hx1, ← hx2]
  have hB : Bs σ₁ = Bs σ₂ := map_toNat_inj eB
  have n4 : ∀ {a b : BitVec 64} {k : Nat}, a.toNat = k → b.toNat = k → a = b :=
    fun ha hb => BitVec.eq_of_toNat_eq (ha.trans hb.symm)
  refine ⟨agree_of (by simp only [State.withRegions_sp]; rw [f₁.sp, f₂.sp, esp]) fun r hr => ?_,
    rfl, rfl, fun y hy => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [State.withRegions_gpr]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [l₁.x2, l₂.x2, So, So, scP, scP, e2]
    · rw [l₁.x3, l₂.x3, aP, aP, e1]
    · exact n4 l₁.x4 l₂.x4
    · exact n4 l₁.x5 l₂.x5
    · exact n4 l₁.x9 l₂.x9
    · exact n4 l₁.x10 l₂.x10
  · simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem] at hy ⊢
    obtain ⟨R, hR, hc⟩ := hy
    rcases mem2 hR with rfl | rfl
    · obtain ⟨p, hp, rfl⟩ := at_off hc
      rw [l₁.buf p hp, show So σ₁ 0 = So σ₂ 0 by rw [So, So, scP, scP, e2], l₂.buf p hp, hB]
    · rw [byte_zero l₁.zero hc, byte_zero l₂.zero (by rw [show aP σ₂ = aP σ₁ from e1.symm]; exact hc)]

theorem loop_ct (x : Addr × Addr) : RelCT isa (Rel x) sampleLoop fun _ _ => True := by
  refine RelCT.narrow (lrd x.1) (lwr x.2) (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_)
    (RelCT.taint (A := memTaint) (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10])
      (fun _ _ h => loop_agree h) (by taint_decide))
  · obtain ⟨σ₁, σ₂, ⟨p₁, p₂, -, e1, e2, -, -⟩, ⟨-, f₁⟩, ⟨-, f₂⟩, hx1, hx2⟩ := h
    rw [← hx1, ← hx2]
    have c₂ := covers_loop (pre_of p₂) f₂
    rw [show So σ₂ 0 = So σ₁ 0 by rw [So, So, scP, scP, e2], show aP σ₂ = aP σ₁ from e1.symm] at c₂
    exact ⟨covers_loop (pre_of p₁) f₁, c₂⟩
  · obtain ⟨σ₁, σ₂, ⟨-, -, -, e1, e2, -, -⟩, ⟨l₁, -⟩, ⟨l₂, -⟩, hx1, hx2⟩ := h
    rw [← hx1, ← hx2]
    have n₂ := l₂.narrow
    rw [show So σ₂ 0 = So σ₁ 0 by rw [So, So, scP, scP, e2], show aP σ₂ = aP σ₁ from e1.symm] at n₂
    obtain ⟨t₁, u₁, x₁, -⟩ := loop_ok l₁.narrow
    obtain ⟨t₂, u₂, x₂, -⟩ := loop_ok n₂
    exact ⟨⟨t₁, u₁, x₁⟩, ⟨t₂, u₂, x₂⟩⟩

theorem ct : ConstantTime isa sampleAArch64.pre sampleAArch64.pub sampleNTT := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    ((RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
      (fun _ _ h => agree_of h.2.2.2.2.2.1 (by
        obtain ⟨-, -, e0, e1, e2, -, -⟩ := h
        simp [e0, e1, e2])) (by taint_decide)).wpDep (F := FA)
      fun s₁ s₂ h => ⟨phaseA_ok (pre_of h.1), phaseA_ok (pre_of h.2.1)⟩) ?_)
  refine RelCT.mono (RelCT.exists_ (P := Rel) loop_ct) (fun s₁ s₂ h => ?_) fun _ _ h => h
  obtain ⟨-, σ₁, σ₂, hP, f₁, f₂⟩ := h
  exact ⟨(So σ₁ 0, aP σ₁), σ₁, σ₂, hP, f₁, f₂, rfl, rfl⟩

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem sample_correct (s : State) (hs : sampleAArch64.pre s) :
    ∃ t s', Exec isa sampleNTT s t s' ∧ abiPreserved s s' ∧ sampleAArch64.post s s' :=
  correct (pre_of hs)

theorem sample_verified :
    Verified AArch64.target sampleNTT (Spec.MlKem.sampleNTTContract AArch64.abi 16) :=
  Verified.of_correct sample_correct ct (by
    mlkem_implies [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, sampleAArch64,
      AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Sample
