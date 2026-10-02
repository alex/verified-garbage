import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Backend
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Copy

/-! # H′: initializing an unkeyed BLAKE2b computation -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure InitArgs (s t : State) : Prop where
  state : t.gpr .x0 = s.gpr .x24
  key : t.gpr .x2 = s.gpr .x24 + 832
  keylen : t.gpr .x3 = 0
  other : ∀ r, r ≠ .x0 → r ≠ .x2 → r ≠ .x3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem initArgs_ok (s : State) : WP isa (.block initArgs) s (InitArgs s) := by
  apply WP.of_runBlock
  simp only [initArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (832 : Nat) < 4096 from by decide,
    show (16 * 0 : Nat) < 64 from by decide, State.read, Size.bits,
    BitVec.setWidth_eq, BitVec.add_zero,
    ite_true, ite_false, reduceCtorEq, RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]

/-- Narrow the callee's permissions to its state and empty key. -/
theorem init_call_hyps (s u : State) (hu : InitArgs s u)
    (hlen : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr) :
    (Proof.Blake2.initAArch64 Spec.Blake2.b).pre
      (u.callEntry.withRegions [⟨s.gpr .x24 + 832, 0⟩] [⟨s.gpr .x24, 192⟩]) ∧
    Covers [⟨s.gpr .x24 + 832, 0⟩, ⟨s.gpr .x24, 192⟩] (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .x24, 192⟩] u.wr := by
  have hlen' : u.gpr .x1 = s.gpr .x1 := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun _ hr => State.callEntry_gpr u hr
  have hp : (Proof.Blake2.initAArch64 Spec.Blake2.b).pre
      (u.callEntry.withRegions [⟨s.gpr .x24 + 832, 0⟩] [⟨s.gpr .x24, 192⟩]) := by
    simp only [Proof.Blake2.initAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .x0 (by decide), g .x2 (by decide), g .x3 (by decide),
      g .x1 (by decide), hu.state, hu.key, hu.keylen, hlen']
    refine ⟨rfl, rfl, ?_, hlen.1, hlen.2, by decide⟩
    exact (Offset.base_disjoint (s.gpr .x24) (e := 832) (n := 0) (k := 192) (by decide) (by decide)).symm
  have cover : Covers [⟨s.gpr .x24 + 832, 0⟩, ⟨s.gpr .x24, 192⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .x24, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨832, rfl, by change 832 ≤ 16384; decide⟩
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  have writes : Covers [⟨s.gpr .x24, 192⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨s.gpr .x24, 16384⟩, hu.wr.symm ▸ hwr, 0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  exact ⟨hp, cover, writes⟩

theorem init_ok (v : Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr) :
    WP isa (init v.hash) s fun t =>
      Spec.Blake2.Repr Spec.Blake2.b (Spec.Blake2.init Spec.Blake2.b (s.gpr .x1).toNat 0)
        t.mem (s.gpr .x24) [] ∧
      (∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ Frame [⟨s.gpr .x24, 192⟩] s.mem t.mem := by
  unfold init
  refine WP.seq ((initArgs_ok s).mono fun u hu => ?_)
  have hlen' : u.gpr .x1 = s.gpr .x1 := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun _ hr => State.callEntry_gpr u hr
  obtain ⟨hp, cover, writes⟩ := init_call_hyps s u hu hlen hwr
  refine WP.call (k := Proof.Blake2.initAArch64 Spec.Blake2.b)
    v.initCorrect hp cover writes ?_ v.ok.initNoFrames
  intro t rd wr sp frame cs keep post
  have post' := post
  simp only [Proof.Blake2.initAArch64, State.withRegions_gpr, State.withRegions_mem,
    g .x0 (by decide), g .x1 (by decide), g .x2 (by decide), g .x3 (by decide),
    hu.state, hu.key, hu.keylen, hlen', Spec.Blake2.bytesAt, Spec.Blake2.keyBlock] at post'
  refine ⟨post', fun r hr h30 => (cs r hr h30).trans ?_, rd.trans hu.rd, wr.trans hu.wr,
    sp.trans hu.sp, ?_⟩
  · have hn : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [hu.mem] using frame

end VG.Proof.Argon2.AArch64.HPrime
