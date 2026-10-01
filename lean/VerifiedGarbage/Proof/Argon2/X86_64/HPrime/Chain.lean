import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.ChainStep

/-! # H′: repeating the hash-and-prefix iteration -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

structure ChainResult (s : State) (n : Nat) (t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + BitVec.ofNat 64 (32 * n)
  remaining : t.gpr .r15 = s.gpr .r15 - BitVec.ofNat 64 (32 * n)
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, 32 * n⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .rbx + 768) 64 =
    chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64)
  bytes : bytesAt t.mem (s.gpr .r14) (32 * n) =
    chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)

theorem ChainResult.refl (s : State) : ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : ChainStep s u)
    (tail : ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32 * (n + 1)⟩)
    (stackOut : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, 32 * (n + 1)⟩) :
    ChainResult s (n + 1) t := by
  have base := step.regs .rbx (by decide) (by decide) (by decide)
  have sp := step.regs .rsp (by decide) (by decide) (by decide)
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega
  have sumBV : BitVec.ofNat 64 (32 * (n + 1)) = 32 + BitVec.ofNat 64 (32 * n) := by
    rw [sum, BitVec.ofNat_add]; rfl
  have tf : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
      ⟨s.gpr .r14 + 32, 32 * n⟩] u.mem t.mem := by
    rw [← base, ← sp, ← step.output]; exact tail.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ 32 * (n + 1))
      (h : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, 32 * (n + 1)⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ hk⟩
  refine ⟨?_, ?_, fun r hr h1 h2 => (tail.regs r hr h1 h2).trans (step.regs r hr h1 h2),
    tail.rd.trans step.rd, tail.wr.trans step.wr, ?_, ?_, ?_⟩
  · rw [tail.output, step.output, sumBV, BitVec.add_assoc]
  · rw [tail.remaining, step.remaining, sumBV, BitVec.sub_sub]
  · exact (extend 0 32 (by omega) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega) tf)
  · rw [← base, tail.digest, base, step.digest]
    rfl
  · have before : bytesAt t.mem (s.gpr .r14) 32 = bytesAt u.mem (s.gpr .r14) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r14, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left
          (Region.sub_prefix (by omega))
      · exact stackOut.symm.sub_left (Region.sub_prefix (by omega))
      · exact Offset.base_disjoint _ (e := 32) (n := 32 * n) (k := 32) (by decide) (by omega)
    rw [sum, Proof.Blake2.bytesAt_add, before, step.bytes,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl, ← step.output, tail.bytes,
      base, step.digest]
    rfl

theorem chain_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (positive : 1 ≤ n) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (bound : 32 * n + lastLen < 2 ^ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen))
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32 * n, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32 * n⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackOut : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, 32 * n⟩) :
    WP isa (chain (hash v)) s (ChainResult s n) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega)
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega))
    obtain ⟨trace, u, run, step⟩ := chainStep_ok v s work out32 sep32 stackWork
    have base := step.regs .rbx (by decide) (by decide) (by decide)
    have sp := step.regs .rsp (by decide) (by decide) (by decide)
    have countU : u.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega]
    have cfU : u.cf = some (decide (32 * n + lastLen < 65)) := by
      rw [step.cf, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    cases n with
    | zero =>
      have flag : isa.eval .ae u = some false := by
        simp only [eval, cfU, show 32 * 0 + lastLen < 65 by omega, decide_true,
          Option.map_some, Bool.not_true]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega) sep stackOut⟩
    | succ n =>
      have workU : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .r14 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega)
      have suffix : Region.Sub ⟨u.gpr .r14, 32 * (n + 1)⟩ ⟨s.gpr .r14, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .rbx, 16384⟩ : Region).Disjoint ⟨u.gpr .r14, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      have swU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
        rw [sp, base]; exact stackWork
      have soU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .r14, 32 * (n + 1)⟩ := by
        rw [sp]; exact stackOut.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega) (by omega) countU workU outU sepU swU soU
      have flag : isa.eval .ae u = some true := by
        simp only [eval, cfU, show ¬ 32 * (n + 1) + lastLen < 65 by omega, decide_false,
          Option.map_some, Bool.not_false]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega) sep stackOut⟩

end VG.Proof.Argon2.X86_64.HPrime
