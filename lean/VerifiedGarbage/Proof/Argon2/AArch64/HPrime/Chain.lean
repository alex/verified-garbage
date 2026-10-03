import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Compare
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Output
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Absorb

/-! Merged from `Proof.Argon2.AArch64.HPrime.Next`. -/
section
/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.AArch64 (wp_movz)

theorem next_ok (v : Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (next v.hash) s fun t =>
      (bytesAt t.mem (s.gpr .x24 + 768) 64).take (s.gpr .x1).toNat =
        Spec.Argon2.H (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x24 + 768) 64) ∧ Keeps s t := by
  unfold next
  refine WP.seq ((init_ok v s hlen hwr).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, spA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, spA, init_frame _ _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
    rw [ka.x24]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .x24 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) a.mem (a.gpr .x24) [] := by
    rw [ka.x24]; exact reprA
  have wrA' : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact hwr
  have swA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  refine WP.seq ((absorbFixed_ok v a _ 768 64 (by decide) (by rw [ka.sp]; exact hsp) (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) u.mem (u.gpr .x24)
      (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [ku.x24]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_movz fun w hw => WP.block_nil ?_)
  have kw : Keeps u w := by
    refine ⟨fun r hr _ => ?_, hw.rd, hw.wr, hw.sp, ?_⟩
    · have hn : r ≠ .x1 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hw.other r hn
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) w.mem (w.gpr .x24)
      (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [hw.mem, kw.x24]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .x24 + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .x1 = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .x24 + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .x24 + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .x24, 16384⟩ : Region) ∈ w.wr := by rw [ksw.x24, ksw.wr]; exact hwr
  have swW : (below w.sp 16).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [ksw.x24, ksw.sp]; exact stackWork
  refine (finalize_ok v w _ _ reprW count bound (by rw [ksw.sp]; exact hsp) wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, spT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, spT, finalize_frame _ _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .x1).toNat) out
  rw [ksw.x24] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.ChainStep`. -/
section
/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_movz)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + 32
  remaining : t.gpr .x23 = s.gpr .x23 - 32
  regs : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .x24 + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .x22) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64)).take 32
  comparison : t.gpr .x9 = if (s.gpr .x23 - 32).toNat < 65 then 1 else 0

theorem chainStep_ok (v : Backend) (s : State)
    (hsp : 16 ≤ s.sp.toNat)
    (remainingBound : 32 ≤ (s.gpr .x23).toNat ∧ (s.gpr .x23).toNat < 2 ^ 32)
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (.seq (.block [.movz .x .x1 64 0])
      (.seq (next v.hash) (.seq emitPrefix (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63]))))
      s (ChainStep s) := by
  refine WP.seq (wp_movz fun a ha => WP.block_nil ?_)
  have ka : Keeps s a := Keeps.of_upd ha (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact work
  have stackA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  have lengthA : (a.gpr .x1).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok v a (by rw [lengthA]; decide) (by rw [ka.sp]; exact hsp) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .x22 = s.gpr .x22 := ksu.regs _ (by decide) (by decide)
  have digestU : bytesAt u.mem (s.gpr .x24 + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    simpa only [lengthA, ka.x24, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ksu.x24, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .x24 + 768, 32⟩ : Region).Disjoint ⟨u.gpr .x22, 32⟩ := by
    rw [ksu.x24, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  have remainingW : (w.gpr .x23).toNat < 2 ^ 32 := by
    rw [hw.remaining, ksu.regs _ (by decide) (by decide),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact remainingBound.1)]
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) remainingBound.2
  refine (compare_ok w remainingW).mono fun t compared => ?_
  have gt := compared.other
  have mt := compared.mem
  have rt := compared.rd
  have wt := compared.wr
  have fw : Frame [⟨s.gpr .x22, 32⟩] u.mem w.mem := by
    rw [← dstU]; exact hw.frame
  refine ⟨?_, ?_, fun r hr h30 h14 h15 => ?_, rt.trans (hw.rd.trans ksu.rd),
    wt.trans (hw.wr.trans ksu.wr), compared.sp.trans (hw.sp.trans ksu.sp), ?_, ?_, ?_, ?_⟩
  · rw [gt _ (by decide), hw.output, dstU]
  · rw [gt _ (by decide), hw.remaining, ksu.regs _ (by decide) (by decide)]
  · have h9 : r ≠ .x9 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gt r h9]
    have hrax : r ≠ .x8 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .x2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hw.other r hrax hrcx hrdx h14 h15).trans (ksu.regs r hr h30)
  · rw [mt]
    apply Frame.trans (ksu.frame.sub ?_) (fw.sub ?_)
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · intro r hr
      exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .x24 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.x24, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [compared.value, hw.remaining, ksu.regs _ (by decide) (by decide)]

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: repeating the hash-and-prefix iteration -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

structure ChainResult (s : State) (n : Nat) (t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 (32 * n)
  remaining : t.gpr .x23 = s.gpr .x23 - BitVec.ofNat 64 (32 * n)
  regs : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, 32 * n⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .x24 + 768) 64 =
    chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .x22) (32 * n) =
    chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)

theorem ChainResult.refl (s : State) : ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : ChainStep s u)
    (tail : ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32 * (n + 1)⟩)
    (stackOut : (below s.sp 16).Disjoint ⟨s.gpr .x22, 32 * (n + 1)⟩) :
    ChainResult s (n + 1) t := by
  have base := step.regs .x24 (by decide) (by decide) (by decide) (by decide)
  have sp := step.sp
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega
  have sumBV : BitVec.ofNat 64 (32 * (n + 1)) = 32 + BitVec.ofNat 64 (32 * n) := by
    rw [sum, BitVec.ofNat_add]; rfl
  have tf : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
      ⟨s.gpr .x22 + 32, 32 * n⟩] u.mem t.mem := by
    rw [← base, ← sp, ← step.output]; exact tail.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ 32 * (n + 1))
      (h : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
        ⟨s.gpr .x22 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, 32 * (n + 1)⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ hk⟩
  refine ⟨?_, ?_, fun r hr h30 h1 h2 => (tail.regs r hr h30 h1 h2).trans (step.regs r hr h30 h1 h2),
    tail.rd.trans step.rd, tail.wr.trans step.wr, tail.sp.trans step.sp, ?_, ?_, ?_⟩
  · rw [tail.output, step.output, sumBV, BitVec.add_assoc]
  · rw [tail.remaining, step.remaining, sumBV, BitVec.sub_sub]
  · exact (extend 0 32 (by omega) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega) tf)
  · rw [← base, tail.digest, base, step.digest]
    rfl
  · have before : bytesAt t.mem (s.gpr .x22) 32 = bytesAt u.mem (s.gpr .x22) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .x22, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
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

theorem chain_ok (v : Backend) (n lastLen : Nat) (s : State)
    (positive : 1 ≤ n) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (bound : 32 * n + lastLen < 2 ^ 32)
    (hsp : 16 ≤ s.sp.toNat)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen))
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32 * n, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32 * n⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackOut : (below s.sp 16).Disjoint ⟨s.gpr .x22, 32 * n⟩) :
    WP isa (chain v.hash) s (ChainResult s n) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega)
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega))
    obtain ⟨trace, u, run, step⟩ := chainStep_ok v s hsp
      (by rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) work out32 sep32 stackWork
    have base := step.regs .x24 (by decide) (by decide) (by decide) (by decide)
    have sp := step.sp
    have countU : u.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega]
    have compareU : u.gpr .x9 = if 32 * n + lastLen < 65 then 1 else 0 := by
      rw [step.comparison, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    cases n with
    | zero =>
      have flag : isa.eval (.zero .x .x9) u = some false := by
        simp [eval, State.read, compareU, show lastLen < 65 by omega]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega) sep stackOut⟩
    | succ n =>
      have workU : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .x22 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega)
      have suffix : Region.Sub ⟨u.gpr .x22, 32 * (n + 1)⟩ ⟨s.gpr .x22, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .x24, 16384⟩ : Region).Disjoint ⟨u.gpr .x22, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      have swU : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
        rw [sp, base]; exact stackWork
      have soU : (below u.sp 16).Disjoint ⟨u.gpr .x22, 32 * (n + 1)⟩ := by
        rw [sp]; exact stackOut.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega) (by omega) (by rw [sp]; exact hsp) countU workU outU sepU swU soU
      have flag : isa.eval (.zero .x .x9) u = some true := by
        simp [eval, State.read, compareU, show ¬ 32 * (n + 1) + lastLen < 65 by omega]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega) sep stackOut⟩

end VG.Proof.Argon2.AArch64.HPrime
