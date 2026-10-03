import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Output
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb

/-! Merged from `Proof.Argon2.X86_64.HPrime.Next`. -/
section
/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.X86_64 (wp_mov32i)

theorem next_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (next (hash v)) s fun t =>
      (bytesAt t.mem (s.gpr .rbx + 768) 64).take (s.gpr .rsi).toNat =
        Spec.Argon2.H (s.gpr .rsi).toNat (bytesAt s.mem (s.gpr .rbx + 768) 64) ∧ Keeps s t := by
  unfold next
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have retState := (stackWork.sub_left retSub).sub_right
    (Region.sub_prefix (base := s.gpr .rbx) (len := 192) (len' := 16384) (by decide))
  refine WP.seq ((init_ok v s hlen hwr retState).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, init_frame _ _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [ka.rbx]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .rbx + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
    · exact ((stackWork.sub_left retSub).sub_right (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) a.mem (a.gpr .rbx) [] := by
    rw [ka.rbx]; exact reprA
  have wrA' : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact hwr
  have swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  refine WP.seq ((absorbFixed_ok v a _ 768 64 (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) u.mem (u.gpr .rbx)
      (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [ku.rbx]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_mov32i fun w hw _ _ => WP.block_nil ?_)
  have kw : Keeps u w := by
    refine ⟨fun r hr => ?_, hw.rd, hw.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hw.other r hn
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) w.mem (w.gpr .rbx)
      (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [hw.mem, kw.rbx]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .rbx + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .rsi = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .rbx + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .rbx + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .rbx, 16384⟩ : Region) ∈ w.wr := by rw [ksw.rbx, ksw.wr]; exact hwr
  have swW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [ksw.rbx, ksw.rsp]; exact stackWork
  refine (finalize_ok v w _ _ reprW count bound wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, finalize_frame _ _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .rsi).toNat) out
  rw [ksw.rbx] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.ChainStep`. -/
section
/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov32i wp_cmpi)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + 32
  remaining : t.gpr .r15 = s.gpr .r15 - 32
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .rbx + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64)
  bytes : bytesAt t.mem (s.gpr .r14) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64)).take 32
  cf : t.cf = some (decide ((s.gpr .r15 - 32).toNat < 65))

theorem chainStep_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (.seq (.block [.mov32 .rsi (.imm 64)])
      (.seq (next (hash v)) (.seq emitPrefix (.block [.alu .cmp .r15 (.imm 65)]))))
      s (ChainStep s) := by
  refine WP.seq (wp_mov32i fun a ha _ _ => WP.block_nil ?_)
  have ka : Keeps s a := by
    refine ⟨fun r hr => ?_, ha.rd, ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact ha.other r hn
    · rw [ha.mem]; exact Frame.refl _ _
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact work
  have stackA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  have lengthA : (a.gpr .rsi).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok v a (by rw [lengthA]; decide) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .r14 = s.gpr .r14 := ksu.regs _ (by decide)
  have digestU : bytesAt u.mem (s.gpr .rbx + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    simpa only [lengthA, ka.rbx, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ksu.rbx, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .rbx + 768, 32⟩ : Region).Disjoint ⟨u.gpr .r14, 32⟩ := by
    rw [ksu.rbx, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  refine wp_cmpi fun t gt mt rt wt cf _ => WP.block_nil ?_
  have fw : Frame [⟨s.gpr .r14, 32⟩] u.mem w.mem := by
    rw [← dstU]; exact hw.frame
  refine ⟨?_, ?_, fun r hr h14 h15 => ?_, rt.trans (hw.rd.trans ksu.rd),
    wt.trans (hw.wr.trans ksu.wr), ?_, ?_, ?_, ?_⟩
  · rw [gt, hw.output, dstU]
  · rw [gt, hw.remaining, ksu.regs _ (by decide)]
  · rw [gt]
    have hrax : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hw.other r hrax hrcx hrdx h14 h15).trans (ksu.regs r hr)
  · rw [mt]
    apply Frame.trans (ksu.frame.sub ?_) (fw.sub ?_)
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · intro r hr
      exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .rbx + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.rbx, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [cf, hw.remaining, ksu.regs _ (by decide)]
    rfl

end VG.Proof.Argon2.X86_64.HPrime
end

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
