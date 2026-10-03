import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Contract
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Compare
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Space
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Input
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Length
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Frame
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Setup

/-! Merged from `Proof.Argon2.AArch64.HPrime.Restore`. -/
section
/-! # H′: restoring the caller's registers -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem saved_read {m m' : Mem} (p sp : Addr)
    (frame : Frame [⟨p, 832⟩, below sp 16] m m')
    (stack : (below sp 16).Disjoint ⟨p, 16384⟩)
    (d : Nat) (lo : 832 ≤ d) (hi : d + 8 ≤ 16384) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 := by
  apply frame.readW (r := ⟨p + BitVec.ofNat 64 d, 8⟩) ?_ ?_ (by decide)
  · simpa only [BitVec.add_zero] using
      Offset.contains_base (p + BitVec.ofNat 64 d) (d := 0) (n := 8) (k := 8) (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Offset.base_disjoint p lo (by omega)).symm
    · exact (stack.sub_right (Offset.sub_base p hi)).symm

theorem restore_ok (original s : State) (base : s.gpr .x24 = original.gpr .x4)
    (extra : ∀ r ∈ [.x25, .x26, .x27, .x28], s.gpr r = original.gpr r)
    (readable : (⟨original.gpr .x4, 16384⟩ : Region) ∈ s.rd ++ s.wr)
    (values : ∀ r d, (r, d) ∈ saved →
      s.mem.readW (original.gpr .x4 + BitVec.ofNat 64 d) 64 = original.gpr r) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ preserved, t.gpr r = original.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have read (d : Nat) (h : d + 8 ≤ 16384) :
      InRegions (s.rd ++ s.wr) (original.gpr .x4 + BitVec.ofNat 64 d) 8 :=
    ⟨_, readable, Offset.contains_base _ h (by omega)⟩
  have r840 := read 840 (by decide)
  have r848 := read 848 (by decide)
  have r856 := read 856 (by decide)
  have r864 := read 864 (by decide)
  have r872 := read 872 (by decide)
  have r888 := read 888 (by decide)
  have r880 := read 880 (by decide)
  have v840 := values .x19 840 (by decide)
  have v848 := values .x20 848 (by decide)
  have v856 := values .x21 856 (by decide)
  have v864 := values .x22 864 (by decide)
  have v872 := values .x23 872 (by decide)
  have v888 := values .x30 888 (by decide)
  have v880 := values .x24 880 (by decide)
  simp only [Mem.readW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq] at v840 v848 v856 v864 v872 v880 v888
  apply WP.of_runBlock
  simp only [restore, saved, List.map_cons, List.map_nil, runBlock_cons,
    runStep_some, runBlock_nil, exec, addr,
    show (840 : Nat) % 8 = 0 ∧ 840 < 4096 * 8 from by decide,
    show (848 : Nat) % 8 = 0 ∧ 848 < 4096 * 8 from by decide,
    show (856 : Nat) % 8 = 0 ∧ 856 < 4096 * 8 from by decide,
    show (864 : Nat) % 8 = 0 ∧ 864 < 4096 * 8 from by decide,
    show (872 : Nat) % 8 = 0 ∧ 872 < 4096 * 8 from by decide,
    show (880 : Nat) % 8 = 0 ∧ 880 < 4096 * 8 from by decide,
    show (888 : Nat) % 8 = 0 ∧ 888 < 4096 * 8 from by decide,
    and_self, Nat.reduceMul, BitVec.setWidth_eq, Size.bits, Size.bytes,
    State.load,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    base, r840, r848, r856, r864, r872, r880, r888,
    reduceCtorEq, ite_true, ite_false, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ite_true, ite_false,
      v840, v848, v856, v864, v872, v880, v888]
  all_goals exact extra _ (by decide)

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.First`. -/
section
/-! Merged from `Proof.Argon2.AArch64.HPrime.FinishInput`. -/
section
/-! # H′: finalizing the prefixed input -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.AArch64 (wp_mov wp_addImm)

theorem finishInput_ok (v : Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .x24) d)
    (length : d.length = 4 + (s.gpr .x21).toNat) (bound : (s.gpr .x21).toNat < 2 ^ 32)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (finishInput v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x24 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧ Keeps s t := by
  unfold finishInput
  refine WP.seq (wp_mov fun a ha => wp_addImm (by decide) fun u hu => WP.block_nil ?_)
  have ku : Keeps s u := by
    refine ⟨fun r hr _ => ?_, hu.rd.trans ha.rd, hu.wr.trans ha.wr, hu.sp.trans ha.sp, ?_⟩
    · have hn : r ≠ .x1 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hu.other r hn).trans (ha.other r hn)
    · rw [hu.mem, ha.mem]; exact Frame.refl _ _
  have repr' : Repr b h0 u.mem (u.gpr .x24) d := by rw [hu.mem, ha.mem, ku.x24]; exact repr
  have count : u.gpr .x1 = BitVec.ofNat 64 d.length := by
    rw [hu.gpr, ha.gpr, length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_comm _ _
  have len : d.length < 2 ^ 64 := by rw [length]; omega
  have wr : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ku.x24, ku.wr]; exact hwr
  have sw : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [ku.x24, ku.sp]; exact stackWork
  refine (finalize_ok v u h0 d repr' count len (by rw [ku.sp]; exact hsp) wr sw).mono ?_
  rintro t ⟨out, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', finalize_frame _ _ frame⟩⟩
  simpa only [ku.x24] using out

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: the hash of the length prefix and input -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem first_ok (v : Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .x23).toNat ∧ (s.gpr .x23).toNat < 2 ^ 32)
    (len : (s.gpr .x21).toNat < 2 ^ 32)
    (headBytes : bytesAt s.mem (s.gpr .x24 + 832) 4 = Spec.Argon2.le32 (s.gpr .x23).toNat)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .x20, (s.gpr .x21).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .x20, (s.gpr .x21).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackData : (below s.sp 16).Disjoint ⟨s.gpr .x20, (s.gpr .x21).toNat⟩) :
    WP isa (first v.hash) s fun t =>
      (bytesAt t.mem (s.gpr .x24 + 768) 64).take (min (s.gpr .x23).toNat 64) =
        Spec.Argon2.H (min (s.gpr .x23).toNat 64)
          (Spec.Argon2.le32 (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat) ∧
      Keeps s t := by
  unfold first
  refine WP.seq ((chooseLength_ok s hlen.2).mono ?_)
  rintro a ⟨lengthA, ka⟩
  have na : (a.gpr .x1).toNat = min (s.gpr .x23).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have wrA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact hwr
  have swA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  have lenA : 1 ≤ (a.gpr .x1).toNat ∧ (a.gpr .x1).toNat ≤ 64 := by rw [na]; omega
  refine WP.seq ((init_ok v a lenA wrA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  have ku : Keeps a u := ⟨regsU, rdU, wrU, spU, init_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) u.mem (u.gpr .x24) [] := by
    rw [ku.x24]; simpa only [na] using reprU
  have wrU' : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ksu.x24, ksu.wr]; exact hwr
  have swU : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [ksu.x24, ksu.sp]; exact stackWork
  have headU : bytesAt u.mem (u.gpr .x24 + 832) 4 = Spec.Argon2.le32 (s.gpr .x23).toNat := by
    rw [ksu.x24, ksu.prefix stackWork]; exact headBytes
  refine WP.seq ((absorbFixed_ok v u _ 832 4 (by decide) (by rw [ksu.sp]; exact hsp) (by decide) (by decide) reprU' wrU' swU).mono ?_)
  rintro w ⟨reprW, kw⟩
  have ksw := ksu.trans kw
  have r12 : w.gpr .x20 = s.gpr .x20 := ksw.regs _ (by decide) (by decide)
  have r13 : w.gpr .x21 = s.gpr .x21 := ksw.regs _ (by decide) (by decide)
  have headLen : (Spec.Argon2.le32 (s.gpr .x23).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  have reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) w.mem (w.gpr .x24)
      (Spec.Argon2.le32 (s.gpr .x23).toNat) := by
    rw [kw.x24]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  have wrW : (⟨w.gpr .x24, 16384⟩ : Region) ∈ w.wr := by rw [ksw.x24, ksw.wr]; exact hwr
  have dataW : Covers [⟨w.gpr .x20, (w.gpr .x21).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  have dwW : (⟨w.gpr .x20, (w.gpr .x21).toNat⟩ : Region).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [r12, r13, ksw.x24]; exact dataWork
  have swW : (below w.sp 16).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [ksw.sp, ksw.x24]; exact stackWork
  have sdW : (below w.sp 16).Disjoint ⟨w.gpr .x20, (w.gpr .x21).toNat⟩ := by
    rw [ksw.sp, r12, r13]; exact stackData
  have inputW : bytesAt w.mem (w.gpr .x20) (w.gpr .x21).toNat =
      bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .x21).toNat ≤ 2 ^ 64 by omega)
      (dataWork.sub_right (Region.sub_prefix (by decide))) stackData.symm
  refine WP.seq ((absorbInput_ok v w _ _ headLen reprW' (by rw [r13]; exact len)
    (by rw [ksw.sp]; exact hsp) wrW dataW dwW swW sdW).mono ?_)
  rintro x ⟨reprX, kx⟩
  have ksx := ksw.trans kx
  have reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) x.mem (x.gpr .x24)
      (Spec.Argon2.le32 (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat) := by
    rw [kx.x24]; simpa only [inputW] using reprX
  have r13X : x.gpr .x21 = s.gpr .x21 := ksx.regs _ (by decide) (by decide)
  have length : (Spec.Argon2.le32 (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat).length =
      4 + (x.gpr .x21).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  have wrX : (⟨x.gpr .x24, 16384⟩ : Region) ∈ x.wr := by rw [ksx.x24, ksx.wr]; exact hwr
  have swX : (below x.sp 16).Disjoint ⟨x.gpr .x24, 16384⟩ := by
    rw [ksx.sp, ksx.x24]; exact stackWork
  refine (finishInput_ok v x _ _ reprX' length (by rw [r13X]; exact len) (by rw [ksx.sp]; exact hsp) wrX swX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  have result := congrArg (List.take (min (s.gpr .x23).toNat 64)) out
  rw [ksx.x24] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.Finish`. -/
section
/-! Merged from `Proof.Argon2.AArch64.HPrime.Extend`. -/
section
/-! # H′: the prefixes and final digest of a long output -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem maybeChain_ok (v : Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * n + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen))
    (comparison : s.gpr .x9 = if 32 * n + lastLen < 65 then 1 else 0) :
    WP isa (.ite (.nonzero .x .x9) (.block []) (chain v.hash)) s (ChainResult s n) := by
  refine WP.ite (decide (32 * n + lastLen < 65)) (by by_cases h : 32 * n + lastLen < 65 <;>
    simp [eval, State.read, comparison, h]) ?_ ?_
  · intro h
    have hn : n = 0 := by have := of_decide_eq_true h; omega
    subst n
    exact WP.block_nil (ChainResult.refl s)
  · intro h
    have hn : 1 ≤ n := by have := of_decide_eq_false h; omega
    have p := space.prefix (show 32 * n ≤ 32 * n + lastLen by omega)
    exact chain_ok v n lastLen s hn last space.bound space.spBound count p.work p.out p.sep p.stackWork p.stackOut

theorem extendDigest_ok (v : Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (extendDigest v.hash) s fun t =>
      Written s ((bytesAt s.mem (s.gpr .x24 + 768) 64).take 32 ++
        chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)) t ∧
      (bytesAt t.mem (s.gpr .x24 + 768) 64).take lastLen =
        Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64)) ∧
      t.gpr .x23 = BitVec.ofNat 64 lastLen := by
  unfold extendDigest
  have short := space.prefix (show 32 ≤ 32 * (n + 1) + lastLen by omega)
  have sep32 := short.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok s short.work short.out sep32).mono ?_)
  intro a ha
  have wa := Written.of_emitted ha
  have lenA : (bytesAt s.mem (s.gpr .x24 + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have spaceA : Space a (32 * n + lastLen) := space.advance wa (by rw [lenA]; omega)
  have countA : a.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen) := by
    rw [ha.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Offset.ofNat_sub_ofNat (by omega : 32 ≤ 32 * (n + 1) + lastLen)]
    rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega]
  have digestA : bytesAt a.mem (a.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
    rw [wa.x24]; exact ha.digest short.sep
  refine WP.seq ((compare_ok a (by rw [countA, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := spaceA.bound; omega)]; exact spaceA.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  have countU : u.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen) :=
    (compared.other _ (by decide)).trans countA
  have compareU : u.gpr .x9 = if 32 * n + lastLen < 65 then 1 else 0 := by
    rw [compared.value, countA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceA.bound; omega)]
  refine WP.seq ((maybeChain_ok v n lastLen u (spaceA.keeps ku) last countU compareU).mono ?_)
  intro w hw
  have ww := (Written.of_chain hw).before_keeps ku
  have digestU : bytesAt u.mem (u.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
    rw [compared.mem, ku.x24]; exact digestA
  have ww' : Written a (chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)) w := by
    simpa only [digestU] using ww
  have wsw := space.join wa ww' (by rw [lenA, Proof.Argon2.chainPrefixes_length]; omega)
  have produced : ((bytesAt s.mem (s.gpr .x24 + 768) 32) ++
      chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)).length = 32 * (n + 1) := by
    rw [List.length_append, lenA, Proof.Argon2.chainPrefixes_length]; omega
  have spaceW : Space w lastLen := space.advance wsw (by rw [produced])
  have countW : w.gpr .x23 = BitVec.ofNat 64 lastLen := by
    rw [hw.remaining, countU, Offset.ofNat_sub_ofNat (by omega : 32 * n ≤ 32 * n + lastLen)]
    rw [Nat.add_sub_cancel_left]
  have digestW : bytesAt w.mem (w.gpr .x24 + 768) 64 =
      chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [hw.regs .x24 (by decide) (by decide) (by decide) (by decide), hw.digest, digestU]
  refine WP.seq (wp_mov fun x hx => WP.block_nil ?_)
  have kx : Keeps w x := Keeps.of_upd hx (by decide)
  have spaceX := spaceW.keeps kx
  have lenX : (x.gpr .x1).toNat = lastLen := by
    rw [hx.gpr, countW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceW.bound; omega)]
  refine (next_ok v x (by rw [lenX]; omega) spaceX.spBound spaceX.work spaceX.stackWork).mono ?_
  rintro t ⟨dt, kt⟩
  have wwt := Written.of_keeps (kx.trans kt)
  have written := space.join wsw wwt (by rw [produced, List.length_nil]; omega)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_nil, bytesAt_take _ _ 32 64 (by decide)] using written
  · rw [lenX, kx.x24, hx.mem, digestW, wsw.x24] at dt
    exact dt
  · rw [kt.regs _ (by decide) (by decide), kx.regs _ (by decide) (by decide)]; exact countW

theorem longOutput_ok (v : Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (.seq (extendDigest v.hash) copyRemaining) s fun t =>
      Written s (Spec.Argon2.longHash lastLen (n + 1) (bytesAt s.mem (s.gpr .x24 + 768) 64)) t := by
  refine WP.seq ((extendDigest_ok v n lastLen s space last count).mono ?_)
  rintro u ⟨written, digest, remaining⟩
  have len : ((bytesAt s.mem (s.gpr .x24 + 768) 64).take 32 ++
      chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)).length = 32 * (n + 1) := by
    simp only [List.length_append, List.length_take, bytesAt, List.length_map,
      List.length_range, Proof.Argon2.chainPrefixes_length]
    omega
  have spaceU : Space u lastLen := space.advance written (by rw [len])
  refine (copyRemaining_ok u lastLen spaceU (by omega) last.2 remaining).mono ?_
  intro t copied
  have out : bytesAt u.mem (u.gpr .x24 + 768) lastLen =
      Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64)) := by
    rw [written.x24, ← bytesAt_take _ _ lastLen 64 last.2]; exact digest
  have all := space.join written copied (by
    rw [len]; simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl])
  rw [out, ← Proof.Argon2.longHash_chain] at all
  exact all

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: emitting the complete short or long output -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem finishOutput_ok (v : Backend) (s : State) (n : Nat) (input : List Byte)
    (space : Space s n) (positive : 1 ≤ n) (count : s.gpr .x23 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .x24 + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput v.hash) s (Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq ((compare_ok s (by rw [count, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := space.bound; omega)]; exact space.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  have countU : u.gpr .x23 = BitVec.ofNat 64 n := (compared.other _ (by decide)).trans count
  have compareU : u.gpr .x9 = if n < 65 then 1 else 0 := by
    rw [compared.value, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := space.bound; omega)]
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by by_cases h : n < 65 <;> simp [eval, State.read, compareU, h]) ?_ ?_
  · intro h
    have short : n ≤ 64 := by have := of_decide_eq_true h; omega
    apply WP.block_nil
    refine (copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have value : bytesAt u.mem (u.gpr .x24 + 768) n = Spec.Argon2.hPrime n input := by
      rw [compared.mem, ku.x24, ← bytesAt_take _ _ n 64 short]
      simpa only [Nat.min_eq_left short, Spec.Argon2.hPrime, ite_eq_left short] using digest
    rw [value] at result
    exact result
  · intro h
    have long : 64 < n := by have := of_decide_eq_false h; omega
    let r := (n + 31) / 32 - 2
    let lastLen := n - 32 * r
    have bounds : 1 ≤ r ∧ 33 ≤ lastLen ∧ lastLen ≤ 64 ∧ 32 * r + lastLen = n :=
      Proof.Argon2.longHash_bounds n long
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
    change r = q + 1 at hq
    have size : 32 * (q + 1) + lastLen = n := by rw [← hq]; exact bounds.2.2.2
    have spaceU : Space u (32 * (q + 1) + lastLen) := by rw [size]; exact space.keeps ku
    have countLong : u.gpr .x23 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (longOutput_ok v q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have digestU : bytesAt u.mem (u.gpr .x24 + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [compared.mem, ku.x24]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega), bytesAt_take _ _ 64 64 (by decide)] using digest
    have value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .x24 + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega)]
    rw [value] at result
    exact result

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: functional correctness of the complete ARM64 program -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem code_wp (v : Backend) (s : State) (pre : localContract.pre s) :
    WP isa (code v.hash) s fun t => localContract.post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      Frame [outputR s, workR s, stackR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, hsp, dw, ow, sd, so, sw⟩ := pre
  have work : (workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((setup_ok s work).mono ?_)
  intro a ha
  have sp := ha.sp
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  have dataA : Covers [⟨a.gpr .x20, (a.gpr .x21).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  have dwA : (⟨a.gpr .x20, (a.gpr .x21).toNat⟩ : Region).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  have swA : (below (a.sp) 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [sp, ha.workspace]; exact sw
  have sdA : (below (a.sp) 16).Disjoint ⟨a.gpr .x20, (a.gpr .x21).toNat⟩ := by
    rw [sp, ha.input, ha.length]; exact sd
  have inputA : bytesAt a.mem (a.gpr .x20) (a.gpr .x21).toNat =
      bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (setupMem_frame s).bytes (R := inputR s) _ (show (s.gpr .x1).toNat ≤ 2 ^ 64 by omega) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 64 ≤ 16384))
  have headA : bytesAt a.mem (a.gpr .x24 + 832) 4 = Spec.Argon2.le32 (a.gpr .x23).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact setupMem_prefix s
  have spaceA : Space a (s.gpr .x3).toNat := by
    refine ⟨hi, by rw [sp]; exact hsp, workA, ?_, ?_, swA, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
    · rw [sp, ha.output]; exact so
  refine WP.seq ((first_ok v a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA (by rw [sp]; exact hsp) workA dataA dwA swA sdA).mono ?_)
  rintro b ⟨digestB, kb⟩
  have spaceB := spaceA.keeps kb
  have countB : b.gpr .x23 = BitVec.ofNat 64 (s.gpr .x3).toNat := by
    rw [kb.regs _ (by decide) (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have digestB' : (bytesAt b.mem (b.gpr .x24 + 768) 64).take (min (s.gpr .x3).toNat 64) =
      Spec.Argon2.H (min (s.gpr .x3).toNat 64)
        (Spec.Argon2.le32 (s.gpr .x3).toNat ++ bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) := by
    rw [kb.x24]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((finishOutput_ok v b (s.gpr .x3).toNat
    (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  have baseB : b.gpr .x24 = s.gpr .x4 := kb.x24.trans ha.workspace
  have spB : b.sp = s.sp := kb.sp.trans sp
  have dstB : b.gpr .x22 = s.gpr .x2 := (kb.regs _ (by decide) (by decide)).trans ha.output
  have wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  have frame : Frame [⟨s.gpr .x4, 832⟩, stackR s, outputR s] a.mem x.mem := by
    have fb : Frame [⟨s.gpr .x4, 832⟩, stackR s, outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace, sp] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, spB, dstB, stackR, outputR, Proof.Argon2.hPrime_length] using hx.frame)
  have values : ∀ r d, (r, d) ∈ saved →
      x.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hr
    have bounds : ∀ rd ∈ saved, 832 ≤ rd.2 ∧ rd.2 + 8 ≤ 16384 := by decide
    obtain ⟨dlo, dhi⟩ := bounds (r, d) hr
    have keep : x.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 =
        a.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 := by
      apply frame.readW (r := ⟨s.gpr .x4 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact (Offset.base_disjoint _ dlo (by omega)).symm
      · exact (sw.sub_right (Offset.sub_base _ dhi)).symm
      · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
    rw [keep, ha.mem]; exact setupMem_saved s r d hr
  have baseX := hx.x24.trans baseB
  have spX := hx.sp.trans spB
  have readable : workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (restore_ok s x baseX (by
    intro r hr
    have hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h30 : r ≠ .x30 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h22 : r ≠ .x22 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h23 : r ≠ .x23 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [hx.regs r hp h30 h22 h23, kb.regs r hp h30]
    exact ha.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) h22 h23) readable values).mono ?_
  rintro t ⟨regs, mem, _, _⟩
  refine ⟨?_, regs, ?_⟩
  · change bytesAt t.mem (s.gpr .x2) (s.gpr .x3).toNat = _
    rw [mem]
    simpa only [dstB, Proof.Argon2.hPrime_length] using hx.bytes
  · rw [mem]
    have setupFrame : Frame [outputR s, workR s, stackR s] s.mem a.mem := by
      rw [ha.mem]
      apply (setupMem_frame s).sub
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        Offset.sub_base _ (by decide : 832 + 64 ≤ 16384)⟩
    apply setupFrame.trans
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨stackR s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    · exact ⟨outputR s, List.mem_cons_self .., fun _ h => h⟩

theorem code_keepsV (v : Backend) : (code v.hash).allInstrs keepsV = true := by
  simp only [code, setup, saved, first, chooseLength, Impl.Argon2.AArch64.HPrime.init,
    initArgs, absorbFixed, fixedArgs, Impl.Argon2.AArch64.HPrime.update, updateArgs,
    absorbInput, inputArgs, finishInput, Impl.Argon2.AArch64.HPrime.finalize, finalizeArgs,
    finishOutput, extendDigest, emitPrefix, copy, copyByte, chain, next, copyRemaining,
    restore, Code.allInstrs]
  rw [v.initV, v.updateV, v.finalizeV]
  decide +kernel

theorem code_correct (v : Backend) (s : State) (pre : localContract.pre s) :
    ∃ tr t, Exec isa (code v.hash) s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr, t, run, post, regs, _⟩ := code_wp v s pre
  exact ⟨tr, t, run, ⟨regs, VG.AArch64.Exec.sp run,
    VG.AArch64.Exec.preservedV run (code_keepsV v)⟩, post⟩

end VG.Proof.Argon2.AArch64.HPrime
