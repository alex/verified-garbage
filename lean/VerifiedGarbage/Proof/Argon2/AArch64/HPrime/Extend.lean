import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Compare
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Space

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
