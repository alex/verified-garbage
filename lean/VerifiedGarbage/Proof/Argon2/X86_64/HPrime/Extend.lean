import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Space

/-! # H′: the prefixes and final digest of a long output -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov wp_cmpi)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem maybeChain_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * n + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen))
    (cf : s.cf = some (decide (32 * n + lastLen < 65))) :
    WP isa (.ite .b (.block []) (chain (hash v))) s (ChainResult s n) := by
  refine WP.ite (decide (32 * n + lastLen < 65)) (by simp only [eval, cf]) ?_ ?_
  · intro h
    have hn : n = 0 := by have := of_decide_eq_true h; omega
    subst n
    exact WP.block_nil (ChainResult.refl s)
  · intro h
    have hn : 1 ≤ n := by have := of_decide_eq_false h; omega
    have p := space.prefix (show 32 * n ≤ 32 * n + lastLen by omega)
    exact chain_ok v n lastLen s hn last space.bound count p.work p.out p.sep p.stackWork p.stackOut

theorem extendDigest_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (extendDigest (hash v)) s fun t =>
      Written s ((bytesAt s.mem (s.gpr .rbx + 768) 64).take 32 ++
        chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) t ∧
      (bytesAt t.mem (s.gpr .rbx + 768) 64).take lastLen =
        Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64)) ∧
      t.gpr .r15 = BitVec.ofNat 64 lastLen := by
  unfold extendDigest
  have short := space.prefix (show 32 ≤ 32 * (n + 1) + lastLen by omega)
  have sep32 := short.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok s short.work short.out sep32).mono ?_)
  intro a ha
  have wa := Written.of_emitted ha
  have lenA : (bytesAt s.mem (s.gpr .rbx + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have spaceA : Space a (32 * n + lastLen) := space.advance wa (by rw [lenA]; omega)
  have countA : a.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := by
    rw [ha.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Offset.ofNat_sub_ofNat (by omega : 32 ≤ 32 * (n + 1) + lastLen)]
    rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega]
  have digestA : bytesAt a.mem (a.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [wa.rbx]; exact ha.digest short.sep
  refine WP.seq (wp_cmpi fun u gu mu ru wu cf _ => WP.block_nil ?_)
  have ku : Keeps a u := ⟨fun r _ => congrFun gu r, ru, wu, by rw [mu]; exact Frame.refl _ _⟩
  have countU : u.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := (congrFun gu _).trans countA
  have cfU : u.cf = some (decide (32 * n + lastLen < 65)) := by
    rw [cf, countA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt spaceA.bound]; rfl
  refine WP.seq ((maybeChain_ok v n lastLen u (spaceA.keeps ku) last countU cfU).mono ?_)
  intro w hw
  have ww := (Written.of_chain hw).before_keeps ku
  have digestU : bytesAt u.mem (u.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [mu, gu]; exact digestA
  have ww' : Written a (chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) w := by
    simpa only [digestU] using ww
  have wsw := space.join wa ww' (by rw [lenA, Proof.Argon2.chainPrefixes_length]; omega)
  have produced : ((bytesAt s.mem (s.gpr .rbx + 768) 32) ++
      chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)).length = 32 * (n + 1) := by
    rw [List.length_append, lenA, Proof.Argon2.chainPrefixes_length]; omega
  have spaceW : Space w lastLen := space.advance wsw (by rw [produced])
  have countW : w.gpr .r15 = BitVec.ofNat 64 lastLen := by
    rw [hw.remaining, countU, Offset.ofNat_sub_ofNat (by omega : 32 * n ≤ 32 * n + lastLen)]
    rw [Nat.add_sub_cancel_left]
  have digestW : bytesAt w.mem (w.gpr .rbx + 768) 64 =
      chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [hw.regs .rbx (by decide) (by decide) (by decide), hw.digest, digestU]
  refine WP.seq (wp_mov fun x hx _ _ => WP.block_nil ?_)
  have kx : Keeps w x := by
    refine ⟨fun r hr => ?_, hx.rd, hx.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hx.other r hn
    · rw [hx.mem]; exact Frame.refl _ _
  have spaceX := spaceW.keeps kx
  have lenX : (x.gpr .rsi).toNat = lastLen := by
    rw [hx.gpr, countW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt spaceW.bound]
  refine (next_ok v x (by rw [lenX]; omega) spaceX.work spaceX.stackWork).mono ?_
  rintro t ⟨dt, kt⟩
  have wwt := Written.of_keeps (kx.trans kt)
  have written := space.join wsw wwt (by rw [produced, List.length_nil]; omega)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_nil, bytesAt_take _ _ 32 64 (by decide)] using written
  · rw [lenX, kx.rbx, hx.mem, digestW, wsw.rbx] at dt
    exact dt
  · rw [kt.regs _ (by decide), kx.regs _ (by decide)]; exact countW

theorem longOutput_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (.seq (extendDigest (hash v)) copyRemaining) s fun t =>
      Written s (Spec.Argon2.longHash lastLen (n + 1) (bytesAt s.mem (s.gpr .rbx + 768) 64)) t := by
  refine WP.seq ((extendDigest_ok v n lastLen s space last count).mono ?_)
  rintro u ⟨written, digest, remaining⟩
  have len : ((bytesAt s.mem (s.gpr .rbx + 768) 64).take 32 ++
      chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)).length = 32 * (n + 1) := by
    simp only [List.length_append, List.length_take, bytesAt, List.length_map,
      List.length_range, Proof.Argon2.chainPrefixes_length]
    omega
  have spaceU : Space u lastLen := space.advance written (by rw [len])
  refine (copyRemaining_ok u lastLen spaceU (by omega) last.2 remaining).mono ?_
  intro t copied
  have out : bytesAt u.mem (u.gpr .rbx + 768) lastLen =
      Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64)) := by
    rw [written.rbx, ← bytesAt_take _ _ lastLen 64 last.2]; exact digest
  have all := space.join written copied (by
    rw [len]; simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl])
  rw [out, ← Proof.Argon2.longHash_chain] at all
  exact all

end VG.Proof.Argon2.X86_64.HPrime
