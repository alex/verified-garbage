import VerifiedGarbage.Proof.Argon2.X86_64.InitialStart
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Output
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize

/-! Merged from `Proof.Argon2.X86_64.InitialFinish`. -/
section
/-! # H₀: finalize BLAKE2b and copy the digest into the derivation frame -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

structure Finished (s t : State) : Prop where
  regs : ∀ r ∈ calleeSaved, r ≠ .r12 → r ≠ .r14 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .rbp, 64⟩] s.mem t.mem

theorem finishCount_ok (s : State) :
    WP isa (.block [.mov .rsi (.reg .r12)]) s fun t =>
      t.gpr .rsi = s.gpr .r12 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, Frame.refl _ _⟩
  have hn : r ≠ .rsi := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_setReg, hn, ite_false]

theorem finishOutput_ok (s : State) :
    WP isa (.block [.mov .r14 (.reg .rbp), .mov32 .rax (.imm 64)]) s fun t =>
      t.gpr .r14 = s.gpr .rbp ∧ t.gpr .rax = 64 ∧ t.mem = s.mem ∧ Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    RegUpd.mem_setReg]
  refine ⟨rfl, rfl, trivial, fun r hr h12 h14 => ?_, rfl, rfl, Frame.refl _ _⟩
  have hn : r ≠ .rax := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_setReg, hn, h14, ite_false]

theorem finish_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (h : Space s)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .rbx) d)
    (count : s.gpr .r12 = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64) :
    WP isa (finish (HPrime.hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) d ∧
      Finished s t := by
  unfold finish
  refine WP.seq ((finishCount_ok s).mono ?_)
  rintro a ⟨countA, memA, ka'⟩
  have ka := Keeps.of_hash ka'
  have hA := h.keeps ka
  have reprA : Repr b (Spec.Blake2.init b 64 0) a.mem (a.gpr .rbx) d := by
    rw [memA, ka.rbx]; exact repr
  refine WP.seq ((HPrime.finalize_ok v a _ d reprA (countA.trans count) bound
    hA.work hA.stackWork).mono ?_)
  rintro u ⟨digestU, regsU, rdU, wrU, frameU⟩
  have ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, HPrime.finalize_frame _ _ frameU⟩
  have ksu := ka.trans ku
  refine WP.seq ((finishOutput_ok u).mono ?_)
  rintro w ⟨dstW, countW, memW, kw⟩
  have ksw := ksu.trans kw
  have hW := h.keeps ksw
  have outW : ∀ i < 64, InRegions w.wr (w.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [dstW, ← kw.rbp]
    rcases hW.output with ⟨r, hr, hc⟩
    exact ⟨r, hr, hc.byte (by rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]; exact hi)⟩
  have sepW : (⟨w.gpr .rbx + 768, 64⟩ : Region).Disjoint ⟨w.gpr .r14, 64⟩ := by
    rw [dstW, ← kw.rbp]
    exact (hW.frameWork.sub_left (Region.sub_prefix (by decide : 64 ≤ 272))).symm.sub_left
      (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  refine (HPrime.copy_ok w 64 (by decide) (by decide) countW hW.work outW sepW).mono ?_
  intro t ht
  have sourceLength : (bytesAt w.mem (w.gpr .rbx + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨?_, fun r hr h12 h14 => ?_, ht.rd.trans ksw.rd, ht.wr.trans ksw.wr, ?_⟩
  · have dst : w.gpr .r14 = s.gpr .rbp := dstW.trans ksu.rbp
    rw [ht.mem]
    conv_lhs => arg 2; rw [← dst]
    have copied := HPrime.bytesAt_writeBytes w.mem (w.gpr .r14)
      (bytesAt w.mem (w.gpr .rbx + 768) 64) (by rw [sourceLength]; decide)
    rw [sourceLength] at copied
    rw [copied, memW, kw.rbx, ku.rbx]
    exact digestU
  · have hrax : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ht.other r hrax hrcx hrdx h14).trans (ksw.regs r hr h12 h14)
  · apply Frame.trans (ksw.frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))))
    apply ht.frame.mono
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [dstW, ksu.rbp]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end VG.Proof.Argon2.X86_64.Initial
end

/-! # Correctness of H₀ for every verified BLAKE2b backend -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)
open VG.Proof.Argon2 (appendInput)

abbrev inputs : List (Nat × Nat) :=
  [(passwordOffset, passwordLenOffset), (saltOffset, saltLenOffset),
   (secretOffset, secretLenOffset), (adOffset, adLenOffset)]

def message (s : State) (ps : List (Nat × Nat)) (d : List Byte) : List Byte :=
  ps.foldl (fun m p => appendInput m (inputBytes s p.1 p.2)) d

def inputSize (s : State) (ps : List (Nat × Nat)) : Nat :=
  (ps.map fun p => 4 + (wordAt s p.2).toNat).sum

def remaining (h : VG.Impl.Argon2.X86_64.HPrime.Hash) : List (Nat × Nat) → Prog isa
  | [] => finish h
  | p :: ps => .seq (absorb h p.1 p.2) (remaining h ps)

theorem message_keeps {s t : State} (ps : List (Nat × Nat)) (d : List Byte)
    (ready : ∀ p ∈ ps, InputReady s p.1 p.2) (k : Keeps s t) :
    message t ps d = message s ps d := by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih =>
    simp only [message, List.foldl_cons]
    rw [(ready p (by simp only [List.mem_cons, true_or])).bytes_keeps k]
    exact ih _ (fun q hq => ready q (List.mem_cons_of_mem p hq))

theorem inputSize_keeps {s t : State} (ps : List (Nat × Nat))
    (ready : ∀ p ∈ ps, InputReady s p.1 p.2) (k : Keeps s t) :
    inputSize t ps = inputSize s ps := by
  unfold inputSize
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [(ready p hp).space.word_keeps k p.2 (ready p hp).lengthBound]

theorem Finished.before {s u t : State} (k : Keeps s u) (f : Finished u t) : Finished s t := by
  refine ⟨fun r hr h12 h14 => (f.regs r hr h12 h14).trans (k.regs r hr h12 h14),
    f.rd.trans k.rd, f.wr.trans k.wr, ?_⟩
  apply (k.frame.mono ?_).trans
  · simpa only [k.rbx, k.rsp, k.rbp] using f.frame
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))

theorem remaining_ok (v : Proof.Blake2.X86_64.Backend) (ps : List (Nat × Nat))
    (s : State) (space : Space s) (ready : ∀ p ∈ ps, InputReady s p.1 p.2)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .rbx) d)
    (count : s.gpr .r12 = BitVec.ofNat 64 d.length)
    (bound : d.length + inputSize s ps < 2 ^ 64) :
    WP isa (remaining (HPrime.hash v) ps) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 =
        Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) (message s ps d) ∧ Finished s t := by
  induction ps generalizing s d with
  | nil =>
    exact finish_ok v s space d repr count (by simpa only [inputSize, List.map_nil,
      List.sum_nil, Nat.add_zero] using bound)
  | cons p ps ih =>
    have hp := ready p (by simp only [List.mem_cons, true_or])
    have tailReady : ∀ q ∈ ps, InputReady s q.1 q.2 := fun q hq =>
      ready q (List.mem_cons_of_mem p hq)
    have size : inputSize s (p :: ps) = 4 + (wordAt s p.2).toNat + inputSize s ps := rfl
    refine WP.seq ((absorb_ok v s p.1 p.2 hp d repr count (by rw [size] at bound; omega)).mono ?_)
    rintro u ⟨reprU, countU, ku⟩
    refine (ih u (space.keeps ku) (fun q hq => (tailReady q hq).keeps ku)
      _ reprU countU ?_).mono ?_
    · rw [inputSize_keeps ps tailReady ku, Proof.Argon2.appendInput_length, inputBytes_length]
      rw [size] at bound; omega
    · rintro t ⟨digestT, ft⟩
      refine ⟨?_, ft.before ku⟩
      rw [ku.rbp] at digestT
      rw [message_keeps ps _ tailReady ku] at digestT
      exact digestT

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (space : Space s)
    (ready : ∀ p ∈ inputs, InputReady s p.1 p.2) :
    WP isa (code (HPrime.hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 =
        Spec.Argon2.H 64 (message s inputs (headerBytes s)) ∧ Finished s t := by
  change WP isa (.seq (start (HPrime.hash v)) (remaining (HPrime.hash v) inputs)) s _
  refine WP.seq ((start_ok v s space).mono ?_)
  rintro u ⟨reprU, countU, ku⟩
  have count : u.gpr .r12 = BitVec.ofNat 64 (headerBytes s).length := by
    rw [headerBytes_length]; exact countU
  have bound : (headerBytes s).length + inputSize s inputs < 2 ^ 64 := by
    have hp := (ready (passwordOffset, passwordLenOffset) (by decide)).length
    have hs := (ready (saltOffset, saltLenOffset) (by decide)).length
    have hk := (ready (secretOffset, secretLenOffset) (by decide)).length
    have ha := (ready (adOffset, adLenOffset) (by decide)).length
    simp only at hp hs hk ha
    rw [headerBytes_length]
    change 24 + (4 + (wordAt s passwordLenOffset).toNat +
      (4 + (wordAt s saltLenOffset).toNat + (4 + (wordAt s secretLenOffset).toNat +
      (4 + (wordAt s adLenOffset).toNat + 0)))) < 2 ^ 64
    omega
  refine (remaining_ok v inputs u (space.keeps ku) (fun p hp => (ready p hp).keeps ku)
    _ reprU count (by rw [inputSize_keeps inputs ready ku]; exact bound)).mono ?_
  rintro t ⟨digestT, ft⟩
  refine ⟨?_, ft.before ku⟩
  rw [ku.rbp, message_keeps inputs _ ready ku] at digestT
  rw [Proof.Argon2.H_stream, ← digestT]
  exact (List.take_of_length_le (by simp only [bytesAt, List.length_map, List.length_range,
    Nat.le_refl])).symm

/-- The public header is supplied by the enclosing argument-validation proof.
The byte-string contents remain unrestricted. -/
theorem initialHash_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (space : Space s)
    (ready : ∀ p ∈ inputs, InputReady s p.1 p.2) (p : Spec.Argon2.Params)
    (header : headerBytes s = Proof.Argon2.initialHeader p) :
    WP isa (code (HPrime.hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 = Spec.Argon2.initialHash p
        (inputBytes s passwordOffset passwordLenOffset) (inputBytes s saltOffset saltLenOffset)
        (inputBytes s secretOffset secretLenOffset) (inputBytes s adOffset adLenOffset) ∧
      Finished s t := by
  refine (code_ok v s space ready).mono ?_
  rintro t ⟨digest, frame⟩
  refine ⟨?_, frame⟩
  rw [header] at digest
  exact digest

end VG.Proof.Argon2.X86_64.Initial
