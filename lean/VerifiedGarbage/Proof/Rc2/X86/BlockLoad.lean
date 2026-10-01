import VerifiedGarbage.Proof.Rc2.X86.Cipher
import VerifiedGarbage.Proof.Rc2.Memory

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem decode_word (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m p)).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  rw [Spec.Rc2.decodeBlock, getD_ofFn _ i hi]
  change ((Spec.Rc2.blockAt m p).getD (2 * i) 0).setWidth 16 |||
    ((Spec.Rc2.blockAt m p).getD (2 * i + 1) 0).setWidth 16 <<< 8 = _
  rw [Spec.Rc2.blockAt, getD_ofFn _ _ (by omega), getD_ofFn _ _ (by omega)]

theorem loadWord_ok (s : State) (i : Nat) (hi : i < 4)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1)
    (writable : InRegions s.wr (wordBase s + BitVec.ofNat 64 (4 * i)) 4) :
    ∃ s', runBlock isa (loadWord i) s = some s' ∧
      Keep [.eax, .edx] {s with mem := (s.mem.writeW (wordBase s + BitVec.ofNat 64 (4 * i))
        (((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))).getD i 0).setWidth 32))} s' := by
  have lo := readable (2 * i) (by omega)
  have high := readable (2 * i + 1) (by omega)
  have a := addr_add (x := s.gpr .edi) (k := 2 * i) (by omega)
  have b := addr_add (x := s.gpr .edi) (k := 2 * i + 1) (by omega)
  have c : addr32 (s.gpr .ebp + BitVec.ofNat 32 (wordOff i)) = wordBase s + BitVec.ofNat 64 (4 * i) := by
    rw [addr_add (by simp only [wordOff, Nat.mod_eq_of_lt hi]; omega), wordOff_eq s i hi]
  refine ⟨_, by
    simp (config := {decide := true}) only [loadWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, readSrc, State.ea, memOp, State.load8, State.store32,
      ← addr_eq_def, a, b, c, lo, high, writable, ite_true, ite_false,
      Option.map_some, Option.bind_some, gpr_setReg, gpr_setFlags, gpr_arithFlags,
      mem_setReg, mem_setFlags, mem_arithFlags, rd_setReg, rd_setFlags, rd_arithFlags,
      wr_setReg, wr_setFlags, wr_arithFlags]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, hr.1, hr.2, ite_false]
  · rw [decode_word _ _ i hi, Word32.joinBytes]
  · rfl
  · rfl

theorem loadBlockWords_ok (n : Nat) (hn : n ≤ 4) (s : State)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1)
    (writable : ∀ i < 4, InRegions s.wr (wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (addr32 (s.gpr .edi)) 8).Disjoint ⟨wordBase s, 16⟩) :
    WP isa (.block ((List.range n).flatMap loadWord)) s (fun s' =>
      Keep [.eax, .edx] {s with mem := (saveMem s.mem (wordBase s)
        (fun i => ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))).getD i 0).setWidth 32) n)} s') := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    apply WP.mono (ih (by omega))
    intro s₁ keep₁
    have ptr₁ := keep₁.reg .edi (by decide)
    have scratch₁ := keep₁.reg .ebp (by decide)
    have base₁ : wordBase s₁ = wordBase s := by unfold wordBase; rw [scratch₁]
    have frame₁ : Frame [⟨wordBase s, 16⟩] s.mem s₁.mem := by
      rw [keep₁.mem]
      exact saveMem_frame_le _ _ _ n 4 (by omega) (by decide)
    have block₁ : Spec.Rc2.blockAt s₁.mem (addr32 (s₁.gpr .edi)) = Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)) := by
      rw [ptr₁]
      exact blockAt_frame frame₁ _ (by simpa using sep)
    obtain ⟨s₂, run₂, keep₂⟩ := loadWord_ok s₁ n (by omega)
      (by rw [ptr₁]; exact fit) (by rw [scratch₁]; exact scratchFit)
      (by rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable)
      (by rw [keep₁.wr, base₁]; exact writable n (by omega))
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    refine ⟨fun r hr => (keep₂.reg r hr).trans (keep₁.reg r hr), ?_,
      keep₂.rd.trans keep₁.rd, keep₂.wr.trans keep₁.wr⟩
    rw [keep₂.mem, block₁, keep₁.mem, base₁, saveMem_succ]

theorem blockLoad_ok (s : State)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1)
    (writable : ∀ i < 4, InRegions s.wr (wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (addr32 (s.gpr .edi)) 8).Disjoint ⟨wordBase s, 16⟩) :
    WP isa (.block ((List.range 4).flatMap loadWord)) s (fun s' =>
      MemWords s'.mem (wordBase s') (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))) ∧
      RoundFrame s s') := by
  apply WP.mono (loadBlockWords_ok 4 (by decide) s fit scratchFit readable writable sep)
  intro s' h
  have base : wordBase s' = wordBase s := by unfold wordBase; rw [h.reg .ebp (by decide)]
  constructor
  · intro i hi
    rw [base, h.mem]
    exact saveMem_read s.mem (wordBase s)
      (fun j => ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))).getD j 0).setWidth 32)
      4 (by decide) i hi
  · refine ⟨fun r hr => h.reg r (fun hm => hr ((by decide : ∀ r ∈ [.eax, .edx], r ∈ roundWrites) r hm)),
      h.rd, h.wr, ?_⟩
    rw [h.mem]
    exact saveMem_frame s.mem (wordBase s)
      (fun j => ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))).getD j 0).setWidth 32)
      4 (by decide)

end VG.Proof.Rc2.X86
