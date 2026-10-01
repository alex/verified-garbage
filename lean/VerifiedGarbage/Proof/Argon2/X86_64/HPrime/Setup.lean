import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Spec.Argon2

/-! # H′: saving the caller and writing the length prefix -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

/-- Save the six caller registers and then the four-byte length prefix. -/
def setupMem (s : State) : Mem :=
  (saved.foldl (fun m rd => m.writeW (s.gpr .r8 + BitVec.ofNat 64 rd.2) (s.gpr rd.1)) s.mem).writeW
    (s.gpr .r8 + 832) ((s.gpr .rcx).setWidth 32)

theorem setupMem_frame (s : State) :
    Frame [⟨s.gpr .r8 + 832, 56⟩] s.mem (setupMem s) := by
  have store {m : Mem} (h : Frame [⟨s.gpr .r8 + 832, 56⟩] s.mem m)
      (d w : Nat) (v : BitVec w) (lo : 832 ≤ d) (hi : d + w / 8 ≤ 888) :
      Frame [⟨s.gpr .r8 + 832, 56⟩] s.mem (m.writeW (s.gpr .r8 + BitVec.ofNat 64 d) v) :=
    h.writeW (List.mem_singleton_self _) v (Offset.contains _ lo hi (by decide))
  unfold setupMem saved
  simp only [List.foldl_cons, List.foldl_nil]
  apply store (d := 832) (w := 32) _ _ (by decide) (by decide)
  apply store (d := 880) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 872) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 864) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 856) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 848) (w := 64) _ _ (by decide) (by decide)
  exact store (Frame.refl _ _) 840 64 _ (by decide) (by decide)

theorem setupMem_prefix (s : State) :
    Spec.Blake2.bytesAt (setupMem s) (s.gpr .r8 + 832) 4 =
      Spec.Argon2.le32 (s.gpr .rcx).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl)]
  unfold setupMem
  rw [Mem.readW_writeW_self32]
  rfl

theorem setupMem_saved (s : State) (r : Reg) (d : Nat) (hr : (r, d) ∈ saved) :
    (setupMem s).readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  have skip64 (m : Mem) (v : BitVec 64) (d e : Nat)
      (sep : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
      (m.writeW (s.gpr .r8 + BitVec.ofNat 64 e) v).readW
        (s.gpr .r8 + BitVec.ofNat 64 d) 64 = m.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 :=
    Mem.readW_writeW_sep (Offset.sep _ sep hd he) (by decide)
  have skip32 (m : Mem) (v : BitVec 32) (d : Nat) (lo : 836 ≤ d) (hi : d + 8 ≤ 2 ^ 64) :
      (m.writeW (s.gpr .r8 + 832) v).readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 =
        m.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 :=
    Mem.readW_writeW_sep (Offset.sep _ (Or.inr lo) hi (by decide)) (by decide)
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp (disch := decide) only [setupMem, saved, List.foldl_cons, List.foldl_nil,
      skip32, skip64, Mem.readW_writeW_self64]

structure Setup (s t : State) : Prop where
  workspace : t.gpr .rbx = s.gpr .r8
  input : t.gpr .r12 = s.gpr .rdi
  length : t.gpr .r13 = s.gpr .rsi
  output : t.gpr .r14 = s.gpr .rdx
  remaining : t.gpr .r15 = s.gpr .rcx
  other : ∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  mem : t.mem = setupMem s
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem setup_ok (s : State) (hw : (⟨s.gpr .r8, 16384⟩ : Region) ∈ s.wr) :
    WP isa (.block setup) s (Setup s) := by
  have write (d n : Nat) (h : d + n ≤ 16384) :
      InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 d) n :=
    ⟨_, hw, Offset.contains_base _ h (by omega)⟩
  have w832 := write 832 4 (by decide)
  have w840 := write 840 8 (by decide)
  have w848 := write 848 8 (by decide)
  have w856 := write 856 8 (by decide)
  have w864 := write 864 8 (by decide)
  have w872 := write 872 8 (by decide)
  have w880 := write 880 8 (by decide)
  apply WP.of_runBlock
  simp only [setup, saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.store64, State.store32,
    ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    w832, w840, w848, w856, w864, w872, w880, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun r h1 h2 h3 h4 h5 => ?_, ?_, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg, h1, h2, h3, h4, h5, ite_false]
  · rfl

end VG.Proof.Argon2.X86_64.HPrime
