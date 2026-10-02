import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderWords
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-! Compose the seven input fields, preserving frame reads across every write. -/

namespace VG.Proof.Argon2.X86_64.AddressHeader

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressHeader

def value (s : State) (i : Nat) : Addr :=
  if i = 1 then s.gpr .rbx else if i = 2 then s.gpr .r14
  else s.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64

def headerMem (s : State) (p : Addr) : Nat → Mem
  | 0 => s.mem
  | n + 1 => (headerMem s p n).writeW (off p (8 * n)) (value s n)

theorem field_ok (s : State) (i : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) (frameOffset i)) 8)
    (hw : InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (field i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i)) (value s i) ∧
      CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  unfold field value
  by_cases one : i = 1
  · simp only [one, ite_true]
    refine (registerWord_ok s 1 .rbx (one ▸ hw)).mono ?_
    rintro t ⟨mem, regs, rd, wr, mx⟩
    exact ⟨mem, ⟨fun r _ => congrFun regs r, rd, wr⟩, mx⟩
  · simp only [one, ite_false]
    by_cases two : i = 2
    · simp only [two, ite_true]
      refine (registerWord_ok s 2 .r14 (two ▸ hw)).mono ?_
      rintro t ⟨mem, regs, rd, wr, mx⟩
      exact ⟨mem, ⟨fun r _ => congrFun regs r, rd, wr⟩, mx⟩
    · simp only [two, ite_false]
      refine (frameWord_ok s i (frameOffset i) hr hw).mono ?_
      rintro t ⟨mem, regs, rd, wr, mx⟩
      exact ⟨mem, ⟨regs, rd, wr⟩, mx⟩

theorem offset_bound : ∀ i < 7, frameOffset i + 8 ≤ 272 := by decide +kernel

theorem offset_read (s : State) (i : Nat)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) (frameOffset i)) 8 := by
  apply reads
  unfold frameOffset
  split <;> [simp; skip]
  split <;> [simp; skip]
  split <;> [simp; skip]
  split <;> simp

theorem value_kept {s t : State} (keeps : CopyKeeps s t)
    (hf : Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩)
    (i : Nat) (hi : i < 7) : value t i = value s i := by
  unfold value
  rw [keeps.1 .rbx (by decide), keeps.1 .r14 (by decide), keeps.1 .rbp (by decide)]
  have read : t.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64 =
      s.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64 :=
    hf.readW (r := ⟨s.gpr .rbp, 272⟩)
      (Offset.contains_base _ (offset_bound i hi)
        (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) (offset_bound i hi)) (by decide)))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep) (by decide)
  rw [read]

theorem prefix_ok (n : Nat) (hn : n ≤ 7) (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩) :
    WP isa (.block (fields n)) s fun t =>
      t.mem = headerMem s (s.gpr .rdi) n ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, Frame.refl _ _, CopyKeeps.refl s, rfl⟩
  | succ n ih =>
    simp only [fields, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro a ⟨mem, frame, keeps, mx⟩
    have dest : a.gpr .rdi = s.gpr .rdi := keeps.1 .rdi (by decide)
    have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) (frameOffset n)) 8 := by
      rw [keeps.2.1, keeps.2.2, keeps.1 .rbp (by decide)]
      exact offset_read s n reads
    have writable : InRegions a.wr (off (a.gpr .rdi) (8 * n)) 8 := by
      rw [dest, keeps.2.2]
      exact write _ _ ⟨⟨s.gpr .rdi, 1024⟩, by simp,
        Offset.contains_base _ (d := 8 * n) (n := 8) (k := 1024) (by omega) (by omega)⟩
    refine (field_ok a n read writable).mono ?_
    rintro t ⟨mem', keeps', mx'⟩
    have value' := value_kept keeps frame sep n (by omega)
    refine ⟨?_, ?_, keeps.trans keeps', mx'.trans mx⟩
    · rw [mem', dest, value', mem]
      rfl
    · rw [mem', dest]
      exact frame.writeW (r := ⟨s.gpr .rdi, 1024⟩) (by simp) _
        (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Argon2.X86_64.AddressHeader
