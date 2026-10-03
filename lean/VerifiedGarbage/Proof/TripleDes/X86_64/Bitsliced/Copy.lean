import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Pass

/-!
# Copying words

`copy_ok`: the loop of `copyBody src dst` copies `n ≥ 1` words from `A` (in
`src`) to `B` (in `dst`), where the two areas do not overlap, and changes
nothing else in memory. `src` and `dst` are `rsi` and `rdi`, in either
order; `rdx` counts the words left.
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice

/-- Word `i` from `p`. -/
abbrev wAt (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (8 * i)

structure CopyPre (A B : Addr) (n : Nat) (s : State) : Prop where
  read : ∀ i < n, InRegions (s.rd ++ s.wr) (wAt A i) 8
  write : ∀ i < n, InRegions s.wr (wAt B i) 8
  sep : (⟨A, 8 * n⟩ : Region).Disjoint ⟨B, 8 * n⟩
  fitA : 8 * n < 2 ^ 64

theorem wAt_succ (p : Addr) (i : Nat) : wAt p i + 8 = wAt p (i + 1) := by
  simp only [wAt, BitVec.add_assoc]
  congr 1
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
  congr 1

structure CopyInv (src dst : Reg) (A B : Addr) (n : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i < n
  src : s.gpr src = wAt A i
  dst : s.gpr dst = wAt B i
  cnt : s.gpr .rdx = BitVec.ofNat 64 (n - i)
  copied : ∀ j < i, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → r ≠ .rdx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

structure CopyPost (src dst : Reg) (A B : Addr) (n : Nat) (s₀ s : State) : Prop where
  src : s.gpr src = wAt A n
  dst : s.gpr dst = wAt B n
  copied : ∀ j < n, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → r ≠ .rdx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem wAt_in {p : Addr} {i n : Nat} (hi : i < n) (hn : 8 * n < 2 ^ 64) :
    (⟨p, 8 * n⟩ : Region).Contains (wAt p i) 8 :=
  Offset.contains_base p (by omega) (by omega)

theorem copy_ok {src dst : Reg} (hsd : (src = .rsi ∧ dst = .rdi) ∨ (src = .rdi ∧ dst = .rsi))
    {A B : Addr} {n : Nat} {s₀ : State} (hpre : CopyPre A B n s₀) (s : State) (i : Nat)
    (hs : CopyInv src dst A B n s₀ i s) :
    WP isa (.loop (.block (copyBody src dst)) .ne) s (CopyPost src dst A B n s₀) := by
  refine WP.loop (M := isa) (fun m s => CopyInv src dst A B n s₀ (n - m) s ∧ m ≤ n) ?_ (n - i) s
    ⟨by rw [show n - (n - i) = i by have := hs.le; omega]; exact hs, by omega⟩
  intro m s ⟨inv, hm⟩
  let j := n - m
  have hj : j < n := inv.le
  have hsrc : src ≠ .rax ∧ src ≠ .rdx := by rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hdst : dst ≠ .rax ∧ dst ≠ .rdx := by rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hsd' : src ≠ dst := by rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  -- mov rax, [src]
  let v := s₀.mem.readW (wAt A j) 64
  have hv : s.mem.readW (wAt A j) 64 = v :=
    inv.frame.readW (wAt_in hj hpre.fitA) (by simpa using hpre.sep) (by decide)
  let s₁ := s.setReg .rax v
  have e₁ : exec (.mov .rax (.mem { base := src, disp := 0 })) s = some s₁ := by
    have hea : s.ea { base := src, disp := 0 } = wAt A j := by
      show s.gpr src + BitVec.ofInt 64 0 = _
      rw [inv.src]; simp; rfl
    have hr : InRegions (s.rd ++ s.wr) (wAt A j) 8 := by rw [inv.rd, inv.wr]; exact hpre.read j hj
    simp only [exec, readSrc, State.load64, hea, hr, ite_true, hv, Option.map_some]
    rfl
  -- store [dst], rax
  have hea₂ : s₁.ea { base := dst, disp := 0 } = wAt B j := by
    show s₁.gpr dst + BitVec.ofInt 64 0 = _
    simp only [s₁, gpr_setReg_of_ne (s := s) v hdst.1, inv.dst]; simp; rfl
  have hw : InRegions s₁.wr (wAt B j) 8 := by
    simp only [s₁, wr_setReg, inv.wr]; exact hpre.write j hj
  let s₂ : State := { s₁ with mem := s₁.mem.writeW (wAt B j) v }
  have e₂ : exec (.store { base := dst, disp := 0 } .rax) s₁ = some s₂ := by
    simp only [exec, State.store64, hea₂, hw, ite_true, s₁, gpr_setReg_self]
    rfl
  -- add rsi, 8; add rdi, 8; sub rdx, 1
  have e₃ := exec_addImm s₂ .rsi 8
  let s₃ := (arithFlags s₂ (s₂.gpr .rsi + (8 : BitVec 32).signExtend 64)
      (decide (2 ^ 64 ≤ (s₂.gpr .rsi).toNat + ((8 : BitVec 32).signExtend 64).toNat))
      (addOverflow (s₂.gpr .rsi) ((8 : BitVec 32).signExtend 64)
        (s₂.gpr .rsi + (8 : BitVec 32).signExtend 64))).setReg .rsi
      (s₂.gpr .rsi + (8 : BitVec 32).signExtend 64)
  have e₄ := exec_addImm s₃ .rdi 8
  let s₄ := (arithFlags s₃ (s₃.gpr .rdi + (8 : BitVec 32).signExtend 64)
      (decide (2 ^ 64 ≤ (s₃.gpr .rdi).toNat + ((8 : BitVec 32).signExtend 64).toNat))
      (addOverflow (s₃.gpr .rdi) ((8 : BitVec 32).signExtend 64)
        (s₃.gpr .rdi + (8 : BitVec 32).signExtend 64))).setReg .rdi
      (s₃.gpr .rdi + (8 : BitVec 32).signExtend 64)
  let c := s₄.gpr .rdx
  let r := c - (1 : BitVec 32).signExtend 64
  let s₅ := (arithFlags s₄ r (decide (c.toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow c ((1 : BitVec 32).signExtend 64) r)).setReg .rdx r
  have e₅ : exec (.alu .sub .rdx (.imm 1)) s₄ = some s₅ := rfl
  have run : runBlock isa (copyBody src dst) s = some s₅ := by
    rw [copyBody, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons,
      e₃, runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₅, run, ?_⟩
  -- the facts about s₅
  have g₅ : ∀ x, x ≠ .rsi → x ≠ .rdi → x ≠ .rdx → x ≠ .rax → s₅.gpr x = s.gpr x := by
    intro x h1 h2 h3 h4
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg, h1, h2, h3, h4]
  have rsi₅ : s₅.gpr .rsi = s.gpr .rsi + 8 := by
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  have rdi₅ : s₅.gpr .rdi = s.gpr .rdi + 8 := by
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  have rdx₅ : s₅.gpr .rdx = s.gpr .rdx - 1 := by
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg, r, c]
  have mem₅ : s₅.mem = s.mem.writeW (wAt B j) v := by
    simp [s₅, s₄, s₃, s₂, s₁, mem_setReg, mem_arithFlags]
  have rd₅ : s₅.rd = s.rd := by simp [s₅, s₄, s₃, s₂, s₁, rd_setReg, rd_arithFlags]
  have wr₅ : s₅.wr = s.wr := by simp [s₅, s₄, s₃, s₂, s₁, wr_setReg, wr_arithFlags]
  have zf₅ : s₅.zf = some (s.gpr .rdx - 1 == 0) := by
    simp only [s₅, zf_setReg, zf_arithFlags, r, c]
    simp [s₄, s₃, s₂, s₁, gpr_setReg]
  have src₅ : s₅.gpr src = wAt A (j + 1) := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [rsi₅, inv.src, wAt_succ]
    · rw [rdi₅, inv.src, wAt_succ]
  have dst₅ : s₅.gpr dst = wAt B (j + 1) := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [rdi₅, inv.dst, wAt_succ]
    · rw [rsi₅, inv.dst, wAt_succ]
  have copied₅ : ∀ x < j + 1, s₅.mem.readW (wAt B x) 64 = s₀.mem.readW (wAt A x) 64 := by
    intro x hx
    rw [mem₅]
    have fit := hpre.fitA
    by_cases he : x = j
    · subst he; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide)]
      exact inv.copied x (by omega)
  have frame₅ : Frame [⟨B, 8 * n⟩] s₀.mem s₅.mem := by
    rw [mem₅]; exact inv.frame.writeW List.mem_cons_self _ (wAt_in hj hpre.fitA)
  have regs₅ : ∀ x, x ≠ .rax → x ≠ .rsi → x ≠ .rdi → x ≠ .rdx → s₅.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 => (g₅ x h2 h3 h4 h1).trans (inv.regs x h1 h2 h3 h4)
  have cntv : s.gpr .rdx - 1 = BitVec.ofNat 64 (m - 1) := by
    rw [inv.cnt, show n - j = m by omega]
    exact cnt_sub m (by omega)
  by_cases h1 : m = 1
  · left
    refine ⟨?_, ?_⟩
    · show s₅.zf.map (!·) = some false
      rw [zf₅, cntv, h1]; rfl
    · refine ⟨?_, ?_, ?_, frame₅, regs₅, rd₅.trans inv.rd, wr₅.trans inv.wr⟩
      · rw [src₅]; congr 1; omega
      · rw [dst₅]; congr 1; omega
      · intro x hx; exact copied₅ x (by omega)
  · right
    refine ⟨?_, m - 1, by omega, ⟨?_, ?_, ?_, ?_, ?_, frame₅, regs₅, rd₅.trans inv.rd,
      wr₅.trans inv.wr⟩, by omega⟩
    · show s₅.zf.map (!·) = some true
      rw [zf₅, cntv]
      have : (BitVec.ofNat 64 (m - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by have := hpre.fitA; omega)] at this
        omega
      rw [this]; rfl
    · omega
    · rw [src₅]; congr 1; omega
    · rw [dst₅]; congr 1; omega
    · rw [rdx₅, cntv]; congr 1; omega
    · intro x hx; exact copied₅ x (by omega)

end VG.Proof.TripleDes.X86_64.Bitsliced
