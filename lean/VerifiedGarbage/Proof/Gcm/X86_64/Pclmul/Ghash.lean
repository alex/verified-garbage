import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Blocks
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

/-!
# GHASH with PCLMULQDQ: the whole function

Untrusted: everything here is checked by Lean. `ghash_verified` proves
`Impl.Gcm.X86_64.Pclmul.ghash` against `ghashX86_64`.

The registers `xmm3`–`xmm6` hold `Tₖ` with `x · Tₖ = Hᵏ` (`k = 1 … 4`), so
that `mul(a, Tₖ) = a · Hᵏ`, and `xmm2` holds `Y` after `i` blocks, as a
block; the memory is not written until the epilogue stores `Y`.
-/

namespace VG.Proof.Gcm.X86_64.Pclmul

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly prologue body4 body1 epilogue ghash)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Four blocks and one block, in `Q` -/

theorem step4 (H Y X₁ X₂ X₃ X₄ T₁ T₂ T₃ T₄ : Block) (h₁ : x * φ T₁ = φ H)
    (h₂ : x * φ T₂ = φ H ^ 2) (h₃ : x * φ T₃ = φ H ^ 3) (h₄ : x * φ T₄ = φ H ^ 4) :
    reduce ((((Prod.zero.acc (Y ^^^ X₁) T₄).acc X₂ T₃).acc X₃ T₂).acc X₄ T₁) =
      mul (mul (mul (mul (Y ^^^ X₁) H ^^^ X₂) H ^^^ X₃) H ^^^ X₄) H := by
  apply φ_inj
  simp only [φ_reduce, Prod.val_acc, Prod.val_zero, φ_mul, φ_xor]
  linear_combination (φ Y + φ X₁) * h₄ + φ X₂ * h₃ + φ X₃ * h₂ + φ X₄ * h₁

theorem step1 (H Y X₁ T₁ : Block) (h₁ : x * φ T₁ = φ H) :
    reduce (Prod.zero.acc (Y ^^^ X₁) T₁) = mul (Y ^^^ X₁) H := by
  apply φ_inj
  simp only [φ_reduce, Prod.val_acc, Prod.val_zero, φ_mul, φ_xor]
  linear_combination (φ Y + φ X₁) * h₁

/-! ## Addresses and regions -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, toNat_ofNat_lt ho]
  exact h

theorem add_zero' (p : Addr) : p + BitVec.ofInt 64 ((0 : Nat) : Int) = p := by
  rw [ofInt_natCast]; exact BitVec.add_zero p

theorem addr_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofInt 64 (b : Int) = p + BitVec.ofNat 64 (a + b) := by
  rw [ofInt_natCast, BitVec.add_assoc, BitVec.ofNat_add]

section
variable (s₀ : State)

abbrev hA : Addr := s₀.gpr .rdi
abbrev yp : Addr := s₀.gpr .rsi
abbrev dp : Addr := s₀.gpr .rdx
abbrev nb : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev hR : Region := ⟨hA s₀, 16⟩
abbrev yR : Region := ⟨yp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 256⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev H₀ : Block := blockAt s₀.mem (hA s₀)
abbrev Y₀ : Block := blockAt s₀.mem (yp s₀)

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [hR s₀, dR s₀]
  wr : s₀.wr = [yR s₀, scrR s₀]
  h_y : (hR s₀).Disjoint (yR s₀)
  h_scr : (hR s₀).Disjoint (scrR s₀)
  y_d : (yR s₀).Disjoint (dR s₀)
  y_scr : (yR s₀).Disjoint (scrR s₀)
  d_scr : (dR s₀).Disjoint (scrR s₀)
  ret_y : (retR s₀).Disjoint (yR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : ghashX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from `y`). -/
theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.y_d (yp s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (yp s₀ - dp s₀).isLt
  omega

theorem in_h : InRegions (s₀.rd ++ s₀.wr) (hA s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
  ⟨hR s₀, by simp [h.rd], by rw [ofInt_natCast]; exact contains_offset (by omega) (by omega)⟩

theorem in_y : InRegions (s₀.rd ++ s₀.wr) (yp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
  ⟨yR s₀, by simp [h.wr], by rw [ofInt_natCast]; exact contains_offset (by omega) (by omega)⟩

theorem out_y : InRegions s₀.wr (yp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
  ⟨yR s₀, by simp [h.wr], by rw [ofInt_natCast]; exact contains_offset (by omega) (by omega)⟩

/-- Block `i + j` is in the data. -/
theorem in_blk {i j : Nat} (hij : i + j < nb s₀) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16 := by
  have := h.nb_lt
  refine ⟨dR s₀, by simp [h.rd], ?_⟩
  rw [addr_add, ← Nat.mul_add]
  exact contains_offset (by omega) (by omega)

end Pre

/-! ## The loop invariant -/

/-- What holds after `i` blocks. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i ≤ nb s₀
  x0 : s.xmm .xmm0 = revMask
  x1 : s.xmm .xmm1 = poly
  t1 : x * φ (s.xmm .xmm3) = φ (H₀ s₀)
  t2 : x * φ (s.xmm .xmm4) = φ (H₀ s₀) ^ 2
  t3 : x * φ (s.xmm .xmm5) = φ (H₀ s₀) ^ 3
  t4 : x * φ (s.xmm .xmm6) = φ (H₀ s₀) ^ 4
  y : s.xmm .xmm2 = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → s.gpr r = s₀.gpr r
  rdx : s.gpr .rdx = blkAddr s₀ i
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ - i)
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Only.prod {rs : List XReg} {s s' : State} (h : Only rs s s') (h8 : .xmm8 ∉ rs)
    (h9 : .xmm9 ∉ rs) (h10 : .xmm10 ∉ rs) : prod s' = prod s := by
  simp only [VG.Proof.Gcm.X86_64.Pclmul.prod, h.xmm _ h8, h.xmm _ h9, h.xmm _ h10]

/-- The loads of a block body: block `i + j`, into `xmm7`. -/
theorem load_blk {s₀ : State} (hp : Pre s₀) {i j : Nat} (hij : i + j < nb s₀) {s : State}
    (h0 : s.xmm .xmm0 = revMask) (hrdx : s.gpr .rdx = blkAddr s₀ i) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.load j)) s fun s' =>
      s'.xmm .xmm7 = blockAt s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * (i + j))) ∧ Only [.xmm7] s s' := by
  refine WP.mono (ldrev_ok .xmm7 .rdx (16 * j) s (by decide) h0
    (by rw [hrd, hwr, hrdx]; exact hp.in_blk hij)) fun s' ⟨e, o⟩ => ⟨?_, o⟩
  rw [e, hrdx, hm, addr_add, Nat.mul_add]

/-- A single SSE instruction `pxor xmm7, xmm2`. -/
theorem pxor72_ok (s : State) :
    WP isa (.block [.xop (.bin .pxor .xmm7 .xmm2)]) s fun s' =>
      s'.xmm .xmm7 = s.xmm .xmm2 ^^^ s.xmm .xmm7 ∧ Only [.xmm7] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, ite_true, eval_pxor, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [BitVec.xor_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [hr, ite_false]

/-- `rcx − k`, for `rcx` counting blocks down. -/
theorem ofNat_sub_ofNat {n k : Nat} (hk : k ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `rdx + b`, for `rdx` at an offset `a` into the data. -/
theorem add_ofNat_ofNat (p : Addr) {a b c : Nat} (h : a + b = c) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 c := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h]

/-- The end of a body: `add rdx, 16 k`, `sub rcx, k`, and for the four-block
body `cmp rcx, 4`. -/
theorem tail4_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 64), .alu .sub .rcx (.imm 4), .alu .cmp .rcx (.imm 4)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 64 ∧ s'.gpr .rcx = s.gpr .rcx - 4 ∧
        s'.cf = some (decide ((s.gpr .rcx - 4).toNat < 4)) ∧
        (∀ r, r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e4 : BitVec.signExtend 64 (4 : BitVec 32) = 4 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, ite_true, ite_false, e64, e4,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp [h1, h2], trivial⟩

theorem tail1_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 16), .alu .sub .rcx (.imm 1)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        (∀ r, r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, ite_true, ite_false, e16, e1,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial⟩

/-! ## The bodies -/

theorem body4_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i + 4 ≤ nb s₀) {s : State}
    (hI : Inv s₀ i s) :
    WP isa (.block body4) s fun s' =>
      Inv s₀ (i + 4) s' ∧ s'.cf = some (decide (nb s₀ - (i + 4) < 4)) := by
  have hn := hp.nb_lt
  simp only [body4, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load_blk hp (i := i) (j := 0) (by omega) (by rw [o₁.xmm _ (by decide), hI.x0])
    (by rw [o₁.gpr _ (by decide), hI.rdx]) (o₁.mem.trans hI.mem) (o₁.rd.trans hI.rd)
    (o₁.wr.trans hI.wr)) fun s₂ ⟨l₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (pxor72_ok s₂) fun s₃ ⟨l₃, o₃⟩ => ?_
  have o₁₃ := o₁₂.trans o₃
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm6 s₃ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₄ ⟨p₄, o₄⟩ => ?_
  have o₁₄ := o₁₃.trans o₄
  rw [WP.block_append_iff]
  refine WP.mono (load_blk hp (i := i) (j := 1) (by omega) (by rw [o₁₄.xmm _ (by decide), hI.x0])
    (by rw [o₁₄.gpr _ (by decide), hI.rdx]) (o₁₄.mem.trans hI.mem) (o₁₄.rd.trans hI.rd)
    (o₁₄.wr.trans hI.wr)) fun s₅ ⟨l₅, o₅⟩ => ?_
  have o₁₅ := o₁₄.trans o₅
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm5 s₅ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₆ ⟨p₆, o₆⟩ => ?_
  have o₁₆ := o₁₅.trans o₆
  rw [WP.block_append_iff]
  refine WP.mono (load_blk hp (i := i) (j := 2) (by omega) (by rw [o₁₆.xmm _ (by decide), hI.x0])
    (by rw [o₁₆.gpr _ (by decide), hI.rdx]) (o₁₆.mem.trans hI.mem) (o₁₆.rd.trans hI.rd)
    (o₁₆.wr.trans hI.wr)) fun s₇ ⟨l₇, o₇⟩ => ?_
  have o₁₇ := o₁₆.trans o₇
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm4 s₇ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₈ ⟨p₈, o₈⟩ => ?_
  have o₁₈ := o₁₇.trans o₈
  rw [WP.block_append_iff]
  refine WP.mono (load_blk hp (i := i) (j := 3) (by omega) (by rw [o₁₈.xmm _ (by decide), hI.x0])
    (by rw [o₁₈.gpr _ (by decide), hI.rdx]) (o₁₈.mem.trans hI.mem) (o₁₈.rd.trans hI.rd)
    (o₁₈.wr.trans hI.wr)) fun s₉ ⟨l₉, o₉⟩ => ?_
  have o₁₉ := o₁₈.trans o₉
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm3 s₉ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₁₀ ⟨p₁₀, o₁₀⟩ => ?_
  have o₁₁₀ := o₁₉.trans o₁₀
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok .xmm2 s₁₀ (by decide) (by decide) (by decide) (by decide)
    (by rw [o₁₁₀.xmm _ (by decide), hI.x1])) fun s₁₁ ⟨p₁₁, o₁₁⟩ => ?_
  have o₁₁₁ := o₁₁₀.trans o₁₁
  refine WP.mono (tail4_ok s₁₁) fun s' ⟨frdx, frcx, fcf, fg, fx, fm, frd, fwr⟩ => ?_
  have hrdx : s₁₁.gpr .rdx = blkAddr s₀ i := by rw [o₁₁₁.gpr _ (by decide), hI.rdx]
  have hrcx : s₁₁.gpr .rcx - 4 = BitVec.ofNat 64 (nb s₀ - (i + 4)) := by
    rw [o₁₁₁.gpr _ (by decide), hI.rcx]
    exact ofNat_sub_ofNat (k := 4) (by omega) (by have := (s₀.gpr .rcx).isLt; omega)
  have kx : ∀ r, r ≠ .xmm2 → r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 →
      s'.xmm r = s.xmm r := fun r h2 h7 h8 h9 h10 h11 => by
    rw [fx, o₁₁₁.xmm r (by simp [h2, h7, h8, h9, h10, h11])]
  refine ⟨⟨by omega, by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.x0], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.x1], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t1], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t2], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t3], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t4], ?_, fun r ha hd hc => by rw [fg r hd hc, o₁₁₁.gpr r ha, hI.gpr r ha hd hc],
      by rw [frdx, hrdx]; exact add_ofNat_ofNat (b := 64) _ (by omega), by rw [frcx, hrcx],
      by rw [fm, o₁₁₁.mem, hI.mem], by rw [frd, o₁₁₁.rd, hI.rd], by rw [fwr, o₁₁₁.wr, hI.wr]⟩, ?_⟩
  · -- The new `Y`.
    rw [fx, p₁₁, p₁₀, o₉.prod (by decide) (by decide) (by decide), p₈,
      o₇.prod (by decide) (by decide) (by decide), p₆, o₅.prod (by decide) (by decide) (by decide), p₄,
      o₃.prod (by decide) (by decide) (by decide), o₂.prod (by decide) (by decide) (by decide), p₁,
      l₉, l₇, l₅, l₃, l₂, o₁₉.xmm .xmm3 (by decide), o₁₇.xmm .xmm4 (by decide),
      o₁₅.xmm .xmm5 (by decide), o₁₃.xmm .xmm6 (by decide), o₁₂.xmm .xmm2 (by decide), hI.y,
      show i + 4 = i + 3 + 1 from rfl, ghashFrom_blocksAt_succ, show i + 3 = i + 2 + 1 from rfl,
      ghashFrom_blocksAt_succ, show i + 2 = i + 1 + 1 from rfl, ghashFrom_blocksAt_succ,
      ghashFrom_blocksAt_succ, Nat.add_zero]
    exact step4 _ _ _ _ _ _ _ _ _ _ hI.t1 hI.t2 hI.t3 hI.t4
  · rw [fcf, hrcx, toNat_ofNat_lt (by omega)]

theorem beq_ofNat_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem body1_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hI : Inv s₀ i s) :
    WP isa (.block body1) s fun s' =>
      Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (nb s₀ - (i + 1) = 0)) := by
  have hn := hp.nb_lt
  simp only [body1, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load_blk hp (i := i) (j := 0) (by omega) (by rw [o₁.xmm _ (by decide), hI.x0])
    (by rw [o₁.gpr _ (by decide), hI.rdx]) (o₁.mem.trans hI.mem) (o₁.rd.trans hI.rd)
    (o₁.wr.trans hI.wr)) fun s₂ ⟨l₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (pxor72_ok s₂) fun s₃ ⟨l₃, o₃⟩ => ?_
  have o₁₃ := o₁₂.trans o₃
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm3 s₃ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₄ ⟨p₄, o₄⟩ => ?_
  have o₁₄ := o₁₃.trans o₄
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok .xmm2 s₄ (by decide) (by decide) (by decide) (by decide)
    (by rw [o₁₄.xmm _ (by decide), hI.x1])) fun s₅ ⟨p₅, o₅⟩ => ?_
  have o₁₅ := o₁₄.trans o₅
  refine WP.mono (tail1_ok s₅) fun s' ⟨frdx, frcx, fzf, fg, fx, fm, frd, fwr⟩ => ?_
  have hrdx : s₅.gpr .rdx = blkAddr s₀ i := by rw [o₁₅.gpr _ (by decide), hI.rdx]
  have hrcx : s₅.gpr .rcx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [o₁₅.gpr _ (by decide), hI.rcx]
    exact ofNat_sub_ofNat (k := 1) (by omega) (by have := (s₀.gpr .rcx).isLt; omega)
  have kx : ∀ r, r ≠ .xmm2 → r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 →
      s'.xmm r = s.xmm r := fun r h2 h7 h8 h9 h10 h11 => by
    rw [fx, o₁₅.xmm r (by simp [h2, h7, h8, h9, h10, h11])]
  refine ⟨⟨by omega, by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.x0], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.x1], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t1], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t2], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t3], by rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.t4], ?_, fun r ha hd hc => by rw [fg r hd hc, o₁₅.gpr r ha, hI.gpr r ha hd hc],
      by rw [frdx, hrdx]; exact add_ofNat_ofNat (b := 16) _ (by omega), by rw [frcx, hrcx],
      by rw [fm, o₁₅.mem, hI.mem], by rw [frd, o₁₅.rd, hI.rd], by rw [fwr, o₁₅.wr, hI.wr]⟩, ?_⟩
  · rw [fx, p₅, p₄, o₃.prod (by decide) (by decide) (by decide), o₂.prod (by decide) (by decide)
      (by decide), p₁, l₃, l₂, o₁₃.xmm .xmm3 (by decide), o₁₂.xmm .xmm2 (by decide), hI.y,
      ghashFrom_blocksAt_succ, Nat.add_zero]
    exact step1 _ _ _ _ hI.t1
  · rw [fzf, hrcx, beq_ofNat_zero (by omega)]

/-! ## The prologue and the epilogue -/

/-- `Y` loaded into `xmm2`, and `cmp rcx, 4`. -/
theorem loadY_ok (s : State) (h0 : s.xmm .xmm0 = revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 16) :
    WP isa (.block [.movdquLoad .xmm2 (at_ .rsi 0), .xop (.bin .pshufb .xmm2 .xmm0),
        .alu .cmp .rcx (.imm 4)]) s fun s' =>
      s'.xmm .xmm2 = blockAt s.mem (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) ∧
      s'.cf = some (decide ((s.gpr .rcx).toNat < 4)) ∧ Only [.xmm2] s s' := by
  have e4 : BitVec.signExtend 64 (4 : BitVec 32) = 4 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setXmm, State.load128, ea_at, hin,
    ite_true, ite_false, h0, e4, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [blockAt_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [hr, ite_false]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s' => Inv s₀ 0 s' ∧ s'.cf = some (decide (nb s₀ < 4)) := by
  simp only [prologue, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdi 0 s₂ (by decide)
    (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact hp.in_h)) fun s₃ ⟨l₃, o₃⟩ => ?_
  have o₁₃ := o₁₂.trans o₃
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₃) fun s₄ ⟨t₄, o₄⟩ => ?_
  have o₁₄ := o₁₃.trans o₄
  have x1 : ∀ {s'} {rs : List XReg}, Only rs s₄ s' → .xmm1 ∉ rs → s'.xmm .xmm1 = poly :=
    fun o h => by rw [o.xmm _ h, o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂]
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok .xmm4 .xmm3 .xmm3 s₄ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (x1 (rs := []) ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ (by decide)))
    fun s₅ ⟨m₅, o₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok .xmm5 .xmm4 .xmm3 s₅ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (x1 o₅ (by decide))) fun s₆ ⟨m₆, o₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok .xmm6 .xmm5 .xmm3 s₆ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (x1 (o₅.trans o₆) (by decide))) fun s₇ ⟨m₇, o₇⟩ => ?_
  have o₂₇ := o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇))))
  have o₁₇ := o₁.trans o₂₇
  refine WP.mono (loadY_ok s₇ (by rw [o₂₇.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₇.rd, o₁₇.wr, o₁₇.gpr _ (by decide)]; exact hp.in_y)) fun s' ⟨ly, fcf, oy⟩ => ?_
  have O := o₁₇.trans oy
  have hH : x * φ (s₄.xmm .xmm3) = φ (H₀ s₀) := by rw [t₄, l₃, add_zero', o₁₂.mem, o₁₂.gpr _ (by decide)]
  have hH2 : x * φ (s₅.xmm .xmm4) = φ (H₀ s₀) ^ 2 := by
    rw [m₅, show ∀ a : Q, x * (x * a * a) = (x * a) * (x * a) from fun a => by ring, hH]; ring
  have hH3 : x * φ (s₆.xmm .xmm5) = φ (H₀ s₀) ^ 3 := by
    rw [m₆, o₅.xmm .xmm3 (by decide),
      show ∀ a b : Q, x * (x * a * b) = (x * a) * (x * b) from fun a b => by ring, hH2, hH]; ring
  have hH4 : x * φ (s₇.xmm .xmm6) = φ (H₀ s₀) ^ 4 := by
    rw [m₇, (o₅.trans o₆).xmm .xmm3 (by decide),
      show ∀ a b : Q, x * (x * a * b) = (x * a) * (x * b) from fun a b => by ring, hH3, hH]; ring
  refine ⟨⟨Nat.zero_le _, by rw [(o₂₇.trans oy).xmm _ (by decide), c₁, rev_eq],
    x1 (o₅.trans (o₆.trans (o₇.trans oy))) (by decide),
    by rw [(o₅.trans (o₆.trans (o₇.trans oy))).xmm _ (by decide), hH],
    by rw [(o₆.trans (o₇.trans oy)).xmm _ (by decide), hH2],
    by rw [(o₇.trans oy).xmm _ (by decide), hH3], by rw [oy.xmm _ (by decide), hH4],
    by rw [ly, o₁₇.mem, o₁₇.gpr _ (by decide), add_zero', ghashFrom_blocksAt_zero],
    fun r ha _ _ => O.gpr r ha, by rw [O.gpr _ (by decide)]; simp [blkAddr],
    by rw [O.gpr _ (by decide)]; simp [nb], O.mem, O.rd, O.wr⟩, by rw [fcf, o₁₇.gpr _ (by decide)]⟩

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' => gprPreserved s₀ s' ∧ ghashX86_64.post s₀ s' := by
  have hout : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [hI.wr, hI.gpr .rsi (by decide) (by decide) (by decide)]; exact hp.out_y
  have h0 := hI.x0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [epilogue, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, State.setXmm, State.store128, ea_at, hout, ite_true, h0,
    Option.some.injEq, exists_eq_left']
  rw [add_zero', hI.gpr .rsi (by decide) (by decide) (by decide)]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hI.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [Mem.readW_writeW_sep (hp.ret_y.sep (Region.contains_self _ _)
      (Region.contains_self _ _)) (by decide), hI.mem]
  · show blockAt _ (yp s₀) = _
    rw [blockAt_store, hI.y]

theorem test_ok {s₀ : State} (hp : Pre s₀) {i : Nat} {s : State} (hI : Inv s₀ i s) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun s' =>
      Inv s₀ i s' ∧ s'.zf = some (decide (nb s₀ - i = 0)) := by
  have hn := hp.nb_lt
  have hrcx := hI.rcx
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, hrcx, BitVec.and_self, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨{ hI with }, by rw [beq_ofNat_zero (by omega)]⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' => gprPreserved s₀ s' ∧ ghashX86_64.post s₀ s' := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI₁, hcf⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ i, nb s₀ - i < 4 ∧ Inv s₀ i s) ?_ fun s₂ ⟨i, hi, hI₂⟩ => ?_)
  · refine WP.ite (decide (nb s₀ < 4)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0, by simpa using h, hI₁⟩
    · let Inv4 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i + 4 ≤ nb s₀ ∧ Inv s₀ i s
      have hstep : ∀ m s, Inv4 m s → WP isa (.block body4) s (fun s' =>
          (eval .ae s' = some false ∧ ∃ i, nb s₀ - i < 4 ∧ Inv s₀ i s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, Inv4 m' s')) := by
        rintro m s ⟨i, rfl, hi, hI⟩
        refine WP.mono (body4_ok hp hi hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : nb s₀ - (i + 4) < 4
        · exact .inl ⟨by simp [eval, hcf', hlt], i + 4, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], nb s₀ - (i + 4), by omega, i + 4, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) Inv4 hstep (nb s₀) s₁ ⟨0, rfl, by simpa using h, hI₁⟩
  refine WP.seq (WP.mono (test_ok hp hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (nb s₀)) ?_ fun s₄ hI₄ => epilogue_ok hp hI₄)
  refine WP.ite (decide (nb s₀ - i = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : i = nb s₀ := by have := hI₃.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₃)
  · let Inv1 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ Inv s₀ i s
    have hstep : ∀ m s, Inv1 m s → WP isa (.block body1) s (fun s' =>
        (eval .ne s' = some false ∧ Inv s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv1 m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body1_ok hp hi hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : nb s₀ - (i + 1) = 0
      · have : i + 1 = nb s₀ := by omega
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], nb s₀ - (i + 1), by omega, i + 1, rfl, by omega, hI'⟩
    have hlt : i < nb s₀ := by have := hI₃.le; simp at h; omega
    exact WP.loop (M := isa) Inv1 hstep (nb s₀ - i) s₃ ⟨i, rfl, hlt, hI₃⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

theorem ghash_verified :
    Verified X86_64.target Impl.Gcm.X86_64.Pclmul.ghash ghashX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, satState] at h₁ h₂
      bv_omega

end VG.Proof.Gcm.X86_64.Pclmul
