import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitch
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Poly
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.LoopRounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar

/-!
# ChaCha20 and Poly1305 together (AArch64): a counted phase

`Stitch.phase`: five double rounds of the eight-block ChaCha20 kernel, as in
`Mixed8.counted_phase_ok`, and sixteen blocks of Poly1305 (`Poly.block_absorb`)
from `W`. The rounds write only the vector registers, the registers of the
integer block (`Words`) and `x1`; the blocks only `Poly.regs`; neither
writes memory, so each preserves what the other computes.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch
open VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0)
open VG.Proof.ChaCha20.AArch64.Mixed8 (N C RI)
open VG.Proof.Poly1305.AArch64.Radix64 (Keeps Keeps.gpr' Keeps.trans)
open VG.Spec.ChaCha20 (innerBlock)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

abbrev Acc := VG.Proof.ChaCha20Poly1305.AArch64.Poly.Acc

theorem words_not_poly {r : Reg} (h : Words r) : r ∉ Poly.regs := by
  obtain ⟨k, hk, rfl⟩ := h
  exact (show ∀ k < 16, VG.Impl.ChaCha20.AArch64.wreg k ∉ Poly.regs by decide) k hk

theorem x0_not_poly : Reg.x0 ∉ Poly.regs := by decide
theorem x1_not_poly : Reg.x1 ∉ Poly.regs := by decide

/-- The blocks from `W` are readable, and so is the key. -/
structure Readable (W : Addr) (s : State) : Prop where
  blk : ∀ d, d + 8 ≤ 256 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8
  k0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r0Off) 8
  k1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r1Off) 8

theorem Readable.of {W : Addr} {s u : State} (h : Readable W s) (hrd : u.rd = s.rd)
    (hwr : u.wr = s.wr) (hx0 : u.gpr .x0 = s.gpr .x0) : Readable W u :=
  ⟨fun d hd => by rw [hrd, hwr]; exact h.blk d hd, by rw [hrd, hwr, hx0]; exact h.k0,
    by rw [hrd, hwr, hx0]; exact h.k1⟩

/-- The accumulator is unchanged by code that writes neither its registers,
`x0`, nor memory. -/
theorem Acc.of {R a : Nat} {s u : State} (h : Acc R a s)
    (hg : ∀ r ∈ [Reg.x0, .x21, .x22, .x23], u.gpr r = s.gpr r) (hm : u.mem = s.mem) :
    Acc R a u := by
  have e : ∀ d, Poly.rword u d = Poly.rword s d := fun d => by
    simp only [Poly.rword, hg .x0 (by decide), hm]
  have hv : Poly.hval u = Poly.hval s := by
    simp only [Poly.hval, hg .x21 (by decide), hg .x22 (by decide), hg .x23 (by decide)]
  exact ⟨by rw [hv]; exact h.h, by rw [hg .x23 (by decide)]; exact h.h2,
    by simp only [Poly.rval, e]; exact h.key, by rw [e]; exact h.k0, by rw [e]; exact h.k1⟩

theorem bytesAt_succ (m : Mem) (W : Addr) (n : Nat) :
    bytesAt m W (16 * (n + 1)) = bytesAt m W (16 * n) ++
      bytesAt m (W + BitVec.ofNat 64 (16 * n)) 16 := by
  rw [Nat.mul_succ, Poly1305.bytesAt_add]

/-- The `n + 1`st block from `W`. -/
theorem absorb_next {R a : Nat} {W : Addr} {n : Nat} (hn : 16 * n + 16 ≤ 256) {s : State}
    (ha : Acc R (absorbAll R a (bytesAt s.mem W (16 * n))) s)
    (hp : s.gpr .x20 = W + BitVec.ofNat 64 (16 * n)) (hr : Readable W s) :
    WP isa (.block Poly.block) s fun u =>
      Acc R (absorbAll R a (bytesAt s.mem W (16 * (n + 1)))) u ∧
      u.gpr .x20 = W + BitVec.ofNat 64 (16 * (n + 1)) ∧ Keeps Poly.regs s u := by
  have hb (d : Nat) (hd : d + 8 ≤ 16) :
      InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 d) 8 := by
    rw [hp, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hr.blk _ (by omega)
  refine (Poly.block_absorb s ha (hb 0 (by decide)) (hb 8 (by decide)) hr.k0 hr.k1).mono
    fun u ⟨hu, hx, hk⟩ => ⟨?_, ?_, hk⟩
  · have hl : (bytesAt s.mem W (16 * n)).length % 16 = 0 := by
      rw [Poly1305.length_bytesAt]; omega
    rw [bytesAt_succ, Poly1305.absorbAll_append hl, ← hp]
    exact hu
  · rw [hx, hp, BitVec.add_assoc]
    change W + (BitVec.ofNat 64 (16 * n) + BitVec.ofNat 64 16) = _
    rw [← BitVec.ofNat_add, Nat.mul_succ]

/-- Code that keeps `Poly.regs`, memory and the regions. -/
theorem keeps_frame {s u : State} (h : Keeps Poly.regs s u) {r : Reg} (hr : r ∉ Poly.regs) :
    u.gpr r = s.gpr r := h.1 r hr

/-- After `i` iterations of the loop. -/
structure PI (blocks : Nat → VG.Spec.ChaCha20.State) (v : VG.Spec.ChaCha20.State)
    (R a : Nat) (W : Addr) (s₀ s : State) (i : Nat) : Prop where
  vec : N (VG.Proof.ChaCha20.AArch64.Rows6.pack
    (fun b => Nat.repeat innerBlock i (blocks b))) s
  scalar : C (Nat.repeat (fun x => innerBlock (innerBlock x)) i v) s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .x1 → r ∉ Poly.regs → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  ptr : s.gpr .x20 = W + BitVec.ofNat 64 (16 * (1 + 3 * i))
  acc : Acc R (absorbAll R a (bytesAt s₀.mem W (16 * (1 + 3 * i)))) s

theorem PI.readable {blocks v R a W s₀ s i} (h : PI blocks v R a W s₀ s i) (hr : Readable W s₀) :
    Readable W s := hr.of h.rd h.wr (h.keep _ not_words_x0 (by decide) x0_not_poly)

/-- Three blocks, after the double round. -/
theorem absorb3_ok {R a : Nat} {W : Addr} {n : Nat} (hn : 16 * n + 48 ≤ 256) {s : State}
    (ha : Acc R (absorbAll R a (bytesAt s.mem W (16 * n))) s)
    (hp : s.gpr .x20 = W + BitVec.ofNat 64 (16 * n)) (hr : Readable W s) :
    WP isa (.block absorb3) s fun u =>
      Acc R (absorbAll R a (bytesAt s.mem W (16 * (n + 3)))) u ∧
      u.gpr .x20 = W + BitVec.ofNat 64 (16 * (n + 3)) ∧ Keeps Poly.regs s u ∧
      u.v = s.v ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have hv : ∀ i ∈ absorb3, vdstOf i = none := by decide +kernel
  suffices main : WP isa (.block absorb3) s fun u =>
      Acc R (absorbAll R a (bytesAt s.mem W (16 * (n + 3)))) u ∧
      u.gpr .x20 = W + BitVec.ofNat 64 (16 * (n + 3)) ∧ Keeps Poly.regs s u from
    (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv main).mono
      fun u ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩
  unfold absorb3
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (absorb_next (by omega) ha hp hr) fun s₁ ⟨a₁, p₁, k₁⟩ => ?_)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hr₁ : Readable W s₁ := hr.of k₁.2.2.1 k₁.2.2.2 (k₁.gpr' (r := .x0))
  rw [← hm₁] at a₁
  refine WP.block_append (WP.mono (absorb_next (by omega) a₁ p₁ hr₁) fun s₂ ⟨a₂, p₂, k₂⟩ => ?_)
  have hm₂ : s₂.mem = s.mem := k₂.2.1.trans hm₁
  have hr₂ : Readable W s₂ := hr₁.of k₂.2.2.1 k₂.2.2.2 (k₂.gpr' (r := .x0))
  rw [hm₁, ← hm₂] at a₂
  refine WP.mono (absorb_next (by omega) a₂ p₂ hr₂) fun u ⟨a₃, p₃, k₃⟩ => ?_
  rw [hm₂] at a₃
  exact ⟨a₃, p₃, ((k₁.trans k₂).trans k₃).mono (by
    intro r h; simp only [List.mem_append] at h; rcases h with (h | h) | h <;> exact h)⟩

/-- The loop body, from `PI … i` to `PI … (i + 1)`. -/
theorem iter_ok {blocks v R a W s₀ s} {i : Nat} (hi : i < 5) (hr : Readable W s₀)
    (h : PI blocks v R a W s₀ s i) :
    WP isa (.seq VG.Impl.ChaCha20.AArch64.Mixed8.parallelRound (.block (absorb3 ++ ([.subImm .x .x1 .x1 1] : List Instr)))) s
      fun u => PI blocks v R a W s₀ u (i + 1) ∧ u.gpr .x1 = s.gpr .x1 - 1#64 := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.parallelRound_ok h.vec h.scalar h.table).mono
    fun b ⟨hb, hc, hsp, ht⟩ => ?_
  have nw (r : Reg) (hr' : r ∈ Poly.regs) : ¬ Words r := fun hw => words_not_poly hw hr'
  have hbacc : Acc R (absorbAll R a (bytesAt b.mem W (16 * (1 + 3 * i)))) b := by
    rw [hc.mem, h.mem]
    exact h.acc.of (fun r hr' => hc.keep r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl
      · exact not_words_x0
      all_goals exact nw _ (by decide))) hc.mem
  have hbp : b.gpr .x20 = W + BitVec.ofNat 64 (16 * (1 + 3 * i)) :=
    (hc.keep _ (nw _ (by decide))).trans h.ptr
  have hbr : Readable W b := (h.readable hr).of hc.rd hc.wr (hc.keep _ not_words_x0)
  apply WP.block_append
  refine (absorb3_ok (n := 1 + 3 * i) (by omega) hbacc hbp hbr).mono
    fun c ⟨hca, hcp, hck, hcv, hcsp, hcr, hcw⟩ => ?_
  apply WP.block_cons_iff.mpr
  refine ⟨c.write .x .x1 (c.gpr .x1 - BitVec.ofNat 64 1), ?_, WP.block_nil ?_⟩
  · simpa only [State.read, BitVec.setWidth_eq] using
      exec_subImm_x (s := c) (d := .x1) (n := .x1) (imm := 1) (by decide)
  · have hcm : c.mem = s₀.mem := hck.2.1.trans (hc.mem.trans h.mem)
    have hx1 : c.gpr .x1 = b.gpr .x1 := hck.gpr' (r := .x1)
    refine ⟨⟨?_, ?_, hcm, hcr.trans (hc.rd.trans h.rd), hcw.trans (hc.wr.trans h.wr), ?_,
      hcsp.trans (hsp.trans h.sp), ?_, ?_, ?_⟩, ?_⟩
    · intro k j hj
      rw [RegUpd.v_write, hcv]
      exact hb k j hj
    · intro k hk
      rw [RegUpd.gpr_write_of_ne c .x _ (by intro he; exact not_words_x1 ⟨k, hk, he.symm⟩),
        hck.gpr' (r := VG.Impl.ChaCha20.AArch64.wreg k) (words_not_poly ⟨k, hk, rfl⟩)]
      exact hc.holds k hk
    · intro r hw h1 hp
      rw [RegUpd.gpr_write_of_ne c .x _ h1, hck.gpr' (r := r) hp, hc.keep r hw]
      exact h.keep r hw h1 hp
    · rw [RegUpd.v_write, hcv, ht]
    · rw [RegUpd.gpr_write_of_ne c .x _ (by decide), hcp,
        show 1 + 3 * i + 3 = 1 + 3 * (i + 1) by omega]
    · have e : 16 * (1 + 3 * i + 3) = 16 * (1 + 3 * (i + 1)) := by omega
      rw [hc.mem, h.mem, e] at hca
      exact hca.of (fun r hr' => RegUpd.gpr_write_of_ne c .x _ (by
        intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl
    · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hx1, hc.keep _ not_words_x1]

theorem write_v (s : State) (sz : Size) (d : Reg) (x : BitVec sz.bits) : (s.write sz d x).v = s.v := rfl

/-- After the phase. -/
structure Done (blocks : Nat → VG.Spec.ChaCha20.State) (v : VG.Spec.ChaCha20.State)
    (R a : Nat) (W : Addr) (restore : Reg) (s u : State) : Prop where
  vec : N (VG.Proof.ChaCha20.AArch64.Rows6.pack
    (fun b => Nat.repeat innerBlock 5 (blocks b))) u
  scalar : C (Nat.repeat innerBlock 10 v) u
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp
  table : u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  keep : ∀ r, ¬ Words r → r ≠ .x1 → r ∉ Poly.regs → u.gpr r = s.gpr r
  x20 : u.gpr .x20 = s.gpr .x0 + 64#64
  x1 : u.gpr .x1 = u.gpr restore
  acc : Acc R (absorbAll R a (bytesAt s.mem W 256)) u

theorem phase_ok {blocks : Nat → VG.Spec.ChaCha20.State} {v : VG.Spec.ChaCha20.State}
    {R a : Nat} {W : Addr} {start : Instr} {restore : Reg} {s : State}
    (hn : N (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s) (hc : C v s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table)
    (hstart : exec start s = some (s.write .x .x20 W))
    (ha : Acc R a s) (hr : Readable W s) :
    WP isa (phase start restore) s (Done blocks v R a W restore s) := by
  unfold phase
  apply WP.seq
  -- `x20` set, the first block, and the counter.
  let s₁ := s.write .x .x20 W
  have ha₁ : Acc R (absorbAll R a (bytesAt s₁.mem W (16 * 0))) s₁ := by
    have e : bytesAt s₁.mem W (16 * 0) = [] := rfl
    rw [e, Poly1305.absorbAll_nil]
    exact ha.of (fun r hr' => RegUpd.gpr_write_of_ne s .x _ (by
      intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl
  have hr₁ : Readable W s₁ := hr.of rfl rfl (RegUpd.gpr_write_of_ne s .x _ (by decide))
  have hp₁ : s₁.gpr .x20 = W + BitVec.ofNat 64 (16 * 0) := by
    simp only [s₁, RegUpd.gpr_write_self, BitVec.setWidth_eq, Nat.mul_zero, BitVec.add_zero]
  have hv : ∀ i ∈ Poly.block, vdstOf i = none := by decide +kernel
  apply WP.block_cons_iff.mpr
  refine ⟨s₁, hstart, ?_⟩
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv
    (absorb_next (n := 0) (by decide) ha₁ hp₁ hr₁)).mono fun s₂ ⟨⟨a₂, p₂, k₂⟩, v₂, sp₂, rd₂, wr₂⟩ => ?_
  apply WP.block_cons_iff.mpr
  refine ⟨s₂.write .x .x1 ((5 : BitVec 16).setWidth 64), ?_, WP.block_nil ?_⟩
  · simp only [exec, Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero, show 0 < 64 from by decide, ite_true]
  -- The loop.
  · let s₃ := s₂.write .x .x1 5#64
    have nx20 : ∀ r, r ∉ Poly.regs → r ≠ .x20 := fun r h he => h (he ▸ by decide)
    have g₂ : ∀ r, r ∉ Poly.regs → s₂.gpr r = s.gpr r := fun r h =>
      (k₂.gpr' (r := r) h).trans (RegUpd.gpr_write_of_ne s .x _ (nx20 r h))
    have hm₁ : s₁.mem = s.mem := rfl
    have hm₂ : s₂.mem = s.mem := k₂.2.1.trans hm₁
    have h0 : PI blocks v R a W s s₃ 0 := by
      refine ⟨?_, ?_, hm₂, rd₂, wr₂, ?_, sp₂, ?_, ?_, ?_⟩
      · intro k j hj; rw [write_v, v₂]; exact hn k j hj
      · intro k hk
        rw [RegUpd.gpr_write_of_ne s₂ .x _ (by intro he; exact not_words_x1 ⟨k, hk, he.symm⟩),
          g₂ _ (words_not_poly ⟨k, hk, rfl⟩)]
        exact hc k hk
      · intro r _ h1 hp; rw [RegUpd.gpr_write_of_ne s₂ .x _ h1, g₂ r hp]
      · rw [write_v, v₂]; exact ht
      · rw [RegUpd.gpr_write_of_ne s₂ .x _ (by decide), p₂]
      · rw [hm₁] at a₂
        exact a₂.of (fun r hr' => RegUpd.gpr_write_of_ne s₂ .x _ (by
          intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl
    apply WP.seq
    let Inv : Nat → State → Prop := fun n u =>
      ∃ i, i < 5 ∧ n = 5 - i ∧ PI blocks v R a W s u i ∧ u.gpr .x1 = BitVec.ofNat 64 (5 - i)
    have hstep : ∀ n u, Inv n u → WP isa
        (.seq VG.Impl.ChaCha20.AArch64.Mixed8.parallelRound
          (.block (absorb3 ++ [.subImm .x .x1 .x1 1]))) u (fun w =>
        (eval (.nonzero .x .x1) w = some false ∧ PI blocks v R a W s w 5) ∨
        (eval (.nonzero .x .x1) w = some true ∧ ∃ m < n, Inv m w)) := by
      rintro n u ⟨i, hi, rfl, hu, hcount⟩
      refine (iter_ok hi hr hu).mono fun w ⟨hw, hx⟩ => ?_
      have hwc : w.gpr .x1 = BitVec.ofNat 64 (5 - (i + 1)) := by
        rw [hx, hcount, Offset.ofNat_sub_ofNat (by omega : 1 ≤ 5 - i)]
        simp only [Nat.sub_sub]
      have he : eval (.nonzero .x .x1) w = some (BitVec.ofNat 64 (5 - (i + 1)) != 0) := by
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hwc]
      by_cases hl : i + 1 = 5
      · exact .inl ⟨by rw [he, hl]; rfl, hl ▸ hw⟩
      · have hn0 : BitVec.ofNat 64 (5 - (i + 1)) ≠ 0 := by
          intro hz
          have hz' := congrArg BitVec.toNat hz
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 5 - (i + 1) < 2 ^ 64)] at hz'
          change 5 - (i + 1) = 0 at hz'
          omega
        exact .inr ⟨by rw [he]; simpa using hn0, 5 - (i + 1), by omega, i + 1, by omega, rfl, hw, hwc⟩
    refine (WP.loop (M := isa) Inv hstep 5 s₃ ⟨0, by decide, rfl, h0, rfl⟩).mono fun w hw => ?_
    -- `x20` and `x1` restored.
    let t := w.write .x .x20 (w.gpr .x0 + BitVec.ofNat 64 64)
    have hx0 : w.gpr .x0 = s.gpr .x0 := hw.keep _ not_words_x0 (by decide) (by decide)
    apply WP.block_cons_iff.mpr
    refine ⟨t, ?_, ?_⟩
    · simpa only [State.read, BitVec.setWidth_eq] using
        exec_addImm_x (s := w) (d := .x20) (n := .x0) (imm := 64) (by decide)
    apply WP.block_cons_iff.mpr
    refine ⟨t.write .x .x1 (t.gpr restore), ?_, WP.block_nil ?_⟩
    · simpa only [State.read, BitVec.setWidth_eq, BitVec.add_zero] using
        exec_addImm_x (s := t) (d := .x1) (n := restore) (imm := 0) (by decide)
    have g (r : Reg) (h1 : r ≠ .x1) (h20 : r ≠ .x20) :
        (t.write .x .x1 (t.gpr restore)).gpr r = w.gpr r := by
      rw [RegUpd.gpr_write_of_ne t .x _ h1, RegUpd.gpr_write_of_ne w .x _ h20]
    refine ⟨fun k j hj => hw.vec k j hj, ?_, hw.mem, hw.rd, hw.wr, hw.sp, hw.table, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [g _ (by intro he; exact not_words_x1 ⟨k, hk, he.symm⟩)
        (nx20 _ (words_not_poly ⟨k, hk, rfl⟩))]
      have he (f : VG.Spec.ChaCha20.State → VG.Spec.ChaCha20.State) (x : VG.Spec.ChaCha20.State) :
          Nat.repeat (fun x => f (f x)) 5 x = Nat.repeat f 10 x := rfl
      have hs := hw.scalar k hk
      rw [he innerBlock v] at hs
      exact hs
    · intro r hw' h1 hp; rw [g r h1 (nx20 r hp)]; exact hw.keep r hw' h1 hp
    · rw [RegUpd.gpr_write_of_ne t .x _ (by decide), RegUpd.gpr_write_self, BitVec.setWidth_eq, hx0]
    · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
      by_cases h1 : restore = .x1
      · subst h1; rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
      · rw [RegUpd.gpr_write_of_ne t .x _ h1]
    · have e : 16 * (1 + 3 * 5) = 256 := rfl
      have ha' := hw.acc
      rw [e] at ha'
      exact ha'.of (fun r hr' => g r (by intro he; rw [he] at hr'; exact absurd hr' (by decide))
        (by intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl


end VG.Proof.ChaCha20Poly1305.AArch64.Stitch
