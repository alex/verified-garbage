import VerifiedGarbage.Proof.MlKem.X86_64.VLay

/-!
# ML-KEM on x86-64: the layers of the NTT and its inverse with `len` = 4 and 2

Untrusted: everything here is checked by Lean. The layer with `len = 4` runs
two blocks at a time (`vstep4`): the lower halves of their coefficients
gathered into `xmm0` and the upper ones into `xmm1` by `punpcklqdq` and
`punpckhqdq`, and back. The layer with `len = 2` runs four blocks at a time
(`vstep2`): their pairs gathered by `pshufd` and `punpck{l,h}qdq`, and
interleaved back by `punpck{l,h}dq`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem word_punpckldq (a b : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XBinOp.eval .punpckldq a b) i =
      if i / 2 % 2 = 0 then word a (2 * (i / 4) + i % 2) else word b (2 * (i / 4) + i % 2) := by
  rw [dword_punpckldq, word_eq_dword _ hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, ite_true,
    ite_false, Nat.reduceEqDiff, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
    word_eq_dword]

theorem word_punpckhdq (a b : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XBinOp.eval .punpckhdq a b) i =
      if i / 2 % 2 = 0 then word a (4 + 2 * (i / 4) + i % 2) else word b (4 + 2 * (i / 4) + i % 2) := by
  rw [dword_punpckhdq, word_eq_dword _ hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, ite_true,
    ite_false, Nat.reduceEqDiff, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
    word_eq_dword]

/-- The general-purpose registers but `rs`, memory, the permissions and
MXCSR are as they were. -/
structure GKeep (rs : List Reg) (s s' : State) : Prop where
  keep : Keep rs s s'
  mem : s'.mem = s.mem
  mxcsr : s'.mxcsr = s.mxcsr

theorem sel_d8 (j : Nat) (hj : j < 4) : sel 0xD8 j = [0, 2, 1, 3][j]! := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide

/-- The words of `X` that `pshufd` with `0xD8` puts in the lower half, then in the upper half. -/
theorem word_d8 (x : BitVec 128) {e : Nat} (he : e < 8) :
    word (shufDwords x 0xD8) e = word x (if e < 4 then 4 * (e / 2) + e % 2 else 4 * ((e - 4) / 2) + 2 + e % 2) := by
  rw [word_shufDwords _ _ he, sel_d8 _ (by omega)]
  congr 1
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## The layer with `len = 4` -/

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
  {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

/-- The loads, the zetas and the gathering of the lower and upper halves. -/
abbrev pre4 (o : BitVec 8) (dz : BitVec 32) : List Instr :=
  [.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm1 (at_ .rdx 16)] ++ vzeta o ++
    [.alu .add .r8 (.imm dz), xmov .xmm2 .xmm0, xb .punpcklqdq .xmm0 .xmm1, xb .punpckhqdq .xmm2 .xmm1,
      xmov .xmm1 .xmm2]

/-- The interleaving back, the stores and the counts. -/
abbrev post4 : List Instr :=
  [xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm3, xb .punpckhqdq .xmm1 .xmm3,
    .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32),
    .alu .sub .rcx (.imm 1)]

theorem vstep4 {sP : Addr} {i kz : Nat} (hi : i < 16) (o : BitVec 8) (dz : BitVec 32) (zi : Nat → Nat)
    (hk : ∀ j < 4, kz + sel o j < 128) (hsel : ∀ e < 8, kz + sel o (e / 2) = zi (2 * i + e / 4))
    {F : Poly} {s : State} (hc : VConsts s) (hdx : s.gpr .rdx = wAddr (spW sP) (16 * i))
    (h8 : s.gpr .r8 = wAddr sP kz) (hS : S16 s.mem (spW sP) (layF blk F 4 zi (2 * i))) (hT : T16 s.mem sP)
    (hw : pR sP ∈ s.wr) :
    WP isa (.block (pre4 o dz ++ (bf ++ post4))) s fun s' =>
      S16 s'.mem (spW sP) (layF blk F 4 zi (2 * (i + 1))) ∧ s'.gpr .rdx = wAddr (spW sP) (16 * (i + 1)) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ BInv sP s s' := by
  have j0 : 16 * i + 8 ≤ 256 := by omega
  have j1 : 16 * i + 8 + 8 ≤ 256 := by omega
  have a1 : wAddr (spW sP) (16 * i) + BitVec.ofNat 64 16 = wAddr (spW sP) (16 * i + 8) := wAddr_add _ _ 8
  have r0 := sp_in (List.mem_append_right s.rd hw) j0
  have r1 := sp_in (List.mem_append_right s.rd hw) j1
  have rz := tab_in (List.mem_append_right s.rd hw) (k := kz) (by have := hk 0 (by decide); omega)
  generalize hG : layF blk F 4 zi (2 * i) = G at hS
  have lx := lanes_load hS j0
  have ly := lanes_load hS j1
  have lz := zeta_lanes o hk hT
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => Lanes (s1.xmm .xmm0) (fun e => G[16 * i + e + 4 * (e / 4)]!) ∧
      Lanes (s1.xmm .xmm1) (fun e => G[16 * i + 4 + e + 4 * (e / 4)]!) ∧
      ZLanes (s1.xmm .xmm13) (fun e => zeta (zi (2 * i + e / 4))) ∧ VConsts s1 ∧
      s1.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ GKeep [.r8] s s1) ?_
    fun s1 ⟨l0, l1, l13, c1, h81, o1⟩ => ?_
  · simp only [pre4, vzeta, xmov, xb]
    vrunm [hdx, a1, r0, r1, rz, h8]
    refine ⟨?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩⟩
    rotate_left 3
    · constructor <;>
        simp only [xmm_setXmm, RegUpd.xmm_setReg, RegUpd.xmm_setFlags, reduceCtorEq, ite_false] <;>
        [exact hc.q; exact hc.qinv]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
    all_goals try simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.mem_setXmm, mxcsr_setXmm,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.mxcsr_setReg, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.mxcsr_setFlags]
    · intro e he
      rw [word_punpcklqdq _ _ he]
      split
      · rw [lx e he]; dsimp only; rw [show 16 * i + e + 4 * (e / 4) = 16 * i + e by omega]
      · rw [ly (e - 4) (by omega)]; dsimp only
        rw [show 16 * i + e + 4 * (e / 4) = 16 * i + 8 + (e - 4) by omega]
    · intro e he
      rw [word_movdqa, word_punpckhqdq _ _ he, word_movdqa]
      split
      · rw [lx (4 + e) (by omega)]; dsimp only
        rw [show 16 * i + 4 + e + 4 * (e / 4) = 16 * i + (4 + e) by omega]
      · rw [ly e he]; dsimp only; rw [show 16 * i + 4 + e + 4 * (e / 4) = 16 * i + 8 + e by omega]
    · intro e he
      rw [lz e he]; dsimp only; rw [hsel e he]
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ c1 _ _ _ l0 l1 l13) fun s2 ⟨a0, a3, o2⟩ => ?_
  have g2 : s2.gpr .rdx = s.gpr .rdx := by rw [o2.gpr, o1.keep.gpr (by decide)]
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨by rw [o2.rd, o1.keep.2.1], by rw [o2.wr, o1.keep.2.2]⟩
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  have w0 := sp_in hw j0
  have w1 := sp_in hw j1
  have c2 := o2.consts c1 (by decide) (by decide)
  simp only [post4, xmov, xb]
  vrunm [g2, e2.1, e2.2, m2, hdx, a1, w0, w1, sx32]
  have r81 : s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [o2.gpr, h81]
  have rc1 : s2.gpr .rcx = s.gpr .rcx := by rw [o2.gpr, o1.keep.gpr (by decide)]
  refine ⟨?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add, Nat.mul_succ], r81,
    by rw [rc1], by rw [rc1], ?_⟩
  · -- the words stored
    refine s16_write2 hS j0 j1 (by omega)
      (a := fun e => if e < 4 then (op G[16 * i + e]! G[16 * i + 4 + e]! (zeta (zi (2 * i)))).1
        else (op G[16 * i + (e - 4)]! G[16 * i + 4 + (e - 4)]! (zeta (zi (2 * i)))).2)
      (b := fun e => if e < 4 then (op G[16 * i + 8 + e]! G[16 * i + 12 + e]! (zeta (zi (2 * i + 1)))).1
        else (op G[16 * i + 8 + (e - 4)]! G[16 * i + 12 + (e - 4)]! (zeta (zi (2 * i + 1)))).2)
      (fun e he => ?_) (fun e he => ?_) (fun j hj => ?_)
    · rw [word_punpcklqdq _ _ he]
      split
      · rw [a0 e he]; dsimp only
        rw [ite_eq_left (by omega), show 16 * i + e + 4 * (e / 4) = 16 * i + e by omega,
          show 16 * i + 4 + e + 4 * (e / 4) = 16 * i + 4 + e by omega, show 2 * i + e / 4 = 2 * i by omega]
      · rw [a3 (e - 4) (by omega)]; dsimp only
        rw [ite_eq_right (by omega), show 16 * i + (e - 4) + 4 * ((e - 4) / 4) = 16 * i + (e - 4) by omega,
          show 16 * i + 4 + (e - 4) + 4 * ((e - 4) / 4) = 16 * i + 4 + (e - 4) by omega,
          show 2 * i + (e - 4) / 4 = 2 * i by omega]
    · rw [word_punpckhqdq _ _ he, word_movdqa]
      split
      · rw [a0 (4 + e) (by omega)]; dsimp only
        rw [ite_eq_left (by omega), show 16 * i + (4 + e) + 4 * ((4 + e) / 4) = 16 * i + 8 + e by omega,
          show 16 * i + 4 + (4 + e) + 4 * ((4 + e) / 4) = 16 * i + 12 + e by omega,
          show 2 * i + (4 + e) / 4 = 2 * i + 1 by omega]
      · rw [a3 e he]; dsimp only
        rw [ite_eq_right (by omega), show 16 * i + e + 4 * (e / 4) = 16 * i + 8 + (e - 4) by omega,
          show 16 * i + 4 + e + 4 * (e / 4) = 16 * i + 12 + (e - 4) by omega,
          show 2 * i + e / 4 = 2 * i + 1 by omega]
    · -- the specification: two blocks
      rw [← hG, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, layF, foldl_range_succ, foldl_range_succ, ← layF,
        hG, show 2 * 4 * (2 * i) = 16 * i by omega, show 2 * 4 * (2 * i + 1) = 16 * i + 8 by omega]
      have hn : ∀ j, j < 256 → j < n := fun j h => by rw [n_eq]; exact h
      rw [hblk.get _ _ _ _ _ (by decide) (by decide) (by rw [n_eq]; omega) _ (hn j hj)]
      have p2 := fun j (h : j < 256) => hblk.get G 4 (zi (2 * i)) (16 * i) 4 (by decide) (by decide)
        (by rw [n_eq]; omega) j (hn j h)
      rcases (by omega : j < 16 * i ∨ (16 * i ≤ j ∧ j < 16 * i + 4) ∨ (16 * i + 4 ≤ j ∧ j < 16 * i + 8) ∨
          (16 * i + 8 ≤ j ∧ j < 16 * i + 12) ∨ (16 * i + 12 ≤ j ∧ j < 16 * i + 16) ∨ 16 * i + 16 ≤ j) with
        h | h | h | h | h | h
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
        rw [show 16 * i + (j - 16 * i) = j by omega, show 16 * i + 4 + (j - 16 * i) = j + 4 by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
        rw [show 16 * i + (j - 16 * i - 4) = j - 4 by omega, show 16 * i + 4 + (j - 16 * i - 4) = j by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj, p2 (j + 4) (by omega)]
        rw [show 16 * i + 8 + (j - (16 * i + 8)) = j by omega,
          show 16 * i + 12 + (j - (16 * i + 8)) = j + 4 by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj, p2 (j - 4) (by omega)]
        rw [show 16 * i + 8 + (j - (16 * i + 8) - 4) = j - 4 by omega,
          show 16 * i + 12 + (j - (16 * i + 8) - 4) = j by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
  · -- what the step keeps
    refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩, frame_write2 (Frame.refl _ _) j0 j1 _ _, ⟨?_, ?_⟩,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [o2.mxcsr, o1.mxcsr]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      rw [o2.gpr, o1.keep.gpr (by simp [hr])]
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.q
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.qinv


omit hbf hblk in
/-- The prologue of the layers with `len` = 4 and 2. -/
theorem vpre42 {sP : Addr} (k : Nat) (hk : k < 128) {s : State} (hsi : s.gpr .rsi = sP) :
    WP isa (.block (leaR .rdx .rsi oS ++ leaR .r8 .rsi (2 * k))) s fun w =>
      w.gpr .rdx = spW sP ∧ w.gpr .r8 = wAddr sP k ∧ GOnly [.rdx, .r8] s w := by
  simp only [leaR, oS]
  vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), sx_ofNat (show 2 * k < 2 ^ 31 by omega), hsi]
  gonly

theorem vlay4_ok {sP : Addr} (k : Nat) (o : BitVec 8) (dz : BitVec 32) (zi kz : Nat → Nat) (hkz0 : kz 0 = k)
    (hk : ∀ i < 16, ∀ j < 4, kz i + sel o j < 128)
    (hsel : ∀ i < 16, ∀ e < 8, kz i + sel o (e / 2) = zi (2 * i + e / 4))
    (hstep : ∀ i < 16, wAddr sP (kz i) + BitVec.signExtend 64 dz = wAddr sP (kz (i + 1)))
    {F : Poly} {s : State} (hc : VConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay4 bf k o dz) s fun s' => S16 s'.mem (spW sP) (layF blk F 4 zi 32) ∧ BInv sP s s' := by
  have hk0 : k < 128 := by have := hk 0 (by decide) 0 (by decide); omega
  refine WP.seq (WP.mono (vpre42 k hk0 hsi)
    fun w ⟨hdx, h8, og⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 16) (by decide) (by decide)
    (fun i u => S16 u.mem (spW sP) (layF blk F 4 zi (2 * i)) ∧ u.gpr .rdx = wAddr (spW sP) (16 * i) ∧
      u.gpr .r8 = wAddr sP (kz i) ∧ BInv sP w u)
    (fun u ou _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, wAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkz0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        ou.consts (og.consts hc), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : T16 u.mem sP := (by rw [og.mem]; exact hT : T16 w.mem sP).frame hb'.frame
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show pre4 o dz ++ bf ++ [xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm3, xb .punpckhqdq .xmm1 .xmm3,
      .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)] ++
      [.alu .sub .rcx (.imm 1)] = pre4 o dz ++ (bf ++ post4) by simp [List.append_assoc]]
  exact WP.mono (vstep4 hbf hblk hi o dz zi (hk i hi) (hsel i hi) hb'.consts hdx' h8' hS' hT' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', by rw [h8'', h8', hstep i hi],
      hb'.trans hb''⟩, hcx, hzf⟩


/-! ## The layer with `len = 2` -/

/-- The loads, the zetas and the gathering of the pairs. -/
abbrev pre2 (o : BitVec 8) (dz : BitVec 32) : List Instr :=
  [.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm2 (at_ .rdx 16)] ++ vzeta o ++
    [.alu .add .r8 (.imm dz), .xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm2 .xmm2 0xD8),
      xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2]

/-- The interleaving back, the stores and the counts. -/
abbrev post2 : List Instr :=
  [xmov .xmm1 .xmm0, xb .punpckldq .xmm0 .xmm3, xb .punpckhdq .xmm1 .xmm3,
    .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32),
    .alu .sub .rcx (.imm 1)]

omit hbf in
/-- Each coefficient after the first `b` blocks of the layer with `len = 2`. -/
theorem layF2_get (F : Poly) (zi : Nat → Nat) {b : Nat} (hb : b ≤ 64) {j : Nat} (hj : j < 256) :
    (layF blk F 2 zi b)[j]! = if j < 4 * b then
      (if j % 4 < 2 then (op F[j]! F[j + 2]! (zeta (zi (j / 4)))).1
        else (op F[j - 2]! F[j]! (zeta (zi (j / 4)))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega)]; rfl
  | succ b ih =>
    rw [layF, foldl_range_succ, ← layF,
      hblk.get _ 2 _ _ 2 (by decide) (by decide) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    by_cases h1 : 2 * 2 * b ≤ j ∧ j < 2 * 2 * b + 2
    · rw [ite_eq_left h1, ih (by omega) hj, ih (by omega) (by omega), show j / 4 = b by omega]
      simp (disch := omega) only [ite_eq_left, ite_eq_right]
    · rw [ite_eq_right h1]
      by_cases h2 : 2 * 2 * b + 2 ≤ j ∧ j < 2 * 2 * b + 2 + 2
      · rw [ite_eq_left h2, ih (by omega) (by omega), ih (by omega) hj, show j / 4 = b by omega]
        simp (disch := omega) only [ite_eq_left, ite_eq_right]
      · rw [ite_eq_right h2, ih (by omega) hj]
        by_cases h3 : j < 4 * b <;> simp (disch := omega) only [ite_eq_left, ite_eq_right]

theorem vstep2 {sP : Addr} {i kz : Nat} (hi : i < 16) (o : BitVec 8) (dz : BitVec 32) (zi : Nat → Nat)
    (hk : ∀ j < 4, kz + sel o j < 128) (hsel : ∀ e < 8, kz + sel o (e / 2) = zi (4 * i + e / 2))
    {F : Poly} {s : State} (hc : VConsts s) (hdx : s.gpr .rdx = wAddr (spW sP) (16 * i))
    (h8 : s.gpr .r8 = wAddr sP kz) (hS : S16 s.mem (spW sP) (layF blk F 2 zi (4 * i))) (hT : T16 s.mem sP)
    (hw : pR sP ∈ s.wr) :
    WP isa (.block (pre2 o dz ++ (bf ++ post2))) s fun s' =>
      S16 s'.mem (spW sP) (layF blk F 2 zi (4 * (i + 1))) ∧ s'.gpr .rdx = wAddr (spW sP) (16 * (i + 1)) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ BInv sP s s' := by
  have j0 : 16 * i + 8 ≤ 256 := by omega
  have j1 : 16 * i + 8 + 8 ≤ 256 := by omega
  have a1 : wAddr (spW sP) (16 * i) + BitVec.ofNat 64 16 = wAddr (spW sP) (16 * i + 8) := wAddr_add _ _ 8
  have r0 := sp_in (List.mem_append_right s.rd hw) j0
  have r1 := sp_in (List.mem_append_right s.rd hw) j1
  have rz := tab_in (List.mem_append_right s.rd hw) (k := kz) (by have := hk 0 (by decide); omega)
  generalize hG : layF blk F 2 zi (4 * i) = G at hS
  have lx := lanes_load hS j0
  have ly := lanes_load hS j1
  have lz := zeta_lanes o hk hT
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => Lanes (s1.xmm .xmm0) (fun e => G[16 * i + 4 * (e / 2) + e % 2]!) ∧
      Lanes (s1.xmm .xmm1) (fun e => G[16 * i + 4 * (e / 2) + 2 + e % 2]!) ∧
      ZLanes (s1.xmm .xmm13) (fun e => zeta (zi (4 * i + e / 2))) ∧ VConsts s1 ∧
      s1.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ GKeep [.r8] s s1) ?_
    fun s1 ⟨l0, l1, l13, c1, h81, o1⟩ => ?_
  · simp only [pre2, vzeta, xmov, xb]
    vrunm [hdx, a1, r0, r1, rz, h8]
    refine ⟨?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩⟩
    rotate_left 3
    · constructor <;>
        simp only [xmm_setXmm, RegUpd.xmm_setReg, RegUpd.xmm_setFlags, reduceCtorEq, ite_false] <;>
        [exact hc.q; exact hc.qinv]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
    all_goals try simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.mem_setXmm, mxcsr_setXmm,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.mxcsr_setReg, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.mxcsr_setFlags]
    · intro e he
      rw [word_punpcklqdq _ _ he]
      split
      · rw [word_d8 _ he, ite_eq_left (by omega), lx _ (by omega)]; dsimp only
        rw [show 16 * i + (4 * (e / 2) + e % 2) = 16 * i + 4 * (e / 2) + e % 2 by omega]
      · rw [word_d8 _ (by omega), ite_eq_left (by omega), ly _ (by omega)]; dsimp only
        rw [show 16 * i + 8 + (4 * ((e - 4) / 2) + (e - 4) % 2) = 16 * i + 4 * (e / 2) + e % 2 by omega]
    · intro e he
      rw [word_punpckhqdq _ _ he]
      simp only [word_movdqa]
      split
      · rw [word_d8 _ (by omega), ite_eq_right (by omega), lx _ (by omega)]; dsimp only
        rw [show 16 * i + (4 * ((4 + e - 4) / 2) + 2 + (4 + e) % 2) = 16 * i + 4 * (e / 2) + 2 + e % 2 by omega]
      · rw [word_d8 _ he, ite_eq_right (by omega), ly _ (by omega)]; dsimp only
        rw [show 16 * i + 8 + (4 * ((e - 4) / 2) + 2 + e % 2) = 16 * i + 4 * (e / 2) + 2 + e % 2 by omega]
    · intro e he
      rw [lz e he]; dsimp only; rw [hsel e he]
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ c1 _ _ _ l0 l1 l13) fun s2 ⟨a0, a3, o2⟩ => ?_
  have g2 : s2.gpr .rdx = s.gpr .rdx := by rw [o2.gpr, o1.keep.gpr (by decide)]
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨by rw [o2.rd, o1.keep.2.1], by rw [o2.wr, o1.keep.2.2]⟩
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  have w0 := sp_in hw j0
  have w1 := sp_in hw j1
  have c2 := o2.consts c1 (by decide) (by decide)
  simp only [post2, xmov, xb]
  vrunm [g2, e2.1, e2.2, m2, hdx, a1, w0, w1, sx32]
  have r81 : s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [o2.gpr, h81]
  have rc1 : s2.gpr .rcx = s.gpr .rcx := by rw [o2.gpr, o1.keep.gpr (by decide)]
  have lg : ∀ b, b ≤ 64 → ∀ j, j < 256 → _ := fun b hb j hj => layF2_get hblk F zi (b := b) hb (j := j) hj
  refine ⟨?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add, Nat.mul_succ], r81,
    by rw [rc1], by rw [rc1], ?_⟩
  · -- the words stored
    refine s16_write2 hS j0 j1 (by omega)
      (a := fun e => (layF blk F 2 zi (4 * (i + 1)))[16 * i + e]!)
      (b := fun e => (layF blk F 2 zi (4 * (i + 1)))[16 * i + 8 + e]!)
      (fun e he => ?_) (fun e he => ?_) (fun j hj => ?_)
    · rw [word_punpckldq _ _ he]
      split
      · rw [a0 (2 * (e / 4) + e % 2) (by omega)]; dsimp only
        rw [show 16 * i + 4 * ((2 * (e / 4) + e % 2) / 2) + (2 * (e / 4) + e % 2) % 2 = 16 * i + e by omega,
          show 16 * i + 4 * ((2 * (e / 4) + e % 2) / 2) + 2 + (2 * (e / 4) + e % 2) % 2 = 16 * i + e + 2 by omega,
          show 4 * i + (2 * (e / 4) + e % 2) / 2 = (16 * i + e) / 4 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
      · rw [a3 (2 * (e / 4) + e % 2) (by omega)]; dsimp only
        rw [show 16 * i + 4 * ((2 * (e / 4) + e % 2) / 2) + (2 * (e / 4) + e % 2) % 2 = 16 * i + e - 2 by omega,
          show 16 * i + 4 * ((2 * (e / 4) + e % 2) / 2) + 2 + (2 * (e / 4) + e % 2) % 2 = 16 * i + e by omega,
          show 4 * i + (2 * (e / 4) + e % 2) / 2 = (16 * i + e) / 4 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
    · rw [word_punpckhdq _ _ he]
      simp only [word_movdqa]
      split
      · rw [a0 (4 + 2 * (e / 4) + e % 2) (by omega)]; dsimp only
        rw [show 16 * i + 4 * ((4 + 2 * (e / 4) + e % 2) / 2) + (4 + 2 * (e / 4) + e % 2) % 2 = 16 * i + 8 + e by
            omega,
          show 16 * i + 4 * ((4 + 2 * (e / 4) + e % 2) / 2) + 2 + (4 + 2 * (e / 4) + e % 2) % 2 =
            16 * i + 8 + e + 2 by omega,
          show 4 * i + (4 + 2 * (e / 4) + e % 2) / 2 = (16 * i + 8 + e) / 4 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
      · rw [a3 (4 + 2 * (e / 4) + e % 2) (by omega)]; dsimp only
        rw [show 16 * i + 4 * ((4 + 2 * (e / 4) + e % 2) / 2) + (4 + 2 * (e / 4) + e % 2) % 2 =
            16 * i + 8 + e - 2 by omega,
          show 16 * i + 4 * ((4 + 2 * (e / 4) + e % 2) / 2) + 2 + (4 + 2 * (e / 4) + e % 2) % 2 = 16 * i + 8 + e by
            omega,
          show 4 * i + (4 + 2 * (e / 4) + e % 2) / 2 = (16 * i + 8 + e) / 4 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
    · rcases (by omega : (16 * i ≤ j ∧ j < 16 * i + 8) ∨ (16 * i + 8 ≤ j ∧ j < 16 * i + 16) ∨
          j < 16 * i ∨ 16 * i + 16 ≤ j) with h | h | h | h
      · rw [ite_eq_left h, show 16 * i + (j - 16 * i) = j by omega]
      · rw [ite_eq_right (by omega), ite_eq_left h, show 16 * i + 8 + (j - (16 * i + 8)) = j by omega]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ← hG]
        simp (disch := omega) only [lg, ite_eq_left]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
  · -- what the step keeps
    refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩, frame_write2 (Frame.refl _ _) j0 j1 _ _, ⟨?_, ?_⟩,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [o2.mxcsr, o1.mxcsr]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      rw [o2.gpr, o1.keep.gpr (by simp [hr])]
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.q
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.qinv



theorem vlay2_ok {sP : Addr} (k : Nat) (o : BitVec 8) (dz : BitVec 32) (zi kz : Nat → Nat) (hkz0 : kz 0 = k)
    (hk : ∀ i < 16, ∀ j < 4, kz i + sel o j < 128)
    (hsel : ∀ i < 16, ∀ e < 8, kz i + sel o (e / 2) = zi (4 * i + e / 2))
    (hstep : ∀ i < 16, wAddr sP (kz i) + BitVec.signExtend 64 dz = wAddr sP (kz (i + 1)))
    {F : Poly} {s : State} (hc : VConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay2 bf k o dz) s fun s' => S16 s'.mem (spW sP) (layF blk F 2 zi 64) ∧ BInv sP s s' := by
  have hk0 : k < 128 := by have := hk 0 (by decide) 0 (by decide); omega
  refine WP.seq (WP.mono (vpre42 k hk0 hsi) fun w ⟨hdx, h8, og⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 16) (by decide) (by decide)
    (fun i u => S16 u.mem (spW sP) (layF blk F 2 zi (4 * i)) ∧ u.gpr .rdx = wAddr (spW sP) (16 * i) ∧
      u.gpr .r8 = wAddr sP (kz i) ∧ BInv sP w u)
    (fun u ou _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, wAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkz0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        ou.consts (og.consts hc), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : T16 u.mem sP := (by rw [og.mem]; exact hT : T16 w.mem sP).frame hb'.frame
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show pre2 o dz ++ bf ++ [xmov .xmm1 .xmm0, xb .punpckldq .xmm0 .xmm3, xb .punpckhdq .xmm1 .xmm3,
      .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)] ++
      [.alu .sub .rcx (.imm 1)] = pre2 o dz ++ (bf ++ post2) by simp [List.append_assoc]]
  exact WP.mono (vstep2 hbf hblk hi o dz zi (hk i hi) (hsel i hi) hb'.consts hdx' h8' hS' hT' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', by rw [h8'', h8', hstep i hi],
      hb'.trans hb''⟩, hcx, hzf⟩
end

end VG.Proof.MlKem.X86_64
