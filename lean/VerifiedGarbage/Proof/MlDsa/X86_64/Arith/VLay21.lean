import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay

/-!
# ML-DSA on x86-64: the layers of the NTT and its inverse with `len` = 2 and 1

The layer with `len = 2` runs two blocks at a time (`vstep2`): the lower
halves of their coefficients gathered into `xmm0` and the upper ones into
`xmm1` by `punpcklqdq` and `punpckhqdq`, and back. The layer with `len = 1`
runs four blocks at a time (`vstep1`): their coefficients gathered by `pshufd`
and `punpck{l,h}qdq`, and interleaved back by `punpck{l,h}dq`.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (XOnly xmm_setXmm mxcsr_setXmm ifp ifn sel sel_lt add_ofNat_zero Keep GOnly
  wp_rcxLoop sx32)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas)

theorem dword_punpcklqdq (a b : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpcklqdq a b) j = if j < 2 then dword a j else dword b (j - 2) := by
  rw [punpcklqdq_eq]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Nat.reduceLT, Nat.reduceSub, ite_true, ite_false, dword_ofDwords_0,
      dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem dword_punpckhqdq (a b : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpckhqdq a b) j = if j < 2 then dword a (2 + j) else dword b j := by
  rw [punpckhqdq_eq]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Nat.reduceLT, Nat.reduceAdd, ite_true, ite_false, dword_ofDwords_0,
      dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem dword_punpckldq' (a b : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpckldq a b) j = if j % 2 = 0 then dword a (j / 2) else dword b (j / 2) := by
  rw [dword_punpckldq]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> simp

theorem dword_punpckhdq' (a b : BitVec 128) {j : Nat} (hj : j < 4) :
    dword (XBinOp.eval .punpckhdq a b) j = if j % 2 = 0 then dword a (2 + j / 2) else dword b (2 + j / 2) := by
  rw [dword_punpckhdq]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> simp

/-- The doublewords of `x` that `pshufd` with `0xD8` puts in place `e`: the
even ones in the lower half, the odd ones in the upper half. -/
theorem dword_d8 (x : BitVec 128) {e : Nat} (he : e < 4) :
    dword (shufDwords x 0xD8) e = dword x (if e < 2 then 2 * e else 2 * (e - 2) + 1) := by
  rw [dword_shufDwords _ _ he]
  rcases cases4 he with rfl | rfl | rfl | rfl <;> rfl

/-- The general-purpose registers but `rs`, memory, the permissions and
MXCSR are as they were. -/
structure GKeep (rs : List Reg) (s s' : State) : Prop where
  keep : Keep rs s s'
  mem : s'.mem = s.mem
  mxcsr : s'.mxcsr = s.mxcsr

/-! ## The layer with `len = 2` -/

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
  {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

/-- The loads, the zetas and the gathering of the lower and upper halves. -/
abbrev pre2 (o : BitVec 8) (dz : BitVec 32) : List Instr :=
  [.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm1 (at_ .rdx 16)] ++ vzeta o ++
    [.alu .add .r8 (.imm dz), xmov .xmm2 .xmm0, xb .punpcklqdq .xmm0 .xmm1, xb .punpckhqdq .xmm2 .xmm1,
      xmov .xmm1 .xmm2]

/-- The interleaving back, the stores and the counts. -/
abbrev post2 : List Instr :=
  [xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm3, xb .punpckhqdq .xmm1 .xmm3,
    .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32),
    .alu .sub .rcx (.imm 1)]

theorem vstep2 {fP sP : Addr} {i kz : Nat} (hi : i < 32) (o : BitVec 8) (dz : BitVec 32) (zi : Nat → Nat)
    (hk : kz + 4 ≤ 256) (hsel : ∀ e < 4, kz + sel o e = zi (2 * i + e / 2))
    {F : Poly} {s : State} (hc : VConsts s) (hdx : s.gpr .rdx = coeffAddr fP (8 * i))
    (h8 : s.gpr .r8 = coeffAddr sP kz) (hS : PolyIs s.mem fP (layF blk F 2 zi (2 * i)))
    (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (.block (pre2 o dz ++ (bf ++ post2))) s fun s' =>
      PolyIs s'.mem fP (layF blk F 2 zi (2 * (i + 1))) ∧ s'.gpr .rdx = coeffAddr fP (8 * (i + 1)) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ BInv fP s s' := by
  have j0 : 8 * i + 4 ≤ 256 := by omega
  have j1 : 8 * i + 4 + 4 ≤ 256 := by omega
  have a1 : coeffAddr fP (8 * i) + BitVec.ofNat 64 16 = coeffAddr fP (8 * i + 4) := coeffAddr_add _ _ 4
  have r0 := f_in (List.mem_append_right s.rd hwf) j0
  have r1 := f_in (List.mem_append_right s.rd hwf) j1
  have hk' : ∀ j < 4, kz + sel o j < 256 := fun j _ => by have := sel_lt o j; omega
  generalize hG : layF blk F 2 zi (2 * i) = G at hS
  have lx := dlanes_load hS j0
  have ly := dlanes_load hS j1
  rw [WP.block_append_iff, show pre2 o dz = [.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm1 (at_ .rdx 16)] ++
    (vzeta o ++ [.alu .add .r8 (.imm dz), xmov .xmm2 .xmm0, xb .punpcklqdq .xmm0 .xmm1,
      xb .punpckhqdq .xmm2 .xmm1, xmov .xmm1 .xmm2]) by simp, WP.block_append_iff]
  vrund [hdx, a1, r0, r1]
  rw [WP.block_append_iff]
  refine WP.mono (vzeta_ok o hk' (by simp only [RegUpd.gpr_setXmm]; exact h8)
    (by simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm]; exact tab_in (List.mem_append_right _ hw) hk)
    (by simp only [RegUpd.mem_setXmm]; exact hT)) fun s1 ⟨z1, zo1, o1⟩ => ?_
  refine WP.mono (Q := fun (s1' : State) => DLanes (s1'.xmm .xmm0) (fun e => G[8 * i + e + 2 * (e / 2)]!) ∧
      DLanes (s1'.xmm .xmm1) (fun e => G[8 * i + 2 + e + 2 * (e / 2)]!) ∧
      ZLanes (s1'.xmm .xmm13) (fun e => zetas (zi (2 * i + e / 2))) ∧ ZOdd (s1'.xmm .xmm13) (s1'.xmm .xmm12) ∧
      VConsts s1' ∧ s1'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ GKeep [.r8] s s1') ?_
    fun s1' ⟨l0, l1, l13, l12, c1, h81, o1'⟩ => ?_
  · have g1 : s1.gpr = s.gpr := by rw [o1.gpr]; rfl
    have m1 : s1.mem = s.mem := by rw [o1.mem]; rfl
    have e1 : s1.rd = s.rd ∧ s1.wr = s.wr := ⟨by rw [o1.rd]; rfl, by rw [o1.wr]; rfl⟩
    have x1 : s1.mxcsr = s.mxcsr := by rw [o1.mxcsr]; rfl
    have x0 : s1.xmm .xmm0 = s.mem.readW (coeffAddr fP (8 * i)) 128 := by
      rw [o1.xmm _ (by decide)]; simp only [xmm_setXmm]; rfl
    have x1' : s1.xmm .xmm1 = s.mem.readW (coeffAddr fP (8 * i + 4)) 128 := by
      rw [o1.xmm _ (by decide)]; simp only [xmm_setXmm]; rfl
    have c1 : VConsts s1 := xonly_vconsts o1 ((hc.setXmm (by decide) (by decide) _).setXmm (by decide)
      (by decide) _) (by decide) (by decide)
    vrund [g1, m1, e1.1, e1.2, x1, eval_movdqa]
    refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩⟩
    · intro e he
      rw [dword_punpcklqdq _ _ he, x0, x1']
      split
      · rw [lx e he]; dsimp only; rw [show 8 * i + e + 2 * (e / 2) = 8 * i + e by omega]
      · rw [ly (e - 2) (by omega)]; dsimp only
        rw [show 8 * i + e + 2 * (e / 2) = 8 * i + 4 + (e - 2) by omega]
    · intro e he
      rw [dword_punpckhqdq _ _ he, x0, x1']
      split
      · rw [lx (2 + e) (by omega)]; dsimp only
        rw [show 8 * i + 2 + e + 2 * (e / 2) = 8 * i + (2 + e) by omega]
      · rw [ly e he]; dsimp only; rw [show 8 * i + 2 + e + 2 * (e / 2) = 8 * i + 4 + e by omega]
    · intro e he
      rw [z1 e he]; dsimp only; rw [hsel e he]
    · exact zo1
    · exact c1.q
    · exact c1.qinv
    · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, g1]
      rw [ifn (by simpa using hr)]
    all_goals simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.mem_setXmm, mxcsr_setXmm,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.mxcsr_setReg, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.mxcsr_setFlags, e1.1, e1.2, m1, x1]
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ c1 _ _ _ l0 l1 l13 l12) fun s2 ⟨a0, a3, o2⟩ => ?_
  have g2 : s2.gpr .rdx = s.gpr .rdx := by rw [o2.gpr, o1'.keep.gpr (by decide)]
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨by rw [o2.rd, o1'.keep.2.1], by rw [o2.wr, o1'.keep.2.2]⟩
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1'.mem]
  have w0 := f_in hwf j0
  have w1 := f_in hwf j1
  have c2 := xonly_vconsts o2 c1 (by decide) (by decide)
  simp only [post2, xmov, xb]
  vrund [g2, e2.1, e2.2, m2, hdx, a1, w0, w1, sx32]
  have r81 : s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [o2.gpr, h81]
  have rc1 : s2.gpr .rcx = s.gpr .rcx := by rw [o2.gpr, o1'.keep.gpr (by decide)]
  refine ⟨?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add, Nat.mul_succ], r81,
    by rw [rc1], by rw [rc1], ?_⟩
  · -- the coefficients stored
    refine polyIs_write2 hS j0 j1 (by omega)
      (a := fun e => if e < 2 then (op G[8 * i + e]! G[8 * i + 2 + e]! (zetas (zi (2 * i)))).1
        else (op G[8 * i + (e - 2)]! G[8 * i + 2 + (e - 2)]! (zetas (zi (2 * i)))).2)
      (b := fun e => if e < 2 then (op G[8 * i + 4 + e]! G[8 * i + 6 + e]! (zetas (zi (2 * i + 1)))).1
        else (op G[8 * i + 4 + (e - 2)]! G[8 * i + 6 + (e - 2)]! (zetas (zi (2 * i + 1)))).2)
      (fun e he => ?_) (fun e he => ?_) (fun j hj => ?_)
    · rw [dword_punpcklqdq _ _ he]
      split
      · rw [a0 e he]; dsimp only
        rw [ite_eq_left (by omega), show 8 * i + e + 2 * (e / 2) = 8 * i + e by omega,
          show 8 * i + 2 + e + 2 * (e / 2) = 8 * i + 2 + e by omega, show 2 * i + e / 2 = 2 * i by omega]
      · rw [a3 (e - 2) (by omega)]; dsimp only
        rw [ite_eq_right (by omega), show 8 * i + (e - 2) + 2 * ((e - 2) / 2) = 8 * i + (e - 2) by omega,
          show 8 * i + 2 + (e - 2) + 2 * ((e - 2) / 2) = 8 * i + 2 + (e - 2) by omega,
          show 2 * i + (e - 2) / 2 = 2 * i by omega]
    · rw [dword_punpckhqdq _ _ he, eval_movdqa]
      split
      · rw [a0 (2 + e) (by omega)]; dsimp only
        rw [ite_eq_left (by omega), show 8 * i + (2 + e) + 2 * ((2 + e) / 2) = 8 * i + 4 + e by omega,
          show 8 * i + 2 + (2 + e) + 2 * ((2 + e) / 2) = 8 * i + 6 + e by omega,
          show 2 * i + (2 + e) / 2 = 2 * i + 1 by omega]
      · rw [a3 e he]; dsimp only
        rw [ite_eq_right (by omega), show 8 * i + e + 2 * (e / 2) = 8 * i + 4 + (e - 2) by omega,
          show 8 * i + 2 + e + 2 * (e / 2) = 8 * i + 6 + (e - 2) by omega,
          show 2 * i + e / 2 = 2 * i + 1 by omega]
    · -- the specification: two blocks
      rw [← hG, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, layF, foldl_range_succ, foldl_range_succ, ← layF,
        hG, show 2 * 2 * (2 * i) = 8 * i by omega, show 2 * 2 * (2 * i + 1) = 8 * i + 4 by omega]
      have hn : ∀ j, j < 256 → j < n := fun j h => by rw [n_eq]; exact h
      rw [hblk.get _ _ _ _ _ (by decide) (by decide) (by rw [n_eq]; omega) _ (hn j hj)]
      have p2 := fun j (h : j < 256) => hblk.get G 2 (zi (2 * i)) (8 * i) 2 (by decide) (by decide)
        (by rw [n_eq]; omega) j (hn j h)
      rcases (by omega : j < 8 * i ∨ (8 * i ≤ j ∧ j < 8 * i + 2) ∨ (8 * i + 2 ≤ j ∧ j < 8 * i + 4) ∨
          (8 * i + 4 ≤ j ∧ j < 8 * i + 6) ∨ (8 * i + 6 ≤ j ∧ j < 8 * i + 8) ∨ 8 * i + 8 ≤ j) with
        h | h | h | h | h | h
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
        rw [show 8 * i + (j - 8 * i) = j by omega, show 8 * i + 2 + (j - 8 * i) = j + 2 by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
        rw [show 8 * i + (j - 8 * i - 2) = j - 2 by omega, show 8 * i + 2 + (j - 8 * i - 2) = j by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj, p2 (j + 2) (by omega)]
        rw [show 8 * i + 4 + (j - (8 * i + 4)) = j by omega,
          show 8 * i + 6 + (j - (8 * i + 4)) = j + 2 by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj, p2 (j - 2) (by omega)]
        rw [show 8 * i + 4 + (j - (8 * i + 4) - 2) = j - 2 by omega,
          show 8 * i + 6 + (j - (8 * i + 4) - 2) = j by omega]
      · simp (disch := omega) only [ite_eq_left, ite_eq_right, p2 j hj]
  · -- what the step keeps
    refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩, frame_write2 (Frame.refl _ _) j0 j1 _ _, ⟨?_, ?_⟩,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [o2.mxcsr, o1'.mxcsr]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      rw [o2.gpr, o1'.keep.gpr (by simp [hr])]
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.q
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.qinv

omit hbf hblk in
/-- The prologue of the layers with `len` = 2 and 1. -/
theorem vpre21 {fP sP : Addr} (k : Nat) (hk : k + 4 ≤ 256) {s : State} (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) :
    WP isa (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ leaR .r8 .rsi (4 * k))) s fun w =>
      w.gpr .rdx = fP ∧ w.gpr .r8 = coeffAddr sP k ∧ GOnly [.rdx, .r8] s w := by
  simp only [leaR]
  vrund [sx_ofNat (show 4 * k < 2 ^ 31 by omega), hsi, hdi]
  gonlyd

theorem vlay2_ok {fP sP : Addr} (k : Nat) (o : BitVec 8) (dz : BitVec 32) (zi kz : Nat → Nat) (hkz0 : kz 0 = k)
    (hk : ∀ i < 32, kz i + 4 ≤ 256) (hsel : ∀ i < 32, ∀ e < 4, kz i + sel o e = zi (2 * i + e / 2))
    (hstep : ∀ i < 32, coeffAddr sP (kz i) + BitVec.signExtend 64 dz = coeffAddr sP (kz (i + 1)))
    {F : Poly} {s : State} (hc : VConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (vlay2 bf k o dz) s fun s' => PolyIs s'.mem fP (layF blk F 2 zi 64) ∧ BInv fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega
  refine WP.seq (WP.mono (vpre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 2 zi (2 * i)) ∧ u.gpr .rdx = coeffAddr fP (8 * i) ∧
      u.gpr .r8 = coeffAddr sP (kz i) ∧ BInv fP w u)
    (fun u ou _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkz0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        gonly_vconsts ou (gonly_vconsts og hc), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : Tab zmTab u.mem sP 256 := (by rw [og.mem]; exact hT : Tab zmTab w.mem sP 256).frame hb'.frame
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  have hwf' : pR fP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hwf
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show [Instr.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm1 (at_ .rdx 16)] ++ vzeta o ++
      [.alu .add .r8 (.imm dz), xmov .xmm2 .xmm0, xb .punpcklqdq .xmm0 .xmm1, xb .punpckhqdq .xmm2 .xmm1,
        xmov .xmm1 .xmm2] ++ bf ++ [xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm3, xb .punpckhqdq .xmm1 .xmm3,
      .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)] ++
      [.alu .sub .rcx (.imm 1)] = pre2 o dz ++ (bf ++ post2) by simp [List.append_assoc]]
  exact WP.mono (vstep2 hbf hblk hi o dz zi (hk i hi) (hsel i hi) hb'.consts hdx' h8' hS' hT' hwf' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', by rw [h8'', h8', hstep i hi],
      hb'.trans hb''⟩, hcx, hzf⟩

/-! ## The layer with `len = 1` -/

/-- The loads, the zetas and the gathering of the coefficients. -/
abbrev pre1 (o : BitVec 8) (dz : BitVec 32) : List Instr :=
  [.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm2 (at_ .rdx 16)] ++ vzeta o ++
    [.alu .add .r8 (.imm dz), .xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm2 .xmm2 0xD8),
      xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2]

/-- The interleaving back, the stores and the counts. -/
abbrev post1 : List Instr :=
  [xmov .xmm1 .xmm0, xb .punpckldq .xmm0 .xmm3, xb .punpckhdq .xmm1 .xmm3,
    .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32),
    .alu .sub .rcx (.imm 1)]

omit hbf in
/-- Each coefficient after the first `b` blocks of the layer with `len = 1`. -/
theorem layF1_get (F : Poly) (zi : Nat → Nat) {b : Nat} (hb : b ≤ 128) {j : Nat} (hj : j < 256) :
    (layF blk F 1 zi b)[j]! = if j < 2 * b then
      (if j % 2 = 0 then (op F[j]! F[j + 1]! (zetas (zi (j / 2)))).1
        else (op F[j - 1]! F[j]! (zetas (zi (j / 2)))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega)]; rfl
  | succ b ih =>
    rw [layF, foldl_range_succ, ← layF,
      hblk.get _ 1 _ _ 1 (by decide) (by decide) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    by_cases h1 : 2 * 1 * b ≤ j ∧ j < 2 * 1 * b + 1
    · rw [ite_eq_left h1, ih (by omega) hj, ih (by omega) (by omega), show j / 2 = b by omega]
      simp (disch := omega) only [ite_eq_left, ite_eq_right]
    · rw [ite_eq_right h1]
      by_cases h2 : 2 * 1 * b + 1 ≤ j ∧ j < 2 * 1 * b + 1 + 1
      · rw [ite_eq_left h2, ih (by omega) (by omega), ih (by omega) hj, show j / 2 = b by omega]
        simp (disch := omega) only [ite_eq_left, ite_eq_right]
      · rw [ite_eq_right h2, ih (by omega) hj]
        by_cases h3 : j < 2 * b <;> simp (disch := omega) only [ite_eq_left, ite_eq_right]

theorem vstep1 {fP sP : Addr} {i kz : Nat} (hi : i < 32) (o : BitVec 8) (dz : BitVec 32) (zi : Nat → Nat)
    (hk : kz + 4 ≤ 256) (hsel : ∀ e < 4, kz + sel o e = zi (4 * i + e))
    {F : Poly} {s : State} (hc : VConsts s) (hdx : s.gpr .rdx = coeffAddr fP (8 * i))
    (h8 : s.gpr .r8 = coeffAddr sP kz) (hS : PolyIs s.mem fP (layF blk F 1 zi (4 * i)))
    (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (.block (pre1 o dz ++ (bf ++ post1))) s fun s' =>
      PolyIs s'.mem fP (layF blk F 1 zi (4 * (i + 1))) ∧ s'.gpr .rdx = coeffAddr fP (8 * (i + 1)) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ BInv fP s s' := by
  have j0 : 8 * i + 4 ≤ 256 := by omega
  have j1 : 8 * i + 4 + 4 ≤ 256 := by omega
  have a1 : coeffAddr fP (8 * i) + BitVec.ofNat 64 16 = coeffAddr fP (8 * i + 4) := coeffAddr_add _ _ 4
  have r0 := f_in (List.mem_append_right s.rd hwf) j0
  have r1 := f_in (List.mem_append_right s.rd hwf) j1
  have hk' : ∀ j < 4, kz + sel o j < 256 := fun j _ => by have := sel_lt o j; omega
  generalize hG : layF blk F 1 zi (4 * i) = G at hS
  have lx := dlanes_load hS j0
  have ly := dlanes_load hS j1
  rw [WP.block_append_iff, show pre1 o dz = [.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm2 (at_ .rdx 16)] ++
    (vzeta o ++ [.alu .add .r8 (.imm dz), .xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm2 .xmm2 0xD8),
      xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2]) by simp, WP.block_append_iff]
  vrund [hdx, a1, r0, r1]
  rw [WP.block_append_iff]
  refine WP.mono (vzeta_ok o hk' (by simp only [RegUpd.gpr_setXmm]; exact h8)
    (by simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm]; exact tab_in (List.mem_append_right _ hw) hk)
    (by simp only [RegUpd.mem_setXmm]; exact hT)) fun s1 ⟨z1, zo1, o1⟩ => ?_
  refine WP.mono (Q := fun (s1' : State) => DLanes (s1'.xmm .xmm0) (fun e => G[8 * i + 2 * e]!) ∧
      DLanes (s1'.xmm .xmm1) (fun e => G[8 * i + 2 * e + 1]!) ∧
      ZLanes (s1'.xmm .xmm13) (fun e => zetas (zi (4 * i + e))) ∧ ZOdd (s1'.xmm .xmm13) (s1'.xmm .xmm12) ∧
      VConsts s1' ∧ s1'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ GKeep [.r8] s s1') ?_
    fun s1' ⟨l0, l1, l13, l12, c1, h81, o1'⟩ => ?_
  · have g1 : s1.gpr = s.gpr := by rw [o1.gpr]; rfl
    have m1 : s1.mem = s.mem := by rw [o1.mem]; rfl
    have e1 : s1.rd = s.rd ∧ s1.wr = s.wr := ⟨by rw [o1.rd]; rfl, by rw [o1.wr]; rfl⟩
    have x1 : s1.mxcsr = s.mxcsr := by rw [o1.mxcsr]; rfl
    have x0 : s1.xmm .xmm0 = s.mem.readW (coeffAddr fP (8 * i)) 128 := by
      rw [o1.xmm _ (by decide)]; simp only [xmm_setXmm]; rfl
    have x2 : s1.xmm .xmm2 = s.mem.readW (coeffAddr fP (8 * i + 4)) 128 := by
      rw [o1.xmm _ (by decide)]; simp only [xmm_setXmm]; rfl
    have c1 : VConsts s1 := xonly_vconsts o1 ((hc.setXmm (by decide) (by decide) _).setXmm (by decide)
      (by decide) _) (by decide) (by decide)
    vrund [g1, m1, e1.1, e1.2, x1, eval_movdqa]
    refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩⟩
    · intro e he
      rw [dword_punpcklqdq _ _ he, x0, x2]
      split
      · rw [dword_d8 _ he, ite_eq_left (by omega), lx _ (by omega)]
      · rw [dword_d8 _ (by omega), ite_eq_left (by omega), ly _ (by omega)]; dsimp only
        rw [show 8 * i + 4 + 2 * (e - 2) = 8 * i + 2 * e by omega]
    · intro e he
      rw [dword_punpckhqdq _ _ he, x0, x2]
      split
      · rw [dword_d8 _ (by omega), ite_eq_right (by omega), lx _ (by omega)]; dsimp only
        rw [show 8 * i + (2 * (2 + e - 2) + 1) = 8 * i + 2 * e + 1 by omega]
      · rw [dword_d8 _ he, ite_eq_right (by omega), ly _ (by omega)]; dsimp only
        rw [show 8 * i + 4 + (2 * (e - 2) + 1) = 8 * i + 2 * e + 1 by omega]
    · intro e he
      rw [z1 e he]; dsimp only; rw [hsel e he]
    · exact zo1
    · exact c1.q
    · exact c1.qinv
    · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, g1]
      rw [ifn (by simpa using hr)]
    all_goals simp only [RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.mem_setXmm, mxcsr_setXmm,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.mxcsr_setReg, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.mxcsr_setFlags, e1.1, e1.2, m1, x1]
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ c1 _ _ _ l0 l1 l13 l12) fun s2 ⟨a0, a3, o2⟩ => ?_
  have g2 : s2.gpr .rdx = s.gpr .rdx := by rw [o2.gpr, o1'.keep.gpr (by decide)]
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨by rw [o2.rd, o1'.keep.2.1], by rw [o2.wr, o1'.keep.2.2]⟩
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1'.mem]
  have w0 := f_in hwf j0
  have w1 := f_in hwf j1
  have c2 := xonly_vconsts o2 c1 (by decide) (by decide)
  simp only [post1, xmov, xb]
  vrund [g2, e2.1, e2.2, m2, hdx, a1, w0, w1, sx32]
  have r81 : s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [o2.gpr, h81]
  have rc1 : s2.gpr .rcx = s.gpr .rcx := by rw [o2.gpr, o1'.keep.gpr (by decide)]
  have lg : ∀ b, b ≤ 128 → ∀ j, j < 256 → _ := fun b hb j hj => layF1_get hblk F zi (b := b) hb (j := j) hj
  refine ⟨?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add, Nat.mul_succ], r81,
    by rw [rc1], by rw [rc1], ?_⟩
  · -- the coefficients stored
    refine polyIs_write2 hS j0 j1 (by omega)
      (a := fun e => (layF blk F 1 zi (4 * (i + 1)))[8 * i + e]!)
      (b := fun e => (layF blk F 1 zi (4 * (i + 1)))[8 * i + 4 + e]!)
      (fun e he => ?_) (fun e he => ?_) (fun j hj => ?_)
    · rw [dword_punpckldq' _ _ he]
      split
      · rw [a0 (e / 2) (by omega)]; dsimp only
        rw [show 8 * i + 2 * (e / 2) = 8 * i + e by omega,
          show 4 * i + e / 2 = (8 * i + e) / 2 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
      · rw [a3 (e / 2) (by omega)]; dsimp only
        rw [show 8 * i + 2 * (e / 2) = 8 * i + e - 1 by omega, show 8 * i + e - 1 + 1 = 8 * i + e by omega,
          show 4 * i + e / 2 = (8 * i + e) / 2 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
    · rw [dword_punpckhdq' _ _ he, eval_movdqa]
      split
      · rw [a0 (2 + e / 2) (by omega)]; dsimp only
        rw [show 8 * i + 2 * (2 + e / 2) = 8 * i + 4 + e by omega,
          show 4 * i + (2 + e / 2) = (8 * i + 4 + e) / 2 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
      · rw [a3 (2 + e / 2) (by omega)]; dsimp only
        rw [show 8 * i + 2 * (2 + e / 2) = 8 * i + 4 + e - 1 by omega,
          show 8 * i + 4 + e - 1 + 1 = 8 * i + 4 + e by omega,
          show 4 * i + (2 + e / 2) = (8 * i + 4 + e) / 2 by omega, ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
    · rcases (by omega : (8 * i ≤ j ∧ j < 8 * i + 4) ∨ (8 * i + 4 ≤ j ∧ j < 8 * i + 8) ∨
          j < 8 * i ∨ 8 * i + 8 ≤ j) with h | h | h | h
      · rw [ite_eq_left h, show 8 * i + (j - 8 * i) = j by omega]
      · rw [ite_eq_right (by omega), ite_eq_left h, show 8 * i + 4 + (j - (8 * i + 4)) = j by omega]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ← hG]
        simp (disch := omega) only [lg, ite_eq_left]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ← hG]
        simp (disch := omega) only [lg, ite_eq_left, ite_eq_right]
  · -- what the step keeps
    refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩, frame_write2 (Frame.refl _ _) j0 j1 _ _, ⟨?_, ?_⟩,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [o2.mxcsr, o1'.mxcsr]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      rw [o2.gpr, o1'.keep.gpr (by simp [hr])]
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.q
    · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false]
      exact c2.qinv

theorem vlay1_ok {fP sP : Addr} (k : Nat) (o : BitVec 8) (dz : BitVec 32) (zi kz : Nat → Nat) (hkz0 : kz 0 = k)
    (hk : ∀ i < 32, kz i + 4 ≤ 256) (hsel : ∀ i < 32, ∀ e < 4, kz i + sel o e = zi (4 * i + e))
    (hstep : ∀ i < 32, coeffAddr sP (kz i) + BitVec.signExtend 64 dz = coeffAddr sP (kz (i + 1)))
    {F : Poly} {s : State} (hc : VConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (vlay1 bf k o dz) s fun s' => PolyIs s'.mem fP (layF blk F 1 zi 128) ∧ BInv fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega
  refine WP.seq (WP.mono (vpre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 1 zi (4 * i)) ∧ u.gpr .rdx = coeffAddr fP (8 * i) ∧
      u.gpr .r8 = coeffAddr sP (kz i) ∧ BInv fP w u)
    (fun u ou _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkz0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        gonly_vconsts ou (gonly_vconsts og hc), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : Tab zmTab u.mem sP 256 := (by rw [og.mem]; exact hT : Tab zmTab w.mem sP 256).frame hb'.frame
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  have hwf' : pR fP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hwf
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show [Instr.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm2 (at_ .rdx 16)] ++ vzeta o ++
      [.alu .add .r8 (.imm dz), .xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm2 .xmm2 0xD8),
        xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2] ++ bf ++
      [xmov .xmm1 .xmm0, xb .punpckldq .xmm0 .xmm3, xb .punpckhdq .xmm1 .xmm3,
      .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)] ++
      [.alu .sub .rcx (.imm 1)] = pre1 o dz ++ (bf ++ post1) by simp [List.append_assoc]]
  exact WP.mono (vstep1 hbf hblk hi o dz zi (hk i hi) (hsel i hi) hb'.consts hdx' h8' hS' hT' hwf' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', by rw [h8'', h8', hstep i hi],
      hb'.trans hb''⟩, hcx, hzf⟩

end

end VG.Proof.MlDsa.X86_64.Arith
