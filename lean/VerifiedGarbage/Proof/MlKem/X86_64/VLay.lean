import VerifiedGarbage.Proof.MlKem.X86_64.VMem
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ML-KEM on x86-64: the layers of the NTT and its inverse with `len ≥ 8`

For any butterfly code `bf` that does what `op` does to the words of two
registers (`VBflyOk`), and any block of the specification whose butterflies do
`op` (`BlkOk`): eight butterflies of a block (`vstep`), the `len / 8` of them
of a block (`vblock_ok`), and the `128 / len` blocks of a layer (`vlay_ok`),
from the words of the polynomial at `Sp`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- Runs a block of general-purpose and SSE instructions. -/
syntax "vrunm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| vrunm) => `(tactic| vrunm [])
  | `(tactic| vrunm [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
        readSrc, readSrc32, execAlu, execAlu32, State.setReg32, arithFlags_eq, ea_at, add_ofNat_zero,
        State.load128, State.store128, State.load64, State.store64, State.load32, State.store32, setReg_gpr, setReg_mem, setReg_rd, setReg_wr, setReg_cf, setReg_zf,
        setFlags_gpr, setFlags_mem, setFlags_rd, setFlags_wr, setFlags_cf, setFlags_zf, RegUpd.gpr_setXmm,
        RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.zf_setXmm, mxcsr_setXmm, xmm_setXmm,
        RegUpd.xmm_setReg, RegUpd.xmm_setFlags, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags,
        Option.bind_some, Option.map_some, Option.map, Option.some.injEq, exists_eq_left', ite_true,
        ite_false, reduceCtorEq, BitVec.sub_self, sx1, sx16, true_and, and_true, List.cons_append,
        List.nil_append, xb, xmov, $ls,*]))

/-- The code `bf` of eight butterflies does what `op` does to each pair of
words of `xmm0` and `xmm1`, with the zetas in `xmm13`, leaving the results
in `xmm0` and `xmm3`. -/
def VBflyOk (bf : List Instr) (op : Zq → Zq → Zq → Zq × Zq) : Prop :=
  ∀ s : State, VConsts s → ∀ x y ζ : Nat → Zq, Lanes (s.xmm .xmm0) x → Lanes (s.xmm .xmm1) y →
    ZLanes (s.xmm .xmm13) ζ →
    WP isa (.block bf) s fun s' => Lanes (s'.xmm .xmm0) (fun i => (op (x i) (y i) (ζ i)).1) ∧
      Lanes (s'.xmm .xmm3) (fun i => (op (x i) (y i) (ζ i)).2) ∧ XOnly [.xmm1, .xmm2, .xmm0, .xmm3] s s'

theorem vbfly_spec : VBflyOk vbfly (fun x y z => (x + z * y, x - z * y)) :=
  fun _ hc _ _ _ hx hy hz => vbfly_ok hc hx hy hz

theorem vibfly_spec : VBflyOk vibfly (fun x y z => (x + y, z * (y - x))) :=
  fun _ hc _ _ _ hx hy hz => vibfly_ok hc hx hy hz

/-- The first `t` butterflies of a block of the specification do `op` to
`(j, j + len)`. -/
structure BlkOk (blk : Poly → Nat → Nat → Nat → Nat → Poly) (op : Zq → Zq → Zq → Zq × Zq) : Prop where
  zero : ∀ f len k st, blk f len k st 0 = f
  add : ∀ f len k st t t', blk f len k st (t + t') = blk (blk f len k st t) len k (st + t) t'
  get : ∀ f len k st t, 0 < len → t ≤ len → st + len + t ≤ n → ∀ i < n,
    (blk f len k st t)[i]! = if st ≤ i ∧ i < st + t then (op f[i]! f[i + len]! (zeta k)).1
      else if st + len ≤ i ∧ i < st + len + t then (op f[i - len]! f[i]! (zeta k)).2 else f[i]!

theorem nttBlk_ok : BlkOk nttBlockN (fun x y z => (x + z * y, x - z * y)) :=
  ⟨nttBlockN_zero, nttBlockN_add, fun f _ _ _ _ hl ht hs _ hi => nttBlockN_get' f hl ht hs hi⟩

theorem nttInvBlk_ok : BlkOk nttInvBlockN (fun x y z => (x + y, z * (y - x))) :=
  ⟨nttInvBlockN_zero, nttInvBlockN_add, fun f _ _ _ _ hl ht hs _ hi => nttInvBlockN_get' f hl ht hs hi⟩

/-! ## A block -/

/-- The words of the polynomial, 256 bytes into the working space. -/
abbrev spW (sP : Addr) : Addr := sP + BitVec.ofNat 64 256

theorem sp_in {rs : List Region} {sP : Addr} (hw : pR sP ∈ rs) {j : Nat} (hj : j + 8 ≤ 256) :
    InRegions rs (wAddr (spW sP) j) 16 := by
  refine ⟨_, hw, ?_⟩
  rw [wAddr, spW, Offset.add_add]
  exact Offset.contains_base sP (by omega) (by omega)

theorem tab_in {rs : List Region} {sP : Addr} (hw : pR sP ∈ rs) {k : Nat} (hk : 2 * k + 16 ≤ 1024) :
    InRegions rs (wAddr sP k) 16 :=
  ⟨_, hw, Offset.contains_base sP (by omega) (by omega)⟩

theorem sel_zero (j : Nat) : sel 0 j = 0 := by simp [sel]

/-- The code of a block of a layer with `len ≥ 8`. -/
abbrev vblk (bf : List Instr) (len : Nat) (dz : BitVec 32) : Prog isa :=
  .seq (.block (vzeta 0 ++ ([.alu .add .r8 (.imm dz)] : List Instr)))
    (.seq (rcxLoop (len / 8) (([.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm1 (at_ .rdx (2 * len))] : List Instr) ++
        bf ++ ([.movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx (2 * len)) .xmm3,
          .alu .add .rdx (.imm 16)] : List Instr)))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (2 * len))), .alu .sub .rax (.imm 1)]))

/-- Only the general-purpose registers `rs` (and the flags) changed. -/
structure GOnly (rs : List Reg) (s s' : State) : Prop where
  keep : Keep rs s s'
  mem : s'.mem = s.mem
  xmm : s'.xmm = s.xmm
  mxcsr : s'.mxcsr = s.mxcsr

/-- `GOnly` of a chain of `setReg` and `setFlags`. -/
macro "gonly" : tactic => `(tactic| exact ⟨⟨fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false], rfl, rfl⟩, rfl, rfl, rfl⟩)

theorem GOnly.consts {rs : List Reg} {s s' : State} (h : GOnly rs s s') (hc : VConsts s) : VConsts s' :=
  ⟨by rw [h.xmm]; exact hc.q, by rw [h.xmm]; exact hc.qinv⟩

/-- `rcxLoop N body`: the body runs `N` times, from a state that the `mov`
of the count changed in `rcx` only. -/
theorem wp_rcxLoop {body : List Instr} {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 31) (Inv : Nat → State → Prop)
    {s₀ : State} (h0 : ∀ s, GOnly [.rcx] s₀ s → s.gpr .rcx = BitVec.ofNat 64 N → Inv 0 s)
    (hbody : ∀ i < N, ∀ s, Inv i s →
      WP isa (.block (body ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' => Inv (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) :
    WP isa (rcxLoop N body) s₀ (Inv N) := by
  refine WP.seq (WP.mono (Q := fun (s : State) => GOnly [.rcx] s₀ s ∧ s.gpr .rcx = BitVec.ofNat 64 N)
    (by vrunm; exact ⟨by gonly, by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega⟩) fun s ⟨o, hc⟩ => ?_)
  exact wp_countdown (by omega) hN Inv (fun i hi s hI _ => hbody i hi s hI) (fun _ h => h) (h0 s o hc) hc

/-- The first `b` blocks of the layer with `len`, block `c` with the zeta
`zeta (zi c)`. -/
def layF (blk : Poly → Nat → Nat → Nat → Nat → Poly) (F : Poly) (len : Nat) (zi : Nat → Nat) (b : Nat) :
    Poly :=
  (List.range b).foldl (fun f c => blk f len (zi c) (2 * len * c) len) F

/-- The facts a block keeps. -/
structure BInv (sP : Addr) (s₀ s : State) : Prop where
  keep : Keep [.r8, .rcx, .rdx, .rax] s₀ s
  frame : Frame [sR (spW sP)] s₀.mem s.mem
  consts : VConsts s
  mxcsr : s.mxcsr = s₀.mxcsr

theorem BInv.trans {sP : Addr} {s₁ s₂ s₃ : State} (h₁ : BInv sP s₁ s₂) (h₂ : BInv sP s₂ s₃) : BInv sP s₁ s₃ :=
  ⟨(h₁.keep.trans h₂.keep).mono (by simp), h₁.frame.trans h₂.frame, h₂.consts, h₂.mxcsr.trans h₁.mxcsr⟩

/-! ## Eight butterflies -/

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
  {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

/-- The body of the loop over the vectors of a block. -/
abbrev vbody (bf : List Instr) (len : Nat) : List Instr :=
  ([.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm1 (at_ .rdx (2 * len))] : List Instr) ++ bf ++
    ([.movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx (2 * len)) .xmm3, .alu .add .rdx (.imm 16)] : List Instr) ++
    ([.alu .sub .rcx (.imm 1)] : List Instr)

theorem vstep {Sp : Addr} {len st u k : Nat} (hl : 0 < len) (hs : st + 2 * len ≤ 256) (hu : 8 * u + 8 ≤ len)
    {G : Poly} {s : State} (hc : VConsts s) (hz : ZLanes (s.xmm .xmm13) (fun _ => zeta k))
    (hdx : s.gpr .rdx = wAddr Sp (st + 8 * u)) (hS : S16 s.mem Sp (blk G len k st (8 * u)))
    (hin : ∀ j, j + 8 ≤ 256 → InRegions s.wr (wAddr Sp j) 16) :
    WP isa (.block (vbody bf len)) s fun s' =>
      S16 s'.mem Sp (blk G len k st (8 * (u + 1))) ∧ s'.gpr .rdx = wAddr Sp (st + 8 * (u + 1)) ∧
        Frame [sR Sp] s.mem s'.mem ∧ VConsts s' ∧ s'.xmm .xmm13 = s.xmm .xmm13 ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  have j0 : st + 8 * u + 8 ≤ 256 := by omega
  have j1 : st + 8 * u + len + 8 ≤ 256 := by omega
  have a1 : wAddr Sp (st + 8 * u) + BitVec.ofNat 64 (2 * len) = wAddr Sp (st + 8 * u + len) := wAddr_add _ _ _
  have r0 : InRegions (s.rd ++ s.wr) (wAddr Sp (st + 8 * u)) 16 := by
    obtain ⟨r, hr, hc⟩ := hin _ j0; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have r1 : InRegions (s.rd ++ s.wr) (wAddr Sp (st + 8 * u + len)) 16 := by
    obtain ⟨r, hr, hc⟩ := hin _ j1; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have w0 := hin _ j0
  have w1 := hin _ j1
  rw [vbody, List.append_assoc, List.append_assoc, WP.block_append_iff]
  vrunm [hdx, a1, r0, r1]
  rw [WP.block_append_iff]
  have hx := lanes_load hS j0
  have hy := lanes_load hS j1
  refine WP.mono (hbf _ ((hc.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _)
    (fun e => (blk G len k st (8 * u))[st + 8 * u + e]!) (fun e => (blk G len k st (8 * u))[st + 8 * u + len + e]!)
    (fun _ => zeta k) (by rw [xmm_setXmm, xmm_setXmm]; exact hx) (by rw [xmm_setXmm]; exact hy)
    (by rw [xmm_setXmm, xmm_setXmm]; exact hz)) fun s2 ⟨l0, l3, o2⟩ => ?_
  have c2 := o2.consts ((hc.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _) (by decide)
    (by decide)
  have g2 : s2.gpr = s.gpr := o2.gpr
  have m2 : s2.mem = s.mem := o2.mem
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨o2.rd, o2.wr⟩
  have x2 : s2.mxcsr = s.mxcsr := o2.mxcsr
  have z2 : s2.xmm .xmm13 = s.xmm .xmm13 := by rw [o2.xmm _ (by decide), xmm_setXmm, xmm_setXmm]; rfl
  vrunm [g2, m2, e2.1, e2.2, hdx, a1, w0, w1, x2]
  refine ⟨?_, ?_, ?_, ⟨c2.q, c2.qinv⟩, z2, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · refine s16_write2 hS j0 j1 (by omega) l0 l3 fun i hi => ?_
    rw [show 8 * (u + 1) = 8 * u + 8 by omega, hblk.add, hblk.get _ _ _ _ _ hl (by omega)
      (by rw [n_eq]; omega) _ (by rw [n_eq]; exact hi)]
    by_cases c1 : st + 8 * u ≤ i ∧ i < st + 8 * u + 8
    · rw [ite_eq_left_of_eq_true _ _ (eq_true c1), ite_eq_left_of_eq_true _ _ (eq_true c1),
        show st + 8 * u + (i - (st + 8 * u)) = i by omega,
        show st + 8 * u + len + (i - (st + 8 * u)) = i + len by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false c1), ite_eq_right_of_eq_false _ _ (eq_false c1)]
      by_cases c2 : st + 8 * u + len ≤ i ∧ i < st + 8 * u + len + 8
      · rw [ite_eq_left_of_eq_true _ _ (eq_true c2), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
          show st + 8 * u + (i - (st + 8 * u + len)) = i - len by omega,
          show st + 8 * u + len + (i - (st + 8 * u + len)) = i by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false c2), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · rw [show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, wAddr_add,
      show st + 8 * u + 8 = st + 8 * (u + 1) by omega]
  · exact frame_write2 (Frame.refl _ _) j0 j1 _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

theorem vblock_ok {sP : Addr} {len st kz : Nat} (h8 : 8 ≤ len) (hl8 : len % 8 = 0) (hl : len ≤ 128)
    (hs : st + 2 * len ≤ 256) (hkz : kz < 128) (dz : BitVec 32) {G : Poly} {s : State} (hc : VConsts s)
    (hdx : s.gpr .rdx = wAddr (spW sP) st) (h8r : s.gpr .r8 = wAddr sP kz) (hS : S16 s.mem (spW sP) G)
    (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vblk bf len dz) s fun s' => S16 s'.mem (spW sP) (blk G len kz st len) ∧
      s'.gpr .rdx = wAddr (spW sP) (st + 2 * len) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
      s'.gpr .rax = s.gpr .rax - 1 ∧ s'.zf = some (s.gpr .rax - 1 == 0) ∧ BInv sP s s' := by
  -- the zeta
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (vzeta_ok 0 (k := kz) (fun j _ => by rw [sel_zero]; omega) h8r
    (tab_in (List.mem_append_right _ hw) (by omega)) hT) fun s1 ⟨z1, o1⟩ => ?_
  have g1 : s1.gpr = s.gpr := o1.gpr
  refine WP.mono (Q := fun (s2 : State) => s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
      GOnly [.r8] s1 s2)
    (by vrunm [g1]; gonly)
    fun s2 ⟨h82, o2⟩ => ?_
  have c2 := o2.consts (o1.consts hc (by decide) (by decide))
  have z2 : ZLanes (s2.xmm .xmm13) (fun _ => zeta kz) := by
    rw [o2.xmm]; intro i hi; rw [z1 i hi]; dsimp only; rw [sel_zero, Nat.add_zero]
  have dx2 : s2.gpr .rdx = wAddr (spW sP) st := by rw [o2.keep.gpr (by decide), g1, hdx]
  have hw2 : pR sP ∈ s2.wr := by rw [o2.keep.2.2, o1.wr]; exact hw
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  refine WP.seq (WP.mono (wp_rcxLoop (N := len / 8) (by omega) (by omega)
    (fun u w => S16 w.mem (spW sP) (blk G len kz st (8 * u)) ∧ w.gpr .rdx = wAddr (spW sP) (st + 8 * u) ∧
      VConsts w ∧ w.xmm .xmm13 = s2.xmm .xmm13 ∧ Keep [.rcx, .rdx] s2 w ∧ Frame [sR (spW sP)] s2.mem w.mem ∧
      w.mxcsr = s2.mxcsr)
    (fun w o hc => ⟨by rw [hblk.zero, o.mem, m2]; exact hS, by rw [o.keep.gpr (by decide), dx2]; rfl,
      o.consts c2, by rw [o.xmm], o.keep.mono (by simp), by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun u hu w ⟨hS', hdx', hc', hz', hk', hf', hx'⟩ => WP.mono (vstep hbf hblk (by omega) hs (by
        have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hl8); omega) hc' (by rw [hz']; exact z2) hdx' hS'
        (fun j hj => sp_in (by rw [hk'.2.2]; exact hw2) hj))
      fun w' ⟨hS'', hdx'', hf'', hc'', hz'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', by rw [hz'', hz'], (hk'.trans hk'').mono (by simp), hf'.trans hf'', by rw [hx'', hx']⟩,
          hcx, hzf⟩)) fun w ⟨hS3, hdx3, hc3, hz3, hk3, hf3, hx3⟩ => ?_)
  rw [show 8 * (len / 8) = len from Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hl8)] at hS3 hdx3
  have hax : w.gpr .rax = s.gpr .rax := by rw [hk3.gpr (by decide), o2.keep.gpr (by decide), g1]
  have h8w : w.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [hk3.gpr (by decide), h82]
  vrunm [hdx3, sx_ofNat (show 2 * len < 2 ^ 31 by omega), hax, h8w]
  refine ⟨hS3, by rw [wAddr_add, show st + len + len = st + 2 * len by omega], ?_⟩
  have k1 : Keep [.r8, .rcx, .rdx, .rax] s w :=
    (Keep.trans (⟨fun r _ => by rw [g1], o1.rd, o1.wr⟩ : Keep [] s s1) (o2.keep.trans hk3)).mono (by simp)
  refine ⟨⟨fun r hr => ?_, k1.2.1, k1.2.2⟩, by rw [← m2]; exact hf3,
    ⟨by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact hc3.q,
      by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact hc3.qinv⟩,
    by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [hx3, o2.mxcsr, o1.mxcsr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
  exact k1.gpr (by simp [hr])

/-! ## A layer -/

theorem vlay_ok {sP : Addr} {len k : Nat} (hlen : len ∈ [8, 16, 32, 64, 128]) (dz : BitVec 32)
    (zi : Nat → Nat) (hz0 : zi 0 = k) (hzi : ∀ c < 128 / len, zi c < 128)
    (hstep : ∀ c < 128 / len, wAddr sP (zi c) + BitVec.signExtend 64 dz = wAddr sP (zi (c + 1)))
    {F : Poly} {s : State} (hc : VConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay bf len k dz) s fun s' => S16 s'.mem (spW sP) (layF blk F len zi (128 / len)) ∧
      BInv sP s s' := by
  have hl : 8 ≤ len ∧ len % 8 = 0 ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
      128 / len ≤ 16 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h8, hl8, hl128, hcov, hpos, h16⟩ := hl
  have hk : k < 128 := hz0 ▸ hzi 0 hpos
  refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .rdx = spW sP ∧ w.gpr .r8 = wAddr sP k ∧
      w.gpr .rax = BitVec.ofNat 64 (128 / len) ∧ GOnly [.rdx, .r8, .rax] s w)
    (by
      simp only [leaR, oS]
      vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), sx_ofNat (show 2 * k < 2 ^ 31 by omega), hsi]
      refine ⟨?_, by gonly⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega) fun w ⟨hdx, h8r, hax, o⟩ => ?_)
  have hw' : pR sP ∈ w.wr := by rw [o.keep.2.2]; exact hw
  refine WP.mono (wp_countdown (cnt := .rax) (N := 128 / len) (by omega) hpos
    (fun c u => S16 u.mem (spW sP) (layF blk F len zi c) ∧ u.gpr .rdx = wAddr (spW sP) (2 * len * c) ∧
      u.gpr .r8 = wAddr sP (zi c) ∧ BInv sP w u ∧ T16 u.mem sP)
    (fun c hc u ⟨hS', hdx', h8', hb', hT'⟩ _ => ?_) (fun u h => h)
    ⟨by rw [o.mem]; exact hS, by rw [hdx, wAddr, Nat.mul_zero, Nat.mul_zero, add_ofNat_zero],
      by rw [h8r, hz0], ⟨Keep.refl _ _, Frame.refl _ _, o.consts hc, rfl⟩, by rw [o.mem]; exact hT⟩ hax)
    fun u ⟨hS', _, _, hb', _⟩ => ⟨hS', ⟨(o.keep.trans hb'.keep).mono (by simp),
      by rw [← o.mem]; exact hb'.frame, hb'.consts, by rw [hb'.mxcsr, o.mxcsr]⟩⟩
  have hs : 2 * len * c + 2 * len ≤ 256 := by
    have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this; omega
  refine WP.mono (vblock_ok hbf hblk h8 hl8 hl128 hs (hzi c hc) dz hb'.consts hdx' h8' hS' hT'
    (by rw [hb'.keep.2.2]; exact hw')) fun u' ⟨hS'', hdx'', h8'', hax'', hzf'', hb''⟩ =>
      ⟨⟨by rw [layF, foldl_range_succ]; exact hS'', by rw [hdx'', Nat.mul_succ],
        by rw [h8'', h8', hstep c hc], hb'.trans hb'', hT'.frame hb''.frame⟩, hax'', hzf''⟩

end

end VG.Proof.MlKem.X86_64
