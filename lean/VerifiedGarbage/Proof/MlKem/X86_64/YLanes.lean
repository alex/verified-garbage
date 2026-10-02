import VerifiedGarbage.Proof.MlKem.X86_64.VLay
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Impl.MlKem.X86_64.Avx

/-!
# ML-KEM on x86-64: coefficients in the lanes of AVX2 registers

The AVX2 code does to each 128-bit lane what the SSE2 code does to a register
(`toY`, `Impl/MlKem/X86_64/Avx.lean`), so the proofs of the SSE2 code hold of
each lane (`ylanes`, from `WP.lanes`): what they say of `xmm r` in `s.proj l`
they say of lane `l` of `ymm r` in `s`. `YOnly rs` is `XOnly rs` for both
lanes, and `YConsts` is `VConsts` for both lanes; `yld_ok` is a 256-bit load,
`yconsts_ok` the constants.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- Only the vector registers `rs` changed, in either lane. -/
structure YOnly (rs : List XReg) (s s' : State) : Prop extends XKeep s s' where
  lane : ∀ r ∉ rs, ∀ l < 2, s'.lane r l = s.lane r l

theorem YOnly.trans {rs rs' : List XReg} {s₁ s₂ s₃ : State} (h₁ : YOnly rs s₁ s₂) (h₂ : YOnly rs' s₂ s₃) :
    YOnly (rs ++ rs') s₁ s₃ :=
  { toXKeep := h₁.toXKeep.trans h₂.toXKeep
    lane := fun r hr l hl => by
      rw [List.mem_append, not_or] at hr
      rw [h₂.lane r hr.2 l hl, h₁.lane r hr.1 l hl] }

theorem YOnly.mono {rs rs' : List XReg} {s s' : State} (h : YOnly rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    YOnly rs' s s' := { toXKeep := h.toXKeep, lane := fun r hr => h.lane r fun h' => hr (hs r h') }

theorem YOnly.refl (rs : List XReg) (s : State) : YOnly rs s s :=
  { toXKeep := XKeep.refl s, lane := fun _ _ _ _ => rfl }

/-- `q` and `q⁻¹` in both lanes of `ymm15` and `ymm14`. -/
def YConsts (s : State) : Prop := ∀ l < 2, VConsts (s.proj l)

theorem YOnly.consts {rs : List XReg} {s s' : State} (h : YOnly rs s s') (hc : YConsts s)
    (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : YConsts s' := fun l hl =>
  ⟨by rw [State.proj_xmm, h.lane _ h15 l hl]; exact (hc l hl).q,
    by rw [State.proj_xmm, h.lane _ h14 l hl]; exact (hc l hl).qinv⟩

/-- A block of AVX2 code that does to each lane what an SSE2 block does. -/
theorem ylanes {vs ss : List Instr} (h : laneSseBlock vs = some ss) {rs : List XReg} {s : State}
    {P : Nat → State → Prop} (hq : ∀ l < 2, WP isa (.block ss) (s.proj l) fun t => P l t ∧ XOnly rs (s.proj l) t) :
    WP isa (.block vs) s fun s' => (∀ l < 2, P l (s'.proj l)) ∧ YOnly rs s s' :=
  WP.mono (WP.lanes h hq) fun _ ⟨k, q⟩ =>
    ⟨fun l hl => (q l hl).1, ⟨⟨k.gpr, k.mem, k.rd, k.wr, k.mxcsr⟩, fun r hr l hl => (q l hl).2.xmm r hr⟩⟩

theorem lane_readW256 (m : Mem) (a : Addr) {l : Nat} (hl : l < 2) :
    (if l = 0 then (m.readW a 256).extractLsb' 0 128 else (m.readW a 256).extractLsb' 128 128) =
      m.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  rcases lane01 hl with rfl | rfl
  · exact readW_extract m a (k := 0) (n := 16) (by decide)
  · exact readW_extract m a (k := 16) (n := 16) (by decide)

@[simp] theorem State.setMem_ymm (s : State) (m : Mem) (r : XReg) : (s.setMem m).ymm r = s.ymm r := by
  cases s; rfl

@[simp] theorem State.setMem_setMem (s : State) (m m' : Mem) : (s.setMem m).setMem m' = s.setMem m' := by
  cases s; rfl

theorem lane_setReg (s : State) (d : Reg) (v : BitVec 64) (r : XReg) (l : Nat) :
    (s.setReg d v).lane r l = s.lane r l := rfl

theorem lane_setFlags (s : State) (a b c d : Option Bool) (r : XReg) (l : Nat) :
    (s.setFlags a b c d).lane r l = s.lane r l := rfl

/-- The lanes after general-purpose instructions and stores. -/
theorem lanes_gpr {s s' : State} (h : ∀ r l, s'.lane r l = s.lane r l) {rs : List XReg} {s₀ : State}
    (o : YOnly rs s₀ s) (hc : YConsts s₀) (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : YConsts s' :=
  fun l hl => ⟨by rw [State.proj_xmm, h]; exact (o.consts hc h14 h15 l hl).q,
    by rw [State.proj_xmm, h]; exact (o.consts hc h14 h15 l hl).qinv⟩

/-- A 256-bit load. -/
theorem yld_ok {s : State} {p : Reg} {off : Nat} {d : XReg}
    (h : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 off) 32) :
    WP isa (.block [.vmovdquLoad .l256 d (at_ p off)]) s fun s' =>
      (∀ l < 2, s'.lane d l = s.mem.readW (s.gpr p + BitVec.ofNat 64 off + BitVec.ofNat 64 (16 * l)) 128) ∧
        YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load256, ea_at, h, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl, lane_readW256 _ _ hl]
  · rw [State.lane_setV256, ifn (by simpa using hr)]

/-- `yconst r v` (`v` in each doubleword of `ymm r`). -/
theorem yconst_ok (r : XReg) (v : BitVec 32) (s : State) :
    WP isa (.block (yconst r v)) s fun s' => (∀ l < 2, s'.lane r l = ofDwords v v v v) ∧
      Keep [.rax] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr ∧ ∀ r' ≠ r, ∀ l < 2, s'.lane r' l = s.lane r' l := by
  apply WP.of_runBlock
  simp only [yconst, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, readSrc32, Option.map_some,
    Option.some.injEq, exists_eq_left', State.setReg32]
  refine ⟨fun l hl => ?_, ⟨fun r' hr' => ?_, rfl, rfl⟩, rfl, rfl, fun r' hr' l hl => ?_⟩
  · rw [State.lane_setV256, ifp rfl]
    have : dword (((s.setReg .rax (v.setWidth 64)).setV .l128 r ((0 : BitVec 64) ++
        (s.setReg .rax (v.setWidth 64)).gpr .rax) 0).xmm r) 0 = v := by
      rw [RegUpd.xmm_setV, ifp rfl, RegUpd.gpr_setReg_self]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [dword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
      rw [BitVec.getLsbD_append, ifp (by omega), BitVec.getLsbD_setWidth]
      simp [show i < 64 by omega]
    rcases lane01 hl with rfl | rfl <;> simp only [ite_true, ite_false, this, Nat.one_ne_zero]
  · simp only [List.mem_singleton] at hr'
    rw [RegUpd.gpr_setV, RegUpd.gpr_setV, RegUpd.gpr_setReg_of_ne _ _ hr']
  · rw [State.lane_setV256, ifn hr', State.lane_setV128, ifn hr']
    rfl

/-- `rcxLoop N body`, with the vector registers in full: the body runs `N`
times, from a state that the `mov` of the count changed in `rcx` only. -/
theorem wp_rcxLoopY {body : List Instr} {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 31) (Inv : Nat → State → Prop)
    {s₀ : State} (h0 : ∀ s, GOnly [.rcx] s₀ s → s.ymmHi = s₀.ymmHi → s.gpr .rcx = BitVec.ofNat 64 N → Inv 0 s)
    (hbody : ∀ i < N, ∀ s, Inv i s →
      WP isa (.block (body ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' => Inv (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) :
    WP isa (rcxLoop N body) s₀ (Inv N) := by
  refine WP.seq (WP.mono (Q := fun (s : State) => GOnly [.rcx] s₀ s ∧ s.ymmHi = s₀.ymmHi ∧
      s.gpr .rcx = BitVec.ofNat 64 N)
    (by vrunm [RegUpd.ymmHi_setReg]; exact ⟨by gonly, by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega⟩) fun s ⟨o, hy, hc⟩ => ?_)
  exact wp_countdown (by omega) hN Inv (fun i hi s hI _ => hbody i hi s hI) (fun _ h => h) (h0 s o hy hc) hc

end VG.Proof.MlKem.X86_64
