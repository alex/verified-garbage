import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Final
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.StoreY
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Store
import VerifiedGarbage.Proof.Poly1305.X86_64.Variant

/-!
# Poly1305 on x86-64 with AVX-512: `vg_poly1305_blocks_avx512`

The whole function: with fewer than 40 blocks it calls
`vg_poly1305_blocks_avx2`; otherwise it absorbs the blocks eight at a time
(see `Impl/Poly1305/X86_64/Avx512.lean`), and calls `vg_poly1305_blocks` for
the last `n mod 8`.

As for AVX2 (`Avx2/Blocks.lean`), the vector code computes the right numbers
only if the accumulator on entry is below `2¹⁹⁴`, which holds whenever the
state represents a message: each block's effect on the vector registers is
established under that assumption, and its execution without it (`guard`).
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Spec.Poly1305 (P leNum bytesAt accumulate Repr clamp)
open VG.Proof.Poly1305.X86_64.Avx2 (guard and_exec TailPre Post tail_ok done_ok cs_ne mxMem mxMem_read
  mxMem_frame mxMem_mx mx_hi mx_bits H2_lt bytesAt_frame vec vec_trans vec_gpr vec_keep repr_frame ret_stk
  ret_frame consts_ok mxcsrIn_ok mxcsrOut_ok storeH_ok finish_ok ext5)

/-- The contract the proof is written against: `blocksX86_64`'s, with the
16 bytes of stack below the return address that its calls use. -/
def blocksAvx512X86_64 : Contract X86_64.isa := Proof.Poly1305.blocksStack 16

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [sR (st s₀)]
  st_bl : (sR (st s₀)).Disjoint (blR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint (sR (st s₀))
  stk_bl : (below (s₀.gpr .rsp) 16).Disjoint (blR s₀)
  nowrap : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : blocksAvx512X86_64.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem below8_16 (sp : Addr) : Region.Sub (below sp 8) (below sp 16) := below_sub (by omega) (by omega)

theorem APre.avx2 {s₀ : State} (hp : APre s₀) : Avx2.APre s₀ :=
  ⟨hp.rd, hp.wr, hp.st_bl, hp.ret_st, hp.stk_st.sub_left (below8_16 _), hp.stk_bl.sub_left (below8_16 _),
    hp.nowrap⟩

/-! ## The call of `vg_poly1305_blocks_avx2` -/

theorem avx2_depth : Impl.Poly1305.X86_64.Avx2.blocksAvx2.depth = 1 := by lit_decide

theorem ret_below16 (s₀ : State) : (retR s₀).Disjoint (below (s₀.gpr .rsp) 16) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 16) (d := 16) (n := 8) (k := 16)
    (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

theorem avx2_ok {s₀ : State} (hp : APre s₀) {s : State} (h : TailPre s₀ 0 s) : WP isa avx2 s (Post s₀) := by
  have hn := hp.avx2.bpre.nb_lt
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.keep .rsp (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  have hdx : (s.gpr .rdx).toNat = nb s₀ := by rw [h.rdx, Nat.sub_zero, toNat_ofNat_lt (by omega)]
  have hsi : s.gpr .rsi = bp s₀ := by rw [h.rsi]; simp [blkAddr]
  have stS : (below (s.gpr .rsp) 16).Disjoint (sR (st s₀)) := by rw [hsp]; exact hp.stk_st
  have stB : (below (s.gpr .rsp) 16).Disjoint (blR s₀) := by rw [hsp]; exact hp.stk_bl
  refine WP.call_mx (k := Avx2.blocksAvx2X86_64) Avx2.blocksAvx2_ok BlocksImpl.avx2_nosp
    (by rw [avx2_depth]; decide) (rd := [blR s₀]) (wr := [sR (st s₀)]) ?_ ?_ ?_ ?_
  · simp only [Avx2.blocksAvx2X86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp), h.rdi, hsi, hdx]
    exact ⟨trivial, trivial, hp.st_bl, stS.sub_left (below8_16 _), stS.sub_left (below_callee _ 8),
      stB.sub_left (below_callee _ 8), hp.nowrap⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨blR s₀, by simp, 0, by simp, show 0 + 16 * nb s₀ ≤ 16 * nb s₀ by omega⟩
    · exact ⟨sR (st s₀), by simp, 0, by simp, show 0 + 128 ≤ 128 by omega⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨sR (st s₀), by simp, 0, by simp, show 0 + 128 ≤ 128 by omega⟩
  · intro s' _ _ hcs hf _ ⟨s₂, hm₂, _, hpost⟩ hmx
    rw [avx2_depth] at hf
    have Fce : Frame [below (s₀.gpr .rsp) 16] s.mem s.callEntry.mem := by
      rw [State.callEntry_mem, hsp]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))
    simp only [Avx2.blocksAvx2X86_64, Proof.Poly1305.blocksX86_64, State.withRegions_gpr,
      State.withRegions_mem, hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
      hne _ (by decide : Reg.rdx ≠ .rsp), h.rdi, hsi, hdx, hm₂] at hpost
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact h.keep r hr, ?_, by rw [hmx]; exact h.mxcsr⟩,
      fun key msg hr => ?_⟩
    · refine (hf.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
      · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact hp.ret_st
        · rw [hsp]; exact ret_below16 s₀
      · exact h.frame.readW (Region.contains_self _ _) (ret_frame hp.avx2) (by decide)
    · have r₁ := repr_frame Fce (by simpa using hp.stk_st.symm) (h.repr key msg hr)
      have x := hpost key _ r₁
      have tb : bytesAt s.callEntry.mem (bp s₀) (16 * nb s₀) = bytesAt s₀.mem (bp s₀) (16 * nb s₀) := by
        rw [bytesAt_frame Fce (by simpa using hp.stk_bl.symm) (by omega),
          bytesAt_frame h.frame (fun r hr => ?_) (by omega)]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_bl.symm.sub_right (Region.sub_prefix (by omega))
        · exact hp.st_bl.symm.sub_right (sub_sR _ (by omega))
      rw [tb, blks_zero, List.append_nil] at x
      exact x

/-! ## Registers, memory and the vector state -/

theorem qz_of {s s' : State} (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) (hz : s'.zmmHi = s.zmmHi)
    (r : XReg) (k : Nat) : qz s' r k = qz s r k := by
  unfold qz State.zlane State.lane; rw [hx, hy, hz]

theorem LaneInv.of_qz {R X : Nat} {s s' : State} (h : ∀ r k, qz s' r k = qz s r k)
    (hI : LaneInv R X s) : LaneInv R X s' := by
  have e₁ : hv s' = hv s := by funext k i; simp only [hv, h]
  have e₂ : yl s' = yl s := by funext k i; simp only [yl, h]
  have e₃ : yh s' = yh s := by funext k i; simp only [yh, h]
  obtain ⟨⟨lo, hi, lob, hib⟩, hb, acc⟩ := hI
  refine ⟨⟨by rw [e₂]; exact lo, by rw [e₃]; exact hi, by rw [e₂]; exact lob, by rw [e₃]; exact hib⟩,
    by rw [e₁]; exact hb, ?_⟩
  simp only [wsum, hval, e₁] at acc ⊢; exact acc

theorem rcx_val (x : BitVec 64) (h : 8 ≤ x.toNat) : (x >>> 3) - 1 = BitVec.ofNat 64 (x.toNat / 8 - 1) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem and7_toNat (x : BitVec 64) : (x &&& 7).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem LaneInv.of_hy {R X : Nat} {s s' : State}
    (h : ∀ i < 5, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k ∧ qz s' (yreg i) k = qz s (yreg i) k)
    (hI : LaneInv R X s) : LaneInv R X s' := by
  have eh : ∀ k < 8, hv s' k = hv s k := fun k hk => ext5 (fun _ h => hv_ge _ _ h) (fun _ h => hv_ge _ _ h)
    fun i hi => by simp only [hv, (h i hi k hk).1]
  refine ⟨hI.y.of_y fun i hi k hk => (h i hi k hk).2, fun k hk i hi => by rw [eh k hk]; exact hI.hb k hk i hi, ?_⟩
  have e : wsum R s' = wsum R s := by
    simp only [wsum, hval, eh 0 (by decide), eh 1 (by decide), eh 2 (by decide), eh 3 (by decide),
      eh 4 (by decide), eh 5 (by decide), eh 6 (by decide), eh 7 (by decide)]
  rw [e]; exact hI.acc

theorem mr_congr {s s' : State} (hg : s'.gpr .rdi = s.gpr .rdi) (hm : s'.mem = s.mem) : mr s' = mr s := by
  funext i; simp only [mr, envOf, hg, hm]

theorem MemY.of_mem {R : Nat} {s s' : State} (h : MemY R s) (hg : s'.gpr .rdi = s.gpr .rdi)
    (hm : s'.mem = s.mem) : MemY R s' :=
  ⟨h.m.of_mem hg hm, by rw [mr_congr hg hm]; exact h.val⟩

/-! ## The prologue -/

/-- What the prologue leaves in memory for the rest: nothing written outside
the working space `wR`, and MXCSR (bits 31:16 cleared) at byte 120. -/
structure MemOK (s₀ : State) (m₁ : Mem) : Prop where
  frame : Frame [wR (st s₀)] s₀.mem m₁
  mx : m₁.readW (off (st s₀) 120) 32 = s₀.mxcsr &&& 0xffff

/-- Before group `j` of eight blocks (the loop's invariant), with the memory
`m₁` the prologue leaves. -/
structure LInv (s₀ : State) (m₁ : Mem) (j : Nat) (s : State) : Prop where
  lt : j < nb s₀ / 8
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = blkAddr s₀ (8 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 8 - 1 - j)
  rdx : s.gpr .rdx = s₀.gpr .rdx
  r8 : s.gpr .r8 = 0x3ffffff
  r9 : s.gpr .r9 = 0x1000000
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁
  acc : H2 s₀ < 4 → LaneInv (Rn s₀) (Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ (8 * j))) s ∧
    MemY (Rn s₀) s

theorem powers_split : Impl.Poly1305.X86_64.Avx2.consts ++ Impl.Poly1305.X86_64.Avx2.mxcsrIn ++ powers ++
    Impl.Poly1305.X86_64.Avx2.loadHw ++ loadH ++ storeY ++
    ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr) =
    Impl.Poly1305.X86_64.Avx2.consts ++ (Impl.Poly1305.X86_64.Avx2.mxcsrIn ++ (loadRg ++ (powersV ++
      (Impl.Poly1305.X86_64.Avx2.loadHw ++ (loadH ++ (storeY ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr))))))) := by
  simp only [powers_eq, List.append_assoc]

theorem pro_ok {s₀ : State} (hp : APre s₀) (hbig : 40 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VKeep s₀ s) :
    WP isa (.block (Impl.Poly1305.X86_64.Avx2.consts ++ Impl.Poly1305.X86_64.Avx2.mxcsrIn ++ powers ++
      Impl.Poly1305.X86_64.Avx2.loadHw ++ loadH ++ storeY ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr))) s
      (fun s' => MemOK s₀ s'.mem ∧ LInv s₀ s'.mem 0 s') := by
  have hp2 := hp.avx2
  rw [powers_split]
  refine WP.block_append (WP.mono (consts_ok s) fun s₁ ⟨r8₁, r9₁, g₁, m₁, k₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = st s₀ := by rw [g₁ _ (by decide) (by decide), hg]
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, hk.wr]
  refine WP.block_append (WP.mono (mxcsrIn_ok s₁ (hp2.inW wr₁ rdi₁ (by omega)) (hp2.inW wr₁ rdi₁ (by omega))
    (hp2.inRW wr₁ rdi₁ (by omega)) (hp2.inRW wr₁ rdi₁ (by omega)))
    fun s₂ ⟨g₂, m₂, _, x₂, y₂, rd₂, wr₂⟩ => ?_)
  have rdi₂ : s₂.gpr .rdi = st s₀ := by rw [g₂ _ (by decide), rdi₁]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have mm₂ : s₂.mem = mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [m₂, m₁, hm, rdi₁, k₁.mxcsr, hk.mxcsr]
  refine WP.block_append (WP.mono (loadRg_ok s₂ (hp2.inRW wr₂' rdi₂ (by omega)) (hp2.inRW wr₂' rdi₂ (by omega)))
    fun s₃ ⟨r10₃, r11₃, ax₃, g₃, m₃, k₃⟩ => ?_)
  have r8₃ : s₃.gpr .r8 = 0x3ffffff := by rw [g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), r8₁]
  refine WP.block_append (WP.mono (powersV_ok r8₃ ax₃) fun s₄ ⟨v₄, Y₄⟩ => ?_)
  obtain ⟨vg₄, vm₄, vrd₄, vwr₄, -⟩ := vec_keep v₄
  have rdi₄ : s₄.gpr .rdi = st s₀ := by rw [vg₄, g₃ _ (by decide) (by decide) (by decide), rdi₂]
  have wr₄ : s₄.wr = s₀.wr := by rw [vwr₄, k₃.wr, wr₂']
  refine WP.block_append (WP.mono (loadHw_ok s₄ (hp2.inRW wr₄ rdi₄ (by omega)) (hp2.inRW wr₄ rdi₄ (by omega))
    (hp2.inRW wr₄ rdi₄ (by omega))) fun s₅ ⟨a₅, b₅, c₅, g₅, m₅, k₅⟩ => ?_)
  have mm₄ : s₄.mem = mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [vm₄, m₃, mm₂]
  have ax₅ : (s₅.gpr .rax).toNat = H2 s₀ := by
    rw [c₅, rdi₄, mm₄, mxMem_read _ _ _ (by omega)]
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₅ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) ldS_eq) fun _ h => h.eq)
    fun hA => loadH_ok (by rw [ax₅]; exact hA)) fun s₆ ⟨v₆, L₆⟩ => ?_)
  obtain ⟨vg₆, vm₆, vrd₆, vwr₆, -⟩ := vec_keep v₆
  have rdi₆ : s₆.gpr .rdi = st s₀ := by rw [vg₆, g₅ _ (by decide) (by decide) (by decide), rdi₄]
  have wr₆ : s₆.wr = s₀.wr := by rw [vwr₆, k₅.wr, wr₄]
  refine WP.block_append (WP.mono (storeY_ok s₆ (fun _ _ h => hp2.inW wr₆ rdi₆ h)
    (fun _ _ h => hp2.inW wr₆ rdi₆ h)) fun s₇ Y₇ => ?_)
  refine WP.mono (rcx_ok s₇) fun s₈ ⟨c₈, g₈, m₈, k₈⟩ => ?_
  have gk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
      s₈.gpr r = s₀.gpr r := by
    intro r a c e f g h
    rw [g₈ r c, Y₇.gpr, vg₆, g₅ r a g h, vg₄, g₃ r a g h, g₂ r a, g₁ r e f, hg]
  have r8₆ : s₆.gpr .r8 = 0x3ffffff := by rw [vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄, r8₃]
  have r9₆ : s₆.gpr .r9 = 0x1000000 := by
    rw [vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄, g₃ _ (by decide) (by decide) (by decide),
      g₂ _ (by decide), r9₁]
  have mm₆ : s₆.mem = mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [vm₆, m₅, mm₄]
  have hb' := hbig
  simp only [nb] at hb'
  have F₇ : Frame [wR (st s₀)] s₆.mem s₇.mem := by rw [← rdi₆]; exact Y₇.frame
  refine ⟨⟨(mxMem_frame s₀.mem (st s₀) s₀.mxcsr).trans (by rw [m₈, ← mm₆]; exact F₇),
    by rw [m₈, ← rdi₆, Y₇.mx, rdi₆, mm₆, mxMem_mx]⟩, ?_⟩
  refine ⟨by simp only [nb]; omega, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, rfl, fun hA => ?_⟩
  · exact gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [blkAddr]
  · rw [c₈, Y₇.gpr, vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄,
      g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide) (by decide), hg,
      rcx_val _ (by omega), nb, Nat.sub_zero]
  · exact gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [g₈ _ (by decide), Y₇.gpr, r8₆]
  · rw [g₈ _ (by decide), Y₇.gpr, r9₆]
  · obtain ⟨a, c, -, -, e, f, g, h⟩ := cs_ne hr
    exact gk r a c e f g h
  · rw [k₈.rd, Y₇.rd, vrd₆, k₅.rd, vrd₄, k₃.rd, rd₂, k₁.rd, hk.rd]
  · rw [k₈.wr, Y₇.wr, wr₆]
  · -- The accumulator in quadword 0, `Y` from `powers`, and its limbs in memory.
    have L := L₆ hA
    have rN₃ : Avx2.rN s₃ = Rn s₀ := by
      simp only [Avx2.rN, Rn, R0, R1]
      rw [r10₃, r11₃, rdi₂, mm₂, mxMem_read _ _ _ (by omega), mxMem_read _ _ _ (by omega)]
    have hN₅ : Avx2.hN s₅ = A0 s₀ := by
      simp only [Avx2.hN, A0]
      rw [a₅, b₅, c₅, rdi₄, mm₄, mxMem_read _ _ _ (by omega), mxMem_read _ _ _ (by omega),
        mxMem_read _ _ _ (by omega), leNum_acc]
    have Y₆ : YInv s₆ (Rn s₀) := by
      rw [← rN₃]
      exact (Y₄.of_y fun i hi k hk => k₅.qz_eq _ _).of_y L.y
    have rdi₈ : s₈.gpr .rdi = s₇.gpr .rdi := g₈ _ (by decide)
    have M₇ : MemM s₇ := by
      refine ⟨fun i hi => by rw [Y₇.r i hi]; exact Y₆.lob 0 (by decide) i hi, fun i h₁ hi => ?_,
        by rw [Y₇.mask, r8₆]; rfl, by rw [Y₇.pad, r9₆]; rfl⟩
      rw [Y₇.five i h₁ hi, Y₇.r i hi]
      have := Y₆.lob 0 (by decide) i hi
      omega
    have V₇ : Limbs26.val (mr s₇) = Limbs26.val (yl s₆ 0) := by
      simp only [Limbs26.val, Y₇.r 0 (by decide), Y₇.r 1 (by decide), Y₇.r 2 (by decide),
        Y₇.r 3 (by decide), Y₇.r 4 (by decide)]
    refine ⟨LaneInv.of_qz (fun r k => k₈.qz_eq r k) (LaneInv.of_hy Y₇.hy
      ⟨Y₆, fun k hk i hi => by have := L.hb k hk i hi; omega, ?_⟩),
      MemY.of_mem ⟨M₇, by rw [V₇]; exact Y₆.lo 0 (by decide)⟩ rdi₈ m₈⟩
    simp only [Nat.mul_zero, blks_zero, Poly1305.absorbAll_nil, wsum]
    rw [L.h 0 (by decide), L.h 1 (by decide), L.h 2 (by decide), L.h 3 (by decide), L.h 4 (by decide),
      L.h 5 (by decide), L.h 6 (by decide), L.h 7 (by decide), hN₅]
    simp (config := {decide := true}) only [Poly1305.lanes8, ite_true, ite_false, Nat.mul_zero,
      Nat.add_zero]
    exact Nat.ModEq.refl _

/-! ## The loop -/

theorem grp_sub {s₀ : State} {j : Nat} (hj : 8 * j + 8 ≤ nb s₀) :
    Region.Sub ⟨blkAddr s₀ (8 * j), 128⟩ (blR s₀) :=
  Offset.sub_base _ (by omega)

theorem ctx_of {s₀ : State} (hp : APre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hdi : s.gpr .rdi = st s₀) {j : Nat} (hsi : s.gpr .rsi = blkAddr s₀ (8 * j)) (hj : 8 * j + 8 ≤ nb s₀) :
    Ctx s := by
  refine ⟨fun i hi => ?_, fun d _ h => hp.avx2.inRW hwr hdi (by omega)⟩
  have := hp.avx2.bpre.nb_lt
  refine ⟨blR s₀, by rw [hrd, hp.rd]; simp, ?_⟩
  rw [hsi, blkAddr, Offset.add_add]
  exact Offset.contains_base _ (by rcases hi with rfl | rfl <;> omega) (by rcases hi with rfl | rfl <;> omega)

/-- The group of blocks at `rsi`, from the memory the prologue leaves. -/
theorem grp_bytes {s₀ : State} (hp : APre s₀) {m₁ : Mem} (hm : MemOK s₀ m₁) {j : Nat}
    (hj : 8 * j + 8 ≤ nb s₀) :
    bytesAt m₁ (blkAddr s₀ (8 * j)) 128 = bytesAt s₀.mem (blkAddr s₀ (8 * j)) 128 :=
  bytesAt_frame hm.frame (by
    simpa using (hp.st_bl.symm.sub_left (grp_sub hj)).sub_right (sub_sR _ (by omega))) (by omega)

theorem absorb_grp (s₀ : State) (R X : Nat) (j : Nat) :
    Poly1305.absorbAll R (Poly1305.absorbAll R X (blks s₀ (8 * j))) (bytesAt s₀.mem (blkAddr s₀ (8 * j)) 128) =
      Poly1305.absorbAll R X (blks s₀ (8 * (j + 1))) := by
  rw [← Poly1305.absorbAll_append (by simp only [blks, Poly1305.length_bytesAt]; omega)]
  simp only [blks, blkAddr]
  rw [← Poly1305.bytesAt_add, show 16 * (8 * j) + 128 = 16 * (8 * (j + 1)) by omega]

theorem add128 (s₀ : State) (j : Nat) : blkAddr s₀ (8 * j) + 128 = blkAddr s₀ (8 * (j + 1)) := by
  simp only [blkAddr]
  rw [show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, Offset.add_add,
    show 16 * (8 * j) + 128 = 16 * (8 * (j + 1)) by omega]

theorem group_body_ok {s₀ : State} (hp : APre s₀) {m₁ : Mem} (hm : MemOK s₀ m₁) {j : Nat}
    (hj : j + 1 < nb s₀ / 8) {s : State} (h : LInv s₀ m₁ j s) :
    WP isa groupBody s fun s' => LInv s₀ m₁ (j + 1) s' ∧ s'.zf = some (decide (nb s₀ / 8 - 1 - j = 1)) := by
  have hb := hp.avx2.bpre.nb_lt
  have hc := ctx_of hp h.rd h.wr h.rdi h.rsi (j := j) (by omega)
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s s' = s') (A := H2 s₀ < 4) ?_
    fun hA => group_ok hc (h.acc hA).2 (h.acc hA).1) fun s₁ ⟨v₁, G₁⟩ => ?_)
  · exact WP.block_append (WP.mono (run_ok (fun _ => hc) addMS_eq) fun s₁ h₁ =>
      WP.mono (run_ok (fun _ => hc.of_vec h₁.eq) mulMS_eq) fun s₂ h₂ => vec_trans h₁.eq h₂.eq)
  obtain ⟨vg₁, vm₁, vrd₁, vwr₁, -⟩ := vec_keep v₁
  refine WP.mono (adv_ok s₁) fun s₂ ⟨si₂, cx₂, zf₂, g₂, m₂, k₂⟩ => ?_
  have gk : ∀ r, r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s.gpr r := fun r a b => by rw [g₂ r a b, vg₁]
  have hcx : s₁.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 8 - 1 - j) := by rw [vg₁, h.rcx]
  refine ⟨⟨hj, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, fun hA => ?_⟩, ?_⟩
  · rw [gk _ (by decide) (by decide), h.rdi]
  · rw [si₂, vg₁, h.rsi, add128]
  · rw [cx₂, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega),
      Nat.sub_sub]
  · rw [gk _ (by decide) (by decide), h.rdx]
  · rw [gk _ (by decide) (by decide), h.r8]
  · rw [gk _ (by decide) (by decide), h.r9]
  · obtain ⟨-, c, -, e, -⟩ := cs_ne hr
    rw [gk r e c, h.keep r hr]
  · rw [k₂.rd, vrd₁, h.rd]
  · rw [k₂.wr, vwr₁, h.wr]
  · rw [m₂, vm₁, h.mem]
  · have G := (G₁ hA).2
    rw [h.mem, h.rsi, grp_bytes hp hm (by omega), absorb_grp] at G
    exact ⟨LaneInv.of_qz (fun r k => k₂.qz_eq r k) G,
      (h.acc hA).2.of_mem (by rw [gk _ (by decide) (by decide)]) (by rw [m₂, vm₁])⟩
  · rw [zf₂, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]

theorem loop_ok {s₀ : State} (hp : APre s₀) {m₁ : Mem} (hm : MemOK s₀ m₁) (hG : 1 < nb s₀ / 8) {s : State}
    (h₀ : LInv s₀ m₁ 0 s) : WP isa (.loop groupBody .ne) s (LInv s₀ m₁ (nb s₀ / 8 - 1)) := by
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = nb s₀ / 8 - 1 - j ∧ j < nb s₀ / 8 - 1 ∧ LInv s₀ m₁ j s
  have hstep : ∀ n s, Inv n s → WP isa groupBody s (fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ m₁ (nb s₀ / 8 - 1) s') ∨
      (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨j, rfl, hj, hI⟩
    refine WP.mono (group_body_ok hp hm (by omega) hI) fun s' ⟨h', hz⟩ => ?_
    by_cases e : nb s₀ / 8 - 1 - j = 1
    · have e' : j + 1 = nb s₀ / 8 - 1 := by omega
      exact .inl ⟨by simp [eval, hz, e], e' ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, e], nb s₀ / 8 - 1 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep _ s ⟨0, rfl, by omega, h₀⟩

/-! ## The epilogue -/

theorem epi_eq : Impl.Poly1305.X86_64.Avx2.consts2 ++ last ++ sumLanes ++ Impl.Poly1305.X86_64.Avx2.fullCarry ++
    Impl.Poly1305.X86_64.Avx2.reduce ++ Impl.Poly1305.X86_64.Avx2.mxcsrOut ++
    Impl.Poly1305.X86_64.Avx2.storeH ++
    ([.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr) =
    Impl.Poly1305.X86_64.Avx2.consts2 ++ (last ++ (sumLanes ++ ((Impl.Poly1305.X86_64.Avx2.fullCarry ++
      Impl.Poly1305.X86_64.Avx2.reduce) ++ (Impl.Poly1305.X86_64.Avx2.mxcsrOut ++
      (Impl.Poly1305.X86_64.Avx2.storeH ++
        ([.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr)))))) := by
  simp only [List.append_assoc]

theorem epi_ok {s₀ : State} (hp : APre s₀) {M₁ : Mem} (hm : MemOK s₀ M₁) {s : State}
    (h : LInv s₀ M₁ (nb s₀ / 8 - 1) s) :
    WP isa (.block (Impl.Poly1305.X86_64.Avx2.consts2 ++ last ++ sumLanes ++
      Impl.Poly1305.X86_64.Avx2.fullCarry ++ Impl.Poly1305.X86_64.Avx2.reduce ++
      Impl.Poly1305.X86_64.Avx2.mxcsrOut ++ Impl.Poly1305.X86_64.Avx2.storeH ++
      ([.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr))) s
      (TailPre s₀ (8 * (nb s₀ / 8))) := by
  have hp2 := hp.avx2
  have hb := hp2.bpre.nb_lt
  have hlt := h.lt
  have h1 : 1 ≤ nb s₀ / 8 := by omega
  rw [epi_eq]
  refine WP.block_append (WP.mono (consts2_ok s) fun s₁ ⟨ax₁, r10₁, g₁, m₁, k₁⟩ => ?_)
  have gk₁ : ∀ r, r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r := g₁
  have hc : Ctx s₁ := ctx_of hp (by rw [k₁.rd, h.rd]) (by rw [k₁.wr, h.wr])
    (by rw [gk₁ _ (by decide) (by decide), h.rdi]) (by rw [gk₁ _ (by decide) (by decide), h.rsi]) (by omega)
  have r8₁ : s₁.gpr .r8 = 0x3ffffff := by rw [gk₁ _ (by decide) (by decide), h.r8]
  have r9₁ : s₁.gpr .r9 = 0x1000000 := by rw [gk₁ _ (by decide) (by decide), h.r9]
  -- The last group.
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₁ s' = s') (A := H2 s₀ < 4) ?_
    fun hA => last_ok r8₁ r9₁ hc ((h.acc hA).1.of_qz fun r k => k₁.qz_eq r k)) fun s₂ ⟨v₂, L₂⟩ => ?_)
  · rw [last_eq]
    exact WP.block_append (WP.mono (run_ok (fun _ => hc) addS_eq) fun _ h₁ =>
      WP.block_append (WP.mono (run_ok (fun h => by cases h) shS_eq) fun _ h₂ =>
        WP.mono (run_ok (fun h => by cases h) mulS_eq) fun _ h₃ => vec_trans h₁.eq (vec_trans h₂.eq h₃.eq)))
  obtain ⟨vg₂, vm₂, vrd₂, vwr₂, vx₂⟩ := vec_keep v₂
  have r8₂ : s₂.gpr .r8 = 0x3ffffff := by rw [vg₂, r8₁]
  -- The sum of the quadwords.
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₂ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) smS_eq) fun _ h => h.eq)
    fun hA => sumLanes_ok r8₂ (L₂ hA).2.1) fun s₃ ⟨v₃, S₃⟩ => ?_)
  obtain ⟨vg₃, vm₃, vrd₃, vwr₃, vx₃⟩ := vec_keep v₃
  -- `h mod p`, on quadword 0 (`vg_poly1305_blocks_avx2`'s code).
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₃ s' = s') (A := H2 s₀ < 4)
    (WP.mono (Avx2.run_ok (fun h => by cases h) Avx2.fnS_eq) fun _ h => h.eq)
    fun hA => finish_ok (by rw [vg₃, r8₂]) (by rw [vg₃, vg₂, ax₁]) (by rw [vg₃, vg₂, r10₁])
      (fun k hk i hi => by rw [hv_avx2 _ hk]; exact (S₃ hA).hball k (by omega) i hi)
      (fun i hi => by rw [hv_avx2 _ (by decide)]; exact (S₃ hA).hb i hi)) fun s₄ ⟨v₄, F₄⟩ => ?_)
  obtain ⟨vg₄, vm₄, vrd₄, vwr₄, vx₄⟩ := vec_keep v₄
  have g₄ : ∀ r, r ≠ .rax → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r a b => by
    rw [vg₄, vg₃, vg₂, gk₁ r a b]
  have rdi₄ : s₄.gpr .rdi = st s₀ := by rw [g₄ _ (by decide) (by decide), h.rdi]
  have wr₄ : s₄.wr = s₀.wr := by rw [vwr₄, vwr₃, vwr₂, k₁.wr, h.wr]
  have mm₄ : s₄.mem = M₁ := by rw [vm₄, vm₃, vm₂, m₁, h.mem]
  -- MXCSR restored.
  refine WP.block_append (WP.mono (mxcsrOut_ok s₄ (hp2.inRW wr₄ rdi₄ (by omega))
    (by rw [mm₄, rdi₄, hm.mx]; exact mx_hi _)) fun s₅ ⟨g₅, m₅, mx₅, x₅, y₅, rd₅, wr₅⟩ => ?_)
  have rdi₅ : s₅.gpr .rdi = st s₀ := by rw [g₅, rdi₄]
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄]
  -- The accumulator stored.
  refine WP.block_append (WP.mono (storeH_ok fun d hd => hp2.inW wr₅' rdi₅ (by omega)) fun s₆ sp₆ => ?_)
  refine WP.mono (fin3_ok s₆) fun s₇ ⟨si₇, dx₇, g₇, m₇, mx₇, rd₇, wr₇⟩ => ?_
  have g₆ : ∀ r, r ≠ .rax → r ≠ .r10 → s₆.gpr r = s.gpr r := fun r a b => by
    rw [sp₆.gpr, g₅, g₄ r a b]
  have hmx : s₇.mxcsr = s₀.mxcsr &&& 0xffff := by
    rw [mx₇, sp₆.mxcsr, mx₅, mm₄, rdi₄, hm.mx]
  have hframe : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₇.mem := by
    rw [m₇]
    refine (hm.frame.mono (by simp)).trans ?_
    rw [← mm₄, ← m₅]
    exact sp₆.frame.mono (by rw [rdi₅]; simp)
  refine ⟨by omega, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, hframe, by rw [hmx, mx_bits], fun key msg hr => ?_⟩
  · rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide), h.rdi]
  · rw [si₇, g₆ _ (by decide) (by decide), h.rsi, add128, Nat.sub_add_cancel h1]
  · rw [dx₇, g₆ _ (by decide) (by decide), h.rdx]
    apply BitVec.eq_of_toNat_eq
    rw [and7_toNat, toNat_ofNat_lt (by omega)]
    simp only [nb]
    omega
  · obtain ⟨a, -, c, d, -, -, g, -⟩ := cs_ne hr
    rw [g₇ r d c, g₆ r a g, h.keep r hr]
  · rw [rd₇, sp₆.rd, rd₅, vrd₄, vrd₃, vrd₂, k₁.rd, h.rd]
  · rw [wr₇, sp₆.wr, wr₅']
  · -- The accumulator represents the blocks absorbed.
    have hA := H2_lt hr
    obtain ⟨hlen, hkey, hacc⟩ := hr
    have hkey' : bytesAt s₀.mem (off (st s₀) 24) 32 = key := by rw [off_24]; exact hkey
    have hA0 : accumulate (Rn s₀) msg = A0 s₀ := by rw [A0, hacc, ← hkey', clamp_key]
    have hlt : A0 s₀ < P := by rw [← hA0]; exact Poly1305.accumulate_lt _ _
    have L := (L₂ hA).2.2
    have S := (S₃ hA).h
    obtain ⟨-, F, Fb⟩ := F₄ hA
    rw [gk₁ _ (by decide) (by decide), h.rsi, m₁, h.mem, grp_bytes hp hm (by omega), absorb_grp,
      Nat.sub_add_cancel h1] at L
    have e₅ : Avx2.h0 s₅ = Avx2.hv s₄ 0 := by
      funext i; simp only [Avx2.h0, Avx2.hv, Avx2.qw_of x₅ y₅]
    have e₃ : Limbs26.val (Avx2.hv s₃ 0) = hval s₃ 0 :=
      congrArg Limbs26.val (funext fun i => hv_avx2 _ (by decide) i)
    obtain ⟨W, -, -⟩ := Limbs26.words_val (o := Avx2.h0 s₅) (by rw [e₅]; exact Fb)
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega
    · rw [← off_24, key_frame hframe, hkey']
    · rw [leNum_acc, m₇, ← rdi₅, sp₆.w0, sp₆.w1, sp₆.w2, W, e₅, F, e₃, ← hkey', clamp_key,
        Poly1305.accumulate_append hlen]
      change _ = Poly1305.absorbAll (Rn s₀) (accumulate (Rn s₀) msg) _
      rw [hA0, (S.trans L : _ ≡ _ [MOD P]),
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)]

/-! ## The whole function -/

theorem body_ok {s₀ : State} (hp : APre s₀) (hbig : 40 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VKeep s₀ s) :
    WP isa body s (TailPre s₀ (8 * (nb s₀ / 8))) :=
  WP.seq (WP.mono (pro_ok hp hbig hg hm hk) fun _ h₁ =>
    WP.seq (WP.mono (loop_ok hp h₁.1 (by omega) h₁.2) fun _ h₂ => epi_ok hp h₁.1 h₂))

theorem correct {s₀ : State} (hp : APre s₀) : WP isa blocksAvx512 s₀ (Post s₀) := by
  have hb := hp.avx2.bpre.nb_lt
  refine WP.seq (WP.mono (cmp_ok s₀) fun s₁ ⟨g₁, m₁, k₁, cf₁⟩ => ?_)
  refine WP.ite (decide (nb s₀ < 40)) (by simp [eval, cf₁]) (fun hlt => ?_) (fun hge => ?_)
  · refine avx2_ok hp ⟨by omega, by rw [g₁], by rw [g₁]; simp [blkAddr], ?_,
      fun r _ => by rw [g₁], k₁.rd, k₁.wr, by rw [m₁]; exact Frame.refl _ _, by rw [k₁.mxcsr],
      fun key msg hr => by rw [m₁, blks_zero, List.append_nil]; exact hr⟩
    rw [g₁, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.seq (WP.mono (body_ok hp hge g₁ m₁ k₁) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (Avx2.test_ok s₂) fun s₃ ⟨z₃, g₃, m₃, mx₃, rd₃, wr₃⟩ => ?_)
    have h₃ := h₂.congr g₃ m₃ mx₃ rd₃ wr₃
    refine WP.ite (s₃.gpr .rdx &&& s₃.gpr .rdx == 0) (by simp [eval, z₃, g₃]) (fun h => ?_)
      (fun _ => tail_ok hp.avx2 h₃)
    have e : 8 * (nb s₀ / 8) = nb s₀ := by
      have := h₃.rdx
      simp only [BitVec.and_self, beq_iff_eq] at h
      rw [h] at this
      have := congrArg BitVec.toNat this
      rw [toNat_ofNat_lt (by omega)] at this
      rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
      simp only [nb] at this ⊢
      omega
    exact WP.block_nil (M := isa) (done_ok hp.avx2 (e ▸ h₃))

theorem blocksAvx512_ok (s : State) (hs : blocksAvx512X86_64.pre s) :
    ∃ t s', Exec isa blocksAvx512 s t s' ∧ abiPreserved s s' ∧ blocksAvx512X86_64.post s s' :=
  correct (APre.of s hs)

/-! ## Constant time -/

theorem blocksAvx512_ct : ConstantTime isa blocksAvx512X86_64.pre blocksAvx512X86_64.pub blocksAvx512 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨⟨h1, h2, h3⟩, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem blocksAvx512_verified :
    Verified X86_64.target blocksAvx512 (Spec.Poly1305.blocksContract X86_64.abi 16) :=
  Verified.of_correct blocksAvx512_ok blocksAvx512_ct (by
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig, blocksAvx512X86_64,
      Proof.Poly1305.blocksStack, Proof.Poly1305.blocksX86_64, X86_64.abi, X86_64.argRegs]
      [Avx2.sat] using Avx2.sat)

end VG.Proof.Poly1305.X86_64.Avx512
