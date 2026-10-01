import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Store
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Group
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Gpr
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# Poly1305 on x86-64 with AVX2: `vg_poly1305_blocks_avx2`

Untrusted: everything here is checked by Lean. The whole function: with
fewer than 16 blocks, or for the last `n mod 4`, it calls
`vg_poly1305_blocks`; otherwise it absorbs the blocks four at a time (see
`Impl/Poly1305/X86_64/Avx2.lean`).

The vector code computes the right numbers only if the accumulator on entry
is below `2¹⁹⁴` (its top word below 4), which holds whenever the state
represents a message; it runs, and leaves everything but the vector
registers as the proofs of its blocks say, whatever the state holds. So each
block's effect on the vector registers is established under that
assumption (`hA`), and its execution without it (`guard`).
-/

open VG.Proof.Poly1305.Limbs64

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Spec.Poly1305 (P leNum bytesAt accumulate Repr clamp)

/-- The contract the proof is written against: `blocksX86_64`'s, with the
8 bytes of stack below the return address that its call uses. -/
def blocksAvx2X86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let blocks : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧ ret.Disjoint state ∧
      stack.Disjoint state ∧ stack.Disjoint blocks ∧
      (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post := Proof.Poly1305.blocksX86_64.post
  pub s₁ s₂ := Proof.Poly1305.blocksX86_64.pub s₁ s₂ ∧ s₁.gpr .rsp = s₂.gpr .rsp

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [sR (st s₀)]
  st_bl : (sR (st s₀)).Disjoint (blR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))
  stk_st : (below (s₀.gpr .rsp) 8).Disjoint (sR (st s₀))
  stk_bl : (below (s₀.gpr .rsp) 8).Disjoint (blR s₀)
  nowrap : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : blocksAvx2X86_64.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem APre.bpre {s₀ : State} (hp : APre s₀) : BPre s₀ :=
  ⟨hp.rd, hp.wr, hp.st_bl, hp.ret_st, hp.nowrap⟩

/-- What the function guarantees. -/
def Post (s₀ s : State) : Prop := abiPreserved s₀ s ∧ Proof.Poly1305.blocksX86_64.post s₀ s

/-! ## Executions that establish more under an assumption -/

/-- An execution that satisfies `R`, and `Q` if `A` holds. -/
theorem guard {c : Prog isa} {s : State} {R Q : State → Prop} {A : Prop} (hR : WP isa c s R)
    (hQ : A → WP isa c s Q) : WP isa c s fun s' => R s' ∧ (A → Q s') := by
  obtain ⟨t, s', he, hr⟩ := hR
  refine ⟨t, s', he, hr, fun ha => ?_⟩
  obtain ⟨t', s'', he', hq⟩ := hQ ha
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact hq

/-- A property of every execution. -/
theorem and_exec {c : Prog isa} {s : State} {Q R : State → Prop} (h : WP isa c s Q)
    (hR : ∀ t s', Exec isa c s t s' → R s') : WP isa c s fun s' => Q s' ∧ R s' := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, hR t s' he⟩

/-! ## Memory outside the state -/

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A state represents the same message after writes outside it. -/
theorem repr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (sR p).Disjoint r) {key msg : List Byte} (h : Repr m p key msg) :
    Repr m' p key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  have s₁ : Region.Sub ⟨p + 24, 32⟩ (sR p) := by rw [← off_24]; exact sub_sR p (by omega)
  have s₂ : Region.Sub ⟨p, 24⟩ (sR p) := by
    have := sub_sR p (d := 0) (n := 24) (by omega)
    rwa [off_eq, BitVec.add_zero] at this
  refine ⟨h1, ?_, ?_⟩
  · rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left s₁) (by omega), h2]
  · rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left s₂) (by omega), h3]

theorem blks_split (s₀ : State) {i : Nat} (hi : i ≤ nb s₀) :
    blks s₀ i ++ bytesAt s₀.mem (blkAddr s₀ i) (16 * (nb s₀ - i)) = blks s₀ (nb s₀) := by
  simp only [blks, blkAddr]
  rw [← Poly1305.bytesAt_add, show 16 * i + 16 * (nb s₀ - i) = 16 * nb s₀ by omega]

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (below (s₀.gpr .rsp) 8) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8)
    (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

/-! ## The call of `vg_poly1305_blocks` -/

/-- Before the call of `vg_poly1305_blocks` for the blocks from block `i`
on (or the return, if there are none). -/
structure TailPre (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i ≤ nb s₀
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [hR (st s₀), wR (st s₀)] s₀.mem s.mem
  mxcsr : s.mxcsr.extractLsb' 6 10 = s₀.mxcsr.extractLsb' 6 10
  repr : ∀ key msg, Repr s₀.mem (st s₀) key msg → Repr s.mem (st s₀) key (msg ++ blks s₀ i)

theorem ret_frame {s₀ : State} (hp : APre s₀) : ∀ r ∈ [hR (st s₀), wR (st s₀)], (retR s₀).Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hp.ret_st.sub_right (Region.sub_prefix (by omega))
  · exact hp.ret_st.sub_right (sub_sR _ (by omega))

theorem done_ok {s₀ : State} (hp : APre s₀) {s : State} (h : TailPre s₀ (nb s₀) s) : Post s₀ s :=
  ⟨⟨h.keep, h.frame.readW (Region.contains_self _ _) (ret_frame hp) (by decide), h.mxcsr⟩,
    fun key msg hr => h.repr key msg hr⟩

theorem blocks_keeps :
    ((instrs Impl.Poly1305.X86_64.blocks).all fun i => !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem blocks_nosp : NoSp Impl.Poly1305.X86_64.blocks := by
  intro i hi
  simpa using List.all_eq_true.mp blocks_keeps i hi

theorem blocks_depth : Impl.Poly1305.X86_64.blocks.depth = 0 := by lit_decide

theorem blocks_mx : ((instrs Impl.Poly1305.X86_64.blocks).all fun i => !loadsMxcsr i) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem scalar_mxcsr {s s' : State} {t : List Leak} (h : Exec isa scalar s t s') : s'.mxcsr = s.mxcsr :=
  Exec.mxcsr (c := scalar) (fun i hi => by simpa using List.all_eq_true.mp blocks_mx i hi) h

theorem tail_ok {s₀ : State} (hp : APre s₀) {i : Nat} {s : State} (h : TailPre s₀ i s) :
    WP isa scalar s (Post s₀) := by
  have hn := hp.bpre.nb_lt
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.keep .rsp (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  have hdx : (s.gpr .rdx).toNat = nb s₀ - i := by rw [h.rdx, toNat_ofNat_lt (by omega)]
  have hle := h.le
  have tsub : Region.Sub ⟨blkAddr s₀ i, 16 * (nb s₀ - i)⟩ (blR s₀) :=
    Offset.sub_base _ (by omega)
  have stkR : below (s.gpr .rsp) 8 = below (s₀.gpr .rsp) 8 := by rw [hsp]
  refine WP.mono (and_exec (Q := fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.blocksX86_64.post s₀ s')
    ?_ fun _ _ he => scalar_mxcsr he) fun s' ⟨⟨g, p⟩, m⟩ => ⟨⟨g.1, g.2, by rw [m]; exact h.mxcsr⟩, p⟩
  refine WP.call (k := Proof.Poly1305.blocksX86_64) blocks_ok blocks_nosp (by rw [blocks_depth]; decide)
    (rd := [⟨blkAddr s₀ i, 16 * (nb s₀ - i)⟩]) (wr := [sR (st s₀)]) ?_ ?_ ?_ ?_
  · simp only [Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, hdx, hsp]
    refine ⟨trivial, trivial, hp.st_bl.sub_right tsub, hp.stk_st, ?_⟩
    have := hp.nowrap
    simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨blR s₀, by simp, 16 * i, rfl, show 16 * i + 16 * (nb s₀ - i) ≤ 16 * nb s₀ by omega⟩
    · exact ⟨sR (st s₀), by simp, 0, by simp, show 0 + 128 ≤ 128 by omega⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨sR (st s₀), by simp, 0, by simp, show 0 + 128 ≤ 128 by omega⟩
  · intro s' _ _ hcs hf _ ⟨s₂, hm₂, _, hpost⟩
    rw [blocks_depth, stkR] at hf
    have Fce : Frame [below (s₀.gpr .rsp) 8] s.mem s.callEntry.mem := by
      rw [State.callEntry_mem, hsp]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))
    simp only [Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
      hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
      hne _ (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, hdx, hm₂] at hpost
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact h.keep r hr, ?_⟩, fun key msg hr => ?_⟩
    · refine (hf.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
      · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact hp.ret_st
        · exact ret_stk s₀
      · exact h.frame.readW (Region.contains_self _ _) (ret_frame hp) (by decide)
    · have r₁ := repr_frame Fce (by simpa using hp.stk_st.symm) (h.repr key msg hr)
      have x := hpost key _ r₁
      have tb : bytesAt s.callEntry.mem (blkAddr s₀ i) (16 * (nb s₀ - i)) =
          bytesAt s₀.mem (blkAddr s₀ i) (16 * (nb s₀ - i)) := by
        rw [bytesAt_frame Fce (by simpa using (hp.stk_bl.sub_right tsub).symm) (by omega),
          bytesAt_frame h.frame (fun r hr => ?_) (by omega)]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hp.st_bl.symm.sub_left tsub).sub_right (Region.sub_prefix (by omega))
        · exact (hp.st_bl.symm.sub_left tsub).sub_right (sub_sR _ (by omega))
      rw [tb, List.append_assoc, blks_split s₀ hle] at x
      exact x

/-! ## Registers, memory and the vector state -/

theorem cs_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧
    r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem qw_of {s s' : State} (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) (r : XReg) (k : Nat) :
    qw s' r k = qw s r k := by
  unfold qw State.lane; rw [hx, hy]

theorem LaneInv.of_qw {R X : Nat} {s s' : State} (h : ∀ r k, qw s' r k = qw s r k)
    (hI : LaneInv R X s) : LaneInv R X s' := by
  have e₁ : hv s' = hv s := by funext k i; simp only [hv, h]
  have e₂ : yl s' = yl s := by funext k i; simp only [yl, h]
  have e₃ : yh s' = yh s := by funext k i; simp only [yh, h]
  obtain ⟨⟨lo, hi, lob, hib⟩, hb, acc⟩ := hI
  exact ⟨⟨by rw [e₂]; exact lo, by rw [e₃]; exact hi, by rw [e₂]; exact lob, by rw [e₃]; exact hib⟩,
    by rw [e₁]; exact hb, by rw [e₁]; exact acc⟩

theorem APre.inW {s₀ : State} (hp : APre s₀) {s : State} (hw : s.wr = s₀.wr)
    (hr : s.gpr .rdi = st s₀) {d n : Nat} (h : d + n ≤ 128) : InRegions s.wr (off (s.gpr .rdi) d) n :=
  ⟨sR (st s₀), by rw [hw, hp.wr]; exact List.mem_singleton_self _, by rw [hr]; exact contains_off h (by omega)⟩

theorem APre.inRW {s₀ : State} (hp : APre s₀) {s : State} (hw : s.wr = s₀.wr)
    (hr : s.gpr .rdi = st s₀) {d n : Nat} (h : d + n ≤ 128) :
    InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) n :=
  let ⟨r, hm, hc⟩ := hp.inW hw hr h
  ⟨r, List.mem_append_right _ hm, hc⟩

theorem rd_off (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (hk : w / 8 ≤ 16) (h : d + 8 ≤ e ∨ e + w / 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (sep_off p hd he (by omega) hk h) (by decide)

theorem mxMem_read (m : Mem) (p : Addr) (x : BitVec 32) {d : Nat} (hd : d + 8 ≤ 120) :
    (mxMem m p x).readW (off p d) 64 = m.readW (off p d) 64 := by
  simp only [mxMem]
  rw [rd_off _ _ _ (by omega) (by omega) (by decide) (by omega),
    rd_off _ _ _ (by omega) (by omega) (by decide) (by omega),
    rd_off _ _ _ (by omega) (by omega) (by decide) (by omega)]

theorem mxMem_frame (m : Mem) (p : Addr) (x : BitVec 32) : Frame [wR p] m (mxMem m p x) :=
  (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (wR_contains p (d := 120) (n := 4) (by omega)
    (by omega))).writeW (List.mem_singleton_self _) _ (wR_contains p (d := 120) (n := 4) (by omega)
    (by omega))).writeW (List.mem_singleton_self _) _ (wR_contains p (d := 124) (n := 4) (by omega)
    (by omega))

theorem mxMem_mx (m : Mem) (p : Addr) (x : BitVec 32) :
    (mxMem m p x).readW (off p 120) 32 = x &&& 0xffff := by
  simp only [mxMem]
  rw [Mem.readW_writeW_sep (sep_off p (by omega) (by omega) (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self32]

theorem mx_hi (x : BitVec 32) : (x &&& 0xffff).extractLsb' 16 16 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_and]
  rw [show (0xffff : BitVec 32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, show (0 : BitVec 16).toNat = 0 from rfl]
  have := x.isLt
  omega

theorem mx_bits (x : BitVec 32) : (x &&& 0xffff).extractLsb' 6 10 = x.extractLsb' 6 10 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_and]
  rw [show (0xffff : BitVec 32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem rcx_val (x : BitVec 64) (h : 4 ≤ x.toNat) : (x >>> 2) - 1 = BitVec.ofNat 64 (x.toNat / 4 - 1) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (1 : BitVec 64).toNat = 1 from rfl]
  omega

/-- The top word of the accumulator of a state that represents a message. -/
theorem H2_lt {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) : H2 s₀ < 4 := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2, leNum_acc] at this
  simp only [H2, P] at this ⊢
  omega

/-! ## The prologue -/

/-- Before group `j` of four blocks (the loop's invariant). -/
structure LInv (s₀ : State) (j : Nat) (s : State) : Prop where
  lt : j < nb s₀ / 4
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = blkAddr s₀ (4 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 4 - 1 - j)
  rdx : s.gpr .rdx = s₀.gpr .rdx
  r8 : s.gpr .r8 = 0x3ffffff
  r9 : s.gpr .r9 = 0x1000000
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = mxMem s₀.mem (st s₀) s₀.mxcsr
  acc : H2 s₀ < 4 → LaneInv (Rn s₀) (Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ (4 * j))) s

theorem pro_ok {s₀ : State} (hp : APre s₀) (hbig : 16 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VKeep s₀ s) :
    WP isa (.block (consts ++ mxcsrIn ++ powers ++ loadHw ++ loadH ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 2, .alu .sub .rcx (.imm 1)] : List Instr))) s
      (LInv s₀ 0) := by
  rw [powers_split]
  refine WP.block_append (WP.mono (consts_ok s) fun s₁ ⟨r8₁, r9₁, g₁, m₁, k₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = st s₀ := by rw [g₁ _ (by decide) (by decide), hg]
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, hk.wr]
  refine WP.block_append (WP.mono (mxcsrIn_ok s₁ (hp.inW wr₁ rdi₁ (by omega)) (hp.inW wr₁ rdi₁ (by omega))
    (hp.inRW wr₁ rdi₁ (by omega)) (hp.inRW wr₁ rdi₁ (by omega)))
    fun s₂ ⟨g₂, m₂, _, x₂, y₂, rd₂, wr₂⟩ => ?_)
  have rdi₂ : s₂.gpr .rdi = st s₀ := by rw [g₂ _ (by decide), rdi₁]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have mm₂ : s₂.mem = mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [m₂, m₁, hm, rdi₁, k₁.mxcsr, hk.mxcsr]
  refine WP.block_append (WP.mono (loadRg_ok s₂ (hp.inRW wr₂' rdi₂ (by omega)) (hp.inRW wr₂' rdi₂ (by omega)))
    fun s₃ ⟨r10₃, r11₃, g₃, m₃, k₃⟩ => ?_)
  have r8₃ : s₃.gpr .r8 = 0x3ffffff := by rw [g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), r8₁]
  refine WP.block_append (WP.mono (powersV_ok r8₃) fun s₄ ⟨v₄, Y₄⟩ => ?_)
  obtain ⟨vg₄, vm₄, vrd₄, vwr₄, -⟩ := vec_keep v₄
  have rdi₄ : s₄.gpr .rdi = st s₀ := by rw [vg₄, g₃ _ (by decide) (by decide) (by decide), rdi₂]
  have wr₄ : s₄.wr = s₀.wr := by rw [vwr₄, k₃.wr, wr₂']
  refine WP.block_append (WP.mono (loadHw_ok s₄ (hp.inRW wr₄ rdi₄ (by omega)) (hp.inRW wr₄ rdi₄ (by omega))
    (hp.inRW wr₄ rdi₄ (by omega))) fun s₅ ⟨a₅, b₅, c₅, g₅, m₅, k₅⟩ => ?_)
  have mm₄ : s₄.mem = mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [vm₄, m₃, mm₂]
  have ax₅ : (s₅.gpr .rax).toNat = H2 s₀ := by
    rw [c₅, rdi₄, mm₄, mxMem_read _ _ _ (by omega)]
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₅ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) ldS_eq) fun _ h => h.eq)
    fun hA => loadH_ok (by rw [ax₅]; exact hA)) fun s₆ ⟨v₆, L₆⟩ => ?_)
  obtain ⟨vg₆, vm₆, vrd₆, vwr₆, -⟩ := vec_keep v₆
  refine WP.mono (rcx_ok s₆) fun s₇ ⟨c₇, g₇, m₇, k₇⟩ => ?_
  have gk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
      s₇.gpr r = s₀.gpr r := by
    intro r a c e f g h
    rw [g₇ r c, vg₆, g₅ r a g h, vg₄, g₃ r a g h, g₂ r a, g₁ r e f, hg]
  have hq₇ : ∀ r k, qw s₇ r k = qw s₆ r k := fun r k => k₇.qw_eq r k
  have hb' := hbig
  simp only [nb] at hb'
  refine ⟨by simp only [nb]; omega, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, fun hA => ?_⟩
  · exact gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [blkAddr]
  · rw [c₇, vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄, g₃ _ (by decide) (by decide) (by decide),
      g₂ _ (by decide), g₁ _ (by decide) (by decide), hg, rcx_val _ (by omega), nb, Nat.sub_zero]
  · exact gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [g₇ _ (by decide), vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄,
      g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), r8₁]
  · rw [g₇ _ (by decide), vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄,
      g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), r9₁]
  · obtain ⟨a, c, -, -, e, f, g, h⟩ := cs_ne hr
    exact gk r a c e f g h
  · rw [k₇.rd, vrd₆, k₅.rd, vrd₄, k₃.rd, rd₂, k₁.rd, hk.rd]
  · rw [k₇.wr, vwr₆, k₅.wr, wr₄]
  · rw [m₇, vm₆, m₅, mm₄]
  · -- The accumulator in lane 0, `Y` from `powers`.
    have L := L₆ hA
    have rN₃ : rN s₃ = Rn s₀ := by
      simp only [rN, Rn, R0, R1]
      rw [r10₃, r11₃, rdi₂, mm₂, mxMem_read _ _ _ (by omega), mxMem_read _ _ _ (by omega)]
    have hN₅ : hN s₅ = A0 s₀ := by
      simp only [hN, A0]
      rw [a₅, b₅, c₅, rdi₄, mm₄, mxMem_read _ _ _ (by omega), mxMem_read _ _ _ (by omega),
        mxMem_read _ _ _ (by omega), leNum_acc]
    have Y₆ : YInv s₆ (Rn s₀) := by
      rw [← rN₃]
      exact (Y₄.of_y fun i hi k hk => k₅.qw_eq _ _).of_y L.y
    refine LaneInv.of_qw (fun r k => (hq₇ r k)) ⟨Y₆, fun k hk i hi => by have := L.hb k hk i hi; omega, ?_⟩
    simp only [Nat.mul_zero, blks_zero, Poly1305.absorbAll_nil]
    rw [L.h 0 (by decide), L.h 1 (by decide), L.h 2 (by decide), L.h 3 (by decide), hN₅]
    simp (config := {decide := true}) only [lanes, ite_true, ite_false, Nat.mul_zero, Nat.add_zero]
    exact Nat.ModEq.refl _

/-! ## The loop -/

theorem grp_sub {s₀ : State} {j : Nat} (hj : 4 * j + 4 ≤ nb s₀) :
    Region.Sub ⟨blkAddr s₀ (4 * j), 64⟩ (blR s₀) :=
  Offset.sub_base _ (by omega)

theorem ctx_of {s₀ : State} (hp : APre s₀) {s : State} (hrd : s.rd = s₀.rd) {j : Nat}
    (hsi : s.gpr .rsi = blkAddr s₀ (4 * j)) (hj : 4 * j + 4 ≤ nb s₀) : Ctx s := by
  intro i hi
  have := hp.bpre.nb_lt
  refine ⟨blR s₀, by rw [hrd, hp.rd]; simp, ?_⟩
  rw [hsi, blkAddr, Offset.add_add]
  exact Offset.contains_base _ (by rcases hi with rfl | rfl <;> omega) (by rcases hi with rfl | rfl <;> omega)

/-- The group of blocks at `rsi`, from the memory the prologue leaves. -/
theorem grp_bytes {s₀ : State} (hp : APre s₀) {j : Nat} (hj : 4 * j + 4 ≤ nb s₀) :
    bytesAt (mxMem s₀.mem (st s₀) s₀.mxcsr) (blkAddr s₀ (4 * j)) 64 = bytesAt s₀.mem (blkAddr s₀ (4 * j)) 64 :=
  bytesAt_frame (mxMem_frame _ _ _) (by
    simpa using (hp.st_bl.symm.sub_left (grp_sub hj)).sub_right (sub_sR _ (by omega))) (by omega)

theorem absorb_grp (s₀ : State) (R X : Nat) (j : Nat) :
    Poly1305.absorbAll R (Poly1305.absorbAll R X (blks s₀ (4 * j))) (bytesAt s₀.mem (blkAddr s₀ (4 * j)) 64) =
      Poly1305.absorbAll R X (blks s₀ (4 * (j + 1))) := by
  rw [← Poly1305.absorbAll_append (by simp only [blks, Poly1305.length_bytesAt]; omega)]
  simp only [blks, blkAddr]
  rw [← Poly1305.bytesAt_add, show 16 * (4 * j) + 64 = 16 * (4 * (j + 1)) by omega]

theorem add64 (s₀ : State) (j : Nat) : blkAddr s₀ (4 * j) + 64 = blkAddr s₀ (4 * (j + 1)) := by
  simp only [blkAddr]
  rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, Offset.add_add,
    show 16 * (4 * j) + 64 = 16 * (4 * (j + 1)) by omega]

theorem group_body_ok {s₀ : State} (hp : APre s₀) {j : Nat} (hj : j + 1 < nb s₀ / 4) {s : State}
    (h : LInv s₀ j s) :
    WP isa groupBody s fun s' => LInv s₀ (j + 1) s' ∧ s'.zf = some (decide (nb s₀ / 4 - 1 - j = 1)) := by
  have hb := hp.bpre.nb_lt
  have hc := ctx_of hp h.rd h.rsi (j := j) (by omega)
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s s' = s') (A := H2 s₀ < 4) ?_
    fun hA => group_ok h.r8 h.r9 hc (h.acc hA)) fun s₁ ⟨v₁, G₁⟩ => ?_)
  · exact WP.block_append (WP.mono (run_ok (fun _ => hc) addS_eq) fun s₁ h₁ =>
      WP.mono (run_ok (fun h => by cases h) mulS_eq) fun s₂ h₂ => vec_trans h₁.eq h₂.eq)
  obtain ⟨vg₁, vm₁, vrd₁, vwr₁, -⟩ := vec_keep v₁
  refine WP.mono (adv_ok s₁) fun s₂ ⟨si₂, cx₂, zf₂, g₂, m₂, k₂⟩ => ?_
  have gk : ∀ r, r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s.gpr r := fun r a b => by rw [g₂ r a b, vg₁]
  have hcx : s₁.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 4 - 1 - j) := by rw [vg₁, h.rcx]
  refine ⟨⟨hj, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, fun hA => ?_⟩, ?_⟩
  · rw [gk _ (by decide) (by decide), h.rdi]
  · rw [si₂, vg₁, h.rsi, add64]
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
    rw [h.mem, h.rsi, grp_bytes hp (by omega), absorb_grp] at G
    exact LaneInv.of_qw (fun r k => k₂.qw_eq r k) G
  · rw [zf₂, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]

theorem loop_ok {s₀ : State} (hp : APre s₀) (hG : 1 < nb s₀ / 4) {s : State} (h₀ : LInv s₀ 0 s) :
    WP isa (.loop groupBody .ne) s (LInv s₀ (nb s₀ / 4 - 1)) := by
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = nb s₀ / 4 - 1 - j ∧ j < nb s₀ / 4 - 1 ∧ LInv s₀ j s
  have hstep : ∀ n s, Inv n s → WP isa groupBody s (fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ (nb s₀ / 4 - 1) s') ∨
      (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨j, rfl, hj, hI⟩
    refine WP.mono (group_body_ok hp (by omega) hI) fun s' ⟨h', hz⟩ => ?_
    by_cases e : nb s₀ / 4 - 1 - j = 1
    · have e' : j + 1 = nb s₀ / 4 - 1 := by omega
      exact .inl ⟨by simp [eval, hz, e], e' ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, e], nb s₀ / 4 - 1 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep _ s ⟨0, rfl, by omega, h₀⟩

/-! ## The epilogue -/

theorem epi_eq : consts2 ++ last ++ sumLanes ++ fullCarry ++ reduce ++ mxcsrOut ++
    Impl.Poly1305.X86_64.Avx2.storeH ++
    ([.vop .vzeroupper, .alu .add .rsi (.imm 64), .alu .and .rdx (.imm 3)] : List Instr) =
    consts2 ++ (last ++ (sumLanes ++ ((fullCarry ++ reduce) ++ (mxcsrOut ++
      (Impl.Poly1305.X86_64.Avx2.storeH ++
        ([.vop .vzeroupper, .alu .add .rsi (.imm 64), .alu .and .rdx (.imm 3)] : List Instr)))))) := by
  simp only [List.append_assoc]

theorem epi_ok {s₀ : State} (hp : APre s₀) {s : State} (h : LInv s₀ (nb s₀ / 4 - 1) s) :
    WP isa (.block (consts2 ++ last ++ sumLanes ++ fullCarry ++ reduce ++ mxcsrOut ++
      Impl.Poly1305.X86_64.Avx2.storeH ++
      ([.vop .vzeroupper, .alu .add .rsi (.imm 64), .alu .and .rdx (.imm 3)] : List Instr))) s
      (TailPre s₀ (4 * (nb s₀ / 4))) := by
  have hb := hp.bpre.nb_lt
  have hlt := h.lt
  have h1 : 1 ≤ nb s₀ / 4 := by omega
  rw [epi_eq]
  refine WP.block_append (WP.mono (consts2_ok s) fun s₁ ⟨ax₁, r10₁, g₁, m₁, k₁⟩ => ?_)
  have gk₁ : ∀ r, r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r := g₁
  have hc : Ctx s₁ := ctx_of hp (by rw [k₁.rd, h.rd]) (by rw [gk₁ _ (by decide) (by decide), h.rsi])
    (by omega)
  have r8₁ : s₁.gpr .r8 = 0x3ffffff := by rw [gk₁ _ (by decide) (by decide), h.r8]
  have r9₁ : s₁.gpr .r9 = 0x1000000 := by rw [gk₁ _ (by decide) (by decide), h.r9]
  -- The last group.
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₁ s' = s') (A := H2 s₀ < 4) ?_
    fun hA => last_ok r8₁ r9₁ hc ((h.acc hA).of_qw fun r k => k₁.qw_eq r k)) fun s₂ ⟨v₂, L₂⟩ => ?_)
  · rw [last_eq]
    exact WP.block_append (WP.mono (run_ok (fun _ => hc) addS_eq) fun _ h₁ =>
      WP.block_append (WP.mono (run_ok (fun h => by cases h) shS_eq) fun _ h₂ =>
        WP.mono (run_ok (fun h => by cases h) mulS_eq) fun _ h₃ => vec_trans h₁.eq (vec_trans h₂.eq h₃.eq)))
  obtain ⟨vg₂, vm₂, vrd₂, vwr₂, vx₂⟩ := vec_keep v₂
  have r8₂ : s₂.gpr .r8 = 0x3ffffff := by rw [vg₂, r8₁]
  -- The sum of the lanes.
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₂ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) smS_eq) fun _ h => h.eq)
    fun hA => sumLanes_ok r8₂ (L₂ hA).2.1) fun s₃ ⟨v₃, S₃⟩ => ?_)
  obtain ⟨vg₃, vm₃, vrd₃, vwr₃, vx₃⟩ := vec_keep v₃
  -- `h mod p`.
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₃ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) fnS_eq) fun _ h => h.eq)
    fun hA => finish_ok (by rw [vg₃, r8₂]) (by rw [vg₃, vg₂, ax₁]) (by rw [vg₃, vg₂, r10₁])
      (S₃ hA).hball (S₃ hA).hb) fun s₄ ⟨v₄, F₄⟩ => ?_)
  obtain ⟨vg₄, vm₄, vrd₄, vwr₄, vx₄⟩ := vec_keep v₄
  have g₄ : ∀ r, r ≠ .rax → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r a b => by
    rw [vg₄, vg₃, vg₂, gk₁ r a b]
  have rdi₄ : s₄.gpr .rdi = st s₀ := by rw [g₄ _ (by decide) (by decide), h.rdi]
  have wr₄ : s₄.wr = s₀.wr := by rw [vwr₄, vwr₃, vwr₂, k₁.wr, h.wr]
  have mm₄ : s₄.mem = mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [vm₄, vm₃, vm₂, m₁, h.mem]
  -- MXCSR restored.
  refine WP.block_append (WP.mono (mxcsrOut_ok s₄ (hp.inRW wr₄ rdi₄ (by omega))
    (by rw [mm₄, rdi₄, mxMem_mx]; exact mx_hi _)) fun s₅ ⟨g₅, m₅, mx₅, x₅, y₅, rd₅, wr₅⟩ => ?_)
  have rdi₅ : s₅.gpr .rdi = st s₀ := by rw [g₅, rdi₄]
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄]
  -- The accumulator stored.
  refine WP.block_append (WP.mono (storeH_ok fun d hd => hp.inW wr₅' rdi₅ (by omega)) fun s₆ sp₆ => ?_)
  refine WP.mono (fin3_ok s₆) fun s₇ ⟨si₇, dx₇, g₇, m₇, mx₇, rd₇, wr₇⟩ => ?_
  have g₆ : ∀ r, r ≠ .rax → r ≠ .r10 → s₆.gpr r = s.gpr r := fun r a b => by
    rw [sp₆.gpr, g₅, g₄ r a b]
  have hmx : s₇.mxcsr = s₀.mxcsr &&& 0xffff := by
    rw [mx₇, sp₆.mxcsr, mx₅, mm₄, rdi₄, mxMem_mx]
  have hframe : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₇.mem := by
    rw [m₇]
    refine ((mxMem_frame s₀.mem (st s₀) s₀.mxcsr).mono (by simp)).trans ?_
    rw [← mm₄, ← m₅]
    exact sp₆.frame.mono (by rw [rdi₅]; simp)
  refine ⟨by omega, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, hframe, by rw [hmx, mx_bits], fun key msg hr => ?_⟩
  · rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide), h.rdi]
  · rw [si₇, g₆ _ (by decide) (by decide), h.rsi, add64, Nat.sub_add_cancel h1]
  · rw [dx₇, g₆ _ (by decide) (by decide), h.rdx]
    apply BitVec.eq_of_toNat_eq
    rw [and3_toNat, toNat_ofNat_lt (by omega)]
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
    rw [gk₁ _ (by decide) (by decide), h.rsi, m₁, h.mem, grp_bytes hp (by omega), absorb_grp, Nat.sub_add_cancel h1] at L
    have e₅ : h0 s₅ = hv s₄ 0 := by
      funext i; simp only [h0, hv, qw_of x₅ y₅]
    obtain ⟨W, -, -⟩ := Limbs26.words_val (o := h0 s₅) (by rw [e₅]; exact Fb)
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega
    · rw [← off_24, key_frame hframe, hkey']
    · rw [leNum_acc, m₇, ← rdi₅, sp₆.w0, sp₆.w1, sp₆.w2, W, e₅, F, ← hkey', clamp_key,
        Poly1305.accumulate_append hlen]
      change _ = Poly1305.absorbAll (Rn s₀) (accumulate (Rn s₀) msg) _
      rw [hA0, (S.trans L : _ ≡ _ [MOD P]),
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)]

/-! ## The whole function -/

theorem body_ok {s₀ : State} (hp : APre s₀) (hbig : 16 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VKeep s₀ s) :
    WP isa body s (TailPre s₀ (4 * (nb s₀ / 4))) :=
  WP.seq (WP.mono (pro_ok hp hbig hg hm hk) fun _ h₁ =>
    WP.seq (WP.mono (loop_ok hp (by omega) h₁) fun _ h₂ => epi_ok hp h₂))

theorem TailPre.congr {s₀ s s' : State} {i : Nat} (h : TailPre s₀ i s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hx : s'.mxcsr = s.mxcsr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    TailPre s₀ i s' :=
  ⟨h.le, by rw [hg, h.rdi], by rw [hg, h.rsi], by rw [hg, h.rdx], fun r hr => by rw [hg, h.keep r hr],
    by rw [hrd, h.rd], by rw [hwr, h.wr], by rw [hm]; exact h.frame, by rw [hx]; exact h.mxcsr,
    fun key msg hr => by rw [hm]; exact h.repr key msg hr⟩

theorem correct {s₀ : State} (hp : APre s₀) : WP isa blocksAvx2 s₀ (Post s₀) := by
  have hb := hp.bpre.nb_lt
  refine WP.seq (WP.mono (cmp_ok s₀) fun s₁ ⟨g₁, m₁, k₁, cf₁⟩ => ?_)
  refine WP.ite (decide (nb s₀ < 16)) (by simp [eval, cf₁]) (fun hlt => ?_) (fun hge => ?_)
  · refine tail_ok hp (i := 0) ⟨by omega, by rw [g₁], by rw [g₁]; simp [blkAddr], ?_,
      fun r _ => by rw [g₁], k₁.rd, k₁.wr, by rw [m₁]; exact Frame.refl _ _, by rw [k₁.mxcsr],
      fun key msg hr => by rw [m₁, blks_zero, List.append_nil]; exact hr⟩
    rw [g₁, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.seq (WP.mono (body_ok hp hge g₁ m₁ k₁) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (test_ok s₂) fun s₃ ⟨z₃, g₃, m₃, mx₃, rd₃, wr₃⟩ => ?_)
    have h₃ := h₂.congr g₃ m₃ mx₃ rd₃ wr₃
    refine WP.ite (s₃.gpr .rdx &&& s₃.gpr .rdx == 0) (by simp [eval, z₃, g₃]) (fun h => ?_)
      (fun _ => tail_ok hp h₃)
    have e : 4 * (nb s₀ / 4) = nb s₀ := by
      have := h₃.rdx
      simp only [BitVec.and_self, beq_iff_eq] at h
      rw [h] at this
      have := congrArg BitVec.toNat this
      rw [toNat_ofNat_lt (by omega)] at this
      rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
      simp only [nb] at this ⊢
      omega
    exact WP.block_nil (M := isa) (done_ok hp (e ▸ h₃))

theorem blocksAvx2_ok (s : State) (hs : blocksAvx2X86_64.pre s) :
    ∃ t s', Exec isa blocksAvx2 s t s' ∧ abiPreserved s s' ∧ blocksAvx2X86_64.post s s' :=
  correct (APre.of s hs)

/-! ## Constant time -/

theorem blocksAvx2_ct : ConstantTime isa blocksAvx2X86_64.pre blocksAvx2X86_64.pub blocksAvx2 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨⟨h1, h2, h3⟩, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition (with no blocks). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩]

theorem blocksAvx2_verified :
    Verified X86_64.target blocksAvx2 (Spec.Poly1305.blocksContract X86_64.abi 8) :=
  Verified.of_correct blocksAvx2_ok blocksAvx2_ct (by
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig, blocksAvx2X86_64,
      Proof.Poly1305.blocksX86_64, X86_64.abi, X86_64.argRegs] [sat] using sat)

end VG.Proof.Poly1305.X86_64.Avx2
