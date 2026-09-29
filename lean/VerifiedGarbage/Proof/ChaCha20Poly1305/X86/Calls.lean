import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Common
import VerifiedGarbage.Proof.Poly1305.X86.Init
import VerifiedGarbage.Proof.Poly1305.X86.Blocks
import VerifiedGarbage.Proof.Poly1305.X86.Finalize
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.ChaCha20.X86.Xor

/-!
# ChaCha20-Poly1305 on x86 (32-bit): the calls

Untrusted: everything here is checked by Lean. Each call of a verified
function, in a frame of its arguments (`callWith`), from its proof of
`Verified` (`WP.callWith`): what it needs of the state it is called from
(`CallPre`, which the constant-time proof uses too), and what holds when it
returns.
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Proof.ChaCha20.X86 (contains_off toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## The callees -/

theorem block_nosp : NoSp Impl.ChaCha20.X86.block := NoSp.of_all (by decide +kernel)
theorem xor_nosp : NoSp Impl.ChaCha20.X86.Xor.xor := NoSp.of_all (by decide +kernel)
theorem init_nosp : NoSp Impl.Poly1305.X86.init := NoSp.of_all (by decide +kernel)
theorem blocks_nosp : NoSp Impl.Poly1305.X86.blocks := NoSp.of_all (by decide +kernel)
theorem finalize_nosp : NoSp Impl.Poly1305.X86.finalize := NoSp.of_all (by decide +kernel)

theorem block_stack : stackUse Impl.ChaCha20.X86.block = 0 := by decide +kernel
theorem xor_stack : stackUse Impl.ChaCha20.X86.Xor.xor = 12 := by decide +kernel
theorem init_stack : stackUse Impl.Poly1305.X86.init = 0 := by decide +kernel
theorem blocks_stack : stackUse Impl.Poly1305.X86.blocks = 0 := by decide +kernel
theorem finalize_stack : stackUse Impl.Poly1305.X86.finalize = 0 := by decide +kernel

/-! ## The state a call is made from -/

structure At (s₀ s : State) : Prop where
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Inv.at {s₀ s : State} (h : Inv s₀ s) : At s₀ s := ⟨h.esp, h.rd, h.wr⟩

/-- Part of the stack below the return address. -/
theorem stk_part {s₀ : State} (hp : APre s₀) {a n : Nat} (h : n ≤ a) (ha : a ≤ 32) :
    Region.Sub ⟨(E s₀ - BitVec.ofNat 32 a).setWidth 64, n⟩ (stkR s₀) :=
  fun x hx => below_sub ha hp.sp_lo x (Region.sub_prefix h x hx)

section
variable {s₀ s : State} (hp : APre s₀) (h : At s₀ s) {rs : List Reg} (hk : rs.length ≤ 5)
include hp h hk

theorem At.fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := by
  rw [h.esp]; have := hp.sp_lo; omega

omit hp hk in
theorem At.argAddr0 :
    argAddr (pushed rs s).callEntry 0 = (E s₀ - BitVec.ofNat 32 (4 * rs.length)).setWidth 64 := by
  rw [callEntry_argAddr0, h.esp]

omit hp hk in
theorem At.esp64 :
    ((pushed rs s).callEntry.gpr .esp).setWidth 64 =
      (E s₀ - BitVec.ofNat 32 (4 * rs.length + 4)).setWidth 64 := by
  rw [callEntry_esp', h.esp]

theorem At.espNat : ((pushed rs s).callEntry.gpr .esp).toNat = (E s₀).toNat - (4 * rs.length + 4) := by
  rw [callEntry_espNat (h.fit hp hk), h.esp]

end

/-- A region at offset `o` within one of `rs'`. -/
theorem within {r : Region} {rs' : List Region} (r' : Region) (hr' : r' ∈ rs') (o : Nat)
    (hb : r.base = r'.base + BitVec.ofNat 64 o) (hl : o + r.len ≤ r'.len) :
    ∃ r' ∈ rs', ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len :=
  ⟨r', hr', o, hb, hl⟩

/-! ## `vg_chacha20_block` -/

/-- The permissions it is called with. -/
abbrev rdBlk (s₀ : State) : List Region := [sub s₀ 64 64, below (E s₀) 8]
abbrev wrBlk (s₀ : State) : List Region := [sub s₀ 128 256]

theorem block_pre {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hecx : s.gpr .ecx = C32 s₀ 64)
    (hedx : s.gpr .edx = C32 s₀ 128) :
    CallPre Proof.ChaCha20.blockX86 [.edx, .ecx] (rdBlk s₀) (wrBlk s₀) s := by
  have hk : [Reg.edx, .ecx].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have a0 : arg (pushed [.edx, .ecx] s).callEntry 0 = C32 s₀ 64 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
  have a1 : arg (pushed [.edx, .ecx] s).callEntry 1 = C32 s₀ 128 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
  have e := hp.sp_lo
  have e' := hp.fit_c
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.ChaCha20.blockX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.c64 (k := 64) (by omega), hp.c64 (k := 128) (by omega),
      hp.cNat (k := 64) (by omega), hp.cNat (k := 128) (by omega), List.length_cons, List.length_nil]
    refine ⟨trivial, trivial, sub_disj s₀ (by omega) (by omega) (by omega),
      (hp.below_sub (m := 8) (by omega) (by omega)), ?_, by omega, by omega, by omega⟩
    exact (hp.stk_sub (by omega)).sub_left (stk_part hp (by omega) (by omega))
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact within (ctxR s₀) (by simp) 64 rfl (by show 64 + 64 ≤ 1024; omega)
    · exact within (below (E s₀) 8) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp) 128 rfl (by show 128 + 256 ≤ 1024; omega)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact within (ctxR s₀) (by simp) 128 rfl (by show 128 + 256 ≤ 1024; omega)

/-! ## What holds after a call -/

/-- The call's frame and return address are on the stack below `esp`. -/
theorem At.entry_frame {s₀ s : State} (hp : APre s₀) (h : At s₀ s) {rs : List Reg} (hk : rs.length ≤ 5)
    (hrs : Reg.esp ∉ rs) : Frame [stkR s₀] s.mem (pushed rs s).callEntry.mem :=
  (callEntry_frame (h.fit hp hk) hrs).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [h.esp]; exact below_sub (by omega) hp.sp_lo⟩

/-- A call returns in a state from which calls can be made, with the
callee-saved registers. -/
theorem At.ret {s₀ s s' : State} (h : At s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : At s₀ s' :=
  ⟨by rw [cs .esp (by simp [calleeSaved]), h.esp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem block_call {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hecx : s.gpr .ecx = C32 s₀ 64)
    (hedx : s.gpr .edx = C32 s₀ 128) {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [sub s₀ 128 256, stkR s₀] s.mem s'.mem →
      stateAt s'.mem (cx s₀ + BitVec.ofNat 64 128) =
        Spec.ChaCha20.block (stateAt s.mem (cx s₀ + BitVec.ofNat 64 64)) → Q s') :
    WP isa (callWith [.edx, .ecx] "vg_chacha20_block" Impl.ChaCha20.X86.block) s Q := by
  have hk : [Reg.edx, .ecx].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have e := hp.sp_lo
  refine WP.callWith Proof.ChaCha20.X86.block_verified.1 block_nosp (by simp) (by decide)
    (by rw [block_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (block_pre hp h hecx hedx) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [block_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) ?_
  · simp only [wrBlk, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, below_sub (by omega) hp.sp_lo⟩
  · have a0 : arg (pushed [.edx, .ecx] s).callEntry 0 = C32 s₀ 64 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
    have a1 : arg (pushed [.edx, .ecx] s).callEntry 1 = C32 s₀ 128 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
    simp only [Proof.ChaCha20.blockX86, arg_withRegions, State.withRegions_mem, a0, a1,
      hp.c64 (k := 64) (by omega), hp.c64 (k := 128) (by omega), m₂] at post
    rw [post, VG.Proof.ChaCha20.X86.Xor.stateAt_frame (h.entry_frame hp hk (by decide)) (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_sub (by omega)).symm)]

/-! ## `vg_poly1305_init` -/

abbrev rdInit (s₀ : State) : List Region := [sub s₀ 128 32, below (E s₀) 8]
abbrev wrInit (s₀ : State) : List Region := [sub s₀ 448 128]

theorem init_pre {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hecx : s.gpr .ecx = C32 s₀ 128)
    (hedx : s.gpr .edx = C32 s₀ 448) :
    CallPre Proof.Poly1305.initX86 [.ecx, .edx] (rdInit s₀) (wrInit s₀) s := by
  have hk : [Reg.ecx, .edx].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have a0 : arg (pushed [.ecx, .edx] s).callEntry 0 = C32 s₀ 448 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
  have a1 : arg (pushed [.ecx, .edx] s).callEntry 1 = C32 s₀ 128 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
  have e := hp.sp_lo
  have e' := hp.fit_c
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Poly1305.initX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.c64 (k := 448) (by omega), hp.c64 (k := 128) (by omega),
      hp.cNat (k := 448) (by omega), hp.cNat (k := 128) (by omega), List.length_cons, List.length_nil]
    refine ⟨trivial, trivial, sub_disj s₀ (by omega) (by omega) (by omega),
      (hp.below_sub (m := 8) (by omega) (by omega)), ?_, by omega, by omega, by omega⟩
    exact (hp.stk_sub (by omega)).sub_left (stk_part hp (by omega) (by omega))
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact within (ctxR s₀) (by simp) 128 rfl (by show 128 + 32 ≤ 1024; omega)
    · exact within (below (E s₀) 8) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp) 448 rfl (by show 448 + 128 ≤ 1024; omega)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact within (ctxR s₀) (by simp) 448 rfl (by show 448 + 128 ≤ 1024; omega)

theorem init_call {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hecx : s.gpr .ecx = C32 s₀ 128)
    (hedx : s.gpr .edx = C32 s₀ 448) {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [sub s₀ 448 128, stkR s₀] s.mem s'.mem →
      Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) (bytesAt s.mem (cx s₀ + BitVec.ofNat 64 128) 32) [] →
      Q s') :
    WP isa (callWith [.ecx, .edx] "vg_poly1305_init" Impl.Poly1305.X86.init) s Q := by
  have hk : [Reg.ecx, .edx].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have e := hp.sp_lo
  refine WP.callWith Proof.Poly1305.X86.init_verified.1 init_nosp (by simp) (by decide)
    (by rw [init_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (init_pre hp h hecx hedx) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [init_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) ?_
  · simp only [wrInit, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, below_sub (by omega) hp.sp_lo⟩
  · have a0 : arg (pushed [.ecx, .edx] s).callEntry 0 = C32 s₀ 448 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
    have a1 : arg (pushed [.ecx, .edx] s).callEntry 1 = C32 s₀ 128 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
    simp only [Proof.Poly1305.initX86, arg_withRegions, State.withRegions_mem, a0, a1,
      hp.c64 (k := 448) (by omega), hp.c64 (k := 128) (by omega), m₂] at post
    rwa [bytesAt_frame (h.entry_frame hp hk (by decide)) (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_sub (by omega)).symm) (by omega)] at post

/-! ## `vg_poly1305_blocks` -/

/-- What the `len` bytes at `P` absorbed must be: within memory the functions
may read, and apart from the Poly1305 state and the stack. -/
structure BSrc (s₀ : State) (P : BitVec 32) (len : Nat) : Prop where
  fit : P.toNat + len ≤ 2 ^ 32
  poly : (sub s₀ 448 128).Disjoint ⟨P.setWidth 64, len⟩
  stk : (stkR s₀).Disjoint ⟨P.setWidth 64, len⟩
  cov : ∃ r' ∈ s₀.rd ++ s₀.wr, ∃ o, P.setWidth 64 = r'.base + BitVec.ofNat 64 o ∧ o + len ≤ r'.len

abbrev rdBlocks (s₀ : State) (P : BitVec 32) (n : Nat) : List Region :=
  [⟨P.setWidth 64, 16 * n⟩, below (E s₀) 12]
abbrev wrBlocks (s₀ : State) : List Region := [sub s₀ 448 128]

theorem blocks_pre {s₀ s : State} (hp : APre s₀) (h : At s₀ s) {rn rp rst : Reg}
    (hesp : Reg.esp ∉ [rn, rp, rst]) {P : BitVec 32} {n : Nat} (hs : BSrc s₀ P (16 * n))
    (hst : s.gpr rst = C32 s₀ 448) (hP : s.gpr rp = P) (hn : s.gpr rn = BitVec.ofNat 32 n) :
    CallPre Proof.Poly1305.blocksX86 [rn, rp, rst] (rdBlocks s₀ P n) (wrBlocks s₀) s := by
  have hk : [rn, rp, rst].length ≤ 5 := by simp
  have fit := h.fit hp hk
  have hf := hs.fit
  have a0 : arg (pushed [rn, rp, rst] s).callEntry 0 = C32 s₀ 448 := by
    rw [callEntry_arg fit hesp (by simp)]; exact hst
  have a1 : arg (pushed [rn, rp, rst] s).callEntry 1 = P := by
    rw [callEntry_arg fit hesp (by simp)]; exact hP
  have a2 : (arg (pushed [rn, rp, rst] s).callEntry 2).toNat = n := by
    rw [callEntry_arg fit hesp (by simp)]
    show (s.gpr rn).toNat = n
    rw [hn, toNat_ofNat32 (by omega)]
  have e := hp.sp_lo
  have e' := hp.fit_c
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Poly1305.blocksX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.c64 (k := 448) (by omega), hp.cNat (k := 448) (by omega),
      List.length_cons, List.length_nil]
    refine ⟨trivial, trivial, hs.poly, (hp.below_sub (m := 12) (by omega) (by omega)), ?_, by omega,
      hf, by omega⟩
    exact (hp.stk_sub (by omega)).sub_left (stk_part hp (by omega) (by omega))
  · rw [h.esp, h.rd, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨r', hr', o, hb, hl⟩ := hs.cov
      refine ⟨r', ?_, o, hb, hl⟩
      rcases List.mem_append.mp hr' with hr' | hr'
      · exact List.mem_append_left _ hr'
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr')
    · exact within (below (E s₀) 12) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp [hp.wr]) 448 rfl (by show 448 + 128 ≤ 1024; omega)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact within (ctxR s₀) (by simp) 448 rfl (by show 448 + 128 ≤ 1024; omega)

theorem blocks_call {s₀ s : State} (hp : APre s₀) (h : At s₀ s) {rn rp rst : Reg}
    (hesp : Reg.esp ∉ [rn, rp, rst]) {P : BitVec 32} {n : Nat} (hs : BSrc s₀ P (16 * n))
    (hst : s.gpr rst = C32 s₀ 448) (hP : s.gpr rp = P) (hn : s.gpr rn = BitVec.ofNat 32 n)
    {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [sub s₀ 448 128, stkR s₀] s.mem s'.mem →
      (∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key (msg ++ bytesAt s.mem (P.setWidth 64) (16 * n))) →
      Q s') :
    WP isa (callWith [rn, rp, rst] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) s Q := by
  have hk : [rn, rp, rst].length ≤ 5 := by simp
  have fit := h.fit hp hk
  have e := hp.sp_lo
  have hf := hs.fit
  refine WP.callWith Proof.Poly1305.X86.blocks_verified.1 blocks_nosp (by simp) hesp
    (by rw [blocks_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (blocks_pre hp h hesp hs hst hP hn) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [blocks_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) fun key msg hr => ?_
  · simp only [wrBlocks, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, below_sub (by omega) hp.sp_lo⟩
  · have a0 : arg (pushed [rn, rp, rst] s).callEntry 0 = C32 s₀ 448 := by
      rw [callEntry_arg fit hesp (by simp)]; exact hst
    have a1 : arg (pushed [rn, rp, rst] s).callEntry 1 = P := by
      rw [callEntry_arg fit hesp (by simp)]; exact hP
    have a2 : (arg (pushed [rn, rp, rst] s).callEntry 2).toNat = n := by
      rw [callEntry_arg fit hesp (by simp)]
      show (s.gpr rn).toNat = n
      rw [hn, toNat_ofNat32 (by omega)]
    simp only [Proof.Poly1305.blocksX86, arg_withRegions, State.withRegions_mem, a0, a1, a2,
      hp.c64 (k := 448) (by omega), m₂] at post
    have ef := h.entry_frame hp hk hesp
    have := post key msg (Repr.frame ef (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_sub (by omega)).symm) hr)
    rwa [bytesAt_frame ef (by simp only [List.mem_singleton, forall_eq]; exact hs.stk.symm)
      (by omega)] at this

/-! ## `vg_chacha20_xor` -/

abbrev wrXor (s₀ : State) : List Region := [sub s₀ 64 64, dR s₀, sub s₀ 128 320, below (E s₀) 16]

theorem xor_pre {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (heax : s.gpr .eax = C32 s₀ 64)
    (hecx : s.gpr .ecx = DP s₀) (hedx : s.gpr .edx = LN s₀) (hesi : s.gpr .esi = C32 s₀ 128) :
    CallPre Proof.ChaCha20.xorX86 [.esi, .edx, .ecx, .eax] [] (wrXor s₀) s := by
  have hk : [Reg.esi, .edx, .ecx, .eax].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have a0 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 0 = C32 s₀ 64 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact heax
  have a1 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 1 = DP s₀ := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
  have a2 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 2 = LN s₀ := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
  have a3 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 3 = C32 s₀ 128 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hesi
  have e := hp.sp_lo
  have e₂ := hp.sp_hi
  have e' := hp.fit_c
  have es : (E s₀ - BitVec.ofNat 32 20).setWidth 64 - 12 = (E s₀ - BitVec.ofNat 32 32).setWidth 64 := by
    rw [hp.E64 (by omega), hp.E64 (by omega), show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl]; bv_omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.ChaCha20.xorX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.c64 (k := 64) (by omega), hp.c64 (k := 128) (by omega),
      hp.cNat (k := 64) (by omega), hp.cNat (k := 128) (by omega), List.length_cons, List.length_nil, es]
    refine ⟨trivial, trivial, (hp.d_sub (by omega)).symm, sub_disj s₀ (by omega) (by omega) (by omega),
      hp.d_sub (by omega), hp.below_sub (by omega) (by omega),
      (hp.stk_d.sub_left (stk_below s₀ (n := 16) (by omega) hp)),
      hp.below_sub (by omega) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, by omega, hp.fit_d, by omega, by omega,
      by omega⟩
    · exact (hp.stk_sub (by omega)).sub_left (stk_part hp (by omega) (by omega))
    · exact hp.stk_d.sub_left (stk_part hp (by omega) (by omega))
    · exact (hp.stk_sub (by omega)).sub_left (stk_part hp (by omega) (by omega))
    · exact (hp.stk_sub (by omega)).sub_left (stk_part hp (by omega) (by omega))
    · exact hp.stk_d.sub_left (stk_part hp (by omega) (by omega))
    · exact (hp.stk_sub (by omega)).sub_left (stk_part hp (by omega) (by omega))
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact within (ctxR s₀) (by simp) 64 rfl (by show 64 + 64 ≤ 1024; omega)
    · exact within (dR s₀) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp) 128 rfl (by show 128 + 320 ≤ 1024; omega)
    · exact within (below (E s₀) 16) (by simp) 0 (by simp) (by simp)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact within (ctxR s₀) (by simp) 64 rfl (by show 64 + 64 ≤ 1024; omega)
    · exact within (dR s₀) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp) 128 rfl (by show 128 + 320 ≤ 1024; omega)
    · exact within (below (E s₀) 16) (by simp) 0 (by simp) (by simp)

theorem xor_call {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (heax : s.gpr .eax = C32 s₀ 64)
    (hecx : s.gpr .ecx = DP s₀) (hedx : s.gpr .edx = LN s₀) (hesi : s.gpr .esi = C32 s₀ 128)
    {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem →
      Spec.ChaCha20.bytesAt s'.mem (dp s₀) (L s₀) =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀))
          (keystream (stateAt s.mem (cx s₀ + BitVec.ofNat 64 64)) (L s₀)) → Q s') :
    WP isa (callWith [.esi, .edx, .ecx, .eax] "vg_chacha20_xor" Impl.ChaCha20.X86.Xor.xor) s Q := by
  have hk : [Reg.esi, .edx, .ecx, .eax].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have e := hp.sp_lo
  refine WP.callWith Proof.ChaCha20.X86.Xor.xor_verified.1 xor_nosp (by simp) (by decide)
    (by rw [xor_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (xor_pre hp h heax hecx hedx hesi) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [xor_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) ?_
  · simp only [wrXor, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    have m1 : sub s₀ 64 384 ∈ [sub s₀ 64 384, dR s₀, stkR s₀] := List.mem_cons_self ..
    have m2 : dR s₀ ∈ [sub s₀ 64 384, dR s₀, stkR s₀] := List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have m3 : stkR s₀ ∈ [sub s₀ 64 384, dR s₀, stkR s₀] :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, m1, sub_sub s₀ (Nat.le_refl _) (by omega) (by omega)⟩
    · exact ⟨_, m2, fun _ h => h⟩
    · exact ⟨_, m1, sub_sub s₀ (by omega) (by omega) (by omega)⟩
    · exact ⟨stkR s₀, m3, below_sub (by omega) hp.sp_lo⟩
    · exact ⟨stkR s₀, m3, below_sub (by omega) hp.sp_lo⟩
  · have a0 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 0 = C32 s₀ 64 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact heax
    have a1 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 1 = DP s₀ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
    have a2 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 2 = LN s₀ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
    simp only [Proof.ChaCha20.xorX86, arg_withRegions, State.withRegions_mem, a0, a1, a2,
      hp.c64 (k := 64) (by omega), m₂] at post
    have ef := h.entry_frame hp hk (by decide)
    rw [post, show Spec.ChaCha20.bytesAt = bytesAt from rfl, bytesAt_frame ef (by
      simp only [List.mem_singleton, forall_eq]; exact hp.stk_d.symm) (by have := (LN s₀).isLt; omega),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame ef (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_sub (by omega)).symm)]

/-! ## `vg_poly1305_finalize` -/

/-- Its arguments: the Poly1305 state, `count = 0` (both words), `out` and
its working space, `ctx[672, 800)`, pushed last to first. -/
abbrev finRegs : List Reg := [.ebx, .ecx, .eax, .eax, .esi]

abbrev rdFin (s₀ : State) : List Region := [below (E s₀) 20]
abbrev wrFin (s₀ : State) (out : Nat) : List Region := [sub s₀ 448 128, sub s₀ out 16, sub s₀ 672 128]

/-- Where the tag may be written. -/
def OutOk (out : Nat) : Prop := out = 48 ∨ out = 640

section
variable {s₀ s : State} (hp : APre s₀) (h : At s₀ s) {out : Nat} (ho : OutOk out)
  (hebx : s.gpr .ebx = C32 s₀ 672) (hecx : s.gpr .ecx = C32 s₀ out) (heax : s.gpr .eax = 0)
  (hesi : s.gpr .esi = C32 s₀ 448)
include hp h hebx hecx heax hesi

theorem fin_args :
    arg (pushed finRegs s).callEntry 0 = C32 s₀ 448 ∧ arg (pushed finRegs s).callEntry 1 = 0 ∧
      arg (pushed finRegs s).callEntry 2 = 0 ∧ arg (pushed finRegs s).callEntry 3 = C32 s₀ out ∧
      arg (pushed finRegs s).callEntry 4 = C32 s₀ 672 := by
  have fit := h.fit hp (rs := finRegs) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [callEntry_arg fit (by decide) (by decide)]
  exacts [hesi, heax, heax, hecx, hebx]

include ho in
theorem finalize_pre : CallPre Proof.Poly1305.finalizeX86 finRegs (rdFin s₀) (wrFin s₀ out) s := by
  have ho' : out + 16 ≤ 1024 := by unfold OutOk at ho; omega
  have hk : finRegs.length ≤ 5 := by decide
  obtain ⟨a0, a1, a2, a3, a4⟩ := fin_args hp h hebx hecx heax hesi (out := out)
  have e := hp.sp_lo
  have e₂ := hp.sp_hi
  have e' := hp.fit_c
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Poly1305.finalizeX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a3, a4, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.c64 (k := 448) (by omega), hp.c64 (k := 672) (by omega),
      hp.c64 (k := out) (by omega), hp.cNat (k := 448) (by omega), hp.cNat (k := 672) (by omega),
      hp.cNat (k := out) (by omega), List.length_cons, List.length_nil]
    unfold OutOk at ho
    refine ⟨trivial, trivial, sub_disj s₀ (by omega) (by omega) ho', sub_disj s₀ (by omega) (by omega) (by omega),
      sub_disj s₀ (by omega) ho' (by omega), hp.below_sub (by omega) (by omega), hp.below_sub (by omega) ho',
      hp.below_sub (by omega) (by omega), ?_, ?_, ?_, by omega, by omega, by omega, by omega⟩
    · exact (hp.stk_sub (by omega)).sub_left (stk_part hp (by omega) (by omega))
    · exact (hp.stk_sub ho').sub_left (stk_part hp (by omega) (by omega))
    · exact (hp.stk_sub (by omega)).sub_left (stk_part hp (by omega) (by omega))
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact within (below (E s₀) 20) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp) 448 rfl (by show 448 + 128 ≤ 1024; omega)
    · exact within (ctxR s₀) (by simp) out rfl ho'
    · exact within (ctxR s₀) (by simp) 672 rfl (by show 672 + 128 ≤ 1024; omega)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact within (ctxR s₀) (by simp) 448 rfl (by show 448 + 128 ≤ 1024; omega)
    · exact within (ctxR s₀) (by simp) out rfl ho'
    · exact within (ctxR s₀) (by simp) 672 rfl (by show 672 + 128 ≤ 1024; omega)

include ho in
theorem finalize_call {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [sub s₀ 448 128, sub s₀ out 16, sub s₀ 672 128, stkR s₀] s.mem s'.mem →
      (∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        bytesAt s'.mem (cx s₀ + BitVec.ofNat 64 out) 16 = mac key msg) → Q s') :
    WP isa (callWith finRegs "vg_poly1305_finalize" Impl.Poly1305.X86.finalize) s Q := by
  have ho' : out + 16 ≤ 1024 := by unfold OutOk at ho; omega
  have hk : finRegs.length ≤ 5 := by decide
  have e := hp.sp_lo
  refine WP.callWith Proof.Poly1305.X86.finalize_verified.1 finalize_nosp (by simp) (by decide)
    (by rw [finalize_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (finalize_pre hp h ho hebx hecx heax hesi) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [finalize_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) fun key msg hr => ?_
  · simp only [wrFin, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, below_sub (by omega) hp.sp_lo⟩
  · obtain ⟨a0, a1, a2, a3, -⟩ := fin_args hp h hebx hecx heax hesi (out := out)
    simp only [Proof.Poly1305.finalizeX86, Proof.Poly1305.countX86, arg_withRegions, State.withRegions_mem,
      a0, a1, a2, a3, hp.c64 (k := 448) (by omega), hp.c64 (k := out) (by omega), m₂] at post
    exact post key msg (Proof.Poly1305.Repr.buffered (Repr.frame (h.entry_frame hp hk (by decide)) (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_sub (by omega)).symm) hr))
      (by rw [hr.1]; rfl)

end

end VG.Proof.ChaCha20Poly1305.X86
