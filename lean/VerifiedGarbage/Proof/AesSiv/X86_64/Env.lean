import VerifiedGarbage.Proof.AesSiv.X86_64.Common

/-!
# AES-SIV on x86-64: the regions of `s2v_ad`, `seal` and `open`

The three functions have the same arguments: the key context `C`, the
rounds `R`, `D` (16 bytes), the data `P` (`L` bytes) and the working space
`W` (2560 bytes). They call `vg_cmac_aes_update` and `vg_cmac_aes_finalize`
with the context as the key, a CMAC state in the working space, the data or
the working space as the message, and the working space at `W + 256` as
theirs (`Env.uargs`, `Env.fargs`); and `vg_aes_ctr32` with `K2`'s schedule
and blocks of the working space (`Env.cargs`). `Env` names what their
contracts say about the regions, whichever of them are writable.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64
open VG.Proof.CmacAes.Stream.X86_64 (UArgs FArgs toNat_add_lt)
open VG.Proof.CmacAes.X86_64 (CallPre)

/-- The regions of the arguments. -/
structure Env (s₀ : State) (C D P W : Addr) (R L : Nat) : Prop where
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  ctxIn : (⟨C, 512⟩ : Region) ∈ s₀.rd ++ s₀.wr
  dIn : (⟨D, 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  dataIn : (⟨P, L⟩ : Region) ∈ s₀.rd ++ s₀.wr
  workIn : (⟨W, 2560⟩ : Region) ∈ s₀.wr
  c_w : (⟨C, 512⟩ : Region).Disjoint ⟨W, 2560⟩
  d_p : (⟨D, 16⟩ : Region).Disjoint ⟨P, L⟩
  d_w : (⟨D, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  p_w : (⟨P, L⟩ : Region).Disjoint ⟨W, 2560⟩
  ret_c : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨C, 512⟩
  ret_d : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨D, 16⟩
  ret_p : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨P, L⟩
  ret_w : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  stk_c : (below (s₀.gpr .rsp) 16).Disjoint ⟨C, 512⟩
  stk_d : (below (s₀.gpr .rsp) 16).Disjoint ⟨D, 16⟩
  stk_p : (below (s₀.gpr .rsp) 16).Disjoint ⟨P, L⟩
  stk_w : (below (s₀.gpr .rsp) 16).Disjoint ⟨W, 2560⟩
  wC : C.toNat + 512 ≤ 2 ^ 64
  wD : D.toNat + 16 ≤ 2 ^ 64
  wP : P.toNat + L ≤ 2 ^ 64
  wW : W.toNat + 2560 ≤ 2 ^ 64
  lt : L < 2 ^ 64

/-- The registers that hold the arguments while the code runs: the context
in `rbx`, the rounds in `rbp`, `D` in `r12`, the data in `r13` (`r14` bytes)
and the working space in `r15`. -/
structure Regs (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r13 : s.gpr .r13 = P
  r14 : s.gpr .r14 = BitVec.ofNat 64 L
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Regs.keep {s₀ s s' : State} {C D P W : Addr} {R L : Nat} (h : Regs s₀ C D P W R L s)
    (hs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Regs s₀ C D P W R L s' :=
  ⟨by rw [hs _ (by decide), h.rbx], by rw [hs _ (by decide), h.rbp], by rw [hs _ (by decide), h.r12],
    by rw [hs _ (by decide), h.r13], by rw [hs _ (by decide), h.r14], by rw [hs _ (by decide), h.r15],
    by rw [hs _ (by decide), h.rsp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

/-- A region at an offset of one of `rs`. -/
theorem cov_off {rs : List Region} {r : Region} (hr : r ∈ rs) {off n : Nat} (h : off + n ≤ r.len) :
    Covers [⟨r.base + BitVec.ofNat 64 off, n⟩] rs :=
  Covers.of_sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨r, hr, off, rfl, h⟩

theorem cov_base {rs : List Region} {r : Region} (hr : r ∈ rs) {n : Nat} (h : n ≤ r.len) :
    Covers [⟨r.base, n⟩] rs := by
  have := cov_off hr (off := 0) (n := n) (by omega)
  rwa [Proof.CmacAes.X86_64.k0] at this

/-- The PRF and the cipher of a key context outside a frame's regions. -/
theorem ctxMac_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxMac m' C R = Spec.Siv.ctxMac m C R := by
  unfold Spec.Siv.ctxMac Spec.Siv.schedCiph
  rw [Proof.CmacAes.X86_64.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega))) (by omega),
    Proof.CmacAes.X86_64.bytesAt_frame hf (p := C + 240)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 240) (n := 16) (by decide))) (by decide),
    Proof.CmacAes.X86_64.bytesAt_frame hf (p := C + 256)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 256) (n := 16) (by decide))) (by decide)]

theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxCiph m' C R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.CmacAes.X86_64.bytesAt_frame hf (p := C + 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega))) (by omega)]

namespace Env

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem sW (_h : Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base W hd

theorem sC (_h : Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 512) :
    Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 512⟩ :=
  Offset.sub_base C hd

theorem sP (_h : Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ L) :
    Region.Sub ⟨P + BitVec.ofNat 64 d, n⟩ ⟨P, L⟩ :=
  Offset.sub_base P hd

theorem inW (h : Env s₀ C D P W R L) {s : State} (hwr : s.wr = s₀.wr) {d n : Nat} (hd : d + n ≤ 2560) :
    InRegions s.wr (W + BitVec.ofNat 64 d) n := by
  rw [hwr]; exact ⟨_, h.workIn, Offset.contains_base W hd (by have := h.wW; omega)⟩

theorem inRW (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]
  obtain ⟨r, hr, hc⟩ := h.inW (s := s₀) rfl hd
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem inRC (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 512) : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]; exact ⟨_, h.ctxIn, Offset.contains_base C hd (by have := h.wC; omega)⟩

theorem inRD (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 16) : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]; exact ⟨_, h.dIn, Offset.contains_base D hd (by have := h.wD; omega)⟩

/-- A message for the CMAC functions: `n` bytes at `Q`, which miss the state at
`W + o`, the working space of the functions called and the stack. -/
structure Src (s₀ : State) (W : Addr) (o : Nat) (Q : Addr) (n : Nat) : Prop where
  qo : (⟨Q, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 o, 16⟩
  qs : (⟨Q, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 2176⟩
  stk : (below (s₀.gpr .rsp) 16).Disjoint ⟨Q, n⟩
  wrap : Q.toNat + n ≤ 2 ^ 64
  cov : Covers [⟨Q, n⟩] (s₀.rd ++ s₀.wr)

/-- Data bytes as the message. -/
theorem srcData (h : Env s₀ C D P W R L) {o a n : Nat} (ho : o + 16 ≤ 2560) (ha : a + n ≤ L) :
    Src s₀ W o (P + BitVec.ofNat 64 a) n where
  qo := (h.p_w.sub_left (h.sP ha)).sub_right (h.sW ho)
  qs := (h.p_w.sub_left (h.sP ha)).sub_right (h.sW (by decide))
  stk := h.stk_p.sub_right (h.sP ha)
  wrap := by
    have := h.wP
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := (P + BitVec.ofNat 64 a).isLt; omega
    · rw [toNat_add_lt P this (by omega)]; omega
  cov := cov_off h.dataIn ha

theorem srcData₀ (h : Env s₀ C D P W R L) {o n : Nat} (ho : o + 16 ≤ 2560) (hn : n ≤ L) :
    Src s₀ W o P n := by
  have := h.srcData (o := o) (a := 0) (n := n) ho (by omega)
  rwa [Proof.CmacAes.X86_64.k0] at this

/-- Bytes of the working space below `W + 256`, apart from the state, as the message. -/
theorem srcWork (h : Env s₀ C D P W R L) {o t n : Nat} (ho : o + 16 ≤ 256) (ht : t + n ≤ 256)
    (hs : t + n ≤ o ∨ o + 16 ≤ t) : Src s₀ W o (W + BitVec.ofNat 64 t) n where
  qo := Offset.disjoint W hs (by omega) (by omega)
  qs := Offset.disjoint W (by omega) (by omega) (by omega)
  stk := h.stk_w.sub_right (h.sW (by omega))
  wrap := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  cov := Covers.right (cov_off h.workIn (by simp; omega))

/-- The arguments of `vg_cmac_aes_finalize`: the context as the key, the
state at `W + o`, the message at `Q`, and the working space at `W + 256`. -/
theorem fargs (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) {o : Nat} (ho : o + 16 ≤ 256) {Q : Addr} {n : Nat}
    (hq : Src s₀ W o Q n) (hn : n ≤ 16)
    (rdi : s.gpr .rdi = C) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = W + BitVec.ofNat 64 o)
    (rcx : s.gpr .rcx = Q) (r8 : s.gpr .r8 = BitVec.ofNat 64 n) (r9 : s.gpr .r9 = W + BitVec.ofNat 64 256) :
    FArgs s C (W + BitVec.ofNat 64 o) Q (W + BitVec.ofNat 64 256) n R where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := h.rounds
  len := hn
  kst := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by omega))
  ks := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by decide))
  pst := hq.qo
  ps := hq.qs
  sts := Offset.disjoint W (by omega) (by omega) (by omega)
  stkK := by rw [hsp]; exact h.stk_c.sub_right (Region.sub_prefix (by decide))
  stkP := by rw [hsp]; exact hq.stk
  stkSt := by rw [hsp]; exact h.stk_w.sub_right (h.sW (by omega))
  stkS := by rw [hsp]; exact h.stk_w.sub_right (h.sW (by decide))
  wrapK := by have := h.wC; omega
  wrapSt := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  wrapP := hq.wrap
  wrapS := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  reads := by
    rw [hrd, hwr]
    refine Covers.append_left (Covers.cons (cov_base h.ctxIn (by simp)) (Covers.cons hq.cov Covers.nil))
      (Covers.cons (Covers.right (cov_off h.workIn (by simp; omega)))
        (Covers.cons (Covers.right (cov_off h.workIn (by simp))) Covers.nil))
  writes := by
    rw [hwr]
    exact Covers.cons (cov_off h.workIn (by simp; omega)) (Covers.cons (cov_off h.workIn (by simp)) Covers.nil)

/-- The arguments of `vg_cmac_aes_update`: `K1`'s schedule, the state at
`W + o`, `n` blocks at `Q`, and the working space at `W + 256`. -/
theorem uargs (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) {o : Nat} (ho : o + 16 ≤ 256) {Q : Addr} {n : Nat}
    (hq : Src s₀ W o Q (16 * n)) (hn : 16 * n < 2 ^ 64)
    (rdi : s.gpr .rdi = C) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = W + BitVec.ofNat 64 o)
    (rcx : s.gpr .rcx = Q) (r8 : s.gpr .r8 = BitVec.ofNat 64 n) (r9 : s.gpr .r9 = W + BitVec.ofNat 64 256) :
    UArgs s C (W + BitVec.ofNat 64 o) Q (W + BitVec.ofNat 64 256) R n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := h.rounds
  hn := hn
  wc := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by omega))
  ws := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by decide))
  dc := hq.qo
  ds := hq.qs
  cs := Offset.disjoint W (by omega) (by omega) (by omega)
  stkW := by rw [hsp]; exact h.stk_c.sub_right (Region.sub_prefix (by decide))
  stkD := by rw [hsp]; exact hq.stk
  stkC := by rw [hsp]; exact h.stk_w.sub_right (h.sW (by omega))
  stkS := by rw [hsp]; exact h.stk_w.sub_right (h.sW (by decide))
  wrapC := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  wrapD := hq.wrap
  wrapS := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  reads := by
    rw [hrd, hwr]
    refine Covers.append_left (Covers.cons (cov_base h.ctxIn (by simp)) (Covers.cons hq.cov Covers.nil))
      (Covers.cons (Covers.right (cov_off h.workIn (by simp; omega)))
        (Covers.cons (Covers.right (cov_off h.workIn (by simp))) Covers.nil))
  writes := by
    rw [hwr]
    exact Covers.cons (cov_off h.workIn (by simp; omega)) (Covers.cons (cov_off h.workIn (by simp)) Covers.nil)

end Env

end VG.Proof.AesSiv.X86_64
