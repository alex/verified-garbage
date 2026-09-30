import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallArith

/-!
# ML-DSA verification on x86-64: calls of the samplers

Untrusted: everything here is checked by Lean. The calls of
`vg_mldsa_rej_ntt_poly` (seed at `SB`) and `vg_mldsa_sample_in_ball`: what
they need of the layout (`…Chk`), what they do (`…_ok`: the result in
`eax`, and the sampled polynomial, as `Outcome`), and that two runs whose
layout registers and seeds agree leak the same (`…_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The 32-bit result of a function, in `rax`. -/
abbrev res (s : State) : BitVec 32 := (s.gpr .rax).setWidth 32

/-! ## `RejNTTPoly` -/

def rejChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  sepB bs (sc oSB) 34 a 1024 && sepB bs (sc oSB) 34 (sc oSS) 2048 && sepB bs a 1024 (sc oSS) 2048 &&
    inB bs (sc oSB) 34 && inB bs a 1024 && inB bs (sc oSS) 2048 && inB wbs a 1024 && inB wbs (sc oSS) 2048

abbrev rejArgs (a : Ptr) : List (Reg × Arg) := [(.rdi, .ptr (sc oSB)), (.rsi, .ptr a), (.rdx, .ptr (sc oSS))]

theorem rej_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {a : Ptr} (hc : rejChk bs wbs a = true) :
    ∀ x ∈ rejArgs a, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [rejChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L c4, by decide⟩, ⟨ptr_ok L c5, by decide⟩, ⟨ptr_ok L c6, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {a : Ptr}
  (hc : rejChk (rbs ++ wbs) wbs a = true)
include L hc

theorem rej_cov : Covers ([⟨pa s (sc oSB), 34⟩] ++ [⟨pa s a, 1024⟩, ⟨pa s (sc oSS), 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s a, 1024⟩, ⟨pa s (sc oSS), 2048⟩] s.wr := by
  simp only [rejChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, _⟩, _⟩, c7⟩, c8⟩ := hc
  exact ⟨covers_append (L.cR c4) (covers_wr (covers_cons (L.cW c7) (L.cW c8))), covers_cons (L.cW c7) (L.cW c8)⟩

theorem rej_pre {s1 : State} (h1 : Args (rejArgs a) s s1) :
    (rejNTTContract X86_64.abi 16).pre
      (s1.callEntry.withRegions [⟨pa s (sc oSB), 34⟩] [⟨pa s a, 1024⟩, ⟨pa s (sc oSS), 2048⟩]) := by
  simp only [rejChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = pa s (sc oSB) := h1.r0
  have g2 : s1.gpr .rsi = pa s a := h1.r1
  have g3 : s1.gpr .rdx = pa s (sc oSS) := h1.r2
  sig_pre [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, g3, h1.rsp]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.disj c2, L.disj c3, L.ret8 c4, L.ret8 c5, L.ret8 c6, L.stk16 c4,
    L.stk16 c5, L.stk16 c6, L.nwp c4, L.nwp c5, L.nwp c6⟩

end

theorem rejNttAt_ok {P : Prims} (C : CalleeOk P.rejNtt (rejNTTContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : Lay rbs wbs s) {a : Ptr} (hc : rejChk (rbs ++ wbs) wbs a = true) :
    WP isa (rejNttAt P a) s fun s' => PPostB s s' [(a, 1024), (sc oSS, 2048)] ∧
      (res s' = 1 → Reduced s'.mem (pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (pa s (sc oSB)) 34)) (res s') (polyAt s'.mem (pa s a)) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (rej_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => rej_pre L hc h1) (rej_cov L hc).1 (rej_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, hg, hq⟩ => ⟨hP.b, ?_⟩
  simp only [rejChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, _⟩, _⟩, _⟩, _⟩ := hc
  sig_post [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, hm, h1.rsp, h1.1.2, hg _ (by decide)] at hq
  simp only [Arg.val] at hq
  rw [L.wbytesAt c4] at hq
  exact hq

theorem rejNttAt_tr {P : Prims} (C : CalleeOk P.rejNtt (rejNTTContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : LayOk (rbs ++ wbs)) {a : Ptr} (hc : rejChk (rbs ++ wbs) wbs a = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ SameB x y ∧
      bytesAt x.mem (pa x (sc oSB)) 34 = bytesAt y.mem (pa y (sc oSB)) 34) :
    RelCT isa Q (rejNttAt P a) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (rej_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, e, eb⟩ := hQ x y hp
  refine ⟨_, _, _, _, rej_pre Lx hc h1, rej_pre Ly hc h2, ?_, (rej_cov Lx hc).1, (rej_cov Lx hc).2,
    (rej_cov Ly hc).1, (rej_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [rejChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc'
  sig_pub [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h2.r0, h2.r1, h2.r2, h1.1.2, h2.1.2, h1.rsp, h2.rsp]
  simp only [Arg.val]
  rw [Lx.wbytesAt c4, Ly.wbytesAt c4, eb]
  exact ⟨by rw [e.2], rfl, e.pa (ptr_bs hS c4), e.pa (ptr_bs hS c5), e.pa (ptr_bs hS c6)⟩

/-! ## `SampleInBall` -/

def ballChk (bs wbs : List (Reg × Nat)) (ct : Ptr) (len : Nat) (c : Ptr) : Bool :=
  sepB bs ct len c 1024 && sepB bs ct len (sc oSS) 2048 && sepB bs c 1024 (sc oSS) 2048 &&
    inB bs ct len && inB bs c 1024 && inB bs (sc oSS) 2048 && inB wbs c 1024 && inB wbs (sc oSS) 2048

abbrev ballArgs (ct : Ptr) (len tau : Nat) (c : Ptr) : List (Reg × Arg) :=
  [(.rdi, .ptr ct), (.rsi, .imm len), (.rdx, .imm tau), (.rcx, .ptr c), (.r8, .ptr (sc oSS))]

theorem ball_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {ct c : Ptr} {len tau : Nat}
    (hp : (len, tau) ∈ ballParams) (hc : ballChk bs wbs ct len c = true) :
    ∀ x ∈ ballArgs ct len tau c, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [ballChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc
  simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L c4, by decide⟩, ⟨show len < 2 ^ 31 by omega, by decide⟩, ⟨show tau < 2 ^ 31 by omega, by decide⟩,
    ⟨ptr_ok L c5, by decide⟩, ⟨ptr_ok L c6, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {ct c : Ptr} {len tau : Nat}
  (hp : (len, tau) ∈ ballParams) (hc : ballChk (rbs ++ wbs) wbs ct len c = true)
include L hc

omit hp in
theorem ball_cov : Covers ([⟨pa s ct, len⟩] ++ [⟨pa s c, 1024⟩, ⟨pa s (sc oSS), 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s c, 1024⟩, ⟨pa s (sc oSS), 2048⟩] s.wr := by
  simp only [ballChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, _⟩, _⟩, c7⟩, c8⟩ := hc
  exact ⟨covers_append (L.cR c4) (covers_wr (covers_cons (L.cW c7) (L.cW c8))), covers_cons (L.cW c7) (L.cW c8)⟩

include hp in
theorem ball_pre {s1 : State} (h1 : Args (ballArgs ct len tau c) s s1) :
    (sampleInBallContract X86_64.abi 16).pre
      (s1.callEntry.withRegions [⟨pa s ct, len⟩] [⟨pa s c, 1024⟩, ⟨pa s (sc oSS), 2048⟩]) := by
  simp only [ballChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc
  have hl : len < 2 ^ 31 ∧ tau < 2 ^ 31 := by
    simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp; omega
  sig_pre [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.rsp]
  simp only [Arg.val]
  rw [imm64 (show len < 2 ^ 64 by omega), imm32 (show tau < 2 ^ 32 by omega)]
  exact ⟨L.sp16, by first | rfl | trivial, by first | rfl | trivial, L.disj c1, L.disj c2, L.disj c3, L.ret8 c4, L.ret8 c5, L.ret8 c6,
    L.stk16 c4, L.stk16 c5, L.stk16 c6, L.nwp c4, L.nwp c5, L.nwp c6, hp⟩

end

theorem ballAt_ok {P : Prims} (C : CalleeOk P.ball (sampleInBallContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : Lay rbs wbs s) {ct c : Ptr} {len tau : Nat} (hp : (len, tau) ∈ ballParams)
    (hc : ballChk (rbs ++ wbs) wbs ct len c = true) :
    WP isa (ballAt P ct len tau c) s fun s' => PPostB s s' [(c, 1024), (sc oSS, 2048)] ∧
      (res s' = 1 → Reduced s'.mem (pa s c)) ∧
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (pa s ct) len)).map toRq) (res s')
        (polyAt s'.mem (pa s c)) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (ball_args L.ok hp hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => ball_pre L hp hc h1) (ball_cov L hc).1 (ball_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, hg, hq⟩ => ⟨hP.b, ?_⟩
  have hc' := hc
  simp only [ballChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, c4⟩, _⟩, _⟩, _⟩, _⟩ := hc'
  have hl : len < 2 ^ 31 ∧ tau < 2 ^ 31 := by
    simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp; omega
  sig_post [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, h1.r3, hm, h1.rsp, h1.1.2, hg _ (by decide)] at hq
  simp only [Arg.val] at hq
  rw [imm64 (show len < 2 ^ 64 by omega), imm32 (show tau < 2 ^ 32 by omega), L.wbytesAt c4] at hq
  exact hq

theorem ballAt_tr {P : Prims} (C : CalleeOk P.ball (sampleInBallContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : LayOk (rbs ++ wbs)) {ct c : Ptr} {len tau : Nat} (hp : (len, tau) ∈ ballParams)
    (hc : ballChk (rbs ++ wbs) wbs ct len c = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ SameB x y ∧
      bytesAt x.mem (pa x ct) len = bytesAt y.mem (pa y ct) len) :
    RelCT isa Q (ballAt P ct len tau c) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (ball_args hS hp hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hq h1 h2
  obtain ⟨Lx, Ly, e, eb⟩ := hQ x y hq
  refine ⟨_, _, _, _, ball_pre Lx hp hc h1, ball_pre Ly hp hc h2, ?_, (ball_cov Lx hc).1, (ball_cov Lx hc).2,
    (ball_cov Ly hc).1, (ball_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [ballChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc'
  have hl : len < 2 ^ 31 := by
    simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp; omega
  sig_pub [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h1.1.2, h2.1.2, h1.rsp, h2.rsp]
  simp only [Arg.val]
  rw [imm64 (show len < 2 ^ 64 by omega), Lx.wbytesAt c4, Ly.wbytesAt c4, eb]
  exact ⟨by rw [e.2], rfl, e.pa (ptr_bs hS c4), trivial, trivial, e.pa (ptr_bs hS c5), e.pa (ptr_bs hS c6)⟩

end VG.Proof.MlDsa.X86_64.Verify
