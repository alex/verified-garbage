import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CallPack

/-!
# ML-DSA signing on AArch64: calls of the other primitives

Untrusted: everything here is checked by Lean. As `CallSample.lean`,
`CallRound.lean` and `CallPack.lean`, for the primitives signing calls and
key generation does not: `vg_mldsa_expand_mask_poly`, `vg_mldsa_high_bits`,
`vg_mldsa_low_bits`, `vg_mldsa_make_hint` and `vg_mldsa_hint_bit_pack`.

Signing branches on the results of the two samplers, so it needs them to be
the same in two runs whose samplers' public data agree: a callee whose
result is public in its own runs (`RetPub`) returns the same in both
(`RelCT.callRet`, `callAtK_trRet`). And its leakage is stated for
`maxBounds`, so it needs that a sampler succeeds only if the algorithm
finishes within them: a fact of each run of the callee added to its
postcondition (`withPost`, `CalleeOk.withPost`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Results that are public -/

/-- The result `w0` of `c` is the same in two runs from states that satisfy
`k.pre` and agree on `k.pub`. -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c
    fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32

/-- The run of verified code from a state with more permissions than its
contract gives it is the run its contract describes, but for the permissions. -/
theorem run_narrow {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {t : List Leak} {s' : State}
    (he : Exec isa c s t s') : ∃ s'', Exec isa c (s.withRegions rd wr) t s'' ∧ s''.gpr = s'.gpr := by
  obtain ⟨t', s'', he', -⟩ := hv _ hpre
  have hw' := Exec.widen he' (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨rfl, rfl⟩ := Exec.det he hw'
  exact ⟨_, he', rfl⟩

/-- A call of verified code whose result is public in its own runs: the same
trace, and the same result. -/
theorem RelCT.callRet {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.callEntry.withRegions rd wr) ∧ k.pre (s₂.callEntry.withRegions rd wr) ∧
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ Covers wr s₁.wr ∧
      Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ Covers wr s₂.wr) :
    RelCT isa P (.call n c) fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨_, n₁, g₁⟩ := run_narrow hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨_, n₂, g₂⟩ := run_narrow hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      obtain ⟨ht, hx⟩ := hr _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ n₁ n₂
      simp only [isa, ret] at r₁ r₂
      split at r₁ <;> [skip; cases r₁]
      split at r₂ <;> [skip; cases r₂]
      cases r₁; cases r₂
      refine ⟨by simp only [ht], ?_⟩
      show (s₁'.gpr .x0).setWidth 32 = (s₂'.gpr .x0).setWidth 32
      rw [← g₁, ← g₂]; exact hx

/-- The trace of the moves then a call whose result is public: the same
trace, and the same result, in both runs. -/
theorem callAtK_trRet {S : Nat} {n : String} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    (hr : RetPub k c) {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs) (hnd : (as.map (·.1)).Nodup)
    {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → Args as x x1 → Args as y y1 → ∃ rd wr : List Region,
      k.pre (x1.callEntry.withRegions rd wr) ∧ k.pre (y1.callEntry.withRegions rd wr) ∧
      k.pub (x1.callEntry.withRegions rd wr) (y1.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧
      Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr) :
    RelCT isa P (callAt n c as) fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ Args as x x1 ∧ Args as y y1)
      (block_nomem_tr (glue_nomem as)) (fun x y _ => ⟨glue_ok hok hnd x, glue_ok hok hnd y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.mono (RelCT.exists_ (P := fun (a : List Region × List Region) (x1 y1 : State) =>
        k.pre (x1.callEntry.withRegions a.1 a.2) ∧ k.pre (y1.callEntry.withRegions a.1 a.2) ∧
        k.pub (x1.callEntry.withRegions a.1 a.2) (y1.callEntry.withRegions a.1 a.2) ∧
        Covers (a.1 ++ a.2) (x1.rd ++ x1.wr) ∧ Covers a.2 x1.wr ∧
        Covers (a.1 ++ a.2) (y1.rd ++ y1.wr) ∧ Covers a.2 y1.wr)
      fun a => RelCT.callRet C.correct hr a.1 a.2 fun _ _ h => h)
      (fun x1 y1 ⟨x, y, hp, h1, h2⟩ => by
        obtain ⟨rd, wr, p₁, p₂, pub, c₁, w₁, c₂, w₂⟩ := hP x y x1 y1 hp h1 h2
        exact ⟨(rd, wr), p₁, p₂, pub, by rw [h1.2.rd, h1.2.wr]; exact c₁, by rw [h1.2.wr]; exact w₁,
          by rw [h2.2.rd, h2.2.wr]; exact c₂, by rw [h2.2.wr]; exact w₂⟩)
      fun _ _ h => h)

/-- `k` with the fact `X` of each run added to its postcondition. -/
def withPost (k : Contract isa) (X : State → State → Prop) : Contract isa :=
  { k with post := fun s s' => k.post s s' ∧ X s s' }

theorem CalleeOk.withPost {S : Nat} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    {X : State → State → Prop} (hx : ∀ s t s', k.pre s → Exec isa c s t s' → X s s') :
    CalleeOk S c (withPost k X) :=
  ⟨fun s hs => let ⟨t, s', e, a, p⟩ := C.correct s hs; ⟨t, s', e, a, p, hx s t s' hs e⟩, C.ct, C.fd⟩

/-- A sampler's call leaves the result `w0` public in two runs whose seeds agree. -/
theorem rejNttAtK_trRet {S : Nat} {P : Prims} (C : CalleeOk S P.rejNTT (rejNTTContract AArch64.abi S))
    (hr : RetPub (rejNTTContract AArch64.abi S) P.rejNTT)
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rejNttChk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 34 = bytesAt y.mem (pa y seed) 34 ∧ SameB x y) :
    RelCT isa Q (callAt "vg_mldsa_rej_ntt_poly" P.rejNTT (rejNttArgs seed a ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hc' := hc
  simp only [rejNttChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAtK_trRet C hr (rejNtt_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rejNtt_pre Lx hc h1, ?_, ?_, (rejNtt_cov Lx hc).1, (rejNtt_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rejNtt_pre Ly hc h2
  · sig_pub [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rejNtt_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rejNtt_cov Ly hc).2

theorem ballAtK_trRet {S : Nat} {P : Prims} (C : CalleeOk S P.ball (sampleInBallContract AArch64.abi S))
    (hr : RetPub (sampleInBallContract AArch64.abi S) P.ball)
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {ct c ss : Ptr} {len : Nat}
    (hc : ballChk rbs wbs ct len c ss = true) {tau : Nat} (ht : (len, tau) ∈ ballParams) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x ct) len = bytesAt y.mem (pa y ct) len ∧ SameB x y) :
    RelCT isa Q (callAt "vg_mldsa_sample_in_ball" P.ball (ballArgs ct len tau c ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ht; omega
  have hc' := hc
  simp only [ballChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : ct.1 ∈ bases ∧ c.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAtK_trRet C hr (ball_args hB len tau c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, ball_pre Lx hc ht h1, ?_, ?_, (ball_cov Lx hc).1, (ball_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact ball_pre Ly hc ht h2
  · sig_pub [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, trivial, trivial, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (ball_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (ball_cov Ly hc).2

/-! ## `ExpandMask` -/

def maskChk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  sepB (rbs ++ wbs) seed 66 a 1024 && sepB (rbs ++ wbs) seed 66 ss 2048 && sepB (rbs ++ wbs) a 1024 ss 2048 &&
    inB (rbs ++ wbs) seed 66 && inB (rbs ++ wbs) a 1024 && inB (rbs ++ wbs) ss 2048 && inB wbs a 1024 &&
    inB wbs ss 2048

abbrev maskArgs (seed : Ptr) (γ : Nat) (a ss : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr seed), (.x1, .imm γ), (.x2, .ptr a), (.x3, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : maskChk rbs wbs seed a ss = true)
include L hc

theorem mask_cov : Covers ([⟨pa s seed, 66⟩] ++ [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩] s.wr := by
  simp only [maskChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨covers_append (L.cR c4) (covers_wr (covers_cons (L.cW c7) (L.cW c8))), covers_cons (L.cW c7) (L.cW c8)⟩

theorem mask_pre {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) {s1 : State} (h1 : Args (maskArgs seed γ a ss) s s1) :
    (expandMaskContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s seed, 66⟩] [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩]) := by
  simp only [maskChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1]
  simp only [Arg.val]
  rw [imm32 (by omega)]
  cpre L
  exact hγ

end

theorem mask_args {bs : List (Reg × Nat)} (L : LayOk bs) {seed a ss : Ptr} (γ : Nat) (c4 : inB bs seed 66 = true)
    (c5 : inB bs a 1024 = true) (c6 : inB bs ss 2048 = true) :
    ∀ x ∈ maskArgs seed γ a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c4), by decide⟩, ⟨trivial, by decide⟩, ⟨ptr_ok (ptr_bs L c5), by decide⟩,
    ⟨ptr_ok (ptr_bs L c6), by decide⟩⟩

theorem maskAtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : maskChk rbs wbs seed a ss = true) {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) :
    WP isa (callAt "vg_mldsa_expand_mask_poly" P.expandMask (maskArgs seed γ a ss)) s fun s' =>
      PPostB S s s' [(a, 1024), (ss, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s a) (toRq (bitUnpack (H (bytesAt s.mem (pa s seed) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) := by
  have hc' := hc
  simp only [maskChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAtK_ok hS C (mask_args L.ok γ c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => mask_pre L hc hγ h1) (mask_cov L hc).1 (mask_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [imm32 (by omega)] at hq
  exact hq

theorem maskAtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : maskChk rbs wbs seed a ss = true)
    {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ SameB x y) :
    RelCT isa Q (callAt "vg_mldsa_expand_mask_poly" P.expandMask (maskArgs seed γ a ss)) fun _ _ => True := by
  have hc' := hc
  simp only [maskChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAtK_tr C (mask_args hB γ c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, mask_pre Lx hc hγ h1, ?_, ?_, (mask_cov Lx hc).1, (mask_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact mask_pre Ly hc hγ h2
  · sig_pub [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, trivial, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (mask_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (mask_cov Ly hc).2

/-! ## `HighBits` and `LowBits` -/

theorem gamma2_lt {g2 : Nat} (h : g2 ∈ gamma2s) : g2 < 2 ^ 32 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

/-- The contract of `vg_mldsa_high_bits` or `vg_mldsa_low_bits`: `bitsSig`'s,
with the postcondition `Q γ₂ (the polynomial at r) m' out`. -/
abbrev bitsC (Q : Nat → Poly → Mem → Addr → Prop) (S : Nat) : Contract isa :=
  bitsSig.contract AArch64.abi
    (pre := fun r gamma2 _out m => gamma2.toNat ∈ gamma2s ∧ Reduced m r)
    (post := fun r gamma2 out m m' _ => Q gamma2.toNat (polyAt m r) m' out)
    (writeArgs := true)
    (stack := S)

abbrev bitsArgs (r : Ptr) (g2 : Nat) (out : Ptr) : List (Reg × Arg) := [(.x0, .ptr r), (.x1, .imm g2), (.x2, .ptr out)]

theorem bits_args {bs : List (Reg × Nat)} (L : LayOk bs) {r out : Ptr} (g2 : Nat) (c2 : inB bs r 1024 = true)
    (c3 : inB bs out 1024 = true) : ∀ x ∈ bitsArgs r g2 out, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨ptr_ok (ptr_bs L c3), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {r out : Ptr}
  (hc : rwChk rbs wbs r 1024 out 1024 = true)
include L hc

theorem bits_pre {Q : Nat → Poly → Mem → Addr → Prop} {g2 : Nat} (hg : g2 ∈ gamma2s) (hr : Reduced s.mem (pa s r))
    {s1 : State} (h1 : Args (bitsArgs r g2 out) s s1) :
    (bitsC Q S).pre (s1.callEntry.withRegions [⟨pa s r, 1024⟩] [⟨pa s out, 1024⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  sig_pre [bitsSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val, imm32 (gamma2_lt hg)]
  cpre L
  exacts [hg, hr]

end

theorem bitsAtK_ok {S : Nat} (hS : S < 2 ^ 64) {Q : Nat → Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : CalleeOk S c (bitsC Q S)) {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {r out : Ptr}
    (hc : rwChk rbs wbs r 1024 out 1024 = true) {g2 : Nat} (hg : g2 ∈ gamma2s) (hr : Reduced s.mem (pa s r)) :
    WP isa (callAt n c (bitsArgs r g2 out)) s fun s' => PPostB S s s' [(out, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Q g2 (polyAt s.mem (pa s r)) s'.mem (pa s out) := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  refine WP.mono (callAtK_ok hS C (bits_args L.ok g2 c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => bits_pre L hc hg hr h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [bitsSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 (gamma2_lt hg)] at hq
  exact hq

theorem bitsAtK_tr {S : Nat} {Q : Nat → Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : CalleeOk S c (bitsC Q S)) {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {r out : Ptr}
    (hc : rwChk rbs wbs r 1024 out 1024 = true) {g2 : Nat} (hg : g2 ∈ gamma2s) {R : State → State → Prop}
    (hR : ∀ x y, R x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r) ∧
      SameB x y) :
    RelCT isa R (callAt n c (bitsArgs r g2 out)) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have hb : r.1 ∈ bases ∧ out.1 ∈ bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAtK_tr C (bits_args hB g2 c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hR x y hp
  refine ⟨_, _, bits_pre Lx hc hg rx h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2]; exact bits_pre Ly hc hg ry h2
  · sig_pub [bitsSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, trivial, e.pa hb.2⟩
  · rw [e.pa hb.1, e.pa hb.2]; exact (rw_cov Ly hc).1
  · rw [e.pa hb.2]; exact (rw_cov Ly hc).2

/-! ## `MakeHint` -/

def hintChk (rbs wbs : List (Reg × Nat)) (z r h : Ptr) : Bool :=
  sepB (rbs ++ wbs) z 1024 h 1024 && sepB (rbs ++ wbs) r 1024 h 1024 && inB (rbs ++ wbs) z 1024 &&
    inB (rbs ++ wbs) r 1024 && inB (rbs ++ wbs) h 1024 && inB wbs h 1024

abbrev hintArgs (z r : Ptr) (g2 : Nat) (h : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr z), (.x1, .ptr r), (.x2, .imm g2), (.x3, .ptr h)]

theorem hint_args {bs : List (Reg × Nat)} (L : LayOk bs) {z r h : Ptr} (g2 : Nat) (c3 : inB bs z 1024 = true)
    (c4 : inB bs r 1024 = true) (c5 : inB bs h 1024 = true) : ∀ x ∈ hintArgs z r g2 h, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c3), by decide⟩, ⟨ptr_ok (ptr_bs L c4), by decide⟩, ⟨trivial, by decide⟩,
    ⟨ptr_ok (ptr_bs L c5), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {z r h : Ptr}
  (hc : hintChk rbs wbs z r h = true)
include L hc

theorem hint_cov : Covers ([⟨pa s z, 1024⟩, ⟨pa s r, 1024⟩] ++ [⟨pa s h, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s h, 1024⟩] s.wr := by
  simp only [hintChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, _⟩, c6⟩ := hc
  exact ⟨covers_append (covers_cons (L.cR c3) (L.cR c4)) (covers_wr (L.cW c6)), L.cW c6⟩

theorem hint_pre {g2 : Nat} (hg : g2 ∈ gamma2s) (hz : Reduced s.mem (pa s z)) (hr : Reduced s.mem (pa s r))
    {s1 : State} (h1 : Args (hintArgs z r g2 h) s s1) :
    (makeHintContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s z, 1024⟩, ⟨pa s r, 1024⟩] [⟨pa s h, 1024⟩]) := by
  simp only [hintChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  sig_pre [makeHintContract, makeHintSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val, imm32 (gamma2_lt hg)]
  cpre L
  exacts [hg, hz, hr]

end

theorem hintAtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.makeHint (makeHintContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {z r h : Ptr} (hc : hintChk rbs wbs z r h = true)
    {g2 : Nat} (hg : g2 ∈ gamma2s) (hz : Reduced s.mem (pa s z)) (hr : Reduced s.mem (pa s r)) :
    WP isa (callAt "vg_mldsa_make_hint" P.makeHint (hintArgs z r g2 h)) s fun s' =>
      PPostB S s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      HintIs s'.mem (pa s h) 1 [Vector.zipWith (makeHint g2) (polyAt s.mem (pa s z)) (polyAt s.mem (pa s r))] ∧
      ((s'.gpr .x0).setWidth 32).toNat =
        hintOnes [Vector.zipWith (makeHint g2) (polyAt s.mem (pa s z)) (polyAt s.mem (pa s r))] := by
  have hc' := hc
  simp only [hintChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  refine WP.mono (callAtK_ok hS C (hint_args L.ok g2 c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => hint_pre L hc hg hz hr h1) (hint_cov L hc).1 (hint_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [makeHintContract, makeHintSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 (gamma2_lt hg)] at hq
  exact hq

theorem hintAtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.makeHint (makeHintContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {z r h : Ptr} (hc : hintChk rbs wbs z r h = true)
    {g2 : Nat} (hg : g2 ∈ gamma2s) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ (Reduced x.mem (pa x z) ∧ Reduced x.mem (pa x r)) ∧
      (Reduced y.mem (pa y z) ∧ Reduced y.mem (pa y r)) ∧ SameB x y) :
    RelCT isa Q (callAt "vg_mldsa_make_hint" P.makeHint (hintArgs z r g2 h)) fun _ _ => True := by
  have hc' := hc
  simp only [hintChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  have hb : z.1 ∈ bases ∧ r.1 ∈ bases ∧ h.1 ∈ bases := ⟨ptr_bs hB c3, ptr_bs hB c4, ptr_bs hB c5⟩
  refine callAtK_tr C (hint_args hB g2 c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, hint_pre Lx hc hg rx.1 rx.2 h1, ?_, ?_, (hint_cov Lx hc).1, (hint_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact hint_pre Ly hc hg ry.1 ry.2 h2
  · sig_pub [makeHintContract, makeHintSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, e.pa hb.2.1, trivial, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (hint_cov Ly hc).1
  · rw [e.pa hb.2.2]; exact (hint_cov Ly hc).2

/-! ## `HintBitPack` -/

abbrev hbpArgs (h : Ptr) (hlen omega : Nat) (y : Ptr) (len : Nat) : List (Reg × Arg) :=
  [(.x0, .ptr h), (.x1, .imm hlen), (.x2, .imm omega), (.x3, .ptr y), (.x4, .imm len)]

theorem hbp_args {bs : List (Reg × Nat)} (L : LayOk bs) {h y : Ptr} (hlen omega len : Nat)
    (c2 : inB bs h (hlen * 4) = true) (c3 : inB bs y len = true) :
    ∀ x ∈ hbpArgs h hlen omega y len, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩,
    ⟨ptr_ok (ptr_bs L c3), by decide⟩, ⟨trivial, by decide⟩⟩

/-- What `HintBitPack` asks of its arguments. -/
structure HbpOk (hlen omega len : Nat) : Prop where
  hp : (omega, len - omega) ∈ hintParams
  hle : omega ≤ len
  hh : hlen = 256 * (len - omega)
  hlt : hlen < 2 ^ 32 ∧ omega < 2 ^ 32 ∧ len < 2 ^ 32

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h y : Ptr} {hlen omega len : Nat}
  (hc : rwChk rbs wbs h (hlen * 4) y len = true)
include L hc

theorem hbp_pre (hb : HbpOk hlen omega len) (hn : hintOnes (hintAt s.mem (pa s h) (len - omega)) ≤ omega)
    {s1 : State} (h1 : Args (hbpArgs h hlen omega y len) s s1) :
    (hintBitPackContract AArch64.abi S).pre (s1.callEntry.withRegions [⟨pa s h, hlen * 4⟩] [⟨pa s y, len⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  have l1 := hb.hlt.1; have l2 := hb.hlt.2.1; have l3 := hb.hlt.2.2
  sig_pre [hintBitPackContract, hintBitPackSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val, imm32 l2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show hlen < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
  cpre L
  exacts [hb.hp, hb.hle, hb.hh, hn]

end

theorem hbpAtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.hintBitPack (hintBitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h y : Ptr} {hlen omega len : Nat}
    (hc : rwChk rbs wbs h (hlen * 4) y len = true) (hb : HbpOk hlen omega len)
    (hn : hintOnes (hintAt s.mem (pa s h) (len - omega)) ≤ omega) :
    WP isa (callAt "vg_mldsa_hint_bit_pack" P.hintBitPack (hbpArgs h hlen omega y len)) s fun s' =>
      PPostB S s s' [(y, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s y) len = hintBitPack omega (len - omega) (hintAt s.mem (pa s h) (len - omega)) := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have l1 := hb.hlt.1; have l2 := hb.hlt.2.1; have l3 := hb.hlt.2.2
  refine WP.mono (callAtK_ok hS C (hbp_args L.ok hlen omega len c2 c3)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => hbp_pre L hc hb hn h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [hintBitPackContract, hintBitPackSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 l2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)] at hq
  exact hq

theorem hbpAtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.hintBitPack (hintBitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {h y : Ptr} {hlen omega len : Nat}
    (hc : rwChk rbs wbs h (hlen * 4) y len = true) (hb : HbpOk hlen omega len) {Q : State → State → Prop}
    (hQ : ∀ x y', Q x y' → Lay S rbs wbs x ∧ Lay S rbs wbs y' ∧
      hintOnes (hintAt x.mem (pa x h) (len - omega)) ≤ omega ∧
      hintOnes (hintAt y'.mem (pa y' h) (len - omega)) ≤ omega ∧
      (List.range hlen).map (fun i => (coeffAt x.mem (pa x h) i).toNat) =
        (List.range hlen).map (fun i => (coeffAt y'.mem (pa y' h) i).toNat) ∧ SameB x y') :
    RelCT isa Q (callAt "vg_mldsa_hint_bit_pack" P.hintBitPack (hbpArgs h hlen omega y len)) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have l1 := hb.hlt.1; have l2 := hb.hlt.2.1; have l3 := hb.hlt.2.2
  have hbs : h.1 ∈ bases ∧ y.1 ∈ bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAtK_tr C (hbp_args hB hlen omega len c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y' x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, nx, ny, hl, e⟩ := hQ x y' hp
  refine ⟨_, _, hbp_pre Lx hc hb nx h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact hbp_pre Ly hc hb ny h2
  · sig_pub [hintBitPackContract, hintBitPackSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show hlen < 2 ^ 64 by omega)]
    exact ⟨e.2, hl, e.pa hbs.1, trivial, trivial, e.pa hbs.2, trivial⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (rw_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.Sign
