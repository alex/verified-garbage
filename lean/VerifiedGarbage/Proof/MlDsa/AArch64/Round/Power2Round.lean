import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic

/-!
# ML-DSA on AArch64: `vg_mldsa_power2round`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Arith (Qv toNat_setWidth64 q32 movW_ok)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa

/-- A value `v` plus `q` if it is negative (as a 64-bit number). -/
abbrev addQ (v : BitVec 64) : BitVec 64 := v + (v >>> 63) * Qv

/-- `a + 4095`, in 64 bits. -/
abbrev p2rX (x : BitVec 32) : BitVec 64 := x.setWidth 64 + BitVec.ofNat 64 4095

/-- The `t1` the body stores. -/
def t1V (x : BitVec 32) : BitVec 32 := (p2rX x >>> 13).setWidth 32

/-- The `t0` the body stores. -/
def t0V (x : BitVec 32) : BitVec 32 :=
  (addQ (p2rX x - (p2rX x >>> 13) <<< 13 - BitVec.ofNat 64 4095)).setWidth 32

theorem p2rBody_ok (s : State) (hq : s.gpr .x9 = Qv) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4)
    (h1 : InRegions s.wr (s.gpr .x1) 4) (h2 : InRegions s.wr (s.gpr .x2) 4) :
    WP isa (.block (p2rBody ++ [Reg.x0, .x1, .x2].map (fun p => .addImm .x p p 4) ++
      [.subImm .x .x10 .x10 1])) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .x1) (t1V (s.mem.readW (s.gpr .x0) 32))).writeW (s.gpr .x2)
          (t0V (s.mem.readW (s.gpr .x0) 32)) ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧ s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4 ∧
        s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧ s'.gpr .x10 = s.gpr .x10 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x1, .x2, .x10, .x11, .x12, .x13] s s' := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by decide)
  unfold p2rBody
  arun [h0, h1, h2, hq, t1V, t0V, List.map_cons, List.map_nil]

theorem p2rX_toNat {x : BitVec 32} (hx : x.toNat < q) : (p2rX x).toNat = x.toNat + 4095 := by
  have hq : q = 8380417 := rfl
  rw [BitVec.toNat_add, toNat_setWidth64, BitVec.toNat_ofNat]
  omega

theorem t1V_toNat {x : BitVec 32} (hx : x.toNat < q) : (t1V x).toNat = (x.toNat + 4095) / 8192 := by
  have hq : q = 8380417 := rfl
  have e : (p2rX x >>> 13).toNat = (x.toNat + 4095) / 8192 := by
    rw [BitVec.toNat_ushiftRight, p2rX_toNat hx, Nat.shiftRight_eq_div_pow]
  rw [t1V, BitVec.toNat_setWidth, e]
  omega

/-- `v - k` plus `q` if negative, for `v < 2³²` and `k ≤ q`: `v + q - k` if
`v < k`, else `v - k`. -/
theorem addQ_sub_toNat {v k : BitVec 64} (hv : v.toNat < 2 ^ 32) (hk : k.toNat ≤ q) :
    (addQ (v - k)).toNat = if v.toNat < k.toNat then v.toNat + q - k.toNat else v.toNat - k.toNat := by
  have hq : q = 8380417 := rfl
  have hQ : Qv.toNat = 8380417 := rfl
  have hsub : (v - k).toNat = if v.toNat < k.toNat then 2 ^ 64 - k.toNat + v.toNat else v.toNat - k.toNat := by
    rw [BitVec.toNat_sub]
    split <;> omega
  have hsh : ((v - k) >>> 63).toNat = if v.toNat < k.toNat then 1 else 0 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hsub]
    split <;> omega
  rw [addQ, BitVec.toNat_add, BitVec.toNat_mul, hsh, hsub, hQ]
  split <;> omega

theorem t0V_toNat {x : BitVec 32} (hx : x.toNat < q) :
    (t0V x).toNat = if (x.toNat + 4095) % 8192 < 4095 then (x.toNat + 4095) % 8192 + q - 4095
      else (x.toNat + 4095) % 8192 - 4095 := by
  have hq : q = 8380417 := rfl
  have e1 : (p2rX x - (p2rX x >>> 13) <<< 13).toNat = (x.toNat + 4095) % 8192 := by
    have h2 : ((p2rX x >>> 13) <<< 13).toNat = (x.toNat + 4095) / 8192 * 8192 := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, p2rX_toNat hx, Nat.shiftRight_eq_div_pow,
        Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub, h2, p2rX_toNat hx]
    omega
  have hr := Nat.mod_lt (x.toNat + 4095) (show 8192 > 0 by decide)
  have h4095 : (BitVec.ofNat 64 4095).toNat = 4095 := rfl
  rw [t0V, BitVec.toNat_setWidth, addQ_sub_toNat (by rw [e1]; omega) (by rw [h4095, hq]; omega), e1, h4095]
  split <;> omega

section
variable {s₀ : State} (hp : power2RoundK.pre s₀)
include hp

theorem p2r_layout : Layout s₀ [.x0] [.x1, .x2] where
  rd p hp' := by
    simp only [List.mem_singleton] at hp'; subst hp'; rw [hp.1]; simp
  wr o ho := by
    rw [hp.2.1]; simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
    rcases ho with rfl | rfl <;> simp
  dis p hp' o ho := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp' ho
    subst hp'
    rcases ho with rfl | rfl
    exacts [hp.2.2.1, hp.2.2.2.1]
  pw := List.pairwise_cons.mpr ⟨fun b hb => by
    simp only [List.mem_singleton] at hb; subst hb; exact hp.2.2.2.2.1, List.pairwise_singleton _ _⟩

/-- The values the loop writes. -/
def p2rV (s₀ : State) (o : Reg) (k : Nat) : BitVec 32 :=
  if o = .x1 then t1V (coeffAt s₀.mem (s₀.gpr .x0) k) else t0V (coeffAt s₀.mem (s₀.gpr .x0) k)

theorem p2r_loop (sL : State) (hk : Keep [.x9] s₀ sL) (hm : sL.mem = s₀.mem) (hq : sL.gpr .x9 = Qv) :
    WP isa (mapLoop [.x0, .x1, .x2] .x10 p2rBody) sL
      (Inv sL [.x0, .x1, .x2] [.x9] [.x1, .x2] (p2rV s₀) (fun _ _ => True) 256) := by
  have hL : Layout sL [.x0] [.x1, .x2] := (p2r_layout hp).congr (fun r hr => hk.get r (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl <;> decide)) hk.rd hk.wr
  refine loop_ok (clob := [.x0, .x1, .x2, .x10, .x11, .x12, .x13]) hL (by decide) (by decide) (by decide)
    (by decide) (fun _ _ _ => trivial) fun i hi s hI => ?_
  refine WP.mono (p2rBody_ok s (by rw [hI.fixed .x9 (by simp), hq]) (hI.inR hL (by simp) (by simp) hi)
    (hI.inW hL (by simp) (by simp) hi) (hI.inW hL (by simp) (by simp) hi))
    fun s' ⟨⟨hm', h0, h1, h2, hc⟩, hk'⟩ => ⟨⟨?_, fun p hp' => ?_, hc, trivial⟩, hk'⟩
  · rw [hm', hI.read hL (by simp) (by simp) hi, hm]
    simp [writes, p2rV, hk.get .x0]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    exacts [h0, h1, h2]

end

theorem p2r_correct (s₀ : State) (hp : power2RoundK.pre s₀) :
    ∃ t s', Exec isa power2Round s₀ t s' ∧ abiPreserved s₀ s' ∧ power2RoundK.post s₀ s' := by
  have hr : Reduced s₀.mem (s₀.gpr .x0) := hp.2.2.2.2.2
  obtain ⟨t, s', he, sL, hk, hm, hI⟩ := WP.seq (M := isa) (Q := fun s' => ∃ sL, Keep [.x9] s₀ sL ∧
      sL.mem = s₀.mem ∧ Inv sL [.x0, .x1, .x2] [.x9] [.x1, .x2] (p2rV s₀) (fun _ _ => True) 256 s')
    (WP.mono (movW_ok .x9 (BitVec.ofNat 32 Impl.MlDsa.AArch64.Arith.qNat) s₀) fun sL ⟨⟨hq, hm⟩, hk⟩ =>
      WP.mono (p2r_loop hp sL hk hm (by rw [hq]; exact q32)) fun s' hI => ⟨sL, hk, hm, hI⟩)
  have e : ∀ r ∈ [Reg.x0, .x1, .x2], sL.gpr r = s₀.gpr r := fun r hr => hk.get r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)
  refine ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he, ?_, ?_⟩
  · refine natPolyIs_of_toNat fun k hk' => ?_
    rw [← e .x1 (by simp), hI.done .x1 (by simp) k hk', map_get _ _ hk', p2rV, ite_eq_left rfl,
      t1V_toNat (hr k hk'), power2Round_eq, ← polyAt_val hr hk']
    exact (Int.toNat_natCast _).symm
  · refine polyIs_of_toNat fun k hk' => ?_
    rw [← e .x2 (by simp), hI.done .x2 (by simp) k hk', map_get _ _ hk', p2rV, ite_eq_right (by decide),
      t0V_toNat (hr k hk'), power2Round_t0, polyAt_val hr hk']

theorem p2r_ct : ConstantTime isa power2RoundK.pre power2RoundK.pub power2Round :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ hp => VG.Proof.MlDsa.AArch64.Arith.agree_regs hp.2.2.2 fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def p2rSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]

theorem power2Round_verified :
    Verified AArch64.target power2Round (power2RoundContract AArch64.abi) :=
  Verified.of_correct p2r_correct p2r_ct (by
    mldsa_implies [power2RoundContract, power2RoundSig, power2RoundK, AArch64.abi, AArch64.argRegs] [p2rSat]
      using p2rSat)

end VG.Proof.MlDsa.AArch64.Round
