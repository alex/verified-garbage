import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Hash
import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: `μ` and `tr`

Untrusted: everything here is checked by Lean. In `Ctx`, `muHash` leaves
`μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)` at `X + 840` (`muHash_ok`), and
`trHash` leaves `H(pk, 64)` there (`trHash_ok`): from the zeroed state, each
absorb continues the message from the position the previous one returned.
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Spec.MlDsa (Params)

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- The two bytes `0 ‖ ctx_len` of the formatted message. -/
abbrev hdrBytes (L : Lay) : List Byte := [0, BitVec.ofNat 8 L.ctxLen.toNat]

theorem ofNat_toNat_self (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; exact (ofNat_toNat_self x).symm

/-- The arguments of an absorb are fit, if its data and length are not `x0`. -/
theorem absOk {src len pos : Arg} (h1 : src.ok = true) (h2 : len.ok = true) (h3 : pos.ok = true)
    (r1 : src.isRet = false) (r2 : len.isRet = false) : argsOk (absArgs src len pos) = true := by
  simp (config := { decide := true }) [argsOk, absArgs, h1, h2, h3, r1, r2]

theorem padOk {pos : Arg} (h : pos.ok = true) : argsOk (padArgs pos) = true := by
  simp (config := { decide := true }) [argsOk, padArgs, h]

theorem Ctx.slotV {t : State} (hc : Ctx L g vv m₀ t) {f j : Nat} (hf : f = 920 + 8 * j) (hj : j < 8) :
    (Arg.slot f).val t = L.vals.getD j 0 := by
  subst hf; exact hc.slotJ hj

theorem Ctx.hdrX {t : State} (hc : Ctx L g vv m₀ t) : bytesAt t.mem (L.X + BitVec.ofNat 64 984) 2 = hdrBytes L := by
  have := hc.hdr; rwa [add_add] at this

theorem muHash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t)
    {tr : Arg} (hok : tr.ok = true) (hret : tr.isRet = false) {trp : Addr}
    (htr : ∀ t', Ctx L g vv m₀ t' → tr.val t' = trp)
    (hin : ∃ R ∈ L.rd ++ L.wr, Within ⟨trp, 64⟩ R)
    (dS : Region.Disjoint ⟨trp, 64⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨trp, 64⟩ ⟨L.KS, 640⟩)
    (kD : L.STK.Disjoint ⟨trp, 64⟩) :
    WP isa (muHash v.callee tr) t fun t' => Ctx L g vv m₀ t' ∧
      bytesAt t'.mem L.MU 64 = Spec.MlDsa.H (bytesAt t.mem trp 64 ++ hdrBytes L ++
        bytesAt m₀ L.ctx L.ctxLen.toNat ++ bytesAt m₀ L.msg L.len.toNat) 64 := by
  have hctx := hL.ctxLt
  -- Zero the state.
  refine WP.seq (WP.mono (zeroSt_ok hL hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have etr : bytesAt t1.mem trp 64 = bytesAt t.mem trp 64 :=
    Proof.MlKem.bytesAt_congr fun i hi => hf1.bytes (R := ⟨trp, 64⟩) (by simpa using dS) (by show 64 ≤ 2 ^ 64; decide) hi
  have hR1 : Repr t1.mem L.ST 136 [] := Proof.MlKem.repr_nil hz
  -- `tr`.
  refine WP.seq (WP.mono (kabs_ok v hL hc1 (absOk hok rfl rfl hret rfl) (htr t1 hc1) rfl rfl (by decide)
    (by decide) hin dS dK kD) fun t2 ⟨hc2, _, hR2, _⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  rw [List.nil_append, etr] at hR2
  -- `0 ‖ ctx_len`.
  have fS : Region.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ ⟨L.ST, 200⟩ := by
    have := Offset.disjoint L.X (d := 984) (n := 2) (e := 0) (k := 200) (by omega) (by omega) (by omega)
    simpa only [x0] using this
  have fK : Region.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ ⟨L.KS, 640⟩ :=
    Offset.disjoint L.X (d := 984) (n := 2) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  refine WP.seq (WP.mono (kabs_ok v hL hc2 (absOk rfl rfl rfl rfl rfl) (by rw [hc2.off]; rfl) rfl rfl
    (by decide) (by decide) (cov_x hL (e := 984) (k := 2) (by omega)) fS fK (hL.stk_x (by omega)))
    fun t3 ⟨hc3, _, hR3, _⟩ => ?_)
  have hR3 := hR3 _ hR2 (by rw [Proof.MlKem.bytesAt_length])
  rw [hc2.hdrX] at hR3
  -- The context string.
  have hcl : (Arg.slot fCtxLen).val t3 = BitVec.ofNat 64 L.ctxLen.toNat := by
    rw [hc3.slotV (f := fCtxLen) (j := 4) rfl (by omega), ofNat_toNat_self]; rfl
  refine WP.seq (WP.mono (kabs_ok v hL hc3 (absOk rfl rfl rfl rfl rfl)
    (by rw [hc3.slotV (f := fCtx) (j := 3) rfl (by omega)]; rfl) hcl rfl (by decide) (by omega)
    ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩
    (by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm)
    (hL.x_r hL.xCtx (e := 200) (k := 640) (by omega)).symm hL.kCtx)
    fun t4 ⟨hc4, _, hR4, hx4⟩ => ?_)
  have hR4 := hR4 _ hR3 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil])
  rw [hc3.bytesAt_eq hL.xCtx hL.kCtx (by have := hL.nCtx; omega)] at hR4
  -- The message.
  have hln : (Arg.slot fLen).val t4 = BitVec.ofNat 64 L.len.toNat := by
    rw [hc4.slotV (f := fLen) (j := 2) rfl (by omega), ofNat_toNat_self]; rfl
  refine WP.seq (WP.mono (kabs_ok v hL hc4 (absOk rfl rfl rfl rfl rfl)
    (by rw [hc4.slotV (f := fMsg) (j := 1) rfl (by omega)]; rfl) hln (ofNat_toNat_eq hx4) (Nat.mod_lt _ (by decide))
    (by have := L.len.isLt; omega) ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩
    (by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm)
    (hL.x_r hL.xMsg (e := 200) (k := 640) (by omega)).symm hL.kMsg)
    fun t5 ⟨hc5, _, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil])
  rw [hc4.bytesAt_eq hL.xMsg hL.kMsg (by have := hL.nMsg; omega)] at hR5
  -- Pad and squeeze.
  refine WP.seq (WP.mono (kpad_ok v hL hc5 (padOk rfl) (ofNat_toNat_eq hx5) (Nat.mod_lt _ (by decide)))
    fun t6 ⟨hc6, _, hS6⟩ => ?_)
  have hS6 := hS6 _ hR5 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil]; omega)
  refine WP.mono (ksqz_ok v hL hc6) fun t7 ⟨hc7, _, hm7⟩ => ⟨hc7, ?_⟩
  rw [hm7, hS6, Spec.MlDsa.H, Proof.MlKem.shake256_eq]

/-! ## `tr = H(pk, 64)` -/

theorem trHash_ok (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hL : L.Ok) (hk : L.keyLen = p.pkLen)
    {t : State} (hc : Ctx L g vv m₀ t) :
    WP isa (trHash v.callee p) t fun t' => Ctx L g vv m₀ t' ∧
      bytesAt t'.mem L.MU 64 = Spec.MlDsa.H (bytesAt m₀ L.key L.keyLen) 64 := by
  have hkl := hL.hKey.2
  refine WP.seq (WP.mono (zeroSt_ok hL hc) fun t1 ⟨hc1, _, hz⟩ => ?_)
  have hR1 : Repr t1.mem L.ST 136 [] := Proof.MlKem.repr_nil hz
  refine WP.seq (WP.mono (kabs_ok v hL hc1 (n := L.keyLen) (q := 0)
    (absOk rfl (by simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl)
    (by rw [hc1.slotV (f := fKey) (j := 0) rfl (by omega)]; rfl) (by rw [hk]; rfl) rfl (by decide) (by omega)
    ⟨L.KEY, List.mem_append_left _ hL.inKey, within_self _⟩
    (by have := hL.x_r hL.xKey (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm)
    (hL.x_r hL.xKey (e := 200) (k := 640) (by omega)).symm hL.kKey)
    fun t2 ⟨hc2, _, hR2, _⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  rw [List.nil_append, hc1.bytesAt_eq hL.xKey hL.kKey (by have := hL.nKey; omega)] at hR2
  refine WP.seq (WP.mono (kpad_ok v hL hc2 (padOk (by simp only [Arg.ok, decide_eq_true_eq]; omega))
    (q := p.pkLen % 136) rfl (Nat.mod_lt _ (by decide))) fun t3 ⟨hc3, _, hS3⟩ => ?_)
  have hS3 := hS3 _ hR2 (by rw [Proof.MlKem.bytesAt_length, hk])
  refine WP.mono (ksqz_ok v hL hc3) fun t4 ⟨hc4, _, hm4⟩ => ⟨hc4, ?_⟩
  rw [hm4, hS3, Spec.MlDsa.H, Proof.MlKem.shake256_eq]

end

end VG.Proof.MlDsa.AArch64.Message
