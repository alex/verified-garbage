import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Hash

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: the frame

Untrusted: everything here is checked by Lean. The frame's push of nine
registers (`rs`) holding the key, `msg`, `msg_len`, `ctx`, `ctx_len`, `sig`,
`rnd`, `scratch` and 0, then the store of `ctx_len` after the 0, give `Ctx`
(`entry_ok`); a frame whose body keeps `Ctx` returns with the permissions,
`rsp` and callee-saved registers of entry (`frame_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Spec.Sha3 (bytesAt)

/-- The values the frame's push stores, the first at `SP + 64`. -/
def Lay.vals (L : Lay) : List (BitVec 64) := [L.key, L.msg, L.len, L.ctx, L.ctxLen, L.sig, L.rnd, L.scr, 0]

theorem push_slot (B : Addr) (j : Nat) (hj : j < 9) :
    B + BitVec.ofNat 64 104 - BitVec.ofNat 64 (8 * (j + 1)) = B + BitVec.ofNat 64 32 + BitVec.ofNat 64 (64 - 8 * j) := by
  rw [add_add, Offset.sub_ofNat_eq _ (a := 8 * (j + 1)) (b := 104) (by omega), BitVec.add_sub_cancel]
  congr 2; omega

theorem push_base (B : Addr) : B + BitVec.ofNat 64 104 - BitVec.ofNat 64 (8 * 9) = B + BitVec.ofNat 64 32 := by
  have := push_slot B 8 (by omega); simpa using this

theorem setWidth8 (x : BitVec 64) (_h : x.toNat < 256) : x.setWidth 8 = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- After the push of the registers `rs` holding `L.vals` and the store of
`ctx_len`: `Ctx`. -/
theorem entry_ok {L : Lay} (hL : L.Ok) {rs : List Reg} (hlen : rs.length = 9) (hrs : .rsp ∉ rs) {s : State}
    (hsp : s.gpr .rsp = L.B + BitVec.ofNat 64 104) (hrd : s.rd = L.rd) (hwr : s.wr = L.wr)
    (hv : ∀ j (hj : j < 9), s.gpr (rs[j]'(by omega)) = L.vals[j]'(by simp [Lay.vals]; omega))
    (h8 : s.gpr .r8 = L.ctxLen) :
    WP isa (.block setHdr) (pushed rs s) fun t => Ctx L s.gpr s.mxcsr s.mem t ∧
      t.wr = (pushed rs s).wr ∧ t.gpr .rsp = (pushed rs s).gpr .rsp := by
  have hn : 8 * rs.length ≤ (s.gpr .rsp).toNat := by
    rw [hsp, hlen, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hL.nB
    rw [Nat.mod_eq_of_lt (a := 104) (by omega), Nat.mod_eq_of_lt this]; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s rs hrs hn
  have hslot : ∀ j (hj : j < 9), (pushed rs s).mem.readW (L.SP + BitVec.ofNat 64 (64 - 8 * j)) 64 =
      L.vals[j]'(by simp [Lay.vals]; omega) := fun j hj => by
    rw [← hv j hj, ← hw j (by omega), hsp, push_slot _ j hj]; rfl
  have hrsp : (pushed rs s).gpr .rsp = L.SP := by rw [pushed_rsp, hsp, hlen, push_base]
  have hwr' : (pushed rs s).wr = L.FR :: L.wr := by rw [pushed_wr, hsp, hlen, push_base, hwr]
  have hin : InRegions (pushed rs s).wr (L.SP + BitVec.ofNat 64 1) 1 :=
    ⟨L.FR, by rw [hwr']; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have h8' : (pushed rs s).gpr .r8 = L.ctxLen := by rw [pushed_gpr _ _ (by decide), h8]
  apply WP.of_runBlock
  simp only [setHdr, fHdr, runBlock_cons, runStep_some, runBlock_nil, exec, State.store8, ea_stk, hrsp,
    Nat.reduceAdd, hin, ite_true, Option.some.injEq, exists_eq_left', h8',
    setWidth8 _ hL.ctxLt]
  -- The memory after the store.
  generalize hm : (pushed rs s).mem.writeW (L.SP + BitVec.ofNat 64 1) (BitVec.ofNat 8 L.ctxLen.toNat) = m'
  have hsep : ∀ j (hj : j < 8), m'.readW (L.SP + BitVec.ofNat 64 (64 - 8 * j)) 64 =
      (pushed rs s).mem.readW (L.SP + BitVec.ofNat 64 (64 - 8 * j)) 64 := fun j hj => by
    rw [← hm]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)
  refine ⟨⟨by simp [hrd], hwr', hrsp, fun r hr hr' => pushed_gpr _ _ hr', by simp,
    (hsep 7 (by omega)).trans (hslot 7 (by omega)), (hsep 6 (by omega)).trans (hslot 6 (by omega)),
    (hsep 5 (by omega)).trans (hslot 5 (by omega)), (hsep 4 (by omega)).trans (hslot 4 (by omega)),
    (hsep 3 (by omega)).trans (hslot 3 (by omega)), (hsep 2 (by omega)).trans (hslot 2 (by omega)),
    (hsep 1 (by omega)).trans (hslot 1 (by omega)), (hsep 0 (by omega)).trans (hslot 0 (by omega)), ?_, ?_⟩,
    trivial, trivial⟩
  · -- The two bytes: the low byte of the pushed 0, and `ctx_len`.
    have h0 := hslot 8 (by omega)
    simp only [Lay.vals, Nat.reduceMul, Nat.sub_self, BitVec.add_zero] at h0
    have b0 : (pushed rs s).mem L.SP = 0 := by
      have := Mem.extractLsb'_read (pushed rs s).mem L.SP (n := 8) (j := 0) (by omega)
      simp only [BitVec.add_zero, Nat.mul_zero] at this
      rw [← this]
      have e : (pushed rs s).mem.read L.SP 8 = (pushed rs s).mem.readW L.SP 64 := by
        simp only [Mem.readW]; rfl
      rw [e, h0]; rfl
    rw [← hm]
    simp only [bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, BitVec.add_zero]
    refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
    · rw [Mem.writeW, Mem.write_apply (by
        rw [Offset.toNat_sub_add _ _ (by decide), BitVec.sub_self]; simp)]
      exact b0
    · simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.reduceDiv, Nat.lt_add_one,
        ite_true]
      ext i hi
      simp
  · show Frame [L.XS, L.STK] s.mem m'
    rw [← hm]
    have hf1 : Frame [L.STK] s.mem (pushed rs s).mem := by
      refine Frame.sub hf fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      rw [hsp, hlen, push_base]
      exact Offset.sub_base _ (by omega)
    have hf2 : Frame [L.STK] s.mem ((pushed rs s).mem.writeW (L.SP + 1#64) (BitVec.ofNat 8 L.ctxLen.toNat)) :=
      hf1.writeW (List.mem_singleton_self _) _ (by
        rw [Lay.SP, add_add]; exact Offset.contains_base _ (by omega) (by omega))
    exact hf2.mono fun r hr => by simp at hr ⊢; exact .inr hr

end VG.Proof.MlDsa.X86_64.Message
