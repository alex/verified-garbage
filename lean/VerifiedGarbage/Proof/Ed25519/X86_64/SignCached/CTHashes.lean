import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.CTHash

/-! All three signing hashes leak only their pointers and lengths. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)

theorem input_ct (v : Compress) (source count : Nat) (hs : source + 8 ≤ 248) (hc : count < 2 ^ 32)
    (p : Lay → Addr) (hi : ∀ L, L.Ok → Input L ⟨p L, 32⟩)
    (hp : ∀ L g mx m (t : State), Ctx L g mx m t →
      t.mem.readW (L.B + BitVec.ofNat 64 (16 + source)) 64 = p L)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (inputArgs source count)) hint).isSome = true) :
    RelCT isa (Two fun _ _ _ => True) (update v.callee v.suffix (inputArgs source count))
      (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block (inputArgs source count))
      (Two fun L _ => UpdArgs L (BitVec.ofNat 64 count) (p L) 32) :=
    two_blk ht fun L g mx m t _ h _ => WP.mono (inputArgs_ok h source count hs hc (p L) (hp L g mx m t h))
      fun _ ⟨h', _, ha⟩ => ⟨h', ha⟩
  exact b.seq (upd_ct v (fun _ => BitVec.ofNat 64 count) p (fun _ => 32) hi)

theorem message_ct (v : Compress) (count : Nat) (hc : count < 2 ^ 32)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (messageArgs count)) hint).isSome = true) :
    RelCT isa (Two fun _ _ _ => True) (update v.callee v.suffix (messageArgs count))
      (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block (messageArgs count))
      (Two fun L _ => UpdArgs L (BitVec.ofNat 64 count) L.msg L.len) :=
    two_blk ht fun _ _ _ _ _ _ h _ => WP.mono (messageArgs_ok h count hc)
      fun _ ⟨h', _, ha⟩ => ⟨h', ha⟩
  exact b.seq (upd_ct v (fun _ => BitVec.ofNat 64 count) Lay.msg Lay.len
    (fun _ hL => (stable_input hL (by simp [Lay.inputs])).toInput))

theorem hashSeed_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (hashSeed v.callee v.suffix) (Two fun _ _ _ => True) :=
  init_ct.seq ((input_ct v fSeed 0 (by decide) (by decide) Lay.seed
    (fun _ hL => (stable_input hL (by simp [Lay.inputs])).toInput)
    (fun _ _ _ _ _ h => h.pSeed) (by taint_decide)).seq
    (finalize_ct v 32 (by decide) false (by taint_decide)))

theorem hashNonce_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (hashNonce v.callee v.suffix) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block prefixArgs)
      (Two fun L _ => UpdArgs L 0 (L.B + BitVec.ofNat 64 48) 32) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ h _ => WP.mono (prefixArgs_ok h)
      fun _ ⟨h', _, ha⟩ => ⟨h', ha⟩
  exact init_ct.seq ((b.seq (upd_ct v (fun _ => 0) (fun L => L.B + BitVec.ofNat 64 48) (fun _ => 32)
    (fun _ hL => (stable_prefix hL).toInput))).seq
    ((message_ct v 32 (by decide) (by taint_decide)).seq (finalize_ct v 32 (by decide) true (by taint_decide))))

theorem hashChallenge_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (hashChallenge v.callee v.suffix) (Two fun _ _ _ => True) :=
  init_ct.seq ((input_ct v fOut 0 (by decide) (by decide) Lay.out
    (fun _ hL => (stable_out hL).toInput) (fun _ _ _ _ _ h => h.pOut) (by taint_decide)).seq
    ((input_ct v fPublicKey 32 (by decide) (by decide) Lay.pk
      (fun _ hL => (stable_input hL (by simp [Lay.inputs])).toInput)
      (fun _ _ _ _ _ h => h.pPk) (by taint_decide)).seq
    ((message_ct v 64 (by decide) (by taint_decide)).seq (finalize_ct v 64 (by decide) true (by taint_decide)))))

end VG.Proof.Ed25519.X86_64.SignCached
