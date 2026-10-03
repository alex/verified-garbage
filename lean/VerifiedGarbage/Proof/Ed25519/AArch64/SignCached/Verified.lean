import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Body
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Entry
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTReady
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.Contract

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Correct`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem body_depth (v : Whole.Backend) : (body v.code v.suffix).aarch64Depth ≤ 1 := by
  have hu := Whole.update_depth v
  have hf := Whole.finalize_depth v
  change (Impl.Sha512.AArch64.Stream.updateWith v.suffix v.code).aarch64Depth ≤ 1 at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith v.suffix v.code).aarch64Depth ≤ 1 at hf
  have hr := Whole.depth_zero_of_noFrames reduce_noFrames
  have hb := Whole.depth_zero_of_noFrames base_noFrames
  have hm := Whole.depth_zero_of_noFrames mul_noFrames
  simp only [body, secretCode, nonceCode, challengeCode, hashSeed, hashNonce, hashChallenge,
    init, update, finalize, reduce, Impl.Ed25519.AArch64.Whole.callWith, Code.aarch64Depth,
    Impl.Sha512.AArch64.Stream.init, hr, hb, hm]
  omega

theorem signCached_ok (v : Whole.Backend) {s : State} (h : signCachedLocal.pre s) :
    WP isa (code v.code v.suffix) s fun u => abiPreserved s u ∧ signCachedLocal.post s u := by
  have hw := Whole.wrap_ok (body_depth v) (entry_below h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (s.gpr .x0) 64 = Spec.Ed25519.sign
      (Spec.Ed25519.bytesAt m (s.gpr .x1) 32)
      (Spec.Ed25519.bytesAt m (s.gpr .x3) (s.gpr .x4).toNat))
    (fun p hp => WP.mono (body_ok v (entry_ctx h hp) (lay_ok h) (entry_args hp) (entry_key h hp))
      fun u ⟨hu, ho⟩ => ⟨by
        simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.PK, Lay.MSG,
          Lay.OUT, Lay.SCR, Lay.ARGS, Whole.ARGS, show BitVec.ofNat 64 256 = (256 : Addr) from rfl, lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs := entry_input h hf (r := ⟨s.gpr .x1, 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  have hm := entry_input h hf (r := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩) (by rw [h.1]; simp)
    (Nat.le_of_lt (s.gpr .x4).isLt)
  change Spec.Ed25519.bytesAt u.mem (s.gpr .x0) 64 = _
  rw [hp, hs, hm]

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTBody`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTHash`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem init_call_ct :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 5 0)]))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct (Proof.Sha512.AArch64.Stream.init_verified _).1
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 (Whole.depth_of_noFrames rfl)
  · intro g v m t _ hs
    have h := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at h
    rw [BitVec.add_zero] at h
    exact init_ready h
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide), hsp⟩

theorem update_call_ct (backend : Backend) (hL : L.Ok) (count : Nat) (p n : Value)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L
      [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)]))
      (.call (Spec.Sha512.updateApi.name ++ backend.suffix) backend.update)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct backend.update_verified.1 backend.update_verified.2.1 (Whole.update_depth backend)
  · intro g v m t hc hs
    have a0 := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    rw [BitVec.add_zero] at a0
    exact update_ready hL hc.sp hi ⟨a0, hs (.x1, .const count) (by simp), hs (.x2, p) (by simp),
      hs (.x3, n) (by simp), hs (.x4, .caller 5 192) (by simp)⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .const count)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x2, p)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x3, n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x4, .caller 5 192)) h (by simp) (by decide), hsp⟩

theorem finalize_call_ct (backend : Backend) (hL : L.Ok) (n : Nat) (b : Bool) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L
      [(.x0, .caller 5 0), (.x1, if b then .caller 4 n else .const n),
        (.x2, .frame 192), (.x3, .caller 5 192)]))
      (.call (Spec.Sha512.finalizeApi.name ++ backend.suffix) backend.finalize)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct backend.finalize_verified.1 backend.finalize_verified.2.1 (Whole.finalize_depth backend)
  · intro g v m t hc hs
    have a0 := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    rw [BitVec.add_zero] at a0
    exact finalize_ready hL hc.sp ⟨a0, hs (.x1, if b then .caller 4 n else .const n) (by simp),
      hs (.x2, .frame 192) (by simp), hs (.x3, .caller 5 192) (by simp)⟩
  · intro a c ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, if b then .caller 4 n else .const n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x2, .frame 192)) h (by simp) (by decide),
      call_gpr_eq (p := (.x3, .caller 5 192)) h (by simp) (by decide), hsp⟩

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) init
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 5 0)] (by decide) (by simp [Whole.valid])
    (by simp [preserved]) (by taint_decide)).seq init_call_ct

theorem update_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hc : count < 65536) (hp : Whole.valid p) (hn : Whole.valid n)
    (hi : Input L (value L p) (value L n))
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup
      [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)])) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (update backend.code backend.suffix (setup
        [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)]))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : ∀ x : Reg × Value, x ∈ [(.x0, .caller 5 0), (.x1, .const count),
      (.x2, p), (.x3, n), (.x4, .caller 5 192)] → Whole.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · exact hc
    · exact hp
    · exact hn
    · simp [Whole.valid]
  exact (setup_ct hL ha hb _ (by simp) hv (by simp [preserved]) ht).seq
    (update_call_ct backend hL count p n hi)

theorem finalize_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 4096) (b : Bool)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (finalize backend.code backend.suffix n b)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (if b then .caller 4 n else .const n) := by
    cases b <;> simp [Whole.valid] <;> omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.x0, .caller 5 0),
      (.x1, if b then .caller 4 n else .const n), (.x2, .frame 192), (.x3, .caller 5 192)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · exact hv
    · simp [Whole.valid]
    · simp [Whole.valid]
  exact (setup_ct hL ha hb _ (by simp) hvall (by simp [preserved]) ht).seq
    (finalize_call_ct backend hL n b)

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTHashPipeline`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem hashSeed_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hashSeed backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hi : Input L (value L (.caller 1 0)) (value L (.const 32)) := by
    change Input L (L.seed + 0#64) 32#64
    rw [BitVec.add_zero]
    exact seed_input hL
  exact (init_ct hL ha hb).seq ((update_ct backend hL ha hb 0 (.caller 1 0) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hi (by taint_decide)).seq
    (finalize_ct backend hL ha hb 32 (by decide) false (by taint_decide)))

theorem hashNonce_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hashNonce backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hp : Input L (value L (.frame 64)) (value L (.const 32)) := prefix_input hL
  have hm : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    change Input L (L.msg + 0#64) (L.len + 0#64)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact message_input hL
  exact (init_ct hL ha hb).seq ((update_ct backend hL ha hb 0 (.frame 64) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hp (by taint_decide)).seq
    ((update_ct backend hL ha hb 32 (.caller 3 0) (.caller 4 0)
      (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hm (by taint_decide)).seq
      (finalize_ct backend hL ha hb 32 (by decide) true (by taint_decide))))

theorem hashChallenge_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hashChallenge backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have ho : Input L (value L (.caller 0 0)) (value L (.const 32)) := by
    change Input L (L.out + 0#64) 32#64
    rw [BitVec.add_zero]
    exact point_input hL
  have hk : Input L (value L (.caller 2 0)) (value L (.const 32)) := by
    change Input L (L.pk + 0#64) 32#64
    rw [BitVec.add_zero]
    exact key_input hL
  have hm : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    change Input L (L.msg + 0#64) (L.len + 0#64)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact message_input hL
  exact (init_ct hL ha hb).seq ((update_ct backend hL ha hb 0 (.caller 0 0) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) ho (by taint_decide)).seq
    ((update_ct backend hL ha hb 32 (.caller 2 0) (.const 32)
      (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hk (by taint_decide)).seq
      ((update_ct backend hL ha hb 64 (.caller 3 0) (.caller 4 0)
        (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hm (by taint_decide)).seq
        (finalize_ct backend hL ha hb 64 (by decide) true (by taint_decide)))))

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTPrimitives`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (d : Nat) (hd : d + 32 ≤ 256) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarReduce_ok scalarReduce_ct (Whole.depth_of_noFrames reduce_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0, .frame d) (by simp)
    have a1 := hs (.x1, .frame 192) (by simp)
    have a2 := hs (.x2, .caller 5 0) (by simp)
    change t.gpr .x2 = L.scr + 0#64 at a2
    rw [BitVec.add_zero] at a2
    exact reduce_ready hL hd ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .frame d)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x1, .frame 192)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .caller 5 0)) h (by simp) (by decide)⟩

theorem base_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)]))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarBase_ok scalarBase_ct (Whole.depth_of_noFrames base_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0, .caller 0 0) (by simp)
    change t.gpr .x0 = L.out + 0#64 at a0
    rw [BitVec.add_zero] at a0
    have a1 := hs (.x1, .frame 96) (by simp)
    have a2 := hs (.x2, .caller 5 0) (by simp)
    change t.gpr .x2 = L.scr + 0#64 at a2
    rw [BitVec.add_zero] at a2
    exact base_ready hL ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .caller 0 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .frame 96)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .caller 5 0)) h (by simp) (by decide)⟩

theorem mul_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128), (.x3, .frame 32), (.x4, .caller 5 0)]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.AArch64.scalarMulAdd)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarMulAdd_ok scalarMulAdd_ct (Whole.depth_of_noFrames mul_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0, .caller 0 32) (by simp)
    have a1 := hs (.x1, .frame 96) (by simp)
    have a2 := hs (.x2, .frame 128) (by simp)
    have a3 := hs (.x3, .frame 32) (by simp)
    have a4 := hs (.x4, .caller 5 0) (by simp)
    change t.gpr .x4 = L.scr + 0#64 at a4
    rw [BitVec.add_zero] at a4
    exact mul_ready hL ⟨a0, a1, a2, a3, a4⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .caller 0 32)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .frame 96)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .frame 128)) h (by simp) (by decide),
      call_gpr_eq (p := (.x3, .frame 32)) h (by simp) (by decide),
      call_gpr_eq (p := (.x4, .caller 5 0)) h (by simp) (by decide)⟩

theorem saveSecret_ct :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (saveSecret_ok hc rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (saveSecret_ok hc rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (d : Nat) (hd : d + 32 ≤ 256)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (reduceArgs d)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (reduce d)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (.frame d) := by change d < 4096; omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · exact hv
    · simp [Whole.valid]
    · simp [Whole.valid]
  exact (setup_ct hL ha hb _ (by simp) hvall (by simp [preserved]) ht).seq
    (reduce_call_ct hL d hd)

theorem base_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)]
    (by decide) (by simp [Whole.valid]) (by simp [preserved]) (by taint_decide)).seq
    (base_call_ct hL)

theorem mul_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (callWith mulAddArgs "vg_ed25519_scalar_mul_add" Impl.Ed25519.AArch64.scalarMulAdd)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128),
    (.x3, .frame 32), (.x4, .caller 5 0)]
    (by decide) (by simp [Whole.valid]) (by simp [preserved]) (by taint_decide)).seq
    (mul_call_ct hL)

theorem body_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  ((hashSeed_ct backend hL ha hb).seq saveSecret_ct).seq
    (((hashNonce_ct backend hL ha hb).seq ((reduce_ct hL ha hb 96 (by decide) (by taint_decide)).seq
      (base_ct hL ha hb))).seq
      (((hashChallenge_ct backend hL ha hb).seq ((reduce_ct hL ha hb 128 (by decide) (by taint_decide)).seq
        (mul_ct hL ha hb))).seq (wipe_ct hL)))

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CT`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem lay_eq {s t : State} (hp : signCachedLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, h3, h4, h5]

theorem signCached_ct (v : Whole.Backend) :
    ConstantTime isa signCachedLocal.pre signCachedLocal.pub (code v.code v.suffix) := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok v (entry_ctx hs hp) (lay_ok hs) (entry_args hp) (entry_key hs hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args hqb
    exact ⟨(body_ct v (lay_ok hs) (entry_args hpa) hqa _ _ _ _ _ _
      ⟨entry_ctx hs hpa, hq, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Contract`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.Sat`. -/
section
/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else if a.toNat < 0x3020 then satKey[a.toNat - 0x3000]?.getD 0
  else 0

theorem sat_seed : Spec.Ed25519.bytesAt satMem 0x2000 32 = satSeed := by
  unfold satSeed Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed25519.bytesAt satMem 0x3000 32 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, show 0x3000 + i < 0x3020 from by omega, ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x5 => 0x5000 | _ => 0
  sp := 0x9000
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed25519.signCachedContract AArch64.abi 352).pre s := by
  refine ⟨satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, satState]
    sig_and_intros
    · decide +kernel
    · change Spec.Ed25519.bytesAt satMem 0x3000 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt satMem 0x2000 32)
      rw [sat_seed, sat_key]
      rfl

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

theorem signCached_implies : signCachedLocal.Implies (Spec.Ed25519.signCachedContract AArch64.abi 352) where
  pre := by
    sig_implies_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedLocal, below, AArch64.abi, AArch64.argRegs]
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedLocal, below, AArch64.abi, AArch64.argRegs]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedLocal, below, AArch64.abi, AArch64.argRegs]
  sat := sat

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem signCached_verified (v : Whole.Backend) :
    Verified AArch64.target (code v.code v.suffix) (Spec.Ed25519.signCachedContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => signCached_ok v h) (signCached_ct v) (.refl signCached_implies.sat_left))
    signCached_implies

end VG.Proof.Ed25519.AArch64.SignCached
