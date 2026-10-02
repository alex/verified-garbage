import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Args
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
import VerifiedGarbage.Spec.Ed25519.CachedSign

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

def signCachedLocal : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 64⟩
    let seed : Region := ⟨s.gpr .x1, 32⟩
    let pk : Region := ⟨s.gpr .x2, 32⟩
    let msg : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 8192⟩
    let stk : Region := below s.sp 352
    s.rd = [seed, pk, msg] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint scr ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat ∧
      Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32)
  post s t := Spec.Ed25519.bytesAt t.mem (s.gpr .x0) 64 = Spec.Ed25519.sign
    (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.gpr .x5 = t.gpr .x5

def lay (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, Whole.base s⟩

theorem entry_below {s : State} (h : signCachedLocal.pre s) : 352 ≤ s.sp.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := h
  exact hb

theorem entry_writes {s : State} (h : signCachedLocal.pre s) :
    ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  obtain ⟨_, hw, _, _, _, _, _, _, _, ko, _, _, _, kc, _⟩ := h
  intro r hr
  rw [hw] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ko
  · exact kc

theorem lay_ok {s : State} (h : signCachedLocal.pre s) : (lay s).Ok := by
  obtain ⟨_, _, os, op, om, oc, sc, pc, mc, ko, ks, kp, km, kc, no, ns, np, nm, nc, hb, _⟩ := h
  have stk := Whole.stk_sub s
  have fr : Region.Sub (Whole.FR (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Region.sub_prefix (by decide) : Region.Sub (Whole.FR (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ar : Region.Sub (Whole.ARGS (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Offset.sub_base _ (by decide) : Region.Sub (Whole.ARGS (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ck := Whole.ck_sub s
  refine ⟨?_, ?_, oc, ko.sub_left fr, no, ?_, ?_, kc.sub_left fr, np, nm, ns, nc, Whole.base_16 hb, ?_,
    ko.sub_left ck, kc.sub_left ck⟩
  · change (s.sp - 336#64).toNat + 304 ≤ 2 ^ 64
    rw [BitVec.toNat_sub_of_le (by change 336 ≤ s.sp.toNat; omega)]
    have hs := s.sp.isLt
    change s.sp.toNat - 336 + 304 ≤ 2 ^ 64
    omega
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact os
    · exact op
    · exact om
    · exact (ko.sub_left ar).symm
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact sc
    · exact pc
    · exact mc
    · exact kc.sub_left ar
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ks.sub_left fr
    · exact kp.sub_left fr
    · exact km.sub_left fr
    · exact Offset.base_disjoint _ (by decide) (by decide)
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ks.sub_left ck
    · exact kp.sub_left ck
    · exact km.sub_left ck
    · exact Whole.ck_frame (by decide : 256 + 48 ≤ 304)

theorem entry_ctx {s p : State} (h : signCachedLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr s.v p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.PK, Lay.MSG, Lay.OUT, Lay.SCR, Lay.ARGS, Whole.ARGS, show BitVec.ofNat 64 256 = (256 : Addr) from rfl, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : Arguments (lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hp hj
  have he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw

theorem entry_input {s : State} (h : signCachedLocal.pre s) {m : Mem}
    (hf : Frame [below s.sp 336] s.mem m) {r : Region} (hr : r ∈ s.rd) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m r.base r.len = Spec.Ed25519.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR]
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, ks, kp, km, _⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have hb : Region.Sub (below s.sp 336) (below s.sp 352) := below_sub (by decide) (by decide)
  rcases hr with rfl | rfl | rfl
  · exact (ks.sub_left hb).symm
  · exact (kp.sub_left hb).symm
  · exact (km.sub_left hb).symm

theorem entry_key {s p : State} (h : signCachedLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Spec.Ed25519.bytesAt p.mem (lay s).pk 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt p.mem (lay s).seed 32) := by
  have hk : Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk⟩ := h
    exact hk
  have hf := Whole.saved_frame hp
  have hp' := entry_input h hf (r := ⟨s.gpr .x2, 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  have hs' := entry_input h hf (r := ⟨s.gpr .x1, 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt p.mem (s.gpr .x2) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt p.mem (s.gpr .x1) 32)
  rw [hp', hs']
  exact hk

end VG.Proof.Ed25519.AArch64.SignCached
