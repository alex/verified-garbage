import VerifiedGarbage.Proof.Ed25519.X86.ScalarContract
import VerifiedGarbage.Proof.Ed25519.X86.Workspace
import VerifiedGarbage.Impl.Ed25519.X86.MulAdd
import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.X86.ScalarEngine
import VerifiedGarbage.Proof.Ed25519.X86.MulAddLit
import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline

/-! Merged from `Proof.Ed25519.X86.MulAddMain`. -/
section
/-! Merged from `Proof.Ed25519.X86.MulAddContract`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86

def scalarMulAddLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let r : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let k : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let a : Region := ⟨(arg s 3).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [r, k, a, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      r.Disjoint scratch ∧ k.Disjoint scratch ∧ a.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 32)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧ arg s 4 = arg t 4

theorem scalarMulAdd_pre {s : State} (h : scalarMulAddLocal.pre s) :
    ScratchPre s 4 5 ∧ InputPre s 4 2 8 ∧ InputPre s 4 3 8 ∧ InputPre s 4 1 8 ∧ OutputPre s 4 := by
  obtain ⟨rd, wr, os, rs, ks, ss, _, ars, ro, rsc, ofit, rfit, kfit, afit, sfit, spfit⟩ := h
  refine ⟨⟨by decide, ?_, sfit, ?_, by omega_using [spfit], ars, rsc⟩,
    ⟨?_, kfit, ?_⟩, ⟨?_, afit, ?_⟩, ⟨?_, rfit, ?_⟩, ⟨?_, ofit, os, ro⟩⟩
  · rw [wr]; simp
  · rw [rd]; simp
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact ks
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact ss
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact rs
  · rw [wr]; simp
end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.MulAddSetup`. -/
section
/-! Merged from `Proof.Ed25519.X86.MulAddWide`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarMulTerms_value (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (scalarMulTerms k) = colv m x (prodTerms 256 288 k) +
      (if k < 8 then wv m x (320 + 4 * k) else 0) := by
  simp only [scalarMulTerms, colv, List.map_append, List.sum_append]
  split <;> simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, tval]

theorem num_extend8 (f : Nat → Nat) : num (fun k => if k < 8 then f k else 0) 16 = num f 8 := by
  rw [num_16]
  have h0 : num (fun k => if 8 + k < 8 then f (8 + k) else 0) 8 = 0 := by
    have he : (fun k => if 8 + k < 8 then f (8 + k) else 0) = (fun _ => 0) := by
      funext k; rw [ite_eq_right (by omega_using [])]
    rw [he]; rfl
  rw [h0, Nat.mul_zero, Nat.add_zero]
  exact num_congr fun k hk => ite_eq_left hk

theorem scalarMulTerms_num (m : Mem) (x : BitVec 32) :
    num (fun k => colv m x (scalarMulTerms k)) 16 = fe m x 256 * fe m x 288 + fe m x 320 := by
  simp only [scalarMulTerms_value]
  rw [num_add, num_extend8]
  have hp : num (fun k => colv m x (prodTerms 256 288 k)) 16 = fe m x 256 * fe m x 288 := by
    simp only [colv, prodTerms, List.map_map]
    exact prod_identity (fun i => wv m x (256 + 4 * i)) (fun i => wv m x (288 + 4 * i))
  rw [hp]; rfl

theorem scalarMulTerms_bound (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (scalarMulTerms k) < 2 ^ 68 := by
  rw [scalarMulTerms_value]
  have hl : (prodTerms 256 288 k).length ≤ 8 := by
    simp only [prodTerms, List.length_map]
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hp := colv_le_len (m := m) (x := x) (B := 2 ^ 64) (ts := prodTerms 256 288 k) fun t ht => by
    simp only [prodTerms, List.mem_map] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact wv_mul_le _ _ _ _
  have hm := Nat.mul_le_mul_right (2 ^ 64) hl
  have hw := wv_lt m x (320 + 4 * k)
  split <;> omega_using [hp, hm, hw]

theorem scalarMulTerms_reads {k : Nat} (hk : k < 16) {t : Term} (ht : t ∈ scalarMulTerms k)
    {d : Nat} (hd : d ∈ treads t) : d + 4 ≤ 4096 ∧ 128 + 4 * k ≤ d := by
  simp only [scalarMulTerms, List.mem_append] at ht
  rcases ht with ht | ht
  · simp only [prodTerms, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq] at ht
    obtain ⟨i, ⟨hi, _, hki⟩, rfl⟩ := ht
    simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> constructor <;> omega_using [hk, hi, hki]
  · split at ht
    · simp only [List.mem_singleton] at ht; subst ht
      simp only [treads, List.mem_singleton] at hd; subst hd
      constructor <;> omega_using [hk]
    · simp only [List.not_mem_nil] at ht

theorem scalarWideMul_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block scalarWideMul) s fun t => Keep s t ∧ Frame [sub x 128 64] s.mem t.mem ∧
      num (fun k => wv t.mem x (128 + 4 * k)) 16 = fe s.mem x 256 * fe s.mem x 288 + fe s.mem x 320 := by
  refine WP.block_append (WP.mono zeroAcc_ok fun u ⟨ku, mu, au⟩ => ?_)
  refine WP.mono (cols_ok (ku.ctx hc) scalarMulTerms 16 (by decide)
    (fun k hk t ht d hd => let h := scalarMulTerms_reads hk ht hd; ⟨h.1, Or.inr h.2⟩)
    (fun k _ => scalarMulTerms_bound _ _ k) (by rw [au]; decide)) fun t ⟨kt, ft, et, _⟩ => ?_
  rw [au, Nat.zero_add, scalarMulTerms_num, mu] at et
  have hA := fe_lt s.mem x 256
  have hB := fe_lt s.mem x 288
  have hC := fe_lt s.mem x 320
  have hab := Nat.mul_le_mul (Nat.le_pred_of_lt hA) (Nat.le_pred_of_lt hB)
  change fe s.mem x 256 * fe s.mem x 288 ≤ (2 ^ 256 - 1) * (2 ^ 256 - 1) at hab
  have hz : acc t = 0 := by
    change _ + (2 ^ 256 * 2 ^ 256) * acc t = _ at et
    omega_using [et, hab, hC]
  rw [hz, Nat.mul_zero, Nat.add_zero] at et
  rw [mu] at ft
  exact ⟨ku.trans kt, ft, et⟩
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem copied_fe {s₀ t : State} {p x : BitVec 32} {dst : Nat}
    (hp : p.toNat + 32 ≤ 2 ^ 32)
    (hw : ∀ k < 8, wd t.mem x (dst + 4 * k) = wd s₀.mem p (4 * k)) :
    fe t.mem x dst = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem (p.setWidth 64) 32) := by
  have ew : fe t.mem x dst = num (fun k => wv s₀.mem p (0 + 4 * k)) 8 :=
    num_congr fun k hk => by simpa only [Nat.zero_add] using congrArg BitVec.toNat (hw k hk)
  rw [ew, ← decode_words s₀.mem 8 (by omega_using [hp]), addr_zero]

theorem scalarMulInputs_ok {s₀ s : State} (hp : ScratchPre s₀ 4 5)
    (hA : InputPre s₀ 4 2 8) (hB : InputPre s₀ 4 3 8) (hC : InputPre s₀ 4 1 8)
    (hs : Saved s₀ (arg s₀ 4) s) :
    WP isa (.block scalarMulInputs) s fun t => Saved s₀ (arg s₀ 4) t ∧
      fe t.mem (arg s₀ 4) 256 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) ∧
      fe t.mem (arg s₀ 4) 288 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 3).setWidth 64) 32) ∧
      fe t.mem (arg s₀ 4) 320 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32) := by
  have he : scalarMulInputs =
      (([.mov .esi (.mem (at_ .esp 12))] : List Instr) ++ copyWords 256 8) ++
      ((([.mov .esi (.mem (at_ .esp 16))] : List Instr) ++ copyWords 288 8) ++
      (([.mov .esi (.mem (at_ .esp 8))] : List Instr) ++ copyWords 320 8)) := by
    simp only [scalarMulInputs, List.append_assoc]
  rw [he]
  refine WP.block_append (WP.mono (loadInput_ok hp hA hs (by decide) (dst := 256)
    (by decide) (by decide) (by decide)) fun u ⟨hu, wu, _⟩ => ?_)
  refine WP.block_append (WP.mono (loadInput_ok hp hB hu (by decide) (dst := 288)
    (by decide) (by decide) (by decide)) fun v ⟨hv, wv, fv⟩ => ?_)
  refine WP.mono (loadInput_ok hp hC hv (by decide) (dst := 320)
    (by decide) (by decide) (by decide)) fun t ⟨ht, wt, ft⟩ => ?_
  refine ⟨ht, ?_, ?_, copied_fe hC.fit wt⟩
  · rw [fe_frame1 ft hp.fit (by decide) (by decide) (Or.inl (by decide)),
      fe_frame1 fv hp.fit (by decide) (by decide) (Or.inl (by decide))]
    exact copied_fe hA.fit wu
  · rw [fe_frame1 ft hp.fit (by decide) (by decide) (Or.inl (by decide))]
    exact copied_fe hB.fit wv
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarMulAdd_correct {s : State} (h : scalarMulAddLocal.pre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  obtain ⟨hp, hA, hB, hC, ho⟩ := scalarMulAdd_pre h
  simp only [scalarMulAdd, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (abiSave_ok hp) fun u hu => ?_))
  refine WP.block_append (WP.mono (scalarMulInputs_ok hp hA hB hC hu) fun v ⟨hv, evA, evB, evC⟩ => ?_)
  refine WP.mono (scalarWideMul_ok (hv.ctx hp.fit hp.wr)) fun w ⟨kw, fw, ew⟩ => ?_
  have hw := hv.of_offset hp.fit (Keep.scalar kw) fw (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (scalarEngine_ok (hw.ctx hp.fit hp.wr)) fun z ⟨kz, fz, ez⟩ => ?_)
  have hz := hw.scalarEngine hp.fit kz fz
  refine WP.mono (finishWords_ok hp ho hz (src := scalarR) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = _
  rw [et, ez, scalarInput_num w.mem hp.fit, ew, evA, evB, evC, Spec.Ed25519.scalarMulAdd]
  rw [Nat.add_comm]
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarMulAdd_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 4 5) s := by
  obtain ⟨hp, _, _, _, ho⟩ := scalarMulAdd_pre h
  obtain ⟨_, wr, _, _, _, _, ao, _⟩ := h
  exact scalarTaint_wf hp ho wr ao

theorem scalarMulAdd_ct : ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 4 5) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2, a3, a4⟩ := hp
  have ps := (scalarMulAdd_pre hs).1
  have pt := (scalarMulAdd_pre ht).1
  refine scalarTaint_agree (scalarMulAdd_wf hs) (scalarMulAdd_wf ht) sp ?_ (by decide)
    hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

def mulAddSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30 else
  if a = 0x8011 then 0x38 else if a = 0x8015 then 0x40 else 0

def mulAddSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := mulAddSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x3800, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 20⟩]

theorem scalarMulAdd_ok (s : State) (h : scalarMulAddLocal.pre s) :
    ∃ tr t, Exec isa scalarMulAdd s tr t ∧ abiPreserved s t ∧ scalarMulAddLocal.post s t :=
  scalarMulAdd_correct h

def scalarMulAddWide : Contract isa :=
  { scalarMulAddLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let r : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let k : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let a : Region := ⟨(arg s 3).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [r, k, a] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      r.Disjoint scratch ∧ k.Disjoint scratch ∧ a.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

def scalarMulAddRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 32⟩, ⟨(arg s 2).setWidth 64, 32⟩, ⟨(arg s 3).setWidth 64, 32⟩, ⟨argAddr s 0, 20⟩]
def scalarMulAddWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 4).setWidth 64, 8192⟩]

theorem scalarMulAddWide_pre (s : State) (h : scalarMulAddWide.pre s) :
    scalarMulAddLocal.pre (s.withRegions (scalarMulAddRd s) (scalarMulAddWr s)) := by
  simp only [scalarMulAddLocal, scalarMulAddRd, scalarMulAddWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarMulAddWide_implies : scalarMulAddWide.Implies (Spec.Ed25519.scalarMulAddContract X86.abi) := by
    have a0 : arg mulAddSatState 0 = 0x1000 := by decide
    have a1 : arg mulAddSatState 1 = 0x2000 := by decide
    have a2 : arg mulAddSatState 2 = 0x3000 := by decide
    have a3 : arg mulAddSatState 3 = 0x3800 := by decide
    have a4 : arg mulAddSatState 4 = 0x4000 := by decide
    have e : argAddr mulAddSatState 0 = 0x8004 := by decide
    have esp : mulAddSatState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Ed25519.scalarMulAddContract, Spec.Ed25519.scalarMulAddSig,
      Spec.Ed25519.scratchWords, scalarMulAddWide, scalarMulAddLocal, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, e, esp] using mulAddSatState

theorem scalarMulAdd_verified : Verified X86.target scalarMulAdd (Spec.Ed25519.scalarMulAddContract X86.abi) := by
  have hsat := scalarMulAddWide_implies.sat_left
  have satLocal : ∃ s, scalarMulAddLocal.pre s := hsat.elim fun s h => ⟨_, scalarMulAddWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarMulAdd scalarMulAddLocal :=
    Verified.of_correct scalarMulAdd_ok scalarMulAdd_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scalarMulAddRd scalarMulAddWr scalarMulAddWide_pre
    ?_ ?_ ?_ ?_ hsat) scalarMulAddWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [scalarMulAddRd, scalarMulAddWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarMulAddWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [scalarMulAddWide, scalarMulAddLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [scalarMulAddWide, scalarMulAddLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86
