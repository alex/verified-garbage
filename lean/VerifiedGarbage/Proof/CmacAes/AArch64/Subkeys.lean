import VerifiedGarbage.Proof.CmacAes.AArch64.Dbl
import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_subkeys`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-! ## Doubling a block -/

/-- The memory after `dbl src dst`, from `x19 = K`. -/
def dblMem (m : Mem) (K : Addr) (src dst : Nat) : Mem :=
  let hi := rev64 (m.readW (K + BitVec.ofNat 64 src) 64)
  let lo := rev64 (m.readW (K + BitVec.ofNat 64 (src + 8)) 64)
  (m.writeW (K + BitVec.ofNat 64 dst) (rev64 (dblHi hi lo))).writeW (K + BitVec.ofNat 64 (dst + 8))
    (rev64 (dblLo hi lo))

theorem mz0 : BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) = 0 := by decide
theorem mz87 : BitVec.setWidth 64 (135 : BitVec 16) <<< (16 * 0) = 0x87 := by decide

theorem dbl_ok (s : State) {K : Addr} (hb : s.gpr .x19 = K) {src dst : Nat}
    (hs : src % 8 = 0 ∧ src + 8 < 32768) (hd : dst % 8 = 0 ∧ dst + 8 < 32768)
    (r₀ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 src) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 (src + 8)) 8)
    (w₀ : InRegions s.wr (K + BitVec.ofNat 64 dst) 8) (w₁ : InRegions s.wr (K + BitVec.ofNat 64 (dst + 8)) 8) :
    ∃ s', runBlock isa (dbl src dst) s = some s' ∧ s'.mem = dblMem s.mem K src dst ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [dbl, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
      ite_true, ite_false, Option.bind_some, Option.map_some, hb, hs.1, hd.1, BitVec.setWidth_eq,
      show src < 32768 by omega, show src + 8 < 32768 from hs.2, show dst < 32768 by omega,
      show dst + 8 < 32768 from hd.2, Nat.add_mod_right, r₀, r₁, w₀, w₁, and_self]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, rfl, rfl⟩
  simp only [dblMem, dblHi, dblLo, Mem.writeW, Mem.readW, BitVec.setWidth_eq, mz0, mz87]

theorem dblMem_frame (m : Mem) (K : Addr) (src dst : Nat) :
    Frame [⟨K + BitVec.ofNat 64 dst, 16⟩] m (dblMem m K src dst) := by
  rw [dblMem, show K + BitVec.ofNat 64 (dst + 8) = K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8 from
    (Offset.add_add _ _ _).symm]
  exact Proof.Cmac.frame_store2 _ _ _

theorem dblMem_bytes (m : Mem) (K : Addr) (src dst : Nat) :
    Spec.Aes.bytesAt (dblMem m K src dst) (K + BitVec.ofNat 64 dst) 16 =
      Spec.Cmac.dbl 16 (Spec.Aes.bytesAt m (K + BitVec.ofNat 64 src) 16) := by
  rw [dblMem, show K + BitVec.ofNat 64 (dst + 8) = K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8 from
      (Offset.add_add _ _ _).symm,
    show K + BitVec.ofNat 64 (src + 8) = K + BitVec.ofNat 64 src + BitVec.ofNat 64 8 from
      (Offset.add_add _ _ _).symm,
    Proof.Cmac.bytesAt_store2, le8_rev, dbl_words, Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _),
    ← Spec.Gcm.blockAt, ← Proof.Gcm.AArch64.blockAt_rev, BitVec.add_zero]

/-! ## Before the call -/

/-- The memory after `subkeysPre`. -/
def preMem (s : State) : Mem :=
  ((((((s.mem.writeW (s.gpr .x3 + BitVec.ofNat 64 2064) (s.gpr .x19)).writeW
    (s.gpr .x3 + BitVec.ofNat 64 2072) (s.gpr .x20)).writeW
    (s.gpr .x3 + BitVec.ofNat 64 2080) (s.gpr .x30)).writeW
    (s.gpr .x3 + BitVec.ofNat 64 2048) (0 : BitVec 64)).writeW
    (s.gpr .x3 + BitVec.ofNat 64 2056) (0 : BitVec 64)).writeW
    (s.gpr .x2 + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW
    (s.gpr .x2 + BitVec.ofNat 64 8) (0 : BitVec 64)

theorem subkeysPre_ok (s : State)
    (w₁ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 2064) 8)
    (w₂ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 2072) 8)
    (w₃ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 2080) 8)
    (w₄ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 2048) 8)
    (w₅ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 2056) 8)
    (w₆ : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 0) 8)
    (w₇ : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa subkeysPre s = some s' ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.gpr .x1 = s.gpr .x1 ∧
      s'.gpr .x2 = s.gpr .x3 + BitVec.ofNat 64 2048 ∧ s'.gpr .x3 = s.gpr .x2 ∧ s'.gpr .x4 = 1 ∧
      s'.gpr .x5 = s.gpr .x3 ∧ s'.gpr .x19 = s.gpr .x2 ∧ s'.gpr .x20 = s.gpr .x3 ∧
      (∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = preMem s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [subkeysPre, ctrArgs, cOff, mov, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, mem_write, wr_write, ite_true, ite_false, Option.bind_some,
      BitVec.setWidth_eq, w₁, w₂, w₃, w₄, w₅, w₆, w₇]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], rfl,
    by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], fun r hr h₁ h₂ => ?_, rfl, ?_, rfl, rfl⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_write]
  · simp only [mem_write, preMem, Mem.writeW, BitVec.setWidth_eq, mz0]

/-! ## The whole function -/

/-- The precondition, by name: the schedule `W`, the subkeys `K`, the scratch
buffer `S` and the rounds `R`. -/
structure SPre (s₀ : State) (W K S : Addr) (R : Nat) : Prop where
  x0 : s₀.gpr .x0 = W
  x2 : s₀.gpr .x2 = K
  x3 : s₀.gpr .x3 = S
  x1 : (s₀.gpr .x1).toNat = R
  rd : s₀.rd = [⟨W, 240⟩]
  wr : s₀.wr = [⟨K, 32⟩, ⟨S, 2176⟩]
  sch_k : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  sch_scr : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  k_scr : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  k_wrap : K.toNat + 32 ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem SPre.of {s₀ : State} (h : subkeysAArch64.pre s₀) :
    SPre s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h⟩

theorem bytesAt_32 (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p 32 = Spec.Aes.bytesAt m p 16 ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 16) 16 := by
  simp only [Spec.Aes.bytesAt]
  rw [show (32 : Nat) = 16 + 16 from rfl, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

theorem k0 (K : Addr) : K + BitVec.ofNat 64 0 = K := BitVec.add_zero K

theorem zeros_8_8 : Spec.Cmac.zeros 8 ++ Spec.Cmac.zeros 8 = Spec.Cmac.zeros 16 := by decide

theorem scr_sub' {S : Addr} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ := Offset.sub_base _ h

theorem preMem_frame (s : State) :
    Frame [⟨s.gpr .x3 + BitVec.ofNat 64 2048, 40⟩, ⟨s.gpr .x2, 16⟩] s.mem (preMem s) := by
  have c (d : Nat) (h : d + 8 ≤ 40) :
      (⟨s.gpr .x3 + BitVec.ofNat 64 2048, 40⟩ : Region).Contains (s.gpr .x3 + BitVec.ofNat 64 (2048 + d)) 8 := by
    rw [← Offset.add_add]; exact Offset.contains_base _ h (by omega)
  have k (d : Nat) (h : d + 8 ≤ 16) : (⟨s.gpr .x2, 16⟩ : Region).Contains (s.gpr .x2 + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base _ h (by omega)
  exact (((((((Frame.refl _ _).writeW (by simp) _ (c 16 (by decide))).writeW (by simp) _
    (c 24 (by decide))).writeW (by simp) _ (c 32 (by decide))).writeW
    (by simp) _ (c 0 (by decide))).writeW (by simp) _ (c 8 (by decide))).writeW (by simp) _
    (k 0 (by decide))).writeW (by simp) _ (k 8 (by decide))

theorem frame_store2' {m : Mem} (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW (p + BitVec.ofNat 64 0) w₀).writeW (p + BitVec.ofNat 64 8) w₁) := by
  rw [k0]; exact Proof.Cmac.frame_store2 _ _ _

theorem restore3_ok (s : State) {B : Addr} (hb : s.gpr .x20 = B)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2064) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2072) 8)
    (r₃ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2080) 8) :
    ∃ s', runBlock isa [.ldr .x .x30 .x20 2080, .ldr .x .x19 .x20 2064, .ldr .x .x20 .x20 2072] s = some s' ∧
      s'.gpr .x19 = s.mem.readW (B + BitVec.ofNat 64 2064) 64 ∧
      s'.gpr .x20 = s.mem.readW (B + BitVec.ofNat 64 2072) 64 ∧
      s'.gpr .x30 = s.mem.readW (B + BitVec.ofNat 64 2080) 64 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x30 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write, wr_write, ite_true, ite_false,
      Option.bind_some, Option.map_some, hb, r₁, r₂, r₃]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, Mem.readW], by simp [gpr_write, Mem.readW], by simp [gpr_write, Mem.readW],
    fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃], rfl, rfl⟩

theorem readW_writeW_other' (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  readW_writeW_other m b v h hd he

theorem preMem_slot (s : State) {d : Nat} (hd : d = 2064 ∨ d = 2072 ∨ d = 2080)
    (hks : (⟨s.gpr .x2, 32⟩ : Region).Disjoint ⟨s.gpr .x3, 2176⟩) :
    (preMem s).readW (s.gpr .x3 + BitVec.ofNat 64 d) 64 =
      if d = 2064 then s.gpr .x19 else if d = 2072 then s.gpr .x20 else s.gpr .x30 := by
  have kd (e : Nat) (he : e + 8 ≤ 32) : Mem.Sep (s.gpr .x3 + BitVec.ofNat 64 d) (64 / 8)
      (s.gpr .x2 + BitVec.ofNat 64 e) (64 / 8) :=
    hks.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Offset.contains_base _ he (by omega))
  rw [preMem, Mem.readW_writeW_sep (kd 8 (by decide)) (by decide), Mem.readW_writeW_sep (kd 0 (by decide)) (by decide),
    readW_writeW_other _ _ _ (by omega) (by omega) (by decide),
    readW_writeW_other _ _ _ (by omega) (by omega) (by decide)]
  rcases hd with rfl | rfl | rfl
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [Mem.readW_writeW_self64]; rfl

theorem callPre_of {s₀ : State} {W K S : Addr} {R : Nat} (hp : SPre s₀ W K S R) {s₁ : State}
    (x0₁ : s₁.gpr .x0 = s₀.gpr .x0) (x1₁ : s₁.gpr .x1 = s₀.gpr .x1)
    (x2₁ : s₁.gpr .x2 = s₀.gpr .x3 + BitVec.ofNat 64 2048) (x3₁ : s₁.gpr .x3 = s₀.gpr .x2)
    (x4₁ : s₁.gpr .x4 = 1) (x5₁ : s₁.gpr .x5 = s₀.gpr .x3)
    (mem₁ : s₁.mem = preMem s₀) (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    CallPre s₁ W (S + BitVec.ofNat 64 2048) K S R := by
  have hR := hp.rounds
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have cK : (⟨K, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (scr_sub' (by decide))
  have zK : Spec.Aes.bytesAt s₁.mem K 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, preMem, hp.x2, k0, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero, zeros_8_8]
  exact
      { x0 := by rw [x0₁, hp.x0]
        x1 := by rw [x1₁]; apply BitVec.eq_of_toNat_eq; simp [hp.x1]; omega
        x2 := by rw [x2₁, hp.x3]
        x3 := by rw [x3₁, hp.x2]
        x4 := x4₁
        x5 := by rw [x5₁, hp.x3]
        rounds := hR
        wc := hp.sch_scr.sub_right (scr_sub' (by decide))
        wd := hp.sch_k.sub_right (Region.sub_prefix (by decide))
        ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
        cd := cK.symm
        cs := Offset.disjoint_base _ (by decide) (by omega)
        ds := (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
        wrap := by omega
        reads := by
          rw [rd₁, wr₁, hp.rd, hp.wr]
          refine Covers.of_sub fun r hr => ?_
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact ⟨⟨W, 240⟩, by simp, 0, by simp, by simp⟩
          · exact ⟨⟨S, 2176⟩, by simp, 2048, rfl, by simp⟩
          · exact ⟨⟨K, 32⟩, by simp, 0, by simp, by simp⟩
          · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
        writes := by
          rw [wr₁, hp.wr]
          refine Covers.of_sub fun r hr => ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨⟨S, 2176⟩, by simp, 2048, rfl, by simp⟩
          · exact ⟨⟨K, 32⟩, by simp, 0, by simp, by simp⟩
          · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
        zero := zK }

theorem subkeys_wp (v : Ctr32Impl) {s₀ : State} (h0 : subkeysAArch64.pre s₀) :
    WP isa (subkeys v.callee) s₀ fun s' => GprAbi s₀ s' ∧ subkeysAArch64.post s₀ s' := by
  have hp := SPre.of h0
  generalize s₀.gpr .x0 = W at hp
  generalize s₀.gpr .x2 = K at hp
  generalize s₀.gpr .x3 = S at hp
  generalize (s₀.gpr .x1).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (K + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega))
  -- Before the call.
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, x19₁, x20₁, cs₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    subkeysPre_ok s₀ (by rw [hp.x3]; exact inS _ (by decide)) (by rw [hp.x3]; exact inS _ (by decide))
      (by rw [hp.x3]; exact inS _ (by decide)) (by rw [hp.x3]; exact inS _ (by decide))
      (by rw [hp.x3]; exact inS _ (by decide))
      (by rw [hp.x2]; exact inK _ (by decide)) (by rw [hp.x2]; exact inK _ (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- The memory before the call.
  have f₁ : Frame [⟨S + BitVec.ofNat 64 2048, 40⟩, ⟨K, 16⟩] s₀.mem s₁.mem := by
    rw [mem₁, ← hp.x3, ← hp.x2]; exact preMem_frame s₀
  have cK : (⟨K, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (scr_sub' (by decide))
  have zC : Spec.Aes.bytesAt s₁.mem (S + BitVec.ofNat 64 2048) 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, preMem, hp.x3, hp.x2]
    rw [Proof.Cmac.bytesAt_frame16 (frame_store2' K _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact cK.symm)]
    rw [(Offset.add_add_eq S (a := 2048) (b := 8) (c := 2056) rfl).symm, Proof.Cmac.bytesAt_store2,
      Proof.Cmac.le8_zero, zeros_8_8]
  have zK : Spec.Aes.bytesAt s₁.mem K 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, preMem, hp.x2, k0, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero, zeros_8_8]
  have schB : ∀ m : Mem, Frame [⟨S + BitVec.ofNat 64 2048, 40⟩, ⟨K, 16⟩] s₀.mem m →
      Spec.Aes.bytesAt m W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) := fun m hf =>
    Proof.Cmac.bytesAt_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.sch_scr.sub_left (Region.sub_prefix hRb)).sub_right (scr_sub' (by decide))
      · exact (hp.sch_k.sub_left (Region.sub_prefix hRb)).sub_right (Region.sub_prefix (by decide))) (by omega)
  -- The call.
  have pre := callPre_of hp x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ mem₁ rd₁ wr₁
  refine WP.seq (WP.mono (ctr_call v pre) fun s₂ h₂ => ?_)
  -- After the call.
  have x19₂ : s₂.gpr .x19 = K := by rw [h₂.saved .x19 (by simp [preserved]) (by decide), x19₁, hp.x2]
  have x20₂ : s₂.gpr .x20 = S := by rw [h₂.saved .x20 (by simp [preserved]) (by decide), x20₁, hp.x3]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, rd₁, wr₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [h₂.wr, wr₁]
  have rIn (a : Addr) (h : InRegions s₀.wr a 8) : InRegions (s₀.rd ++ s₀.wr) a 8 := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [subkeysPost, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₃, run₃, mem₃, g₃, sp₃, rd₃, wr₃⟩ := dbl_ok s₂ x19₂ (src := 0) (dst := 0) (by decide) (by decide)
    (by rw [rdwr₂]; exact rIn _ (inK 0 (by decide))) (by rw [rdwr₂]; exact rIn _ (inK 8 (by decide)))
    (by rw [wr₂]; exact inK 0 (by decide)) (by rw [wr₂]; exact inK 8 (by decide))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have x19₃ : s₃.gpr .x19 = K := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), x19₂]
  obtain ⟨s₄, run₄, mem₄, g₄, sp₄, rd₄, wr₄⟩ := dbl_ok s₃ x19₃ (src := 0) (dst := 16) (by decide) (by decide)
    (by rw [rd₃, wr₃, rdwr₂]; exact rIn _ (inK 0 (by decide)))
    (by rw [rd₃, wr₃, rdwr₂]; exact rIn _ (inK 8 (by decide)))
    (by rw [wr₃, wr₂]; exact inK 16 (by decide)) (by rw [wr₃, wr₂]; exact inK 24 (by decide))
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have x20₄ : s₄.gpr .x20 = S := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide),
      x20₂]
  obtain ⟨s₅, run₅, x19₅, x20₅, x30₅, g₅, sp₅, mem₅⟩ := restore3_ok s₄ x20₄
    (by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]; exact rIn _ (inS 2064 (by decide)))
    (by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]; exact rIn _ (inS 2072 (by decide)))
    (by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]; exact rIn _ (inS 2080 (by decide)))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  -- Memory.
  have f₂ := h₂.frame
  have f₃ : Frame [⟨K + BitVec.ofNat 64 0, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact dblMem_frame _ _ _ _
  have f₄ : Frame [⟨K + BitVec.ofNat 64 16, 16⟩] s₃.mem s₄.mem := by rw [mem₄]; exact dblMem_frame _ _ _ _
  have slotD : ∀ r ∈ [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨K, 16⟩, ⟨S, 2048⟩],
      (⟨S + BitVec.ofNat 64 2064, 24⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint S (by decide) (by omega) (by omega)
    · exact (hp.k_scr.symm.sub_left (scr_sub' (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.disjoint_base _ (by decide) (by omega)
  have slotK (e : Nat) (he : e ≤ 16) : (⟨S + BitVec.ofNat 64 2064, 24⟩ : Region).Disjoint ⟨K + BitVec.ofNat 64 e, 16⟩ :=
    (hp.k_scr.symm.sub_left (scr_sub' (by decide))).sub_right (Offset.sub_base _ (by omega))
  have slot (d : Nat) (h₁ : 2064 ≤ d) (h₂' : d + 8 ≤ 2088) :
      s₄.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    have c : (⟨S + BitVec.ofNat 64 2064, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (64 / 8) := by
      rw [show S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 2064 + BitVec.ofNat 64 (d - 2064) from
        (Offset.add_add_eq S (by omega)).symm]
      exact Offset.contains_base _ (by omega) (by omega)
    rw [f₄.readW c (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact slotK 16 (by decide))
        (by decide),
      f₃.readW c (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact slotK 0 (by decide))
        (by decide),
      f₂.readW c slotD (by decide)]
  have pslot := fun d hd => preMem_slot s₀ (d := d) hd (by rw [hp.x2, hp.x3]; exact hp.k_scr)
  rw [hp.x3] at pslot
  have gk (r : Reg) (hr : r ∈ preserved) (h19 : r ≠ .x19) (h20 : r ≠ .x20) (h30 : r ≠ .x30) :
      s₅.gpr r = s₀.gpr r := by
    have n9 : r ≠ .x9 := by rintro rfl; simp [preserved] at hr
    have n10 : r ≠ .x10 := by rintro rfl; simp [preserved] at hr
    have n11 : r ≠ .x11 := by rintro rfl; simp [preserved] at hr
    have n12 : r ≠ .x12 := by rintro rfl; simp [preserved] at hr
    rw [g₅ r h19 h20 h30, g₄ r n9 n10 n11 n12, g₃ r n9 n10 n11 n12, h₂.saved r hr h30, cs₁ r hr h19 h20]
  refine ⟨⟨fun r hr => ?_, by rw [sp₅, sp₄, sp₃, h₂.sp, sp₁]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₅, slot 2064 (by decide) (by decide), mem₁, pslot 2064 (.inl rfl)]; rfl
    by_cases h20 : r = .x20
    · subst h20; rw [x20₅, slot 2072 (by decide) (by decide), mem₁, pslot 2072 (.inr (.inl rfl))]; rfl
    by_cases h30 : r = .x30
    · subst h30; rw [x30₅, slot 2080 (by decide) (by decide), mem₁, pslot 2080 (.inr (.inr rfl))]; rfl
    exact gk r hr h19 h20 h30
  · show Spec.Aes.bytesAt s₅.mem (s₀.gpr .x2) 32 = _
    rw [hp.x2, hp.x0, hp.x1, mem₅, bytesAt_32]
    have L : Spec.Aes.bytesAt s₂.mem K 16 = ciphAt s₀.mem W R (Spec.Cmac.zeros 16) := by
      rw [h₂.out, schB _ f₁, zC]
    have b3 : Spec.Aes.bytesAt s₃.mem K 16 = Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₂.mem K 16) := by
      have := dblMem_bytes s₂.mem K 0 0
      rw [k0] at this; rw [mem₃, this]
    have b4lo : Spec.Aes.bytesAt s₄.mem K 16 = Spec.Aes.bytesAt s₃.mem K 16 :=
      Proof.Cmac.bytesAt_frame16 f₄ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base K (by decide) (by omega)).symm
    have b4hi : Spec.Aes.bytesAt s₄.mem (K + BitVec.ofNat 64 16) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₃.mem K 16) := by
      have := dblMem_bytes s₃.mem K 0 16
      rw [k0] at this; rw [mem₄, this]
    rw [b4lo, b4hi, b3, L]
    rfl

end VG.Proof.CmacAes.AArch64
