import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_subkeys`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-! ## Doubling a block -/

/-- The words `dbl` stores, from the halves `hi` and `lo` it loads. -/
def dblHi (hi lo : BitVec 64) : BitVec 64 := (hi + hi) ||| (lo >>> 63)
def dblLo (hi lo : BitVec 64) : BitVec 64 :=
  (lo + lo) ^^^ (((0 : BitVec 32).setWidth 64 - (hi >>> 63)) &&& BitVec.signExtend 64 (0x87 : BitVec 32))

/-- The memory after `dbl src dst`, from `rbx = K`. -/
def dblMem (m : Mem) (K : Addr) (src dst : Nat) : Mem :=
  let hi := bswap64 (m.readW (K + BitVec.ofNat 64 src) 64)
  let lo := bswap64 (m.readW (K + BitVec.ofNat 64 (src + 8)) 64)
  (m.writeW (K + BitVec.ofNat 64 dst) (bswap64 (dblHi hi lo))).writeW (K + BitVec.ofNat 64 (dst + 8))
    (bswap64 (dblLo hi lo))

theorem dbl_ok (s : State) {K : Addr} (hb : s.gpr .rbx = K) {src dst : Nat}
    (r₀ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 src) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 (src + 8)) 8)
    (w₀ : InRegions s.wr (K + BitVec.ofNat 64 dst) 8) (w₁ : InRegions s.wr (K + BitVec.ofNat 64 (dst + 8)) 8) :
    ∃ s', runBlock isa (dbl src dst) s = some s' ∧ s'.mem = dblMem s.mem K src dst ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [dbl, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, readSrc32, execAlu, execShift, State.load64, State.store64, State.ea, State.setReg32, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags,
      mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags,
      ite_true, ite_false, hb, r₀, r₁, w₀, w₁]
    rfl, ?_⟩
  refine ⟨?_, ?_, rfl, rfl⟩
  · rfl
  · intro r h₁ h₂ h₃ h₄
    simp [gpr_setReg, gpr_setFlags, h₁, h₂, h₃, h₄]

theorem dbl_words' (hi lo : BitVec 64) : dblHi hi lo ++ dblLo hi lo = Proof.Cmac.dbl128 (hi ++ lo) := by
  rw [dblHi, dblLo, show (0 : BitVec 32).setWidth 64 = 0 from rfl]
  exact dbl_words hi lo

theorem dblMem_frame (m : Mem) (K : Addr) (src dst : Nat) :
    Frame [⟨K + BitVec.ofNat 64 dst, 16⟩] m (dblMem m K src dst) := by
  rw [dblMem, show K + BitVec.ofNat 64 (dst + 8) = K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8 from
    (Offset.add_add _ _ _).symm]
  exact frame_store2 _ _ _

theorem dblMem_bytes (m : Mem) (K : Addr) (src dst : Nat) :
    Spec.Aes.bytesAt (dblMem m K src dst) (K + BitVec.ofNat 64 dst) 16 =
      Spec.Cmac.dbl 16 (Spec.Aes.bytesAt m (K + BitVec.ofNat 64 src) 16) := by
  rw [dblMem, show K + BitVec.ofNat 64 (dst + 8) = K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8 from
      (Offset.add_add _ _ _).symm,
    show K + BitVec.ofNat 64 (src + 8) = K + BitVec.ofNat 64 src + BitVec.ofNat 64 8 from
      (Offset.add_add _ _ _).symm,
    Proof.Cmac.bytesAt_store2, le8_bswap, dbl_words', Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _),
    ← Spec.Gcm.blockAt, ← Proof.Gcm.X86_64.blockAt_bswap, BitVec.add_zero]

/-! ## Before the call -/

/-- The memory after `subkeysPre`. -/
def preMem (s : State) : Mem :=
  (((((s.mem.writeW (s.gpr .rcx + BitVec.ofNat 64 2064) (s.gpr .rbx)).writeW
    (s.gpr .rcx + BitVec.ofNat 64 2072) (s.gpr .rbp)).writeW
    (s.gpr .rcx + BitVec.ofNat 64 2048) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
    (s.gpr .rcx + BitVec.ofNat 64 2056) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
    (s.gpr .rdx + BitVec.ofNat 64 0) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
    (s.gpr .rdx + BitVec.ofNat 64 8) (BitVec.setWidth 64 (0 : BitVec 32))

theorem subkeysPre_ok (s : State)
    (w₁ : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 2064) 8)
    (w₂ : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 2072) 8)
    (w₃ : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 2048) 8)
    (w₄ : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 2056) 8)
    (w₅ : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 0) 8)
    (w₆ : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa subkeysPre s = some s' ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsi = s.gpr .rsi ∧
      s'.gpr .rdx = s.gpr .rcx + BitVec.ofNat 64 2048 ∧ s'.gpr .rcx = s.gpr .rdx ∧ s'.gpr .r8 = 1 ∧
      s'.gpr .r9 = s.gpr .rcx ∧ s'.gpr .rbx = s.gpr .rdx ∧ s'.gpr .rbp = s.gpr .rcx ∧
      (∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧
      s'.mem = preMem s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [subkeysPre, ctrArgs, cOff, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32, execAlu, State.store64,
      State.ea, State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, w₁, w₂, w₃, w₄, w₅, w₆]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rfl
    | (simp [gpr_setReg]; done)
    | (intro r hr h₁ h₂
       simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_setReg])

/-! ## The whole function -/

/-- The precondition, by name: the schedule `W`, the subkeys `K`, the scratch
buffer `S` and the rounds `R`. -/
structure SPre (s₀ : State) (W K S : Addr) (R : Nat) : Prop where
  rdi : s₀.gpr .rdi = W
  rdx : s₀.gpr .rdx = K
  rcx : s₀.gpr .rcx = S
  rsi : (s₀.gpr .rsi).toNat = R
  rd : s₀.rd = [⟨W, 240⟩]
  wr : s₀.wr = [⟨K, 32⟩, ⟨S, 2176⟩]
  sch_k : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  sch_scr : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  k_scr : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  ret_k : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨K, 32⟩
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2176⟩
  stk_sch : (below (s₀.gpr .rsp) 8).Disjoint ⟨W, 240⟩
  stk_k : (below (s₀.gpr .rsp) 8).Disjoint ⟨K, 32⟩
  stk_scr : (below (s₀.gpr .rsp) 8).Disjoint ⟨S, 2176⟩
  k_wrap : K.toNat + 32 ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem SPre.of {s₀ : State} (h : subkeysX86_64.pre s₀) :
    SPre s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m⟩

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

theorem zero_le8 : Proof.Cmac.le8 (BitVec.setWidth 64 (0 : BitVec 32)) = Spec.Cmac.zeros 8 := by decide

theorem scr_sub' {S : Addr} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ := Offset.sub_base _ h


theorem preMem_frame (s : State) :
    Frame [⟨s.gpr .rcx + BitVec.ofNat 64 2048, 32⟩, ⟨s.gpr .rdx, 16⟩] s.mem (preMem s) := by
  have c (d : Nat) (h : d + 8 ≤ 32) :
      (⟨s.gpr .rcx + BitVec.ofNat 64 2048, 32⟩ : Region).Contains (s.gpr .rcx + BitVec.ofNat 64 (2048 + d)) 8 := by
    rw [← Offset.add_add]; exact Offset.contains_base _ h (by omega)
  have k (d : Nat) (h : d + 8 ≤ 16) : (⟨s.gpr .rdx, 16⟩ : Region).Contains (s.gpr .rdx + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base _ h (by omega)
  exact ((((((Frame.refl _ _).writeW (by simp) _ (c 16 (by decide))).writeW (by simp) _ (c 24 (by decide))).writeW
    (by simp) _ (c 0 (by decide))).writeW (by simp) _ (c 8 (by decide))).writeW (by simp) _ (k 0 (by decide))).writeW
    (by simp) _ (k 8 (by decide))

theorem frame_store2' {m : Mem} (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW (p + BitVec.ofNat 64 0) w₀).writeW (p + BitVec.ofNat 64 8) w₁) := by
  rw [k0]; exact frame_store2 _ _ _

theorem restore2_ok (s : State) {B : Addr} (hb : s.gpr .rbp = B)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2064) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2072) 8) :
    ∃ s', runBlock isa [.mov .rbx (.mem (at_ .rbp 2064)), .mov .rbp (.mem (at_ .rbp 2072))] s = some s' ∧
      s'.gpr .rbx = s.mem.readW (B + BitVec.ofNat 64 2064) 64 ∧
      s'.gpr .rbp = s.mem.readW (B + BitVec.ofNat 64 2072) 64 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, offset_nat, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false,
      Option.map_some, hb, r₁, r₂]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

theorem preMem_slot (s : State) {d : Nat} (hd : d = 2064 ∨ d = 2072)
    (hks : (⟨s.gpr .rdx, 32⟩ : Region).Disjoint ⟨s.gpr .rcx, 2176⟩) :
    (preMem s).readW (s.gpr .rcx + BitVec.ofNat 64 d) 64 = if d = 2064 then s.gpr .rbx else s.gpr .rbp := by
  have kd (e : Nat) (he : e + 8 ≤ 32) : Mem.Sep (s.gpr .rcx + BitVec.ofNat 64 d) (64 / 8)
      (s.gpr .rdx + BitVec.ofNat 64 e) (64 / 8) :=
    hks.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Offset.contains_base _ he (by omega))
  rw [preMem, Mem.readW_writeW_sep (kd 8 (by decide)) (by decide), Mem.readW_writeW_sep (kd 0 (by decide)) (by decide),
    readW_writeW_other _ _ _ (by omega) (by omega) (by decide),
    readW_writeW_other _ _ _ (by omega) (by omega) (by decide)]
  rcases hd with rfl | rfl
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [Mem.readW_writeW_self64]; rfl

theorem callPre_of {s₀ : State} {W K S : Addr} {R : Nat} (hp : SPre s₀ W K S R) {s₁ : State}
    (rdi₁ : s₁.gpr .rdi = s₀.gpr .rdi) (rsi₁ : s₁.gpr .rsi = s₀.gpr .rsi)
    (rdx₁ : s₁.gpr .rdx = s₀.gpr .rcx + BitVec.ofNat 64 2048) (rcx₁ : s₁.gpr .rcx = s₀.gpr .rdx)
    (r8₁ : s₁.gpr .r8 = 1) (r9₁ : s₁.gpr .r9 = s₀.gpr .rcx) (rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp)
    (mem₁ : s₁.mem = preMem s₀) (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    CallPre s₁ W (S + BitVec.ofNat 64 2048) K S R := by
  have hR := hp.rounds
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have cK : (⟨K, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (scr_sub' (by decide))
  have zK : Spec.Aes.bytesAt s₁.mem K 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, preMem, hp.rdx, k0, Proof.Cmac.bytesAt_store2, zero_le8, zeros_8_8]
  exact
      { rdi := by rw [rdi₁, hp.rdi]
        rsi := by rw [rsi₁]; apply BitVec.eq_of_toNat_eq; simp [hp.rsi]; omega
        rdx := by rw [rdx₁, hp.rcx]
        rcx := by rw [rcx₁, hp.rdx]
        r8 := r8₁
        r9 := by rw [r9₁, hp.rcx]
        rounds := hR
        wc := hp.sch_scr.sub_right (scr_sub' (by decide))
        wd := hp.sch_k.sub_right (Region.sub_prefix (by decide))
        ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
        cd := cK.symm
        cs := Offset.disjoint_base _ (by decide) (by omega)
        ds := (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
        stkW := by rw [rsp₁]; exact hp.stk_sch
        stkC := by rw [rsp₁]; exact hp.stk_scr.sub_right (scr_sub' (by decide))
        stkD := by rw [rsp₁]; exact hp.stk_k.sub_right (Region.sub_prefix (by decide))
        stkS := by rw [rsp₁]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
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

theorem subkeys_wp (v : Ctr32Impl) {s₀ : State} (h0 : subkeysX86_64.pre s₀) :
    WP isa (subkeys v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ subkeysX86_64.post s₀ s' := by
  have hp := SPre.of h0
  generalize s₀.gpr .rdi = W at hp
  generalize s₀.gpr .rdx = K at hp
  generalize s₀.gpr .rcx = S at hp
  generalize (s₀.gpr .rsi).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (K + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega))
  -- Before the call.
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, rbx₁, rbp₁, cs₁, mem₁, rd₁, wr₁⟩ :=
    subkeysPre_ok s₀ (by rw [hp.rcx]; exact inS _ (by decide)) (by rw [hp.rcx]; exact inS _ (by decide))
      (by rw [hp.rcx]; exact inS _ (by decide)) (by rw [hp.rcx]; exact inS _ (by decide))
      (by rw [hp.rdx]; exact inK _ (by decide)) (by rw [hp.rdx]; exact inK _ (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- The memory before the call.
  have f₁ : Frame [⟨S + BitVec.ofNat 64 2048, 32⟩, ⟨K, 16⟩] s₀.mem s₁.mem := by
    rw [mem₁, ← hp.rcx, ← hp.rdx]; exact preMem_frame s₀
  have cK : (⟨K, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (scr_sub' (by decide))
  have zC : Spec.Aes.bytesAt s₁.mem (S + BitVec.ofNat 64 2048) 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, preMem, hp.rcx, hp.rdx]
    rw [bytesAt_frame' (frame_store2' K _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact cK.symm)]
    rw [(Offset.add_add_eq S (a := 2048) (b := 8) (c := 2056) rfl).symm, Proof.Cmac.bytesAt_store2, zero_le8,
      zeros_8_8]
  have zK : Spec.Aes.bytesAt s₁.mem K 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, preMem, hp.rdx, k0, Proof.Cmac.bytesAt_store2, zero_le8, zeros_8_8]
  have schB : ∀ m : Mem, Frame [⟨S + BitVec.ofNat 64 2048, 32⟩, ⟨K, 16⟩] s₀.mem m →
      Spec.Aes.bytesAt m W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) := fun m hf =>
    bytesAt_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.sch_scr.sub_left (Region.sub_prefix hRb)).sub_right (scr_sub' (by decide))
      · exact (hp.sch_k.sub_left (Region.sub_prefix hRb)).sub_right (Region.sub_prefix (by decide))) (by omega)
  -- The call.
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := cs₁ .rsp (by simp [calleeSaved]) (by decide) (by decide)
  have pre := callPre_of hp rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁ rsp₁ mem₁ rd₁ wr₁
  refine WP.seq (WP.mono (ctr_call v pre) fun s₂ h₂ => ?_)
  -- After the call.
  have rbx₂ : s₂.gpr .rbx = K := by rw [h₂.saved .rbx (by simp [calleeSaved]), rbx₁, hp.rdx]
  have rbp₂ : s₂.gpr .rbp = S := by rw [h₂.saved .rbp (by simp [calleeSaved]), rbp₁, hp.rcx]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, rd₁, wr₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [h₂.wr, wr₁]
  have rIn (a : Addr) (h : InRegions s₀.wr a 8) : InRegions (s₀.rd ++ s₀.wr) a 8 := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [subkeysPost, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₃, run₃, mem₃, g₃, rd₃, wr₃⟩ := dbl_ok s₂ rbx₂ (src := 0) (dst := 0)
    (by rw [rdwr₂]; exact rIn _ (inK 0 (by decide))) (by rw [rdwr₂]; exact rIn _ (inK 8 (by decide)))
    (by rw [wr₂]; exact inK 0 (by decide)) (by rw [wr₂]; exact inK 8 (by decide))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have rbx₃ : s₃.gpr .rbx = K := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), rbx₂]
  obtain ⟨s₄, run₄, mem₄, g₄, rd₄, wr₄⟩ := dbl_ok s₃ rbx₃ (src := 0) (dst := 16)
    (by rw [rd₃, wr₃, rdwr₂]; exact rIn _ (inK 0 (by decide)))
    (by rw [rd₃, wr₃, rdwr₂]; exact rIn _ (inK 8 (by decide)))
    (by rw [wr₃, wr₂]; exact inK 16 (by decide)) (by rw [wr₃, wr₂]; exact inK 24 (by decide))
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have rbp₄ : s₄.gpr .rbp = S := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide),
      rbp₂]
  obtain ⟨s₅, run₅, rbx₅, rbp₅, g₅, mem₅⟩ := restore2_ok s₄ rbp₄
    (by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]; exact rIn _ (inS 2064 (by decide)))
    (by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]; exact rIn _ (inS 2072 (by decide)))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  -- Memory.
  have f₂ := h₂.frame
  have f₃ : Frame [⟨K + BitVec.ofNat 64 0, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact dblMem_frame _ _ _ _
  have f₄ : Frame [⟨K + BitVec.ofNat 64 16, 16⟩] s₃.mem s₄.mem := by rw [mem₄]; exact dblMem_frame _ _ _ _
  have slotD : ∀ r ∈ [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨K, 16⟩, ⟨S, 2048⟩, below (s₁.gpr .rsp) 8],
      (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint S (by decide) (by omega) (by omega)
    · exact (hp.k_scr.symm.sub_left (scr_sub' (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.disjoint_base _ (by decide) (by omega)
    · rw [rsp₁]; exact (hp.stk_scr.symm.sub_left (scr_sub' (by decide)))
  have slotK (e : Nat) (he : e ≤ 16) : (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Disjoint ⟨K + BitVec.ofNat 64 e, 16⟩ :=
    (hp.k_scr.symm.sub_left (scr_sub' (by decide))).sub_right (Offset.sub_base _ (by omega))
  have slot (d : Nat) (h₁ : 2064 ≤ d) (h₂' : d + 8 ≤ 2080) :
      s₄.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    have c : (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Contains (S + BitVec.ofNat 64 d) (64 / 8) := by
      rw [show S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 2064 + BitVec.ofNat 64 (d - 2064) from
        (Offset.add_add_eq S (by omega)).symm]
      exact Offset.contains_base _ (by omega) (by omega)
    rw [f₄.readW c (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact slotK 16 (by decide))
        (by decide),
      f₃.readW c (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact slotK 0 (by decide))
        (by decide),
      f₂.readW c slotD (by decide)]
  have pslot := fun d hd => preMem_slot s₀ (d := d) hd (by rw [hp.rdx, hp.rcx]; exact hp.k_scr)
  rw [hp.rcx] at pslot
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hb : r = .rbx
    · subst hb; rw [rbx₅, slot 2064 (by decide) (by decide), mem₁, pslot 2064 (.inl rfl)]; rfl
    by_cases hb' : r = .rbp
    · subst hb'; rw [rbp₅, slot 2072 (by decide) (by decide), mem₁, pslot 2072 (.inr rfl)]; rfl
    rw [g₅ r hb hb', g₄ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr),
      g₃ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr),
      h₂.saved r hr, cs₁ r hr hb hb']
  · have fall : Frame [⟨K, 32⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 8] s₀.mem s₅.mem := by
      rw [mem₅]
      refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans
        ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨S, 2176⟩, by simp, scr_sub' (by decide)⟩
        · exact ⟨⟨K, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨⟨S, 2176⟩, by simp, scr_sub' (by decide)⟩
        · exact ⟨⟨K, 32⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨⟨S, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨below (s₀.gpr .rsp) 8, by simp, by rw [rsp₁]; exact fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨K, 32⟩, by simp, Offset.sub_base _ (by decide)⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨K, 32⟩, by simp, Offset.sub_base _ (by decide)⟩
    refine fall.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_k
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show Spec.Aes.bytesAt s₅.mem (s₀.gpr .rdx) 32 = _
    rw [hp.rdx, hp.rdi, hp.rsi, mem₅, bytesAt_32]
    have L : Spec.Aes.bytesAt s₂.mem K 16 = ciphAt s₀.mem W R (Spec.Cmac.zeros 16) := by
      rw [h₂.out, schB _ f₁, zC]
    have b3 : Spec.Aes.bytesAt s₃.mem K 16 = Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₂.mem K 16) := by
      have := dblMem_bytes s₂.mem K 0 0
      rw [k0] at this; rw [mem₃, this]
    have b4lo : Spec.Aes.bytesAt s₄.mem K 16 = Spec.Aes.bytesAt s₃.mem K 16 :=
      bytesAt_frame' f₄ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base K (by decide) (by omega)).symm
    have b4hi : Spec.Aes.bytesAt s₄.mem (K + BitVec.ofNat 64 16) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₃.mem K 16) := by
      have := dblMem_bytes s₃.mem K 0 16
      rw [k0] at this; rw [mem₄, this]
    rw [b4lo, b4hi, b3, L]
    rfl

end VG.Proof.CmacAes.X86_64
