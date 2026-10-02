import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Common

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_init`

Untrusted: everything here is checked by Lean. The code saves `x19`, `x20`,
`x21` and `x30` in the scratch buffer, expands the key into the state,
derives the subkeys after the schedule, zeroes the chaining value and
restores the registers: the state then represents the empty message. The
code between the calls is constant time by the taint analysis, and the
calls by their own proofs (`ek_rel`, `sub_rel`), their arguments pinned by
`IMid₁` and `IMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 readW_writeW_other agree_of)
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : Addr) (KL : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x1 : s₀.gpr .x1 = Kp
  x2 : (s₀.gpr .x2).toNat = KL
  x3 : s₀.gpr .x3 = S
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_k : (⟨St, 304⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32

theorem IPre.of {s₀ : State} (h : initAArch64.pre s₀) :
    IPre s₀ (s₀.gpr .x0) (s₀.gpr .x1) (s₀.gpr .x3) (s₀.gpr .x2).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

theorem IPre.rounds {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-- The memory after saving the registers. -/
def initSavedMem (s : State) (S : Addr) : Mem :=
  (((s.mem.writeW (S + BitVec.ofNat 64 2176) (s.gpr .x19)).writeW (S + BitVec.ofNat 64 2184) (s.gpr .x20)).writeW
    (S + BitVec.ofNat 64 2192) (s.gpr .x21)).writeW (S + BitVec.ofNat 64 2200) (s.gpr .x30)

theorem initSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 32⟩] s.mem (initSavedMem s S) := by
  have c (d : Nat) (hd : d + 8 ≤ 32) : (⟨S + BitVec.ofNat 64 2176, 32⟩ : Region).Contains
      (S + BitVec.ofNat 64 (2176 + d)) 8 := by
    rw [← Offset.add_add]; exact Offset.contains_base _ hd (by omega)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simpa using c 0 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _
    (c 16 (by decide))).writeW (List.mem_singleton_self _) _ (c 24 (by decide))

theorem initSaved_read (s : State) (S : Addr) :
    (initSavedMem s S).readW (S + BitVec.ofNat 64 2176) 64 = s.gpr .x19 ∧
      (initSavedMem s S).readW (S + BitVec.ofNat 64 2184) 64 = s.gpr .x20 ∧
      (initSavedMem s S).readW (S + BitVec.ofNat 64 2192) 64 = s.gpr .x21 ∧
      (initSavedMem s S).readW (S + BitVec.ofNat 64 2200) 64 = s.gpr .x30 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [initSavedMem, readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [initSavedMem, readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [initSavedMem, readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [initSavedMem, Mem.readW_writeW_self64]

/-! ## Before the first call -/

theorem initPre_ok {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    ∃ s₁, runBlock isa initPre s₀ = some s₁ ∧ s₁.gpr .x0 = Kp ∧ s₁.gpr .x1 = BitVec.ofNat 64 KL ∧
      s₁.gpr .x2 = St ∧ s₁.gpr .x3 = S ∧ s₁.gpr .x19 = St ∧ s₁.gpr .x20 = S ∧
      s₁.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6) ∧
      (∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → s₁.gpr r = s₀.gpr r) ∧ s₁.sp = s₀.sp ∧
      s₁.mem = initSavedMem s₀ S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega)⟩
  have hKL : s₀.gpr .x2 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.x2
  refine ⟨_, by
    simp (config := {decide := true}) only [initPre, initSaved, mov, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, ite_true, ite_false, Option.bind_some,
      BitVec.setWidth_eq, hp.x3, inS 2176 (by decide), inS 2184 (by decide), inS 2192 (by decide),
      inS 2200 (by decide)]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, hp.x1], by simp [gpr_write, hKL], by simp [gpr_write, hp.x0],
    by simp [gpr_write, hp.x3], by simp [gpr_write, hp.x0], by simp [gpr_write],
    by simp [gpr_write, hKL, rounds_bv hp.klen], fun r hr h19 h20 h21 => ?_, rfl, ?_, rfl, rfl⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_write]
  · simp only [mem_write, initSavedMem, Mem.writeW, BitVec.setWidth_eq]

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp St S KL
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = S
  x21 : s.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6)
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = initSavedMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    WP isa (.block initPre) s₀ (IMid₁ s₀ St Kp S KL) := by
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x19₁, x20₁, x21₁, o₁, sp₁, m₁, rd₁, wr₁⟩ := initPre_ok hp
  refine WP.of_runBlock ⟨s₁, run₁, ⟨?_, x19₁, x20₁, x21₁, o₁, sp₁, m₁, rd₁, wr₁⟩⟩
  exact
  { x0 := x0₁, x1 := x1₁, x2 := x2₁, x3 := x3₁, klen := hp.klen
    kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
    ks := hp.k_s.sub_right (Region.sub_prefix (by decide))
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    reads := by
      rw [rd₁, wr₁, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨Kp, KL⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₁, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

/-! ## Between the calls, and after them -/

theorem initMid_ok {s : State} {St S : Addr} {R : Nat} (h19 : s.gpr .x19 = St) (h20 : s.gpr .x20 = S)
    (h21 : s.gpr .x21 = BitVec.ofNat 64 R) :
    ∃ s', runBlock isa initMid s = some s' ∧ s'.gpr .x0 = St ∧ s'.gpr .x1 = BitVec.ofNat 64 R ∧
      s'.gpr .x2 = St + BitVec.ofNat 64 240 ∧ s'.gpr .x3 = S ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [initMid, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, h19], by simp [gpr_write, h21], by simp [gpr_write, h19],
    by simp [gpr_write, h20], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-- The memory after zeroing the chaining value. -/
def zeroCv (m : Mem) (St : Addr) : Mem :=
  (m.writeW (St + BitVec.ofNat 64 272) (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 280) (0 : BitVec 64)

theorem zeroCv_eq (m : Mem) (St : Addr) : zeroCv m St = Proof.Cmac.zero2 m (St + BitVec.ofNat 64 272) := by
  rw [zeroCv, Proof.Cmac.zero2, Offset.add_add]

theorem initPost_ok {s : State} {St S : Addr} (h19 : s.gpr .x19 = St) (h20 : s.gpr .x20 = S)
    (w₁ : InRegions s.wr (St + BitVec.ofNat 64 272) 8) (w₂ : InRegions s.wr (St + BitVec.ofNat 64 280) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2176) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2184) 8)
    (r₃ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2192) 8)
    (r₄ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2200) 8) :
    ∃ s', runBlock isa initPost s = some s' ∧
      s'.gpr .x19 = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 2176) 64 ∧
      s'.gpr .x20 = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 2184) 64 ∧
      s'.gpr .x21 = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 2192) 64 ∧
      s'.gpr .x30 = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 2200) 64 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = zeroCv s.mem St := by
  refine ⟨_, by
    simp (config := {decide := true}) only [initPost, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write,
      wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq, h19, h20,
      w₁, w₂, r₁, r₂, r₃, r₄]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r a b c d f => by simp [gpr_write, a, b, c, d, f], rfl, ?_⟩
  all_goals simp [gpr_write, mem_write, zeroCv, Mem.readW, Mem.writeW]

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ : State) (St S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : SArgs s St (St + BitVec.ofNat 64 240) S (KL / 4 + 6)
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = S
  keep : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initMid_wp {s₀ s : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL)
    (h19 : s.gpr .x19 = St) (h20 : s.gpr .x20 = S) (h21 : s.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6))
    (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hk : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → s.gpr r = s₀.gpr r) :
    WP isa (.block initMid) s (IMid₂ s₀ St S KL s.mem) := by
  obtain ⟨s', run, x0, x1, x2, x3, sv, sp, mem, rd, wr⟩ := initMid_ok h19 h20 h21
  have hw := hp.wSt
  have kSt : Region.Sub ⟨St + BitVec.ofNat 64 240, 32⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  refine WP.of_runBlock ⟨s', run, ⟨?_, by rw [sv _ (by simp [preserved]), h19],
    by rw [sv _ (by simp [preserved]), h20], fun r hr a b c d => by rw [sv r hr, hk r hr a b c d],
    by rw [sp, hsp], mem, by rw [rd, hrd], by rw [wr, hwr]⟩⟩
  exact
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, rounds := hp.rounds
    wk := Offset.base_disjoint St (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
    wrapK := by rw [toNat_add_lt St hw (by decide)]; omega
    wrapS := by have := hp.wS; omega
    reads := by
      rw [rd, wr, hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

/-! ## The whole function -/

theorem init_wp (v : Ctr32Impl) {s₀ : State} (h0 : initAArch64.pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => GprAbi s₀ s' ∧ initAArch64.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x1 = Kp at hp
  generalize s₀.gpr .x3 = S at hp
  generalize (s₀.gpr .x2).toNat = KL at hp
  have hw := hp.wSt
  have hsw := hp.wS
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ek_call v h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₂.gpr r = s₁.gpr r := h₂.saved r hr h30
  refine WP.seq (WP.mono (initMid_wp hp (by rw [g₂ _ (by simp [preserved]) (by decide), h₁.x19])
    (by rw [g₂ _ (by simp [preserved]) (by decide), h₁.x20])
    (by rw [g₂ _ (by simp [preserved]) (by decide), h₁.x21]) (by rw [h₂.sp, h₁.sp]) (by rw [h₂.rd, h₁.rd])
    (by rw [h₂.wr, h₁.wr]) (fun r hr a b c d => by rw [g₂ r hr d, h₁.other r hr a b c])) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (sub_call v _ h₃.args) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₄.gpr r = s₃.gpr r := h₄.saved r hr h30
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₄.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions s₄.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inR (d : Nat) (hd : d + 8 ≤ 2304) : InRegions (s₄.rd ++ s₄.wr) (S + BitVec.ofNat 64 d) 8 := by
    obtain ⟨r, hr, hc⟩ := inS d hd; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨s₅, run₅, x19₅, x20₅, x21₅, x30₅, keep₅, sp₅, m₅⟩ := initPost_ok (s := s₄) (St := St) (S := S)
    (by rw [g₄ _ (by simp [preserved]) (by decide), h₃.x19])
    (by rw [g₄ _ (by simp [preserved]) (by decide), h₃.x20])
    (inSt 272 (by decide)) (inSt 280 (by decide)) (inR 2176 (by decide)) (inR 2184 (by decide))
    (inR 2192 (by decide)) (inR 2200 (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  -- The memory, step by step.
  have fz : Frame [⟨St + BitVec.ofNat 64 272, 16⟩] s₄.mem (zeroCv s₄.mem St) := by
    rw [zeroCv_eq]; exact Proof.Cmac.frame_store2 _ _ _
  have f₁ : Frame [⟨S + BitVec.ofNat 64 2176, 32⟩] s₀.mem s₁.mem := by
    rw [h₁.mem]; exact initSavedMem_frame _ _
  have f₂ : Frame [⟨St, 240⟩, ⟨S, 512⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩] s₃.mem s₄.mem := h₄.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  -- The saved registers.
  have dSv (r : Region) (hr : r ∈ [⟨St, 240⟩, ⟨S, 512⟩, ⟨St + BitVec.ofNat 64 240, 32⟩,
      ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 272, 16⟩]) (d : Nat) (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2304) :
      (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
  have rd' (d : Nat) (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2304) :
      (zeroCv s₄.mem St).readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    have c := Region.contains_self (S + BitVec.ofNat 64 d) 8
    rw [fz.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]) d hd hd') (by decide),
      f₄.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl <;> simp) d hd hd') (by decide), m₃,
      f₂.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl <;> simp) d hd hd') (by decide)]
  obtain ⟨sv₁, sv₂, sv₃, sv₄⟩ := initSaved_read s₀ S
  have m₁ := h₁.mem
  -- The state, outside what the last block writes.
  have dSt (d n : Nat) (hd : d + n ≤ 272) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩]) :
      (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega)
  have hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by
    have := hp.klen; simp only [Spec.Aes.rounds]; omega
  refine ⟨⟨fun r hr => ?_, by rw [sp₅, h₄.sp, h₃.sp]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₅, rd' 2176 (by decide) (by decide), m₁]; exact sv₁
    by_cases h20 : r = .x20
    · subst h20; rw [x20₅, rd' 2184 (by decide) (by decide), m₁]; exact sv₂
    by_cases h21 : r = .x21
    · subst h21; rw [x21₅, rd' 2192 (by decide) (by decide), m₁]; exact sv₃
    by_cases h30 : r = .x30
    · subst h30; rw [x30₅, rd' 2200 (by decide) (by decide), m₁]; exact sv₄
    have h9 : r ≠ .x9 := by rintro rfl; simp [preserved] at hr
    rw [keep₅ r h19 h20 h21 h30 h9, g₄ r hr h30, h₃.keep r hr h19 h20 h21 h30]
  · show Spec.Cmac.Repr s₅.mem (s₀.gpr .x0) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat) []
    rw [hp.x0, hp.x1, hp.x2, Proof.Cmac.Stream.repr_iff]
    have hkey : Spec.Aes.bytesAt s₁.mem Kp KL = Spec.Aes.bytesAt s₀.mem Kp KL :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.k_s.sub_right (Offset.sub_base S (by decide))) (by have := hp.wK; omega)
    have hlen : (Spec.Aes.bytesAt s₀.mem Kp KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    -- The schedule, from the first call on.
    have sch : ∀ {d n : Nat}, d + n ≤ 240 → Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₂.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [m₅, Proof.Cmac.bytesAt_frame fz (dSt d n (by omega)) (by omega),
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega) (by omega) (by omega)
          · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).sub_right (Region.sub_prefix (by decide)))
          (by omega), m₃]
    have hsch : Spec.Aes.bytesAt s₂.mem St (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp KL) := by rw [h₂.out, hkey]
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (KL / 4) + 1)) (by omega)
      rw [k0] at this; rw [this, hsch]
    · have e : Spec.Aes.bytesAt s₅.mem (St + 240) 32 = Spec.Aes.bytesAt s₄.mem (St + 240) 32 := by
        rw [m₅]; exact Proof.Cmac.bytesAt_frame fz (dSt 240 32 (by decide)) (by decide)
      rw [e]
      refine h₄.out.trans ?_
      rw [m₃, show KL / 4 + 6 = Spec.Aes.rounds (KL / 4) from rfl, hsch]
      simp only [Spec.Cmac.aes, hlen]
    · rw [m₅, zeroCv_eq]; exact (Proof.Cmac.zero2_bytes _ _).trans rfl

/-! ## Constant time -/

/-- What the call of `vg_aes_expand_key` leaves, for `initMid`. -/
structure IAfter (s₀ : State) (St S : Addr) (KL : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = S
  x21 : s.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6)
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ek_after (v : Ctr32Impl) {s₀ s : State} {St Kp S : Addr} {KL : Nat} (h : IMid₁ s₀ St Kp S KL s) :
    WP isa (.call v.expand.name v.expand.code) s (IAfter s₀ St S KL) :=
  WP.mono (ek_call v h.args) fun _ h₂ =>
    ⟨by rw [h₂.saved _ (by simp [preserved]) (by decide), h.x19],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h.x20],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h.x21], by rw [h₂.sp, h.sp],
      fun r hr a b c d => by rw [h₂.saved r hr d, h.other r hr a b c], by rw [h₂.rd, h.rd], by rw [h₂.wr, h.wr]⟩

theorem init_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : initAArch64.pre s₀) (h0' : initAArch64.pre s₀')
    (hq : initAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init v.expand v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := hq
  have hp := IPre.of h0
  have hp' : IPre s₀' (s₀.gpr .x0) (s₀.gpr .x1) (s₀.gpr .x3) (s₀.gpr .x2).toNat := by
    rw [q0, q1, q2, q3]; exact IPre.of h0'
  generalize s₀.gpr .x0 = St at hp hp'
  generalize s₀.gpr .x1 = Kp at hp hp'
  generalize s₀.gpr .x3 = S at hp hp'
  generalize (s₀.gpr .x2).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21]) (.block initMid) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q4 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := IMid₁ s₀ St Kp S KL) (F₂ := IMid₁ s₀' St Kp S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩
  have e := (ek_rel v (P := fun a b => IMid₁ s₀ St Kp S KL a ∧ IMid₁ s₀' St Kp S KL b)
    fun a b h => ⟨h.1.args, h.2.args, by rw [h.1.sp, h.2.sp, q4]⟩).wp
    (F₁ := IAfter s₀ St S KL) (F₂ := IAfter s₀' St S KL) fun a b h => ⟨ek_after v h.1, ek_after v h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => IAfter s₀ St S KL a ∧ IAfter s₀' St S KL b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q4]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x20, h.2.x20]
      · rw [h.1.x21, h.2.x21]) hB).wp
    (F₁ := fun (s : State) => ∃ m, IMid₂ s₀ St S KL m s) (F₂ := fun (s : State) => ∃ m, IMid₂ s₀' St S KL m s)
    fun a b h => ⟨WP.mono (initMid_wp hp h.1.x19 h.1.x20 h.1.x21 h.1.sp h.1.rd h.1.wr h.1.keep)
        fun _ h => ⟨_, h⟩,
      WP.mono (initMid_wp hp' h.2.x19 h.2.x20 h.2.x21 h.2.sp h.2.rd h.2.wr h.2.keep) fun _ h => ⟨_, h⟩⟩
  have sk := (sub_rel v ("vg_cmac_aes_subkeys" ++ v.suffix)
    (P := fun a b => (∃ m, IMid₂ s₀ St S KL m a) ∧ ∃ m, IMid₂ s₀' St S KL m b)
    fun a b ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨h₁.args, h₂.args, by rw [h₁.sp, h₂.sp, q4]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = St ∧ s.gpr .x20 = S ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = St ∧ s.gpr .x20 = S ∧ s.sp = s₀'.sp)
    fun a b ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ =>
      ⟨WP.mono (sub_call v _ h₁.args) fun _ h => ⟨by rw [h.saved _ (by simp [preserved]) (by decide), h₁.x19],
          by rw [h.saved _ (by simp [preserved]) (by decide), h₁.x20], by rw [h.sp, h₁.sp]⟩,
        WP.mono (sub_call v _ h₂.args) fun _ h => ⟨by rw [h.saved _ (by simp [preserved]) (by decide), h₂.x19],
          by rw [h.saved _ (by simp [preserved]) (by decide), h₂.x20], by rw [h.sp, h₂.sp]⟩⟩
  have p := RelCT.taint (A := taint)
    (P := fun a b => (a.gpr .x19 = St ∧ a.gpr .x20 = S ∧ a.sp = s₀.sp) ∧
      b.gpr .x19 = St ∧ b.gpr .x20 = S ∧ b.sp = s₀'.sp) _
    (fun a b h => by
      refine agree_of (by rw [h.1.2.2, h.2.2.2, q4]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem init_ct (v : Ctr32Impl) :
    ConstantTime isa initAArch64.pre initAArch64.pub (init v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.AArch64
