import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_init`

Untrusted: everything here is checked by Lean. The code saves `rbx`, `rbp`
and `r12` in the scratch buffer, expands the key into the state, derives
the subkeys after the schedule, zeroes the chaining value and restores the
registers: the state then represents the empty message. The code between
the calls is constant time by the taint analysis, and the calls by their
own proofs (`ek_rel`, `sub_rel`), their arguments pinned by `IMid₁` and
`IMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : Addr) (KL : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rsi : s₀.gpr .rsi = Kp
  rdx : (s₀.gpr .rdx).toNat = KL
  rcx : s₀.gpr .rcx = S
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_k : (⟨St, 304⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2304⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_k : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨Kp, KL⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2304⟩
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_k : (below (s₀.gpr .rsp) 16).Disjoint ⟨Kp, KL⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32

theorem IPre.of {s₀ : State} (h : initX86_64.pre s₀) :
    IPre s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rcx) (s₀.gpr .rdx).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

/-- The rounds, as `shr 2; add 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 64 KL >>> 2 + BitVec.signExtend 64 (6 : BitVec 32) = BitVec.ofNat 64 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

/-- The memory after saving the registers. -/
def initSavedMem (s : State) (S : Addr) : Mem :=
  ((s.mem.writeW (S + BitVec.ofNat 64 2176) (s.gpr .rbx)).writeW (S + BitVec.ofNat 64 2184) (s.gpr .rbp)).writeW
    (S + BitVec.ofNat 64 2192) (s.gpr .r12)

theorem initSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 24⟩] s.mem (initSavedMem s S) := by
  have c (d : Nat) (hd : d + 8 ≤ 24) : (⟨S + BitVec.ofNat 64 2176, 24⟩ : Region).Contains
      (S + BitVec.ofNat 64 (2176 + d)) 8 := by
    rw [← Offset.add_add]; exact Offset.contains_base _ hd (by omega)
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simpa using c 0 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _ (c 16 (by decide))

/-! ## Before the first call -/

theorem initPre_ok {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    ∃ s₁, runBlock isa initPre s₀ = some s₁ ∧ s₁.gpr .rdi = Kp ∧ s₁.gpr .rsi = BitVec.ofNat 64 KL ∧
      s₁.gpr .rdx = St ∧ s₁.gpr .rcx = S ∧ s₁.gpr .rbx = St ∧ s₁.gpr .rbp = S ∧
      s₁.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = initSavedMem s₀ S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega)⟩
  have hKL : s₀.gpr .rdx = BitVec.ofNat 64 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.rdx, toNat_ofNat (by rcases hp.klen with h | h | h <;> omega)])
  refine ⟨_, by
    simp (config := {decide := true}) only [initPre, initSaved, sOff, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, execAlu, execShift,
      State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      ite_true, ite_false, hp.rcx, inS 2176 (by decide),
      inS 2184 (by decide), inS 2192 (by decide)]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, ite_true, ite_false, hp.rdi, hp.rsi, hp.rcx, hKL, rounds_bv hp.klen, Nat.reduceAdd]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    fun r h₁ h₂ h₃ hr => ?_, rfl, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem initSaved_read (s : State) (S : Addr) :
    (initSavedMem s S).readW (S + BitVec.ofNat 64 2176) 64 = s.gpr .rbx ∧
      (initSavedMem s S).readW (S + BitVec.ofNat 64 2184) 64 = s.gpr .rbp ∧
      (initSavedMem s S).readW (S + BitVec.ofNat 64 2192) 64 = s.gpr .r12 := by
  have sp (a b : Nat) (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 2304) (hb : b + 8 ≤ 2304) :
      Mem.Sep (S + BitVec.ofNat 64 a) (64 / 8) (S + BitVec.ofNat 64 b) (64 / 8) :=
    Offset.sep S h (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [initSavedMem, Mem.readW_writeW_sep (sp 2176 2192 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sp 2176 2184 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [initSavedMem, Mem.readW_writeW_sep (sp 2184 2192 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [initSavedMem, Mem.readW_writeW_self64]

/-! ## Between the calls, and after them -/

theorem initMid_ok {s : State} {St S : Addr} {R : Nat} (hb : s.gpr .rbx = St) (hp : s.gpr .rbp = S)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 R) :
    ∃ s', runBlock isa initMid s = some s' ∧ s'.gpr .rdi = St ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.gpr .rdx = St + BitVec.ofNat 64 240 ∧ s'.gpr .rcx = S ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [initMid, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, hb, hp, h12, sx240]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The memory after zeroing the chaining value. -/
def zeroCv (m : Mem) (St : Addr) : Mem :=
  (m.writeW (St + BitVec.ofNat 64 272) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
    (St + BitVec.ofNat 64 280) (BitVec.setWidth 64 (0 : BitVec 32))

theorem zeroCv_eq (m : Mem) (St : Addr) : zeroCv m St = zero2 m (St + BitVec.ofNat 64 272) := by
  rw [zeroCv, zero2, Offset.add_add]

theorem initPost_ok {s : State} {St S : Addr} (hb : s.gpr .rbx = St) (hp : s.gpr .rbp = S)
    (w₁ : InRegions s.wr (St + BitVec.ofNat 64 272) 8) (w₂ : InRegions s.wr (St + BitVec.ofNat 64 280) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2176) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2184) 8)
    (r₃ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2192) 8) :
    ∃ s', runBlock isa initPost s = some s' ∧
      s'.gpr .rbx = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 2176) 64 ∧
      s'.gpr .rbp = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 2184) 64 ∧
      s'.gpr .r12 = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 2192) 64 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s'.gpr r = s.gpr r) ∧
      s'.mem = zeroCv s.mem St := by
  refine ⟨_, by
    simp (config := {decide := true}) only [initPost, sOff, runBlock_cons, runStep_some, runBlock_nil,
      at_, exec, readSrc, readSrc32, State.load64, State.store64, State.ea, State.setReg32, offset_nat,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true,
      ite_false, hb, hp, w₁, w₂, r₁, r₂, r₃, Nat.reduceAdd]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, mem_setReg, ite_true, ite_false]
  refine ⟨rfl, rfl, rfl, fun r h₁ h₂ h₃ hr => ?_, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## The whole function -/

/-- The regions the function writes: the state, the scratch buffer and the
stack its calls use. -/
abbrev IFrame (St S sp : Addr) : List Region := [⟨St, 304⟩, ⟨S, 2304⟩, below sp 16]

theorem IPre.rounds {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp St S KL
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = S
  r12 : s.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  other : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r
  mem : s.mem = initSavedMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    WP isa (.block initPre) s₀ (IMid₁ s₀ St Kp S KL) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, rbx₁, rbp₁, r12₁, rsp₁, o₁, m₁, rd₁, wr₁⟩ := initPre_ok hp
  refine WP.of_runBlock ⟨s₁, run₁, ⟨?_, rbx₁, rbp₁, r12₁, rsp₁, o₁, m₁, rd₁, wr₁⟩⟩
  exact
  { rdi := rdi₁, rsi := rsi₁, rdx := rdx₁, rcx := rcx₁, klen := hp.klen
    kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
    ks := hp.k_s.sub_right (Region.sub_prefix (by decide))
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    stkK := by rw [rsp₁]; exact hp.stk_k
    stkW := by rw [rsp₁]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkS := by rw [rsp₁]; exact hp.stk_s.sub_right (Region.sub_prefix (by decide))
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

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ : State) (St S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : SArgs s St (St + BitVec.ofNat 64 240) S (KL / 4 + 6)
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  keep : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initMid_wp {s₀ s : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL)
    (hb : s.gpr .rbx = St) (hbp : s.gpr .rbp = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6))
    (hsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hk : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r) :
    WP isa (.block initMid) s (IMid₂ s₀ St S KL s.mem) := by
  obtain ⟨s', run, rdi, rsi, rdx, rcx, sv, mem, rd, wr⟩ := initMid_ok hb hbp h12
  have hw := hp.wSt
  have rsp' : s'.gpr .rsp = s₀.gpr .rsp := by rw [sv _ (by simp [calleeSaved]), hsp]
  have kSt : Region.Sub ⟨St + BitVec.ofNat 64 240, 32⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  refine WP.of_runBlock ⟨s', run, ⟨?_, by rw [sv _ (by simp [calleeSaved]), hb],
    by rw [sv _ (by simp [calleeSaved]), hbp], rsp', fun r h₁ h₂ h₃ hr => by rw [sv r hr, hk r h₁ h₂ h₃ hr],
    mem, by rw [rd, hrd], by rw [wr, hwr]⟩⟩
  exact
  { rdi := rdi, rsi := rsi, rdx := rdx, rcx := rcx, rounds := hp.rounds
    wk := Offset.base_disjoint St (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
    stkW := by rw [rsp']; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkK := by rw [rsp']; exact hp.stk_st.sub_right kSt
    stkS := by rw [rsp']; exact hp.stk_s.sub_right (Region.sub_prefix (by decide))
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

theorem init_wp (v : Ctr32Impl) {s₀ : State} (h0 : initX86_64.pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ initX86_64.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rsi = Kp at hp
  generalize s₀.gpr .rcx = S at hp
  generalize (s₀.gpr .rdx).toNat = KL at hp
  have hw := hp.wSt
  have hsw := hp.wS
  have hR := hp.rounds
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ek_call v h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s₁.gpr r := h₂.saved r hr
  refine WP.seq (WP.mono (initMid_wp hp (by rw [g₂ _ (by simp [calleeSaved]), h₁.rbx])
    (by rw [g₂ _ (by simp [calleeSaved]), h₁.rbp]) (by rw [g₂ _ (by simp [calleeSaved]), h₁.r12])
    (by rw [g₂ _ (by simp [calleeSaved]), h₁.rsp]) (by rw [h₂.rd, h₁.rd]) (by rw [h₂.wr, h₁.wr])
    (fun r a b c hr => by rw [g₂ r hr, h₁.other r a b c hr])) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (sub_call v _ h₃.args) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ calleeSaved) : s₄.gpr r = s₃.gpr r := h₄.saved r hr
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₄.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions s₄.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inR (d : Nat) (hd : d + 8 ≤ 2304) : InRegions (s₄.rd ++ s₄.wr) (S + BitVec.ofNat 64 d) 8 := by
    obtain ⟨r, hr, hc⟩ := inS d hd; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨s₅, run₅, rbx₅, rbp₅, r12₅, keep₅, m₅⟩ := initPost_ok (s := s₄) (St := St) (S := S)
    (by rw [g₄ _ (by simp [calleeSaved]), h₃.rbx]) (by rw [g₄ _ (by simp [calleeSaved]), h₃.rbp])
    (inSt 272 (by decide)) (inSt 280 (by decide)) (inR 2176 (by decide)) (inR 2184 (by decide))
    (inR 2192 (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  -- The memory, step by step.
  have rsp₀ := hp.sp
  have fz : Frame [⟨St + BitVec.ofNat 64 272, 16⟩] s₄.mem (zeroCv s₄.mem St) := by
    rw [zeroCv_eq]; exact Proof.CmacAes.X86_64.frame_store2 _ _ _
  have f₁ : Frame [⟨S + BitVec.ofNat 64 2176, 24⟩] s₀.mem s₁.mem := by
    rw [h₁.mem]; exact initSavedMem_frame _ _
  have f₂ : Frame [⟨St, 240⟩, ⟨S, 512⟩, below (s₀.gpr .rsp) 16] s₁.mem s₂.mem := by
    rw [← h₁.rsp]; exact h₂.frame
  have f₄ : Frame [⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16] s₃.mem s₄.mem := by
    rw [← h₃.rsp]; exact h₄.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  -- The saved registers.
  have dSv (r : Region) (hr : r ∈ [⟨St, 240⟩, ⟨S, 512⟩, below (s₀.gpr .rsp) 16, ⟨St + BitVec.ofNat 64 240, 32⟩,
      ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 272, 16⟩]) (d : Nat) (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2304) :
      (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact hp.stk_s.symm.sub_left sub
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
        rcases hr with rfl | rfl | rfl <;> simp) d hd hd') (by decide), m₃,
      f₂.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl <;> simp) d hd hd') (by decide)]
  obtain ⟨sv₁, sv₂, sv₃⟩ := initSaved_read s₀ S
  have m₁ := h₁.mem
  -- The state, outside what the last block writes.
  have dSt (d n : Nat) (hd : d + n ≤ 272) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩]) :
      (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega)
  have hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by simp only [Spec.Aes.rounds]; omega
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rbx₅, rd' 2176 (by decide) (by decide), m₁]; exact sv₁
    · rw [rbp₅, rd' 2184 (by decide) (by decide), m₁]; exact sv₂
    · rw [keep₅ _ (by decide) (by decide) (by decide) (by simp [calleeSaved]),
        g₄ _ (by simp [calleeSaved]), h₃.rsp]
    · rw [r12₅, rd' 2192 (by decide) (by decide), m₁]; exact sv₃
    all_goals rw [keep₅ _ (by decide) (by decide) (by decide) (by simp [calleeSaved]),
      g₄ _ (by simp [calleeSaved]), h₃.keep _ (by decide) (by decide) (by decide) (by simp [calleeSaved])]
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    have stS : Region.Sub ⟨S, 2176⟩ ⟨S, 2304⟩ := Region.sub_prefix (by decide)
    rw [m₅, fz.readW c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_st.sub_right (Offset.sub_base St (by decide))) (by decide),
      f₄.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.ret_st.sub_right (Offset.sub_base St (by decide))
        · exact hp.ret_s.sub_right stS
        · exact Offset.base_disjoint_below _ (by decide)) (by decide), m₃,
      f₂.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.ret_st.sub_right (Region.sub_prefix (by decide))
        · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
        · exact Offset.base_disjoint_below _ (by decide)) (by decide),
      f₁.readW c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_s.sub_right (Offset.sub_base S (by decide))) (by decide)]
  · show Spec.Cmac.Repr s₅.mem (s₀.gpr .rdi) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rsi) (s₀.gpr .rdx).toNat) []
    rw [hp.rdi, hp.rsi, hp.rdx, Proof.Cmac.Stream.repr_iff]
    have hkey : Spec.Aes.bytesAt s₁.mem Kp KL = Spec.Aes.bytesAt s₀.mem Kp KL :=
      bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.k_s.sub_right (Offset.sub_base S (by decide))) (by have := hp.wK; omega)
    have hlen : (Spec.Aes.bytesAt s₀.mem Kp KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    -- The schedule, from the first call on.
    have sch : ∀ {d n : Nat}, d + n ≤ 240 → Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₂.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [m₅, bytesAt_frame fz (dSt d n (by omega)) (by omega), bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint St (by omega) (by omega) (by omega)
        · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).sub_right (Region.sub_prefix (by decide))
        · exact (hp.stk_st.sub_right (Offset.sub_base St (by omega))).symm) (by omega), m₃]
    have hsch : Spec.Aes.bytesAt s₂.mem St (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp KL) := by rw [h₂.out, hkey]
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (KL / 4) + 1)) (by omega)
      rw [k0] at this; rw [this, hsch]
    · have e : Spec.Aes.bytesAt s₅.mem (St + 240) 32 = Spec.Aes.bytesAt s₄.mem (St + 240) 32 := by
        rw [m₅]; exact bytesAt_frame fz (dSt 240 32 (by decide)) (by decide)
      rw [e]
      refine h₄.out.trans ?_
      rw [m₃, show KL / 4 + 6 = Spec.Aes.rounds (KL / 4) from rfl, hsch]
      simp only [Spec.Cmac.aes, hlen]
    · rw [m₅, zeroCv_eq]; exact (zero2_bytes _ _).trans rfl

/-! ## Constant time -/

/-- What the call of `vg_aes_expand_key` leaves, for `initMid`. -/
structure IAfter (s₀ : State) (St S : Addr) (KL : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = S
  r12 : s.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  keep : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ek_after (v : Ctr32Impl) {s₀ s : State} {St Kp S : Addr} {KL : Nat} (h : IMid₁ s₀ St Kp S KL s) :
    WP isa (.call v.expand.name v.expand.code) s (IAfter s₀ St S KL) :=
  WP.mono (ek_call v h.args) fun _ h₂ =>
    ⟨by rw [h₂.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₂.saved _ (by simp [calleeSaved]), h.rbp],
      by rw [h₂.saved _ (by simp [calleeSaved]), h.r12], by rw [h₂.saved _ (by simp [calleeSaved]), h.rsp],
      fun r a b c hr => by rw [h₂.saved r hr, h.other r a b c hr], by rw [h₂.rd, h.rd], by rw [h₂.wr, h.wr]⟩

theorem init_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : initX86_64.pre s₀) (h0' : initX86_64.pre s₀')
    (hq : initX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init v.expand v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := IPre.of h0
  have hp' : IPre s₀' (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rcx) (s₀.gpr .rdx).toNat := by
    rw [q2, q3, q4, q5]; exact IPre.of h0'
  generalize s₀.gpr .rdi = St at hp hp'
  generalize s₀.gpr .rsi = Kp at hp hp'
  generalize s₀.gpr .rcx = S at hp hp'
  generalize (s₀.gpr .rdx).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .rsp]) (.block initMid) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := IMid₁ s₀ St Kp S KL) (F₂ := IMid₁ s₀' St Kp S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩
  have e := (ek_rel v (P := fun a b => IMid₁ s₀ St Kp S KL a ∧ IMid₁ s₀' St Kp S KL b)
    fun a b h => ⟨_, _, _, _, h.1.args, h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := IAfter s₀ St S KL) (F₂ := IAfter s₀' St S KL) fun a b h => ⟨ek_after v h.1, ek_after v h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => IAfter s₀ St S KL a ∧ IAfter s₀' St S KL b) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx]
      · rw [h.1.rbp, h.2.rbp]
      · rw [h.1.r12, h.2.r12]
      · rw [h.1.rsp, h.2.rsp, q1]) hB).wp
    (F₁ := fun (s : State) => ∃ m, IMid₂ s₀ St S KL m s) (F₂ := fun (s : State) => ∃ m, IMid₂ s₀' St S KL m s)
    fun a b h => ⟨WP.mono (initMid_wp hp h.1.rbx h.1.rbp h.1.r12 h.1.rsp h.1.rd h.1.wr h.1.keep)
        fun _ h => ⟨_, h⟩,
      WP.mono (initMid_wp hp' h.2.rbx h.2.rbp h.2.r12 h.2.rsp h.2.rd h.2.wr h.2.keep) fun _ h => ⟨_, h⟩⟩
  have sk := (sub_rel v ("vg_cmac_aes_subkeys" ++ v.suffix)
    (P := fun a b => (∃ m, IMid₂ s₀ St S KL m a) ∧ ∃ m, IMid₂ s₀' St S KL m b)
    fun a b ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨_, _, _, _, h₁.args, h₂.args, by rw [h₁.rsp, h₂.rsp, q1]⟩).wp
    (F₁ := fun (s : State) => s.gpr .rbx = St ∧ s.gpr .rbp = S)
    (F₂ := fun (s : State) => s.gpr .rbx = St ∧ s.gpr .rbp = S)
    fun a b ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ =>
      ⟨WP.mono (sub_call v _ h₁.args) fun _ h => ⟨by rw [h.saved _ (by simp [calleeSaved]), h₁.rbx],
          by rw [h.saved _ (by simp [calleeSaved]), h₁.rbp]⟩,
        WP.mono (sub_call v _ h₂.args) fun _ h => ⟨by rw [h.saved _ (by simp [calleeSaved]), h₂.rbx],
          by rw [h.saved _ (by simp [calleeSaved]), h₂.rbp]⟩⟩
  have p := RelCT.taint (A := taint)
    (P := fun a b => (a.gpr .rbx = St ∧ a.gpr .rbp = S) ∧ b.gpr .rbx = St ∧ b.gpr .rbp = S) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2, h.2.2]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem init_ct (v : Ctr32Impl) :
    ConstantTime isa initX86_64.pre initX86_64.pub (init v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86_64
