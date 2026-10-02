import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Impl.ChaCha20.AArch64.Stream

/-!
# Streaming ChaCha20 on AArch64: `init` and `set_nonce`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20

open VG.AArch64
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt)

/-- AArch64 contract for `vg_chacha20_set_nonce(state = x0, nonce = x1)`. -/
def setNonceAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 768⟩
    let nonce : Region := ⟨s.gpr .x1, 16⟩
    s.rd = [nonce] ∧ s.wr = [state] ∧ state.Disjoint nonce
  post s s' :=
    keyAt s'.mem (s.gpr .x0) = keyAt s.mem (s.gpr .x0) ∧
      restAt s'.mem (s.gpr .x0) = keystreamOf (keyAt s.mem (s.gpr .x0)) (bytesAt s.mem (s.gpr .x1) 16)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

/-- AArch64 contract for `vg_chacha20_init(state = x0, key = x1, nonce = x2)`. -/
def initAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 768⟩
    let key : Region := ⟨s.gpr .x1, 32⟩
    let nonce : Region := ⟨s.gpr .x2, 16⟩
    s.rd = [key, nonce] ∧ s.wr = [state] ∧ state.Disjoint key ∧ state.Disjoint nonce
  post s s' :=
    keyAt s'.mem (s.gpr .x0) = bytesAt s.mem (s.gpr .x1) 32 ∧
      restAt s'.mem (s.gpr .x0) = keystreamOf (bytesAt s.mem (s.gpr .x1) 32) (bytesAt s.mem (s.gpr .x2) 16)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.AArch64.Stream

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Stream
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt wordLE)

/-- No instruction of `c` writes a callee-saved register. -/
def Untouched (c : Prog isa) : Prop := ∀ r ∈ preserved, ∀ i ∈ instrs c, dstOf i ≠ some r

/-- What `set_nonce` needs of the state it runs from. -/
structure NPre (s : State) (st np : Addr) : Prop where
  x0 : s.gpr .x0 = st
  x1 : s.gpr .x1 = np
  w_st : ∀ d, d + 8 ≤ 768 → InRegions s.wr (st + BitVec.ofNat 64 d) 8
  r_n : ∀ d, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (np + BitVec.ofNat 64 d) 8

/-- The constants as the code builds them (`movz`, then `movk` of each half-word). -/
def c0 : BitVec 64 := 0x3320646e61707865
def c1 : BitVec 64 := 0x6b20657479622d32

theorem c0_eq : ((BitVec.setWidth 64 (30821 : BitVec 16) <<< (16 * 0) &&& ~~~((65535 : BitVec 64) <<< (16 * 1)) |||
    BitVec.setWidth 64 (24944 : BitVec 16) <<< (16 * 1)) &&& ~~~((65535 : BitVec 64) <<< (16 * 2)) |||
    BitVec.setWidth 64 (25710 : BitVec 16) <<< (16 * 2)) &&& ~~~((65535 : BitVec 64) <<< (16 * 3)) |||
    BitVec.setWidth 64 (13088 : BitVec 16) <<< (16 * 3) = c0 := by decide

theorem c1_eq : ((BitVec.setWidth 64 (11570 : BitVec 16) <<< (16 * 0) &&& ~~~((65535 : BitVec 64) <<< (16 * 1)) |||
    BitVec.setWidth 64 (31074 : BitVec 16) <<< (16 * 1)) &&& ~~~((65535 : BitVec 64) <<< (16 * 2)) |||
    BitVec.setWidth 64 (25972 : BitVec 16) <<< (16 * 2)) &&& ~~~((65535 : BitVec 64) <<< (16 * 3)) |||
    BitVec.setWidth 64 (27424 : BitVec 16) <<< (16 * 3) = c1 := by decide

/-- The memory `set_nonce` leaves, from `m`, for the state at `st` and the
nonce at `np`. -/
def nonceMem (m : Mem) (st np : Addr) : Mem :=
  ((((m.writeW (st + BitVec.ofNat 64 48) (m.readW np 64)).writeW (st + BitVec.ofNat 64 56)
    (m.readW (np + BitVec.ofNat 64 8) 64)).writeW (st + BitVec.ofNat 64 0) c0).writeW
    (st + BitVec.ofNat 64 8) c1).writeW (st + BitVec.ofNat 64 128)
    ((BitVec.setWidth 64 (1 : BitVec 16) <<< (16 * 2) - (m.readW np 32).setWidth 64) <<< 6)

set_option simprocs false in
theorem setNonce_exec {s : State} {st np : Addr} (hp : NPre s st np) :
    WP isa setNonce s fun s' => s'.mem = nonceMem s.mem st np ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) := by
  have o0 := hp.w_st 0 (by decide); have o8 := hp.w_st 8 (by decide)
  have o48 := hp.w_st 48 (by decide); have o56 := hp.w_st 56 (by decide)
  have o128 := hp.w_st 128 (by decide)
  have i0 := hp.r_n 0 (by decide); have i8 := hp.r_n 8 (by decide)
  have i0' : InRegions (s.rd ++ s.wr) (np + BitVec.ofNat 64 0) 4 := by
    obtain ⟨r, hr, hc⟩ := i0; exact ⟨r, hr, by simp only [Region.Contains] at hc ⊢; omega⟩
  apply WP.of_runBlock
  simp (config := {decide := true}) only [setNonceInstrs, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, Size.bytes, State.load, State.store, State.read, State.write, Size.bits,
    BitVec.setWidth_eq, Option.bind_some, Option.map_some, hp.x0, hp.x1, o0, o8, o48, o56, o128, i0, i8,
    i0', ite_true, ite_false, Option.some.injEq, exists_eq_left', c0_eq, c1_eq]
  refine ⟨by simp [nonceMem, Mem.writeW, Mem.readW], trivial, trivial, fun r hr => ?_⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true})


theorem c0_bytes : ∀ j < 8, c0.extractLsb' (8 * j) 8 = sigma.getD j 0 := by decide
theorem c1_bytes : ∀ j < 8, c1.extractLsb' (8 * j) 8 = sigma.getD (8 + j) 0 := by decide

/-- `64 × (2³² − c)`. -/
theorem left_eq (c : BitVec 32) :
    (BitVec.setWidth 64 (1 : BitVec 16) <<< (16 * 2) - c.setWidth 64) <<< 6 =
      BitVec.ofNat 64 (64 * (2 ^ 32 - c.toNat)) := by
  have hc := c.isLt
  have h0 : BitVec.setWidth 64 (1 : BitVec 16) <<< (16 * 2) - c.setWidth 64 = BitVec.ofNat 64 (2 ^ 32 - c.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [show BitVec.setWidth 64 (1 : BitVec 16) <<< (16 * 2) = BitVec.ofNat 64 (2 ^ 32) by decide, BitVec.toNat_sub,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [h0]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The words `set_nonce` leaves. -/
theorem nonceMem_word (m : Mem) (st np : Addr) {k : Nat} (hk : k < 8) :
    (nonceMem m st np).readW (st + BitVec.ofNat 64 (8 * k)) 64 =
      if k = 0 then c0 else if k = 1 then c1 else if k = 6 then m.readW (np + BitVec.ofNat 64 0) 64
      else if k = 7 then m.readW (np + BitVec.ofNat 64 8) 64 else m.readW (st + BitVec.ofNat 64 (8 * k)) 64 := by
  simp only [nonceMem]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  all_goals simp (config := {decide := true}) only [Nat.reduceMul, Mem.readW_writeW_self64,
    readW_writeW_ofNat, ite_true, ite_false]
  all_goals simp

theorem nonceMem_left (m : Mem) (st np : Addr) :
    leftAt (nonceMem m st np) st = 64 * (2 ^ 32 - (m.readW np 32).toNat) := by
  have hc := (m.readW np 32).isLt
  simp only [leftAt, nonceMem]
  rw [show (st + 128 : Addr) = st + BitVec.ofNat 64 128 from rfl, Mem.readW_writeW_self64, left_eq,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- What `set_nonce` leaves: the key kept, and the whole keystream of the
nonce. -/
theorem nonceMem_post (m : Mem) (st np : Addr) :
    keyAt (nonceMem m st np) st = keyAt m st ∧
      restAt (nonceMem m st np) st = keystreamOf (keyAt m st) (bytesAt m np 16) := by
  have hw : ∀ k, 0 ≤ k → k < 8 → (nonceMem m st np).readW (st + BitVec.ofNat 64 (8 * k)) 64 =
      (if k = 0 then c0 else if k = 1 then c1 else if k = 6 then m.readW (np + BitVec.ofNat 64 0) 64
      else if k = 7 then m.readW (np + BitVec.ofNat 64 8) 64 else m.readW (st + BitVec.ofNat 64 (8 * k)) 64) :=
    fun k _ hk => nonceMem_word _ _ _ hk
  have hm : ∀ k, 0 ≤ k → k < 8 → m.readW (st + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (st + BitVec.ofNat 64 (8 * k)) 64 := fun _ _ _ => rfl
  have hn : ∀ k, 0 ≤ k → k < 2 → m.readW (np + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (np + BitVec.ofNat 64 (8 * k)) 64 := fun _ _ _ => rfl
  refine stream_of_parts (by simp [keyAt, length_bytesAt]) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) ?_
  · rw [byte_of_words64 hw (Nat.zero_le _) (by omega)]
    by_cases h : i < 8
    · rw [show i / 8 = 0 by omega, ite_pos rfl, c0_bytes _ (Nat.mod_lt _ (by decide)), Nat.mod_eq_of_lt h]
    · rw [show i / 8 = 1 by omega, ite_neg (by decide), ite_pos rfl, c1_bytes _ (Nat.mod_lt _ (by decide)),
        show 8 + i % 8 = i by omega]
  · rw [byte_of_words64 hw (Nat.zero_le _) (by omega), keyAt,
      show (st + 16 : Addr) = st + BitVec.ofNat 64 16 from rfl, bytesAt_getD _ _ hi, Offset.add_add,
      byte_of_words64 hm (Nat.zero_le _) (by omega)]
    rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
  · rw [byte_of_words64 hw (Nat.zero_le _) (by omega), bytesAt_getD _ _ hi,
      byte_of_words64 hn (i := i) (Nat.zero_le _) (by omega)]
    by_cases h : i < 8
    · rw [show (48 + i) / 8 = 6 by omega, show i / 8 = 0 by omega, show (48 + i) % 8 = i % 8 by omega]
      simp
    · rw [show (48 + i) / 8 = 7 by omega, show i / 8 = 1 by omega, show (48 + i) % 8 = i % 8 by omega]
      simp
  · rw [nonceMem_left, wordLE_bytesAt _ _ (by decide)]


theorem contains_st (st : Addr) {d : Nat} (hd : d + 8 ≤ 768) :
    (⟨st, 768⟩ : Region).Contains (st + BitVec.ofNat 64 d) (64 / 8) :=
  Offset.contains_base _ hd (by omega)

theorem nonceMem_frame (m : Mem) (st np : Addr) : Frame [⟨st, 768⟩] m (nonceMem m st np) := by
  simp only [nonceMem]
  exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_st st (d := 48) (by decide))).writeW
    (List.mem_singleton_self _) _ (contains_st st (d := 56) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st st (d := 0) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st st (d := 8) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st st (d := 128) (by decide)))

theorem setNonce_untouched : Untouched setNonce :=
  fun r hr i hi => by
    have : ((instrs setNonce).all fun i => preserved.all fun r => dstOf i != some r) = true := by
      rw [← Code.allInstrs_eq]; decide +kernel
    simpa using List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr

theorem setNonce_ok (s : State) (hs : Proof.ChaCha20.setNonceAArch64.pre s) :
    ∃ t s', Exec isa setNonce s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.setNonceAArch64.post s s' := by
  obtain ⟨hrd, hwr, _⟩ := hs
  have hp : NPre s (s.gpr .x0) (s.gpr .x1) :=
    ⟨rfl, rfl, fun d hd => ⟨_, by rw [hwr]; exact List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩,
      fun d hd => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
        Offset.contains_base _ hd (by omega)⟩⟩
  obtain ⟨t, s', he, hm, -, -, -⟩ := setNonce_exec hp
  refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (setNonce_untouched r hr) he, Exec.sp he, Exec.preservedV he⟩, ?_⟩
  simp only [Proof.ChaCha20.setNonceAArch64]; rw [hm]; exact nonceMem_post _ _ _

theorem setNonce_ct :
    ConstantTime isa Proof.ChaCha20.setNonceAArch64.pre Proof.ChaCha20.setNonceAArch64.pub setNonce := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

/-- A state satisfying the precondition of `set_nonce`. -/
def setNonceSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 16⟩]
  wr := [⟨0x1000, 768⟩]

theorem setNonce_verified :
    Verified AArch64.target setNonce (Spec.ChaCha20.setNonceContract AArch64.abi) :=
  Verified.of_correct setNonce_ok setNonce_ct (by
    sig_implies [Spec.ChaCha20.setNonceContract, Spec.ChaCha20.setNonceSig,
      Proof.ChaCha20.setNonceAArch64, AArch64.abi, AArch64.argRegs] [setNonceSat] using setNonceSat)

/-! ## `init` -/

/-- The memory after the key is copied. -/
def keyMem (m : Mem) (st kp : Addr) : Mem :=
  (((m.writeW (st + BitVec.ofNat 64 16) (m.readW (kp + BitVec.ofNat 64 0) 64)).writeW (st + BitVec.ofNat 64 24)
    (m.readW (kp + BitVec.ofNat 64 8) 64)).writeW (st + BitVec.ofNat 64 32)
    (m.readW (kp + BitVec.ofNat 64 16) 64)).writeW (st + BitVec.ofNat 64 40) (m.readW (kp + BitVec.ofNat 64 24) 64)

set_option simprocs false in
theorem key_exec {s : State} {st kp : Addr} (hx0 : s.gpr .x0 = st) (hx1 : s.gpr .x1 = kp)
    (hw : ∀ d, d + 8 ≤ 768 → InRegions s.wr (st + BitVec.ofNat 64 d) 8)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 d) 8) :
    WP isa (.block keyInstrs) s fun s' => s'.mem = keyMem s.mem st kp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .x0 = st ∧ s'.gpr .x1 = s.gpr .x2 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) := by
  have o16 := hw 16 (by decide); have o24 := hw 24 (by decide)
  have o32 := hw 32 (by decide); have o40 := hw 40 (by decide)
  have i0 := hr 0 (by decide); have i8 := hr 8 (by decide)
  have i16 := hr 16 (by decide); have i24 := hr 24 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [keyInstrs, Impl.ChaCha20.AArch64.Xor.mov, runBlock_cons,
    runStep_some, runBlock_nil, exec, addr, Size.bytes, State.load, State.store, State.read, State.write,
    Size.bits, BitVec.setWidth_eq, Option.bind_some, Option.map_some, hx0, hx1, o16, o24, o32, o40, i0, i8,
    i16, i24, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨by simp [keyMem, Mem.writeW, Mem.readW], trivial, trivial, by simp, by simp, fun r hr => ?_⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true})

theorem keyMem_frame (m : Mem) (st kp : Addr) : Frame [⟨st, 768⟩] m (keyMem m st kp) := by
  simp only [keyMem]
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_st st (d := 16) (by decide))).writeW
    (List.mem_singleton_self _) _ (contains_st st (d := 24) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st st (d := 32) (by decide))).writeW (List.mem_singleton_self _) _ (contains_st st (d := 40) (by decide))

theorem keyMem_key (m : Mem) (st kp : Addr) : keyAt (keyMem m st kp) st = bytesAt m kp 32 := by
  have hw : ∀ k, 2 ≤ k → k < 6 → (keyMem m st kp).readW (st + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (kp + BitVec.ofNat 64 (8 * (k - 2))) 64 := by
    intro k h₁ h₂
    simp only [keyMem]
    obtain rfl | rfl | rfl | rfl : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    all_goals simp (config := {decide := true}) only [Nat.reduceMul, Nat.reduceSub, Mem.readW_writeW_self64,
      readW_writeW_ofNat]
  have hk : ∀ k, 0 ≤ k → k < 4 → m.readW (kp + BitVec.ofNat 64 (8 * k)) 64 = m.readW (kp + BitVec.ofNat 64 (8 * k)) 64 :=
    fun _ _ _ => rfl
  apply List.ext_getElem
  · simp [keyAt, length_bytesAt]
  · intro i h₁ h₂
    simp only [keyAt, length_bytesAt] at h₁
    rw [getElem_eq_getD, getElem_eq_getD, keyAt, show (st + 16 : Addr) = st + BitVec.ofNat 64 16 from rfl,
      bytesAt_getD _ _ h₁, bytesAt_getD _ _ h₁, Offset.add_add, byte_of_words64 hw (by omega) (by omega),
      byte_of_words64 hk (Nat.zero_le _) (by omega)]
    rw [show (16 + i) / 8 - 2 = i / 8 by omega, show (16 + i) % 8 = i % 8 by omega]

theorem init_eq : init = .block (keyInstrs ++ setNonceInstrs) := rfl

theorem init_ok (s : State) (hs : Proof.ChaCha20.initAArch64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.initAArch64.post s s' := by
  obtain ⟨hrd, hwr, hdk, hdn⟩ := hs
  have hw : ∀ d, d + 8 ≤ 768 → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨_, by rw [hwr]; exact List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩
  have h₁ := key_exec (s := s) rfl rfl hw fun d hd => ⟨_, by rw [hrd]; simp,
    Offset.contains_base (s.gpr .x1) (k := 32) hd (by omega)⟩
  rw [init_eq]
  obtain ⟨t, s', he, hm, hpost⟩ : WP isa (.block (keyInstrs ++ setNonceInstrs)) s fun s' =>
      s'.mem = nonceMem (keyMem s.mem (s.gpr .x0) (s.gpr .x1)) (s.gpr .x0) (s.gpr .x2) ∧
        ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
    refine WP.block_append (WP.mono h₁ fun s₁ ⟨m₁, rd₁, wr₁, x0₁, x1₁, g₁⟩ => ?_)
    have hp : NPre s₁ (s.gpr .x0) (s.gpr .x2) :=
      ⟨x0₁, x1₁, fun d hd => by rw [wr₁]; exact hw d hd, fun d hd => ⟨⟨s.gpr .x2, 16⟩,
        by rw [rd₁, wr₁, hrd]; simp, Offset.contains_base _ hd (by omega)⟩⟩
    exact WP.mono (setNonce_exec hp) fun s' ⟨m', _, _, g'⟩ =>
      ⟨by rw [m', m₁], fun r hr => by rw [g' r hr, g₁ r hr]⟩
  refine ⟨t, s', he, ⟨hpost, Exec.sp he, Exec.preservedV he⟩, ?_⟩
  obtain ⟨hk, hr⟩ := nonceMem_post (keyMem s.mem (s.gpr .x0) (s.gpr .x1)) (s.gpr .x0) (s.gpr .x2)
  have hn : bytesAt (keyMem s.mem (s.gpr .x0) (s.gpr .x1)) (s.gpr .x2) 16 = bytesAt s.mem (s.gpr .x2) 16 :=
    List.map_congr_left fun i hi => (keyMem_frame _ _ _).bytes (R := ⟨s.gpr .x2, 16⟩)
      (by simpa using hdn.symm) (show 16 ≤ 2 ^ 64 by decide) (List.mem_range.mp hi)
  simp only [Proof.ChaCha20.initAArch64]
  rw [hm, hk, hr, keyMem_key, hn]
  exact ⟨rfl, rfl⟩

theorem init_ct : ConstantTime isa Proof.ChaCha20.initAArch64.pre Proof.ChaCha20.initAArch64.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition of `init`. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x1000, 768⟩]

theorem init_verified : Verified AArch64.target init (Spec.ChaCha20.initContract AArch64.abi) :=
  Verified.of_correct init_ok init_ct (by
    sig_implies [Spec.ChaCha20.initContract, Spec.ChaCha20.initSig, Proof.ChaCha20.initAArch64,
      AArch64.abi, AArch64.argRegs] [initSat] using initSat)

end VG.Proof.ChaCha20.AArch64.Stream
