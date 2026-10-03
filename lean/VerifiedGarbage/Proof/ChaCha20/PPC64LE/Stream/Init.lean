import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Xor
import VerifiedGarbage.Impl.ChaCha20.PPC64LE.Stream

/-!
# Streaming ChaCha20 on PPC64LE: `init` and `set_nonce`

Untrusted: everything here is checked by Lean. The same structure as the
AArch64 proof (`VG.Proof.ChaCha20.AArch64.Stream`), but for the words of the
state, which are all written 32 bits at a time.
-/

namespace VG.Proof.ChaCha20

open VG.PPC64LE
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt)

/-- PPC64LE contract for `vg_chacha20_set_nonce(state = r3, nonce = r4)`. -/
def setNoncePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 768⟩
    let nonce : Region := ⟨s.gpr .r4, 16⟩
    s.rd = [nonce] ∧ s.wr = [state] ∧ state.Disjoint nonce
  post s s' :=
    keyAt s'.mem (s.gpr .r3) = keyAt s.mem (s.gpr .r3) ∧
      restAt s'.mem (s.gpr .r3) = keystreamOf (keyAt s.mem (s.gpr .r3)) (bytesAt s.mem (s.gpr .r4) 16)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp

/-- PPC64LE contract for `vg_chacha20_init(state = r3, key = r4, nonce = r5)`. -/
def initPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 768⟩
    let key : Region := ⟨s.gpr .r4, 32⟩
    let nonce : Region := ⟨s.gpr .r5, 16⟩
    s.rd = [key, nonce] ∧ s.wr = [state] ∧ state.Disjoint key ∧ state.Disjoint nonce
  post s s' :=
    keyAt s'.mem (s.gpr .r3) = bytesAt s.mem (s.gpr .r4) 32 ∧
      restAt s'.mem (s.gpr .r3) = keystreamOf (bytesAt s.mem (s.gpr .r4) 32) (bytesAt s.mem (s.gpr .r5) 16)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.ChaCha20.PPC64LE.Stream
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt wordLE)

theorem write64_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp [Mem.writeW]
theorem write32_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.write a 4 v = m.writeW a v := by
  simp [Mem.writeW]
theorem read64_eq (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by simp [Mem.readW]
theorem read32_eq (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by simp [Mem.readW]

theorem setWidth_32_64_32 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v :=
  BitVec.setWidth_setWidth_of_le _ (by decide)

/-- `lis_ori`, with the width as the model writes it. -/
theorem lis_ori' (x : BitVec 32) :
    (((x.extractLsb' 16 16 ++ (0 : BitVec 16)).signExtend 64 |||
      (x.extractLsb' 0 16).setWidth 64)).setWidth (8 * 4) = x := lis_ori x

theorem setWidth_32_64_32' (v : BitVec 32) : (v.setWidth 64).setWidth (8 * 4) = v := setWidth_32_64_32 v

/-- No instruction of the code writes a callee-saved register. -/
theorem keeps {c : Prog isa} (hc : ((instrs c).all fun i => preserved.all fun r => dstOf i != some r) = true)
    {s s' : State} {t : List Leak} (he : Exec isa c s t s') (hn : c.noCalls = true := by decide +kernel) :
    ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr =>
  Exec.gpr (fun i hi => by simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr) he (.inl hn)

/-- What `set_nonce` needs of the state it runs from. -/
structure NPre (s : State) (st np : Addr) : Prop where
  r3 : s.gpr .r3 = st
  r4 : s.gpr .r4 = np
  w_st : ∀ d n, d + n ≤ 768 → InRegions s.wr (st + BitVec.ofNat 64 d) n
  r_n : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (np + BitVec.ofNat 64 d) n

/-- The constants, as words. -/
def sigmaW (k : Nat) : BitVec 32 :=
  if k = 0 then 0x61707865 else if k = 1 then 0x3320646e else if k = 2 then 0x79622d32 else 0x6b206574

/-- The bytes left, as the code computes them. -/
def leftW (c : BitVec 32) : BitVec 64 := (BitVec.ofNat 64 1 <<< 32 - c.setWidth 64) <<< 6

/-- The memory `set_nonce` leaves, from `m`, for the state at `st` and the
nonce at `np`. -/
def nonceMem (m : Mem) (st np : Addr) : Mem :=
  ((((((((m.writeW (st + BitVec.ofNat 64 48) (m.readW (np + BitVec.ofNat 64 0) 32)).writeW
    (st + BitVec.ofNat 64 52) (m.readW (np + BitVec.ofNat 64 4) 32)).writeW
    (st + BitVec.ofNat 64 56) (m.readW (np + BitVec.ofNat 64 8) 32)).writeW
    (st + BitVec.ofNat 64 60) (m.readW (np + BitVec.ofNat 64 12) 32)).writeW
    (st + BitVec.ofNat 64 0) (sigmaW 0)).writeW (st + BitVec.ofNat 64 4) (sigmaW 1)).writeW
    (st + BitVec.ofNat 64 8) (sigmaW 2)).writeW (st + BitVec.ofNat 64 12) (sigmaW 3)).writeW
    (st + BitVec.ofNat 64 128) (leftW (m.readW (np + BitVec.ofNat 64 0) 32))

set_option simprocs false in
theorem setNonce_exec {s : State} {st np : Addr} (hp : NPre s st np) :
    WP isa setNonce s fun s' => s'.mem = nonceMem s.mem st np ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o0 := hp.w_st 0 4 (by decide); have o4 := hp.w_st 4 4 (by decide)
  have o8 := hp.w_st 8 4 (by decide); have o12 := hp.w_st 12 4 (by decide)
  have o48 := hp.w_st 48 4 (by decide); have o52 := hp.w_st 52 4 (by decide)
  have o56 := hp.w_st 56 4 (by decide); have o60 := hp.w_st 60 4 (by decide)
  have o128 := hp.w_st 128 8 (by decide)
  have i0 := hp.r_n 0 4 (by decide); have i4 := hp.r_n 4 4 (by decide)
  have i8 := hp.r_n 8 4 (by decide); have i12 := hp.r_n 12 4 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [setNonceInstrs, word, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, Size.bytes, State.load, State.store, State.write,
    BitVec.setWidth_eq, Option.bind_some, Option.map_some, hp.r3, hp.r4, o0, o4, o8, o12, o48, o52, o56,
    o60, o128, i0, i4, i8, i12, ite_true, ite_false, Option.some.injEq, exists_eq_left', List.cons_append,
    List.nil_append, write32_eq, write64_eq, read32_eq]
  simp (config := {decide := true}) only [nonceMem, sigmaW, leftW, setWidth_32_64_32', lis_ori',
    ite_true, ite_false, BitVec.add_zero]

/-- `64 × (2³² − c)`. -/
theorem leftW_eq (c : BitVec 32) : leftW c = BitVec.ofNat 64 (64 * (2 ^ 32 - c.toNat)) := by
  have hc := c.isLt
  have h0 : BitVec.ofNat 64 1 <<< 32 - c.setWidth 64 = BitVec.ofNat 64 (2 ^ 32 - c.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [show BitVec.ofNat 64 1 <<< 32 = BitVec.ofNat 64 (2 ^ 32) by decide, BitVec.toNat_sub,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [leftW, h0]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem sigma_bytes : ∀ i < 16, (sigmaW (i / 4)).extractLsb' (8 * (i % 4)) 8 = sigma.getD i 0 := by decide

/-- The words `set_nonce` leaves. -/
theorem nonceMem_word (m : Mem) (st np : Addr) {k : Nat} (hk : k < 16) :
    (nonceMem m st np).readW (st + BitVec.ofNat 64 (4 * k)) 32 =
      if k < 4 then sigmaW k else if 12 ≤ k then m.readW (np + BitVec.ofNat 64 (4 * (k - 12))) 32
      else m.readW (st + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [nonceMem]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
      k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  all_goals simp (config := {decide := true}) only [Nat.reduceMul, Nat.reduceSub, Mem.readW_writeW_self32,
    readW_writeW_ofNat, ite_true, ite_false]

theorem nonceMem_left (m : Mem) (st np : Addr) :
    leftAt (nonceMem m st np) st = 64 * (2 ^ 32 - (m.readW np 32).toNat) := by
  have hc := (m.readW np 32).isLt
  simp only [leftAt, nonceMem]
  rw [show (st + 128 : Addr) = st + BitVec.ofNat 64 128 from rfl, Mem.readW_writeW_self64, leftW_eq,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show np + BitVec.ofNat 64 0 = np by simp]

/-- What `set_nonce` leaves: the key kept, and the whole keystream of the
nonce. -/
theorem nonceMem_post (m : Mem) (st np : Addr) :
    keyAt (nonceMem m st np) st = keyAt m st ∧
      restAt (nonceMem m st np) st = keystreamOf (keyAt m st) (bytesAt m np 16) := by
  have hw : ∀ k, 0 ≤ k → k < 16 → (nonceMem m st np).readW (st + BitVec.ofNat 64 (4 * k)) 32 =
      (if k < 4 then sigmaW k else if 12 ≤ k then m.readW (np + BitVec.ofNat 64 (4 * (k - 12))) 32
      else m.readW (st + BitVec.ofNat 64 (4 * k)) 32) :=
    fun k _ hk => nonceMem_word _ _ _ hk
  have hm : ∀ k, 0 ≤ k → k < 16 → m.readW (st + BitVec.ofNat 64 (4 * k)) 32 =
      m.readW (st + BitVec.ofNat 64 (4 * k)) 32 := fun _ _ _ => rfl
  have hn : ∀ k, 0 ≤ k → k < 4 → m.readW (np + BitVec.ofNat 64 (4 * k)) 32 =
      m.readW (np + BitVec.ofNat 64 (4 * k)) 32 := fun _ _ _ => rfl
  refine stream_of_parts (by simp [keyAt, length_bytesAt]) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) ?_
  · rw [byte_of_words32 hw (Nat.zero_le _) (by omega), ite_pos (by omega), sigma_bytes i hi]
  · rw [byte_of_words32 hw (Nat.zero_le _) (by omega), keyAt,
      show (st + 16 : Addr) = st + BitVec.ofNat 64 16 from rfl, bytesAt_getD _ _ hi, Offset.add_add,
      byte_of_words32 hm (Nat.zero_le _) (by omega), ite_neg (by omega), ite_neg (by omega)]
  · rw [byte_of_words32 hw (Nat.zero_le _) (by omega), bytesAt_getD _ _ hi,
      byte_of_words32 hn (i := i) (Nat.zero_le _) (by omega), ite_neg (by omega), ite_pos (by omega),
      show (48 + i) / 4 - 12 = i / 4 by omega, show (48 + i) % 4 = i % 4 by omega]
  · rw [nonceMem_left, wordLE_bytesAt _ _ (by decide)]

theorem contains_st (st : Addr) {d n : Nat} (hd : d + n ≤ 768) :
    (⟨st, 768⟩ : Region).Contains (st + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ hd (by omega)

theorem nonceMem_frame (m : Mem) (st np : Addr) : Frame [⟨st, 768⟩] m (nonceMem m st np) := by
  simp only [nonceMem]
  have w : ∀ {m' : Mem} (_ : Frame [⟨st, 768⟩] m m') (d : Nat) {k : Nat} (v : BitVec k), d + k / 8 ≤ 768 →
      Frame [⟨st, 768⟩] m (m'.writeW (st + BitVec.ofNat 64 d) v) :=
    fun {_} hf d {_} v h => hf.writeW (List.mem_singleton_self _) v (contains_st st h)
  exact w (w (w (w (w (w (w (w (w (Frame.refl _ _) 48 _ (by decide)) 52 _ (by decide)) 56 _ (by decide)) 60 _
    (by decide)) 0 _ (by decide)) 4 _ (by decide)) 8 _ (by decide)) 12 _ (by decide)) 128 _ (by decide)

theorem setNonce_ok (s : State) (hs : Proof.ChaCha20.setNoncePPC64LE.pre s) :
    ∃ t s', Exec isa setNonce s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.setNoncePPC64LE.post s s' := by
  obtain ⟨hrd, hwr, _⟩ := hs
  have hp : NPre s (s.gpr .r3) (s.gpr .r4) :=
    ⟨rfl, rfl, fun d n hd => ⟨_, by rw [hwr]; exact List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩,
      fun d n hd => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
        Offset.contains_base _ hd (by omega)⟩⟩
  obtain ⟨t, s', he, hm, -, -⟩ := setNonce_exec hp
  refine ⟨t, s', he, ⟨keeps (by rw [← Code.allInstrs_eq]; decide +kernel) he, Exec.sp he,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, ?_⟩
  simp only [Proof.ChaCha20.setNoncePPC64LE]; rw [hm]; exact nonceMem_post _ _ _

theorem setNonce_ct :
    ConstantTime isa Proof.ChaCha20.setNoncePPC64LE.pre Proof.ChaCha20.setNoncePPC64LE.pub setNonce := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h1
  · exact h2

/-- A state satisfying the precondition of `set_nonce`. -/
def setNonceSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 16⟩]
  wr := [⟨0x1000, 768⟩]

theorem setNonce_verified :
    Verified PPC64LE.target setNonce (Spec.ChaCha20.setNonceContract PPC64LE.abi) :=
  Verified.of_correct setNonce_ok setNonce_ct (by
    sig_implies [Spec.ChaCha20.setNonceContract, Spec.ChaCha20.setNonceSig,
      Proof.ChaCha20.setNoncePPC64LE, PPC64LE.abi, PPC64LE.argRegs] [setNonceSat] using setNonceSat)

/-! ## `init` -/

/-- The memory after the key is copied. -/
def keyMem (m : Mem) (st kp : Addr) : Mem :=
  (((m.writeW (st + BitVec.ofNat 64 16) (m.readW (kp + BitVec.ofNat 64 0) 64)).writeW (st + BitVec.ofNat 64 24)
    (m.readW (kp + BitVec.ofNat 64 8) 64)).writeW (st + BitVec.ofNat 64 32)
    (m.readW (kp + BitVec.ofNat 64 16) 64)).writeW (st + BitVec.ofNat 64 40) (m.readW (kp + BitVec.ofNat 64 24) 64)

set_option simprocs false in
theorem key_exec {s : State} {st kp : Addr} (hr3 : s.gpr .r3 = st) (hr4 : s.gpr .r4 = kp)
    (hw : ∀ d, d + 8 ≤ 768 → InRegions s.wr (st + BitVec.ofNat 64 d) 8)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 d) 8) :
    WP isa (.block keyInstrs) s fun s' => s'.mem = keyMem s.mem st kp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .r3 = st ∧ s'.gpr .r4 = s.gpr .r5 := by
  have o16 := hw 16 (by decide); have o24 := hw 24 (by decide)
  have o32 := hw 32 (by decide); have o40 := hw 40 (by decide)
  have i0 := hr 0 (by decide); have i8 := hr 8 (by decide)
  have i16 := hr 16 (by decide); have i24 := hr 24 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [keyInstrs, Impl.ChaCha20.PPC64LE.Xor.mov, runBlock_cons,
    runStep_some, runBlock_nil, exec, addr, Size.bytes, State.load, State.store, State.write,
    BitVec.setWidth_eq, Option.bind_some, Option.map_some, hr3, hr4, o16, o24, o32, o40, i0, i8,
    i16, i24, ite_true, ite_false, Option.some.injEq, exists_eq_left', write64_eq, read64_eq]
  exact ⟨by simp [keyMem], trivial, trivial, by simp, by simp⟩

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

theorem init_ok (s : State) (hs : Proof.ChaCha20.initPPC64LE.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.initPPC64LE.post s s' := by
  obtain ⟨hrd, hwr, hdk, hdn⟩ := hs
  have hw : ∀ d n, d + n ≤ 768 → InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 d) n :=
    fun d n hd => ⟨_, by rw [hwr]; exact List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩
  have h₁ := key_exec (s := s) rfl rfl (fun d hd => hw d 8 hd) fun d hd => ⟨_, by rw [hrd]; simp,
    Offset.contains_base (s.gpr .r4) (k := 32) hd (by omega)⟩
  obtain ⟨t, s', he, hm⟩ : WP isa init s fun s' =>
      s'.mem = nonceMem (keyMem s.mem (s.gpr .r3) (s.gpr .r4)) (s.gpr .r3) (s.gpr .r5) := by
    rw [init_eq]
    refine WP.block_append (WP.mono h₁ fun s₁ ⟨m₁, rd₁, wr₁, r3₁, r4₁⟩ => ?_)
    have hp : NPre s₁ (s.gpr .r3) (s.gpr .r5) :=
      ⟨r3₁, r4₁, fun d n hd => by rw [wr₁]; exact hw d n hd, fun d n hd => ⟨⟨s.gpr .r5, 16⟩,
        by rw [rd₁, wr₁, hrd]; simp, Offset.contains_base _ hd (by omega)⟩⟩
    exact WP.mono (setNonce_exec hp) fun s' ⟨m', _, _⟩ => by rw [m', m₁]
  refine ⟨t, s', he, ⟨keeps (by rw [← Code.allInstrs_eq]; decide +kernel) he, Exec.sp he,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, ?_⟩
  obtain ⟨hk, hr⟩ := nonceMem_post (keyMem s.mem (s.gpr .r3) (s.gpr .r4)) (s.gpr .r3) (s.gpr .r5)
  have hn : bytesAt (keyMem s.mem (s.gpr .r3) (s.gpr .r4)) (s.gpr .r5) 16 = bytesAt s.mem (s.gpr .r5) 16 :=
    List.map_congr_left fun i hi => (keyMem_frame _ _ _).bytes (R := ⟨s.gpr .r5, 16⟩)
      (by simpa using hdn.symm) (show 16 ≤ 2 ^ 64 by decide) (List.mem_range.mp hi)
  simp only [Proof.ChaCha20.initPPC64LE]
  rw [hm, hk, hr, keyMem_key, hn]
  exact ⟨rfl, rfl⟩

theorem init_ct : ConstantTime isa Proof.ChaCha20.initPPC64LE.pre Proof.ChaCha20.initPPC64LE.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

/-- A state satisfying the precondition of `init`. -/
def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x1000, 768⟩]

theorem init_verified : Verified PPC64LE.target init (Spec.ChaCha20.initContract PPC64LE.abi) :=
  Verified.of_correct init_ok init_ct (by
    sig_implies [Spec.ChaCha20.initContract, Spec.ChaCha20.initSig, Proof.ChaCha20.initPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [initSat] using initSat)

end VG.Proof.ChaCha20.PPC64LE.Stream
