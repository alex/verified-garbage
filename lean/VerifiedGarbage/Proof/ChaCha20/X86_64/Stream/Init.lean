import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.ChaCha20.X86_64.Block
import VerifiedGarbage.Impl.ChaCha20.X86_64.Stream

/-!
# Streaming ChaCha20 on x86-64: `init` and `set_nonce`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20

open VG.X86_64
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt)

/-- x86-64 contract for `vg_chacha20_set_nonce(state = rdi, nonce = rsi)`. -/
def setNonceX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 768⟩
    let nonce : Region := ⟨s.gpr .rsi, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [nonce] ∧ s.wr = [state] ∧ state.Disjoint nonce ∧ ret.Disjoint state
  post s s' :=
    keyAt s'.mem (s.gpr .rdi) = keyAt s.mem (s.gpr .rdi) ∧
      restAt s'.mem (s.gpr .rdi) = keystreamOf (keyAt s.mem (s.gpr .rdi)) (bytesAt s.mem (s.gpr .rsi) 16)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

/-- x86-64 contract for `vg_chacha20_init(state = rdi, key = rsi, nonce = rdx)`. -/
def initX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 768⟩
    let key : Region := ⟨s.gpr .rsi, 32⟩
    let nonce : Region := ⟨s.gpr .rdx, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key, nonce] ∧ s.wr = [state] ∧ state.Disjoint key ∧ state.Disjoint nonce ∧
      ret.Disjoint state
  post s s' :=
    keyAt s'.mem (s.gpr .rdi) = bytesAt s.mem (s.gpr .rsi) 32 ∧
      restAt s'.mem (s.gpr .rdi) = keystreamOf (bytesAt s.mem (s.gpr .rsi) 32) (bytesAt s.mem (s.gpr .rdx) 16)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Stream
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64 (toNat_ofNat_lt contains_off ea_at ofInt_natCast off_sep)
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt wordLE)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

theorem off_eq (p : Addr) (d : Nat) : off p d = p + BitVec.ofNat 64 d := by rw [off, ofInt_natCast]

/-- Reading a 64-bit word after writing a 64-bit word elsewhere. -/
theorem readW64_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (off_sep p hd he (by decide) (by decide) h) (by decide)

/-- Reading after writing a 64-bit word in another region. -/
theorem readW64_writeW_disj (m : Mem) {a b : Addr} (v : BitVec 64) {w : Nat}
    {R R' : Region} (hR : R.Contains a (w / 8)) (hR' : R'.Contains b 8) (hd : R.Disjoint R')
    (hw : w / 8 < 2 ^ 64) :
    (m.writeW b v).readW a w = m.readW a w :=
  Frame.readW (rs := [R']) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ hR') hR
    (by simpa using hd) hw

/-! ## The number of bytes left -/

/-- `64 × (2³² − c)`, computed by doubling six times. -/
theorem left_eq (c : BitVec 32) :
    let v : BitVec 64 := 0x100000000 - c.setWidth 64
    let v := v + v; let v := v + v; let v := v + v; let v := v + v; let v := v + v; let v := v + v
    v = BitVec.ofNat 64 (64 * (2 ^ 32 - c.toNat)) := by
  have hc := c.isLt
  have h0 : (0x100000000 : BitVec 64) - c.setWidth 64 = BitVec.ofNat 64 (2 ^ 32 - c.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [show (0x100000000 : BitVec 64) = BitVec.ofNat 64 (2 ^ 32) from rfl, BitVec.toNat_sub,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  intro v
  simp only [v, h0, BitVec.ofNat_add_ofNat]
  congr 1
  omega

/-! ## `set_nonce` -/

/-- The constants as the code stores them. -/
def c0 : BitVec 64 := 0x3320646e61707865
def c1 : BitVec 64 := 0x6b20657479622d32

theorem c0_bytes : ∀ j < 8, c0.extractLsb' (8 * j) 8 = sigma.getD j 0 := by decide
theorem c1_bytes : ∀ j < 8, c1.extractLsb' (8 * j) 8 = sigma.getD (8 + j) 0 := by decide

/-- The memory `set_nonce` leaves, from `m`, for the state at `st` and the
nonce at `np`. -/
def nonceMem (m : Mem) (st np : Addr) : Mem :=
  let v : BitVec 64 := 0x100000000 - (m.readW (off np 0) 32).setWidth 64
  let v := v + v; let v := v + v; let v := v + v; let v := v + v; let v := v + v; let v := v + v
  ((((m.writeW (off st 48) (m.readW (off np 0) 64)).writeW (off st 56) (m.readW (off np 8) 64)).writeW
    (off st 0) c0).writeW (off st 8) c1).writeW (off st 128) v

/-- What `set_nonce` needs of the state it runs from. -/
structure NPre (s : State) (st np : Addr) : Prop where
  rdi : s.gpr .rdi = st
  rsi : s.gpr .rsi = np
  w_st : ∀ d, d + 8 ≤ 768 → InRegions s.wr (off st d) 8
  r_n : ∀ d, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (off np d) 8

set_option simprocs false in
theorem setNonce_exec {s : State} {st np : Addr} (hp : NPre s st np) :
    WP isa setNonce s fun s' => s'.mem = nonceMem s.mem st np ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) := by
  have o0 := hp.w_st 0 (by decide); have o8 := hp.w_st 8 (by decide)
  have o48 := hp.w_st 48 (by decide); have o56 := hp.w_st 56 (by decide)
  have o128 := hp.w_st 128 (by decide)
  have i0 := hp.r_n 0 (by decide); have i8 := hp.r_n 8 (by decide)
  have i0' : InRegions (s.rd ++ s.wr) (off np 0) 4 := by
    obtain ⟨r, hr, hc⟩ := i0; exact ⟨r, hr, by simp only [Region.Contains] at hc ⊢; omega⟩
  simp only [off] at o0 o8 o48 o56 o128 i0 i8 i0'
  apply WP.of_runBlock
  simp (config := {decide := true}) only [setNonceInstrs, runBlock_cons, runStep_some,
    runBlock_nil, exec, ea_at, readSrc, readSrc32, execAlu, arithFlags, State.store64, State.load64,
    State.load32, State.setReg, State.setReg32, State.setFlags, hp.rdi, hp.rsi, o0, o8, o48, o56, o128,
    i0, i8, i0', ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, trivial, trivial, fun r h₁ h₂ h₃ => ?_⟩
  simp [h₁, h₂, h₃]

/-- The words `set_nonce` leaves. -/
theorem nonceMem_word (m : Mem) (st np : Addr) {k : Nat} (hk : k < 8) :
    (nonceMem m st np).readW (off st (8 * k)) 64 =
      if k = 0 then c0 else if k = 1 then c1 else if k = 6 then m.readW (off np 0) 64
      else if k = 7 then m.readW (off np 8) 64 else m.readW (off st (8 * k)) 64 := by
  simp only [nonceMem]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  all_goals simp (config := {decide := true}) only [Nat.mul_zero, Nat.mul_one, Mem.readW_writeW_self64,
    readW64_writeW_off, ite_true, ite_false]

theorem nonceMem_left (m : Mem) (st np : Addr) :
    leftAt (nonceMem m st np) st = 64 * (2 ^ 32 - (m.readW (off np 0) 32).toNat) := by
  have hc := (m.readW (off np 0) 32).isLt
  simp only [leftAt, nonceMem]
  rw [show (st + 128 : Addr) = off st 128 by rw [off_eq]; rfl, Mem.readW_writeW_self64, left_eq,
    toNat_ofNat_lt (by omega)]


/-- A word of the state from the bytes of memory. -/
theorem word_off (m : Mem) (p : Addr) (k : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = m.readW (off p (8 * k)) 64 := by rw [off_eq]

/-- What `set_nonce` leaves: the key kept, and the whole keystream of the
nonce. -/
theorem nonceMem_post (m : Mem) (st np : Addr) :
    keyAt (nonceMem m st np) st = keyAt m st ∧
      restAt (nonceMem m st np) st = keystreamOf (keyAt m st) (bytesAt m np 16) := by
  have hw : ∀ k, 0 ≤ k → k < 8 → (nonceMem m st np).readW (st + BitVec.ofNat 64 (8 * k)) 64 =
      (if k = 0 then c0 else if k = 1 then c1 else if k = 6 then m.readW (off np 0) 64
      else if k = 7 then m.readW (off np 8) 64 else m.readW (off st (8 * k)) 64) :=
    fun k _ hk => by rw [word_off, nonceMem_word _ _ _ hk]
  have hm : ∀ k, 0 ≤ k → k < 8 → m.readW (st + BitVec.ofNat 64 (8 * k)) 64 = m.readW (off st (8 * k)) 64 :=
    fun k _ _ => word_off _ _ _
  have hn : ∀ k, 0 ≤ k → k < 2 → m.readW (np + BitVec.ofNat 64 (8 * k)) 64 = m.readW (off np (8 * k)) 64 :=
    fun k _ _ => word_off _ _ _
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
  · rw [nonceMem_left, wordLE_bytesAt _ _ (by decide), off_eq]; simp


theorem nonceMem_frame (m : Mem) (st np : Addr) : Frame [⟨st, 768⟩] m (nonceMem m st np) := by
  have c : ∀ d, d + 8 ≤ 768 → (⟨st, 768⟩ : Region).Contains (off st d) (64 / 8) :=
    fun d hd => contains_off hd (by omega)
  simp only [nonceMem]
  exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 48 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 56 (by decide))).writeW (List.mem_singleton_self _) _
    (c 0 (by decide))).writeW (List.mem_singleton_self _) _ (c 8 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 128 (by decide)))

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem setNonce_ok (s : State) (hs : Proof.ChaCha20.setNonceX86_64.pre s) :
    ∃ t s', Exec isa setNonce s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.setNonceX86_64.post s s' := by
  obtain ⟨hrd, hwr, _, hret⟩ := hs
  have hp : NPre s (s.gpr .rdi) (s.gpr .rsi) :=
    ⟨rfl, rfl, fun d hd => ⟨_, by rw [hwr]; exact List.mem_singleton_self _, contains_off hd (by omega)⟩,
      fun d hd => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
        contains_off hd (by omega)⟩⟩
  obtain ⟨t, s', he, hm, -, -, hg⟩ := setNonce_exec hp
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · exact hg r (calleeSaved_ne hr).1 (calleeSaved_ne hr).2.1 (calleeSaved_ne hr).2.2
  · rw [hm]
    exact (nonceMem_frame _ _ _).readW (Region.contains_self _ _) (by simpa using hret) (by decide)
  · simp only [Proof.ChaCha20.setNonceX86_64]; rw [hm]; exact nonceMem_post _ _ _

theorem setNonce_ct : ConstantTime isa Proof.ChaCha20.setNonceX86_64.pre Proof.ChaCha20.setNonceX86_64.pub
    setNonce := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

/-- A state satisfying the precondition of `set_nonce`. -/
def setNonceSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 16⟩]
  wr := [⟨0x1000, 768⟩]

theorem setNonce_verified :
    Verified X86_64.target setNonce (Spec.ChaCha20.setNonceContract X86_64.abi) :=
  Verified.of_correct setNonce_ok setNonce_ct (by
    sig_implies [Spec.ChaCha20.setNonceContract, Spec.ChaCha20.setNonceSig,
      Proof.ChaCha20.setNonceX86_64, X86_64.abi, X86_64.argRegs] [setNonceSat] using setNonceSat)

/-! ## `init` -/

/-- The memory after the key is copied. -/
def keyMem (m : Mem) (st kp : Addr) : Mem :=
  (((m.writeW (off st 16) (m.readW (off kp 0) 64)).writeW (off st 24) (m.readW (off kp 8) 64)).writeW
    (off st 32) (m.readW (off kp 16) 64)).writeW (off st 40) (m.readW (off kp 24) 64)

set_option simprocs false in
theorem key_exec {s : State} {st kp : Addr} (hrdi : s.gpr .rdi = st) (hrsi : s.gpr .rsi = kp)
    (hw : ∀ d, d + 8 ≤ 768 → InRegions s.wr (off st d) 8)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off kp d) 8) :
    WP isa (.block keyInstrs) s fun s' => s'.mem = keyMem s.mem st kp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rdi = st ∧ s'.gpr .rsi = s.gpr .rdx ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) := by
  have o16 := hw 16 (by decide); have o24 := hw 24 (by decide)
  have o32 := hw 32 (by decide); have o40 := hw 40 (by decide)
  have i0 := hr 0 (by decide); have i8 := hr 8 (by decide)
  have i16 := hr 16 (by decide); have i24 := hr 24 (by decide)
  simp only [off] at o16 o24 o32 o40 i0 i8 i16 i24
  apply WP.of_runBlock
  simp (config := {decide := true}) only [keyInstrs, runBlock_cons, runStep_some,
    runBlock_nil, exec, ea_at, readSrc, State.store64, State.load64, State.setReg, hrdi, hrsi,
    o16, o24, o32, o40, i0, i8, i16, i24, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, trivial, trivial, by simp, by simp, fun r h₁ h₂ h₃ h₄ h₅ => ?_⟩
  simp [h₁, h₂, h₃, h₄, h₅]

theorem keyMem_frame (m : Mem) (st kp : Addr) : Frame [⟨st, 768⟩] m (keyMem m st kp) := by
  have c : ∀ d, d + 8 ≤ 768 → (⟨st, 768⟩ : Region).Contains (off st d) (64 / 8) :=
    fun d hd => contains_off hd (by omega)
  simp only [keyMem]
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 16 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 24 (by decide))).writeW (List.mem_singleton_self _) _
    (c 32 (by decide))).writeW (List.mem_singleton_self _) _ (c 40 (by decide))

theorem keyMem_key (m : Mem) (st kp : Addr) : keyAt (keyMem m st kp) st = bytesAt m kp 32 := by
  have hw : ∀ k, 2 ≤ k → k < 6 → (keyMem m st kp).readW (st + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (kp + BitVec.ofNat 64 (8 * (k - 2))) 64 := by
    intro k h₁ h₂
    rw [word_off, word_off]
    simp only [keyMem]
    obtain rfl | rfl | rfl | rfl : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    all_goals simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW64_writeW_off]
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

theorem init_ok (s : State) (hs : Proof.ChaCha20.initX86_64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.initX86_64.post s s' := by
  obtain ⟨hrd, hwr, hdk, hdn, hret⟩ := hs
  have hw : ∀ d, d + 8 ≤ 768 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, by rw [hwr]; exact List.mem_singleton_self _, contains_off hd (by omega)⟩
  have h₁ := key_exec (s := s) rfl rfl hw fun d hd => ⟨_, by rw [hrd]; simp,
    contains_off (base := s.gpr .rsi) (len := 32) hd (by omega)⟩
  rw [init_eq]
  obtain ⟨t, s', he, hm, hpost⟩ : WP isa (.block (keyInstrs ++ setNonceInstrs)) s fun s' =>
      s'.mem = nonceMem (keyMem s.mem (s.gpr .rdi) (s.gpr .rsi)) (s.gpr .rdi) (s.gpr .rdx) ∧
        ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := by
    refine WP.block_append (WP.mono h₁ fun s₁ ⟨m₁, rd₁, wr₁, rdi₁, rsi₁, g₁⟩ => ?_)
    have hp : NPre s₁ (s.gpr .rdi) (s.gpr .rdx) :=
      ⟨rdi₁, rsi₁, fun d hd => by rw [wr₁]; exact hw d hd, fun d hd => ⟨⟨s.gpr .rdx, 16⟩,
        by rw [rd₁, wr₁, hrd]; simp, contains_off hd (by omega)⟩⟩
    refine WP.mono (setNonce_exec hp) fun s' ⟨m', _, _, g'⟩ => ⟨by rw [m', m₁], fun r hr => ?_⟩
    have := calleeSaved_ne hr
    rw [g' r this.1 this.2.1 this.2.2]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact g₁ r this.1 this.2.1 (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he ⟨hpost, ?_⟩, ?_⟩
  · rw [hm]
    exact ((keyMem_frame _ _ _).trans (nonceMem_frame _ _ _)).readW (Region.contains_self _ _)
      (by simpa using hret) (by decide)
  · obtain ⟨hk, hr⟩ := nonceMem_post (keyMem s.mem (s.gpr .rdi) (s.gpr .rsi)) (s.gpr .rdi) (s.gpr .rdx)
    have hn : bytesAt (keyMem s.mem (s.gpr .rdi) (s.gpr .rsi)) (s.gpr .rdx) 16 = bytesAt s.mem (s.gpr .rdx) 16 :=
      List.map_congr_left fun i hi => (keyMem_frame _ _ _).bytes (R := ⟨s.gpr .rdx, 16⟩)
        (by simpa using hdn.symm) (show 16 ≤ 2 ^ 64 by decide) (List.mem_range.mp hi)
    simp only [Proof.ChaCha20.initX86_64]
    rw [hm, hk, hr, keyMem_key, hn]
    exact ⟨rfl, rfl⟩

theorem init_ct : ConstantTime isa Proof.ChaCha20.initX86_64.pre Proof.ChaCha20.initX86_64.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition of `init`. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x1000, 768⟩]

theorem init_verified : Verified X86_64.target init (Spec.ChaCha20.initContract X86_64.abi) :=
  Verified.of_correct init_ok init_ct (by
    sig_implies [Spec.ChaCha20.initContract, Spec.ChaCha20.initSig, Proof.ChaCha20.initX86_64,
      X86_64.abi, X86_64.argRegs] [initSat] using initSat)

end VG.Proof.ChaCha20.X86_64.Stream
