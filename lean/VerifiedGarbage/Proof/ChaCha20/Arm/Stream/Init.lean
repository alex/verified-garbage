import VerifiedGarbage.Proof.ChaCha20.StreamBytes
import VerifiedGarbage.Proof.ChaCha20.Arm.Block
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.ChaCha20.Arm.Stream

/-!
# Streaming ChaCha20 on ARMv7: `init` and `set_nonce`

Untrusted: everything here is checked by Lean. `set_nonce` loads the nonce
first and then stores everything (`setNonce_exec`; `nonceMem` is the memory
it leaves); `init` first copies the key a word at a time (`copy_ok`, which
`apply` uses too for the copy of the state).
-/

namespace VG.Proof.ChaCha20

open VG.Arm
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt)

/-- ARMv7 contract for `vg_chacha20_set_nonce(state = r0, nonce = r1)`. -/
def setNonceArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 768⟩
    let nonce : Region := ⟨State.addr (s.gpr .r1), 16⟩
    s.rd = [nonce] ∧ s.wr = [state] ∧ state.Disjoint nonce ∧
      (s.gpr .r0).toNat + 768 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 16 ≤ 2 ^ 32
  post s s' :=
    keyAt s'.mem (State.addr (s.gpr .r0)) = keyAt s.mem (State.addr (s.gpr .r0)) ∧
      restAt s'.mem (State.addr (s.gpr .r0)) =
        keystreamOf (keyAt s.mem (State.addr (s.gpr .r0))) (bytesAt s.mem (State.addr (s.gpr .r1)) 16)
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

/-- ARMv7 contract for `vg_chacha20_init(state = r0, key = r1, nonce = r2)`. -/
def initArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 768⟩
    let key : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let nonce : Region := ⟨State.addr (s.gpr .r2), 16⟩
    s.rd = [key, nonce] ∧ s.wr = [state] ∧ state.Disjoint key ∧ state.Disjoint nonce ∧
      (s.gpr .r0).toNat + 768 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32
  post s s' :=
    keyAt s'.mem (State.addr (s.gpr .r0)) = bytesAt s.mem (State.addr (s.gpr .r1)) 32 ∧
      restAt s'.mem (State.addr (s.gpr .r0)) =
        keystreamOf (bytesAt s.mem (State.addr (s.gpr .r1)) 32) (bytesAt s.mem (State.addr (s.gpr .r2)) 16)
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.Arm.Stream

open VG VG.Arm VG.Impl.ChaCha20.Arm.Stream
open VG.Proof.MdStream.Arm (addr_off addr_toNat)
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt wordLE)

/-- The number of bytes left for the initial block counter `c`. -/
abbrev V (c : BitVec 32) : Nat := 64 * (2 ^ 32 - c.toNat)

theorem V_lt (c : BitVec 32) : V c < 2 ^ 39 := by have := c.isLt; simp only [V]; omega

/-- What `set_nonce` needs of the state it runs from. -/
structure NPre (s : State) (ST NP : BitVec 32) : Prop where
  r0 : s.gpr .r0 = ST
  r1 : s.gpr .r1 = NP
  st_fit : ST.toNat + 768 ≤ 2 ^ 32
  n_fit : NP.toNat + 16 ≤ 2 ^ 32
  w : ∀ d n, d + n ≤ 768 → InRegions s.wr (State.addr ST + BitVec.ofNat 64 d) n
  r : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (State.addr NP + BitVec.ofNat 64 d) n

/-- The low and high words of the number of bytes left, as the code computes
them from the initial block counter `c`. -/
abbrev lo (c : BitVec 32) : BitVec 32 := (0 - c) <<< 6
abbrev hi (c : BitVec 32) : BitVec 32 :=
  (0 - c) >>> 26 |||
    ((0 : BitVec 32) + 0 + if decide (c.toNat ≤ BitVec.toNat (0 : BitVec 32)) = true then (1 : BitVec 32) else 0) <<< 6

theorem lo_eq (c : BitVec 32) : lo c = BitVec.ofNat 32 (V c) := by
  have hc := c.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    show (0 : BitVec 32).toNat = 0 from rfl]
  simp only [V]
  omega

theorem hi_eq (c : BitVec 32) : hi c = BitVec.ofNat 32 (V c / 2 ^ 32) := by
  have hc := c.isLt
  by_cases h0 : c = 0
  · subst h0; decide
  · have hpos : 0 < c.toNat := by
      rcases Nat.eq_zero_or_pos c.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) h0
      · exact h
    simp only [hi, show (0 : BitVec 32).toNat = 0 from rfl, show ¬ c.toNat ≤ 0 by omega, decide_false,
      Bool.false_eq_true, ite_false]
    rw [show ((0 : BitVec 32) + 0 + 0) <<< 6 = 0 by decide, show ∀ x : BitVec 32, x ||| 0 = x from
      fun x => by ext i hi; simp]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      show (0 : BitVec 32).toNat = 0 from rfl]
    simp only [V]
    omega

theorem k0_eq : (((24944 : BitVec 16) ++ BitVec.extractLsb' 0 16 (BitVec.setWidth 32 (30821 : BitVec 16))) : BitVec 32) =
    0x61707865 := by decide
theorem k1_eq : (((13088 : BitVec 16) ++ BitVec.extractLsb' 0 16 (BitVec.setWidth 32 (25710 : BitVec 16))) : BitVec 32) =
    0x3320646e := by decide
theorem k2_eq : (((31074 : BitVec 16) ++ BitVec.extractLsb' 0 16 (BitVec.setWidth 32 (11570 : BitVec 16))) : BitVec 32) =
    0x79622d32 := by decide
theorem k3_eq : (((27424 : BitVec 16) ++ BitVec.extractLsb' 0 16 (BitVec.setWidth 32 (25972 : BitVec 16))) : BitVec 32) =
    0x6b206574 := by decide

/-- The memory `set_nonce` leaves, from `m`, for the state at `st`, the
nonce words `w₀`…`w₃` and the number of bytes left `l`, `h`. -/
def nonceMem (m : Mem) (st : Addr) (w₀ w₁ w₂ w₃ l h : BitVec 32) : Mem :=
  (((((((((m.writeW (st + BitVec.ofNat 64 48) w₀).writeW (st + BitVec.ofNat 64 52) w₁).writeW
    (st + BitVec.ofNat 64 56) w₂).writeW (st + BitVec.ofNat 64 60) w₃).writeW (st + BitVec.ofNat 64 128) l).writeW
    (st + BitVec.ofNat 64 132) h).writeW (st + BitVec.ofNat 64 0) (0x61707865 : BitVec 32)).writeW
    (st + BitVec.ofNat 64 4) (0x3320646e : BitVec 32)).writeW (st + BitVec.ofNat 64 8) (0x79622d32 : BitVec 32)).writeW
    (st + BitVec.ofNat 64 12) (0x6b206574 : BitVec 32)

/-- What `set_nonce` leaves, from the nonce at `np`. -/
abbrev setNonceMem (m : Mem) (st np : Addr) : Mem :=
  nonceMem m st (m.readW (np + BitVec.ofNat 64 0) 32) (m.readW (np + BitVec.ofNat 64 4) 32)
    (m.readW (np + BitVec.ofNat 64 8) 32) (m.readW (np + BitVec.ofNat 64 12) 32)
    (lo (m.readW (np + BitVec.ofNat 64 0) 32)) (hi (m.readW (np + BitVec.ofNat 64 0) 32))

set_option simprocs false in
theorem setNonce_exec {s : State} {ST NP : BitVec 32} (hp : NPre s ST NP) :
    WP isa setNonce s fun s' => s'.mem = setNonceMem s.mem (State.addr ST) (State.addr NP) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) := by
  have eS : ∀ d, d < 768 → State.addr (ST + BitVec.ofNat 32 d) = State.addr ST + BitVec.ofNat 64 d :=
    fun d hd => addr_off (by have := hp.st_fit; omega)
  have eN : ∀ d, d < 16 → State.addr (NP + BitVec.ofNat 32 d) = State.addr NP + BitVec.ofNat 64 d :=
    fun d hd => addr_off (by have := hp.n_fit; omega)
  have n0 := eN 0 (by decide); have n4 := eN 4 (by decide); have n8 := eN 8 (by decide)
  have n12 := eN 12 (by decide)
  have i0 := hp.r 0 4 (by decide); have i4 := hp.r 4 4 (by decide); have i8 := hp.r 8 4 (by decide)
  have i12 := hp.r 12 4 (by decide)
  have s0 := eS 0 (by decide); have s4 := eS 4 (by decide); have s8 := eS 8 (by decide)
  have s12 := eS 12 (by decide); have s48 := eS 48 (by decide); have s52 := eS 52 (by decide)
  have s56 := eS 56 (by decide); have s60 := eS 60 (by decide); have s128 := eS 128 (by decide)
  have s132 := eS 132 (by decide)
  have o0 := hp.w 0 4 (by decide); have o4 := hp.w 4 4 (by decide); have o8 := hp.w 8 4 (by decide)
  have o12 := hp.w 12 4 (by decide); have o48 := hp.w 48 4 (by decide); have o52 := hp.w 52 4 (by decide)
  have o56 := hp.w 56 4 (by decide); have o60 := hp.w 60 4 (by decide); have o128 := hp.w 128 4 (by decide)
  have o132 := hp.w 132 4 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [setNonceInstrs, runBlock_cons, runStep_some, runBlock_nil,
    exec, Op2.eval, State.load32, State.store32, State.setReg, subFlags, hp.r0, hp.r1, n0, n4, n8, n12, i0,
    i4, i8, i12, s0, s4, s8, s12, s48, s52, s56, s60, s128, s132, o0, o4, o8, o12, o48, o52, o56, o60, o128,
    o132, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left', k0_eq, k1_eq, k2_eq, k3_eq]
  exact ⟨rfl, trivial, trivial, trivial, fun r h₁ h₂ h₃ h₄ => by simp [h₁, h₂, h₃, h₄]⟩

/-! ## What `set_nonce` leaves -/

theorem k_bytes : ∀ j < 16, ([(0x61707865 : BitVec 32), 0x3320646e, 0x79622d32, 0x6b206574].getD (j / 4) 0).extractLsb'
    (8 * (j % 4)) 8 = sigma.getD j 0 := by
  decide

set_option simprocs false in
/-- The words `set_nonce` stores in the 16-word state. -/
theorem nonceMem_word (m : Mem) (st : Addr) (w₀ w₁ w₂ w₃ l h : BitVec 32) {k : Nat} (hk : k < 16)
    (hk' : k < 4 ∨ 12 ≤ k) :
    (nonceMem m st w₀ w₁ w₂ w₃ l h).readW (st + BitVec.ofNat 64 (4 * k)) 32 =
      [(0x61707865 : BitVec 32), 0x3320646e, 0x79622d32, 0x6b206574, 0, 0, 0, 0, 0, 0, 0, 0, w₀, w₁, w₂, w₃].getD k 0 := by
  simp only [nonceMem]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  all_goals simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_ofNat,
    List.getD_cons_zero, List.getD_cons_succ]

theorem nonceMem_post (m : Mem) (st np : Addr) :
    keyAt (setNonceMem m st np) st = keyAt m st ∧
      restAt (setNonceMem m st np) st = keystreamOf (keyAt m st) (bytesAt m np 16) := by
  have hv := V_lt (m.readW (np + BitVec.ofNat 64 0) 32)
  have hw := fun k (h₁ : 0 ≤ k) (h₂ : k < 4) => nonceMem_word m st (m.readW (np + BitVec.ofNat 64 0) 32)
    (m.readW (np + BitVec.ofNat 64 4) 32) (m.readW (np + BitVec.ofNat 64 8) 32)
    (m.readW (np + BitVec.ofNat 64 12) 32) (lo (m.readW (np + BitVec.ofNat 64 0) 32))
    (hi (m.readW (np + BitVec.ofNat 64 0) 32)) (k := k) (by omega) (.inl h₂)
  have hn := fun k (h₁ : 12 ≤ k) (h₂ : k < 16) => nonceMem_word m st (m.readW (np + BitVec.ofNat 64 0) 32)
    (m.readW (np + BitVec.ofNat 64 4) 32) (m.readW (np + BitVec.ofNat 64 8) 32)
    (m.readW (np + BitVec.ofNat 64 12) 32) (lo (m.readW (np + BitVec.ofNat 64 0) 32))
    (hi (m.readW (np + BitVec.ofNat 64 0) 32)) (k := k) h₂ (.inr h₁)
  refine stream_of_parts (by simp [keyAt, length_bytesAt]) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) ?_
  · dsimp only [setNonceMem]
    rw [byte_of_words32 hw (Nat.zero_le _) (by omega)]
    rw [← k_bytes i hi]
    have : i / 4 < 4 := by omega
    obtain h | h | h | h : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 := by omega
    all_goals simp only [h, List.getD_cons_zero, List.getD_cons_succ]
  · simp only [setNonceMem, nonceMem]
    rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      keyAt, show (st + 16 : Addr) = st + BitVec.ofNat 64 16 from rfl, bytesAt_getD _ _ hi, Offset.add_add]
  · dsimp only [setNonceMem]
    rw [byte_of_words32 hn (by omega) (by omega), bytesAt_getD _ _ hi]
    have e : ∀ j < 4, ([(0x61707865 : BitVec 32), 0x3320646e, 0x79622d32, 0x6b206574, 0, 0, 0, 0, 0, 0, 0, 0,
        m.readW (np + BitVec.ofNat 64 0) 32, m.readW (np + BitVec.ofNat 64 4) 32, m.readW (np + BitVec.ofNat 64 8) 32,
        m.readW (np + BitVec.ofNat 64 12) 32].getD (12 + j) 0) = m.readW (np + BitVec.ofNat 64 (4 * j)) 32 := by
      intro j hj
      obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      all_goals rfl
    rw [show (48 + i) / 4 = 12 + i / 4 by omega, e _ (by omega), ← Mem.readW_byte _ _ (by omega), Offset.add_add,
      show (48 + i) % 4 = i % 4 by omega, show 4 * (i / 4) + i % 4 = i by omega]
  · simp only [leftAt, setNonceMem, nonceMem]
    rw [show (st + 128 : Addr) = st + BitVec.ofNat 64 128 from rfl,
      readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
      readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
      readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
      readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by omega),
      lo_eq, hi_eq, show (132 : Nat) = 128 + 4 from rfl, readW64_halves _ _ _ (by decide), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), wordLE_bytesAt _ _ (by decide), show np + BitVec.ofNat 64 0 = np by simp]

/-- The stores of `set_nonce` write only the state. -/
theorem nonceMem_frame (m : Mem) (st : Addr) (w₀ w₁ w₂ w₃ l h : BitVec 32) :
    Frame [⟨st, 768⟩] m (nonceMem m st w₀ w₁ w₂ w₃ l h) := by
  have w : ∀ {m' : Mem} (_ : Frame [⟨st, 768⟩] m m') (d : Nat), d + 4 ≤ 768 → ∀ v : BitVec 32,
      Frame [⟨st, 768⟩] m (m'.writeW (st + BitVec.ofNat 64 d) v) :=
    fun hf d hd v => hf.writeW (List.mem_singleton_self _) v (Proof.ChaCha20.Arm.contains_off hd (by omega))
  exact w (w (w (w (w (w (w (w (w (w (Frame.refl _ _) 48 (by decide) _) 52 (by decide) _) 56 (by decide) _)
    60 (by decide) _) 128 (by decide) _) 132 (by decide) _) 0 (by decide) _) 4 (by decide) _) 8 (by decide) _)
    12 (by decide) _

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem setNonce_ok (s : State) (hs : Proof.ChaCha20.setNonceArm.pre s) :
    ∃ t s', Exec isa setNonce s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.setNonceArm.post s s' := by
  obtain ⟨hrd, hwr, _, hst, hn⟩ := hs
  have hp : NPre s (s.gpr .r0) (s.gpr .r1) :=
    ⟨rfl, rfl, hst, hn, fun d n hd => ⟨_, by rw [hwr]; exact List.mem_singleton_self _,
        Proof.ChaCha20.Arm.contains_off hd (by omega)⟩,
      fun d n hd => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
        Proof.ChaCha20.Arm.contains_off hd (by omega)⟩⟩
  obtain ⟨t, s', he, hm, -, -, hsp, hg⟩ := setNonce_exec hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, hsp⟩, ?_⟩
  · have := preserved_ne hr
    exact hg r this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2
  · simp only [Proof.ChaCha20.setNonceArm]; rw [hm]; exact nonceMem_post _ _ _

theorem setNonce_ct : ConstantTime isa Proof.ChaCha20.setNonceArm.pre Proof.ChaCha20.setNonceArm.pub setNonce := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

/-- A state satisfying the precondition of `set_nonce`. -/
def setNonceSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 16⟩]
  wr := [⟨0x1000, 768⟩]

theorem setNonce_verified : Verified Arm.target setNonce (Spec.ChaCha20.setNonceContract Arm.abi) :=
  Verified.of_correct setNonce_ok setNonce_ct (by
    sig_implies [Spec.ChaCha20.setNonceContract, Spec.ChaCha20.setNonceSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Proof.ChaCha20.setNonceArm, State.addr]
      [setNonceSat] using setNonceSat)

/-! ## Copying words -/

/-- After `k` of the `n` words of `copyWords t sr dr so dof n` are copied from
`S + so` to `D + dof`. -/
structure CInv (s₀ : State) (t : Reg) (S D : BitVec 32) (so dof n k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ t → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  copied : ∀ i < 4 * k, s.mem (State.addr D + BitVec.ofNat 64 (dof + i)) =
    s₀.mem (State.addr S + BitVec.ofNat 64 (so + i))
  frame : Frame [⟨State.addr D + BitVec.ofNat 64 dof, 4 * n⟩] s₀.mem s.mem

/-- What `copyWords` needs. -/
structure CPre (s₀ : State) (t sr dr : Reg) (S D : BitVec 32) (so dof n : Nat) : Prop where
  hsr : s₀.gpr sr = S
  hdr : s₀.gpr dr = D
  tsr : sr ≠ t
  tdr : dr ≠ t
  s_fit : S.toNat + so + 4 * n ≤ 2 ^ 32
  d_fit : D.toNat + dof + 4 * n ≤ 2 ^ 32
  so_lt : so + 4 * n ≤ 4096
  dof_lt : dof + 4 * n ≤ 4096
  r : ∀ i n', i + n' ≤ 4 * n → InRegions (s₀.rd ++ s₀.wr) (State.addr S + BitVec.ofNat 64 (so + i)) n'
  w : ∀ i n', i + n' ≤ 4 * n → InRegions s₀.wr (State.addr D + BitVec.ofNat 64 (dof + i)) n'
  disj : (⟨State.addr S + BitVec.ofNat 64 so, 4 * n⟩ : Region).Disjoint ⟨State.addr D + BitVec.ofNat 64 dof, 4 * n⟩

open VG.Proof.MdStream.Arm (wp_ldr wp_str) in
theorem copy_step {s₀ : State} {t sr dr : Reg} {S D : BitVec 32} {so dof n : Nat}
    (hp : CPre s₀ t sr dr S D so dof n) {k : Nat} (hk : k < n) {s : State}
    (h : CInv s₀ t S D so dof n k s) :
    WP isa (.block [.ldr t sr (so + 4 * k), .str t dr (dof + 4 * k)]) s (CInv s₀ t S D so dof n (k + 1)) := by
  have hsf := hp.s_fit
  have hdf := hp.d_fit
  have ea₁ : State.addr (s.gpr sr + BitVec.ofNat 32 (so + 4 * k)) = State.addr S + BitVec.ofNat 64 (so + 4 * k) := by
    rw [h.gpr sr hp.tsr, hp.hsr]; exact addr_off (by omega)
  have i₁ : InRegions (s.rd ++ s.wr) (State.addr S + BitVec.ofNat 64 (so + 4 * k)) 4 := by
    rw [h.rd, h.wr]; exact hp.r (4 * k) 4 (by omega)
  refine wp_ldr (by have := hp.so_lt; omega) ea₁ i₁ fun s₁ u₁ => ?_
  have ea₂ : State.addr (s₁.gpr dr + BitVec.ofNat 32 (dof + 4 * k)) = State.addr D + BitVec.ofNat 64 (dof + 4 * k) := by
    rw [u₁.other dr hp.tdr, h.gpr dr hp.tdr, hp.hdr]; exact addr_off (by omega)
  have o₂ : InRegions s₁.wr (State.addr D + BitVec.ofNat 64 (dof + 4 * k)) 4 := by
    rw [u₁.wr, h.wr]; exact hp.w (4 * k) 4 (by omega)
  refine wp_str (by have := hp.dof_lt; omega) ea₂ o₂ fun s₂ g₂ => WP.block_nil ?_
  have hv : s.mem.readW (State.addr S + BitVec.ofNat 64 (so + 4 * k)) 32 =
      s₀.mem.readW (State.addr S + BitVec.ofNat 64 (so + 4 * k)) 32 :=
    h.frame.readW (r := ⟨State.addr S + BitVec.ofNat 64 so, 4 * n⟩) (Offset.contains _ (by omega) (by omega) (by omega))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) (by decide)
  have hm : s₂.mem = s.mem.writeW (State.addr D + BitVec.ofNat 64 (dof + 4 * k))
      (s₀.mem.readW (State.addr S + BitVec.ofNat 64 (so + 4 * k)) 32) := by
    rw [g₂.mem, u₁.gpr, u₁.mem, hv]
  refine ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, h.gpr r hr], by rw [g₂.rd, u₁.rd, h.rd],
    by rw [g₂.wr, u₁.wr, h.wr], by rw [g₂.sp, u₁.sp, h.sp], fun i hi => ?_, ?_⟩
  · rw [hm]
    by_cases hik : i < 4 * k
    · rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), h.copied i hik]
    · rw [show dof + i = (dof + 4 * k) + (i - 4 * k) by omega, ← Offset.add_add _ (dof + 4 * k) (i - 4 * k),
        byte_writeW_self _ _ _ (by omega) (by omega), ← Mem.readW_byte _ _ (by omega), Offset.add_add,
        show so + 4 * k + (i - 4 * k) = so + i by omega]
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

theorem copy_ok {s₀ : State} {t sr dr : Reg} {S D : BitVec 32} {so dof n : Nat}
    (hp : CPre s₀ t sr dr S D so dof n) : WP isa (.block (copyWords t sr dr so dof n)) s₀ (CInv s₀ t S D so dof n n) :=
  wp_range_flatMap (M := isa) (CInv s₀ t S D so dof n) (fun k s hk h => copy_step hp hk h) n (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, fun i hi => absurd hi (by omega), Frame.refl _ _⟩

/-! ## `init` -/

theorem init_eq : init = .block ((copyWords .r3 .r1 .r0 0 16 8 ++ [.mov .r1 (.reg .r2)]) ++ setNonceInstrs) := rfl

theorem init_ok (s : State) (hs : Proof.ChaCha20.initArm.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.initArm.post s s' := by
  obtain ⟨hrd, hwr, hdk, hdn, hst, hk, hn⟩ := hs
  have z : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => by simp
  have hc : CPre s .r3 .r1 .r0 (s.gpr .r1) (s.gpr .r0) 0 16 8 :=
    ⟨rfl, rfl, by decide, by decide, by omega, by omega, by decide, by decide,
      fun i n' h => ⟨⟨State.addr (s.gpr .r1), 32⟩, by rw [hrd]; simp, by
        rw [Nat.zero_add]; exact Proof.ChaCha20.Arm.contains_off (base := State.addr (s.gpr .r1)) (len := 32) h
          (by omega)⟩,
      fun i n' h => ⟨_, by rw [hwr]; exact List.mem_singleton_self _,
        Proof.ChaCha20.Arm.contains_off (by omega) (by omega)⟩,
      by rw [z]; exact (hdk.sub_left (Offset.sub_base _ (by omega))).symm⟩
  rw [init_eq]
  obtain ⟨t, s', he, hm, hg, hsp⟩ : WP isa (.block ((copyWords .r3 .r1 .r0 0 16 8 ++ [.mov .r1 (.reg .r2)]) ++
      setNonceInstrs)) s fun s' =>
      (∃ m₁ : Mem, (∀ i < 32, m₁ (State.addr (s.gpr .r0) + BitVec.ofNat 64 (16 + i)) =
          s.mem (State.addr (s.gpr .r1) + BitVec.ofNat 64 (0 + i))) ∧
        Frame [⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 16, 32⟩] s.mem m₁ ∧
        s'.mem = setNonceMem m₁ (State.addr (s.gpr .r0)) (State.addr (s.gpr .r2))) ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (copy_ok hc) fun s₁ h₁ => ?_
    refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₂ u₂ => WP.block_nil ?_
    have hp : NPre s₂ (s.gpr .r0) (s.gpr .r2) :=
      ⟨by rw [u₂.other _ (by decide), h₁.gpr _ (by decide)], by rw [u₂.gpr, h₁.gpr _ (by decide)], hst, hn,
        fun d n hd => ⟨_, by rw [u₂.wr, h₁.wr, hwr]; exact List.mem_singleton_self _,
          Proof.ChaCha20.Arm.contains_off hd (by omega)⟩,
        fun d n hd => ⟨⟨State.addr (s.gpr .r2), 16⟩, by rw [u₂.rd, u₂.wr, h₁.rd, h₁.wr, hrd]; simp,
          Proof.ChaCha20.Arm.contains_off hd (by omega)⟩⟩
    refine WP.mono (setNonce_exec hp) fun s₃ ⟨m₃, _, _, sp₃, g₃⟩ =>
      ⟨⟨s₁.mem, h₁.copied, h₁.frame, by rw [m₃, u₂.mem]⟩, ?_, ?_⟩
    · intro r hr
      have := preserved_ne hr
      rw [g₃ r this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, u₂.other r this.2.1, h₁.gpr r this.2.2.2.1]
    · rw [sp₃, u₂.sp, h₁.sp]
  obtain ⟨m₁, hcp, hfr, hm⟩ := hm
  refine ⟨t, s', he, ⟨hg, hsp⟩, ?_⟩
  have hkey : keyAt m₁ (State.addr (s.gpr .r0)) = bytesAt s.mem (State.addr (s.gpr .r1)) 32 := by
    apply List.ext_getElem
    · simp [keyAt, length_bytesAt]
    · intro i h₁' h₂
      simp only [keyAt, length_bytesAt] at h₁'
      rw [getElem_eq_getD, getElem_eq_getD, keyAt,
        show (State.addr (s.gpr .r0) + 16 : Addr) = State.addr (s.gpr .r0) + BitVec.ofNat 64 16 from rfl,
        bytesAt_getD _ _ h₁', bytesAt_getD _ _ h₁', Offset.add_add]
      have := hcp i (by omega)
      simp only [Nat.zero_add] at this
      rw [this]
  have hnb : bytesAt m₁ (State.addr (s.gpr .r2)) 16 = bytesAt s.mem (State.addr (s.gpr .r2)) 16 := by
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    exact hfr.bytes (R := ⟨State.addr (s.gpr .r2), 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hdn.sub_left (Offset.sub_base _ (by omega))).symm) (by show 16 ≤ 2 ^ 64; decide)
      (List.mem_range.mp hi)
  obtain ⟨hk', hr'⟩ := nonceMem_post m₁ (State.addr (s.gpr .r0)) (State.addr (s.gpr .r2))
  simp only [Proof.ChaCha20.initArm]
  rw [hm, hk', hr', hkey, hnb]
  exact ⟨rfl, rfl⟩

theorem init_ct : ConstantTime isa Proof.ChaCha20.initArm.pre Proof.ChaCha20.initArm.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition of `init`. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x1000, 768⟩]

theorem init_verified : Verified Arm.target init (Spec.ChaCha20.initContract Arm.abi) :=
  Verified.of_correct init_ok init_ct (by
    sig_implies [Spec.ChaCha20.initContract, Spec.ChaCha20.initSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Proof.ChaCha20.initArm, State.addr]
      [initSat] using initSat)

end VG.Proof.ChaCha20.Arm.Stream
