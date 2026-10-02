import VerifiedGarbage.Impl.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.Linear
import VerifiedGarbage.Proof.Aes.X86.Common

/-!
# Encrypting two blocks, bitsliced, on x86 (32-bit)

`encrypt2_ok`: from two blocks in slots `0 … 7` (`InRel`), with the
bitsliced round keys in the scratch buffer (`KeysAt`), `encrypt2` leaves
the two ciphertexts, having written only the first 256 bytes of the scratch
buffer. The layers are composed from their proofs (`Sbox.lean`,
`Linear.lean`); the round loop's invariant is the specification's `foldl`
over the rounds done.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.Spec.Aes (roundKey subBytes shiftRows mixColumns addRoundKey cipher)
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_addm wp_sub wp_subi wp_cmp wp_cmpi wp_test
  wp_bswap wp_ldm wp_xorm wp_stm sub_beq sub_ofNat toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

/-- The offset of bitsliced round key `j` of `R` in the scratch buffer. -/
def keyOff (R j : Nat) : Nat := lastKey - 32 * (R - j)

/-- The bitsliced round keys `0 … R` of the schedule `w`, in the scratch buffer at `B`. -/
def KeysAt (m : Mem) (B : BitVec 32) (R : Nat) (w : List Byte) : Prop :=
  ∀ j ≤ R, KeyRel (fun k => m.readW (addr B (keyOff R j + 4 * k)) 32) (roundKey w j)

/-- What encryption needs: the scratch buffer (2048 bytes at `edi`) is
writable, the round keys are in it, and `rounds` is the second argument. -/
structure EncPre (s₀ : State) (R : Nat) (w : List Byte) : Prop where
  scr : reg32 (s₀.gpr sb) 2048 ∈ s₀.wr
  fit : (s₀.gpr sb).toNat + 2048 ≤ 2 ^ 32
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  argIn : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 8) 4
  argR : s₀.mem.readW (addr (s₀.gpr .esp) 8) 32 = BitVec.ofNat 32 R
  argSep : Region.Disjoint ⟨addr (s₀.gpr .esp) 8, 4⟩ (reg32 (s₀.gpr sb) 256)
  keys : KeysAt s₀.mem (s₀.gpr sb) R w

/-- What stays the same during encryption. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ tmpRegs → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame [reg32 (s₀.gpr sb) 256] s₀.mem s.mem

theorem Ctx.refl (s₀ : State) : Ctx s₀ s₀ := ⟨rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide)

theorem Ctx.esp {s₀ s : State} (hc : Ctx s₀ s) : s.gpr .esp = s₀.gpr .esp :=
  hc.keep _ (by decide) (by decide)

theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hoth : ∀ r, r ∉ tmpRegs → r ≠ kp → s'.gpr r = s.gpr r)
    (hfr : Frame [reg32 (s.gpr sb) 256] s.mem s'.mem) : Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 => (hoth r h1 h2).trans (hc.keep r h1 h2),
    hc.frame.trans (by rw [← hc.base]; exact hfr)⟩

/-- A step that writes only a register of `tmpRegs` or `kp`. -/
theorem Ctx.upd {s₀ s s' : State} {d : Reg} {v : BitVec 32} (hc : Ctx s₀ s) (u : Upd s s' d v)
    (hd : d ∈ tmpRegs ∨ d = kp) : Ctx s₀ s' :=
  hc.step u.rd u.wr (fun r h1 h2 => u.other r (by rintro rfl; rcases hd with h | h <;> simp_all))
    (by rw [u.mem]; exact Frame.refl _ _)

theorem Ctx.linOk {s₀ s : State} {R : Nat} {w : List Byte} (hp : EncPre s₀ R w) (hc : Ctx s₀ s) : Ok linCfg s :=
  Ok.of_off (r := reg32 (s₀.gpr sb) 2048) (r' := reg32 (s₀.gpr sb) 2048) (b := s₀.gpr sb)
    (b' := s₀.gpr sb) (off := 0) (off' := 0) (n := 2048) (n' := 2048)
    (by rw [hc.wr]; exact hp.scr) rfl hp.fit (Nat.le_refl _)
    (by show s.gpr sb = _; rw [hc.base]; simp) (by simp [linCfg])
    (by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hp.scr) rfl hp.fit (Nat.le_refl _)
    (by rw [show linCfg.ext = sb from rfl, hc.base]; simp) (by simp [linCfg])
    (.inr (.inl rfl))

theorem keyOff_le {R j : Nat} (hR : R ≤ 14) : 1024 ≤ keyOff R j ∧ keyOff R j ≤ lastKey := by
  simp only [keyOff, lastKey]; omega

theorem Ctx.arkOk {s₀ s : State} {R : Nat} {w : List Byte} (hp : EncPre s₀ R w) (hc : Ctx s₀ s) {j : Nat} (hR : R ≤ 14)
    (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R j)) : Ok arkCfg s :=
  Ok.of_off (r := reg32 (s₀.gpr sb) 2048) (r' := reg32 (s₀.gpr sb) 2048) (b := s₀.gpr sb)
    (b' := s₀.gpr sb) (off := 0) (off' := keyOff R j) (n := 2048) (n' := 2048)
    (by rw [hc.wr]; exact hp.scr) rfl hp.fit (Nat.le_refl _)
    (by show s.gpr sb = _; rw [hc.base]; simp) (by simp [arkCfg])
    (by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hp.scr) rfl hp.fit (Nat.le_refl _)
    hk (by simp only [arkCfg, keyOff, lastKey]; omega)
    (.inr (.inr (.inr ⟨rfl, .inl (by simp only [arkCfg]; have := keyOff_le (j := j) hR; omega)⟩)))

/-- The round keys are outside what the layers write. -/
theorem EncPre.keysAt {s₀ s : State} {R : Nat} {w : List Byte} (hp : EncPre s₀ R w) (hc : Ctx s₀ s) :
    KeysAt s.mem (s₀.gpr sb) R w := by
  intro j hj
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  refine keyRel_congr (hp.keys j hj) fun k hk => ?_
  have := keyOff_le (j := j) hR
  refine hc.frame.readW (r := ⟨addr (s₀.gpr sb) (keyOff R j + 4 * k), 4⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint _ ⟨(s₀.gpr sb).setWidth 64, 256⟩
  rw [← addr_zero]
  exact part_disj hp.fit (by simp only [lastKey] at this; omega) (by omega)
    (.inr (by simp only [lastKey] at this; omega))

/-- The argument `rounds` is outside what the layers write. -/
theorem EncPre.arg {s₀ s : State} {R : Nat} {w : List Byte} (hp : EncPre s₀ R w) (hc : Ctx s₀ s) :
    s.mem.readW (addr (s.gpr .esp) 8) 32 = BitVec.ofNat 32 R := by
  rw [hc.esp, ← hp.argR]
  exact hc.frame.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.argSep) (by decide)

/-! ## One layer at a time -/

/-- A layer that writes only `tmpRegs` and the first 256 bytes of the
scratch buffer keeps `Ctx`. -/
theorem layer_wp {s₀ s : State} {is : List Instr} {P : State → Prop} {Q : State → Prop}
    (hl : ∃ s', runBlock isa is s = some s' ∧ P s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧ Frame [slotRegion linCfg s] s.mem s'.mem)
    (hc : Ctx s₀ s)
    (hQ : ∀ s', Ctx s₀ s' → P s' → s'.gpr kp = s.gpr kp → Q s') : WP isa (.block is) s Q := by
  obtain ⟨s', hs', hP, hrd, hwr, hoth, hfr⟩ := hl
  exact WP.of_runBlock ⟨s', hs', hQ s' (hc.step hrd hwr (fun r h _ => hoth r h) hfr) hP
    (hoth kp (by decide))⟩

theorem Q_congr {s s' : State} (hb : s'.gpr sb = s.gpr sb) (hm : s'.mem = s.mem) : Q s' = Q s := by
  funext i; simp only [Q, hb, hm]

/-! ## The rounds -/

/-- A middle round of the specification (round `j`). -/
def rnd (w : List Byte) (j : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  addRoundKey (mixColumns (shiftRows (subBytes x))) (roundKey w j)

/-- Rounds `1 … m`, as `cipher` folds them. -/
def midRounds (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  (List.range m).foldl (fun s j => rnd w (j + 1) s) x

theorem midRounds_succ (w : List Byte) (m : Nat) (x : Spec.Aes.State) :
    midRounds w (m + 1) x = rnd w (m + 1) (midRounds w m x) := by
  simp [midRounds, List.range_succ, List.foldl_append]

theorem keyOff_succ {R m : Nat} (h : m + 1 ≤ R) (hR : R ≤ 14) (B : BitVec 32) :
    B + BitVec.ofNat 32 (keyOff R m) + 32 = B + BitVec.ofNat 32 (keyOff R (m + 1)) := by
  rw [BitVec.add_assoc, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
  congr 2; simp only [keyOff, lastKey]; omega

/-- `add kp, 32`. -/
theorem addKp_wp {s₀ s : State} {Q : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp + 32 → Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s → Q s') :
    WP isa (.block [addI kp 32]) s Q :=
  wp_addi fun s' u => WP.block_nil (h s' (hc.upd u (.inr rfl)) u.gpr
    (Q_congr (u.other _ (by decide)) u.mem))

theorem sub_self_add (B : BitVec 32) (a b : Nat) :
    B + BitVec.ofNat 32 a - (B + BitVec.ofNat 32 b) = BitVec.ofNat 32 a - BitVec.ofNat 32 b := by
  bv_omega

/-- `mov eax, edi; add eax, lastKey - 32; cmp kp, eax`. -/
theorem cmpLast_wp {s₀ s : State} {Q : State → Prop} (hc : Ctx s₀ s) {R m : Nat}
    (hm : m + 1 < R) (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R (m + 1)))
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp → Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s →
      s'.zf = some (decide (m + 2 = R)) → Q s') :
    WP isa (.block [movR .eax .edi, addI .eax (BitVec.ofNat 32 (lastKey - 32)),
      .alu .cmp kp (.reg .eax)]) s Q := by
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_cmp fun s₃ u₃ _ hz => WP.block_nil ?_
  have c₂ := (hc.upd u₁ (.inl (by decide))).upd u₂ (.inl (by decide))
  have hk₂ : s₂.gpr kp = s.gpr kp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  refine h s₃ (c₂.step u₃.rd u₃.wr (fun r _ _ => by rw [u₃.gpr]) (by rw [u₃.mem]; exact Frame.refl _ _))
    (by rw [u₃.gpr, hk₂]) ?_ ?_
  · exact Q_congr ((congrFun u₃.gpr sb).trans (c₂.base.trans hc.base.symm))
      (by rw [u₃.mem, u₂.mem, u₁.mem])
  · have hb : s.gpr .edi = s₀.gpr sb := hc.base
    rw [hz, hk₂, hk, u₂.gpr, u₁.gpr, hb, sub_self_add, sub_beq (by simp only [keyOff, lastKey]; omega)
      (by simp only [lastKey]; omega)]
    simp only [keyOff, lastKey]
    exact congrArg some (decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩)

/-- A middle round. -/
theorem round_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hc : Ctx s₀ s)
    (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R m))
    (hm : m + 1 < R) (hbs : BsRel (Q s) T) :
    WP isa (.block roundBody) s fun s' => Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R (m + 1)) ∧
      BsRel (Q s') (fun b => rnd w (m + 1) (T b)) ∧ s'.zf = some (decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  simp only [roundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, keyOff_succ (by omega) hR] at hk₁
  have hbs₁ : BsRel (Q s₁) T := by rw [hq₁]; exact hbs
  refine layer_wp (sbox_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := bs_subBytes h₂ hbs₁
  refine layer_wp (shiftRows_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := bs_shiftRows h₃ hbs₂
  refine layer_wp (mixColumns_ok (hc₃.linOk hp)) hc₃ fun s₄ hc₄ h₄ hk₄ => ?_
  have hbs₄ := bs_mixColumns h₄ hbs₃
  have hk₄' : s₄.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R (m + 1)) := by
    rw [hk₄, hk₃, hk₂, hk₁]
  have hkey : KeyRel (keyWord s₄) (roundKey w (m + 1)) := by
    have := hp.keysAt hc₄ (m + 1) (by omega)
    refine keyRel_congr this fun k _ => ?_
    simp only [keyWord, wordAddr, hk₄', addr_add]
  obtain ⟨s₅, hs₅, h₅, hrd, hwr, hoth, hfr⟩ := addRoundKey_ok (hc₄.arkOk hp hR hk₄')
  have hc₅ : Ctx s₀ s₅ := hc₄.step hrd hwr (fun r h _ => hoth r h)
    (hfr.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by simp [arkCfg])⟩)
  have hbs₅ := bs_addRoundKey h₅ hbs₄ hkey
  refine WP.of_runBlock ⟨s₅, hs₅, ?_⟩
  have hk₅ : s₅.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R (m + 1)) := by
    rw [hoth kp (by decide), hk₄']
  refine cmpLast_wp hc₅ hm hk₅ fun s₆ hc₆ hk₆ hq₆ hz₆ => ⟨hc₆, by rw [hk₆, hk₅], ?_, hz₆⟩
  rw [hq₆]; exact hbs₅

/-- `esi :=` the first round key. -/
theorem keyStart_wp {s₀ s : State} {R : Nat} {w : List Byte} (hp : EncPre s₀ R w) (hc : Ctx s₀ s)
    {Q : State → Prop}
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R 0) →
      Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s → Q s') :
    WP isa (.block keyStart) s Q := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := by
    rw [hc.rd, hc.wr, hc.esp]; exact hp.argIn
  refine wp_ldm (B := s.gpr .esp) rfl hin fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ _ => wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ => wp_add fun s₅ u₅ _ =>
    wp_add fun s₆ u₆ _ => wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_sub fun s₉ u₉ _ =>
    wp_mov fun s₁₀ u₁₀ => WP.block_nil ?_
  have c : Ctx s₀ s₁₀ := ((((((((((hc.upd u₁ (.inr rfl)).upd u₂ (.inr rfl)).upd u₃ (.inr rfl)).upd u₄
    (.inr rfl)).upd u₅ (.inr rfl)).upd u₆ (.inr rfl)).upd u₇ (.inl (by decide))).upd u₈
    (.inl (by decide))).upd u₉ (.inl (by decide))).upd u₁₀ (.inr rfl))
  refine h s₁₀ c ?_ (Q_congr (by rw [c.base, hc.base])
    (by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]))
  have e6 : s₆.gpr .esi = BitVec.ofNat 32 (32 * R) := by
    rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hp.arg hc]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e7 : s₇.gpr .eax = s₀.gpr sb := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ← hc.base]; rfl
  show s₁₀.gpr .esi = _
  rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₈.other .esi (by decide), u₇.other .esi (by decide), e6, e7]
  simp only [keyOff, lastKey, Nat.sub_zero]
  bv_omega

theorem ark_step {s₀ s : State} {R j : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hc : Ctx s₀ s) (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R j))
    (hj : j ≤ R) (hbs : BsRel (Q s) T) {P : State → Prop}
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp →
      BsRel (Q s') (fun b => addRoundKey (T b) (roundKey w j)) → P s') :
    WP isa (.block addRoundKey) s P := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hkey : KeyRel (keyWord s) (roundKey w j) := by
    refine keyRel_congr (hp.keysAt hc j hj) fun k _ => ?_
    simp only [keyWord, wordAddr, hk, addr_add]
  obtain ⟨s', hs', h', hrd, hwr, hoth, hfr⟩ := addRoundKey_ok (hc.arkOk hp hR hk)
  have hc' : Ctx s₀ s' := hc.step hrd hwr (fun r h _ => hoth r h)
    (hfr.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by simp [arkCfg])⟩)
  exact WP.of_runBlock ⟨s', hs', h s' hc' (hoth kp (by decide)) (bs_addRoundKey h' hbs hkey)⟩

theorem cipher_eq (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher R w x = addRoundKey (shiftRows (subBytes (midRounds w (R - 1)
      (addRoundKey x (roundKey w 0))))) (roundKey w R) := rfl

/-- Two blocks, from `InRel` to `InRel` of their encryptions. -/
theorem encrypt2_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hin : InRel (Q s₀) S) :
    WP isa encrypt2 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => cipher R w (S b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w 0)
  -- The rounds done so far.
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R m) ∧ BsRel (Q s) (fun b => midRounds w m (A b))
  let Mid : State → Prop := fun s => Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (keyOff R (R - 1)) ∧
    BsRel (Q s) (fun b => midRounds w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- ortho, the first round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine layer_wp (toBs_ok ((Ctx.refl s₀).linOk hp)) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine keyStart_wp hp hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
    have hbs₂ : BsRel (Q s₂) S := by rw [hq₂]; exact hbs₁
    exact ark_step hp hc₂ hk₂ (by omega) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega, by omega, hc₃, by rw [hk₃, hk₂], hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (round_ok hp hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨by simp [X86.eval, hz, hlast], hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega
      · rw [show R - 1 = m + 1 by omega]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [midRounds_succ]
    · refine .inr ⟨by simp [X86.eval, hz, hlast], R - 1 - (m + 1), by omega, m + 1, rfl, by omega, hc', hk',
        fun b hb i hi => by rw [hbs' b hb i hi]; simp only [midRounds_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [lastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, keyOff_succ (by omega) hR, show R - 1 + 1 = R by omega] at hk₁
    have hbs₁ : BsRel (Q s₁) (fun b => midRounds w (R - 1) (A b)) := by rw [hq₁]; exact hbs
    refine layer_wp (sbox_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := bs_subBytes h₂ hbs₁
    refine layer_wp (shiftRows_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := bs_shiftRows h₃ hbs₂
    refine ark_step hp hc₃ (by rw [hk₃, hk₂, hk₁]) (Nat.le_refl R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine layer_wp (fromBs_ok (hc₄.linOk hp)) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [cipher_eq]; rfl

end VG.Proof.Aes.X86
