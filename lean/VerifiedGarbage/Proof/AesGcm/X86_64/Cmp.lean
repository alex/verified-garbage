import VerifiedGarbage.Proof.AesGcm.X86_64.J0

/-!
# AES-GCM on x86-64: checking a received tag (`tagLenOk`, `recv`, `cmp o`)

Untrusted: everything here is checked by Lean. `tagLenOk` clears ZF iff
§5.2.1.2 allows a tag of `rbx` bytes (`tagLenOk_ok`); `recv` pads the `rbx`
bytes of the received tag at `W` with zeros at `W + 256` (`recv_ok`); `cmp o`
pads the first `rbx` bytes of the tag at `W + o` at `W + 240` and leaves 1 in
`rax` if they are the received ones, 0 if not (`cmp_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le8)

/-! ## The length -/

/-- `cmp r, k`. -/
theorem cmpImm_ok (s : State) (r : Reg) {n k : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64)
    (hk : k < 2 ^ 31) :
    ∃ s', runBlock isa [.alu .cmp r (imm k)] s = some s' ∧ s'.zf = some (decide (n = k)) ∧
      s'.cf = some (decide (n < k)) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, imm]; rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [zf_arithFlags, h, imm_eq hk]; exact congrArg some (sub_beq hn (by omega))
  · rw [cf_arithFlags, h, imm_eq hk, toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (by omega)]
  all_goals rfl

theorem setRcx_ok (s : State) (k : Nat) (hk : k < 2 ^ 32) :
    ∃ s', runBlock isa [.mov32 .rcx (imm k)] s = some s' ∧ s'.gpr .rcx = BitVec.ofNat 64 k ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl

/-- What `tagLenOk` keeps. -/
structure Keeps (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rcx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

/-- `rcx := 1` if the condition holds. -/
theorem setIf_ok {s : State} {c : Cond} {b : Bool} (hc : isa.eval c s = some b) {k : Nat}
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 k) (_hk : k ≤ 1) :
    WP isa (.ite c (.block [.mov32 .rcx (imm 1)]) (.block [])) s fun s' => Keeps s s' ∧
      s'.gpr .rcx = BitVec.ofNat 64 (if b then 1 else k) := by
  refine WP.ite b hc (fun ht => ?_) (fun hf => ?_)
  · obtain ⟨s', run, h1, hg, _, _, hm, hrd, hwr⟩ := setRcx_ok s 1 (by decide)
    exact WP.of_runBlock ⟨s', run, ⟨hg, hm, hrd, hwr⟩, by rw [h1, ht]; rfl⟩
  · exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, by rw [hrcx, hf]; rfl⟩

/-- `tagLenOk`: ZF is clear iff the tag length is allowed. -/
theorem tagLenOk_ok (s : State) {t : Nat} (h : s.gpr .rbx = BitVec.ofNat 64 t) (ht : t < 2 ^ 64) :
    WP isa tagLenOk s fun s' => s'.zf = some (!Spec.Gcm.tagLenOk t) ∧ Keeps s s' := by
  obtain ⟨s₁, run₁, hcx₁, hg₁, -, -, hm₁, hrd₁, hwr₁⟩ := setRcx_ok s 0 (by decide)
  have hbx₁ : s₁.gpr .rbx = BitVec.ofNat 64 t := by rw [hg₁ _ (by decide), h]
  obtain ⟨s₂, run₂, hz₂, -, hg₂, hm₂, hrd₂, hwr₂⟩ := cmpImm_ok s₁ .rbx hbx₁ ht (show 4 < 2 ^ 31 by decide)
  have k₂ : Keeps s s₂ := ⟨fun r hr => by rw [hg₂, hg₁ r hr], hm₂.trans hm₁, hrd₂.trans hrd₁, hwr₂.trans hwr₁⟩
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  refine WP.seq (WP.mono (setIf_ok (eval_e hz₂) (by rw [hg₂, hcx₁]) (k := 0) (by decide)) fun s₃ ⟨k₃, hcx₃⟩ => ?_)
  have hbx₃ : s₃.gpr .rbx = BitVec.ofNat 64 t := by rw [k₃.gpr _ (by decide), hg₂, hbx₁]
  obtain ⟨s₄, run₄, hz₄, -, hg₄, hm₄, hrd₄, hwr₄⟩ := cmpImm_ok s₃ .rbx hbx₃ ht (show 8 < 2 ^ 31 by decide)
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  refine WP.seq (WP.mono (setIf_ok (eval_e hz₄) (k := if decide (t = 4) then 1 else 0) (by rw [hg₄, hcx₃])
    (by split <;> decide)) fun s₅ ⟨k₅, hcx₅⟩ => ?_)
  have hbx₅ : s₅.gpr .rbx = BitVec.ofNat 64 t := by rw [k₅.gpr _ (by decide), hg₄, hbx₃]
  obtain ⟨s₆, run₆, -, hc₆, hg₆, hm₆, hrd₆, hwr₆⟩ := cmpImm_ok s₅ .rbx hbx₅ ht (show 12 < 2 ^ 31 by decide)
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have k₆ : Keeps s s₆ := ((k₂.trans k₃).trans ⟨fun r _ => by rw [hg₄], hm₄, hrd₄, hwr₄⟩).trans k₅ |>.trans
    ⟨fun r _ => by rw [hg₆], hm₆, hrd₆, hwr₆⟩
  generalize hk : (if decide (t = 8) then 1 else if decide (t = 4) then 1 else 0) = k at hcx₅
  have hk1 : k ≤ 1 := by rw [← hk]; split <;> (try split) <;> decide
  have hcx₆ : s₆.gpr .rcx = BitVec.ofNat 64 k := by rw [hg₆, hcx₅]
  have hite : WP isa (.ite .b (.block [])
      (.seq (.block [.alu .cmp .rbx (imm 17)]) (.ite .b (.block [.mov32 .rcx (imm 1)]) (.block [])))) s₆
      (fun s₇ => Keeps s s₇ ∧ s₇.gpr .rcx = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk t then 1 else 0)) := by
    refine WP.ite (decide (t < 12)) (eval_b hc₆) (fun hlt => ?_) (fun hge => ?_)
    · refine WP.block_nil ⟨k₆, ?_⟩
      rw [hcx₆, ← hk]
      have : t < 12 := by simpa using hlt
      simp only [Spec.Gcm.tagLenOk]
      rcases (show t = 4 ∨ t = 8 ∨ (t ≠ 4 ∧ t ≠ 8) by omega) with rfl | rfl | ⟨h4, h8⟩
      · rfl
      · rfl
      · simp [h4, h8, show ¬ 12 ≤ t by omega]
    · have hbx₆ : s₆.gpr .rbx = BitVec.ofNat 64 t := by rw [hg₆, hbx₅]
      obtain ⟨s₇, run₇, -, hc₇, hg₇, hm₇, hrd₇, hwr₇⟩ := cmpImm_ok s₆ .rbx hbx₆ ht (show 17 < 2 ^ 31 by decide)
      refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
      refine WP.mono (setIf_ok (eval_b hc₇) (by rw [hg₇, hcx₆]) hk1) fun s₈ ⟨k₈, hcx₈⟩ =>
        ⟨k₆.trans ⟨fun r _ => by rw [hg₇], hm₇, hrd₇, hwr₇⟩ |>.trans k₈, ?_⟩
      rw [hcx₈, ← hk]
      have : 12 ≤ t := by simpa using hge
      simp only [Spec.Gcm.tagLenOk]
      by_cases h17 : t < 17
      · simp [h17, show t ≠ 4 by omega, show t ≠ 8 by omega, this, show t ≤ 16 by omega]
      · simp [h17, show t ≠ 4 by omega, show t ≠ 8 by omega, show ¬ t ≤ 16 by omega]
  refine WP.seq (WP.mono hite fun s₇ ⟨k₇, hcx₇⟩ => ?_)
  obtain ⟨s₈, run₈, hz₈, hg₈, hm₈, hrd₈, hwr₈⟩ := test_ok s₇ .rcx hcx₇ (by split <;> decide)
  refine WP.of_runBlock ⟨s₈, run₈, ?_, k₇.trans ⟨fun r _ => by rw [hg₈], hm₈, hrd₈, hwr₈⟩⟩
  rw [hz₈]; cases Spec.Gcm.tagLenOk t <;> rfl

/-! ## Padded tags -/

/-- `xs` written over 16 zero bytes at `P`. -/
theorem pad_bytes (m : Mem) (P : Addr) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes ((m.writeW P (0 : BitVec 64)).writeW (P + BitVec.ofNat 64 8) (0 : BitVec 64)) P xs) P 16 =
      xs ++ zeros (16 - xs.length) := by
  rw [bytesAt_writeBytes_prefix _ _ _ hx (by decide)]
  congr 1
  have := zeroT_bytes m P
  rw [show (16 : Nat) = xs.length + (16 - xs.length) by omega, bytesAt_add] at this
  have e := congrArg (List.drop xs.length) this
  rw [List.drop_left' (length_bytesAt _ _ _)] at e
  rw [e, show xs.length + (16 - xs.length) = 16 by omega, zeros, List.drop_replicate]
  rfl

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Cmac.getD_le8 _ (show i / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega, decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

/-- Two blocks are equal iff the OR of the XORs of their words is 0. -/
theorem words_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)
      = 0) ↔ bytesAt m p 16 = bytesAt m q 16 := by
  rw [Cmac.bytesAt_split m p, Cmac.bytesAt_split m q, ← Cmac.le8_readW, ← Cmac.le8_readW, ← Cmac.le8_readW,
    ← Cmac.le8_readW]
  constructor
  · intro h
    have h₁ : m.readW p 64 ^^^ m.readW q 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    have h₂ : m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    rw [BitVec.xor_eq_zero_iff.mp h₁, BitVec.xor_eq_zero_iff.mp h₂]
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Cmac.length_le8, Cmac.length_le8])
    rw [le8_inj h₁, le8_inj h₂, BitVec.xor_self, BitVec.xor_self, BitVec.or_self]; rfl

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `recv`: the `t` bytes of the received tag at `W`, padded at `W + 256`. -/
theorem recv_ok {s : State} (he : Env Ctx St W SP s) {t : Nat} (hbx : s.gpr .rbx = BitVec.ofNat 64 t)
    (h1 : 1 ≤ t) (h16 : t ≤ 16) :
    WP isa recv s fun s' => Env Ctx St W SP s' ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem W t ++ zeros (16 - t) ∧
      Frame [⟨W + BitVec.ofNat 64 256, 16⟩] s.mem s'.mem ∧ s'.gpr .rbx = s.gpr .rbx := by
  have h15 := he.r15
  have w₁ := he.perm.wW (show 256 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 264 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r15 rO) .rax, .store (at_ .r15 (rO + 8)) .rax] ++
        ptr .rdi .r15 rO ++ [.mov .rsi (.reg .r15), .mov .rcx (.reg .rbx)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .rdi = W + BitVec.ofNat 64 256 ∧ s₁.gpr .rsi = W ∧ s₁.gpr .rcx = BitVec.ofNat 64 t ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, hbx]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have dW : (⟨W, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩ := by
    simpa using L.w_w (a := 0) (n := t) (d := 256) (k := 16) (.inl (by omega)) (by omega) (by decide)
  have lp : LoopPre s₁ W (W + BitVec.ofNat 64 256) t :=
    ⟨hsi, hdi, hcx, h1, by omega, covers_left (by simpa using he₁.perm.wC (d := 0) (n := t) (by omega)),
      he₁.perm.wC (by omega), dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_
  have fz : Frame [⟨W + BitVec.ofNat 64 256, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact zeroT_frame _ _
  have hR : bytesAt s₁.mem W t = bytesAt s.mem W t :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW) (by omega)
  have hlen := length_bytesAt s₁.mem W t
  refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂, ?_, ?_, ?_⟩
  · rw [hm₂, hm₁, pad_bytes _ _ _ (by rw [length_bytesAt]; exact h16), length_bytesAt, ← hm₁, hR]
  · refine fz.trans ?_
    rw [hm₂]
    exact (writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  · rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide)]

/-- `cmp o`: 1 in `rax` iff the first `t` bytes of the tag at `W + o` are
the received tag `R`, padded at `W + 256`. -/
theorem cmp_ok {o : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env Ctx St W SP s) {t : Nat}
    (hbx : s.gpr .rbx = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16) {R : List Byte} (hRl : R.length = t)
    (hR : bytesAt s.mem (W + BitVec.ofNat 64 256) 16 = R ++ zeros (16 - t)) :
    WP isa (cmp o) s fun s' => Env Ctx St W SP s' ∧
      s'.gpr .rax = (if bytesAt s.mem (W + BitVec.ofNat 64 o) t = R then 1 else 0) ∧
      Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s'.mem := by
  have h15 := he.r15
  have w₁ := he.perm.wW (show 240 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 248 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r15 vO) .rax, .store (at_ .r15 (vO + 8)) .rax] ++
        ptr .rdi .r15 vO ++ ptr .rsi .r15 o ++ [.mov .rcx (.reg .rbx)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .rdi = W + BitVec.ofNat 64 240 ∧ s₁.gpr .rsi = W + BitVec.ofNat 64 o ∧
      s₁.gpr .rcx = BitVec.ofNat 64 t ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have hoi : o < 2 ^ 31 := by omega
    refine ⟨_, by xrun [h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, h15, imm_eq hoi]
    · simp [gpr_setReg, hbx]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have dW : (⟨W + BitVec.ofNat 64 o, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 240, 16⟩ :=
    L.w_w (.inl (by omega)) (by omega) (by decide)
  have lp : LoopPre s₁ (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 240) t :=
    ⟨hsi, hdi, hcx, h1, by omega, covers_left (he₁.perm.wC (by omega)), he₁.perm.wC (by omega),
      dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.seq (WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  have fz : Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact zeroT_frame _ _
  have hT : bytesAt s₁.mem (W + BitVec.ofNat 64 o) t = bytesAt s.mem (W + BitVec.ofNat 64 o) t :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW) (by omega)
  have hlen := length_bytesAt s₁.mem (W + BitVec.ofNat 64 o) t
  have f₂ : Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s₂.mem := by
    refine fz.trans ?_
    rw [hm₂]
    exact (writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  have hV : bytesAt s₂.mem (W + BitVec.ofNat 64 240) 16 = bytesAt s.mem (W + BitVec.ofNat 64 o) t ++ zeros (16 - t) := by
    rw [hm₂, hm₁, pad_bytes _ _ _ (by rw [length_bytesAt]; exact h16), length_bytesAt, ← hm₁, hT]
  have hR₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 256) 16 = R ++ zeros (16 - t) := by
    rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), hR]
  have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
  have r₁ := he₂.perm.wR (show 240 + 8 ≤ 2560 by decide)
  have r₂ := he₂.perm.wR (show 256 + 8 ≤ 2560 by decide)
  have r₃ := he₂.perm.wR (show 248 + 8 ≤ 2560 by decide)
  have r₄ := he₂.perm.wR (show 264 + 8 ≤ 2560 by decide)
  have h15₂ := he₂.r15
  generalize hX : (s₂.mem.readW (W + BitVec.ofNat 64 240) 64 ^^^ s₂.mem.readW (W + BitVec.ofNat 64 256) 64) |||
    (s₂.mem.readW (W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) 64 ^^^
      s₂.mem.readW (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) 64) = X
  have hXe : X = 0 ↔ bytesAt s.mem (W + BitVec.ofNat 64 o) t = R := by
    rw [← hX, words_eq, hV, hR₂]
    constructor
    · intro e; exact List.append_cancel_right e
    · intro e; rw [e]
  have e248 : W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 248 := add_ofNat_assoc ..
  have e264 : W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 264 := add_ofNat_assoc ..
  rw [e248, e264] at hX
  refine WP.run (Q := fun s₃ => s₃.gpr .rax = (if X = 0 then 1 else 0) ∧ s₃.gpr .r13 = s₂.gpr .r13 ∧
      s₃.gpr .r14 = s₂.gpr .r14 ∧ s₃.gpr .r15 = s₂.gpr .r15 ∧ s₃.gpr .rsp = s₂.gpr .rsp ∧ s₃.mem = s₂.mem ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr)
    ⟨_, by xrun [h15₂, r₁, r₂, r₃, r₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ fun s₃ ⟨hax, h13, h14, h15', hsp, hm, hrd, hwr⟩ =>
      ⟨he₂.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> assumption) hrd hwr,
       by rw [hax]; simp only [hXe], hm ▸ f₂⟩
  · simp only [gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags, ite_true, ite_false, reduceCtorEq, hX]
    by_cases e : X = 0
    · subst e; rfl
    · have : ¬ X.toNat < 1 := fun h => e (BitVec.eq_of_toNat_eq (by simp; omega))
      simp only [e, ite_false, show (1#64 : BitVec 64).toNat = 1 from rfl, this, decide_false]
      rfl
  all_goals rfl

end

end VG.Proof.AesGcm.X86_64
