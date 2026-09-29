import VerifiedGarbage.Proof.Pbkdf2.X86_64.Derive.Block

/-!
# PBKDF2-HMAC-SHA-256 on x86-64: a block of the derived key to `out`, and the loop

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Pbkdf2.X86_64.Derive

open VG VG.X86_64 VG.Impl.Pbkdf2.X86_64
open VG.Impl.Sha256.X86_64 (at_)
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey sha256)
open VG.Proof.Sha256.X86_64 (contains_offset sub_offset toNat_ofNat_lt ea_at ofInt_natCast)
open VG.Proof.Sha256.X86_64.Stream (wp_movzx8 wp_store8 wp_addi wp_subi wp_cmpi wp_test ofNat_succ ofNat_pred
  ofNat_beq_zero)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_snoc writeBytes_nil)
open VG.X86_64.RegBlock (upd wp_run wp_run')

/-! ## Copying bytes -/

/-- `j` of the `n` bytes from `a` copied to `b`. -/
structure Cp (s : State) (a b : Addr) (n j : Nat) (s' : State) : Prop where
  rdi : s'.gpr .rdi = a + BitVec.ofNat 64 j
  rsi : s'.gpr .rsi = b + BitVec.ofNat 64 j
  rcx : s'.gpr .rcx = BitVec.ofNat 64 (n - j)
  keep : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : s'.mem = writeBytes s.mem b (bytesAt s.mem a j)

theorem bytesAt_succ' (m : Mem) (p : Addr) (j : Nat) :
    bytesAt m p (j + 1) = bytesAt m p j ++ [m (p + BitVec.ofNat 64 j)] := by
  simp only [bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

section
variable {s : State} {a b : Addr} {n : Nat} (hn : n < 2 ^ 64)
  (hin : ∀ i < n, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 i) 1)
  (hout : ∀ i < n, InRegions s.wr (b + BitVec.ofNat 64 i) 1)
  (hsep : Region.Disjoint ⟨a, n⟩ ⟨b, n⟩)
include hn hin hout hsep

theorem copy_step {j : Nat} (hj : j < n) {s' : State} (h : Cp s a b n j s') :
    WP isa (.block [.movzx8 .rax (at_ .rdi 0), .store8 (at_ .rsi 0) .rax, .alu .add .rdi (.imm 1),
      .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) s' fun s'' =>
      Cp s a b n (j + 1) s'' ∧ s''.zf = some (decide (n - (j + 1) = 0)) := by
  -- The byte read is not among those written.
  have hsrc : s'.mem (a + BitVec.ofNat 64 j) = s.mem (a + BitVec.ofNat 64 j) := by
    rw [h.mem]
    simp only [writeBytes, Proof.Hmac.X86_64.bytesAt_length]
    split
    · rename_i hc
      exfalso
      refine hsep (a + BitVec.ofNat 64 j) ?_ ?_
      · simp only [Region.Contains]
        rw [show a + BitVec.ofNat 64 j - a = BitVec.ofNat 64 j by bv_omega, toNat_ofNat_lt (by omega)]
        omega
      · simp only [Region.Contains]; omega
    · rfl
  refine wp_movzx8 (a := a + BitVec.ofNat 64 j) (by rw [ea_at, ofInt_natCast, h.rdi]; simp)
    (by rw [h.rd, h.wr]; exact hin j hj) fun s₁ u₁ => ?_
  refine wp_store8 (r := .rax) (a := b + BitVec.ofNat 64 j)
    (by rw [ea_at, ofInt_natCast, u₁.other .rsi (by decide), h.rsi]; simp)
    (by rw [u₁.wr, h.wr]; exact hout j hj) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => WP.block_nil ?_
  have hrcx : s₄.gpr .rcx = BitVec.ofNat 64 (n - j) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), h.rcx]
  refine ⟨⟨?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), h.rdi, se1,
      ofNat_succ, BitVec.add_assoc]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide), h.rsi, se1,
      ofNat_succ, BitVec.add_assoc]
  · rw [u₅.gpr, hrcx, se1, ofNat_pred (by omega), Nat.sub_sub]
  · rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, g₂, u₁.other r h1, h.keep r h1 h2 h3 h4]
  · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr]
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, u₁.gpr, hsrc, h.mem, bytesAt_succ',
      writeBytes_snoc _ _ _ _ (by rw [Proof.Hmac.X86_64.bytesAt_length]; omega), Proof.Hmac.X86_64.bytesAt_length,
      BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
  · rw [hz₅, hrcx, se1, ofNat_pred (by omega), ofNat_beq_zero (by omega), Nat.sub_sub]

theorem copy_loop (hn0 : 0 < n) (hdi : s.gpr .rdi = a) (hsi : s.gpr .rsi = b)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 n) :
    WP isa byteLoop s (Cp s a b n n) := by
  have h₀ : Cp s a b n 0 s :=
    ⟨by rw [hdi]; simp, by rw [hsi]; simp, by rw [hcx]; rfl, fun _ _ _ _ _ => rfl, rfl, rfl,
      by rw [show bytesAt s.mem a 0 = [] from rfl, writeBytes_nil]⟩
  refine WP.loop (M := isa) (fun m s' => ∃ j, m = n - j ∧ j < n ∧ Cp s a b n j s') ?_ n s ⟨0, rfl, hn0, h₀⟩
  rintro m s' ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hn hin hout hsep hj hc) fun s'' ⟨hc', hz⟩ => ?_
  by_cases hl : n - (j + 1) = 0
  · refine .inl ⟨by simp [eval, hz, hl], ?_⟩
    rwa [show j + 1 = n by omega] at hc'
  · exact .inr ⟨by simp [eval, hz, hl], _, by omega, j + 1, rfl, by omega, hc'⟩

end

/-! ## A block to `out` -/

/-- The bytes of the derived key left before block `k + 1`, and how many of them it gives. -/
abbrev L (s₀ : State) (k : Nat) : Nat := ol s₀ - 32 * k
abbrev W (s₀ : State) (k : Nat) : Nat := min 32 (L s₀ k)

theorem ol_lt (s₀ : State) : ol s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt

theorem se32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide

theorem ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

def BO1 (s₀ : State) (k : Nat) (s : State) : Prop :=
  AtT s₀ k s ∧ s.gpr .rcx = BitVec.ofNat 64 32 ∧ s.cf = some (decide (L s₀ k < 32))

def BO2 (s₀ : State) (k : Nat) (s : State) : Prop :=
  AtT s₀ k s ∧ s.gpr .rcx = BitVec.ofNat 64 (W s₀ k)

/-- Before the bytes are copied. -/
structure BO3 (s₀ : State) (k : Nat) (s : State) : Prop where
  regs : Kp s₀ s (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (L s₀ k - W s₀ k)) (BitVec.ofNat 64 (cc s₀ - 1))
    (BitVec.ofNat 64 (64 + sl s₀)) (op s₀ + BitVec.ofNat 64 (32 * k))
  key : KeyR s₀ s.mem
  salt : Repr s.mem (sc s₀ + BitVec.ofNat 64 192) (xorPad (k0 s₀) ipad ++ S s₀)
  lt : 32 * k < ol s₀
  out : bytesAt s.mem (op s₀) (32 * k) = G s₀ k
  t : bytesAt s.mem (sc s₀ + BitVec.ofNat 64 384) 32 = Fk s₀ k
  rdi : s.gpr .rdi = sc s₀ + BitVec.ofNat 64 384
  rsi : s.gpr .rsi = op s₀ + BitVec.ofNat 64 (32 * k)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (W s₀ k)

section

theorem bo1_ok {s₀ : State} {k : Nat} {s : State} (h : AtT s₀ k s) :
    WP isa (.block [.mov32 .rcx (.imm 32), .alu .cmp .r13 (.imm 32)]) s (BO1 s₀ k) := by
  obtain ⟨c, ht⟩ := h
  have := ol_lt s₀
  refine wp_run (is := [.mov32 .rcx (.imm 32)]) rfl fun s₁ g₁ m₁ rd₁ wr₁ =>
    wp_cmpi fun s₂ g₂ m₂ rd₂ wr₂ c₂ _ => WP.block_nil ?_
  have k₁ := c.regs.regs rd₁ wr₁ m₁ (by cs_keep g₁)
  have k₂ := k₁.regs rd₂ wr₂ m₂ (fun r _ => by rw [g₂])
  refine ⟨⟨c.regs' k₂ (m₂.trans m₁), by rw [m₂, m₁]; exact ht⟩, by rw [g₂, g₁]; simp [upd], ?_⟩
  rw [c₂, k₁.r13, se32, toNat_ofNat_lt (by omega)]
  rfl

theorem bo2_ok {s₀ : State} {k : Nat} {s : State} (h : BO1 s₀ k s) :
    WP isa (.ite .b (.block [.mov .rcx (.reg .r13)]) (.block [])) s (BO2 s₀ k) := by
  obtain ⟨⟨c, ht⟩, hcx, hcf⟩ := h
  refine WP.ite _ hcf (fun hb => ?_) (fun hb => WP.block_nil ⟨⟨c, ht⟩, ?_⟩)
  · refine wp_run' rfl fun s' hg hm rd wr =>
      ⟨⟨c.regs' (c.regs.regs rd wr hm (by cs_keep hg)) hm, hm ▸ ht⟩, ?_⟩
    have : L s₀ k < 32 := by simpa using hb
    rw [hg]; simp only [upd, ite_true, c.regs.r13]
    simp only [W, L] at this ⊢
    rw [Nat.min_eq_right (by omega)]
  · have : ¬ L s₀ k < 32 := by simpa using hb
    rw [hcx]; simp only [W, L] at this ⊢
    rw [Nat.min_eq_left (by omega)]

theorem bo3_ok {s₀ : State} {k : Nat} {s : State} (h : BO2 s₀ k s) :
    WP isa (.block ([.alu .sub .r13 (.reg .rcx)] ++ ptr .rdi .rbx 384 ++ [.mov .rsi (.reg .rbp)])) s (BO3 s₀ k) := by
  obtain ⟨⟨c, ht⟩, hcx⟩ := h
  have := ol_lt s₀
  have kr := c.regs
  refine wp_run' rfl fun s' hg hm rd wr => ?_
  have cs : ∀ r, r ≠ .r13 → r ≠ .rdi → r ≠ .rsi → s'.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [hg]; simp [upd, h1, h2, h3]
  refine ⟨⟨kr.base.regs rd wr (cs _ (by decide) (by decide) (by decide)) (cs _ (by decide) (by decide) (by decide)) hm,
    (cs _ (by decide) (by decide) (by decide)).trans kr.r12, ?_, (cs _ (by decide) (by decide) (by decide)).trans kr.r14,
    (cs _ (by decide) (by decide) (by decide)).trans kr.r15, (cs _ (by decide) (by decide) (by decide)).trans kr.rbp⟩,
    hm ▸ c.key, hm ▸ c.salt, c.lt, hm ▸ c.out, hm ▸ ht, ?_, ?_, ?_⟩
  · rw [hg]; simp only [upd, reduceCtorEq, ite_true, ite_false, kr.r13, hcx]
    exact ofNat_sub (by simp only [W, L]; omega) (by omega)
  · rw [hg]; simp [upd, kr.base.rbx, se_ofNat]
  · rw [hg]; simp [upd, kr.rbp]
  · rw [hg]; simp [upd, hcx]

end

open VG.Impl.Sha256.X86_64.Stream (Callee)

/-! ## Copying `T` -/

theorem bytesAt_take (m : Mem) (p : Addr) {j n : Nat} (h : j ≤ n) :
    (bytesAt m p n).take j = bytesAt m p j := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem G_succ (s₀ : State) (k : Nat) : G s₀ (k + 1) = G s₀ k ++ Fk s₀ k := by
  simp only [G, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- After the bytes are copied. -/
structure BO4 (s₀ : State) (k : Nat) (s : State) : Prop where
  regs : Kp s₀ s (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (L s₀ k - W s₀ k)) (BitVec.ofNat 64 (cc s₀ - 1))
    (BitVec.ofNat 64 (64 + sl s₀)) (op s₀ + BitVec.ofNat 64 (32 * k))
  key : KeyR s₀ s.mem
  salt : Repr s.mem (sc s₀ + BitVec.ofNat 64 192) (xorPad (k0 s₀) ipad ++ S s₀)
  lt : 32 * k < ol s₀
  out : bytesAt s.mem (op s₀) (32 * k + W s₀ k) = G s₀ k ++ (Fk s₀ k).take (W s₀ k)
  glen : (G s₀ k).length = 32 * k
  fk : (Fk s₀ k).length = 32
  rsi : s.gpr .rsi = op s₀ + BitVec.ofNat 64 (32 * k + W s₀ k)

theorem cs_copy : ∀ r ∈ calleeSaved, r ≠ .rax ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rcx := by decide

/-- The derived key when the blocks are done. -/
def Done (s₀ : State) (s : State) : Prop :=
  Base s₀ s ∧ bytesAt s.mem (op s₀) (ol s₀) = (G s₀ ((ol s₀ + 31) / 32)).take (ol s₀)

/-- After block `k + 1`: done, or on to the next one. -/
structure Next (s₀ : State) (k : Nat) (s : State) : Prop where
  zf : s.zf = some (decide (L s₀ k - W s₀ k = 0))
  done : L s₀ k - W s₀ k = 0 → Done s₀ s
  next : L s₀ k - W s₀ k ≠ 0 → Core s₀ (k + 1) s

section
variable {s₀ : State} (hp : Pre s₀) {f : Callee} (hv : Vf f)
include hp

theorem bo4_ok {k : Nat} {s : State} (h : BO3 s₀ k s) : WP isa byteLoop s (BO4 s₀ k) := by
  have := ol_lt s₀
  have := h.lt
  have hW : W s₀ k ≤ 32 := Nat.min_le_left _ _
  have hW0 : 0 < W s₀ k := by simp only [W, L]; omega
  have hWL : 32 * k + W s₀ k ≤ ol s₀ := by simp only [W, L]; omega
  have hwr := h.regs.base.wr
  have hsub : Region.Sub ⟨op s₀ + BitVec.ofNat 64 (32 * k), W s₀ k⟩ (outR s₀) := sub_offset (by omega) (by omega)
  refine WP.mono (copy_loop (a := sc s₀ + BitVec.ofNat 64 384) (b := op s₀ + BitVec.ofNat 64 (32 * k))
    (by omega) (fun i hi => by rw [add_ofNat]; exact hp.in_sc' hwr (by omega))
    (fun i hi => ⟨outR s₀, by rw [hwr, hp.wr]; simp, by
      rw [add_ofNat]; exact contains_offset (by omega) (by omega)⟩)
    ((hp.o_sR (o := 384) (n := W s₀ k) (by omega)).symm.sub_right hsub) hW0 h.rdi h.rsi h.rcx) fun s' c => ?_
  have f : Frame [⟨op s₀ + BitVec.ofNat 64 (32 * k), W s₀ k⟩] s.mem s'.mem := by
    rw [c.mem]; exact copy_frame _ _ _ _
  have hd : ∀ {o n : Nat}, o + n ≤ 2048 → ∀ r ∈ [(⟨op s₀ + BitVec.ofNat 64 (32 * k), W s₀ k⟩ : Region)],
      Region.Disjoint (sR s₀ o n) r := fun hon r hr => by
    rw [List.mem_singleton.1 hr]; exact (hp.o_sR hon).symm.sub_right hsub
  have fk : (Fk s₀ k).length = 32 := by rw [← h.t, Proof.Hmac.X86_64.bytesAt_length]
  have glen : (G s₀ k).length = 32 * k := by rw [← h.out, Proof.Hmac.X86_64.bytesAt_length]
  refine ⟨h.regs.call hp c.rd c.wr (fun r hr => let ⟨a, b, d, e⟩ := cs_copy r hr; c.keep r a b d e)
      (f.sub fun r hr => ⟨outR s₀, by simp, by rw [List.mem_singleton.1 hr]; exact hsub⟩),
    ⟨repr_frame f (hd (o := 0) (n := 96) (by omega)) h.key.1, repr_frame f (hd (o := 96) (n := 96) (by omega)) h.key.2⟩,
    repr_frame f (hd (o := 192) (n := 96) (by omega)) h.salt, h.lt, ?_, glen, fk, by rw [c.rsi, add_ofNat]⟩
  have e := Proof.Sha256.Stream.bytesAt_writeBytes s.mem (op s₀) (32 * k)
    (bytesAt s.mem (sc s₀ + BitVec.ofNat 64 384) (W s₀ k)) (by rw [Proof.Hmac.X86_64.bytesAt_length]; omega)
  rw [Proof.Hmac.X86_64.bytesAt_length] at e
  rw [c.mem, e, h.out, ← h.t, bytesAt_take _ _ hW]

omit hp in
theorem bo5_ok {k : Nat} {s : State} (h : BO4 s₀ k s) :
    WP isa (.block [.mov .rbp (.reg .rsi), .alu .add .r12 (.imm 1), .alu .test .r13 (.reg .r13)]) s (Next s₀ k) := by
  have := ol_lt s₀
  have := h.lt
  have kr := h.regs
  refine wp_run (is := [.mov .rbp (.reg .rsi), .alu .add .r12 (.imm 1)]) rfl fun s₁ g₁ m₁ rd₁ wr₁ =>
    wp_test fun s₂ g₂ m₂ rd₂ wr₂ z₂ => WP.block_nil ?_
  have r13' : s₁.gpr .r13 = BitVec.ofNat 64 (L s₀ k - W s₀ k) := by rw [g₁]; simp [upd, kr.r13]
  have r13 : s₂.gpr .r13 = BitVec.ofNat 64 (L s₀ k - W s₀ k) := by rw [g₂, r13']
  have z : s₂.zf = some (decide (L s₀ k - W s₀ k = 0)) := by
    rw [z₂, r13', BitVec.and_self, ofNat_beq_zero (by simp only [W, L]; omega)]
  have base : Base s₀ s₂ := kr.base.regs (rd₂.trans rd₁) (wr₂.trans wr₁) (by rw [g₂, g₁]; simp [upd])
    (by rw [g₂, g₁]; simp [upd]) (m₂.trans m₁)
  refine ⟨z, fun hl => ?_, fun hl => ?_⟩
  · have hW : W s₀ k = ol s₀ - 32 * k := by simp only [W, L] at hl ⊢; omega
    have hk : (ol s₀ + 31) / 32 = k + 1 := by simp only [W, L] at hl; omega
    have hol : ol s₀ = 32 * k + W s₀ k := by omega
    have e1 : bytesAt s₂.mem (op s₀) (ol s₀) = G s₀ k ++ (Fk s₀ k).take (W s₀ k) := by
      rw [m₂, m₁, hol]; exact h.out
    refine ⟨base, ?_⟩
    rw [e1, hk, G_succ, List.take_append, List.take_of_length_le (l := G s₀ k) (by rw [h.glen]; omega), h.glen, hW]
  · have hL : 32 * (k + 1) < ol s₀ := by simp only [W, L] at hl; omega
    have hW : W s₀ k = 32 := by simp only [W, L]; omega
    have hk : 32 * (k + 1) = 32 * k + W s₀ k := by omega
    refine ⟨⟨base, ?_, ?_, ?_, ?_, ?_⟩, m₂ ▸ m₁ ▸ h.key, m₂ ▸ m₁ ▸ h.salt, by omega, ?_⟩
    · rw [g₂, g₁, ofNat_succ (k + 1)]; simp only [upd, reduceCtorEq, ite_true, ite_false, kr.r12, se1]
    · rw [r13, show L s₀ k - W s₀ k = ol s₀ - 32 * (k + 1) by simp only [W, L]; omega]
    · rw [g₂, g₁]; simp [upd, kr.r14]
    · rw [g₂, g₁]; simp [upd, kr.r15]
    · rw [g₂, g₁]; simp [upd, h.rsi, hk]
    · rw [m₂, m₁, hk, h.out, G_succ, hW, List.take_of_length_le (by rw [h.fk])]

theorem blockOut_ok {k : Nat} {s : State} (h : AtT s₀ k s) : WP isa blockOut s (Next s₀ k) :=
  WP.seq (WP.mono (bo1_ok h) fun _ h1 => WP.seq (WP.mono (bo2_ok h1) fun _ h2 => WP.seq (WP.mono (bo3_ok h2)
    fun _ h3 => WP.seq (WP.mono (bo4_ok hp h3) fun _ h4 => bo5_ok h4))))

include hv in
theorem body_ok (sfx : String) {k : Nat} {s : State} (h : Core s₀ k s) : WP isa (block f sfx) s (Next s₀ k) :=
  WP.seq (WP.mono (bu_ok hp hv sfx h) fun _ h1 => WP.seq (WP.mono (bt_ok hp hv sfx h1) fun _ h2 => blockOut_ok hp h2))

include hv in
theorem loop_ok (sfx : String) {s : State} (h : Core s₀ 0 s) : WP isa (.loop (block f sfx) .ne) s (Done s₀) := by
  refine WP.loop (M := isa) (fun n t => ∃ k, n = ol s₀ - 32 * k ∧ Core s₀ k t) ?_ (ol s₀) s ⟨0, by simp, h⟩
  clear h
  rintro n t ⟨k, rfl, hc⟩
  refine WP.mono (body_ok hp hv sfx hc) fun s' hs' => ?_
  by_cases hl : L s₀ k - W s₀ k = 0
  · exact .inl ⟨by simp [eval, hs'.zf, hl], hs'.done hl⟩
  · have := (hs'.next hl).lt
    exact .inr ⟨by simp [eval, hs'.zf, hl], ol s₀ - 32 * (k + 1), by omega, k + 1, rfl, hs'.next hl⟩

end

end VG.Proof.Pbkdf2.X86_64.Derive
