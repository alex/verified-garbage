import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCalls
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`, correct

Untrusted: everything here is checked by Lean. `pbkdf2` saves our caller's
registers, makes the key (hashing a password longer than a block), HMAC's
states for it and the inner state after the salt; then each block `i` of the
output is `U₁` (`update` with `INT (i)` and HMAC's `finalize`), `iterate`
from it, and as much of `T_i` as the output still needs.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK ea_nat wp_mov32r zx32 contains_pre)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Hmac.Generic.X86_64 (initG finG After SavedRegs SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep readW_writeW_ne InRegions.right' sub_of_off sub_of_self bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep bytesAt_getD' writeBytes_at xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-! ## The entry -/

omit hp hz in
/-- After `scratch` is loaded. -/
structure Loaded (s₀ s : State) : Prop where
  r8 : s.gpr .r8 = scr s₀
  r10 : s.gpr .r10 = s₀.gpr .r8
  other : ∀ r, r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

omit hz in
theorem loadScr_ok : WP isa (.block Hash.loadScr) s₀ (Loaded s₀) := by
  simp only [Hash.loadScr]
  refine wp_mov fun s₁ u₁ _ _ => ?_
  refine wp_movm (a := s₀.gpr .rsp + BitVec.ofNat 64 16) (by rw [ea_nat, u₁.other _ (by decide)]) ?_
    fun s₂ u₂ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁.rd, u₁.wr, hp.rd]
    exact ⟨argR s₀, by simp, show (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Contains _ 8 from
      Offset.contains _ (by omega) (by omega) (by omega)⟩
  · rw [u₂.gpr, u₁.mem]; rfl
  · rw [u₂.other _ (by decide), u₁.gpr]
  · intro r h₁ h₂; rw [u₂.other r h₁, u₁.other r h₂]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

theorem entry_ok {s₂ : State} (hl₂ : Loaded s₀ s₂) : WP isa (.block H.entry) s₂ fun s => KR (H := H) s₀ s ∧
    s.gpr .rbx = pw s₀ ∧ s.gpr .rbp = s₀.gpr .rsi ∧ s.gpr .r12 = salt s₀ ∧ s.gpr .r13 = s₀.gpr .rcx ∧
    s.cf = some (decide (pwl s₀ < H.P.B + 1)) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have := hp.snw; have hc0 := hp.c0
  have hS : H.S = H.P.N + H.P.B := rfl
  simp only [Hash.entry]
  have h8 : s₂.gpr .r8 = scr s₀ := hl₂.r8
  have g₂ : ∀ r, r ≠ .r8 → r ≠ .r10 → s₂.gpr r = s₀.gpr r := hl₂.other
  refine VG.Proof.Hmac.Generic.X86_64.save_ok H.hh h8 hW (L := (H.W + H.S) * 8)
    (by rw [hl₂.wr]; exact sc_mem hp) (by show 8 * H.W + 48 ≤ (H.W + H.S) * 8; omega)
    fun s₃ g₃ rd₃ wr₃ f₃ sv₃ => ?_
  refine wp_mov fun s₄ u₄ _ _ => ?_
  have h15 : s₄.gpr .r15 = scr s₀ := by rw [u₄.gpr, g₃, h8]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, wr₃, hl₂.wr]
  refine wp_store (a := A s₀ H.outO) (by rw [ea_nat, h15]) (in_sc hp hz wr₄ (by omega))
    fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_mov32r fun s₆ u₆ => wp_subi fun s₇ u₇ _ => ?_
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, wr₅, wr₄]
  have h15' : s₆.gpr .r15 = scr s₀ := by rw [u₆.other _ (by decide), g₅, h15]
  refine wp_store (a := A s₀ H.cO) (by rw [ea_nat, u₇.other _ (by decide), h15'])
    (by rw [u₇.wr, wr₆]; exact in_sc hp hz rfl (by omega)) fun s₈ g₈ m₈ rd₈ wr₈ => ?_
  refine wp_mov fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ => wp_mov fun s₁₁ u₁₁ _ _ =>
    wp_mov fun s₁₂ u₁₂ _ _ => wp_cmpi fun s₁₃ g₁₃ m₁₃ rd₁₃ wr₁₃ c₁₃ _ => WP.block_nil ?_
  -- The registers.
  have g : ∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r8 → r ≠ .r10 →
      s₁₃.gpr r = s₀.gpr r := fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => by
    rw [g₁₃, u₁₂.other r h₆, u₁₁.other r h₅, u₁₀.other r h₄, u₉.other r h₃, g₈, u₇.other r h₁, u₆.other r h₁,
      g₅, u₄.other r h₂, g₃, g₂ r h₇ h₈]
  have gs : ∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → s₈.gpr r = s₂.gpr r :=
    fun r h₁ h₂ _ _ _ _ => by rw [g₈, u₇.other r h₁, u₆.other r h₁, g₅, u₄.other r h₂, g₃]
  have rax₈ : s₇.gpr .rax = BitVec.ofNat 64 (cc s₀ - 1) := by
    rw [u₇.gpr, u₆.gpr, g₅, u₄.other _ (by decide), g₃, hl₂.r10, zx32, sx1,
      ofNat_pred hc0]
  have r9₄ : s₄.gpr .r9 = out s₀ := by rw [u₄.other _ (by decide), g₃, g₂ _ (by decide) (by decide)]
  -- The memory.
  have m₁₃ : s₁₃.mem = (s₃.mem.writeW (A s₀ H.outO) (out s₀)).writeW (A s₀ H.cO)
      (BitVec.ofNat 64 (cc s₀ - 1)) := by
    rw [m₁₃, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈, u₇.mem, u₆.mem, m₅, u₄.mem, r9₄, rax₈]
  have dOC : Region.Disjoint ⟨A s₀ H.outO, 8⟩ ⟨A s₀ H.cO, 8⟩ := part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  have fW : Frame [sR s₀ H.outO 16] s₃.mem s₁₃.mem := by
    rw [m₁₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl _) (by omega)
      (by omega))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  have f₀ : Frame [outR s₀, scR (H := H) s₀, stkR s₀] s₀.mem s₁₃.mem := by
    have e₂ : s₂.mem = s₀.mem := hl₂.mem
    rw [← e₂]
    refine (f₃.sub fun r hr => ?_).trans (fW.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR (H := H) s₀, by simp, Offset.sub_base _ (by show 8 * H.W + 48 ≤ (H.W + H.S) * 8; omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR (H := H) s₀, by simp, part_sub (by omega)⟩
  have sv : SavedRegs H.hh (scr s₀) s₀ s₃.mem :=
    ⟨by rw [sv₃.rbx, g₂ _ (by decide) (by decide)], by rw [sv₃.rbp, g₂ _ (by decide) (by decide)],
      by rw [sv₃.r12, g₂ _ (by decide) (by decide)], by rw [sv₃.r13, g₂ _ (by decide) (by decide)],
      by rw [sv₃.r14, g₂ _ (by decide) (by decide)], by rw [sv₃.r15, g₂ _ (by decide) (by decide)]⟩
  refine ⟨⟨by rw [rd₁₃, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, rd₈, u₇.rd, u₆.rd, rd₅, u₄.rd, rd₃, hl₂.rd],
    by rw [wr₁₃, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, wr₈, u₇.wr, wr₆],
    g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), g₈, u₇.other _ (by decide), h15'],
    SavedRegs.frame H.hh sv fW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (a := 8 * H.W) (m := 48) (Or.inl (by omega)) (by omega) (by omega),
    by rw [m₁₃, readW_writeW_ne _ _ dOC, Mem.readW_writeW_self64],
    by rw [m₁₃, Mem.readW_writeW_self64], f₀⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [c₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide), sx_ofNat (by omega), toNat_ofNat_lt (by omega)]

/-! ## Helpers -/

omit hp hz in
theorem KR.same {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) (hm : s'.mem = s.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp h15 (rs := []) (hm ▸ Frame.refl [] s.mem) (fun _ h => by simp at h) (fun _ h => by simp at h)

omit hp hz in
theorem KR.upd {s s' : State} (h : KR (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ≠ .r15 ∧ d ≠ .rsp) : KR (H := H) s₀ s' :=
  h.same u.rd u.wr (u.other _ hd.2.symm) (u.other _ hd.1.symm) u.mem

omit hp hz in
/-- `d ← scratch + o`. -/
theorem scr_ok {s : State} {d : Reg} (h15 : s.gpr .r15 = scr s₀) {o : Nat} (ho : o < 2 ^ 31)
    {rest : List Instr} {Q : State → Prop} (k : ∀ s', Upd s s' d (A s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr d o ++ rest)) s Q := by
  simp only [VG.Impl.Hmac.Generic.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_addi fun s₂ u₂ => k s₂ ⟨?_, fun r hr => by rw [u₂.other r hr, u₁.other r hr],
    by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  rw [u₂.gpr, u₁.gpr, h15, sx_ofNat ho]

omit hp hz in
theorem stk_sub {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ 24) :
    Region.Sub (below (s.gpr .rsp) n) (stkR s₀) := by
  rw [h.rsp]; exact below_stk hn

omit hz in
theorem stk_sc {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ 24) {R : Region}
    (hR : Region.Sub R (scR (H := H) s₀)) : (below (s.gpr .rsp) n).Disjoint R :=
  (hp.stk_s.sub_left (stk_sub h hn)).sub_right hR

omit hz in
theorem in_wr {s : State} (h : KR (H := H) s₀ s) : scR (H := H) s₀ ∈ s.wr := by rw [h.wr]; exact sc_mem hp

omit hz in
/-- The parts of `scratch` the functions we call get, as covered regions. -/
theorem cov_part {s : State} (h : KR (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  sub_of_off (in_wr hp h) hon

omit hz in
theorem cov_low {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (⟨scr s₀, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨scr s₀, n⟩ : Region).len ≤ r'.len :=
  sub_of_self (in_wr hp h) hn

/-! ## The key -/

/-- The key HMAC's `init` gets: the password, or the digest of a password
longer than a block, in `scratch`; either gives the same `K₀`. -/
structure KeyAt (hH : HashOK H) (s₀ : State) (m : Mem) (kp : Addr) (kl : Nat) : Prop where
  loc : (kp = pw s₀ ∧ kl = pwl s₀) ∨ (kp = A s₀ H.hkO ∧ kl = H.D)
  le : kl ≤ H.P.B
  k0 : blockKey hH.SH.H (bytesAt m kp kl) = blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

omit hp hz in
theorem hash_len (hH : HashOK H) (m : List Byte) : (hH.SH.H.hash m).length = H.D := by
  rw [hH.hash, List.length_take, VG.Proof.MdStream.Md.hash, hH.md.digest_length]; have := hH.hDN; omega

omit hp hz in
/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash (hH : HashOK H) {k : List Byte} (hk : H.P.B < k.length) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hl := hash_len hH k; have hB := hH.hB; have := hH.hDL
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ H.P.B < H.D by omega))]

omit hp hz in
theorem blockKey_length (hH : HashOK H) (k : List Byte) : (blockKey hH.SH.H k).length = H.P.B := by
  have hB := hH.hB; have := hH.hDL
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [hash_len]; omega
  · omega

omit hp hz in
/-- What the entry sets up, kept until the salt is absorbed. -/
structure KE (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  rbx : s.gpr .rbx = pw s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = salt s₀
  r13 : s.gpr .r13 = s₀.gpr .rcx

/-- The registers `KE` fixes. -/
abbrev eregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

omit hp hz in
theorem KE.upd {s s' : State} (h : KE (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ eregs) : KE (H := H) s₀ s' := by
  have ne : ∀ r ∈ eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u ⟨(ne _ (by simp)).symm, (ne _ (by simp)).symm⟩, by rw [u.other _ (ne _ (by simp)), h.rbx],
    by rw [u.other _ (ne _ (by simp)), h.rbp], by rw [u.other _ (ne _ (by simp)), h.r12],
    by rw [u.other _ (ne _ (by simp)), h.r13]⟩

theorem KE.call {s s' : State} (h : KE (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {ws : List Region} {n : Nat} (hn : n ≤ 24)
    (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) : KE (H := H) s₀ s' :=
  ⟨h.kr.call hp hz hrd hwr hcs hn hf hw, by rw [hcs _ (by simp [calleeSaved]), h.rbx],
    by rw [hcs _ (by simp [calleeSaved]), h.rbp], by rw [hcs _ (by simp [calleeSaved]), h.r12],
    by rw [hcs _ (by simp [calleeSaved]), h.r13]⟩

/-! ### Hashing a password longer than a block -/

omit hp in
theorem hk1_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.stWO)) s fun t =>
      KE (H := H) s₀ t ∧ t.gpr .rdi = A s₀ H.stWO := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W; have hB := hz.z.B_le
  have hN := hz.z.N; have hD := hz.z.D
  rw [← List.append_nil (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.stWO)]
  exact scr_ok h.kr.r15 (by omega) fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), u₁.gpr⟩

theorem hk2_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hdi : s.gpr .rdi = A s₀ H.stWO) :
    WP isa (.call H.initN H.initC) s fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  exact VG.Proof.Hmac.Generic.X86_64.init_call hH.stream (st := A s₀ H.stWO) hdi
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by omega))
    (stk_sc hp h.kr (by omega) (part_sub (by omega))) fun s₂ a₂ r₂ =>
      ⟨h.call hp hz a₂.rd a₂.wr a₂.cs (by omega) a₂.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, _, rfl, by omega, by omega⟩, r₂⟩

/-- `update`'s arguments: the password. -/
theorem hk3_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.stWO ++ ([.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbx),
      .mov .rcx (.reg .rbp), .mov .r8 (.reg .r15)] : List Instr))) s fun t => KE (H := H) s₀ t ∧
      VG.Proof.Hmac.Generic.X86_64.UpdArgs hH.stream t (A s₀ H.stWO) (pw s₀) (scr s₀) (pwl s₀) ∧
      t.gpr .rsi = BitVec.ofNat 64 0 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine scr_ok h.kr.r15 (by omega) fun s₃ u₃ => wp_mov32i fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ => WP.block_nil ?_
  have k₇ := ((((h.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇
    (by decide)
  refine ⟨k₇, ?_, by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl,
    by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact hr⟩
  exact
    { rdi := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.gpr]
      rdx := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
          u₃.other _ (by decide), h.rbx]
      rcx := by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.rbp]
      r8 := by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.kr.r15]
      cd := VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [k₇.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₇.kr (by omega)
        · exact cov_low hp k₇.kr (by rw [hWb]; omega)
      st_sc := (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix (by rw [hWb]; omega))
      d_st := hp.pw_s.sub_right (part_sub (by omega))
      d_sc := hp.pw_s.sub_right (Region.sub_prefix (by rw [hWb]; omega))
      stk_st := stk_sc hp k₇.kr (by omega) (part_sub (by omega))
      stk_d := (hp.stk_pw.sub_left (stk_sub k₇.kr (by omega)))
      stk_sc := stk_sc hp k₇.kr (by omega) (Region.sub_prefix (by rw [hWb]; omega)) }

theorem hk4_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (ua : VG.Proof.Hmac.Generic.X86_64.UpdArgs hH.stream s (A s₀ H.stWO) (pw s₀) (scr s₀) (pwl s₀))
    (hsi : s.gpr .rsi = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.call H.updN H.updC) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Hmac.Generic.X86_64.upd_call hH.stream ua (by have := hp.pwnw; omega) fun s₈ a₈ r₈ =>
    ⟨h.call hp hz a₈.rd a₈.wr a₈.cs (by omega) a₈.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by omega, by omega⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; omega⟩
  · have := r₈ [] hr hsi
    rwa [List.nil_append, h.kr.pwBytes hp] at this

/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.stWO ++ ([.mov .rsi (.reg .rbp)] : List Instr) ++
      VG.Impl.Hmac.Generic.X86_64.scr .rdx H.hkO ++ ([.mov .rcx (.reg .r15)] : List Instr))) s fun t =>
      KE (H := H) s₀ t ∧ VG.Proof.Hmac.Generic.X86_64.FinArgs hH.stream t (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀) ∧
      t.gpr .rsi = s₀.gpr .rsi ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  simp only [List.append_assoc]
  refine scr_ok h.kr.r15 (by omega) fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ _ _ => ?_
  refine scr_ok (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), h.kr.r15]) (by omega)
    fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ _ _ => WP.block_nil ?_
  have k₁₂ := (((h.upd u₉ (by decide)).upd u₁₀ (by decide)).upd u₁₁ (by decide)).upd u₁₂ (by decide)
  refine ⟨k₁₂, ?_, by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
    h.rbp], by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]; exact hr⟩
  exact
    { rdi := by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr]
      rdx := by rw [u₁₂.other _ (by decide), u₁₁.gpr]
      rcx := by rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), h.kr.r15]
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₁₂.kr (by omega)
        · exact cov_part hp k₁₂.kr (by rw [hF]; omega)
        · exact cov_low hp k₁₂.kr (by rw [hWb]; omega)
      st_o := part_disj hz (Or.inl (by omega)) (by omega) (by rw [hF]; omega)
      st_sc := (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix (by rw [hWb]; omega))
      o_sc := (low_disj hz (by omega) (by rw [hF]; omega)).sub_right (Region.sub_prefix (by rw [hWb]; omega))
      stk_st := stk_sc hp k₁₂.kr (by omega) (part_sub (by omega))
      stk_o := stk_sc hp k₁₂.kr (by omega) (part_sub (by rw [hF]; omega))
      stk_sc := stk_sc hp k₁₂.kr (by omega) (Region.sub_prefix (by rw [hWb]; omega)) }

theorem hk6_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (fa : VG.Proof.Hmac.Generic.X86_64.FinArgs hH.stream s (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀))
    (hsi : s.gpr .rsi = s₀.gpr .rsi) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.call H.finN H.finC) s fun t => KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Hmac.Generic.X86_64.fin_call hH.stream fa fun s₁₃ a₁₃ r₁₃ =>
    ⟨h.call hp hz a₁₃.rd a₁₃.wr a₁₃.cs (by omega) a₁₃.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, rfl, by omega, by omega⟩
    · exact .inr ⟨_, _, rfl, by omega, by rw [hF]; omega⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; omega⟩
  · rw [bytesAt_take _ _ hD.2.1]
    exact r₁₃ _ hr (by rw [bytesAt_length]; exact (s₀.gpr .rsi).isLt)
      (by rw [hsi, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp in
theorem hk7_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdx H.hkO ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.D))] : List Instr))) s fun t =>
      KE (H := H) s₀ t ∧ t.gpr .rdx = A s₀ H.hkO ∧ (t.gpr .rcx).toNat = H.D ∧ t.mem = s.mem := by
  have hl := layout (H := H); have he := end_le hz; have hD := hz.z.D; have hN := hz.z.N
  have hL := L_lt hz; have hW := hz.W; have hB := hz.z.B_le
  refine scr_ok h.kr.r15 (by omega) fun s₁₄ u₁₄ => wp_mov32i fun s₁₅ u₁₅ _ _ => WP.block_nil ?_
  exact ⟨(h.upd u₁₄ (by decide)).upd u₁₅ (by decide), by rw [u₁₅.other _ (by decide), u₁₄.gpr],
    by rw [u₁₅.gpr, zx_ofNat (by omega), toNat_ofNat_lt (by omega)], by rw [u₁₅.mem, u₁₄.mem]⟩

theorem hashKey_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) :
    WP isa H.hashKey s fun t => KE (H := H) s₀ t ∧ t.gpr .rdx = A s₀ H.hkO ∧ (t.gpr .rcx).toNat = H.D ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (hk1_ok hz h) fun s₁ ⟨k₁, d₁⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hp hz hH k₂ r₂) fun s₃ ⟨k₃, a₃, i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok hp hz hH k₄ r₄) fun s₅ ⟨k₅, a₅, i₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok hz k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

omit hp hz in
/-- Where the key is, and its length. -/
abbrev kp (H : Hash) (s₀ : State) : Addr := if pwl s₀ < H.P.B + 1 then pw s₀ else A s₀ H.hkO
omit hp hz in
abbrev kl (H : Hash) (s₀ : State) : Nat := if pwl s₀ < H.P.B + 1 then pwl s₀ else H.D

theorem key_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (hcf : s.cf = some (decide (pwl s₀ < H.P.B + 1))) :
    WP isa H.key s fun t => KE (H := H) s₀ t ∧ t.gpr .rdx = kp H s₀ ∧ (t.gpr .rcx).toNat = kl H s₀ ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hD := hz.z.D
  unfold Hash.key
  refine WP.ite (!decide (pwl s₀ < H.P.B + 1)) (by simp [eval, hcf]) (fun hT => ?_) fun hF => ?_
  · have hlong : ¬ pwl s₀ < H.P.B + 1 := of_decide_eq_false (Bool.not_eq_true' _ ▸ hT)
    have e₁ : kp H s₀ = A s₀ H.hkO := ite_eq_right_of_eq_false _ _ (eq_false hlong)
    have e₂ : kl H s₀ = H.D := ite_eq_right_of_eq_false _ _ (eq_false hlong)
    rw [e₁, e₂]
    refine WP.mono (hashKey_ok hp hz hH h) fun t ⟨k, rdx, rcx, hb⟩ =>
      ⟨k, rdx, rcx, ⟨.inr ⟨rfl, rfl⟩, by omega, ?_⟩⟩
    rw [hb, blockKey_hash hH (by rw [bytesAt_length]; omega)]
  · have hshort : pwl s₀ < H.P.B + 1 := of_decide_eq_true (by simpa using hF)
    have e₁ : kp H s₀ = pw s₀ := ite_eq_left_of_eq_true _ _ (eq_true hshort)
    have e₂ : kl H s₀ = pwl s₀ := ite_eq_left_of_eq_true _ _ (eq_true hshort)
    rw [e₁, e₂]
    refine wp_mov fun t₁ u₁ _ _ => wp_mov fun t₂ u₂ _ _ => WP.block_nil ?_
    refine ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.rbx],
      by rw [u₂.gpr, u₁.other _ (by decide), h.rbp], ⟨.inl ⟨rfl, rfl⟩, by omega, ?_⟩⟩
    rw [u₂.mem, u₁.mem, h.kr.pwBytes hp]

/-! ## HMAC's states -/

omit hp hz in
theorem repr_keep (hH : HashOK H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.stream.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd
    (by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 2 ^ 64; omega) hi) hr

omit hp hz in
/-- A state copied from `p` to `q` represents the same message. -/
theorem repr_copy (hH : HashOK H) {m : Mem} {p q : Addr} {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr (writeBytes m q (bytesAt m p H.S)) q msg := by
  have : H.S ≤ 256 := by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 256; omega
  refine hH.stream.repr _ _ _ _ _ (fun i hi => ?_) hr
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ (show i < H.S from hi)]

/-- `K₀`, the password as a key. -/
abbrev K0 (hH : HashOK H) (s₀ : State) : List Byte := blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- HMAC's states in `scratch`: `K₀ ⊕ ipad`, `K₀ ⊕ opad`, and `K₀ ⊕ ipad`
after the salt. -/
structure States (hH : HashOK H) (s₀ : State) (m : Mem) : Prop where
  i : hH.SH.Repr m (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad)
  o : hH.SH.Repr m (A s₀ H.st1O) (xorPad (K0 hH s₀) opad)
  s : hH.SH.Repr m (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad ++ bytesAt s₀.mem (salt s₀) (sl s₀))

omit hp in
theorem States.keep (hH : HashOK H) {m m' : Mem} (h : States hH s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ H.st0O (3 * H.S)) r) : States hH s₀ m' := by
  have hl := layout (H := H); have he := end_le hz
  exact ⟨repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by omega))) h.i,
    repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) h.o,
    repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) h.s⟩

omit hz in
/-- Regions a call writes, disjoint from a part of `scratch`. -/
theorem disj_call {s : State} (h : KR (H := H) s₀ s) {X : Region} (hX : Region.Sub X (scR (H := H) s₀))
    {ws : List Region} {n : Nat} (hn : n ≤ 24) (hw : ∀ r ∈ ws, X.Disjoint r) :
    ∀ r ∈ ws ++ [below (s.gpr .rsp) n], X.Disjoint r := fun r hr => by
  rcases List.mem_append.mp hr with hr | hr
  · exact hw r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact (stk_sc hp h hn hX).symm

/-- The key's region: where HMAC's `init` may read it. -/
theorem KeyAt.facts (hH : HashOK H) {m : Mem} {kp : Addr} {kl : Nat} (hk : KeyAt hH s₀ m kp kl) {s : State}
    (h : KR (H := H) s₀ s) :
    Covers [⟨kp, kl⟩] (s.rd ++ s.wr) ∧ Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st0O, H.S⟩ ∧
      Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st1O, H.S⟩ ∧ Region.Disjoint ⟨kp, kl⟩ (lowR (H := H) s₀) ∧
      (below (s.gpr .rsp) 24).Disjoint ⟨kp, kl⟩ := by
  have hl := layout (H := H); have he := end_le hz; have hD := hz.z.D; have hN := hz.z.N
  rcases hk.loc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [h.rd, hp.rd]; simp)),
      hp.pw_s.sub_right (part_sub (by omega)), hp.pw_s.sub_right (part_sub (by omega)),
      hp.pw_s.sub_right low_sub, hp.stk_pw.sub_left (stk_sub h (Nat.le_refl _))⟩
  · refine ⟨Covers.of_sub fun r hr => ?_, part_disj hz (Or.inr (by omega)) (by omega) (by omega),
      part_disj hz (Or.inr (by omega)) (by omega) (by omega), low_disj hz (by omega) (by omega),
      stk_sc hp h (Nat.le_refl _) (part_sub (by omega))⟩
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨r', h', off, e, l⟩ := cov_part hp h (o := H.hkO) (n := H.D) (by omega)
    exact ⟨r', List.mem_append_right _ h', off, e, l⟩

/-- HMAC's `init`'s arguments: its two states and the key. -/
theorem su1_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hdx : s.gpr .rdx = kp H s₀)
    (hcx : (s.gpr .rcx).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.st0O ++ VG.Impl.Hmac.Generic.X86_64.scr .rsi H.st1O ++
      ([.mov .r8 (.reg .r15)] : List Instr))) s fun t => KE (H := H) s₀ t ∧
      InitArgs (H := H) t (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀) ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  simp only [List.append_assoc]
  refine scr_ok h.kr.r15 (by omega) fun s₁ u₁ => ?_
  refine scr_ok (by rw [u₁.other _ (by decide), h.kr.r15]) (by omega) fun s₂ u₂ => wp_mov fun s₃ u₃ _ _ =>
    WP.block_nil ?_
  have k₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain ⟨kc, k_i, k_o, k_s, k_stk⟩ := hk.facts hp hz hH k₃.kr
  refine ⟨k₃, ?_, m₃ ▸ hk⟩
  exact
    { rdi := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      rsi := by rw [u₃.other _ (by decide), u₂.gpr]
      rdx := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdx]
      rcx := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hcx]
      r8 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.r15]
      klB := hk.le
      cr := kc
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₃.kr (by omega)
        · exact cov_part hp k₃.kr (by omega)
        · exact cov_low hp k₃.kr (by omega)
      i_o := part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      i_s := low_disj hz (by omega) (by omega)
      o_s := low_disj hz (by omega) (by omega)
      k_i := k_i
      k_o := k_o
      k_s := k_s
      stk_i := stk_sc hp k₃.kr (Nat.le_refl _) (part_sub (by omega))
      stk_o := stk_sc hp k₃.kr (Nat.le_refl _) (part_sub (by omega))
      stk_k := k_stk
      stk_s := stk_sc hp k₃.kr (Nat.le_refl _) low_sub
      scnw := by show (scr s₀).toNat + 8 * H.W ≤ 2 ^ 64; omega }

/-- HMAC's `init`: the key's inner and outer states. -/
theorem su2_ok (hH : HashOK H) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) {s : State} (h : KE (H := H) s₀ s)
    (ia : InitArgs (H := H) s (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀))
    (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.call H.hmacInitN H.hmacInit) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine hinit_call hH hI hIsp hId ia fun s₄ rd₄ wr₄ cs₄ f₄ ri₄ ro₄ => ⟨?_, ?_, ?_⟩
  · exact h.call hp hz rd₄ wr₄ cs₄ (Nat.le_refl _) f₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by omega⟩
      · exact .inr ⟨_, _, rfl, by omega, by omega⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · rw [hk.k0] at ri₄; exact ri₄
  · rw [hk.k0] at ro₄; exact ro₄

/-- The inner state copied, and `update`'s arguments: the salt. -/
theorem su3_ok (hH : HashOK H) {s₄ : State} (h : KE (H := H) s₀ s₄)
    (ri₄ : hH.SH.Repr s₄.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad))
    (ro₄ : hH.SH.Repr s₄.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad)) :
    WP isa (.seq (VG.Impl.Hmac.Generic.X86_64.copy .r15 H.st0O .r15 H.stSO H.S)
      (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.stSO ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 H.P.B)),
        .mov .rdx (.reg .r12), .mov .rcx (.reg .r13), .mov .r8 (.reg .r15)] : List Instr)))) s₄ fun t =>
      KE (H := H) s₀ t ∧
      VG.Proof.Hmac.Generic.X86_64.UpdArgs hH.stream t (A s₀ H.stSO) (salt s₀) (scr s₀) (sl s₀) ∧
      t.gpr .rsi = BitVec.ofNat 64 H.P.B ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad) ∧
      hH.SH.Repr t.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine WP.seq (WP.mono (VG.Proof.Hmac.Generic.X86_64.copy_ok (src := .r15) (dst := .r15) (by decide) (by decide)
    (so := H.st0O) (d := H.stSO) (n := H.S) (by omega) (by omega) (s := s₄)
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz h.kr.wr (by omega)))
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega))
    (by rw [h.kr.r15]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega))) fun s₅ c₅ => ?_)
  rw [h.kr.r15] at c₅
  have f₅ : Frame [sR s₀ H.stSO H.S] s₄.mem s₅.mem := by
    rw [c₅.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have k₅ : KE (H := H) s₀ s₅ := ⟨h.kr.write hz c₅.rd c₅.wr (c₅.other _ (by decide) (by decide))
      (c₅.other _ (by decide) (by decide)) (o := H.stSO) (n := H.S) (by omega) (by omega) f₅,
    by rw [c₅.other _ (by decide) (by decide), h.rbx], by rw [c₅.other _ (by decide) (by decide), h.rbp],
    by rw [c₅.other _ (by decide) (by decide), h.r12], by rw [c₅.other _ (by decide) (by decide), h.r13]⟩
  have dS : ∀ o, o + H.S ≤ H.stSO → ∀ r ∈ [sR s₀ H.stSO H.S], Region.Disjoint ⟨A s₀ o, H.S⟩ r := fun o ho r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl ho) (by omega) (by omega)
  have ri₅ := repr_keep hH f₅ (dS _ (by omega)) ri₄
  have ro₅ := repr_keep hH f₅ (dS _ (by omega)) ro₄
  have rs₅ : hH.SH.Repr s₅.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad) := by rw [c₅.mem]; exact repr_copy hH ri₄
  refine scr_ok k₅.kr.r15 (by omega) fun s₆ u₆ => wp_mov32i fun s₇ u₇ _ _ => wp_mov fun s₈ u₈ _ _ =>
    wp_mov fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ => WP.block_nil ?_
  have k₁₀ := ((((k₅.upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀
    (by decide)
  have m₁₀ : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  refine ⟨k₁₀, ?_, by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      zx_ofNat (by omega)], m₁₀ ▸ ri₅, m₁₀ ▸ ro₅, m₁₀ ▸ rs₅⟩
  exact
    { rdi := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
          u₇.other _ (by decide), u₆.gpr]
      rdx := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.r12]
      rcx := by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.r13]
      r8 := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.kr.r15]
      cd := VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [k₁₀.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₁₀.kr (by omega)
        · exact cov_low hp k₁₀.kr (by rw [hWb]; omega)
      st_sc := (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix (by rw [hWb]; omega))
      d_st := hp.sa_s.sub_right (part_sub (by omega))
      d_sc := hp.sa_s.sub_right (Region.sub_prefix (by rw [hWb]; omega))
      stk_st := stk_sc hp k₁₀.kr (by omega) (part_sub (by omega))
      stk_d := hp.stk_sa.sub_left (stk_sub k₁₀.kr (by omega))
      stk_sc := stk_sc hp k₁₀.kr (by omega) (Region.sub_prefix (by rw [hWb]; omega)) }

/-- `update` with the salt. -/
theorem su4_ok (hH : HashOK H) {s₁₀ : State} (k₁₀ : KE (H := H) s₀ s₁₀)
    (ua : VG.Proof.Hmac.Generic.X86_64.UpdArgs hH.stream s₁₀ (A s₀ H.stSO) (salt s₀) (scr s₀) (sl s₀))
    (hsi : s₁₀.gpr .rsi = BitVec.ofNat 64 H.P.B)
    (ri : hH.SH.Repr s₁₀.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad))
    (ro : hH.SH.Repr s₁₀.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad))
    (rs : hH.SH.Repr s₁₀.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad)) :
    WP isa (.call H.updN H.updC) s₁₀ fun t => KE (H := H) s₀ t ∧ States hH s₀ t.mem := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine VG.Proof.Hmac.Generic.X86_64.upd_call hH.stream ua (by have := hp.sanw; omega) fun s₁₁ a₁₁ r₁₁ => ?_
  have k₁₁ := k₁₀.call hp hz a₁₁.rd a₁₁.wr a₁₁.cs (by omega) a₁₁.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by omega, by omega⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; omega⟩
  have dW : ∀ o, H.st0O ≤ o → o + H.S ≤ H.stSO → ∀ r ∈ [(⟨A s₀ H.stSO, H.stream.S⟩ : Region), ⟨scr s₀, hH.stream.Wb⟩] ++
      [below (s₁₀.gpr .rsp) 16], Region.Disjoint ⟨A s₀ o, H.S⟩ r := fun o ho₀ ho =>
    disj_call hp k₁₀.kr (part_sub (by omega)) (by omega) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact part_disj hz (Or.inl ho) (by omega) (by omega)
      · exact (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix (by rw [hWb]; omega))
  refine ⟨k₁₁, repr_keep hH a₁₁.frame (dW _ (by omega) (by omega)) ri,
    repr_keep hH a₁₁.frame (dW _ (by omega) (by omega)) ro, ?_⟩
  have := r₁₁ _ rs (by rw [hsi, xorPad_length, blockKey_length])
  rwa [k₁₀.kr.saltBytes hp] at this

theorem setup_ok (hH : HashOK H) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) {s : State} (h : KE (H := H) s₀ s)
    (hdx : s.gpr .rdx = kp H s₀) (hcx : (s.gpr .rcx).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa H.setup s fun t => KE (H := H) s₀ t ∧ States hH s₀ t.mem := by
  unfold Hash.setup
  refine WP.seq (WP.mono (su1_ok hp hz hH h hdx hcx hk) fun s₁ ⟨k₁, a₁, h₁⟩ => ?_)
  refine WP.seq (WP.mono (su2_ok hp hz hH hI hIsp hId k₁ a₁ h₁) fun s₂ ⟨k₂, i₂, o₂⟩ => ?_)
  refine WP.assoc (WP.seq (WP.mono (su3_ok hp hz hH k₂ i₂ o₂) fun s₃ ⟨k₃, a₃, si₃, i₃, o₃, r₃⟩ => ?_))
  exact su4_ok hp hz hH k₃ a₃ si₃ i₃ o₃ r₃

end

end VG.Proof.Pbkdf2.Md.X86_64.Pbk
