import VerifiedGarbage.Proof.Pbkdf2.AArch64.Derive.Key
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Finalize

/-!
# PBKDF2-HMAC-SHA-256 on AArch64: one block's `U₁` and `T`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Pbkdf2.AArch64Derive

open VG VG.AArch64 VG.Impl.Pbkdf2.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey sha256)
open VG.Proof.Sha256.AArch64 (contains_offset toNat_ofNat_lt)
open VG.Proof.Sha256.AArch64.Stream (wp_str32)
open VG.Proof.Pbkdf2.X86_64.Derive (copy_frame copy_bytes repr_of_bytes wordBytes_int)
open VG.AArch64.RegBlock (upd wp_run wp_run')

/-! ## The derived key so far -/

/-- `T_{i+1}`. -/
def Fk (s₀ : State) (i : Nat) : List Byte :=
  Spec.Pbkdf2.F (Spec.Hmac.hmac sha256 (P s₀)) (S s₀) (cc s₀) (i + 1)

/-- `T₁ ‖ … ‖ T_k`. -/
def G (s₀ : State) (k : Nat) : List Byte := (List.range k).flatMap (Fk s₀)

/-- `U₁` of block `k + 1`. -/
def u1 (s₀ : State) (k : Nat) : List Byte := hmacBlockKey sha256 (k0 s₀) (S s₀ ++ Spec.Pbkdf2.int (k + 1))

/-- The registers in the loop over the blocks, before block `k + 1`. -/
abbrev KpL (s₀ s : State) (k : Nat) : Prop :=
  Kp s₀ s (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (ol s₀ - 32 * k)) (BitVec.ofNat 64 (cc s₀ - 1))
    (BitVec.ofNat 64 (64 + sl s₀)) (op s₀ + BitVec.ofNat 64 (32 * k))

/-- What holds throughout block `k + 1`. -/
structure Core (s₀ : State) (k : Nat) (s : State) : Prop where
  regs : KpL s₀ s k
  key : KeyR s₀ s.mem
  salt : Repr s.mem (sc s₀ + BitVec.ofNat 64 192) (xorPad (k0 s₀) ipad ++ S s₀)
  lt : 32 * k < ol s₀
  out : bytesAt s.mem (op s₀) (32 * k) = G s₀ k

theorem ol_lt (s₀ : State) : ol s₀ < 2 ^ 64 := (s₀.gpr .x6).isLt

theorem Core.frame {s₀ : State} {k : Nat} {s s' : State} {rs : List Region} (h : Core s₀ k s)
    (regs : KpL s₀ s' k) (hf : Frame rs s.mem s'.mem) (hk : ∀ r ∈ rs, (sR s₀ 0 288).Disjoint r)
    (ho : ∀ r ∈ rs, (outR s₀).Disjoint r) : Core s₀ k s' where
  regs := regs
  key := ⟨repr_frame hf (fun r hr => (hk r hr).sub_left (sR_sub_sR s₀ (by omega) (by omega) (by omega))) h.key.1,
    repr_frame hf (fun r hr => (hk r hr).sub_left (sR_sub_sR s₀ (by omega) (by omega) (by omega))) h.key.2⟩
  salt := repr_frame hf (fun r hr => (hk r hr).sub_left (sR_sub_sR s₀ (by omega) (by omega) (by omega))) h.salt
  lt := h.lt
  out := by
    have := h.lt
    have := ol_lt s₀
    rw [← h.out]
    exact frame_bytesAt hf (fun r hr => (ho r hr).sub_left (Region.sub_prefix (by omega))) (by omega)

theorem Core.regs' {s₀ : State} {k : Nat} {s s' : State} (h : Core s₀ k s) (regs : KpL s₀ s' k)
    (hm : s'.mem = s.mem) : Core s₀ k s' :=
  ⟨regs, hm ▸ h.key, hm ▸ h.salt, h.lt, hm ▸ h.out⟩

set_option hygiene false in
/-- The regions a call writes are clear of the key, the salt and `out`. -/
macro "cdj" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  repeat' apply And.intro
  all_goals dj))

/-! ## `INT (i)` -/

theorem int_bytes (m : Mem) (a : Addr) {i : Nat} (h : i < 2 ^ 32) :
    bytesAt (m.writeW a (rev32 (BitVec.ofNat 32 i))) a 4 = Spec.Pbkdf2.int i := by
  rw [Proof.Sha256.AArch64.Stream.Finalize.writeW_rev32, ← wordBytes_int h]
  exact Proof.Hmac.X86_64.bytesAt_writeBytes_self _ _ _ (by simp [Spec.Sha256.wordBytes])

theorem setWidth_ofNat32 (n : Nat) : (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sw32 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v := by ext i hi; simp

/-! ## `U₁` -/

theorem Pre.k_lt {s₀ : State} (hp : Pre s₀) {k : Nat} {s : State} (h : Core s₀ k s) : k + 1 < 2 ^ 32 := by
  have := h.lt; have := hp.len; omega

def BU1 (s₀ : State) (k : Nat) (s : State) : Prop :=
  Core s₀ k s ∧ Repr s.mem (sc s₀ + BitVec.ofNat 64 288) (xorPad (k0 s₀) ipad ++ S s₀) ∧
  bytesAt s.mem (sc s₀ + BitVec.ofNat 64 416) 4 = Spec.Pbkdf2.int (k + 1) ∧
  s.gpr .x0 = sc s₀ + BitVec.ofNat 64 288 ∧ s.gpr .x1 = BitVec.ofNat 64 (64 + sl s₀) ∧
  s.gpr .x2 = sc s₀ + BitVec.ofNat 64 416 ∧ s.gpr .x3 = BitVec.ofNat 64 4 ∧
  s.gpr .x4 = sc s₀ + BitVec.ofNat 64 528

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem bu1_ok {k : Nat} {s : State} (h : Core s₀ k s) :
    WP isa (.block ((List.range 12).flatMap (Impl.Hmac.AArch64.cp64 .x19 .x19 192 288) ++
      [.rev32 .x9 .x20, .str .w .x9 .x19 416, .addImm .x .x0 .x19 288, mov .x1 .x23, .addImm .x .x2 .x19 416,
        .movz .x .x3 4 0, .addImm .x .x4 .x19 528])) s (BU1 s₀ k) := by
  have kr := h.regs
  refine sc_copy hp kr.base.x19 kr.base.wr (o₁ := 192) (o₂ := 288) (n := 12) (by omega) (by omega) (by omega)
    (by decide) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  have f₁ : Frame [sR s₀ 288 96] s.mem s₁.mem := by rw [m₁]; exact copy_frame _ _ _ _
  have k₁ : KpL s₀ s₁ k := kr.call hp rd₁ wr₁ sp₁ (fun r hr _ => g₁ r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    (f₁.sub (by fwk))
  have c₁ : Core s₀ k s₁ := h.frame k₁ f₁ (by cdj) (by cdj)
  have hS : Repr s₁.mem (sc s₀ + BitVec.ofNat 64 288) (xorPad (k0 s₀) ipad ++ S s₀) := by
    refine repr_of_bytes ?_ h.salt
    rw [m₁, show 8 * 12 = 96 from rfl, copy_bytes _ _ _ _ (by omega)]
  refine wp_run (is := [.rev32 .x9 .x20]) rfl fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have k₂ : KpL s₀ s₂ k := k₁.regs rd₂ wr₂ sp₂ m₂ (by cs_keep g₂)
  have x9 : (s₂.gpr .x9).setWidth 32 = rev32 (BitVec.ofNat 32 (k + 1)) := by
    rw [g₂]; simp only [upd, ite_true]; rw [sw32, k₁.x20, setWidth_ofNat32]
  refine wp_str32 (a := sc s₀ + BitVec.ofNat 64 416) (by decide) (by rw [k₂.base.x19])
    (hp.in_sc k₂.base.wr (by omega)) fun s₃ u₃ => ?_
  have f₃ : Frame [sR s₀ 416 4] s₂.mem s₃.mem := by
    rw [u₃.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sR s₀ (w := 32 / 8) le_rfl le_rfl (by omega))
  have k₃ : KpL s₀ s₃ k := k₂.call hp u₃.rd u₃.wr u₃.sp (fun r _ _ => by rw [u₃.gpr]) (f₃.sub (by fwk))
  have c₃ : Core s₀ k s₃ := (c₁.regs' k₂ m₂).frame k₃ f₃ (by cdj) (by cdj)
  have hI : bytesAt s₃.mem (sc s₀ + BitVec.ofNat 64 416) 4 = Spec.Pbkdf2.int (k + 1) := by
    rw [u₃.mem, x9]; exact int_bytes _ _ (hp.k_lt h)
  have hS₃ : Repr s₃.mem (sc s₀ + BitVec.ofNat 64 288) (xorPad (k0 s₀) ipad ++ S s₀) :=
    repr_frame f₃ (by cdj) (m₂ ▸ hS)
  refine wp_run' rfl fun s' hg hm rd wr sp =>
    ⟨c₃.regs' (k₃.regs rd wr sp hm (by cs_keep hg)) hm, hm ▸ hS₃, hm ▸ hI, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hg] <;> simp [upd, k₃.base.x19, k₃.x23]

end

def BU2 (s₀ : State) (k : Nat) (s : State) : Prop :=
  Core s₀ k s ∧ Repr s.mem (sc s₀ + BitVec.ofNat 64 288) (xorPad (k0 s₀) ipad ++ (S s₀ ++ Spec.Pbkdf2.int (k + 1)))

def BU3 (s₀ : State) (k : Nat) (s : State) : Prop :=
  BU2 s₀ k s ∧ s.gpr .x0 = sc s₀ + BitVec.ofNat 64 288 ∧ s.gpr .x1 = sc s₀ + BitVec.ofNat 64 96 ∧
  s.gpr .x2 = BitVec.ofNat 64 (64 + (sl s₀ + 4)) ∧ s.gpr .x3 = sc s₀ + BitVec.ofNat 64 912

/-- After `blockU`. -/
def AtU (s₀ : State) (k : Nat) (s : State) : Prop :=
  Core s₀ k s ∧ bytesAt s.mem (sc s₀ + BitVec.ofNat 64 1088) 32 = u1 s₀ k

theorem S_length (s₀ : State) : (S s₀).length = sl s₀ := Proof.Hmac.X86_64.bytesAt_length _ _ _

theorem int_length (i : Nat) : (Spec.Pbkdf2.int i).length = 4 := rfl

theorem xorPad_k0_length (s₀ : State) (p : Byte) : (xorPad (k0 s₀) p).length = 64 := by
  simp [xorPad, k0, blockKey_length]

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem bu2_ok {nm : String} {k : Nat} {s : State} (h : BU1 s₀ k s) :
    WP isa (.call nm Impl.Sha256.AArch64.Stream.update) s (BU2 s₀ k) := by
  obtain ⟨c, hS, hI, h0, h1, h2, h3, h4⟩ := h
  refine update_call c.regs.base.sp hp.sp16 h0 h2 (n := 4) (by rw [h3]; rfl) h4 (by dj) (by dj) (by dj)
    (by dj) (by dj) (by dj) (by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov)
    (by rw [c.regs.base.wr, hp.wr]; cov) hS
    (by rw [h1, List.length_append, xorPad_k0_length, S_length]) fun s' rd wr sp cs hf hr' => ?_
  have k' := c.regs.call hp rd wr sp cs (hf.sub (by fwk))
  refine ⟨c.frame k' hf (by cdj) (by cdj), ?_⟩
  rwa [hI, List.append_assoc] at hr'

omit hp in
theorem bu3_ok {k : Nat} {s : State} (h : BU2 s₀ k s) :
    WP isa (.block [.addImm .x .x0 .x19 288, .addImm .x .x1 .x19 96, .addImm .x .x2 .x23 4,
      .addImm .x .x3 .x19 912]) s (BU3 s₀ k) := by
  obtain ⟨c, hS⟩ := h
  refine wp_run' rfl fun s' hg hm rd wr sp =>
    ⟨⟨c.regs' (c.regs.regs rd wr sp hm (by cs_keep hg)) hm, hm ▸ hS⟩, ?_, ?_, ?_, ?_⟩ <;>
    rw [hg] <;> simp [upd, c.regs.base.x19, c.regs.x23]
  rw [← BitVec.ofNat_add, Nat.add_assoc]

theorem bu4_ok {nm : String} {k : Nat} {s : State} (h : BU3 s₀ k s) :
    WP isa (.call nm Impl.Hmac.AArch64.finalize) s (AtU s₀ k) := by
  obtain ⟨⟨c, hS⟩, h0, h1, h2, h3⟩ := h
  refine hfin_call c.regs.base.sp hp.sp32 h0 h1 h3 (by dj) (by dj) (by dj) (by dj) (by dj) (by dj)
    (by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov) (by rw [c.regs.base.wr, hp.wr]; cov)
    (blockKey_length _) hS c.key.2 (by rw [h2, List.length_append, S_length, int_length])
    fun s' rd wr sp cs hf hu => ?_
  have k' := c.regs.call hp rd wr sp cs (hf.sub (by fwk))
  refine ⟨c.frame k' hf (by cdj) (by cdj), ?_⟩
  rw [show sc s₀ + BitVec.ofNat 64 912 + 176 = sc s₀ + BitVec.ofNat 64 1088 by
    rw [BitVec.add_assoc]; rfl] at hu
  exact hu

theorem bu_ok {k : Nat} {s : State} (h : Core s₀ k s) : WP isa blockU s (AtU s₀ k) := by
  unfold blockU
  exact WP.seq (WP.mono (bu1_ok hp h) fun _ h₁ => WP.seq (WP.mono (bu2_ok hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (bu3_ok h₂) fun _ h₃ => bu4_ok hp h₃)))

end

/-! ## `T` -/

def BT1 (s₀ : State) (k : Nat) (s : State) : Prop :=
  Core s₀ k s ∧ bytesAt s.mem (sc s₀ + BitVec.ofNat 64 1088) 32 = u1 s₀ k ∧
  bytesAt s.mem (sc s₀ + BitVec.ofNat 64 384) 32 = u1 s₀ k ∧
  s.gpr .x0 = sc s₀ + BitVec.ofNat 64 0 ∧ s.gpr .x1 = sc s₀ + BitVec.ofNat 64 1088 ∧
  ((s.gpr .x2).setWidth 32).toNat = cc s₀ - 1 ∧ s.gpr .x3 = sc s₀ + BitVec.ofNat 64 384 ∧
  s.gpr .x4 = sc s₀ + BitVec.ofNat 64 528

/-- After `blockT`. -/
def AtT (s₀ : State) (k : Nat) (s : State) : Prop :=
  Core s₀ k s ∧ bytesAt s.mem (sc s₀ + BitVec.ofNat 64 384) 32 = Fk s₀ k

theorem Fk_eq (s₀ : State) (k : Nat) :
    Fk s₀ k = Spec.Pbkdf2.iterate (hmacBlockKey sha256 (k0 s₀)) (cc s₀ - 1) (u1 s₀ k) (u1 s₀ k) := rfl

theorem cc_lt (s₀ : State) : cc s₀ < 2 ^ 32 := BitVec.isLt _

theorem add96 (a : Addr) : a + BitVec.ofNat 64 0 + 96 = a + BitVec.ofNat 64 96 := by
  rw [BitVec.add_assoc]; rfl

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem bt1_ok {k : Nat} {s : State} (h : AtU s₀ k s) :
    WP isa (.block ((List.range 4).flatMap (Impl.Hmac.AArch64.cp64 .x19 .x19 1088 384) ++
      [mov .x0 .x19, .addImm .x .x1 .x19 1088, mov .x2 .x22, .addImm .x .x3 .x19 384,
        .addImm .x .x4 .x19 528])) s (BT1 s₀ k) := by
  obtain ⟨c, hu⟩ := h
  have kr := c.regs
  refine sc_copy hp kr.base.x19 kr.base.wr (o₁ := 1088) (o₂ := 384) (n := 4) (by omega) (by omega) (by omega)
    (by decide) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  have f₁ : Frame [sR s₀ 384 32] s.mem s₁.mem := by rw [m₁]; exact copy_frame _ _ _ _
  have k₁ : KpL s₀ s₁ k := kr.call hp rd₁ wr₁ sp₁ (fun r hr _ => g₁ r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    (f₁.sub (by fwk))
  have c₁ : Core s₀ k s₁ := c.frame k₁ f₁ (by cdj) (by cdj)
  have hu₁ : bytesAt s₁.mem (sc s₀ + BitVec.ofNat 64 1088) 32 = u1 s₀ k := by
    rw [← hu]; exact frame_bytesAt f₁ (by cdj) (by omega)
  have ht₁ : bytesAt s₁.mem (sc s₀ + BitVec.ofNat 64 384) 32 = u1 s₀ k := by
    rw [m₁, show 8 * 4 = 32 from rfl, copy_bytes _ _ _ _ (by omega)]; exact hu
  have hcc := cc_lt s₀
  refine wp_run' rfl fun s' hg hm rd wr sp =>
    ⟨c₁.regs' (k₁.regs rd wr sp hm (by cs_keep hg)) hm, hm ▸ hu₁, hm ▸ ht₁, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg]; simp [upd, k₁.base.x19]
  · rw [hg]; simp [upd, k₁.base.x19]
  · rw [hg]; simp [upd, k₁.x22]; omega
  · rw [hg]; simp [upd, k₁.base.x19]
  · rw [hg]; simp [upd, k₁.base.x19]

theorem bt2_ok {nm : String} {k : Nat} {s : State} (h : BT1 s₀ k s) :
    WP isa (.call nm Impl.Pbkdf2.AArch64.iterate) s (AtT s₀ k) := by
  obtain ⟨c, hu, ht, h0, h1, h2, h3, h4⟩ := h
  refine iter_call c.regs.base.sp h0 h1 h3 h4 (by dj) (by dj) (by dj) (by dj) (by dj)
    (by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov)
    (by rw [c.regs.base.wr, hp.wr]; cov) (blockKey_length _) c.key.1 (by rw [add96]; exact c.key.2)
    fun s' rd wr sp cs hf hT => ?_
  have k' := c.regs.call hp rd wr sp cs (hf.sub (by fwk))
  refine ⟨c.frame k' hf (by cdj) (by cdj), ?_⟩
  rw [hT, h2, hu, ht, Fk_eq]

theorem bt_ok {k : Nat} {s : State} (h : AtU s₀ k s) : WP isa blockT s (AtT s₀ k) := by
  unfold blockT
  exact WP.seq (WP.mono (bt1_ok hp h) fun _ h₁ => bt2_ok hp h₁)

end

end VG.Proof.Pbkdf2.AArch64Derive
