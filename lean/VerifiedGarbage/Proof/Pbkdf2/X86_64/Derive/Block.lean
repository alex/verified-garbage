import VerifiedGarbage.Proof.Pbkdf2.X86_64.Derive.Key

/-!
# PBKDF2-HMAC-SHA-256 on x86-64: one block's `U₁` and `T`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Pbkdf2.X86_64.Derive

open VG VG.X86_64 VG.Impl.Pbkdf2.X86_64
open VG.Impl.Sha256.X86_64 (at_)
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey sha256)
open VG.Proof.Sha256.X86_64 (contains_offset toNat_ofNat_lt ea_at ofInt_natCast)
open VG.Proof.Sha256.X86_64.Stream (wp_store32)
open VG.X86_64.RegBlock (upd wp_run wp_run')
open VG.Impl.Sha256.X86_64.Stream (Callee)

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
    have : ol s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
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

theorem wordBytes_int {i : Nat} (h : i < 2 ^ 32) :
    Spec.Sha256.wordBytes (BitVec.ofNat 32 i) = Spec.Pbkdf2.int i := by
  simp only [Spec.Sha256.wordBytes, Spec.Pbkdf2.int, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] <;> omega

theorem int_bytes (m : Mem) (a : Addr) {i : Nat} (h : i < 2 ^ 32) :
    bytesAt (m.writeW a (bswap32 (BitVec.ofNat 32 i))) a 4 = Spec.Pbkdf2.int i := by
  rw [Proof.Sha256.X86_64.Stream.Finalize.writeW_bswap32, ← wordBytes_int h]
  exact Proof.Hmac.X86_64.bytesAt_writeBytes_self _ _ _ (by simp [Spec.Sha256.wordBytes])

theorem rax_eq (x : BitVec 64) :
    ((bswap32 (((x.setWidth 32).setWidth 64).setWidth 32)).setWidth 64).setWidth 32 = bswap32 (x.setWidth 32) := by
  simp [BitVec.setWidth_setWidth_of_le]

theorem setWidth_ofNat32 (n : Nat) : (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-! ## `U₁` -/

theorem Pre.k_lt {s₀ : State} (hp : Pre s₀) {k : Nat} {s : State} (h : Core s₀ k s) : k + 1 < 2 ^ 32 := by
  have := h.lt; have := hp.len; omega

def BU1 (s₀ : State) (k : Nat) (s : State) : Prop :=
  Core s₀ k s ∧ Repr s.mem (sc s₀ + BitVec.ofNat 64 288) (xorPad (k0 s₀) ipad ++ S s₀) ∧
  bytesAt s.mem (sc s₀ + BitVec.ofNat 64 416) 4 = Spec.Pbkdf2.int (k + 1) ∧
  s.gpr .rdi = sc s₀ + BitVec.ofNat 64 288 ∧ s.gpr .rsi = BitVec.ofNat 64 (64 + sl s₀) ∧
  s.gpr .rdx = sc s₀ + BitVec.ofNat 64 416 ∧ s.gpr .rcx = BitVec.ofNat 64 4 ∧
  s.gpr .r8 = sc s₀ + BitVec.ofNat 64 512

section
variable {s₀ : State} (hp : Pre s₀) {f : Callee} (hv : Vf f)
include hp

theorem bu1_ok {k : Nat} {s : State} (h : Core s₀ k s) :
    WP isa (.block ((List.range 12).flatMap (Impl.Hmac.X86_64.cp64 .rbx .rbx 192 288) ++
      [.mov32 .rax (.reg .r12), .bswap32 .rax, .store32 (at_ .rbx 416) .rax] ++ ptr .rdi .rbx 288 ++
      [.mov .rsi (.reg .r15)] ++ ptr .rdx .rbx 416 ++ [.mov32 .rcx (.imm 4)] ++ ptr .r8 .rbx 512)) s
      (BU1 s₀ k) := by
  have kr := h.regs
  simp only [ptr, List.append_assoc, List.cons_append, List.nil_append]
  refine sc_copy hp kr.base.rbx kr.base.wr (o₁ := 192) (o₂ := 288) (n := 12) (by omega) (by omega) (by omega)
    fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  have f₁ : Frame [sR s₀ 288 96] s.mem s₁.mem := by rw [m₁]; exact copy_frame _ _ _ _
  have k₁ : KpL s₀ s₁ k := kr.call hp rd₁ wr₁ (fun r hr => g₁ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) (f₁.sub (by fwk))
  have c₁ : Core s₀ k s₁ := h.frame k₁ f₁ (by cdj) (by cdj)
  have hS : Repr s₁.mem (sc s₀ + BitVec.ofNat 64 288) (xorPad (k0 s₀) ipad ++ S s₀) := by
    refine repr_of_bytes ?_ h.salt
    rw [m₁, show 8 * 12 = 96 from rfl, copy_bytes _ _ _ _ (by omega)]
  refine wp_run (is := [.mov32 .rax (.reg .r12), .bswap32 .rax]) rfl fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  have k₂ : KpL s₀ s₂ k := k₁.regs rd₂ wr₂ m₂ (by cs_keep g₂)
  have rbx₂ : s₂.gpr .rbx = sc s₀ := k₂.base.rbx
  have ax : (s₂.gpr .rax).setWidth 32 = bswap32 (BitVec.ofNat 32 (k + 1)) := by
    rw [g₂]; simp only [upd, ite_true]; rw [rax_eq, k₁.r12, setWidth_ofNat32]
  refine wp_store32 (a := sc s₀ + BitVec.ofNat 64 416) (ea_sc rbx₂ _)
    (hp.in_sc (wr₂.trans k₁.base.wr) (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  have f₃ : Frame [sR s₀ 416 4] s₂.mem s₃.mem := by
    rw [m₃]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sR s₀ (w := 32 / 8) le_rfl le_rfl (by omega))
  have k₃ : KpL s₀ s₃ k := k₂.call hp rd₃ wr₃ (fun r _ => by rw [g₃]) (f₃.sub (by fwk))
  have c₃ : Core s₀ k s₃ := (c₁.regs' k₂ m₂).frame k₃ f₃ (by cdj) (by cdj)
  have hI : bytesAt s₃.mem (sc s₀ + BitVec.ofNat 64 416) 4 = Spec.Pbkdf2.int (k + 1) := by
    rw [m₃, ax]; exact int_bytes _ _ (hp.k_lt h)
  have hS₃ : Repr s₃.mem (sc s₀ + BitVec.ofNat 64 288) (xorPad (k0 s₀) ipad ++ S s₀) :=
    repr_frame f₃ (by cdj) (m₂ ▸ hS)
  refine wp_run' rfl fun s' hg hm rd wr =>
    ⟨c₃.regs' (k₃.regs rd wr hm (by cs_keep hg)) hm, hm ▸ hS₃, hm ▸ hI, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hg] <;> simp [upd, k₃.base.rbx, k₃.r15, se_ofNat]

end

def BU2 (s₀ : State) (k : Nat) (s : State) : Prop :=
  Core s₀ k s ∧ Repr s.mem (sc s₀ + BitVec.ofNat 64 288) (xorPad (k0 s₀) ipad ++ (S s₀ ++ Spec.Pbkdf2.int (k + 1)))

def BU3 (s₀ : State) (k : Nat) (s : State) : Prop :=
  BU2 s₀ k s ∧ s.gpr .rdi = sc s₀ + BitVec.ofNat 64 288 ∧ s.gpr .rsi = sc s₀ + BitVec.ofNat 64 96 ∧
  s.gpr .rdx = BitVec.ofNat 64 (64 + (sl s₀ + 4)) ∧ s.gpr .rcx = sc s₀ + BitVec.ofNat 64 896

/-- After `blockU`. -/
def AtU (s₀ : State) (k : Nat) (s : State) : Prop :=
  Core s₀ k s ∧ bytesAt s.mem (sc s₀ + BitVec.ofNat 64 1072) 32 = u1 s₀ k

theorem S_length (s₀ : State) : (S s₀).length = sl s₀ := Proof.Hmac.X86_64.bytesAt_length _ _ _

theorem int_length (i : Nat) : (Spec.Pbkdf2.int i).length = 4 := rfl

theorem xorPad_k0_length (s₀ : State) (p : Byte) : (xorPad (k0 s₀) p).length = 64 := by
  simp [xorPad, k0, blockKey_length]

section
variable {s₀ : State} (hp : Pre s₀) {f : Callee} (hv : Vf f)
include hp

include hv in
theorem bu2_ok {nm : String} {k : Nat} {s : State} (h : BU1 s₀ k s) :
    WP isa (.call nm (Impl.Sha256.X86_64.Stream.update f)) s (BU2 s₀ k) := by
  obtain ⟨c, hS, hI, h1, h2, h3, h4, h5⟩ := h
  have hsp := c.regs.base.rsp
  refine update_call hv h1 h3 (n := 4) (by rw [h4]; rfl) h5 (by dj) (by dj) (by dj) (by rw [hsp]; dj)
    (by rw [hsp]; dj) (by rw [hsp]; dj) (by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov)
    (by rw [c.regs.base.wr, hp.wr]; cov) hS
    (by rw [h2, List.length_append, xorPad_k0_length, S_length]) fun s' rd wr cs hf hr' => ?_
  have k' := c.regs.call hp rd wr cs (hf.sub (by fwk))
  rw [hsp] at hf
  refine ⟨c.frame k' hf (by cdj) (by cdj), ?_⟩
  rwa [hI, List.append_assoc] at hr'

omit hp in
theorem bu3_ok {k : Nat} {s : State} (h : BU2 s₀ k s) :
    WP isa (.block (ptr .rdi .rbx 288 ++ ptr .rsi .rbx 96 ++ ptr .rdx .r15 4 ++ ptr .rcx .rbx 896)) s
      (BU3 s₀ k) := by
  obtain ⟨c, hS⟩ := h
  refine wp_run' rfl fun s' hg hm rd wr =>
    ⟨⟨c.regs' (c.regs.regs rd wr hm (by cs_keep hg)) hm, hm ▸ hS⟩, ?_, ?_, ?_, ?_⟩ <;>
    rw [hg] <;> simp [upd, c.regs.base.rbx, c.regs.r15, se_ofNat]
  rw [← BitVec.ofNat_add, Nat.add_assoc]

include hv in
theorem bu4_ok {nm name : String} {k : Nat} {s : State} (h : BU3 s₀ k s) :
    WP isa (.call nm (Impl.Hmac.X86_64.finalize f name)) s (AtU s₀ k) := by
  obtain ⟨⟨c, hS⟩, h1, h2, h3, h4⟩ := h
  have hsp := c.regs.base.rsp
  refine hfin_call hv name h1 h2 h4 (by dj) (by dj) (by dj) (by rw [hsp]; dj) (by rw [hsp]; dj) (by rw [hsp]; dj)
    (by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov) (by rw [c.regs.base.wr, hp.wr]; cov)
    (blockKey_length _) hS c.key.2 (by rw [h3, List.length_append, S_length, int_length])
    fun s' rd wr cs hf hu => ?_
  have k' := c.regs.call hp rd wr cs (hf.sub (by fwk))
  rw [hsp] at hf
  refine ⟨c.frame k' hf (by cdj) (by cdj), ?_⟩
  rw [show sc s₀ + BitVec.ofNat 64 896 + 176 = sc s₀ + BitVec.ofNat 64 1072 by
    rw [BitVec.add_assoc]; rfl] at hu
  exact hu

include hv in
theorem bu_ok (sfx : String) {k : Nat} {s : State} (h : Core s₀ k s) : WP isa (blockU f sfx) s (AtU s₀ k) := by
  unfold blockU
  exact WP.seq (WP.mono (bu1_ok hp h) fun _ h₁ => WP.seq (WP.mono (bu2_ok hp hv h₁) fun _ h₂ =>
    WP.seq (WP.mono (bu3_ok h₂) fun _ h₃ => bu4_ok hp hv h₃)))

end

/-! ## `T` -/

def BT1 (s₀ : State) (k : Nat) (s : State) : Prop :=
  Core s₀ k s ∧ bytesAt s.mem (sc s₀ + BitVec.ofNat 64 1072) 32 = u1 s₀ k ∧
  bytesAt s.mem (sc s₀ + BitVec.ofNat 64 384) 32 = u1 s₀ k ∧
  s.gpr .rdi = sc s₀ + BitVec.ofNat 64 0 ∧ s.gpr .rsi = sc s₀ + BitVec.ofNat 64 1072 ∧
  ((s.gpr .rdx).setWidth 32).toNat = cc s₀ - 1 ∧ s.gpr .rcx = sc s₀ + BitVec.ofNat 64 384 ∧
  s.gpr .r8 = sc s₀ + BitVec.ofNat 64 512

/-- After `blockT`. -/
def AtT (s₀ : State) (k : Nat) (s : State) : Prop :=
  Core s₀ k s ∧ bytesAt s.mem (sc s₀ + BitVec.ofNat 64 384) 32 = Fk s₀ k

theorem Fk_eq (s₀ : State) (k : Nat) :
    Fk s₀ k = Spec.Pbkdf2.iterate (hmacBlockKey sha256 (k0 s₀)) (cc s₀ - 1) (u1 s₀ k) (u1 s₀ k) := rfl

theorem cc_lt (s₀ : State) : cc s₀ < 2 ^ 32 := BitVec.isLt _

theorem add96 (a : Addr) : a + BitVec.ofNat 64 0 + 96 = a + BitVec.ofNat 64 96 := by
  rw [BitVec.add_assoc]; rfl

section
variable {s₀ : State} (hp : Pre s₀) {f : Callee} (hv : Vf f)
include hp

theorem bt1_ok {k : Nat} {s : State} (h : AtU s₀ k s) :
    WP isa (.block ((List.range 4).flatMap (Impl.Hmac.X86_64.cp64 .rbx .rbx 1072 384) ++ [.mov .rdi (.reg .rbx)] ++
      ptr .rsi .rbx 1072 ++ [.mov32 .rdx (.reg .r14)] ++ ptr .rcx .rbx 384 ++ ptr .r8 .rbx 512)) s (BT1 s₀ k) := by
  obtain ⟨c, hu⟩ := h
  have kr := c.regs
  simp only [ptr, List.append_assoc, List.cons_append, List.nil_append]
  refine sc_copy hp kr.base.rbx kr.base.wr (o₁ := 1072) (o₂ := 384) (n := 4) (by omega) (by omega) (by omega)
    fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  have f₁ : Frame [sR s₀ 384 32] s.mem s₁.mem := by rw [m₁]; exact copy_frame _ _ _ _
  have k₁ : KpL s₀ s₁ k := kr.call hp rd₁ wr₁ (fun r hr => g₁ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) (f₁.sub (by fwk))
  have c₁ : Core s₀ k s₁ := c.frame k₁ f₁ (by cdj) (by cdj)
  have hu₁ : bytesAt s₁.mem (sc s₀ + BitVec.ofNat 64 1072) 32 = u1 s₀ k := by
    rw [← hu]; exact frame_bytesAt f₁ (by cdj) (by omega)
  have ht₁ : bytesAt s₁.mem (sc s₀ + BitVec.ofNat 64 384) 32 = u1 s₀ k := by
    rw [m₁, show 8 * 4 = 32 from rfl, copy_bytes _ _ _ _ (by omega)]; exact hu
  have hcc := cc_lt s₀
  refine wp_run' rfl fun s' hg hm rd wr =>
    ⟨c₁.regs' (k₁.regs rd wr hm (by cs_keep hg)) hm, hm ▸ hu₁, hm ▸ ht₁, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg]; simp [upd, k₁.base.rbx]
  · rw [hg]; simp [upd, k₁.base.rbx, se_ofNat]
  · rw [hg]; simp [upd, k₁.r14]; omega
  · rw [hg]; simp [upd, k₁.base.rbx, se_ofNat]
  · rw [hg]; simp [upd, k₁.base.rbx, se_ofNat]

include hv in
theorem bt2_ok {nm : String} {k : Nat} {s : State} (h : BT1 s₀ k s) :
    WP isa (.call nm (iterate f)) s (AtT s₀ k) := by
  obtain ⟨c, hu, ht, h1, h2, h3, h4, h5⟩ := h
  have hsp := c.regs.base.rsp
  refine iter_call hv h1 h2 h4 h5 (by dj) (by dj) (by dj) (by dj) (by dj) (by rw [hsp]; dj) (by rw [hsp]; dj)
    (by rw [hsp]; dj) (by rw [hsp]; dj) (by rw [c.regs.base.rd, c.regs.base.wr, hp.rd, hp.wr]; cov)
    (by rw [c.regs.base.wr, hp.wr]; cov) (blockKey_length _) c.key.1 (by rw [add96]; exact c.key.2)
    (by rw [hsp, add96]; dj) fun s' rd wr cs hf hT => ?_
  have k' := c.regs.call hp rd wr cs (hf.sub (by fwk))
  rw [hsp] at hf
  refine ⟨c.frame k' hf (by cdj) (by cdj), ?_⟩
  rw [hT, h3, hu, ht, Fk_eq]

include hv in
theorem bt_ok (sfx : String) {k : Nat} {s : State} (h : AtU s₀ k s) : WP isa (blockT f sfx) s (AtT s₀ k) := by
  unfold blockT
  exact WP.seq (WP.mono (bt1_ok hp h) fun _ h₁ => bt2_ok hp hv h₁)

end

end VG.Proof.Pbkdf2.X86_64.Derive
