import VerifiedGarbage.Proof.Pbkdf2.X86.Common

/-!
# PBKDF2-HMAC-SHA-256's iteration on x86 (32-bit): the loop

Untrusted: everything here is checked by Lean. One step is HMAC-SHA-256 of
`U` as two compressions (`VG.Proof.Pbkdf2.hmac_step`), then `T ← T ⊕ U`.
-/

namespace VG.Proof.Pbkdf2.X86

open VG VG.X86 VG.Impl.Pbkdf2.X86
open VG.Impl.Sha256.X86.Stream (saved)
open VG.Proof.Sha256.X86.Stream (wp_subi eval_e eval_ne ofNat_beq_zero sub_ofNat)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base blockAt_eq xorBytes_length add_ofNat digest_self)
open VG.Spec.Sha256 (bytesAt stateAt blockAt compress HashValue)

section
variable (s₀ : State)

/-- The key's inner and outer hash values. -/
abbrev Hi : HashValue := stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 0)
abbrev Ho : HashValue := stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 96)

/-- A step, as the code computes it. -/
def stepM (u : List Byte) : List Byte :=
  Pbkdf2.digest (compress (Ho s₀) (block96 (Pbkdf2.digest (compress (Hi s₀) (block96 u)))))

/-- Our caller's registers, saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

/-- What the body writes: `t`, the compression's part of the scratch space,
the stack below `esp`, `T` and the block's first 32 bytes. -/
abbrev bodyR : List Region := [tR s₀, cmpR s₀, stkR s₀, sR s₀ 160 32, sR s₀ 192 32]

end

/-- Parts of the scratch space that the body leaves: the saved registers
(`[112..128)`) and the padding (from 224). -/
theorem body_disj {s₀ : State} (hp : Pre s₀) {o n : Nat} (h₁ : (112 ≤ o ∧ o + n ≤ 128) ∨ 224 ≤ o)
    (h₂ : o + n ≤ 256) : ∀ r ∈ bodyR s₀, Region.Disjoint (sR s₀ o n) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hp.t_s.sub_right (scr_sub s₀ h₂)).symm
  · exact scr_disj0 s₀ (by omega) h₂
  · exact (hp.stk_s.sub_right (scr_sub s₀ h₂)).symm
  · exact scr_disj s₀ (b := 160) (n := 32) (by omega) h₂ (by omega)
  · exact scr_disj s₀ (b := 192) (n := 32) (by omega) h₂ (by omega)

/-- The block's first 32 bytes are neither `t`, the compression's scratch
nor the stack. -/
theorem blk_disj {s₀ : State} (hp : Pre s₀) :
    ∀ r ∈ [tR s₀, cmpR s₀, stkR s₀], Region.Disjoint (sR s₀ 192 32) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.t_s.sub_right (scr_sub s₀ (by omega))).symm
  · exact scr_disj0 s₀ (by omega) (by omega)
  · exact (hp.stk_s.sub_right (scr_sub s₀ (by omega))).symm

/-- `T` is none of the other parts the body writes. -/
theorem T_disj {s₀ : State} (hp : Pre s₀) :
    ∀ r ∈ [tR s₀, cmpR s₀, stkR s₀, sR s₀ 192 32], Region.Disjoint (sR s₀ 160 32) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.t_s.sub_right (scr_sub s₀ (by omega))).symm
  · exact scr_disj0 s₀ (by omega) (by omega)
  · exact (hp.stk_s.sub_right (scr_sub s₀ (by omega))).symm
  · exact scr_disj s₀ (by omega) (by omega) (by omega)

theorem saved_off {p : Reg × Nat} (hp : p ∈ saved) : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp

theorem Saved.frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m) (hf : Frame (bodyR s₀) m m') :
    Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  have hd := saved_off hp'
  exact hf.readW (r := sR s₀ p.2 4) (Region.contains_self _ _) (body_disj hp (.inl hd) (by omega)) (by decide)

theorem frame_body {s₀ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, r ∈ bodyR s₀) :
    Frame (bodyR s₀) m m' := hf.mono hs

/-- The loop invariant, with `r` steps left. -/
structure Inv (s₀ : State) (r : Nat) (s : State) : Prop extends Regs s₀ s where
  edi : s.gpr .edi = BitVec.ofNat 32 r
  saved : Saved s₀ s.mem
  pad : bytesAt s.mem (scA s₀ + BitVec.ofNat 64 224) 32 = pad96
  le : r ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM s₀) (nn s₀) (bytesAt s₀.mem (uA s₀) 32) (bytesAt s₀.mem (tA s₀) 32) =
    Spec.Pbkdf2.iterate (stepM s₀) r (bytesAt s.mem (blkA s₀) 32) (bytesAt s.mem (TA s₀) 32)

end VG.Proof.Pbkdf2.X86
