import VerifiedGarbage.Proof.Argon2.X86_64.DeriveRegions
import VerifiedGarbage.Proof.Argon2.X86_64.InitialBody

/-! Exact words consumed by hashing, initialization, filling, and finalization. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64
open VG.Proof.Argon2.X86_64.Initial (wordAt)

theorem params_variant_code (kind passes memory lanes tagLen : Nat) (bound : kind ≤ 2) :
    (Spec.Argon2.params kind passes memory lanes tagLen).variant.code = kind := by
  by_cases zero : kind = 0
  · subst kind; rfl
  · by_cases one : kind = 1
    · subst kind; rfl
    · have two : kind = 2 := by omega
      subst kind; rfl

structure DeriveWords (s t : State) : Prop where
  passes : wordAt t 72 = BitVec.ofNat 64 (abiParams s).passes
  saltLength : wordAt t 80 = s.gpr .r8
  salt : wordAt t 88 = s.gpr .rcx
  passwordLength : wordAt t 96 = s.gpr .rdx
  password : wordAt t 104 = s.gpr .rsi
  kind : wordAt t 112 = BitVec.ofNat 64 (abiParams s).variant.code
  memory : wordAt t 176 = BitVec.ofNat 64 (abiParams s).memory
  lanes : wordAt t 184 = BitVec.ofNat 64 (abiParams s).lanes
  secret : wordAt t 200 = abiWord s 32
  secretLength : wordAt t 208 = abiWord s 40
  ad : wordAt t 216 = abiWord s 48
  adLength : wordAt t 224 = abiWord s 56
  matrix : wordAt t 232 = abiWord s 64
  blocks : wordAt t 240 = BitVec.ofNat 64 (abiParams s).blocks
  work : wordAt t 248 = abiWord s 80
  output : wordAt t 256 = abiWord s 88
  tagLength : wordAt t 264 = BitVec.ofNat 64 (abiParams s).tagLen

theorem private_words {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : DeriveWords s t := by
  have parameters := private_parameters h prepared
  refine ⟨?_, private_argument_word prepared (80, .r8) (by decide),
    private_argument_word prepared (88, .rcx) (by decide),
    private_argument_word prepared (96, .rdx) (by decide),
    private_argument_word prepared (104, .rsi) (by decide), ?_, parameters.memoryWord, parameters.lanesWord,
    private_stack_word h prepared 3 (by decide), private_stack_word h prepared 4 (by decide),
    private_stack_word h prepared 5 (by decide), private_stack_word h prepared 6 (by decide),
    private_stack_word h prepared 7 (by decide), ?_, private_stack_word h prepared 9 (by decide),
    private_stack_word h prepared 10 (by decide), ?_⟩
  · have word := private_argument_word prepared (72, .r9) (by decide)
    change wordAt t 72 = ((s.gpr .r9).setWidth 32).setWidth 64 at word
    change wordAt t 72 = BitVec.ofNat 64 ((s.gpr .r9).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]
  · have code := params_variant_code ((s.gpr .rdi).setWidth 32).toNat
      (abiParams s).passes (abiParams s).memory (abiParams s).lanes (abiParams s).tagLen h.kind
    change (abiParams s).variant.code = ((s.gpr .rdi).setWidth 32).toNat at code
    rw [code]
    have word := private_argument_word prepared (112, .rdi) (by decide)
    change wordAt t 112 = ((s.gpr .rdi).setWidth 32).setWidth 64 at word
    rw [word, BitVec.ofNat_toNat]
  · have word := private_stack_word h prepared 8 (by decide)
    change wordAt t 240 = abiWord s 72 at word
    rw [word, ← h.blocks, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have word := private_stack_word h prepared 11 (by decide)
    change wordAt t 264 = abiWord s 96 at word
    change wordAt t 264 = BitVec.ofNat 64 (abiWord s 96).toNat
    rw [word, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end VG.Proof.Argon2.X86_64.Derive
