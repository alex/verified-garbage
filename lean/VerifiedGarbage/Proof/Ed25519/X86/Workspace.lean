import VerifiedGarbage.Proof.X25519.X86.Freeze

/-!
# Ed25519 on x86 (32-bit): the field arithmetic

Ed25519's field operations are X25519's code (`Impl.X25519.X86`), so their
proofs are X25519's, for Ed25519's working space of 8192 bytes, whose slots
start at offset 64.
-/

namespace VG.Proof.Ed25519.X86

/-- The code's view of the working space of 8192 bytes. -/
abbrev Ctx (x : BitVec 32) (s : VG.X86.State) : Prop := X25519.X86.Ctx 8192 x s

export VG.Proof.X25519.X86 (v wd wv num fe sub scR addr_zero sub_contains sub_disj scR_eq scR_contains
  wd_write_ne wd_write_self wd_frame wd_frame1 frame_write1 sub_sub frameWiden Keep Keep.refl num_succ
  num_congr num_add num_mul fe_lt fe_frame fe_frame1 acc tval treads colv toNat_zero32 updKeep cols_ok
  wp_mul prod_identity num_16 colv_le_len wv_lt wv_mul_le zeroAcc_ok Below F isSlot slot_below slot_ne
  frame_wide mask cswap_ok opOut opIns opValid opVal run op_ok shr31_toNat low31_toNat setAcc_ok
  selects_ok fold_top colv_addM freeze_ok)

end VG.Proof.Ed25519.X86
