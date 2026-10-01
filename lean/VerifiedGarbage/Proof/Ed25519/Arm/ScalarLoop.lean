import VerifiedGarbage.Proof.Ed25519.Arm.ScalarByte
import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
import VerifiedGarbage.Spec.Ed25519.Contract

/-! The fixed 64-byte reduction loop, with an exact suffix invariant. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed25519 (L bytesAt decodeLE)

theorem scalar_bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

theorem scalar_suffix_step (m : Mem) (p : Addr) (n : Nat) (hn : n < 64) :
    decodeLE ((bytesAt m p 64).drop n) % L =
      (256 * (decodeLE ((bytesAt m p 64).drop (n + 1)) % L) +
        (m (p + BitVec.ofNat 64 n)).toNat) % L := by
  rw [List.drop_eq_getElem_cons (by rw [scalar_bytesAt_length]; exact hn), reduce_cons]
  simp only [bytesAt, List.getElem_map, List.getElem_range]

structure ScalarInv (b : BitVec 32) (p : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 64
  counter : s.gpr .r10 = BitVec.ofNat 32 n
  limbs : Lim s.mem (State.addr b) SR
  value : V s.mem (State.addr b) SR = decodeLE ((bytesAt s0.mem p 64).drop n) % L
  keeps : ScalarBodyKeep b s0 s

theorem scalarLoop_ok {b p : BitVec 32} {s0 : State} (hc : Ctx b s0)
    (hp : s0.gpr .r12 = p) (hfit : p.toNat + 64 ≤ 2 ^ 32)
    (hread : ∀ n < 64, InRegions (s0.rd ++ s0.wr) (State.addr p + BitVec.ofNat 64 n) 1)
    (hsep : ∀ r ∈ scalarRegions b, (⟨State.addr p, 64⟩ : Region).Disjoint r)
    (h10 : s0.gpr .r10 = 64) (hl : Lim s0.mem (State.addr b) SR)
    (hz : V s0.mem (State.addr b) SR = 0) :
    WP isa (.loop (.block scalarByte) .ne) s0 fun t => ScalarBodyKeep b s0 t ∧
      Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR = decodeLE (bytesAt s0.mem (State.addr p) 64) % L := by
  apply WP.loop (ScalarInv b (State.addr p) s0) (n := 64)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 64 := by have := hi.bound; omega
    have hps : s.gpr .r12 = p := (hi.keeps.rest.gpr _ (by decide)).trans hp
    have hrs : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 k) 1 := by
      rw [hi.keeps.rest.rd, hi.keeps.rest.wr]; exact hread k hk
    refine WP.mono (scalarByte_ok (hi.keeps.ctx hc) hk hps hfit hi.counter hrs hi.limbs
      (by rw [hi.value]; exact Nat.mod_lt _ order_pos)) fun t ⟨kt, lt, vt, et, zt⟩ => ?_
    have km := hi.keeps.trans kt
    have mb : s.mem (State.addr p + BitVec.ofNat 64 k) = s0.mem (State.addr p + BitVec.ofNat 64 k) :=
      hi.keeps.frame.bytes hsep (by decide : 64 ≤ 2 ^ 64) hk
    have val : V t.mem (State.addr b) SR = decodeLE ((bytesAt s0.mem (State.addr p) 64).drop k) % L := by
      rw [vt, hi.value, mb, scalar_suffix_step _ _ _ hk]
    by_cases hk0 : k = 0
    · subst hk0
      refine .inl ⟨by rw [eval_ne, zt]; rfl, km, lt, ?_⟩
      simpa only [List.drop_zero] using val
    · refine .inr ⟨by rw [eval_ne, zt]; simp only [hk0, decide_false, Bool.not_false],
        k, by omega, ?_⟩
      exact ⟨by omega, by omega, et, lt, val, km⟩
  · refine ⟨by decide, by decide, h10, hl, ?_, ⟨Rest.refl _ _, Frame.refl _ _⟩⟩
    rw [hz, List.drop_eq_nil_of_le (by rw [scalar_bytesAt_length])]
    rfl

theorem scalarInit_ok {b : BitVec 32} {s : State} (hc : Ctx b s) :
    WP isa (.block scalarInit) s fun t => ScalarBodyKeep b s t ∧
      t.gpr .r10 = 64 ∧ Lim t.mem (State.addr b) SR ∧ V t.mem (State.addr b) SR = 0 := by
  rw [scalarInit, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun u hu => ?_
  refine WP.append (stores_ok (by decide) (hc.of_rest (hu.rest (ws := [.r3]) (by decide)) (by decide)))
    fun v ⟨out, frame, _, kv⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  have he : ∀ k < 16, limb t.mem (State.addr b) SR k = 0 := by
    intro k hk; rw [ht.mem]; have h := out k hk; rw [hu.gpr] at h; exact h
  refine ⟨⟨(hu.rest (by decide)).trans ((kv.mono (by decide)).trans (ht.rest (by decide))), ?_⟩,
    ht.gpr, fun k hk => by rw [he k hk]; decide, ?_⟩
  · rw [ht.mem, ← hu.mem]
    exact frame.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self
  · exact (val16_congr he).trans (val16_zero_fn _)

theorem scalarReduceEngine_ok {b p : BitVec 32} {s : State} (hc : Ctx b s)
    (hp : s.gpr .r12 = p) (hfit : p.toNat + 64 ≤ 2 ^ 32)
    (hread : ∀ n < 64, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 n) 1)
    (hsep : ∀ r ∈ scalarRegions b, (⟨State.addr p, 64⟩ : Region).Disjoint r) :
    WP isa scalarReduceEngine s fun t => ScalarBodyKeep b s t ∧
      Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR = decodeLE (bytesAt s.mem (State.addr p) 64) % L := by
  unfold scalarReduceEngine
  refine WP.seq (WP.mono (scalarInit_ok hc) fun u ⟨ku, eu, lu, vu⟩ => ?_)
  refine WP.mono (scalarLoop_ok (ku.ctx hc) ((ku.rest.gpr _ (by decide)).trans hp) hfit
    (fun n hn => by rw [ku.rest.rd, ku.rest.wr]; exact hread n hn) hsep eu lu vu)
    fun t ⟨kt, lt, vt⟩ => ⟨ku.trans kt, lt, ?_⟩
  have bytes : bytesAt u.mem (State.addr p) 64 = bytesAt s.mem (State.addr p) 64 := by
    unfold bytesAt; apply List.map_congr_left
    intro n hn
    exact ku.frame.bytes hsep (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hn)
  rw [vt, bytes]

end VG.Proof.Ed25519.Arm
