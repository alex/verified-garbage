import VerifiedGarbage.Proof.Rc4.AArch64.Group
import VerifiedGarbage.Proof.Rc4.AArch64.ApplySetup
import VerifiedGarbage.Proof.Rc4.Schedule

/-!
# The key schedule's lanes

`keyByte_ok`: the next key byte is added to `j`, and the key pointer `x7`
and the bytes left before the key repeats, `x5`, advance (wrapping).
`ksaSwap_ok`: then the swap step is the specification's scheduling round.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem mod_succ_wrap {n L : Nat} (h : n % L + 1 = L) : (n + 1) % L = 0 := by
  have := Nat.div_add_mod n L
  rw [show n + 1 = L * (n / L + 1) by rw [Nat.mul_add]; omega]
  exact Nat.mul_mod_right _ _

theorem mod_succ_lt {n L : Nat} (h : n % L + 1 < L) : (n + 1) % L = n % L + 1 := by
  have := Nat.div_add_mod n L
  rw [show n + 1 = (n % L + 1) + L * (n / L) by omega, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt h]

theorem low8 (x : BitVec 8) : ((x.setWidth 32).setWidth 64).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; omega

theorem keyLoad_ok {s : State} {K : Addr} {L n : Nat} {J : BitVec 8} (hL : 0 < L) (hL' : L < 2 ^ 64)
    (h7 : s.gpr .x7 = K + BitVec.ofNat 64 (n % L)) (h5 : s.gpr .x5 = BitVec.ofNat 64 (L - n % L))
    (hkey : InRegions (s.rd ++ s.wr) K L) (hj : s.v (dq 0) = bc J) :
    WP isa (.block [.ldrb .x6 .x7 0, .vop (.dup .b16 .v6 .x6), .vop (.add .b16 (dq 0) (dq 0) .v6),
      .addImm .x .x7 .x7 1, .subImm .x .x5 .x5 1]) s fun t =>
      t.v (dq 0) = bc (J + s.mem (K + BitVec.ofNat 64 (n % L))) ∧
      t.gpr .x7 = K + BitVec.ofNat 64 (n % L) + 1 ∧ t.gpr .x5 = BitVec.ofNat 64 (L - n % L - 1) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ dq 0 → v ≠ .v6 → t.v v = s.v v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hm : n % L < L := Nat.mod_lt _ hL
  have hb := region_offset _ _ _ (n % L) 1 (by omega) (by omega) hkey
  have hj' : s.v .v0 = bc J := hj
  have h1 : BitVec.ofNat 64 (L - n % L) - 1#64 = BitVec.ofNat 64 (L - n % L - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)
  have d0 : dq 0 = .v0 := rfl
  rrun [d0, hb, read_byte', hj', h7, h5, low8, bc_lit, add_bc, h1]
  refine ⟨fun r a b c => ?_, fun v a b => ?_, ?_⟩
  · simp [a, b, c]
  · simp [a, b]
  · simp [State.write, State.setV]

theorem keyByte_ok {s : State} {K : Addr} {L n : Nat} {J : BitVec 8} (hL : 0 < L) (hL' : L < 2 ^ 64)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 L)
    (h7 : s.gpr .x7 = K + BitVec.ofNat 64 (n % L)) (h5 : s.gpr .x5 = BitVec.ofNat 64 (L - n % L))
    (hkey : InRegions (s.rd ++ s.wr) K L) (hj : s.v (dq 0) = bc J) :
    WP isa keyByte s fun t =>
      t.v (dq 0) = bc (J + s.mem (K + BitVec.ofNat 64 (n % L))) ∧
      t.gpr .x7 = K + BitVec.ofNat 64 ((n + 1) % L) ∧
      t.gpr .x5 = BitVec.ofNat 64 (L - (n + 1) % L) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ dq 0 → v ≠ .v6 → t.v v = s.v v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hm : n % L < L := Nat.mod_lt _ hL
  unfold keyByte
  refine WP.seq (WP.mono (keyLoad_ok hL hL' h7 h5 hkey hj)
    fun a ⟨aj, a7, a5, ag, av, am, ard, awr, asp⟩ => ?_)
  apply WP.ite _ (eval_zero' a .x5 a5 (by omega))
  · intro hz
    have hw : n % L + 1 = L := by simp at hz; omega
    have a0 : a.gpr .x0 = K := by rw [ag _ (by decide) (by decide) (by decide), h0]
    have a1 : a.gpr .x1 = BitVec.ofNat 64 L := by rw [ag _ (by decide) (by decide) (by decide), h1]
    rrun [a0, a1]
    refine ⟨aj, ?_, ?_, fun r r5 r6 r7 => ?_, av, am, ard, awr, ?_⟩
    · rw [mod_succ_wrap hw]; simp
    · rw [mod_succ_wrap hw, Nat.sub_zero]
    · simp only [r5, r7, ite_false]; exact ag r r5 r6 r7
    · simp only [State.write]; exact asp
  · intro hnz
    have hlt : n % L + 1 < L := by simp at hnz; omega
    refine WP.block_nil ⟨aj, ?_, ?_, ag, av, am, ard, awr, asp⟩
    · rw [a7, mod_succ_lt hlt, Offset.add_ofNat_add_one]
    · rw [a5, mod_succ_lt hlt, Nat.sub_add_eq]

theorem byte_rearr (a b c d : BitVec 8) : a + b - d + c = a + c + b - d := by bv_omega

/-- A scheduling round at lane `l` of the group whose base is `B`, once the
key byte is in `j`. -/
theorem ksaSwap_ok {l B n : Nat} (hl : l < 16) (hn : n = B + l) (hn' : n < 256) {key : List Byte}
    {s : State} (hk : Consts s) (ht : TableIn s B (schedulePrefix key n).1)
    (hj : s.v (dq 0) = bc ((schedulePrefix key n).2 + key.getD (n % key.length) 0 - bB B))
    (hsi : s.v si = bc (tbyte s.v l)) :
    ∃ s', runBlock isa (swapStep false l) s = some s' ∧
      TableIn s' B (schedulePrefix key (n + 1)).1 ∧
      s'.v (dq 0) = bc ((schedulePrefix key (n + 1)).2 - bB B) ∧
      s'.v si = bc (tbyte s'.v (l + 1)) ∧ Only stepRegs s s' := by
  have hS := schedule_succ key n
  simp only [scheduleRound] at hS
  generalize schedulePrefix key n = st at ht hj hS
  obtain ⟨s₁, run₁, t₁, j₁, i₁, -, o₁⟩ :=
    swapStep_run false hl hk hj hsi (NB := 0) fun h => absurd h (by decide)
  have hR : ∀ k < 256, tbyte s.v k = st.1.getD (BitVec.ofNat 8 (B + k)).toNat 0 := ht
  have ha : tbyte s.v l = st.1.getD n 0 := by
    rw [hR l (by omega), ← hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn']
  have hJ : st.2 + key.getD (n % key.length) 0 - bB B + tbyte s.v l =
      st.2 + st.1.getD n 0 + key.getD (n % key.length) 0 - bB B := by rw [ha, byte_rearr]
  rw [hJ] at t₁ j₁ i₁
  refine ⟨s₁, run₁, fun k hk => ?_, by rw [j₁, hS], ?_, o₁⟩
  · rw [hS, t₁ k hk, swapR_eq st.1 (by omega) hR _ hk, hn]
  · rw [i₁, t₁ _ (by omega)]

end VG.Proof.Rc4.AArch64
