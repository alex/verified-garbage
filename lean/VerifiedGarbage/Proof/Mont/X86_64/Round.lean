import VerifiedGarbage.Proof.Mont.X86_64.Blocks

/-!
# Montgomery arithmetic on x86-64: a round of the multiplication

The accumulator's window of registers (`wins n i`), how it rotates from one
round to the next, and a round (`round_ok`): the accumulator `T < 2m`
becomes `(T + a_i B + u m) / 2⁶⁴ < 2m` for some `u`, with the low word of
`T + a_i B + u m` zero.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-! ## The window -/

theorem win_succ (n i j : Nat) : win n (i + 1) j = win n i (j + 1) := by
  simp only [win, Nat.add_assoc, Nat.add_comm 1 j]

theorem win_wrap (n i : Nat) : win n i (n + 2) = win n i 0 := by
  simp only [win, Nat.add_zero, Nat.add_mod_right]

theorem win_mod (n i j : Nat) : win n i j = win n (i % (n + 2)) j := by
  simp only [win, Nat.add_mod i j, Nat.mod_mod, Nat.add_mod (i % (n + 2)) j]

theorem wins_mod (n i : Nat) : wins n i = wins n (i % (n + 2)) := by
  simp only [wins]; exact List.map_congr_left fun j _ => win_mod n i j

theorem wins_length (n i : Nat) : (wins n i).length = n + 2 := by simp [wins]

theorem wins_cons (n i : Nat) :
    wins n i = win n i 0 :: (List.range (n + 1)).map (fun j => win n i (j + 1)) := by
  simp only [wins, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem wins_succ (n i : Nat) :
    wins n (i + 1) = (List.range (n + 1)).map (fun j => win n i (j + 1)) ++ [win n i 0] := by
  rw [wins, show win n (i + 1) = fun j => win n i (j + 1) from funext (win_succ n i)]
  simp only [List.range_succ (n := n + 1), List.map_append, List.map_cons, List.map_nil, win_wrap]

theorem wins_split (n i : Nat) :
    wins n i = (List.range n).map (win n i) ++ [win n i n, win n i (n + 1)] := by
  simp only [wins, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.singleton_append]

theorem nodup_wins_lt : ∀ n < 7, ∀ i < n + 2, (wins n i).Nodup := by decide

theorem regs_wins_lt : ∀ n < 7, ∀ i < n + 2, ∀ t ∈ wins n i, t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx := by
  decide

theorem regs_wins_lt' : ∀ n < 7, ∀ i < n + 2, ∀ t ∈ wins n i, t ≠ .rbp ∧ t ≠ .rdi := by decide

theorem fresh_wins_lt (n : Nat) (hn : n < 7) (i : Nat) (hi : i < n + 2) : Fresh (wins n i) :=
  ⟨nodup_wins_lt n hn i hi, fun t ht =>
    have h := regs_wins_lt n hn i hi t ht
    have h' := regs_wins_lt' n hn i hi t ht
    ⟨h.1, h.2.1, h.2.2, h'.1, h'.2⟩⟩

theorem fresh_wins {n : Nat} (hn : n < 7) (i : Nat) : Fresh (wins n i) := by
  rw [wins_mod]; exact fresh_wins_lt n hn _ (Nat.mod_lt _ (by omega))

/-! ## A row and its carry -/

/-- A row of `rcx · [d]` into the low words of `W = low ++ [tn, tn1]`, and its
carry into `tn` and `tn1`, if the sum fits. -/
theorem rowCarry_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {low : List Reg} {tn tn1 : Reg} (hf : Fresh (low ++ [tn, tn1])) {d : Nat}
    (hd : d + 8 * low.length ≤ size)
    (hb : regsVal s (low ++ [tn, tn1]) + (s.gpr .rcx).toNat * wordsVal s.mem base d low.length <
      2 ^ (64 * low.length) * 2 ^ 128) :
    WP isa (.block (mulRow low d ++ carryUp tn tn1)) s fun s' =>
      regsVal s' (low ++ [tn, tn1]) =
        regsVal s (low ++ [tn, tn1]) + (s.gpr .rcx).toNat * wordsVal s.mem base d low.length ∧
      Keeps (.rbp :: .rax :: .rdx :: (low ++ [tn, tn1])) s s' := by
  have hfl : Fresh low := ⟨(List.nodup_append.mp hf.1).1, fun q hq => hf.2 q (by simp [hq])⟩
  have hn : tn ∉ low ∧ tn1 ∉ low ∧ tn ≠ tn1 := by
    have h := hf.1
    simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at h
    exact ⟨fun hm => h.2.2 tn hm tn (by simp) rfl, fun hm => h.2.2 tn1 hm tn1 (by simp) rfl,
      h.2.1.1⟩
  have ftn := hf.2 tn (by simp)
  have ftn1 := hf.2 tn1 (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (mulRow_ok hs hd hfl) fun s₁ ⟨e₁, k₁⟩ => ?_
  have gtn : s₁.gpr tn = s.gpr tn := k₁.1 tn (by simp [hn.1, ftn.1, ftn.2.2.1, ftn.2.2.2.1])
  have gtn1 : s₁.gpr tn1 = s.gpr tn1 := k₁.1 tn1 (by simp [hn.2.1, ftn1.1, ftn1.2.2.1, ftn1.2.2.2.1])
  have hX := regsVal_lt s₁ low
  simp only [regsVal_append, regsVal, Nat.mul_zero, Nat.add_zero] at hb ⊢
  -- The carry fits.
  have hc : (s₁.gpr tn).toNat + 2 ^ 64 * (s₁.gpr tn1).toNat + (s₁.gpr .rbp).toNat < 2 ^ 128 := by
    rw [gtn, gtn1]
    have h' : 2 ^ (64 * low.length) * ((s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat +
        (s₁.gpr .rbp).toNat) < 2 ^ (64 * low.length) * 2 ^ 128 := by
      rw [Nat.mul_add]; omega
    exact Nat.lt_of_mul_lt_mul_left h'
  refine WP.mono (carryUp_ok s₁ hn.2.2 hc) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hl : regsVal s₂ low = regsVal s₁ low := regsVal_congr fun q hq => k₂.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => hn.1 (h ▸ hq), fun h => hn.2.1 (h ▸ hq)⟩)
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  rw [hl, e₂, gtn, gtn1]
  have : 2 ^ (64 * low.length) * ((s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat +
      (s₁.gpr .rbp).toNat) = 2 ^ (64 * low.length) * ((s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat) +
      2 ^ (64 * low.length) * (s₁.gpr .rbp).toNat := Nat.mul_add _ _ _
  rw [this]
  omega

/-! ## A round -/

/-- `t₀ + (t₀ m' mod 2⁶⁴) m ≡ 0 (mod 2⁶⁴)` when `m m' ≡ -1`. -/
theorem mont_low (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 64 = 0) :
    (t0 + t0 * minv % 2 ^ 64 * m) % 2 ^ 64 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 64), Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod, show t0 + t0 * minv * m = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m]; omega,
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

theorem round_eq (M : Mod) (a b i : Nat) :
    round M a b i = ([.mov .rcx (.mem (sc (a + 8 * i)))] : List Instr) ++
      ((mulRow ((List.range M.n).map (win M.n i)) b ++ carryUp (win M.n i M.n) (win M.n i (M.n + 1))) ++
        (([.mov .rax (.reg (win M.n i 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax)] :
          List Instr) ++
          (mulRow ((List.range M.n).map (win M.n i)) M.mo ++
            carryUp (win M.n i M.n) (win M.n i (M.n + 1))))) := by
  simp only [round, List.append_assoc]

/-- Round `i` of the multiplication: `2⁶⁴ T' = T + a_i B + u m`, and
`T' < 2m` if `T < 2m`. -/
theorem round_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 7) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * M.n ≤ size)
    (hmo : M.mo + 8 * M.n ≤ size) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hB : wordsVal s.mem base b M.n < m)
    (hT : regsVal s (wins M.n i) < 2 * m) :
    WP isa (.block (round M a b i)) s fun s' =>
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: wins M.n i) s s' := by
  have hW := wins_split M.n i
  have hf : Fresh ((List.range M.n).map (win M.n i) ++ [win M.n i M.n, win M.n i (M.n + 1)]) :=
    hW ▸ fresh_wins hn i
  have hl : ((List.range M.n).map (win M.n i)).length = M.n := by simp
  have hm' : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  have hP : 2 ^ (64 * M.n) * 2 ^ 128 = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
    rw [Nat.mul_assoc]; rfl
  rw [round_eq, WP.block_append_iff]
  refine WP.mono (movRcx_ok hs ha) fun s₁ ⟨c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hT₁ : regsVal s₁ (wins M.n i) = regsVal s (wins M.n i) := regsVal_congr fun q hq =>
    k₁.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (fresh_wins hn i).2 q hq |>.2.1)
  rw [WP.block_append_iff]
  have hA := (word s.mem base (a + 8 * i)).isLt
  have hAB : (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega) (by omega)
  refine WP.mono (rowCarry_ok hs₁ hf (d := b) (by rw [hl]; omega) (by
      rw [← hW, hl, hT₁, c₁, k₁.2.1, hP]
      have : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (by omega)
      omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [← hW, hl, hT₁, c₁, k₁.2.1] at e₂
  have hs₂ := hs₁.of_keeps k₂ (by
    intro h; rw [← hW] at h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (fresh_wins hn i).2 _ h |>.2.2.2.2 rfl)
  rw [WP.block_append_iff]
  refine WP.mono (uBlock_ok s₂ (win M.n i 0) M.minv) fun s₃ ⟨u₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have hT₃ : regsVal s₃ (wins M.n i) = regsVal s₂ (wins M.n i) := regsVal_congr fun q hq =>
    k₃.1 q (by
      have := (fresh_wins hn i).2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨this.1, this.2.1, this.2.2.1⟩)
  have hu := (s₃.gpr .rcx).isLt
  have hum : (s₃.gpr .rcx).toNat * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
  have hmem₃ : s₃.mem = s.mem := by rw [k₃.2.1, k₂.2.1, k₁.2.1]
  refine WP.mono (rowCarry_ok hs₃ hf (d := M.mo) (by rw [hl]; omega) (by
      rw [← hW, hl, hT₃, e₂, hmem₃, hm, hP]
      have : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (by omega)
      omega)) fun s₄ ⟨e₄, k₄⟩ => ?_
  rw [← hW, hl, hT₃, e₂, hmem₃, hm] at e₄
  -- The window's value, and its low word, which is zero.
  have hcons := wins_cons M.n i
  have ht0₂ : (regsVal s₂ (wins M.n i)) % 2 ^ 64 = (s₂.gpr (win M.n i 0)).toNat := by
    rw [hcons, regsVal]; omega
  have h₄ : (regsVal s₄ (wins M.n i)) % 2 ^ 64 = (s₄.gpr (win M.n i 0)).toNat := by
    rw [hcons, regsVal]; omega
  have hlow : (s₄.gpr (win M.n i 0)).toNat = 0 := by
    have h := mont_low (s₂.gpr (win M.n i 0)).toNat M.minv.toNat m hinv
    rw [← u₃] at h
    rw [← e₂] at e₄
    omega
  have hrot : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) = regsVal s₄ (wins M.n i) := by
    rw [wins_succ, regsVal_append, hcons, regsVal]
    simp only [regsVal, hlow, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  refine ⟨⟨(s₃.gpr .rcx).toNat, by rw [hrot, e₄]⟩, ?_, ?_⟩
  · have : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) < 2 ^ 64 * (2 * m) := by
      rw [hrot, e₄]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  · rw [← hW] at k₂ k₄
    exact (((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans
      (k₃.mono (by sub_regs))).trans (k₄.mono (by sub_regs))

end VG.Proof.Mont.X86_64