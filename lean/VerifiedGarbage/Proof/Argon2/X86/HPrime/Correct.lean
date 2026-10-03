import VerifiedGarbage.Proof.Argon2.X86.HPrime.Finish

/-!
# Argon2 H′ on x86 (32-bit): correctness

`setup_ok` saves the caller's registers and lays out the output pointer, the
bytes left and the length prefix in `scratch`; `correct` composes it with
`first_ok`, `finish_ok` and the restore of the registers.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (setup restore first finishOutput saved outOff leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_store readW_writeW_addr contains_addr)
open VG.Proof.Sha512.X86 (ea_of)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem arg_in_rd {s : State} (hrd : s.rd = s₀.rd) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [hrd, hp.rd], ?_⟩
  show Region.Contains ⟨addr (esp₀ s₀) (4 + 4 * 0), 20⟩ _ _
  rw [arg_addr hp hi, arg_addr hp (by decide)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem arg_frame {m : Mem} (f : Frame [scrR s₀] s₀.mem m) {i : Nat} (hi : i < 5) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine f.readW (r := ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.arg_scr.sub_left (arg_sub hp hi)

theorem scr_in {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 16384) :
    InRegions s.wr (addr (scr s₀) d) 4 := by
  rw [hwr, hp.wr]
  exact ⟨scrR s₀, by simp, contains_addr hd (by decide) hp.scr_fits⟩

theorem scr_frame {m : Mem} (f : Frame [scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 16384)
    (v : BitVec 32) : Frame [scrR s₀] s₀.mem (m.writeW (addr (scr s₀) d) v) :=
  f.writeW (List.mem_singleton_self _) v (contains_addr hd (by decide) hp.scr_fits)

/-- The state after `setup`. -/
theorem setup_ok : WP isa (.block setup) s₀ fun t => Body s₀ t ∧ Out s₀ t [] ∧
    t.gpr .ebp = s₀.gpr .ebp ∧ Frame [scrR s₀] s₀.mem t.mem := by
  have hs := hp.scr_fits
  have esp : s₀.gpr .esp = esp₀ s₀ := rfl
  unfold setup
  simp only [saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_movm (ea_of esp 20) (arg_in_rd hp (i := 4) rfl (by decide)) fun t₁ u₁ => ?_
  have a₁ : t₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (ea_of a₁ 840) (scr_in hp u₁.wr (by decide)) fun t₂ u₂ => ?_
  have a₂ : t₂.gpr .eax = scr s₀ := by rw [u₂.gpr, a₁]
  refine wp_store (ea_of a₂ 844) (scr_in hp (by rw [u₂.wr, u₁.wr]) (by decide)) fun t₃ u₃ => ?_
  have a₃ : t₃.gpr .eax = scr s₀ := by rw [u₃.gpr, a₂]
  refine wp_store (ea_of a₃ 848) (scr_in hp (by rw [u₃.wr, u₂.wr, u₁.wr]) (by decide)) fun t₄ u₄ => ?_
  refine wp_mov fun t₅ u₅ => ?_
  have b₅ : t₅.gpr .ebx = scr s₀ := by rw [u₅.gpr, u₄.gpr, a₃]
  have g₅ : ∀ r, r ≠ .ebx → r ≠ .eax → t₅.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₅.other _ h1, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ h2]
  have rd₅ : t₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : t₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have F₅ : Frame [scrR s₀] s₀.mem t₅.mem := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    exact scr_frame hp (scr_frame hp (scr_frame hp (by rw [u₁.mem]; exact Frame.refl _ _) (by decide) _)
      (by decide) _) (by decide) _
  refine wp_movm (ea_of (by rw [g₅ _ (by decide) (by decide)]) 12)
    (arg_in_rd hp (i := 2) (by rw [rd₅]) (by decide)) fun t₆ u₆ => ?_
  refine wp_store (ea_of (by rw [u₆.other _ (by decide), b₅]) outOff)
    (scr_in hp (by rw [u₆.wr, wr₅]) (by decide)) fun t₇ u₇ => ?_
  refine wp_movm (ea_of (by rw [u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide) (by decide)]) 16)
    (arg_in_rd hp (i := 3) (by rw [u₇.rd, u₆.rd, rd₅]) (by decide)) fun t₈ u₈ => ?_
  refine wp_store (ea_of (by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]) leftOff)
    (scr_in hp (by rw [u₈.wr, u₇.wr, u₆.wr, wr₅]) (by decide)) fun t₉ u₉ => ?_
  refine wp_store (ea_of (by rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]) 832)
    (scr_in hp (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]) (by decide)) fun t u => WP.block_nil ?_
  -- Values.
  have v₆ : t₆.gpr .eax = op s₀ := by rw [u₆.gpr, arg_frame hp F₅ (i := 2) (by decide)]
  have F₇ : Frame [scrR s₀] s₀.mem t₇.mem := by
    rw [u₇.mem, u₆.mem]; exact scr_frame hp F₅ (by decide) _
  have v₈ : t₈.gpr .eax = arg s₀ 3 := by rw [u₈.gpr, arg_frame hp F₇ (i := 3) (by decide)]
  have rds : t.rd = s₀.rd := by rw [u.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wrs : t.wr = s₀.wr := by rw [u.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  have gt : ∀ r, r ≠ .ebx → r ≠ .eax → t.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u.gpr, u₉.gpr, u₈.other _ h2, u₇.gpr, u₆.other _ h2, g₅ _ h1 h2]
  have bt : t.gpr .ebx = scr s₀ := by
    rw [u.gpr, u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]
  have m₉ : t₉.mem = (t₇.mem.writeW (addr (scr s₀) leftOff) (arg s₀ 3)) := by
    rw [u₉.mem, u₈.mem, v₈]
  have mt : t.mem = (t₇.mem.writeW (addr (scr s₀) leftOff) (arg s₀ 3)).writeW (addr (scr s₀) 832)
      (arg s₀ 3) := by
    rw [u.mem, m₉, u₉.gpr, v₈]
  have m₇ : t₇.mem = t₅.mem.writeW (addr (scr s₀) outOff) (op s₀) := by
    rw [u₇.mem, u₆.mem, v₆]
  have Ft : Frame [scrR s₀] s₀.mem t.mem := by
    rw [mt]; exact scr_frame hp (scr_frame hp F₇ (by decide) _) (by decide) _
  -- Reads of `scratch` after the last writes.
  have R : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 16384 → e + 4 ≤ 16384 →
      (d + 4 ≤ e ∨ e + 4 ≤ d) →
      (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v d e hd he h => readW_writeW_addr m v (by omega) (by omega) h
  have keep7 : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ 832 ∨ 864 ≤ d ∨ (836 ≤ d ∧ d + 4 ≤ 856)) →
      t.mem.readW (addr (scr s₀) d) 32 = t₅.mem.readW (addr (scr s₀) d) 32 := fun d hd h => by
    rw [mt, R _ _ d 832 hd (by decide) (by omega), R _ _ d leftOff hd (by decide) (by simp only [leftOff]; omega),
      m₇, R _ _ d outOff hd (by decide) (by simp only [outOff]; omega)]
  have m₅ : t₅.mem = ((s₀.mem.writeW (addr (scr s₀) 840) (s₀.gpr .ebx)).writeW (addr (scr s₀) 844)
      (s₀.gpr .esi)).writeW (addr (scr s₀) 848) (s₀.gpr .edi) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide)]
  refine ⟨⟨bt, by rw [gt _ (by decide) (by decide)], rds, wrs,
      Ft.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, fun q hq => ?_, ?_⟩,
    ⟨?_, ?_, rfl, Nat.zero_le _⟩, gt _ (by decide) (by decide), Ft⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rw [keep7 _ (by decide) (by decide), m₅, R _ _ 840 848 (by decide) (by decide) (by decide),
        R _ _ 840 844 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    · rw [keep7 _ (by decide) (by decide), m₅, R _ _ 844 848 (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32]
    · rw [keep7 _ (by decide) (by decide), m₅, Mem.readW_writeW_self32]
  · rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (.inl rfl), show P s₀ + 832 = addr (scr s₀) 832 from
      (scr_addr hp (d := 832) (by decide)).symm, mt, Mem.readW_writeW_self32, Spec.Argon2.le32,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · show _ = _
    rw [mt, R _ _ outOff 832 (by decide) (by decide) (by decide),
      R _ _ outOff leftOff (by decide) (by decide) (by decide), m₇, Mem.readW_writeW_self32]
    simp
  · rw [mt, R _ _ leftOff 832 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    simp [ol]

theorem scr_rd {s : State} (b : Body s₀ s) {d : Nat} (hd : d + 4 ≤ 16384) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 := by
  rw [b.rd, b.wr]
  exact ⟨scrR s₀, by simp [hp.wr], contains_addr hd (by decide) hp.scr_fits⟩

theorem correct : WP isa Impl.Argon2.X86.HPrime.code s₀ fun t => abiPreserved s₀ t ∧ hPrimeX86.post s₀ t := by
  have hif := hp.in_fits
  unfold Impl.Argon2.X86.HPrime.code
  refine WP.seq ((setup_ok hp).mono fun s₁ ⟨b₁, o₁, e₁, F₁⟩ => ?_)
  have hin : bytesAt s₁.mem ((inp s₀).setWidth 64) (inl s₀) = bytesAt s₀.mem ((inp s₀).setWidth 64) (inl s₀) :=
    Proof.Blake2.bytesAt_congr fun i hi => F₁.bytes (R := inR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega) hi
  refine WP.seq ((first_ok hp ⟨b₁, o₁, e₁, hin⟩).mono fun s₂ ⟨⟨b₂, o₂, e₂, _⟩, d₂⟩ => ?_)
  refine WP.seq ((finish_ok hp b₂ o₂ d₂).mono fun s₃ ⟨b₃, e₃, h₃⟩ => ?_)
  unfold restore
  refine wp_movm (ea_of b₃.ebx 848) (scr_rd hp b₃ (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (ea_of (by rw [u₄.other _ (by decide), b₃.ebx]) 844)
    (by rw [u₄.rd, u₄.wr]; exact scr_rd hp b₃ (by decide)) fun s₅ u₅ => ?_
  refine wp_movm (ea_of (by rw [u₅.other _ (by decide), u₄.other _ (by decide), b₃.ebx]) 840)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact scr_rd hp b₃ (by decide)) fun t u => WP.block_nil ?_
  have mt : t.mem = s₃.mem := by rw [u.mem, u₅.mem, u₄.mem]
  have sv := b₃.saved
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at sv
  obtain ⟨sb, ss, sd⟩ := sv
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u.gpr, u₅.mem, u₄.mem]; exact sb
    · rw [u.other _ (by decide), u₅.gpr, u₄.mem]; exact ss
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; exact sd
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃, e₂]
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), b₃.esp]
  · rw [mt]
    refine b₃.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_out
    · exact hp.ret_scr
    · show Region.Disjoint _ ⟨(esp₀ s₀ - BitVec.ofNat 32 60).setWidth 64, 60⟩
      rw [Taint.sub_setWidth hp.esp_lo]
      exact Offset.base_disjoint_below _ (by omega)
  · show bytesAt t.mem _ _ = _
    rw [mt]; exact h₃

end

end VG.Proof.Argon2.X86.HPrime
