import VerifiedGarbage.Proof.Ed25519.X86.SignCached.CTHash
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashInputs

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) init (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [.caller 5 0] (by decide) (by simp [Whole.valid]) (by taint_decide)).seq
    (init_call_ct hL)

theorem update_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hp : Whole.valid 6 p) (hn : Whole.valid 6 n)
    (hi : Input L (value L p) (value L n))
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0
      [.caller 5 0, .const count, .const 0, p, n, .caller 5 192])) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True)
      (update (setup 0 [.caller 5 0, .const count, .const 0, p, n, .caller 5 192]))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb _ (by simp) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · simp [Whole.valid]
    · simp [Whole.valid]
    · exact hp
    · exact hn
    · simp [Whole.valid]) ht).seq
    (update_call_ct hL rfl hi (fun _ hs => update_args hL count p n hs))

theorem finalize_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (finalize n b)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (finalize_args_ct hL ha hb n hn b ht).seq (finalize_call_ct hL _)

theorem hashSeed_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hashSeed
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hs := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 0 (.caller 1 0) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa [value, Lay.value] using seed_input hL)
    (by taint_decide)
  exact (init_ct hL ha hb).seq (hs.seq (finalize_ct hL ha hb 32 (by decide) false (by taint_decide)))

theorem hashNonce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hashNonce
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hs := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 0 (.frame 64) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (prefix_input hL) (by taint_decide)
  have hm := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 32 (.caller 3 0) (.caller 4 0)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa only [value, Lay.value, BitVec.add_zero] using message_input hL)
    (by taint_decide)
  exact (init_ct hL ha hb).seq (hs.seq (hm.seq
    (finalize_ct hL ha hb 32 (by decide) true (by taint_decide))))

theorem hashChallenge_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hashChallenge
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hr := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 0 (.caller 0 0) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa [value, Lay.value] using point_input hL)
    (by taint_decide)
  have hp := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 32 (.caller 2 0) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa [value, Lay.value] using key_input hL)
    (by taint_decide)
  have hm := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 64 (.caller 3 0) (.caller 4 0)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa only [value, Lay.value, BitVec.add_zero] using message_input hL)
    (by taint_decide)
  exact (init_ct hL ha hb).seq (hr.seq (hp.seq (hm.seq
    (finalize_ct hL ha hb 64 (by decide) true (by taint_decide)))))

end VG.Proof.Ed25519.X86.SignCached
