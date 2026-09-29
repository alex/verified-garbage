theorem o1 (a b : Nat) (hb : b < 2^32) : (a * 2 ^ 32 + b) % 64 = b % 64 := by omega
theorem o2 (x : Nat) (h : x + 96 ≤ 2^64) : x + 64 ≤ 2^64 := by omega
theorem o3 (x c : Nat) (h : x + 96 ≤ 2^64) (hc : c ≤ 32) : x + c + 64 ≤ 2^64 := by omega
theorem o4 (m : Nat) (h : m % 64 = 5) : (m + 59) % 64 = 0 := by omega
theorem o5 (x c : Nat) (h : x + 96 ≤ 2^64) (hc : c ≤ 32) : x + c + 64 ≤ 18446744073709551616 := by omega
